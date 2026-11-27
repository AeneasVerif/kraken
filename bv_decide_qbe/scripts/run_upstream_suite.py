#!/usr/bin/env python3
"""Upstream Lean 4 `bv_decide` compatibility and head-to-head benchmark runner."""

from __future__ import annotations

import argparse
import concurrent.futures
from dataclasses import asdict, dataclass, field
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from typing import Callable, Sequence


IMPORT_BV_DECIDE_RE = re.compile(
    r"^([ \t]*(?:(?:public|private|meta|all)[ \t]+)*import[ \t]+)Std\.Tactic\.BVDecide\b",
    re.MULTILINE,
)
BV_DECIDE_TACTIC_RE = re.compile(r"\bbv_decide(_push)?\b")
GUARD_MISMATCH_MARKER = "Docstring on `#guard_msgs` does not match generated message:"
SOLVER_AXIOM_RE = re.compile(
    r"\b([A-Za-z_][A-Za-z0-9_.']*?)\."
    r"(?:_native\.bv_decide(?:_qbe)?\.ax_\d+_\d+|_leanqbe\.bv_solve\.ax_\d+_\d+)\b"
)
ASSIGN_LINE_RE = re.compile(r"^(.+?)\s+=\s+(\S.*)$")
CEX_HEADERS = {
    "error: The prover found a counterexample, consider the following assignment:",
    "The prover found a counterexample, consider the following assignment:",
    "Consider the following assignment:",
}
CEX_PREFIXES = (
    "error: The prover found a counterexample",
    "error: The prover found a potentially spurious counterexample:",
    "error: - The prover used the following expressions as uninterpreted functions:",
)


@dataclass
class GuardMismatch:
    """Parsed `#guard_msgs` mismatch block from Lean output."""

    line: int
    diff_lines: list[str]

    def expected_lines(self) -> list[str]:
        """Return lines representing the expected `#guard_msgs` docstring."""
        return [ln[2:] for ln in self.diff_lines if ln.startswith(("  ", "- "))]

    def actual_lines(self) -> list[str]:
        """Return lines representing the actual generated Lean message."""
        return [ln[2:] for ln in self.diff_lines if ln.startswith(("  ", "+ "))]


@dataclass
class Diagnostic:
    """Single `file:line:col: severity: message` diagnostic from Lean."""

    line: int
    col: int
    severity: str
    lines: list[str]

    @property
    def text(self) -> str:
        """Full multi-line diagnostic payload without `file:line:col: severity: ` prefix."""
        return "\n".join(self.lines)


@dataclass
class RunOutput:
    """Subprocess execution result for one Lean file invocation."""

    returncode: int
    elapsed_s: float
    stdout: str
    stderr: str
    timed_out: bool = False


@dataclass
class SuiteResult:
    """Compatibility and optional head-to-head comparison record for one test file."""

    file: str
    qbe_status: str
    qbe_time_s: float | None = None
    qbe_rc: int | None = None
    qbe_note: str = ""
    diff_kinds: list[str] = field(default_factory=list)
    up_status: str | None = None
    up_time_s: float | None = None
    up_rc: int | None = None
    up_note: str = ""


def resolve_bv_decide_qbe_dir() -> Path:
    """Return the `bv_decide_qbe/` package directory relative to this script."""
    return Path(__file__).resolve().parents[1]


def resolve_lean_prefix() -> Path:
    """Resolve the active Lean toolchain prefix via `lean --print-prefix`."""
    prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    if not prefix:
        raise RuntimeError("`lean --print-prefix` returned empty output")
    return Path(prefix)


def shared_lib_ext() -> str:
    """Return the platform shared library suffix."""
    return ".dylib" if sys.platform == "darwin" else ".so"


def qbe_dynlib_paths(bv_dir: Path) -> tuple[Path, Path]:
    """Return paths to `libkissat_qbe` and `BvDecideQbeNative` shared libraries."""
    ext = shared_lib_ext()
    lib_dir = bv_dir / ".lake" / "build" / "lib"
    return (
        lib_dir / f"libkissat_qbe{ext}",
        lib_dir / f"libbv__decide__qbe_BvDecideQbeNative{ext}",
    )


def validate_qbe_artifacts(bv_dir: Path, repo_root: Path) -> None:
    """Ensure required `.olean` and `.so` artifacts exist before running tests."""
    kissat_so, native_so = qbe_dynlib_paths(bv_dir)
    tactic_olean = bv_dir / ".lake" / "build" / "lib" / "lean" / "BvDecideQbe" / "Tactic.olean"
    missing = [p for p in (kissat_so, native_so, tactic_olean) if not p.is_file()]
    if not missing:
        return
    missing_str = ", ".join(str(p) for p in missing)
    raise FileNotFoundError(
        f"Missing built bv_decide_qbe artifacts ({missing_str}). "
        f"Build inside {bv_dir} with: "
        "env LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true LEAN_NUM_THREADS=1 "
        "lake build libkissat_qbe BvDecideQbeNative:shared BvDecideQbe"
    )


def build_qbe_invocation(
    bv_dir: Path,
    repo_root: Path,
    lean_prefix: Path,
    base_env: dict[str, str] | None = None,
) -> tuple[list[str], dict[str, str]]:
    """Build `[lean, --load-dynlib=...]` command prefix and environment for `bv_decide_qbe`."""
    env = dict(os.environ if base_env is None else base_env)
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_PATH"] = os.pathsep.join(
        [
            str(repo_root / ".lake" / "build" / "lib" / "lean"),
            str(bv_dir / ".lake" / "build" / "lib" / "lean"),
            str(lean_prefix / "lib" / "lean"),
        ]
    )
    lib_dir = str(bv_dir / ".lake" / "build" / "lib")
    existing_ld = env.get("LD_LIBRARY_PATH", "")
    env["LD_LIBRARY_PATH"] = f"{lib_dir}{os.pathsep}{existing_ld}" if existing_ld else lib_dir
    kissat_so, native_so = qbe_dynlib_paths(bv_dir)
    cmd = [
        str(lean_prefix / "bin" / "lean"),
        f"--load-dynlib={kissat_so}",
        f"--load-dynlib={native_so}",
    ]
    return cmd, env


def build_upstream_invocation(
    lean_prefix: Path,
    base_env: dict[str, str] | None = None,
) -> tuple[list[str], dict[str, str]]:
    """Build `[lean]` command prefix and environment for unmodified upstream `bv_decide`."""
    env = dict(os.environ if base_env is None else base_env)
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_PATH"] = str(lean_prefix / "lib" / "lean")
    return [str(lean_prefix / "bin" / "lean")], env


def discover_tests(tests_dir: Path, filter_regex: str | None = None) -> list[Path]:
    """Discover `elab/bv_*.lean` and `elab_bench/bv_*.lean` relative paths under `tests_dir`."""
    if not tests_dir.is_dir():
        raise FileNotFoundError(f"Upstream tests directory does not exist: {tests_dir}")
    subdirs = [tests_dir / "elab", tests_dir / "elab_bench"]
    if not any(d.is_dir() for d in subdirs):
        raise FileNotFoundError(
            f"Expected `elab/` or `elab_bench/` inside `--lean4-tests-dir`: {tests_dir}"
        )
    pattern = re.compile(filter_regex) if filter_regex else None
    found: list[Path] = []
    for sub in subdirs:
        if not sub.is_dir():
            continue
        for path in sorted(sub.glob("bv_*.lean")):
            if path.is_file():
                rel = path.relative_to(tests_dir)
                if pattern is None or pattern.search(rel.as_posix()):
                    found.append(rel)
    return found


def is_na_test(rel_path: Path) -> bool:
    """Return True for upstream tests that are not applicable to `bv_decide_qbe`."""
    return rel_path.name == "bv_import.lean"


def rewrite_for_qbe(src: str) -> str:
    """Rewrite an upstream `bv_decide` Lean file to import and invoke `bv_decide_qbe`."""
    rewritten = IMPORT_BV_DECIDE_RE.sub(r"\1BvDecideQbe.Tactic", src)
    return BV_DECIDE_TACTIC_RE.sub(
        lambda m: "bv_decide_qbe_push" if m.group(1) else "bv_decide_qbe",
        rewritten,
    )


def parse_diagnostics(lean_file: Path, stdout: str) -> tuple[list[Diagnostic], list[str]]:
    """Parse `<lean_file>:<line>:<col>: <sev>: ...` blocks and stray non-prefixed errors."""
    diag_re = re.compile(
        rf"^{re.escape(str(lean_file))}:(\d+):(\d+): (error|warning|info): (.*)$"
    )
    diagnostics: list[Diagnostic] = []
    stray_errors: list[str] = []
    current: Diagnostic | None = None
    in_guard_diff = False

    for line in stdout.splitlines():
        match = diag_re.match(line)
        if match:
            current = Diagnostic(
                line=int(match.group(1)),
                col=int(match.group(2)),
                severity=match.group(3),
                lines=[match.group(4)],
            )
            diagnostics.append(current)
            in_guard_diff = (
                current.severity == "error"
                and GUARD_MISMATCH_MARKER in match.group(4)
            )
            continue

        if current is not None:
            if in_guard_diff:
                if line == "" or line.startswith(("  ", "- ", "+ ")):
                    current.lines.append(line)
                    continue
                in_guard_diff = False
                current = None
            elif not line.startswith("error:"):
                current.lines.append(line)
                continue

        if line.startswith("error:"):
            stray_errors.append(line)

    return diagnostics, stray_errors


def _normalize_axiom_line(line: str) -> str:
    if "depends on axioms:" not in line:
        return line
    return SOLVER_AXIOM_RE.sub(r"\1.<BV_SOLVER_AXIOM>", line)


def _classify_guard_diff(mismatch: GuardMismatch) -> str | None:
    """Classify one `#guard_msgs` mismatch as `axiom_name` or `sat_cex`, else None."""
    expected = mismatch.expected_lines()
    actual = mismatch.actual_lines()
    if not expected or not actual:
        return None

    # 1. Expected solver axiom name diff in `#print axioms`.
    if any("depends on axioms:" in ln for ln in expected) and [
        _normalize_axiom_line(ln) for ln in expected
    ] == [_normalize_axiom_line(ln) for ln in actual]:
        return "axiom_name"

    # 2. Expected SAT counterexample value/ordering diff.
    if not expected[0].startswith(CEX_PREFIXES) or not actual[0].startswith(CEX_PREFIXES):
        return None
    header_indices = [
        i for i, ln in enumerate(mismatch.diff_lines)
        if ln.startswith("  ") and ln[2:] in CEX_HEADERS
    ]
    if not header_indices:
        return None
    last_header_idx = header_indices[-1]
    minus_lhs: list[str] = []
    plus_lhs: list[str] = []
    for idx, ln in enumerate(mismatch.diff_lines):
        if ln.startswith(("- ", "+ ")):
            if idx <= last_header_idx:
                return None
            assign = ASSIGN_LINE_RE.match(ln[2:])
            if not assign:
                return None
            lhs = assign.group(1)
            if lhs.startswith(("error:", "warning:", "info:")):
                return None
            (minus_lhs if ln.startswith("- ") else plus_lhs).append(lhs)
    if minus_lhs and sorted(minus_lhs) == sorted(plus_lhs):
        return "sat_cex"
    return None


def classify_qbe_output(lean_file: Path, run: RunOutput) -> tuple[str, str, list[str]]:
    """Classify a `bv_decide_qbe` execution into PASS / PASS_EXPECTED_DIFF / FAIL."""
    if run.timed_out:
        return "FAIL", f"timeout after {run.elapsed_s:.2f}s", []
    if run.returncode == 0:
        return "PASS", "verbatim", []
    if run.stderr.strip():
        first_err = run.stderr.strip().splitlines()[0]
        return "FAIL", f"rc={run.returncode} stderr: {first_err}", []

    diagnostics, stray_errors = parse_diagnostics(lean_file, run.stdout)
    if stray_errors:
        return "FAIL", f"rc={run.returncode}: {stray_errors[0]}", []

    error_diags = [d for d in diagnostics if d.severity == "error"]
    if not error_diags:
        return "FAIL", f"rc={run.returncode} with no parsed errors", []

    guard_entries: list[tuple[GuardMismatch, str, str]] = []
    other_errors: list[Diagnostic] = []
    for diag in error_diags:
        if GUARD_MISMATCH_MARKER in diag.lines[0]:
            # Drop the header line and optional leading blank separator line.
            body = diag.lines[1:]
            while body and body[0] == "":
                body = body[1:]
            while body and body[-1] == "":
                body = body[:-1]
            mismatch = GuardMismatch(line=diag.line, diff_lines=body)
            kind = _classify_guard_diff(mismatch)
            if kind is None:
                return "FAIL", f"unexpected #guard_msgs diff at line {diag.line}", []
            actual_msg = "\n".join(mismatch.actual_lines()).strip()
            guard_entries.append((mismatch, kind, actual_msg))
        else:
            other_errors.append(diag)

    if not guard_entries:
        first = other_errors[0]
        return "FAIL", f"line {first.line}: {first.lines[0]}", []

    # Verify every non-guard `error:` was emitted solely by a validated `#guard_msgs` block.
    matched_guards: set[int] = set()
    for err in other_errors:
        rendered = f"error: {err.text}".strip()
        matched_idx: int | None = None
        for idx, (mismatch, _kind, actual_msg) in enumerate(guard_entries):
            if idx not in matched_guards and err.line >= mismatch.line and rendered == actual_msg:
                matched_idx = idx
                break
        if matched_idx is None:
            return "FAIL", f"unguarded error at line {err.line}: {err.lines[0]}", []
        matched_guards.add(matched_idx)

    kinds = sorted({kind for _mismatch, kind, _actual in guard_entries})
    return "PASS_EXPECTED_DIFF", f"expected #guard_msgs diff ({', '.join(kinds)})", kinds


def run_lean_file(
    cmd_prefix: Sequence[str],
    lean_file: Path,
    env: dict[str, str],
    timeout_s: float,
) -> RunOutput:
    """Invoke Lean on `lean_file` with `timeout_s` and measure monotonic wall time."""
    cmd = list(cmd_prefix) + [str(lean_file)]
    t0 = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        dt = time.monotonic() - t0
        return RunOutput(
            returncode=proc.returncode,
            elapsed_s=dt,
            stdout=proc.stdout,
            stderr=proc.stderr,
            timed_out=False,
        )
    except subprocess.TimeoutExpired as exc:
        dt = time.monotonic() - t0
        stdout = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return RunOutput(
            returncode=-1,
            elapsed_s=dt,
            stdout=stdout,
            stderr=stderr,
            timed_out=True,
        )


def compute_compare_summary(results: Sequence[SuiteResult]) -> dict[str, float | int | None]:
    """Compute paired counts, total wall times, W-AM, and W-GM across passing compare pairs."""
    paired = [
        r
        for r in results
        if r.qbe_status in ("PASS", "PASS_EXPECTED_DIFF")
        and r.up_status == "PASS"
        and r.qbe_time_s is not None
        and r.up_time_s is not None
        and r.qbe_time_s > 0.0
        and r.up_time_s > 0.0
    ]
    if not paired:
        return {
            "paired_count": 0,
            "total_up_s": 0.0,
            "total_qbe_s": 0.0,
            "w_am": None,
            "w_gm": None,
            "speedup_am": None,
            "speedup_gm": None,
        }
    total_up = sum(r.up_time_s for r in paired if r.up_time_s is not None)
    total_qbe = sum(r.qbe_time_s for r in paired if r.qbe_time_s is not None)
    w_am = total_qbe / total_up
    log_sum = sum(
        math.log(r.qbe_time_s / r.up_time_s)
        for r in paired
        if r.qbe_time_s is not None and r.up_time_s is not None
    )
    w_gm = math.exp(log_sum / len(paired))
    return {
        "paired_count": len(paired),
        "total_up_s": total_up,
        "total_qbe_s": total_qbe,
        "w_am": w_am,
        "w_gm": w_gm,
        "speedup_am": 1.0 / w_am,
        "speedup_gm": 1.0 / w_gm,
    }


def summarize_counts(results: Sequence[SuiteResult]) -> dict[str, int]:
    """Count compatibility and upstream statuses across all suite results."""
    return {
        "total": len(results),
        "pass": sum(1 for r in results if r.qbe_status == "PASS"),
        "pass_expected_diff": sum(1 for r in results if r.qbe_status == "PASS_EXPECTED_DIFF"),
        "na": sum(1 for r in results if r.qbe_status == "NA"),
        "fail": sum(1 for r in results if r.qbe_status == "FAIL"),
        "up_pass": sum(1 for r in results if r.up_status == "PASS"),
        "up_fail": sum(1 for r in results if r.up_status == "FAIL"),
    }


def _evaluate_one(
    rel_path: Path,
    tests_dir: Path,
    tmp_dir: Path,
    mode: str,
    timeout_s: float,
    qbe_cmd: Sequence[str],
    qbe_env: dict[str, str],
    up_cmd: Sequence[str] | None,
    up_env: dict[str, str] | None,
    runner: Callable[[Sequence[str], Path, dict[str, str], float], RunOutput],
) -> SuiteResult:
    rel_str = rel_path.as_posix()
    if is_na_test(rel_path):
        return SuiteResult(
            file=rel_str,
            qbe_status="NA",
            qbe_note="not applicable (tests built-in missing Std.Tactic.BVDecide import error)",
            up_status="NA" if mode == "compare" else None,
            up_note="skipped (N/A for bv_decide_qbe)" if mode == "compare" else "",
        )

    src_path = tests_dir / rel_path
    qbe_file = tmp_dir / rel_path
    qbe_file.parent.mkdir(parents=True, exist_ok=True)
    qbe_file.write_text(rewrite_for_qbe(src_path.read_text(encoding="utf-8")), encoding="utf-8")

    up_status: str | None = None
    up_time_s: float | None = None
    up_rc: int | None = None
    up_note = ""
    if mode == "compare":
        assert up_cmd is not None and up_env is not None
        up_run = runner(up_cmd, src_path, up_env, timeout_s)
        up_time_s = up_run.elapsed_s
        up_rc = up_run.returncode
        if up_run.timed_out:
            up_status = "FAIL"
            up_note = f"upstream timeout after {up_run.elapsed_s:.2f}s"
        elif up_run.returncode == 0:
            up_status = "PASS"
        else:
            up_status = "FAIL"
            up_note = f"upstream rc={up_run.returncode}"

    qbe_run = runner(qbe_cmd, qbe_file, qbe_env, timeout_s)
    qbe_status, qbe_note, diff_kinds = classify_qbe_output(qbe_file, qbe_run)
    return SuiteResult(
        file=rel_str,
        qbe_status=qbe_status,
        qbe_time_s=qbe_run.elapsed_s,
        qbe_rc=qbe_run.returncode,
        qbe_note=qbe_note,
        diff_kinds=diff_kinds,
        up_status=up_status,
        up_time_s=up_time_s,
        up_rc=up_rc,
        up_note=up_note,
    )


def run_suite(
    tests_dir: Path,
    mode: str = "compat",
    timeout_s: float = 120.0,
    jobs: int = 1,
    filter_regex: str | None = None,
    bv_dir: Path | None = None,
    repo_root: Path | None = None,
    lean_prefix: Path | None = None,
    runner: Callable[[Sequence[str], Path, dict[str, str], float], RunOutput] | None = None,
    skip_artifact_check: bool = False,
    on_result: Callable[[SuiteResult], None] | None = None,
) -> tuple[list[SuiteResult], dict[str, int], dict[str, float | int | None]]:
    """Run compatibility or compare suite and return `(results, counts, compare_summary)`."""
    if jobs < 1:
        raise ValueError(f"--jobs must be >= 1, got {jobs}")
    if timeout_s <= 0:
        raise ValueError(f"--timeout must be > 0, got {timeout_s}")

    active_runner = run_lean_file if runner is None else runner
    rel_paths = discover_tests(tests_dir, filter_regex)
    resolved_bv_dir = (bv_dir or resolve_bv_decide_qbe_dir()).resolve()
    resolved_repo_root = (repo_root or resolved_bv_dir.parent).resolve()
    if not skip_artifact_check:
        validate_qbe_artifacts(resolved_bv_dir, resolved_repo_root)
    resolved_prefix = lean_prefix or resolve_lean_prefix()

    qbe_cmd, qbe_env = build_qbe_invocation(resolved_bv_dir, resolved_repo_root, resolved_prefix)
    up_cmd, up_env = (
        build_upstream_invocation(resolved_prefix) if mode == "compare" else (None, None)
    )

    with tempfile.TemporaryDirectory(prefix="bv_decide_qbe_suite_") as tmp_root:
        tmp_dir = Path(tmp_root)
        if jobs == 1:
            results = []
            for rel in rel_paths:
                res = _evaluate_one(
                    rel, tests_dir, tmp_dir, mode, timeout_s,
                    qbe_cmd, qbe_env, up_cmd, up_env, active_runner,
                )
                results.append(res)
                if on_result is not None:
                    on_result(res)
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
                futures = [
                    pool.submit(
                        _evaluate_one,
                        rel, tests_dir, tmp_dir, mode, timeout_s,
                        qbe_cmd, qbe_env, up_cmd, up_env, active_runner,
                    )
                    for rel in rel_paths
                ]
                results = []
                for f in futures:
                    res = f.result()
                    results.append(res)
                    if on_result is not None:
                        on_result(res)

    counts = summarize_counts(results)
    compare_summary = compute_compare_summary(results) if mode == "compare" else {}
    return results, counts, compare_summary


def format_header(mode: str) -> str:
    """Return the table header line for `mode`."""
    if mode == "compare":
        return (
            f"{'File':42s} {'QBE':18s} {'Up':6s} {'Up(s)':>8s} {'QBE(s)':>8s} "
            f"{'QBE/Up':>8s} {'Speedup':>8s}  Note"
        )
    return f"{'File':42s} {'Status':18s} {'Time(s)':>8s}  Note"


def format_row(r: SuiteResult, mode: str) -> str:
    """Format a single `SuiteResult` table row."""
    if mode == "compare":
        up_t = f"{r.up_time_s:8.2f}" if r.up_time_s is not None else f"{'-':>8s}"
        qbe_t = f"{r.qbe_time_s:8.2f}" if r.qbe_time_s is not None else f"{'-':>8s}"
        if (
            r.up_time_s
            and r.qbe_time_s
            and r.up_status == "PASS"
            and r.qbe_status in ("PASS", "PASS_EXPECTED_DIFF")
        ):
            ratio = f"{r.qbe_time_s / r.up_time_s:7.3f}x"
            spd = f"{r.up_time_s / r.qbe_time_s:7.2f}x"
        else:
            ratio = f"{'-':>8s}"
            spd = f"{'-':>8s}"
        up_st = r.up_status or "-"
        note = "; ".join(n for n in (r.qbe_note, r.up_note) if n)
        return (
            f"{r.file:42s} {r.qbe_status:18s} {up_st:6s} {up_t} {qbe_t} "
            f"{ratio} {spd}  {note}"
        )
    qbe_t = f"{r.qbe_time_s:8.2f}" if r.qbe_time_s is not None else f"{'-':>8s}"
    return f"{r.file:42s} {r.qbe_status:18s} {qbe_t}  {r.qbe_note}"


def format_summary(
    counts: dict[str, int],
    compare_summary: dict[str, float | int | None],
    mode: str,
) -> str:
    """Format compatibility and compare summary lines."""
    compat_ok = counts["pass"] + counts["pass_expected_diff"]
    lines = [
        "",
        f"Summary ({mode}): total={counts['total']} compat_pass={compat_ok} "
        f"(verbatim={counts['pass']}, expected_diff={counts['pass_expected_diff']}) "
        f"na={counts['na']} fail={counts['fail']}",
    ]
    if mode == "compare":
        n_paired = compare_summary.get("paired_count", 0)
        tot_up = compare_summary.get("total_up_s", 0.0)
        tot_qbe = compare_summary.get("total_qbe_s", 0.0)
        w_am = compare_summary.get("w_am")
        w_gm = compare_summary.get("w_gm")
        spd_am = compare_summary.get("speedup_am")
        spd_gm = compare_summary.get("speedup_gm")
        if w_am is not None and w_gm is not None and spd_am is not None and spd_gm is not None:
            lines.append(
                f"Compare (n={n_paired}): up_total={tot_up:.2f}s qbe_total={tot_qbe:.2f}s "
                f"W-AM={w_am:.3f}x ({spd_am:.2f}x) W-GM={w_gm:.3f}x ({spd_gm:.2f}x)"
            )
        else:
            lines.append("Compare (n=0): no paired passing runs to aggregate")
    return "\n".join(lines)


def format_report(
    results: Sequence[SuiteResult],
    counts: dict[str, int],
    compare_summary: dict[str, float | int | None],
    mode: str,
) -> str:
    """Format human-readable table and summary block."""
    lines = [format_header(mode)]
    lines.extend(format_row(r, mode) for r in results)
    lines.append(format_summary(counts, compare_summary, mode))
    return "\n".join(lines)


def build_arg_parser() -> argparse.ArgumentParser:
    """Create CLI argument parser for `run_upstream_suite.py`."""
    parser = argparse.ArgumentParser(
        description="Run upstream Lean 4 bv_decide compatibility & head-to-head benchmark suite."
    )
    parser.add_argument(
        "--lean4-tests-dir",
        type=Path,
        required=True,
        help="Path to upstream Lean 4 tests directory containing elab/ and elab_bench/.",
    )
    parser.add_argument(
        "--mode",
        choices=("compat", "compare"),
        default="compat",
        help="Run mode: compat (bv_decide_qbe only) or compare (head-to-head vs upstream).",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=120.0,
        help="Per-file subprocess timeout in seconds (default: 120).",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="Concurrent workers (default: 1 for clean timing).",
    )
    parser.add_argument(
        "--filter",
        type=str,
        default=None,
        help="Optional regex matched against relative test paths (e.g. elab/bv_arith.lean).",
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=None,
        help="Optional path to write machine-readable JSON results.",
    )
    parser.add_argument(
        "--bv-decide-qbe-dir",
        type=Path,
        default=None,
        help="Optional path to built bv_decide_qbe/ directory (defaults to script parent).",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entrypoint."""
    parser = build_arg_parser()
    args = parser.parse_args(argv)

    header_printed = False

    def emit_row(r: SuiteResult) -> None:
        nonlocal header_printed
        if not header_printed:
            print(format_header(args.mode), flush=True)
            header_printed = True
        print(format_row(r, args.mode), flush=True)

    try:
        results, counts, compare_summary = run_suite(
            tests_dir=args.lean4_tests_dir,
            mode=args.mode,
            timeout_s=args.timeout,
            jobs=args.jobs,
            filter_regex=args.filter,
            bv_dir=args.bv_decide_qbe_dir,
            on_result=emit_row,
        )
    except (FileNotFoundError, ValueError, RuntimeError, re.error) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if not header_printed:
        print(format_header(args.mode), flush=True)
    print(format_summary(counts, compare_summary, args.mode), flush=True)

    if args.out_json is not None:
        payload = {
            "mode": args.mode,
            "timeout_s": args.timeout,
            "jobs": args.jobs,
            "filter": args.filter,
            "lean4_tests_dir": str(args.lean4_tests_dir),
            "counts": counts,
            "compare": compare_summary if args.mode == "compare" else None,
            "results": [asdict(r) for r in results],
        }
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    return 0 if counts["fail"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
