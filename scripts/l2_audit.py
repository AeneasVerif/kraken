#!/usr/bin/env python3
"""Single-command deterministic L2 PR audit CLI (N11 + N9).

Consolidates mechanical L2 verification into one structured JSON report:
  1. Zero-disk `git merge-tree --write-tree` against `refs/heads/leanqbe/main`
  2. Exact diff stats, `git diff --check`, and optional `--allow <regex>` scope
  3. Static `.lean` hygiene: `<= 100` cols, `< 2,500` LOC, `0` `@[expose]` on
     theorems/lemmas, `0` banned tokens, and `import all` audit
  4. `sync_hubs.py --check --strict` and `check_firewall.py --require-isa`
     (+ `--data-proof` automatically when supported)
  5. `rdeps_scope.py` + N9 `<60s` Cross-Subsystem Core Canary Frontier trigger
  6. Kernel `collectAxioms` (`⊆ std3`) + `!ci.isUnsafe` audit
  7. Optional `--abi-diff` and C0 SHA-256 memoized ASan+UBSan verification
"""

from __future__ import annotations

import argparse
import collections
import contextlib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Iterator

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from lean_imports import (  # noqa: E402
    LEGACY_CERT_RE,
    mod_to_rel_path,
    parse_imports,
    rel_path_to_mod,
    strip_comments_line,
)
from rdeps_scope import (  # noqa: E402
    BARRELS,
    EXE_ROOT_TO_TARGET,
    _is_kraken_path,
    compute_rdeps,
    modules_to_lake_targets,
)

MAX_LOC = 2500
MAX_COL = 100
CANARY_RDEPS_THRESHOLD = 50
RDEPS_BUILD_CAP = 250
C0_ASAN_CACHE_PATH = Path("/tmp/leanqbe_verified_c0_asan.json")

CANARY_FRONTIER: tuple[str, ...] = (
    "LeanQbe.T.CoreHub",
    "LeanQbe.T.PassFlatKit",
    "LeanQbe.T.Wasm.BulkSafety",
    "LeanQbe.T.LeanLCNF.LcnfC0RtProofCommon",
    "LeanQbe.T.LeanLRC.Runtime",
    "LeanQbe.T.Frontend.Bedrock2.ToT",
    "LeanQbe.T.MainLinkReuseLegalCalls",
    "LeanQbe.T.Amd64.Targ",
    "LeanQbe.T.Arm64.Targ",
    "LeanQbe.T.Examples.Kissat.FullFidelityBcpProof1",
    "LeanQbe.T.Examples.Kissat.FullFidelityBvaProof1a",
)

CORE_TRIGGER_RE = re.compile(
    r"^(?:Main(?:Arm64)?\.lean"
    r"|LeanQbe/T/(?:IL|Target|Main[^/]*|Inline[^/]*|MainCertInline[^/]*)\.lean"
    r"|LeanQbe/T/Logic/.*\.lean"
    r"|LeanQbe/T/(?:Amd64|Arm64)/Targ(?:Lemmas)?\.lean)$"
)

BANNED_TOKEN_RE = re.compile(
    r"\b(?:sorry|admit|bv_decide|native_decide|ofReduceBool|ofReduceNat"
    r"|trustCompiler)\b"
    r"|decide\s+\+native"
    r"|@\[[^\]]*\b(?:implemented_by|extern)\b"
)
AXIOM_DECL_RE = re.compile(
    r"(?:^|;)\s*(?:(?:public|private|protected|unsafe|noncomputable|"
    r"local|scoped)\s+)*axiom\b"
)
BAD_IMPORT_ALL_RE = re.compile(
    r"^\s*(?:public\s+(?:meta\s+)?import\s+all\b"
    r"|(?:meta\s+)?import\s+all\s+LeanQbe\b)"
)
ANY_IMPORT_ALL_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+all\b"
)
CONFLICT_RE = re.compile(r"^(?:<{7}|={7}|>{7})(?: |$)")
STRING_LIT_RE = re.compile(r'"(?:\\.|[^"\\])*"')
EXPOSE_ATTR_RE = re.compile(r"@\[[^\]]*\bexpose\b[^\]]*\]")
THM_DECL_RE = re.compile(
    r"^(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma)\b"
)
MODIFIER_ONLY_RE = re.compile(
    r"^(?:@\[[^\]]*\]|public|private|protected|noncomputable|unsafe)+$"
)
X64_PFX = ("Kraken.X64", "LeanQbe.T.Amd64.")
ARM_PFX = ("Kraken.AArch64", "LeanQbe.T.Arm64.")


def systemd_scope_available() -> bool:
    """Return True if `systemd-run --user --scope` works in this session."""
    if shutil.which("systemd-run") is None:
        return False
    res = subprocess.run(
        ["systemd-run", "--user", "--scope", "true"],
        capture_output=True,
        check=False,
    )
    return res.returncode == 0


def wrap_build_cmd(
    cmd: list[str],
    *,
    timeout_sec: int = 600,
    memory_max: str = "12G",
    use_systemd: bool | None = None,
) -> list[str]:
    """Wrap command in `timeout` + `systemd-run --user --scope` + Lake env."""
    env_prefix = [
        "env",
        "LAKE_ARTIFACT_CACHE=true",
        "LAKE_RESTORE_ARTIFACTS=true",
        "LAKE_JOBS=2",
        "LEAN_NUM_THREADS=2",
    ]
    base_cmd = ["timeout", "--foreground", str(timeout_sec), *env_prefix, *cmd]
    scoped = systemd_scope_available() if use_systemd is None else use_systemd
    if scoped:
        return [
            "systemd-run",
            "--user",
            "--scope",
            "--quiet",
            "-p",
            f"MemoryMax={memory_max}",
            "-p",
            "OOMPolicy=kill",
            *base_cmd,
        ]
    return base_cmd


def resolve_commit(repo: Path, ref: str) -> str:
    """Resolve `ref` to a 40-char commit SHA or raise RuntimeError."""
    res = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "--verify", f"{ref}^{{commit}}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        raise RuntimeError(f"cannot resolve commit '{ref}': {res.stderr.strip()}")
    return res.stdout.strip()


def run_merge_tree(repo: Path, base_sha: str, target_sha: str) -> dict[str, object]:
    """Run zero-disk `git merge-tree --write-tree` between two commits."""
    res = subprocess.run(
        ["git", "-C", str(repo), "merge-tree", "--write-tree", base_sha, target_sha],
        capture_output=True,
        text=True,
        check=False,
    )
    lines = [ln.strip() for ln in res.stdout.splitlines() if ln.strip()]
    tree = lines[0] if lines and re.fullmatch(r"[0-9a-f]{40}", lines[0]) else None
    conflicts = [ln for ln in lines[1:] if "CONFLICT" in ln]
    return {
        "status": "pass" if res.returncode == 0 else "fail",
        "clean": res.returncode == 0,
        "tree": tree,
        "conflicts": conflicts[:20],
        "stderr": res.stderr.strip()[:400] if res.returncode != 0 else "",
    }


def collect_diff_stats(
    repo: Path,
    base_sha: str,
    target_sha: str,
    allow_regex: str | None = None,
) -> dict[str, object]:
    """Compute exact diff stats, whitespace check, and `--allow` compliance."""
    ns_res = subprocess.run(
        ["git", "-C", str(repo), "diff", "--name-status", base_sha, target_sha],
        capture_output=True,
        text=True,
        check=True,
    )
    num_res = subprocess.run(
        ["git", "-C", str(repo), "diff", "--numstat", base_sha, target_sha],
        capture_output=True,
        text=True,
        check=True,
    )
    chk_res = subprocess.run(
        ["git", "-C", str(repo), "diff", "--check", base_sha, target_sha],
        capture_output=True,
        text=True,
        check=False,
    )

    files: list[str] = []
    deletions: list[str] = []
    statuses: dict[str, str] = {}
    for ln in ns_res.stdout.splitlines():
        if not ln.strip():
            continue
        parts = ln.split("\t")
        st = parts[0]
        path = parts[-1]
        files.append(path)
        statuses[path] = st
        if st.startswith("D"):
            deletions.append(path)

    added_loc = 0
    deleted_loc = 0
    for ln in num_res.stdout.splitlines():
        if not ln.strip():
            continue
        parts = ln.split("\t", 2)
        if len(parts) < 3:
            continue
        if parts[0].isdigit():
            added_loc += int(parts[0])
        if parts[1].isdigit():
            deleted_loc += int(parts[1])

    disallowed: list[str] = []
    if allow_regex:
        pat = re.compile(allow_regex)
        disallowed = [f for f in files if not pat.search(f)]

    ws_issues = [ln for ln in chk_res.stdout.splitlines() if ln.strip()]
    ok = (chk_res.returncode == 0) and (not disallowed)
    return {
        "status": "pass" if ok else "fail",
        "files_changed": len(files),
        "added_loc": added_loc,
        "deleted_loc": deleted_loc,
        "files": files,
        "statuses": statuses,
        "deletions": deletions,
        "disallowed_files": disallowed,
        "whitespace_ok": chk_res.returncode == 0,
        "whitespace_issues": ws_issues[:20],
    }


def _clean_lean_code_lines(lines: list[str]) -> list[tuple[int, str, str]]:
    """Return `[(lineno, raw_line, code_without_comments_or_strings)]`."""
    out: list[tuple[int, str, str]] = []
    depth = 0
    for idx, raw in enumerate(lines, 1):
        code, depth, _ = strip_comments_line(raw, depth)
        code_nostr = STRING_LIT_RE.sub('""', code) if code else ""
        out.append((idx, raw, code_nostr))
    return out


def audit_lean_text(rel_path: str, text: str) -> dict[str, object]:
    """Audit a single `.lean` source string for hygiene invariants."""
    lines = text.splitlines()
    loc = len(lines)
    over_loc = loc >= MAX_LOC
    long_lines: list[dict[str, object]] = []
    expose_on_thm: list[int] = []
    banned_hits: list[dict[str, object]] = []
    bad_import_all: list[int] = []
    total_import_all = 0
    conflicts: list[int] = []

    pending_expose = False
    cleaned = _clean_lean_code_lines(lines)
    for idx, raw, code in cleaned:
        if CONFLICT_RE.match(raw):
            conflicts.append(idx)
        if len(raw) > MAX_COL and not raw.strip().startswith(("--", "/-", '"')):
            long_lines.append({"line": idx, "cols": len(raw)})
        if not code:
            continue
        if BAD_IMPORT_ALL_RE.match(code):
            bad_import_all.append(idx)
        if ANY_IMPORT_ALL_RE.match(code):
            total_import_all += 1
        if BANNED_TOKEN_RE.search(code) or AXIOM_DECL_RE.search(code):
            banned_hits.append({"line": idx, "text": code.strip()[:90]})

        # Track `@[expose]` applying to a theorem/lemma on same or later line.
        has_expose = bool(EXPOSE_ATTR_RE.search(code))
        after_expose = EXPOSE_ATTR_RE.sub("", code).strip()
        if THM_DECL_RE.match(after_expose) and (has_expose or pending_expose):
            expose_on_thm.append(idx)
            pending_expose = False
        elif has_expose:
            if not after_expose or MODIFIER_ONLY_RE.match(after_expose):
                pending_expose = True
            else:
                pending_expose = False
        elif pending_expose:
            if not MODIFIER_ONLY_RE.match(code):
                pending_expose = False

    return {
        "file": rel_path,
        "loc": loc,
        "over_loc": over_loc,
        "long_lines": long_lines,
        "expose_on_thm": expose_on_thm,
        "banned_hits": banned_hits,
        "bad_import_all": bad_import_all,
        "total_import_all": total_import_all,
        "conflicts": conflicts,
    }


def read_blob_at_commit(repo: Path, commit: str, rel_path: str) -> str | None:
    """Read tracked file text at `commit` via `git show` (zero disk)."""
    res = subprocess.run(
        ["git", "-C", str(repo), "show", f"{commit}:{rel_path}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        return None
    return res.stdout


def audit_static_hygiene(
    repo: Path,
    target_sha: str,
    changed_files: list[str],
    deletions: set[str],
) -> dict[str, object]:
    """Run LOC, line-width, `@[expose]`, banned-token, and `import all` checks."""
    lean_files = [
        f for f in changed_files if f.endswith(".lean") and f not in deletions
    ]
    file_reports: list[dict[str, object]] = []
    violations: list[str] = []
    total_import_all = 0
    max_loc = 0
    max_col = 0

    for rel in lean_files:
        txt = read_blob_at_commit(repo, target_sha, rel)
        if txt is None:
            continue
        rep = audit_lean_text(rel, txt)
        file_reports.append(rep)
        loc = int(rep["loc"])  # type: ignore[arg-type]
        max_loc = max(max_loc, loc)
        total_import_all += int(rep["total_import_all"])  # type: ignore[arg-type]
        for ln_info in rep["long_lines"]:  # type: ignore[attr-defined]
            max_col = max(max_col, int(ln_info["cols"]))
        if rep["over_loc"]:
            violations.append(f"{rel}: {loc} LOC >= {MAX_LOC}")
        if rep["long_lines"]:
            first = rep["long_lines"][0]  # type: ignore[index]
            violations.append(
                f"{rel}:{first['line']}: width {first['cols']} > {MAX_COL}"
            )
        for ln in rep["expose_on_thm"]:  # type: ignore[attr-defined]
            violations.append(f"{rel}:{ln}: @[expose] on theorem/lemma")
        for hit in rep["banned_hits"]:  # type: ignore[attr-defined]
            violations.append(
                f"{rel}:{hit['line']}: banned token in `{hit['text']}`"
            )
        for ln in rep["bad_import_all"]:  # type: ignore[attr-defined]
            violations.append(f"{rel}:{ln}: forbidden `import all`")
        for ln in rep["conflicts"]:  # type: ignore[attr-defined]
            violations.append(f"{rel}:{ln}: merge conflict marker")

    return {
        "status": "pass" if not violations else "fail",
        "checked_lean_files": len(file_reports),
        "max_loc": max_loc,
        "max_col_violation": max_col,
        "total_import_all": total_import_all,
        "violations": violations[:40],
    }


@contextlib.contextmanager
def target_worktree_ctx(
    repo: Path,
    target_sha: str,
    *,
    worktree_pool: Path | None,
    dry_run: bool,
) -> Iterator[Path]:
    """Provide a clean checkout worktree at `target_sha`."""
    head_res = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    )
    dirty_res = subprocess.run(
        ["git", "-C", str(repo), "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=False,
    )
    if (
        dry_run
        and head_res.returncode == 0
        and head_res.stdout.strip() == target_sha
        and not dirty_res.stdout.strip()
    ):
        yield repo
        return

    if dry_run or worktree_pool is None:
        with tempfile.TemporaryDirectory(prefix="l2-audit-wt-") as td:
            wt = Path(td) / "wt"
            subprocess.run(
                ["git", "-C", str(repo), "worktree", "add", "--detach", str(wt), target_sha],
                capture_output=True,
                text=True,
                check=True,
            )
            try:
                yield wt
            finally:
                subprocess.run(
                    ["git", "-C", str(repo), "worktree", "remove", "--force", str(wt)],
                    capture_output=True,
                    check=False,
                )
                subprocess.run(
                    ["git", "-C", str(repo), "worktree", "prune"],
                    capture_output=True,
                    check=False,
                )
        return

    # Persistent pooled worktree mode (preserves `.lake/build` cache).
    pool = worktree_pool.resolve()
    if not (pool / ".git").exists():
        pool.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "-C", str(repo), "worktree", "add", "--detach", str(pool), target_sha],
            capture_output=True,
            text=True,
            check=True,
        )
    else:
        subprocess.run(
            ["git", "-C", str(pool), "checkout", "--detach", target_sha],
            capture_output=True,
            text=True,
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(pool), "clean", "-fd", "-e", ".lake"],
            capture_output=True,
            check=False,
        )
    yield pool


def run_sync_hubs_check(wt: Path) -> dict[str, object]:
    """Run `sync_hubs.py --check --strict` against `wt`."""
    script = wt / "scripts" / "sync_hubs.py"
    if not script.is_file():
        script = SCRIPTS_DIR / "sync_hubs.py"
    res = subprocess.run(
        [
            "timeout",
            "60",
            sys.executable,
            "-B",
            str(script),
            "--root",
            str(wt),
            "--check",
            "--strict",
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    return {
        "status": "pass" if res.returncode == 0 else "fail",
        "output": (res.stdout or res.stderr).strip()[:500],
    }


def run_firewall_check(wt: Path) -> dict[str, object]:
    """Run `check_firewall.py --require-isa` (+ `--data-proof` if supported)."""
    script = wt / "scripts" / "check_firewall.py"
    if not script.is_file():
        script = SCRIPTS_DIR / "check_firewall.py"
    help_res = subprocess.run(
        [sys.executable, "-B", str(script), "--help"],
        capture_output=True,
        text=True,
        check=False,
    )
    has_data_proof = "--data-proof" in (help_res.stdout + help_res.stderr)
    cmd = [
        "timeout",
        "60",
        sys.executable,
        "-B",
        str(script),
        "--root",
        str(wt),
        "--require-isa",
        "--json",
    ]
    if has_data_proof:
        cmd.append("--data-proof")
    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    parsed = None
    try:
        parsed = json.loads(res.stdout)
    except json.JSONDecodeError:
        parsed = None
    return {
        "status": "pass" if res.returncode == 0 else "fail",
        "data_proof_flag": has_data_proof,
        "report": parsed if parsed is not None else (res.stdout or res.stderr).strip()[:500],
    }


def compute_exact_lean_rdeps(
    wt: Path, changed_files: list[str]
) -> tuple[list[str], list[str]]:
    """Compute exact non-barrel reverse-import closure of changed `.lean` files."""
    seeds: set[str] = set()
    for f in changed_files:
        if not f.endswith(".lean"):
            continue
        p = wt / f
        if not p.is_file():
            continue
        rel = Path(f)
        if _is_kraken_path(rel):
            continue
        mod = rel_path_to_mod(rel)
        if mod not in BARRELS:
            seeds.add(mod)
    if not seeds:
        return [], []

    raw_ls = subprocess.check_output(
        [
            "git",
            "-C",
            str(wt),
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
            "*.lean",
        ]
    )
    rgraph: dict[str, list[str]] = collections.defaultdict(list)
    for blob in raw_ls.split(b"\0"):
        if not blob:
            continue
        rel = Path(blob.decode("utf-8"))
        if _is_kraken_path(rel):
            continue
        mod = rel_path_to_mod(rel)
        if mod in BARRELS:
            continue
        if mod not in seeds and (
            (rel.parts and rel.parts[0] == "LeanQbeLegacyTest")
            or LEGACY_CERT_RE.match(mod)
        ):
            continue
        full = wt / rel
        if not full.is_file():
            continue
        _, imps = parse_imports(full)
        for imp in imps:
            if imp.module not in BARRELS:
                rgraph[imp.module].append(mod)

    seen = set(seeds)
    q: collections.deque[str] = collections.deque(sorted(seeds))
    while q:
        cur = q.popleft()
        for nxt in rgraph.get(cur, ()):
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return sorted(seeds), sorted(seen)


def plan_rdeps_and_canary(
    wt: Path,
    changed_files: list[str],
    base_sha: str,
) -> dict[str, object]:
    """Compute `rdeps_scope.py` result and N9 Core Canary Frontier targets."""
    capped_mods = compute_rdeps(
        wt,
        changed_files,
        max_rdeps=RDEPS_BUILD_CAP,
        base=base_sha,
        include_legacy=False,
    )
    seeds, exact_mods = compute_exact_lean_rdeps(wt, changed_files)
    core_touched = [f for f in changed_files if CORE_TRIGGER_RE.match(f)]
    canary_triggered = (
        len(exact_mods) > CANARY_RDEPS_THRESHOLD or bool(core_touched)
    )
    present_canary = [
        m for m in CANARY_FRONTIER if (wt / mod_to_rel_path(m)).is_file()
    ]
    absent_canary = [m for m in CANARY_FRONTIER if m not in present_canary]

    build_targets: list[str] = []
    if canary_triggered:
        build_targets.extend(present_canary)
        if capped_mods is not None:
            build_targets.extend(modules_to_lake_targets(capped_mods))
        else:
            build_targets.extend(modules_to_lake_targets(seeds))
    elif capped_mods is not None:
        build_targets.extend(modules_to_lake_targets(capped_mods))
    elif seeds:
        build_targets.extend(modules_to_lake_targets(seeds))

    dedup_targets = sorted(set(build_targets))
    return {
        "rdeps_capped_pass": capped_mods is not None,
        "rdeps_capped_count": len(capped_mods) if capped_mods is not None else None,
        "exact_rdeps_count": len(exact_mods),
        "exact_rdeps_sample": exact_mods[:25],
        "seed_mods": seeds,
        "core_files_touched": core_touched,
        "canary_triggered": canary_triggered,
        "canary_present": present_canary,
        "canary_absent": absent_canary,
        "build_targets": dedup_targets,
    }


def execute_lake_build(
    wt: Path, targets: list[str], timeout_sec: int = 600
) -> dict[str, object]:
    """Run wrapped `lake build --wfail` over `targets`."""
    if not targets:
        return {"status": "skip", "reason": "no_targets", "targets": []}
    cmd = wrap_build_cmd(
        ["lake", "build", "--wfail", *targets], timeout_sec=timeout_sec
    )
    res = subprocess.run(
        cmd, cwd=str(wt), capture_output=True, text=True, check=False
    )
    err_lines = [
        ln
        for ln in (res.stdout + "\n" + res.stderr).splitlines()
        if "error" in ln.lower() or "warning:" in ln.lower()
    ]
    return {
        "status": "pass" if res.returncode == 0 else "fail",
        "returncode": res.returncode,
        "target_count": len(targets),
        "targets": targets,
        "errors": err_lines[:30],
    }


def classify_module_arch(
    wt: Path, mod: str, cache: dict[str, str], stack: set[str]
) -> str:
    """Classify a Lean module as `generic`, `x64`, `arm64`, or `conflict`."""
    if mod in cache:
        return cache[mod]
    if mod == "LeanQbeAmd64" or mod.startswith(X64_PFX):
        cache[mod] = "x64"
        return "x64"
    if mod == "LeanQbeArm64" or mod.startswith(ARM_PFX):
        cache[mod] = "arm64"
        return "arm64"
    if mod in stack:
        return "generic"
    p = wt / mod_to_rel_path(mod)
    if not p.is_file():
        return "generic"
    _, imps = parse_imports(p)
    arches: set[str] = set()
    nxt = stack | {mod}
    for imp in imps:
        sub = classify_module_arch(wt, imp.module, cache, nxt)
        if sub in ("x64", "arm64", "conflict"):
            arches.add(sub)
    if "conflict" in arches or ("x64" in arches and "arm64" in arches):
        res = "conflict"
    elif "x64" in arches:
        res = "x64"
    elif "arm64" in arches:
        res = "arm64"
    else:
        res = "generic"
    cache[mod] = res
    return res


def collect_active_headlines_for_mods(
    wt: Path, mods: set[str]
) -> dict[str, list[str]]:
    """Map audited module -> headline constants from `scripts/headlines.d/*.txt`."""
    hdir = wt / "scripts" / "headlines.d"
    out: dict[str, list[str]] = collections.defaultdict(list)
    if not hdir.is_dir():
        return out
    for fp in sorted(hdir.glob("*.txt")):
        if "legacy" in fp.name:
            continue
        for raw in fp.read_text(encoding="utf-8").splitlines():
            s = raw.strip()
            if not s or s.startswith("#"):
                continue
            parts = s.split()
            if len(parts) >= 2 and parts[0] in mods:
                out[parts[0]].append(parts[1])
    return out


def build_axiom_lean_script(
    groups: list[tuple[str, list[str], list[str]]]
) -> str:
    """Generate a Lean 4 script checking `collectAxioms` + `isUnsafe`."""
    lines = [
        "import Lean",
        "open Lean",
        "private def allowed : Array Name :=",
        "  #[``propext, ``Classical.choice, ``Quot.sound]",
        "private def parseName (s : String) : Name :=",
        '  (s.splitOn ".").foldl (fun acc part => Name.str acc part) .anonymous',
        "private def isLeanQbeOrKraken (n : Name) : Bool :=",
        '  let s := n.toString',
        '  s.startsWith "LeanQbe." || s.startsWith "LeanQbeTest."'
        ' || s.startsWith "Kraken."',
        "private def checkGroup (grp : String)",
        "    (mods consts : List String) : IO Bool := do",
        "  let imps : Array Import := mods.toArray.map fun m =>",
        "    { module := parseName m }",
        "  let env ← importModules imps {} (trustLevel := 0) (loadExts := false)",
        "  let modIdxs := mods.filterMap fun m => env.getModuleIdx? (parseName m)",
        "  let mut targets : Array Name := consts.toArray.map parseName",
        "  let extra := env.constants.fold (init := #[]) fun acc nm _ =>",
        '    if !nm.isInternal && !nm.toString.endsWith "._unsafe_rec" then',
        "      match env.getModuleIdxFor? nm with",
        "      | some idx => if modIdxs.contains idx then acc.push nm else acc",
        "      | none => acc",
        "    else acc",
        "  targets := targets ++ extra",
        "  let ctx : Core.Context := { fileName := \"<audit>\", fileMap := default }",
        "  let st : Core.State := { env := env }",
        "  let ((failed, checked), _) ← (Core.CoreM.toIO (ctx := ctx) (s := st)) do",
        "    let mut failed := false",
        "    let mut checked := 0",
        "    let mut seen : Std.HashSet Name := {}",
        "    for nm in targets do",
        "      if seen.contains nm then continue",
        "      seen := seen.insert nm",
        "      match env.find? nm with",
        "      | none =>",
        '        IO.eprintln s!"FAIL [{grp}] missing constant {nm}"',
        "        failed := true",
        "      | some (.opaqueInfo _) =>",
        "        if isLeanQbeOrKraken nm then",
        '          IO.eprintln s!"FAIL [{grp}] opaque decl {nm}"',
        "          failed := true",
        "      | some ci =>",
        "        if ci.isUnsafe then",
        '          IO.eprintln s!"FAIL [{grp}] unsafe decl {nm}"',
        "          failed := true",
        "        let axs ← Lean.collectAxioms nm",
        "        for ax in axs do",
        "          if !allowed.contains ax then",
        '            IO.eprintln s!"FAIL [{grp}] {nm} disallowed axiom {ax}"',
        "            failed := true",
        "        checked := checked + 1",
        "    return (failed, checked)",
        '  IO.println s!"AXIOM_GROUP {grp} checked={checked} failed={failed}"',
        "  return failed",
        "#eval show IO Unit from do",
        "  initSearchPath (← findSysroot)",
        "  let mut anyFail := false",
    ]
    for grp, mods, consts in groups:
        m_lit = ", ".join(f'"{m}"' for m in mods)
        c_lit = ", ".join(f'"{c}"' for c in consts)
        lines.append(
            f'  if (← checkGroup "{grp}" [{m_lit}] [{c_lit}]) then anyFail := true'
        )
    lines.append('  if anyFail then throw <| IO.userError "axiom/unsafe check failed"')
    return "\n".join(lines) + "\n"


def run_axiom_audit(
    wt: Path,
    built_targets: list[str],
    *,
    dry_run: bool,
) -> dict[str, object]:
    """Run kernel `collectAxioms` + `!isUnsafe` across audited modules."""
    rev_exe = {v: k for k, v in EXE_ROOT_TO_TARGET.items()}
    mods = sorted(
        {
            rev_exe.get(t, t)
            for t in built_targets
            if (wt / mod_to_rel_path(rev_exe.get(t, t))).is_file()
        }
    )
    if not mods:
        return {"status": "skip", "reason": "no_lean_modules", "groups": []}

    headlines = collect_active_headlines_for_mods(wt, set(mods))
    arch_cache: dict[str, str] = {}
    grouped: dict[str, list[str]] = collections.defaultdict(list)
    for m in mods:
        arch = classify_module_arch(wt, m, arch_cache, set())
        grouped[arch].append(m)

    groups: list[tuple[str, list[str], list[str]]] = []
    for arch in ("generic", "x64", "arm64"):
        ms = grouped.get(arch, [])
        if ms:
            cs = [c for m in ms for c in headlines.get(m, [])]
            groups.append((arch, ms, cs))
    for idx, m in enumerate(grouped.get("conflict", []), 1):
        groups.append((f"solo_{idx}", [m], headlines.get(m, [])))

    if dry_run:
        return {
            "status": "planned",
            "groups": [
                {"group": g, "modules": ms, "headline_consts": len(cs)}
                for g, ms, cs in groups
            ],
        }

    # Check in small chunks of <= 12 modules per `importModules` call for fast memory caps.
    script = build_axiom_lean_script(groups)
    cmd = wrap_build_cmd(["lake", "env", "lean", "--stdin"], timeout_sec=180)
    res = subprocess.run(
        cmd,
        cwd=str(wt),
        input=script,
        capture_output=True,
        text=True,
        check=False,
    )
    return {
        "status": "pass" if res.returncode == 0 else "fail",
        "groups": [
            {"group": g, "modules": ms, "headline_consts": len(cs)}
            for g, ms, cs in groups
        ],
        "stdout": res.stdout.strip()[:600],
        "stderr": res.stderr.strip()[:600],
    }


def extract_c0_sha256(
    wt: Path, c0_target: str
) -> tuple[str | None, Path | None, str]:
    """Extract C0-direct C99 into a temp file and return `(sha256, tmp_path, err)`."""
    ext = wt / "bench" / "kissat" / "extract_c0_direct.py"
    if not ext.is_file():
        return None, None, f"missing {ext}"
    fd, raw_path = tempfile.mkstemp(prefix="l2-c0-", suffix=".c")
    os.close(fd)
    out_p = Path(raw_path)
    res = subprocess.run(
        [
            "timeout",
            "30",
            sys.executable,
            "-B",
            str(ext),
            "--target",
            c0_target,
            "--out",
            str(out_p),
        ],
        cwd=str(wt),
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        out_p.unlink(missing_ok=True)
        return None, None, (res.stderr or res.stdout).strip()[:400]
    digest = hashlib.sha256(out_p.read_bytes()).hexdigest()
    return digest, out_p, ""


def load_c0_memo(cache_path: Path) -> dict[str, object]:
    """Load `/tmp/leanqbe_verified_c0_asan.json` safely."""
    if not cache_path.is_file():
        return {}
    try:
        data = json.loads(cache_path.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except (json.JSONDecodeError, OSError):
        return {}


def save_c0_memo(cache_path: Path, data: dict[str, object]) -> None:
    """Atomically persist C0 SHA-256 ASan verification memo cache."""
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_raw = tempfile.mkstemp(
        prefix=cache_path.name + ".", dir=str(cache_path.parent)
    )
    os.close(fd)
    tmp_p = Path(tmp_raw)
    tmp_p.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    os.replace(tmp_p, cache_path)


def run_c0_asan_check(
    wt: Path,
    c0_target: str | None,
    target_sha: str,
    *,
    dry_run: bool,
    cache_path: Path = C0_ASAN_CACHE_PATH,
) -> dict[str, object]:
    """Run SHA-256 memoized C0-direct ASan+UBSan canary verification."""
    if not c0_target:
        return {"status": "skip", "reason": "not_requested"}
    digest, tmp_c, err = extract_c0_sha256(wt, c0_target)
    if tmp_c is not None:
        tmp_c.unlink(missing_ok=True)
    if digest is None:
        return {"status": "fail", "target": c0_target, "error": err}

    memo_key = f"{c0_target}:{digest}"
    memo = load_c0_memo(cache_path)
    if memo.get(memo_key, {}).get("verified") is True:  # type: ignore[union-attr]
        return {
            "status": "pass",
            "target": c0_target,
            "c0_sha256": digest,
            "memo_hit": True,
        }
    if dry_run:
        return {
            "status": "planned",
            "target": c0_target,
            "c0_sha256": digest,
            "memo_hit": False,
        }

    with tempfile.TemporaryDirectory(prefix="l2-c0asan-") as td:
        td_p = Path(td)
        build_sh = wt / "bench" / "kissat" / "build_c0_direct.sh"
        bin_path = td_p / f"bench_c0direct_{c0_target}_asan"
        bres = subprocess.run(
            [
                "timeout",
                "120",
                "bash",
                str(build_sh),
                "--target",
                c0_target,
                "--asan",
                "--out-dir",
                str(td_p / "build"),
                "--out",
                str(bin_path),
            ],
            cwd=str(wt),
            capture_output=True,
            text=True,
            check=False,
        )
        if bres.returncode != 0:
            return {
                "status": "fail",
                "target": c0_target,
                "c0_sha256": digest,
                "memo_hit": False,
                "error": (bres.stderr or bres.stdout).strip()[:400],
            }

        cnf_dir = td_p / "cnfs"
        gen_py = wt / "bench" / "kissat" / "gen_canary_cnfs.py"
        gres = subprocess.run(
            ["timeout", "60", sys.executable, "-B", str(gen_py), str(cnf_dir)],
            cwd=str(wt),
            capture_output=True,
            text=True,
            check=False,
        )
        if gres.returncode != 0:
            return {
                "status": "fail",
                "target": c0_target,
                "c0_sha256": digest,
                "error": (gres.stderr or gres.stdout).strip()[:400],
            }
        cnfs = sorted(str(p) for p in cnf_dir.glob("*.cnf"))
        if not cnfs:
            return {
                "status": "fail",
                "target": c0_target,
                "c0_sha256": digest,
                "error": "no canary CNFs generated",
            }
        rres = subprocess.run(
            [
                "timeout",
                "300",
                str(bin_path),
                "--poison-work",
                "67108864",
                "2000000",
                *cnfs,
            ],
            cwd=str(wt),
            capture_output=True,
            text=True,
            check=False,
        )
        if rres.returncode != 0:
            return {
                "status": "fail",
                "target": c0_target,
                "c0_sha256": digest,
                "memo_hit": False,
                "error": (rres.stderr or rres.stdout).strip()[:500],
            }

    memo[memo_key] = {
        "verified": True,
        "target": c0_target,
        "c0_sha256": digest,
        "commit": target_sha,
    }
    save_c0_memo(cache_path, memo)
    return {
        "status": "pass",
        "target": c0_target,
        "c0_sha256": digest,
        "memo_hit": False,
        "canaries_run": len(cnfs),
    }


def _dump_mod_signatures(wt: Path, mod: str) -> dict[str, str] | None:
    """Dump public constant type strings for `mod` via Lean `Environment`."""
    lean_code = "\n".join(
        [
            "import Lean",
            "open Lean Meta",
            "#eval show IO Unit from do",
            "  initSearchPath (← findSysroot)",
            f"  let env ← importModules #[{{ module := `{mod} }}] {{}} (loadExts := false)",
            "  let targetIdx := env.getModuleIdx? `" + mod,
            "  let names := env.constants.fold (init := #[]) fun acc nm _ =>",
            "    if !nm.isInternal && env.getModuleIdxFor? nm == targetIdx then",
            "      acc.push nm",
            "    else acc",
            '  let ctx : Core.Context := { fileName := "<abi>", fileMap := default }',
            "  let st : Core.State := { env := env }",
            "  let _ ← (Core.CoreM.toIO (ctx := ctx) (s := st)) <| MetaM.run' do",
            "    for nm in names do",
            "      if let some ci := env.find? nm then",
            "        let rawTy := (← ppExpr ci.type).pretty (width := 1000)",
            '        let tyStr := String.intercalate " " (rawTy.splitOn "\\n")',
            '        IO.println s!"SIG\\t{nm}\\t{ci.levelParams.length}\\t{tyStr}"',
        ]
    )
    cmd = wrap_build_cmd(["lake", "env", "lean", "--stdin"], timeout_sec=120)
    res = subprocess.run(
        cmd, cwd=str(wt), input=lean_code, capture_output=True, text=True, check=False
    )
    if res.returncode != 0:
        return None
    sigs: dict[str, str] = {}
    for ln in res.stdout.splitlines():
        if ln.startswith("SIG\t"):
            parts = ln.split("\t", 3)
            if len(parts) == 4:
                sigs[parts[1]] = f"{parts[2]}:{parts[3]}"
    return sigs


def run_abi_diff(
    repo: Path,
    base_sha: str,
    target_wt: Path,
    changed_files: list[str],
    deletions: set[str],
    *,
    dry_run: bool,
) -> dict[str, object]:
    """Check public constant ABI parity for modified `LeanQbe/` modules."""
    common_mods: list[str] = []
    for f in changed_files:
        if not f.startswith("LeanQbe/") or not f.endswith(".lean") or f in deletions:
            continue
        if read_blob_at_commit(repo, base_sha, f) is not None:
            mod = rel_path_to_mod(Path(f))
            if mod not in BARRELS:
                common_mods.append(mod)
    if not common_mods:
        return {"status": "skip", "reason": "no_modified_existing_modules", "modules": []}
    if dry_run:
        return {"status": "planned", "modules": common_mods}

    # Build common modules at target and compare against temporary base checkout.
    changes: list[dict[str, object]] = []
    with target_worktree_ctx(
        repo, base_sha, worktree_pool=None, dry_run=True
    ) as base_wt:
        bres = execute_lake_build(base_wt, common_mods, timeout_sec=300)
        if bres["status"] != "pass":
            return {"status": "fail", "reason": "base_build_failed", "detail": bres}
        for mod in common_mods:
            bsig = _dump_mod_signatures(base_wt, mod)
            tsig = _dump_mod_signatures(target_wt, mod)
            if bsig is None or tsig is None:
                changes.append({"module": mod, "error": "sig_dump_failed"})
                continue
            removed = sorted(set(bsig) - set(tsig))
            changed_tys = sorted(
                k for k in (set(bsig) & set(tsig)) if bsig[k] != tsig[k]
            )
            if removed or changed_tys:
                changes.append(
                    {
                        "module": mod,
                        "removed": removed[:20],
                        "changed_types": changed_tys[:20],
                    }
                )
    return {
        "status": "pass" if not changes else "fail",
        "modules": common_mods,
        "abi_diffs": changes,
    }


def run_audit(
    repo: Path,
    base_ref: str,
    target_ref: str,
    *,
    main_ref: str = "refs/heads/leanqbe/main",
    worktree_pool: Path | None = Path("/var/tmp/wt-pool/l2"),
    allow_regex: str | None = None,
    c0_target: str | None = None,
    abi_diff: bool = False,
    dry_run: bool = False,
) -> dict[str, object]:
    """Execute the full N11 + N9 audit pipeline and return JSON report."""
    base_sha = resolve_commit(repo, base_ref)
    target_sha = resolve_commit(repo, target_ref)
    try:
        main_sha = resolve_commit(repo, main_ref)
    except RuntimeError:
        main_sha = base_sha

    merge_res = run_merge_tree(repo, main_sha, target_sha)
    diff_res = collect_diff_stats(repo, base_sha, target_sha, allow_regex=allow_regex)
    changed_files: list[str] = diff_res["files"]  # type: ignore[assignment]
    deletions = set(diff_res["deletions"])  # type: ignore[arg-type]

    hygiene_res = audit_static_hygiene(repo, target_sha, changed_files, deletions)

    with target_worktree_ctx(
        repo,
        target_sha,
        worktree_pool=worktree_pool,
        dry_run=dry_run,
    ) as wt:
        hubs_res = run_sync_hubs_check(wt)
        fw_res = run_firewall_check(wt)
        rdeps_info = plan_rdeps_and_canary(wt, changed_files, base_sha)
        targets: list[str] = rdeps_info["build_targets"]  # type: ignore[assignment]

        if dry_run:
            build_res: dict[str, object] = {
                "status": "planned",
                "target_count": len(targets),
                "targets": targets,
            }
        else:
            build_res = execute_lake_build(wt, targets)

        if build_res["status"] == "fail":
            axiom_res: dict[str, object] = {
                "status": "skip",
                "reason": "build_failed",
            }
        else:
            axiom_res = run_axiom_audit(wt, targets, dry_run=dry_run)

        abi_res: dict[str, object] = (
            run_abi_diff(
                repo,
                base_sha,
                wt,
                changed_files,
                deletions,
                dry_run=dry_run,
            )
            if abi_diff
            else {"status": "skip", "reason": "not_requested"}
        )
        c0_res = run_c0_asan_check(
            wt, c0_target, target_sha, dry_run=dry_run
        )

    steps = {
        "merge_tree": merge_res,
        "diff_stats": diff_res,
        "static_hygiene": hygiene_res,
        "sync_hubs": hubs_res,
        "check_firewall": fw_res,
        "rdeps_canary": rdeps_info,
        "lake_build": build_res,
        "axiom_audit": axiom_res,
        "abi_diff": abi_res,
        "c0_asan": c0_res,
    }
    failed = [
        name
        for name, rep in steps.items()
        if isinstance(rep, dict) and rep.get("status") == "fail"
    ]
    return {
        "ok": not failed,
        "mode": "dry-run" if dry_run else "audit",
        "base": base_sha,
        "target": target_sha,
        "main_ref": main_sha,
        "failed_steps": failed,
        "steps": steps,
    }


def format_human(report: dict[str, object]) -> str:
    """Render concise human-readable L2 audit summary."""
    st = report["steps"]  # type: ignore[index]
    rc = st["rdeps_canary"]  # type: ignore[index]
    ds = st["diff_stats"]  # type: ignore[index]
    verdict = "PASS" if report["ok"] else "FAIL"
    lines = [
        f"l2_audit {verdict} ({report['mode']}): "
        f"target={str(report['target'])[:8]} vs base={str(report['base'])[:8]}",
        f"  merge-tree: {st['merge_tree']['status']} "
        f"(conflicts={len(st['merge_tree']['conflicts'])})",
        f"  diff: {ds['files_changed']} files (+{ds['added_loc']}/-{ds['deleted_loc']}), "
        f"status={ds['status']}",
        f"  hygiene: {st['static_hygiene']['status']} "
        f"(max_loc={st['static_hygiene']['max_loc']}, "
        f"import_all={st['static_hygiene']['total_import_all']})",
        f"  hubs={st['sync_hubs']['status']}, firewall={st['check_firewall']['status']}",
        f"  rdeps={rc['exact_rdeps_count']} (capped_ok={rc['rdeps_capped_pass']}), "
        f"canary_triggered={rc['canary_triggered']} "
        f"(targets={len(rc['build_targets'])})",
        f"  build={st['lake_build']['status']}, axioms={st['axiom_audit']['status']}, "
        f"abi={st['abi_diff']['status']}, c0_asan={st['c0_asan']['status']}",
    ]
    if report["failed_steps"]:
        lines.append(f"  failed_steps: {report['failed_steps']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for `scripts/l2_audit.py`."""
    ap = argparse.ArgumentParser(
        description="Deterministic N11+N9 L2 PR audit tool."
    )
    ap.add_argument("--root", default=".", help="Repository root (default: .)")
    ap.add_argument("--base", required=True, help="Base commit/ref.")
    ap.add_argument("--target", required=True, help="Target commit/ref.")
    ap.add_argument(
        "--main-ref",
        default="refs/heads/leanqbe/main",
        help="Main integration ref for zero-disk merge-tree (default: refs/heads/leanqbe/main).",
    )
    ap.add_argument(
        "--worktree-pool",
        default="/var/tmp/wt-pool/l2",
        help="Persistent pooled worktree path (default: /var/tmp/wt-pool/l2).",
    )
    ap.add_argument(
        "--allow",
        default=None,
        help="Optional regex that all changed file paths must match.",
    )
    ap.add_argument(
        "--c0-target",
        choices=("m7fidelity", "fidelity"),
        default=None,
        help="Optional Kissat C0 ASan+UBSan SHA-256 memoized check target.",
    )
    ap.add_argument(
        "--abi-diff",
        action="store_true",
        help="Verify public declaration ABI parity against --base.",
    )
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="Run zero-disk/static/rdeps/canary simulation without lake build.",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit full machine-readable JSON output.",
    )
    args = ap.parse_args(argv)

    repo = Path(args.root).resolve()
    pool = Path(args.worktree_pool) if args.worktree_pool else None
    report = run_audit(
        repo,
        args.base,
        args.target,
        main_ref=args.main_ref,
        worktree_pool=pool,
        allow_regex=args.allow,
        c0_target=args.c0_target,
        abi_diff=args.abi_diff,
        dry_run=args.dry_run,
    )
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(format_human(report))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
