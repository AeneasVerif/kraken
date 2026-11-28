#!/usr/bin/env python3
"""Shared process, cgroup, git, worktree, and `check.sh` helpers for `scripts/`."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from collections.abc import Callable, Iterable, Mapping, Sequence
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from lean_imports import (  # noqa: E402
    ARM_PFX,
    END_SCOPE_RE,
    KISSAT_ARM_PFX,
    KISSAT_X64_PFX,
    NS_OPEN_RE,
    SEC_OPEN_RE,
    X64_PFX,
    classify_module_arch,
    collect_active_headlines,
    compute_import_closure,
    list_lean_files,
    mod_to_rel_path,
    parse_imports,
    run_git,
)

DEFAULT_CGROUP_SLICE = "leanqbe-builds.slice"
LEANQBE_MOD_PREFIXES: tuple[str, ...] = (
    "LeanQbe.", "LeanQbeTest.", "LeanQbeBootstrap0Test.",
)
DEF_MAIN_RE = re.compile(r"^(?:(?:public|private|protected|noncomputable)\s+)*def\s+main\b")


def systemd_scope_available() -> bool:
    """Return True if `systemd-run --user --scope` works in this session."""
    if shutil.which("systemd-run") is None:
        return False
    return subprocess.run(
        ["systemd-run", "--user", "--scope", "true"], capture_output=True, check=False
    ).returncode == 0


def build_cgroup_cmd(
    cmd: Sequence[str],
    *,
    memory_max: str = "12G",
    timeout_sec: int | None = 600,
    env_vars: Mapping[str, str] | None = None,
    slice_name: str = DEFAULT_CGROUP_SLICE,
    unit_name: str | None = None,
    use_systemd: bool | None = None,
) -> list[str]:
    """Build `[systemd-run ...] [timeout ...] [env ...] <cmd>` command argv."""
    inner: list[str] = list(cmd)
    if env_vars:
        inner = ["env", *(f"{k}={v}" for k, v in env_vars.items()), *inner]
    if timeout_sec is not None and timeout_sec > 0:
        inner = ["timeout", "--foreground", str(timeout_sec), *inner]
    if not (systemd_scope_available() if use_systemd is None else use_systemd):
        return inner
    prefix = ["systemd-run", "--user", "--scope", "--quiet"]
    if unit_name:
        prefix.append(f"--unit={unit_name}")
    prefix.extend([
        f"--slice={slice_name}", "-p", f"MemoryMax={memory_max}",
        "-p", "MemorySwapMax=0", "-p", "OOMPolicy=kill",
    ])
    return [*prefix, *inner]


def run_cgroup(
    cmd: Sequence[str],
    *,
    memory_max: str = "12G",
    timeout_sec: int | None = 600,
    env_vars: Mapping[str, str] | None = None,
    slice_name: str = DEFAULT_CGROUP_SLICE,
    unit_name: str | None = None,
    use_systemd: bool | None = None,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
    **run_kwargs: object,
) -> subprocess.CompletedProcess[str]:
    """Run `cmd` inside a swap-disabled systemd scope (when available)."""
    wrapped = build_cgroup_cmd(
        cmd, memory_max=memory_max, timeout_sec=timeout_sec, env_vars=env_vars,
        slice_name=slice_name, unit_name=unit_name, use_systemd=use_systemd,
    )
    run_kwargs.setdefault("check", False)
    return runner(wrapped, **run_kwargs)


def wrap_build_cmd(
    cmd: Sequence[str],
    *,
    timeout_sec: int = 600,
    memory_max: str = "12G",
    use_systemd: bool | None = None,
) -> list[str]:
    """Wrap Lake build/audit command with cache env, `timeout`, and systemd cgroup."""
    return build_cgroup_cmd(
        cmd,
        memory_max=memory_max,
        timeout_sec=timeout_sec,
        env_vars={
            "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true",
            "LAKE_JOBS": "2", "LEAN_NUM_THREADS": "2",
        },
        use_systemd=use_systemd,
    )


def resolve_commit(repo: Path, ref: str) -> str:
    """Resolve `ref` to a 40-char commit SHA or raise `RuntimeError`."""
    res = run_git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}")
    if res.returncode != 0:
        raise RuntimeError(f"cannot resolve commit '{ref}': {res.stderr.strip()}")
    return res.stdout.strip()


def try_resolve_commit(repo: Path, ref: str) -> str | None:
    """Resolve `ref` to commit SHA, returning `None` if unresolvable."""
    try:
        return resolve_commit(repo, ref)
    except RuntimeError:
        return None


def read_blob_at_commit(repo: Path, commit: str, rel_path: str) -> str | None:
    """Read tracked file text at `commit` via `git show` (zero disk)."""
    res = run_git(repo, "show", f"{commit}:{rel_path}")
    return res.stdout if res.returncode == 0 else None


def is_dirty_worktree(wt_path: Path) -> bool | None:
    """Return True if worktree has modified/untracked files, None on git error."""
    res = run_git(wt_path, "status", "--porcelain", "--untracked-files=normal")
    return None if res.returncode != 0 else bool(res.stdout.strip())


def git_dirty_paths(repo: Path) -> set[str]:
    """Return modified/untracked repo-relative paths reported by `git status`."""
    res = run_git(repo, "status", "--porcelain")
    if res.returncode != 0:
        return set()
    return {ln[3:].split(" -> ")[-1].strip() for ln in res.stdout.splitlines() if len(ln) > 3}


def ensure_worktree(
    repo: Path, wt: Path, target_sha: str, *, checkout_detached: bool = True
) -> None:
    """Create or reset pooled worktree `wt` to `target_sha`, preserving `.lake`."""
    wt_res = wt.resolve()
    if not (wt_res / ".git").exists():
        wt_res.parent.mkdir(parents=True, exist_ok=True)
        run_git(repo, "worktree", "add", "--detach", str(wt_res), target_sha, check=True)
        return
    run_git(wt_res, "merge", "--abort")
    reset_args = ("reset", "--hard") if checkout_detached else ("reset", "--hard", target_sha)
    run_git(wt_res, *reset_args, check=True)
    run_git(wt_res, "clean", "-fd", "-e", ".lake")
    if checkout_detached:
        run_git(wt_res, "checkout", "--detach", target_sha, check=True)


def resolve_script(wt: Path, name: str, fallback_dir: Path = SCRIPTS_DIR) -> Path:
    """Prefer `wt/scripts/<name>` when present, else fall back to `fallback_dir/<name>`."""
    cand = wt / "scripts" / name
    return cand if cand.is_file() else fallback_dir / name


def audit_axioms_cache_key(root: Path) -> str | None:
    """Compute 16-char SHA-256 key over `lean-toolchain` + `scripts/AuditAxioms.lean`."""
    tc, src = root / "lean-toolchain", resolve_script(root, "AuditAxioms.lean")
    if not (tc.is_file() and src.is_file()):
        return None
    h = hashlib.sha256()
    h.update(tc.read_bytes())
    h.update(src.read_bytes())
    return h.hexdigest()[:16]


def resolve_audit_axioms_bin(root: Path) -> Path | None:
    """Locate prebuilt `audit_axioms` binary matching current toolchain + source key."""
    key = audit_axioms_cache_key(root)
    if key is None:
        return None
    local_bin = root / ".lake" / "build" / "bin" / "audit_axioms"
    local_key = root / ".lake" / "build" / "bin" / "audit_axioms.key"
    if local_bin.is_file() and os.access(local_bin, os.X_OK) and local_key.is_file():
        if local_key.read_text(encoding="utf-8").strip() == key:
            return local_bin
    xdg = Path(os.environ.get("XDG_CACHE_HOME") or (Path.home() / ".cache"))
    cache_dir = Path(os.environ.get("AUDIT_AXIOMS_CACHE_DIR") or (xdg / "lean-qbe"))
    cache_bin = cache_dir / f"audit_axioms-{key}"
    return cache_bin if cache_bin.is_file() and os.access(cache_bin, os.X_OK) else None


def format_audit_manifest(groups: Iterable[tuple[str, Iterable[tuple[str, str]]]]) -> str:
    """Render `GROUP <name>` + `<Module> <Const>` manifest text for `audit_axioms`."""
    lines: list[str] = []
    for grp, entries in groups:
        entry_list = list(entries)
        if not entry_list:
            continue
        lines.append(f"GROUP {grp}")
        lines.extend(f"{mod} {const}" for mod, const in entry_list)
    return "\n".join(lines) + ("\n" if lines else "")


def _has_root_main(root: Path, mod: str, memo: dict[str, bool], stack: set[str]) -> bool:
    """Return True if `mod` (or its LeanQbe imports) defines top-level `def main`."""
    if mod in memo:
        return memo[mod]
    if mod in stack:
        return False
    p = root / mod_to_rel_path(mod)
    if not p.is_file():
        return False
    nxt = stack | {mod}
    found = any(
        imp.module.startswith(LEANQBE_MOD_PREFIXES) and _has_root_main(root, imp.module, memo, nxt)
        for imp in parse_imports(p)[1]
    )
    if not found:
        scopes: list[str] = []
        for raw_ln in p.read_text(encoding="utf-8").splitlines():
            s = raw_ln.strip()
            if NS_OPEN_RE.match(s):
                scopes.append("ns")
            elif SEC_OPEN_RE.match(s):
                scopes.append("sec")
            elif END_SCOPE_RE.match(s) and scopes:
                scopes.pop()
            elif "ns" not in scopes and DEF_MAIN_RE.match(raw_ln):
                found = True
                break
    memo[mod] = found
    return found


def select_scoped_test_modules(
    root: Path, scope: str, headlines_path: Path, changed_path: Path
) -> list[str]:
    """Select `LeanQbeTest.*`/`LeanQbeBootstrap0Test.*` modules for `x64`/`arm64` scope."""
    cache: dict[str, str] = {}
    want: list[str] = []
    seen: set[str] = set()
    for raw in headlines_path.read_text(encoding="utf-8").splitlines():
        parts = raw.split()
        if len(parts) < 2:
            continue
        mod = parts[0]
        if not mod.startswith(("LeanQbeTest.", "LeanQbeBootstrap0Test.")) or mod in seen:
            continue
        arch = classify_module_arch(
            root, mod, cache, recurse_prefixes=LEANQBE_MOD_PREFIXES, missing_status="conflict"
        )
        if arch in ("generic", scope):
            seen.add(mod)
            want.append(mod)
    for ln in changed_path.read_text(encoding="utf-8").splitlines():
        f = ln.strip()
        if (
            f.startswith(("LeanQbeTest/", "LeanQbeBootstrap0Test/"))
            and f.endswith(".lean")
            and (root / f).is_file()
        ):
            mod = f[:-5].replace("/", ".")
            if mod not in seen:
                seen.add(mod)
                want.append(mod)
    return want


def plan_audit_batches(
    root: Path, tmp_dir: Path, scope: str, rdeps_filter_path: Path | None = None
) -> None:
    """Emit `selected_headlines.txt` and `audit_manifest.txt` for `check.sh` Step 4."""
    def read_set(name: str) -> set[str]:
        p = tmp_dir / f"closure_{name}.txt"
        return set(p.read_text(encoding="utf-8").splitlines()) if p.exists() else set()

    c_gen = read_set("LeanQbe")
    c_x64, c_arm = read_set("LeanQbeAmd64") - c_gen, read_set("LeanQbeArm64") - c_gen
    cache: dict[str, str] = {}
    if scope == "rdeps" and rdeps_filter_path is not None and rdeps_filter_path.is_file():
        rdeps_allowed: set[str] | None = {
            ln.strip()
            for ln in rdeps_filter_path.read_text(encoding="utf-8").splitlines()
            if ln.strip()
        }
    else:
        rdeps_allowed = None
    main_memo: dict[str, bool] = {}
    buckets: dict[str, list[tuple[str, str]]] = {b: [] for b in ("generic", "x64", "arm64")}
    solo, conflict = {}, {}
    selected: list[str] = []

    for raw in (tmp_dir / "headlines_all.txt").read_text(encoding="utf-8").splitlines():
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        parts = s.split()
        if len(parts) < 2:
            continue
        mod, const = parts[0], parts[1]
        if rdeps_allowed is not None and mod not in rdeps_allowed:
            continue
        b = classify_module_arch(
            root, mod, cache, c_gen=c_gen, x64_only=c_x64, arm_only=c_arm,
            recurse_prefixes=LEANQBE_MOD_PREFIXES, missing_status="conflict",
        )
        if (scope == "x64" and b == "arm64") or (scope == "arm64" and b == "x64"):
            continue
        selected.append(f"{mod} {const}")
        if b == "conflict":
            conflict.setdefault(mod, []).append((mod, const))
        elif _has_root_main(root, mod, main_memo, set()):
            solo.setdefault(mod, []).append((mod, const))
        else:
            buckets[b].append((mod, const))

    (tmp_dir / "selected_headlines.txt").write_text(
        "\n".join(selected) + ("\n" if selected else ""), encoding="utf-8"
    )
    groups: list[tuple[str, list[tuple[str, str]]]] = [
        (b, buckets[b]) for b in ("generic", "x64", "arm64") if buckets[b]
    ]
    groups.extend((f"solo_{i}", e) for i, e in enumerate(solo.values(), 1))
    groups.extend((f"conflict_{i}", e) for i, e in enumerate(conflict.values(), 1))
    (tmp_dir / "audit_manifest.txt").write_text(format_audit_manifest(groups), encoding="utf-8")


def check_import_closures(root: Path, tmp_dir: Path, raw_scope: str) -> list[str]:
    """Verify Step 3 arch isolation and `LeanQbe/T/` reachability."""
    scope = "full" if raw_scope == "rdeps" else raw_scope
    has_external = False
    manifest_p = root / "lake-manifest.json"
    if manifest_p.is_file():
        try:
            has_external = bool(json.loads(manifest_p.read_text(encoding="utf-8")).get("packages"))
        except Exception:
            has_external = False

    def lean_closure(root_mod: str) -> list[str]:
        f = tmp_dir / f"Closure_{root_mod}.lean"
        f.write_text(
            f"import Lean\nimport {root_mod}\nopen Lean in\n#eval show CoreM Unit from do\n"
            '  for n in (← getEnv).header.moduleNames do\n    IO.println s!"MOD {n}"\n',
            encoding="utf-8",
        )
        out = subprocess.check_output(["lake", "env", "lean", str(f)], cwd=str(root), text=True)
        return [ln[4:].strip() for ln in out.splitlines() if ln.startswith("MOD ")]

    imp_cache: dict[str, list] = {}
    case_roots = {
        "x64": ["LeanQbe", "LeanQbeAmd64"],
        "arm64": ["LeanQbe", "LeanQbeArm64"],
        "full": ["LeanQbe", "LeanQbeAmd64", "LeanQbeArm64"],
    }[scope]

    closures: dict[str, set[str]] = {}
    for r in case_roots:
        c = lean_closure(r) if has_external else sorted(
            compute_import_closure([r], root, import_cache=imp_cache)
        )
        closures[r] = set(c)
        (tmp_dir / f"closure_{r}.txt").write_text("\n".join(c) + "\n", encoding="utf-8")

    errors: list[str] = []
    if "LeanQbe" in closures:
        bad = sorted(m for m in closures["LeanQbe"] if m.startswith((*X64_PFX, *ARM_PFX)))
        if bad:
            errors.append(f"the generic LeanQbe imports an architecture ({', '.join(bad)})")
    for r, bad_pfx, msg in (
        ("LeanQbeAmd64", ARM_PFX, "LeanQbeAmd64 imports AArch64/Arm64"),
        ("LeanQbeArm64", X64_PFX, "LeanQbeArm64 imports X64/Amd64"),
    ):
        if r in closures:
            bad = sorted(m for m in closures[r] if m.startswith(bad_pfx))
            if bad:
                errors.append(f"{msg} ({', '.join(bad)})")
    for r in case_roots:
        if r not in closures[r]:
            errors.append(f"could not compute the closure of {r}")

    extra_specs = [
        ("bootstrap0", ["LeanQbeBootstrap0"], "bootstrap0_closure.txt"),
        ("bootstrap0_test", [
            p.with_suffix("").as_posix().replace("/", ".")
            for p in list_lean_files(root, "LeanQbeBootstrap0Test")
        ], "bootstrap0_test_closure.txt"),
    ]
    for key, roots_list, out_name in extra_specs:
        mods = sorted(compute_import_closure(roots_list, root, import_cache=imp_cache))
        closures[key] = set(mods)
        (tmp_dir / out_name).write_text("\n".join(mods) + "\n", encoding="utf-8")

    if scope != "arm64":
        for key, label in (
            ("bootstrap0", "LeanQbeBootstrap0"),
            ("bootstrap0_test", "LeanQbeBootstrap0Test"),
        ):
            if any(m.startswith(ARM_PFX) for m in closures[key]):
                errors.append(f"{label} imports AArch64/Arm64 modules")

    c_x64_full = closures.get("LeanQbeAmd64", set())
    c_arm_full = closures.get("LeanQbeArm64", set())
    for rel in list_lean_files(root, "LeanQbe/T", include_untracked=False):
        f = rel.as_posix()
        m = f[:-5].replace("/", ".")
        if m.startswith(("LeanQbe.T.Amd64.", *KISSAT_X64_PFX)):
            if scope != "arm64" and m not in c_x64_full:
                errors.append(f"{f} is not imported by LeanQbeAmd64.lean")
        elif m.startswith("LeanQbe.T.Bootstrap0."):
            if scope != "arm64" and m not in closures.get("bootstrap0", set()):
                errors.append(f"{f} is not imported by LeanQbeBootstrap0.lean")
        elif m.startswith(("LeanQbe.T.Arm64.", *KISSAT_ARM_PFX)):
            if scope != "x64" and m not in c_arm_full:
                errors.append(f"{f} is not imported by LeanQbeArm64.lean")
        elif m not in closures.get("LeanQbe", set()):
            errors.append(f"{f} is not imported by the root LeanQbe.lean (so it is not built)")
    return errors


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args:
        print(
            "Usage: _common.py <collect-headlines|scoped-tests|audit-batches|"
            "check-closures|find-audit-axioms>",
            file=sys.stderr,
        )
        return 2
    cmd = args[0]
    if cmd == "collect-headlines":
        entries = collect_active_headlines(Path(args[1]).resolve())
        lines = [f"{m} {c}" for m, c in entries]
        out_path = Path(args[2] if len(args) == 3 else args[3])
        out_path.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")
        return 0
    if cmd == "scoped-tests":
        mods = select_scoped_test_modules(
            Path(args[1]).resolve(), args[2], Path(args[3]), Path(args[4])
        )
        for m in mods:
            print(m)
        return 0
    if cmd == "audit-batches":
        rf = Path(args[4]) if len(args) > 4 and args[4] else None
        plan_audit_batches(Path(args[1]).resolve(), Path(args[2]), args[3], rf)
        return 0
    if cmd == "check-closures":
        errs = check_import_closures(Path(args[1]).resolve(), Path(args[2]), args[3])
        if errs:
            print("\n".join(f"FAIL: {e}" for e in errs), file=sys.stderr)
            return 1
        return 0
    if cmd == "find-audit-axioms":
        p = resolve_audit_axioms_bin(Path(args[1]).resolve())
        if p is not None:
            print(p)
        return 0 if p is not None else 1
    print(f"unknown _common command: {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
