#!/usr/bin/env python3
"""Deterministic Bors/Zuul bisecting merge train (N10 + N8).

Combines candidate branches onto `--base` (`leanqbe/main`):
  1. Enforces N8 (`STANDALONE_GREEN` vs partial `TRAIN_SHARD` gating).
  2. Verifies each candidate via zero-disk `git merge-tree --write-tree`.
  3. Combines passing candidates in a staging worktree, runs
     `sync_hubs.py --write`, checks `rdeps` / N9 Canary Frontier `--wfail`.
  4. If any batch fails, binary-bisects in `O(log k)` trials to eject ONLY
     the failing PR(s) while keeping cleanly passing PRs.
  5. Optionally invokes `scripts/fast_land.sh` via `--execute`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, TypeVar

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from l2_audit import (  # noqa: E402
    execute_lake_build,
    plan_rdeps_and_canary,
    resolve_commit,
    run_firewall_check,
    run_merge_tree,
    run_sync_hubs_check,
)

T = TypeVar("T")

TRAIN_SHARD_RE = re.compile(r"\bTRAIN_SHARD\b")
STANDALONE_GREEN_RE = re.compile(r"\bSTANDALONE_GREEN\b")


@dataclass
class Candidate:
    """Candidate branch/commit entering the merge train."""

    branch: str
    sha: str


@dataclass
class EjectedPR:
    """Candidate rejected during pre-screen or O(log k) bisection."""

    branch: str
    sha: str
    reason: str
    detail: dict[str, object]


def bisect_candidates(
    candidates: list[T],
    test_fn: Callable[[list[T]], tuple[bool, dict[str, object]]],
    trace: list[dict[str, object]] | None = None,
) -> tuple[list[T], list[tuple[T, dict[str, object]]]]:
    """Find maximal passing subset via O(log k) divide-and-conquer bisection.

    If `good_left + good_right` fails due to a cross-PR interaction, holds
    `good_left` fixed and bisects `good_right` against `good_left` so only
    conflicting right-hand PR(s) are ejected.
    """
    log = trace if trace is not None else []

    def run_test(prefix: list[T], subset: list[T]) -> tuple[bool, dict[str, object]]:
        ok, diag = test_fn(prefix + subset)
        log.append(
            {
                "prefix_len": len(prefix),
                "subset_len": len(subset),
                "total_len": len(prefix) + len(subset),
                "ok": ok,
            }
        )
        return ok, diag

    def solve(items: list[T]) -> tuple[list[T], list[tuple[T, dict[str, object]]]]:
        if not items:
            return [], []
        ok, diag = run_test([], items)
        if ok:
            return list(items), []
        if len(items) == 1:
            return [], [(items[0], diag)]
        mid = len(items) // 2
        g_left, b_left = solve(items[:mid])
        g_right, b_right = solve(items[mid:])
        if not g_left:
            return g_right, b_left + b_right
        if not g_right:
            return g_left, b_left + b_right
        g_compat, b_compat = solve_with_prefix(g_left, g_right)
        return g_left + g_compat, b_left + b_right + b_compat

    def solve_with_prefix(
        prefix: list[T], items: list[T]
    ) -> tuple[list[T], list[tuple[T, dict[str, object]]]]:
        if not items:
            return [], []
        ok, diag = run_test(prefix, items)
        if ok:
            return list(items), []
        if len(items) == 1:
            return [], [(items[0], diag)]
        mid = len(items) // 2
        g1, b1 = solve_with_prefix(prefix, items[:mid])
        g2, b2 = solve_with_prefix(prefix + g1, items[mid:])
        return g1 + g2, b1 + b2

    return solve(candidates)


def check_n8_shard_policy(
    repo: Path, branch: str, sha: str, *, allow_shard: bool
) -> tuple[bool, str]:
    """Enforce N8: block partial `TRAIN_SHARD` PRs unless integrated train."""
    if allow_shard or branch.startswith(("leanqbe/train/", "refs/heads/leanqbe/train/")):
        return True, ""
    res = subprocess.run(
        ["git", "-C", str(repo), "log", "-1", "--format=%B", sha],
        capture_output=True,
        text=True,
        check=False,
    )
    msg = res.stdout if res.returncode == 0 else ""
    if TRAIN_SHARD_RE.search(msg) and not STANDALONE_GREEN_RE.search(msg):
        return False, "commit marked TRAIN_SHARD (merge into leanqbe/train/<id> first)"
    return True, ""


def prescreen_candidates(
    repo: Path,
    base_sha: str,
    branches: list[str],
    *,
    allow_shard: bool = False,
) -> tuple[list[Candidate], list[EjectedPR]]:
    """Resolve branches and reject N8 shard violations or base merge conflicts."""
    passing: list[Candidate] = []
    ejected: list[EjectedPR] = []
    for br in branches:
        try:
            sha = resolve_commit(repo, br)
        except RuntimeError as exc:
            ejected.append(
                EjectedPR(
                    branch=br,
                    sha="",
                    reason="unresolvable_ref",
                    detail={"error": str(exc)},
                )
            )
            continue

        n8_ok, n8_reason = check_n8_shard_policy(
            repo, br, sha, allow_shard=allow_shard
        )
        if not n8_ok:
            ejected.append(
                EjectedPR(
                    branch=br,
                    sha=sha,
                    reason="n8_train_shard",
                    detail={"error": n8_reason},
                )
            )
            continue

        mt = run_merge_tree(repo, base_sha, sha)
        if not mt["clean"]:
            ejected.append(
                EjectedPR(
                    branch=br,
                    sha=sha,
                    reason="merge_conflict_with_base",
                    detail=mt,
                )
            )
            continue
        passing.append(Candidate(branch=br, sha=sha))
    return passing, ejected


def dry_run_test_subset(
    repo: Path, base_sha: str, subset: list[Candidate]
) -> tuple[bool, dict[str, object]]:
    """Zero-disk dry-run test of candidate subset compatibility + Canary scope."""
    conflicts: list[dict[str, object]] = []
    changed_union: set[str] = set()
    for cand in subset:
        diff_res = subprocess.run(
            ["git", "-C", str(repo), "diff", "--name-only", f"{base_sha}...{cand.sha}"],
            capture_output=True,
            text=True,
            check=False,
        )
        if diff_res.returncode == 0:
            changed_union.update(
                ln.strip() for ln in diff_res.stdout.splitlines() if ln.strip()
            )

    # Check pairwise 3-way mergeability across all pairs in `subset`.
    for i in range(len(subset)):
        for j in range(i + 1, len(subset)):
            a, b = subset[i], subset[j]
            res = subprocess.run(
                [
                    "git",
                    "-C",
                    str(repo),
                    "merge-tree",
                    "--write-tree",
                    f"--merge-base={base_sha}",
                    a.sha,
                    b.sha,
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            if res.returncode != 0:
                lines = [ln for ln in res.stdout.splitlines() if "CONFLICT" in ln]
                conflicts.append(
                    {
                        "pair": [a.branch, b.branch],
                        "conflicts": lines[:10],
                    }
                )

    canary_info = plan_rdeps_and_canary(repo, sorted(changed_union), base_sha)
    if conflicts:
        return False, {
            "reason": "pairwise_merge_conflict",
            "conflicts": conflicts,
            "rdeps_canary": canary_info,
        }
    return True, {
        "changed_files": sorted(changed_union),
        "rdeps_canary": canary_info,
    }


def ensure_staging_worktree(repo: Path, wt: Path, base_sha: str) -> None:
    """Create or reset staging worktree while preserving `.lake/build`."""
    wt = wt.resolve()
    if not (wt / ".git").exists():
        wt.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "-C", str(repo), "worktree", "add", "--detach", str(wt), base_sha],
            capture_output=True,
            text=True,
            check=True,
        )
    else:
        subprocess.run(
            ["git", "-C", str(wt), "merge", "--abort"],
            capture_output=True,
            check=False,
        )
        subprocess.run(
            ["git", "-C", str(wt), "reset", "--hard", base_sha],
            capture_output=True,
            text=True,
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(wt), "clean", "-fd", "-e", ".lake"],
            capture_output=True,
            check=False,
        )


def _sync_hubs_write(wt: Path) -> tuple[bool, str]:
    """Run `sync_hubs.py --write` and commit updated hubs if modified."""
    script = wt / "scripts" / "sync_hubs.py"
    if not script.is_file():
        script = SCRIPTS_DIR / "sync_hubs.py"
    res = subprocess.run(
        ["timeout", "60", sys.executable, "-B", str(script), "--root", str(wt), "--write"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        return False, (res.stderr or res.stdout).strip()[:400]
    st = subprocess.run(
        ["git", "-C", str(wt), "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=True,
    )
    if st.stdout.strip():
        subprocess.run(
            ["git", "-C", str(wt), "add", "-A"],
            check=True,
            capture_output=True,
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(wt),
                "commit",
                "-m",
                "chore(hubs): sync_hubs --write",
            ],
            check=True,
            capture_output=True,
        )
    return True, res.stdout.strip()[:400]


def stage_and_verify_subset(
    repo: Path,
    wt: Path,
    base_sha: str,
    subset: list[Candidate],
) -> tuple[bool, dict[str, object]]:
    """Combine `subset` in staging worktree `wt`, sync hubs, and build `--wfail`."""
    ensure_staging_worktree(repo, wt, base_sha)
    for cand in subset:
        mres = subprocess.run(
            [
                "git",
                "-C",
                str(wt),
                "merge",
                "--no-edit",
                "--no-ff",
                cand.sha,
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        if mres.returncode != 0:
            subprocess.run(
                ["git", "-C", str(wt), "merge", "--abort"],
                capture_output=True,
                check=False,
            )
            return False, {
                "reason": "staging_merge_conflict",
                "branch": cand.branch,
                "output": (mres.stderr or mres.stdout).strip()[:400],
            }

    ok_write, write_msg = _sync_hubs_write(wt)
    if not ok_write:
        return False, {"reason": "sync_hubs_write_failed", "output": write_msg}

    hubs_chk = run_sync_hubs_check(wt)
    if hubs_chk["status"] != "pass":
        return False, {"reason": "sync_hubs_check_failed", "detail": hubs_chk}

    fw_chk = run_firewall_check(wt)
    if fw_chk["status"] != "pass":
        return False, {"reason": "check_firewall_failed", "detail": fw_chk}

    diff_res = subprocess.run(
        ["git", "-C", str(wt), "diff", "--name-only", base_sha, "HEAD"],
        capture_output=True,
        text=True,
        check=True,
    )
    changed = [ln.strip() for ln in diff_res.stdout.splitlines() if ln.strip()]
    rdeps_info = plan_rdeps_and_canary(wt, changed, base_sha)
    targets: list[str] = rdeps_info["build_targets"]  # type: ignore[assignment]
    build_res = execute_lake_build(wt, targets)
    if build_res["status"] == "fail":
        return False, {
            "reason": "lake_build_failed",
            "rdeps_canary": rdeps_info,
            "lake_build": build_res,
        }

    head_sha = subprocess.check_output(
        ["git", "-C", str(wt), "rev-parse", "HEAD"], text=True
    ).strip()
    return True, {
        "merged_sha": head_sha,
        "changed_files": changed,
        "rdeps_canary": rdeps_info,
        "lake_build": build_res,
    }


def invoke_fast_land(
    repo: Path,
    staging_wt: Path,
    merged_sha: str,
    *,
    base_branch: str,
    fast: bool = False,
) -> dict[str, object]:
    """Invoke authoritative `scripts/fast_land.sh` from `repo`."""
    land_sh = repo / "scripts" / "fast_land.sh"
    cmd = ["timeout", "3600", "bash", str(land_sh)]
    if fast:
        cmd.append("--fast")
    cmd.extend([str(staging_wt), merged_sha])
    env = os.environ.copy()
    env["LAND_BRANCH"] = base_branch.removeprefix("refs/heads/")
    env.setdefault("LAKE_ARTIFACT_CACHE", "true")
    env.setdefault("LAKE_RESTORE_ARTIFACTS", "true")
    res = subprocess.run(
        cmd, cwd=str(repo), env=env, capture_output=True, text=True, check=False
    )
    return {
        "status": "pass" if res.returncode == 0 else "fail",
        "returncode": res.returncode,
        "stdout_tail": "\n".join(res.stdout.splitlines()[-30:]),
        "stderr_tail": "\n".join(res.stderr.splitlines()[-30:]),
    }


def run_merge_train(
    repo: Path,
    branches: list[str],
    *,
    base_ref: str = "leanqbe/main",
    worktree: Path = Path("/var/tmp/wt-pool/merge-train"),
    dry_run: bool = False,
    execute: bool = False,
    fast_land_skip_tests: bool = False,
    allow_shard: bool = False,
) -> dict[str, object]:
    """Execute the full N10 + N8 speculative bisecting merge train."""
    if execute and dry_run:
        raise ValueError("--execute cannot be combined with --dry-run")
    base_sha = resolve_commit(repo, base_ref)
    candidates, pre_ejected = prescreen_candidates(
        repo, base_sha, branches, allow_shard=allow_shard
    )

    bisect_trace: list[dict[str, object]] = []
    last_good_diag: dict[str, object] = {}

    def test_fn(sub: list[Candidate]) -> tuple[bool, dict[str, object]]:
        if dry_run:
            ok, diag = dry_run_test_subset(repo, base_sha, sub)
        else:
            ok, diag = stage_and_verify_subset(repo, worktree, base_sha, sub)
        if ok:
            last_good_diag.clear()
            last_good_diag.update(diag)
        return ok, diag

    accepted, bisect_bad = bisect_candidates(
        candidates, test_fn, trace=bisect_trace
    )

    ejected = list(pre_ejected) + [
        EjectedPR(
            branch=c.branch,
            sha=c.sha,
            reason=str(diag.get("reason", "bisect_failure")),
            detail=diag,
        )
        for c, diag in bisect_bad
    ]

    merged_sha = None
    if not dry_run and accepted:
        # Ensure staging worktree sits on exact combined accepted subset.
        if len(ejected) > len(pre_ejected) or not last_good_diag.get("merged_sha"):
            ok, final_diag = stage_and_verify_subset(
                repo, worktree, base_sha, accepted
            )
            if ok:
                merged_sha = str(final_diag.get("merged_sha"))
                last_good_diag.clear()
                last_good_diag.update(final_diag)
        else:
            merged_sha = str(last_good_diag.get("merged_sha"))

    fast_land_res: dict[str, object] | None = None
    if execute and merged_sha:
        fast_land_res = invoke_fast_land(
            repo,
            worktree,
            merged_sha,
            base_branch=base_ref,
            fast=fast_land_skip_tests,
        )

    ok_overall = bool(accepted) and (
        fast_land_res is None or fast_land_res["status"] == "pass"
    )
    return {
        "ok": ok_overall,
        "mode": "dry-run" if dry_run else ("execute" if execute else "stage"),
        "base_ref": base_ref,
        "base_sha": base_sha,
        "accepted": [asdict(c) for c in accepted],
        "ejected": [asdict(e) for e in ejected],
        "bisect_steps": len(bisect_trace),
        "bisect_trace": bisect_trace,
        "merged_sha": merged_sha,
        "summary_diag": last_good_diag,
        "fast_land": fast_land_res,
    }


def format_human(report: dict[str, object]) -> str:
    """Render concise human-readable merge-train report."""
    acc = [c["branch"] for c in report["accepted"]]  # type: ignore[index]
    ej = [
        f"{e['branch']} ({e['reason']})"
        for e in report["ejected"]  # type: ignore[index]
    ]
    lines = [
        f"merge_train ({report['mode']}, base={report['base_ref']}): "
        f"accepted={len(acc)}, ejected={len(ej)}, "
        f"bisect_steps={report['bisect_steps']}",
        f"  accepted: {acc}",
    ]
    if ej:
        lines.append(f"  ejected:  {ej}")
    if report["merged_sha"]:
        lines.append(f"  merged_sha: {report['merged_sha']}")
    if report["fast_land"]:
        lines.append(f"  fast_land: {report['fast_land']['status']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for `scripts/merge_train.py`."""
    ap = argparse.ArgumentParser(
        description="Deterministic O(log k) bisecting merge train (N10 + N8)."
    )
    ap.add_argument("--root", default=".", help="Repository root (default: .)")
    ap.add_argument(
        "--base",
        default="leanqbe/main",
        help="Target integration branch/commit (default: leanqbe/main).",
    )
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="Simulate merge-tree, Canary Frontier, and bisection with 0 mutations.",
    )
    ap.add_argument(
        "--worktree",
        default="/var/tmp/wt-pool/merge-train",
        help="Staging worktree path (default: /var/tmp/wt-pool/merge-train).",
    )
    ap.add_argument(
        "--execute",
        action="store_true",
        help="Invoke scripts/fast_land.sh once combined subset is green.",
    )
    ap.add_argument(
        "--fast",
        action="store_true",
        help="Pass --fast to scripts/fast_land.sh when --execute is set.",
    )
    ap.add_argument(
        "--allow-shard",
        action="store_true",
        help="Allow commits annotated with TRAIN_SHARD outside leanqbe/train/*.",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON output.",
    )
    ap.add_argument("branches", nargs="+", help="Candidate branches or SHAs.")
    args = ap.parse_args(argv)

    if args.execute and args.dry_run:
        ap.error("--execute cannot be used together with --dry-run")

    repo = Path(args.root).resolve()
    report = run_merge_train(
        repo,
        args.branches,
        base_ref=args.base,
        worktree=Path(args.worktree),
        dry_run=args.dry_run,
        execute=args.execute,
        fast_land_skip_tests=args.fast,
        allow_shard=args.allow_shard,
    )
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(format_human(report))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
