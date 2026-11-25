#!/usr/bin/env python3
"""Safe worktree & dead Lake cache reclamation tool (N13).

Default mode is strictly `--dry-run` (`0` filesystem or git mutations).
With `--apply`, removes ONLY secondary/detached worktrees that pass all
safety guards:
  - NEVER the primary/bare repository or the current working tree
  - NEVER `/monorepo-work/builds/bee-*/wt` (or `bee-*/wt`) unless `--include-bee`
  - NEVER `/var/tmp/...` worktrees unless `--include-vartmp`
  - ONLY `swarm-*` worktrees (or `/var/tmp/...` with `--include-vartmp`)
    unless `--include-non-swarm` is explicitly passed
  - NEVER non-empty dirty worktrees (`git status --porcelain` non-empty)
  - NEVER worktrees matching an open PID in `ps` or active worker in
    `swarm_status`
  - ONLY worktrees whose `HEAD` commit is an ancestor of
    `refs/heads/leanqbe/main` (`--base`) OR (with `--all-anchored`) already
    pointed to by another branch `refs/heads/leanqbe/*`

Also reports dead non-active Lake cache directories (such as `~/.cache/lake`
and `~/.cache/lean-qbe-lake` when `$LAKE_CACHE_DIR` points elsewhere), only
removing them when BOTH `--apply` and `--prune-dead-cache` are passed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

GIB = float(1024**3)


@dataclass
class WorktreeEntry:
    """Parsed `git worktree list --porcelain` record."""

    path: Path
    head: str | None = None
    branch: str | None = None
    detached: bool = False
    bare: bool = False
    locked: bool = False
    prunable: bool = False


@dataclass
class WorktreeDecision:
    """Safety classification and disk footprint of a single worktree."""

    path: str
    head: str
    branch: str | None
    detached: bool
    action: str  # "prune" | "keep" | "prune_metadata"
    reason: str
    size_bytes: int
    exclusive_bytes: int
    is_ancestor_of_base: bool
    anchored_by_other_ref: bool
    anchored_refs: list[str]
    dirty: bool | None
    active_pids: list[int]
    active_workers: list[str]


@dataclass
class DeadCacheReport:
    """Detected non-active Lake cache directory."""

    path: str
    size_bytes: int
    action: str  # "report" | "prune" | "removed"


def is_bare_git_dir(repo: Path) -> bool:
    """Return True if `repo` is a bare git directory (without `.git` subdir)."""
    return (
        (repo / "objects").is_dir()
        and (repo / "HEAD").is_file()
        and not (repo / ".git").exists()
    )


def git_base_cmd(repo: Path, *args: str) -> list[str]:
    """Build `git` argv handling bare repos under `safe.bareRepository=explicit`."""
    if is_bare_git_dir(repo):
        return ["git", "--git-dir", str(repo), *args]
    return ["git", "-C", str(repo), *args]


def resolve_repo_root(raw_root: str | None) -> Path:
    """Resolve worktree top-level (preferred) or bare git dir."""
    start = Path(raw_root).resolve() if raw_root else Path.cwd().resolve()
    if is_bare_git_dir(start):
        return start
    res = subprocess.run(
        ["git", "-C", str(start), "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode == 0 and res.stdout.strip():
        return Path(res.stdout.strip()).resolve()
    return start


def parse_worktree_list(repo: Path) -> list[WorktreeEntry]:
    """Parse `git worktree list --porcelain` output into `WorktreeEntry` items."""
    raw = subprocess.check_output(
        git_base_cmd(repo, "worktree", "list", "--porcelain"),
        text=True,
    )
    entries: list[WorktreeEntry] = []
    cur: WorktreeEntry | None = None
    for line in raw.splitlines():
        if not line.strip():
            if cur is not None:
                entries.append(cur)
                cur = None
            continue
        if line.startswith("worktree "):
            if cur is not None:
                entries.append(cur)
            cur = WorktreeEntry(path=Path(line[len("worktree ") :].strip()))
            continue
        if cur is None:
            continue
        if line.startswith("HEAD "):
            cur.head = line[len("HEAD ") :].strip()
        elif line.startswith("branch "):
            cur.branch = line[len("branch ") :].strip()
        elif line == "detached":
            cur.detached = True
        elif line == "bare":
            cur.bare = True
        elif line == "locked" or line.startswith("locked "):
            cur.locked = True
        elif line == "prunable" or line.startswith("prunable "):
            cur.prunable = True
    if cur is not None:
        entries.append(cur)
    return entries


def load_leanqbe_ref_map(
    repo: Path, ref_prefix: str = "refs/heads/leanqbe/"
) -> dict[str, list[str]]:
    """Map commit SHA -> list of `refs/heads/leanqbe/*` branch names."""
    res = subprocess.run(
        git_base_cmd(
            repo,
            "for-each-ref",
            "--format=%(objectname) %(refname)",
            ref_prefix,
        ),
        capture_output=True,
        text=True,
        check=False,
    )
    out: dict[str, list[str]] = {}
    if res.returncode != 0:
        return out
    for ln in res.stdout.splitlines():
        s = ln.strip()
        if not s or " " not in s:
            continue
        sha, ref = s.split(" ", 1)
        out.setdefault(sha, []).append(ref)
    return out


def is_ancestor(repo: Path, commit: str | None, base_ref: str) -> bool:
    """Return True iff `commit` is an ancestor of `base_ref`."""
    if not commit:
        return False
    res = subprocess.run(
        git_base_cmd(repo, "merge-base", "--is-ancestor", commit, base_ref),
        capture_output=True,
        check=False,
    )
    return res.returncode == 0


def is_dirty_worktree(wt_path: Path) -> bool | None:
    """Return True if worktree has modified/untracked files, None on git error."""
    res = subprocess.run(
        [
            "git",
            "-C",
            str(wt_path),
            "status",
            "--porcelain",
            "--untracked-files=normal",
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        return None
    return bool(res.stdout.strip())


def collect_running_processes() -> list[tuple[int, str, str]]:
    """Return `[(pid, cwd, args)]` for live processes via `ps` and `/proc`."""
    res = subprocess.run(
        ["ps", "-eo", "pid,args"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        return []
    self_pid = os.getpid()
    procs: list[tuple[int, str, str]] = []
    for ln in res.stdout.splitlines()[1:]:
        s = ln.strip()
        if not s:
            continue
        parts = s.split(None, 1)
        if not parts[0].isdigit():
            continue
        pid = int(parts[0])
        if pid == self_pid:
            continue
        args = parts[1] if len(parts) > 1 else ""
        cwd = ""
        try:
            cwd = os.readlink(f"/proc/{pid}/cwd")
        except OSError:
            cwd = ""
        procs.append((pid, cwd, args))
    return procs


def load_active_swarm_workers(
    swarm_status_path: str | None,
) -> list[tuple[str, str]]:
    """Return `[(name, workspace)]` for non-killed workers in swarm_status."""
    raw_path = swarm_status_path or os.environ.get("SWARM_STATUS_JSON")
    if not raw_path:
        return []
    if raw_path == "-":
        raw = sys.stdin.read()
    else:
        p = Path(raw_path)
        if not p.is_file():
            return []
        raw = p.read_text(encoding="utf-8")

    # Handle either pure JSON or tool log headers preceding a `{...}` JSON line.
    payload = None
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError:
        for line in raw.splitlines():
            s = line.strip()
            if s.startswith("{"):
                try:
                    payload = json.loads(s)
                    break
                except json.JSONDecodeError:
                    continue
    if not isinstance(payload, dict):
        return []

    active: list[tuple[str, str]] = []
    for member in payload.get("members", []):
        if not isinstance(member, dict):
            continue
        if member.get("killed") is True or member.get("state") == "killed":
            continue
        name = str(member.get("name", "")).strip()
        ws = str(member.get("workspace", "")).strip()
        if name or ws:
            active.append((name, ws))
    return active


def find_matching_pids(
    wt_path: Path, procs: list[tuple[int, str, str]]
) -> list[int]:
    """Return PIDs whose cwd or cmdline references `wt_path`."""
    raw_str = str(wt_path)
    resolved_str = str(wt_path.resolve()) if wt_path.exists() else raw_str
    dir_name = wt_path.name
    hits: list[int] = []
    for pid, cwd, args in procs:
        if cwd and (
            cwd == raw_str
            or cwd == resolved_str
            or cwd.startswith(raw_str + "/")
            or cwd.startswith(resolved_str + "/")
        ):
            hits.append(pid)
            continue
        if raw_str in args or resolved_str in args:
            hits.append(pid)
            continue
        if dir_name.startswith("swarm-") and len(dir_name) >= 12:
            if dir_name in args:
                hits.append(pid)
    return sorted(set(hits))


def find_matching_workers(
    wt_path: Path, active_workers: list[tuple[str, str]]
) -> list[str]:
    """Return active swarm worker names matching `wt_path`."""
    raw_str = str(wt_path)
    resolved_str = str(wt_path.resolve()) if wt_path.exists() else raw_str
    dir_name = wt_path.name
    hits: list[str] = []
    for name, ws in active_workers:
        if ws:
            ws_res = str(Path(ws).resolve()) if Path(ws).exists() else ws
            if ws == raw_str or ws_res == resolved_str:
                hits.append(name or ws)
                continue
        if name and dir_name.startswith(f"swarm-{name}-"):
            hits.append(name)
    return sorted(set(hits))


def dir_disk_usage(root_dir: Path) -> tuple[int, int]:
    """Return `(total_bytes, exclusive_bytes)` via fast `os.scandir` walk."""
    if not root_dir.exists():
        return 0, 0
    seen_inodes: dict[tuple[int, int], tuple[int, int, int]] = {}
    stack: list[Path] = [root_dir]
    while stack:
        cur = stack.pop()
        try:
            with os.scandir(cur) as it:
                for entry in it:
                    try:
                        st = entry.stat(follow_symlinks=False)
                    except OSError:
                        continue
                    if entry.is_dir(follow_symlinks=False):
                        stack.append(Path(entry.path))
                        continue
                    key = (st.st_dev, st.st_ino)
                    bsize = st.st_blocks * 512 if st.st_blocks else st.st_size
                    if key in seen_inodes:
                        cnt, nlink, prev_sz = seen_inodes[key]
                        seen_inodes[key] = (cnt + 1, nlink, prev_sz)
                    else:
                        seen_inodes[key] = (1, st.st_nlink, bsize)
        except OSError:
            continue

    total = sum(sz for _, _, sz in seen_inodes.values())
    exclusive = sum(
        sz for cnt, nlink, sz in seen_inodes.values() if cnt >= nlink
    )
    return total, exclusive


BEE_DIR_RE = re.compile(r"bee-[^/]+")


def is_bee_wt(wt_path: Path) -> bool:
    """Return True iff `wt_path` is a protected `bee-*/wt` build worktree."""
    candidates = [wt_path.parts]
    if wt_path.exists():
        candidates.append(wt_path.resolve().parts)
    for parts in candidates:
        if len(parts) >= 2 and parts[-1] == "wt" and BEE_DIR_RE.fullmatch(parts[-2]):
            return True
    return False


def is_bee4_wt(wt_path: Path) -> bool:
    """Backward-compatible alias for `is_bee_wt`."""
    return is_bee_wt(wt_path)


def is_swarm_worktree(wt_path: Path) -> bool:
    """Return True iff `wt_path` is a `swarm-*` worker worktree."""
    if wt_path.name.startswith("swarm-"):
        return True
    if wt_path.exists() and wt_path.resolve().name.startswith("swarm-"):
        return True
    return False


def is_vartmp_path(wt_path: Path) -> bool:
    """Return True iff `wt_path` resides under `/var/tmp`."""
    vt = Path("/var/tmp")
    if wt_path == vt or vt in wt_path.parents:
        return True
    if wt_path.exists():
        rp = wt_path.resolve()
        if rp == vt or vt in rp.parents:
            return True
    return False


def is_current_worktree(wt_path: Path, cwd: Path, repo_root: Path) -> bool:
    """Return True if `cwd` or `repo_root` equals or is inside `wt_path`."""
    candidates = [cwd]
    if repo_root != cwd:
        candidates.append(repo_root)
    wt_res = wt_path.resolve() if wt_path.exists() else wt_path
    for p in candidates:
        p_res = p.resolve() if p.exists() else p
        if p_res == wt_res or wt_res in p_res.parents:
            return True
    return False


def detect_active_lake_cache_dir(repo: Path) -> Path | None:
    """Determine active `$LAKE_CACHE_DIR` via env or `lake env`."""
    env_val = os.environ.get("LAKE_CACHE_DIR", "").strip()
    if env_val:
        return Path(env_val).expanduser().resolve()
    res = subprocess.run(
        ["lake", "env"],
        cwd=str(repo),
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode == 0:
        for ln in res.stdout.splitlines():
            if ln.startswith("LAKE_CACHE_DIR="):
                val = ln.split("=", 1)[1].strip()
                if val:
                    return Path(val).expanduser().resolve()
    return None


def find_dead_lake_caches(
    repo: Path,
    *,
    home: Path | None = None,
    apply: bool = False,
    prune_dead_cache: bool = False,
) -> tuple[str | None, list[DeadCacheReport]]:
    """Report dead Lake cache dirs when `$LAKE_CACHE_DIR` points elsewhere."""
    active = detect_active_lake_cache_dir(repo)
    if active is None:
        return None, []
    home_dir = home or Path.home()
    candidates = [
        home_dir / ".cache" / "lake",
        home_dir / ".cache" / "lean-qbe-lake",
    ]
    reports: list[DeadCacheReport] = []
    for cand in candidates:
        if not cand.is_dir():
            continue
        cand_res = cand.resolve()
        if cand_res == active:
            continue
        if active in cand_res.parents or cand_res in active.parents:
            continue
        # Only flag directories that have actual Lake cache layout.
        if not ((cand / "artifacts").is_dir() or (cand / "outputs").is_dir()):
            continue
        total_b, _ = dir_disk_usage(cand)
        action = "report"
        if prune_dead_cache:
            action = "prune" if not apply else "removed"
            if apply:
                shutil.rmtree(cand)
        reports.append(
            DeadCacheReport(
                path=str(cand),
                size_bytes=total_b,
                action=action,
            )
        )
    return str(active), reports


def classify_worktrees(
    repo: Path,
    *,
    base_ref: str = "refs/heads/leanqbe/main",
    all_anchored: bool = False,
    include_vartmp: bool = False,
    include_non_swarm: bool = False,
    include_bee: bool = False,
    protect_patterns: list[str] | None = None,
    procs: list[tuple[int, str, str]] | None = None,
    active_workers: list[tuple[str, str]] | None = None,
    cwd: Path | None = None,
) -> list[WorktreeDecision]:
    """Classify every git worktree as `prune`, `prune_metadata`, or `keep`."""
    entries = parse_worktree_list(repo)
    ref_map = load_leanqbe_ref_map(repo)
    live_procs = procs if procs is not None else collect_running_processes()
    workers = active_workers if active_workers is not None else []
    cur_cwd = (cwd or Path.cwd()).resolve()
    prot_pats = protect_patterns or []

    decisions: list[WorktreeDecision] = []
    for idx, wt in enumerate(entries):
        head = wt.head or ""
        if wt.bare or idx == 0:
            decisions.append(
                WorktreeDecision(
                    path=str(wt.path),
                    head=head,
                    branch=wt.branch,
                    detached=wt.detached,
                    action="keep",
                    reason="primary_or_bare",
                    size_bytes=0,
                    exclusive_bytes=0,
                    is_ancestor_of_base=False,
                    anchored_by_other_ref=False,
                    anchored_refs=[],
                    dirty=False,
                    active_pids=[],
                    active_workers=[],
                )
            )
            continue

        if not wt.path.exists():
            decisions.append(
                WorktreeDecision(
                    path=str(wt.path),
                    head=head,
                    branch=wt.branch,
                    detached=wt.detached,
                    action="prune_metadata",
                    reason="missing_directory",
                    size_bytes=0,
                    exclusive_bytes=0,
                    is_ancestor_of_base=False,
                    anchored_by_other_ref=False,
                    anchored_refs=[],
                    dirty=None,
                    active_pids=[],
                    active_workers=[],
                )
            )
            continue

        refs_for_head = ref_map.get(head, [])
        other_refs = [r for r in refs_for_head if r != wt.branch]
        anc = is_ancestor(repo, head, base_ref)
        anchored = bool(other_refs)
        pids = find_matching_pids(wt.path, live_procs)
        w_hits = find_matching_workers(wt.path, workers)
        dirty = is_dirty_worktree(wt.path)
        tot_b, excl_b = dir_disk_usage(wt.path)

        in_vartmp = is_vartmp_path(wt.path)
        allow_non_swarm = include_non_swarm or (
            include_bee and is_bee_wt(wt.path)
        )
        reason = ""
        action = "keep"
        if is_current_worktree(wt.path, cur_cwd, repo):
            reason = "current_worktree"
        elif is_bee_wt(wt.path) and not include_bee:
            reason = "protected_bee_wt"
        elif any(pat in str(wt.path) for pat in prot_pats):
            reason = "protected_pattern"
        elif wt.locked:
            reason = "locked_worktree"
        elif in_vartmp and not include_vartmp:
            reason = "vartmp_excluded"
        elif (
            (not in_vartmp)
            and (not is_swarm_worktree(wt.path))
            and (not allow_non_swarm)
        ):
            reason = "non_swarm_excluded"
        elif pids:
            reason = "active_pid"
        elif w_hits:
            reason = "active_swarm_worker"
        elif dirty is None:
            reason = "git_status_error"
        elif dirty:
            reason = "dirty_worktree"
        elif anc:
            action = "prune"
            reason = "ancestor_of_base"
        elif all_anchored and anchored:
            action = "prune"
            reason = "anchored_by_other_leanqbe_ref"
        elif anchored:
            reason = "anchored_only_needs_all_anchored"
        else:
            reason = "unmerged_and_unanchored"

        decisions.append(
            WorktreeDecision(
                path=str(wt.path),
                head=head,
                branch=wt.branch,
                detached=wt.detached,
                action=action,
                reason=reason,
                size_bytes=tot_b,
                exclusive_bytes=excl_b,
                is_ancestor_of_base=anc,
                anchored_by_other_ref=anchored,
                anchored_refs=other_refs,
                dirty=dirty,
                active_pids=pids,
                active_workers=w_hits,
            )
        )
    return decisions


def apply_pruning(
    repo: Path, decisions: list[WorktreeDecision]
) -> tuple[list[str], list[dict[str, str]]]:
    """Remove approved worktrees and prune stale metadata."""
    removed: list[str] = []
    errors: list[dict[str, str]] = []
    need_meta_prune = False
    for d in decisions:
        if d.action == "prune_metadata":
            need_meta_prune = True
            continue
        if d.action != "prune":
            continue
        # Remove via `git worktree remove` (re-check clean status inside git).
        res = subprocess.run(
            git_base_cmd(repo, "worktree", "remove", d.path),
            capture_output=True,
            text=True,
            check=False,
        )
        if res.returncode == 0:
            removed.append(d.path)
        else:
            errors.append(
                {
                    "path": d.path,
                    "error": (res.stderr or res.stdout).strip(),
                }
            )
    if need_meta_prune or removed:
        subprocess.run(
            git_base_cmd(repo, "worktree", "prune"),
            capture_output=True,
            check=False,
        )
    return removed, errors


def build_summary(
    repo: Path,
    *,
    base_ref: str,
    apply: bool,
    all_anchored: bool,
    include_vartmp: bool,
    include_non_swarm: bool = False,
    include_bee: bool = False,
    prune_dead_cache: bool,
    decisions: list[WorktreeDecision],
    active_cache: str | None,
    dead_caches: list[DeadCacheReport],
    removed_paths: list[str],
    errors: list[dict[str, str]],
) -> dict[str, object]:
    """Assemble structured summary dictionary for human and JSON output."""
    prunable = [d for d in decisions if d.action == "prune"]
    meta_only = [d for d in decisions if d.action == "prune_metadata"]
    kept = [d for d in decisions if d.action == "keep"]
    anch_extra = [
        d for d in kept if d.reason == "anchored_only_needs_all_anchored"
    ]

    wt_bytes = sum(d.size_bytes for d in prunable)
    wt_excl_bytes = sum(d.exclusive_bytes for d in prunable)
    anch_extra_bytes = sum(d.size_bytes for d in anch_extra)
    dead_cache_bytes = sum(c.size_bytes for c in dead_caches)
    dead_cache_prune_bytes = sum(
        c.size_bytes for c in dead_caches if c.action in ("prune", "removed")
    )

    reason_counts: dict[str, int] = {}
    for d in decisions:
        reason_counts[d.reason] = reason_counts.get(d.reason, 0) + 1

    return {
        "mode": "apply" if apply else "dry-run",
        "repo": str(repo),
        "base": base_ref,
        "all_anchored": all_anchored,
        "include_vartmp": include_vartmp,
        "include_non_swarm": include_non_swarm,
        "include_bee": include_bee,
        "prune_dead_cache": prune_dead_cache,
        "total_worktrees": len(decisions),
        "prunable_count": len(prunable),
        "prunable_metadata_count": len(meta_only),
        "kept_count": len(kept),
        "reclaimable_bytes": wt_bytes,
        "reclaimable_gib": round(wt_bytes / GIB, 3),
        "exclusive_reclaimable_bytes": wt_excl_bytes,
        "exclusive_reclaimable_gib": round(wt_excl_bytes / GIB, 3),
        "anchored_extra_count": len(anch_extra),
        "anchored_extra_gib": round(anch_extra_bytes / GIB, 3),
        "active_lake_cache_dir": active_cache,
        "dead_caches": [asdict(c) for c in dead_caches],
        "dead_cache_total_gib": round(dead_cache_bytes / GIB, 3),
        "dead_cache_reclaimable_gib": round(dead_cache_prune_bytes / GIB, 3),
        "total_reclaimable_gib": round(
            (wt_bytes + dead_cache_prune_bytes) / GIB, 3
        ),
        "reason_counts": reason_counts,
        "removed_worktrees": removed_paths,
        "errors": errors,
        "prunable_worktrees": [asdict(d) for d in prunable],
        "kept_worktrees": [asdict(d) for d in kept],
    }


def format_human(summary: dict[str, object]) -> str:
    """Render concise human-readable disk-reclamation report."""
    lines = [
        f"prune_worktrees ({summary['mode']}, base={summary['base']}, "
        f"all_anchored={summary['all_anchored']}, "
        f"include_vartmp={summary['include_vartmp']}, "
        f"include_non_swarm={summary.get('include_non_swarm', False)}):",
        f"  worktrees: total={summary['total_worktrees']}, "
        f"prunable={summary['prunable_count']}, "
        f"kept={summary['kept_count']}, "
        f"missing_meta={summary['prunable_metadata_count']}",
        f"  worktree disk: {summary['reclaimable_gib']:.2f} GiB "
        f"(exclusive fs blocks: {summary['exclusive_reclaimable_gib']:.2f} GiB)",
    ]
    if not summary["all_anchored"] and summary["anchored_extra_count"]:
        lines.append(
            f"  note (--all-anchored): +{summary['anchored_extra_count']} "
            f"worktrees ({summary['anchored_extra_gib']:.2f} GiB) anchored by "
            f"other refs/heads/leanqbe/*"
        )
    lines.append(
        f"  active $LAKE_CACHE_DIR: {summary['active_lake_cache_dir'] or 'unknown'}"
    )
    for c in summary["dead_caches"]:  # type: ignore[attr-defined]
        lines.append(
            f"  dead cache [{c['action']}]: {c['path']} "
            f"({c['size_bytes'] / GIB:.2f} GiB)"
        )
    lines.append(f"  reasons: {summary['reason_counts']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for `scripts/prune_worktrees.py`."""
    ap = argparse.ArgumentParser(
        description="Safely prune merged/anchored secondary git worktrees."
    )
    ap.add_argument("--root", default=None, help="Git repo or worktree root.")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument(
        "--dry-run",
        action="store_true",
        help="Report prunable worktrees without deleting anything (default).",
    )
    mode.add_argument(
        "--apply",
        action="store_true",
        help="Actually remove approved clean secondary worktrees.",
    )
    ap.add_argument(
        "--base",
        default="refs/heads/leanqbe/main",
        help="Base commit/ref for ancestor check (default: refs/heads/leanqbe/main).",
    )
    ap.add_argument(
        "--all-anchored",
        action="store_true",
        help="Also prune clean secondary worktrees anchored by other refs/heads/leanqbe/*.",
    )
    ap.add_argument(
        "--include-vartmp",
        action="store_true",
        help="Allow pruning secondary worktrees under /var/tmp.",
    )
    ap.add_argument(
        "--include-non-swarm",
        action="store_true",
        help="Allow pruning non-`swarm-*` worktrees outside /var/tmp (excluding bee-*/wt).",
    )
    ap.add_argument(
        "--include-bee",
        action="store_true",
        help="Allow pruning `/monorepo-work/builds/bee-*/wt` worktrees.",
    )
    ap.add_argument(
        "--prune-dead-cache",
        action="store_true",
        help="With --apply, also remove dead non-active Lake cache directories.",
    )
    ap.add_argument(
        "--swarm-status",
        default=None,
        help="Optional JSON file (or '-' for stdin) with swarm status members.",
    )
    ap.add_argument(
        "--protect",
        action="append",
        default=[],
        help="Additional path substring to protect unconditionally (repeatable).",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON output.",
    )
    args = ap.parse_args(argv)

    repo = resolve_repo_root(args.root)
    active_workers = load_active_swarm_workers(args.swarm_status)
    decisions = classify_worktrees(
        repo,
        base_ref=args.base,
        all_anchored=args.all_anchored,
        include_vartmp=args.include_vartmp,
        include_non_swarm=args.include_non_swarm,
        include_bee=args.include_bee,
        protect_patterns=args.protect,
        active_workers=active_workers,
    )
    removed: list[str] = []
    errors: list[dict[str, str]] = []
    if args.apply:
        removed, errors = apply_pruning(repo, decisions)

    active_cache, dead_caches = find_dead_lake_caches(
        repo,
        apply=bool(args.apply),
        prune_dead_cache=bool(args.prune_dead_cache),
    )
    summary = build_summary(
        repo,
        base_ref=args.base,
        apply=bool(args.apply),
        all_anchored=bool(args.all_anchored),
        include_vartmp=bool(args.include_vartmp),
        include_non_swarm=bool(args.include_non_swarm),
        include_bee=bool(args.include_bee),
        prune_dead_cache=bool(args.prune_dead_cache),
        decisions=decisions,
        active_cache=active_cache,
        dead_caches=dead_caches,
        removed_paths=removed,
        errors=errors,
    )
    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        print(format_human(summary))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
