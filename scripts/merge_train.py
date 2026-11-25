#!/usr/bin/env python3
"""Deterministic Bors/Zuul bisecting merge train with HoL bypass (N10 + N8 + P2-2).

Combines candidate branches onto `--base` (`leanqbe/main`):
  1. Enforces N8 (`STANDALONE_GREEN` vs partial `TRAIN_SHARD` gating).
  2. Classifies candidates via `classify_branch` (`infra_fast` -> `disjoint_fast`
     -> `core_heavy`) and partitions into HoL-bypassing fast/heavy lanes
     (`partition_lanes` / `--lane auto|fast|heavy|all`).
  3. Verifies each candidate via zero-disk `git merge-tree --write-tree`.
  4. Combines passing candidates in a staging worktree, runs `sync_hubs.py --write`,
     checks `rdeps` / N9 Canary Frontier `--wfail` under P2-2 2-lane `flock`
     (`CHECK_BUILD_LANE=1|2`).
  5. If any batch fails, binary-bisects in `O(log k)` trials to eject ONLY
     the failing PR(s) while keeping cleanly passing PRs.
  6. Invokes `scripts/fast_land.sh` + atomic `git update-ref` CAS ONLY post-pass.
"""

from __future__ import annotations

import argparse
import collections
import contextlib
import fcntl
import json
import os
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Callable, Iterator, TypeVar

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from l2_audit import (  # noqa: E402
    CORE_TRIGGER_RE,
    execute_lake_build,
    plan_rdeps_and_canary,
    resolve_commit,
    run_firewall_check,
    run_merge_tree,
    run_sync_hubs_check,
)
from lean_imports import (  # noqa: E402
    IMPORT_LINE_RE,
    LEGACY_CERT_RE,
    parse_imports,
    rel_path_to_mod,
    strip_comments_line,
)
from rdeps_scope import BARRELS, _is_kraken_path  # noqa: E402
from sync_hubs import ROOT_LIBS  # noqa: E402

T = TypeVar("T")

TRAIN_SHARD_RE = re.compile(r"\bTRAIN_SHARD\b")
STANDALONE_GREEN_RE = re.compile(r"\bSTANDALONE_GREEN\b")

LANE_INFRA_FAST = "infra_fast"
LANE_DISJOINT_FAST = "disjoint_fast"
LANE_CORE_HEAVY = "core_heavy"
LANE_CHOICES: tuple[str, ...] = ("auto", "fast", "heavy", "all")

LANE_PRIORITY: dict[str, int] = {
    LANE_INFRA_FAST: 0,
    LANE_DISJOINT_FAST: 1,
    LANE_CORE_HEAVY: 2,
}
LANE_BUILD_SLOT: dict[str, int] = {
    LANE_INFRA_FAST: 1,
    LANE_DISJOINT_FAST: 1,
    LANE_CORE_HEAVY: 2,
}

SMALL_RDEPS_MAX = 25
DEFAULT_WORKTREE = Path("/var/tmp/wt-pool/merge-train")
DEFAULT_HEAVY_LOCK_FILE = "/tmp/leanqbe_check_build.lock"
DEFAULT_FAST_LOCK_PREFIX = "/tmp/leanqbe_check_fast"

INFRA_PREFIXES: tuple[str, ...] = (
    "scripts/",
    "test/",
    "bench/",
    "docs/",
    "tool/",
    ".github/",
    "LeanQbeLegacyTest/",
)
TOP_HUB_FILES: frozenset[str] = frozenset(f"{m}.lean" for m in ROOT_LIBS)
TOP_DOC_FILES: frozenset[str] = frozenset({"LICENSE", ".gitignore", ".gitattributes"})
TOOLCHAIN_CORE_FILES: frozenset[str] = frozenset(
    {
        "lean-toolchain",
        "lake-manifest.json",
        "Main.lean",
        "MainArm64.lean",
        "Att2Intel.lean",
        "Bedrock2C.lean",
    }
)
CERT_SLICE_PATH_RE = re.compile(
    r"^LeanQbe/T/(?:"
    r"(?:Amd64|Arm64)/Kissat.*Cert[^/]*\.lean"
    r"|Bootstrap0/Cert[^/]*\.lean"
    r"|Examples/Kissat/.*Cert[^/]*\.lean"
    r"|MainCert[^/]*\.lean"
    r")$"
)
KISSAT_C0_OR_CERT_PATH_RE = re.compile(
    r"^LeanQbe/T/(?:"
    r"(?:Amd64|Arm64)/Kissat[^/]*\.lean"
    r"|Examples/Kissat/.*\.lean"
    r"|Bootstrap0/Cert[^/]*\.lean"
    r"|MainCert[^/]*\.lean"
    r"|InterpKissat\.lean"
    r")$"
)
CERT_SLICE_MOD_RE = re.compile(
    r"^LeanQbe\.T\.(?:"
    r"(?:Amd64|Arm64)\.Kissat.*Cert"
    r"|Bootstrap0\.Cert"
    r"|Examples\.Kissat\..*Cert"
    r"|MainCert"
    r")"
)


@dataclass
class Candidate:
    """Candidate branch/commit entering the merge train."""

    branch: str
    sha: str
    lane: str = LANE_CORE_HEAVY
    priority: int = 2
    build_lane: int = 2
    classification: dict[str, object] = field(default_factory=dict)


@dataclass
class EjectedPR:
    """Candidate rejected during pre-screen or O(log k) bisection."""

    branch: str
    sha: str
    reason: str
    detail: dict[str, object]


def _is_infra_fast_path(path: str) -> bool:
    """Return True if `path` is an infra/test/bench/lakefile/top-hub/doc path."""
    if path == "lakefile.toml" or path in TOP_HUB_FILES or path in TOP_DOC_FILES:
        return True
    if "/" not in path and path.endswith(".md"):
        return True
    return path.startswith(INFRA_PREFIXES)


def is_cert_slice_module(mod: str) -> bool:
    """Return True if Lean module `mod` is a Kissat or Bootstrap0 cert slice."""
    return bool(CERT_SLICE_MOD_RE.match(mod))


def _diff_name_status(
    repo: Path, base_sha: str, target_sha: str
) -> tuple[list[str], set[str], set[str]]:
    """Return `(changed_paths, deleted_paths, renamed_legacy_sources)`."""
    res = subprocess.run(
        ["git", "-C", str(repo), "diff", "--name-status", f"{base_sha}...{target_sha}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        res = subprocess.run(
            ["git", "-C", str(repo), "diff", "--name-status", base_sha, target_sha],
            capture_output=True,
            text=True,
            check=True,
        )
    changed: list[str] = []
    deleted: set[str] = set()
    renamed_legacy: set[str] = set()
    for raw in res.stdout.splitlines():
        if not raw.strip():
            continue
        parts = raw.split("\t")
        st = parts[0]
        if st.startswith(("R", "C")) and len(parts) >= 3:
            old_p, new_p = parts[1], parts[2]
            changed.append(new_p)
            if new_p.startswith("LeanQbeLegacyTest/"):
                renamed_legacy.add(old_p)
        elif st.startswith("D"):
            path = parts[-1]
            changed.append(path)
            deleted.add(path)
        else:
            changed.append(parts[-1])
    return sorted(set(changed)), deleted, renamed_legacy


def _parse_imports_from_text(text: str) -> list[str]:
    """Extract imported module names from a Lean file string."""
    uses_module_system = False
    seen_header = False
    mods: list[str] = []
    depth = 0
    for raw_line in text.splitlines():
        s, depth, _ = strip_comments_line(raw_line, depth)
        if not s:
            continue
        if not seen_header and s in ("module", "prelude"):
            if s == "module":
                uses_module_system = True
            seen_header = True
            continue
        m = IMPORT_LINE_RE.match(s)
        if m:
            seen_header = True
            _ = uses_module_system
            mods.append(m.group(4))
            continue
        if seen_header or depth == 0:
            break
    return mods


def _ls_tree_lean_oids(repo: Path, rev: str) -> dict[str, str]:
    """Return `{repo_rel_path: blob_oid}` for all `.lean` files at `rev`."""
    res = subprocess.run(
        ["git", "-C", str(repo), "ls-tree", "-r", "-z", rev],
        capture_output=True,
        check=False,
    )
    if res.returncode != 0:
        return {}
    out: dict[str, str] = {}
    for rec in res.stdout.split(b"\0"):
        if not rec or b"\t" not in rec:
            continue
        meta, raw_path = rec.split(b"\t", 1)
        path = raw_path.decode("utf-8", errors="replace")
        if path.endswith(".lean"):
            parts = meta.split()
            if len(parts) >= 3:
                out[path] = parts[2].decode("ascii", errors="replace")
    return out


def compute_commit_lean_rdeps(
    repo: Path,
    target_sha: str,
    changed: list[str],
    *,
    deleted: set[str] | None = None,
    include_legacy: bool = False,
    import_cache: dict[str, list[str]] | None = None,
) -> list[str] | None:
    """Compute exact non-barrel Lean reverse-import closure at `target_sha`."""
    del_set = deleted or set()
    for f in changed:
        if f in del_set and f.endswith(".lean"):
            return None

    lean_changed = [f for f in changed if f.endswith(".lean")]
    if not lean_changed:
        return []

    tree_oids = _ls_tree_lean_oids(repo, target_sha)
    if not tree_oids:
        return None

    seeds: set[str] = set()
    touched_barrels: list[str] = []
    for f in lean_changed:
        rel = Path(f)
        if _is_kraken_path(rel) or f not in tree_oids:
            return None
        mod = rel_path_to_mod(rel)
        if mod in BARRELS:
            touched_barrels.append(f)
        else:
            seeds.add(mod)

    if not seeds:
        return None if touched_barrels else []

    head_oids = _ls_tree_lean_oids(repo, "HEAD")
    dirty_res = subprocess.run(
        ["git", "-C", str(repo), "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=False,
    )
    dirty_paths = {
        ln[3:].split(" -> ")[-1].strip()
        for ln in dirty_res.stdout.splitlines()
        if len(ln) > 3
    }

    cache = import_cache if import_cache is not None else {}
    rgraph: dict[str, list[str]] = collections.defaultdict(list)
    for path, oid in tree_oids.items():
        rel = Path(path)
        if _is_kraken_path(rel):
            continue
        mod = rel_path_to_mod(rel)
        if mod in BARRELS:
            continue
        if not include_legacy and mod not in seeds:
            if rel.parts and rel.parts[0] == "LeanQbeLegacyTest":
                continue
            if LEGACY_CERT_RE.match(mod):
                continue
        imps = cache.get(oid)
        if imps is None:
            disk_p = repo / rel
            if head_oids.get(path) == oid and path not in dirty_paths and disk_p.is_file():
                imps = [stmt.module for stmt in parse_imports(disk_p)[1]]
            else:
                blob = subprocess.run(
                    ["git", "-C", str(repo), "cat-file", "blob", oid],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                imps = _parse_imports_from_text(blob.stdout) if blob.returncode == 0 else []
            cache[oid] = imps
        for imp_mod in imps:
            if imp_mod not in BARRELS:
                rgraph[imp_mod].append(mod)

    seen = set(seeds)
    q: collections.deque[str] = collections.deque(sorted(seeds))
    while q:
        cur = q.popleft()
        for nxt in rgraph.get(cur, ()):
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return sorted(seen)


def classify_branch(
    repo: Path,
    base_ref: str,
    branch_or_sha: str,
    *,
    changed_files: list[str] | None = None,
    rdeps_mods: list[str] | None = None,
    small_rdeps_cap: int = SMALL_RDEPS_MAX,
    _import_cache: dict[str, list[str]] | None = None,
) -> dict[str, object]:
    """Classify a candidate PR vs `base_ref` into fast/heavy merge-train lanes.

    Lanes:
      - `infra_fast` (priority 0): touches `scripts/`, `test/`, `bench/`,
        `lakefile.toml`, or top-level hub/doc files without `LeanQbe/T/*.lean`.
      - `disjoint_fast` (priority 1): `rdeps <= small_rdeps_cap` and 0 cert slices.
      - `core_heavy` (priority 2): compiler core, Kissat C0, cert slices, or
        large `rdeps` (`CHECK_BUILD_LANE=2`).
    """
    base_sha = resolve_commit(repo, base_ref)
    target_sha = resolve_commit(repo, branch_or_sha)
    if changed_files is None:
        changed, deleted, _ = _diff_name_status(repo, base_sha, target_sha)
    else:
        changed = sorted({p.strip() for p in changed_files if p.strip()})
        deleted = set()

    touches_leanqbe_t = any(
        p.startswith("LeanQbe/T/") and p.endswith(".lean") for p in changed
    )
    touches_toolchain_or_kraken = any(
        p in TOOLCHAIN_CORE_FILES or _is_kraken_path(Path(p)) for p in changed
    )
    touches_core_trigger = any(CORE_TRIGGER_RE.match(p) for p in changed)
    direct_cert_paths = [p for p in changed if CERT_SLICE_PATH_RE.match(p)]
    touches_kissat_or_cert = any(
        KISSAT_C0_OR_CERT_PATH_RE.match(p) for p in changed
    )

    if (
        changed
        and not touches_leanqbe_t
        and not touches_toolchain_or_kraken
        and all(_is_infra_fast_path(p) for p in changed)
    ):
        lane = LANE_INFRA_FAST
        reason = "infra_fast_paths_only"
        rdeps_count: int | None = 0
        rdeps_sample: list[str] = []
        cert_slices: list[str] = []
    elif touches_toolchain_or_kraken or touches_core_trigger or touches_kissat_or_cert:
        lane = LANE_CORE_HEAVY
        if direct_cert_paths:
            reason = "touches_cert_slices"
        elif touches_kissat_or_cert:
            reason = "touches_kissat_c0_or_cert"
        else:
            reason = "touches_compiler_core"
        if rdeps_mods is not None:
            rdeps_count = len(rdeps_mods)
            rdeps_sample = rdeps_mods[:25]
            cert_slices = sorted(
                set(direct_cert_paths)
                | {m for m in rdeps_mods if is_cert_slice_module(m)}
            )
        else:
            rdeps_count = None
            rdeps_sample = []
            cert_slices = direct_cert_paths
    else:
        mods = (
            list(rdeps_mods)
            if rdeps_mods is not None
            else compute_commit_lean_rdeps(
                repo,
                target_sha,
                changed,
                deleted=deleted,
                import_cache=_import_cache,
            )
        )
        if mods is None:
            lane = LANE_CORE_HEAVY
            reason = "rdeps_fail_closed"
            rdeps_count = None
            rdeps_sample = []
            cert_slices = direct_cert_paths
        else:
            cert_slices = [m for m in mods if is_cert_slice_module(m)]
            rdeps_count = len(mods)
            rdeps_sample = mods[:25]
            if cert_slices:
                lane = LANE_CORE_HEAVY
                reason = "rdeps_includes_cert_slices"
            elif rdeps_count > small_rdeps_cap:
                lane = LANE_CORE_HEAVY
                reason = f"rdeps_exceeds_{small_rdeps_cap}"
            else:
                lane = LANE_DISJOINT_FAST
                reason = "small_rdeps_disjoint" if changed else "empty_diff"

    return {
        "branch": branch_or_sha,
        "sha": target_sha,
        "base_sha": base_sha,
        "lane": lane,
        "priority": LANE_PRIORITY[lane],
        "build_lane": LANE_BUILD_SLOT[lane],
        "reason": reason,
        "changed_files": changed,
        "rdeps_count": rdeps_count,
        "rdeps_sample": rdeps_sample,
        "cert_slices": cert_slices,
    }


def _check_pairwise_merge_tree(
    repo: Path, base_sha: str, a: Candidate, b: Candidate
) -> tuple[bool, list[str]]:
    """Run zero-disk 3-way `git merge-tree --write-tree` for two candidates."""
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
    if res.returncode == 0:
        return True, []
    lines = [ln for ln in res.stdout.splitlines() if "CONFLICT" in ln]
    return False, lines[:10]


def partition_lanes(
    repo: Path,
    base_ref: str,
    candidates: list[Candidate] | list[str],
    *,
    small_rdeps_cap: int = SMALL_RDEPS_MAX,
) -> dict[str, object]:
    """Sort candidates (`infra_fast` first) and split into fast vs heavy batches.

    Fast candidates (`infra_fast` + `disjoint_fast`) that conflict with
    `core_heavy` are deferred into `heavy_batch` so HoL bypass never lands a
    conflicting change ahead of `core_heavy`. Candidates conflicting with
    `base_ref` are reported in `base_conflicts`.
    """
    base_sha = resolve_commit(repo, base_ref)
    import_cache: dict[str, list[str]] = {}
    enriched: list[tuple[int, Candidate]] = []
    classifications: dict[str, dict[str, object]] = {}

    for idx, item in enumerate(candidates):
        if isinstance(item, str):
            sha = resolve_commit(repo, item)
            cand = Candidate(branch=item, sha=sha)
        else:
            cand = item
        info = classify_branch(
            repo,
            base_sha,
            cand.sha,
            small_rdeps_cap=small_rdeps_cap,
            _import_cache=import_cache,
        )
        info["branch"] = cand.branch
        classifications[cand.branch] = info
        enriched.append(
            (
                idx,
                Candidate(
                    branch=cand.branch,
                    sha=cand.sha,
                    lane=str(info["lane"]),
                    priority=int(info["priority"]),  # type: ignore[arg-type]
                    build_lane=int(info["build_lane"]),  # type: ignore[arg-type]
                    classification=info,
                ),
            )
        )

    ordered_pairs = sorted(enriched, key=lambda pair: (pair[1].priority, pair[0]))
    ordered = [cand for _, cand in ordered_pairs]

    fast_batch: list[Candidate] = []
    heavy_pairs: list[tuple[int, Candidate]] = []
    heavy_deferred: list[tuple[int, Candidate]] = []
    base_conflicts: list[Candidate] = []
    deferred_meta: list[dict[str, object]] = []

    for idx, cand in ordered_pairs:
        base_mt = run_merge_tree(repo, base_sha, cand.sha)
        if not base_mt["clean"]:
            base_conflicts.append(cand)
        elif cand.lane == LANE_CORE_HEAVY:
            heavy_pairs.append((idx, cand))

    for idx, cand in ordered_pairs:
        if cand.lane == LANE_CORE_HEAVY or cand in base_conflicts:
            continue
        conflict_heavy: str | None = None
        conflict_lines: list[str] = []
        for _, hc in heavy_pairs:
            ok_pair, lines = _check_pairwise_merge_tree(repo, base_sha, cand, hc)
            if not ok_pair:
                conflict_heavy = hc.branch
                conflict_lines = lines
                break
        if conflict_heavy is not None:
            heavy_deferred.append((idx, cand))
            deferred_meta.append(
                {
                    "branch": cand.branch,
                    "sha": cand.sha,
                    "lane": cand.lane,
                    "conflicts_with": conflict_heavy,
                    "conflicts": conflict_lines,
                    "reason": "conflicts_with_core_heavy",
                }
            )
        else:
            fast_batch.append(cand)

    # Preserve input order when deferred fast candidates share heavy batch.
    heavy_combined = sorted(
        heavy_pairs + heavy_deferred,
        key=lambda pair: pair[0],
    )
    heavy_batch = [cand for _, cand in heavy_combined]

    return {
        "base_sha": base_sha,
        "ordered": ordered,
        "fast_batch": fast_batch,
        "heavy_batch": heavy_batch,
        "base_conflicts": base_conflicts,
        "deferred_to_heavy": deferred_meta,
        "classifications": classifications,
    }


def _try_resolve_branch_ref(repo: Path, base_ref: str) -> str | None:
    """Return full `refs/heads/<name>` if `base_ref` names a local branch."""
    if base_ref.startswith("refs/heads/"):
        cand = base_ref
    elif base_ref.startswith("refs/"):
        return None
    else:
        cand = f"refs/heads/{base_ref}"
    res = subprocess.run(
        ["git", "-C", str(repo), "show-ref", "--verify", "--quiet", cand],
        capture_output=True,
        check=False,
    )
    return cand if res.returncode == 0 else None


def _try_resolve_commit(repo: Path, ref: str) -> str | None:
    """Resolve `ref` to commit SHA, returning None if unresolvable."""
    try:
        return resolve_commit(repo, ref)
    except RuntimeError:
        return None


def cas_update_ref(
    repo: Path,
    branch_ref: str,
    new_sha: str,
    expected_old_sha: str,
) -> dict[str, object]:
    """Atomically advance `branch_ref` from `expected_old_sha` to `new_sha`."""
    full_ref = (
        branch_ref if branch_ref.startswith("refs/") else f"refs/heads/{branch_ref}"
    )
    actual_sha = _try_resolve_commit(repo, full_ref)
    if actual_sha != expected_old_sha:
        return {
            "status": "fail",
            "reason": "cas_mismatch",
            "ref": full_ref,
            "expected": expected_old_sha,
            "actual": actual_sha,
        }
    if new_sha == expected_old_sha:
        return {
            "status": "pass",
            "ref": full_ref,
            "old_sha": expected_old_sha,
            "new_sha": new_sha,
            "noop": True,
        }
    anc = subprocess.run(
        ["git", "-C", str(repo), "merge-base", "--is-ancestor", expected_old_sha, new_sha],
        capture_output=True,
        check=False,
    )
    if anc.returncode != 0:
        return {
            "status": "fail",
            "reason": "not_fast_forward",
            "ref": full_ref,
            "expected": expected_old_sha,
            "new_sha": new_sha,
        }

    sym = subprocess.run(
        ["git", "-C", str(repo), "symbolic-ref", "-q", "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    )
    checked_out = sym.stdout.strip() if sym.returncode == 0 else None
    if checked_out == full_ref:
        head_sha = _try_resolve_commit(repo, "HEAD")
        dirty = subprocess.run(
            ["git", "-C", str(repo), "status", "--porcelain"],
            capture_output=True,
            text=True,
            check=False,
        )
        if head_sha != expected_old_sha or dirty.stdout.strip():
            return {
                "status": "fail",
                "reason": "checked_out_worktree_not_ready",
                "ref": full_ref,
                "expected": expected_old_sha,
                "head_sha": head_sha,
            }
        ff = subprocess.run(
            ["git", "-C", str(repo), "merge", "--ff-only", new_sha],
            capture_output=True,
            text=True,
            check=False,
        )
        if ff.returncode != 0:
            return {
                "status": "fail",
                "reason": "ff_merge_failed",
                "ref": full_ref,
                "output": (ff.stderr or ff.stdout).strip()[:400],
            }
    else:
        upd = subprocess.run(
            ["git", "-C", str(repo), "update-ref", full_ref, new_sha, expected_old_sha],
            capture_output=True,
            text=True,
            check=False,
        )
        if upd.returncode != 0:
            return {
                "status": "fail",
                "reason": "cas_update_ref_failed",
                "ref": full_ref,
                "output": (upd.stderr or upd.stdout).strip()[:400],
            }
    return {
        "status": "pass",
        "ref": full_ref,
        "old_sha": expected_old_sha,
        "new_sha": new_sha,
        "noop": False,
    }


@contextlib.contextmanager
def lane_build_lock(
    build_lane: int,
    *,
    lock_file: str | None = None,
    fast_lock_prefix: str | None = None,
) -> Iterator[dict[str, object]]:
    """Acquire P2-2 2-lane advisory `flock` and export `CHECK_BUILD_LANE`."""
    prev_lane = os.environ.get("CHECK_BUILD_LANE")
    os.environ["CHECK_BUILD_LANE"] = str(build_lane)
    fd: int | None = None
    lock_path: str | None = None
    try:
        if os.environ.get("CHECK_NO_LOCK") != "1":
            if build_lane == 1:
                prefix = (
                    fast_lock_prefix
                    or os.environ.get("CHECK_FAST_LOCK_PREFIX")
                    or DEFAULT_FAST_LOCK_PREFIX
                )
                for slot in (0, 1):
                    cand = f"{prefix}_{slot}.lock"
                    Path(cand).parent.mkdir(parents=True, exist_ok=True)
                    cand_fd = os.open(cand, os.O_CREAT | os.O_RDWR, 0o666)
                    try:
                        fcntl.flock(cand_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        fd = cand_fd
                        lock_path = cand
                        break
                    except BlockingIOError:
                        os.close(cand_fd)
                if fd is None:
                    slot = os.getpid() % 2
                    cand = f"{prefix}_{slot}.lock"
                    Path(cand).parent.mkdir(parents=True, exist_ok=True)
                    fd = os.open(cand, os.O_CREAT | os.O_RDWR, 0o666)
                    fcntl.flock(fd, fcntl.LOCK_EX)
                    lock_path = cand
            else:
                cand = (
                    lock_file
                    or os.environ.get("CHECK_LOCK_FILE")
                    or DEFAULT_HEAVY_LOCK_FILE
                )
                Path(cand).parent.mkdir(parents=True, exist_ok=True)
                fd = os.open(cand, os.O_CREAT | os.O_RDWR, 0o666)
                fcntl.flock(fd, fcntl.LOCK_EX)
                lock_path = cand
        yield {"lane": build_lane, "locked": fd is not None, "lock_path": lock_path}
    finally:
        if fd is not None:
            try:
                fcntl.flock(fd, fcntl.LOCK_UN)
            finally:
                os.close(fd)
        if prev_lane is None:
            os.environ.pop("CHECK_BUILD_LANE", None)
        else:
            os.environ["CHECK_BUILD_LANE"] = prev_lane


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
            ok_pair, lines = _check_pairwise_merge_tree(repo, base_sha, a, b)
            if not ok_pair:
                conflicts.append({"pair": [a.branch, b.branch], "conflicts": lines})

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
    *,
    build_lane: int | None = None,
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
    effective_lane = (
        build_lane
        if build_lane is not None
        else max((c.build_lane for c in subset), default=1)
    )
    if targets:
        with lane_build_lock(effective_lane) as lock_info:
            build_res = execute_lake_build(wt, targets)
    else:
        lock_info = {"lane": effective_lane, "locked": False, "lock_path": None}
        build_res = execute_lake_build(wt, targets)
    if build_res["status"] == "fail":
        return False, {
            "reason": "lake_build_failed",
            "build_lane": effective_lane,
            "lock_info": lock_info,
            "rdeps_canary": rdeps_info,
            "lake_build": build_res,
        }

    head_sha = subprocess.check_output(
        ["git", "-C", str(wt), "rev-parse", "HEAD"], text=True
    ).strip()
    return True, {
        "merged_sha": head_sha,
        "build_lane": effective_lane,
        "lock_info": lock_info,
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
    build_lane: int | None = None,
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
    if build_lane is not None:
        env["CHECK_BUILD_LANE"] = str(build_lane)
    res = subprocess.run(
        cmd, cwd=str(repo), env=env, capture_output=True, text=True, check=False
    )
    return {
        "status": "pass" if res.returncode == 0 else "fail",
        "returncode": res.returncode,
        "build_lane": build_lane,
        "stdout_tail": "\n".join(res.stdout.splitlines()[-30:]),
        "stderr_tail": "\n".join(res.stderr.splitlines()[-30:]),
    }


def _execute_lane_batch(
    repo: Path,
    batch: list[Candidate],
    *,
    base_ref: str,
    stage_base_sha: str,
    build_lane: int,
    worktree: Path,
    dry_run: bool,
    execute: bool,
    fast_land_skip_tests: bool,
    dry_run_prefix: list[Candidate] | None = None,
) -> dict[str, object]:
    """Bisect, stage, and optionally CAS-land one partitioned lane batch."""
    if not batch:
        return {
            "status": "skip",
            "build_lane": build_lane,
            "check_build_lane": str(build_lane),
            "base_sha": stage_base_sha,
            "accepted": [],
            "ejected": [],
            "bisect_steps": 0,
            "bisect_trace": [],
            "merged_sha": None,
            "summary_diag": {},
            "fast_land": None,
            "cas": None,
        }

    # If advancing atop an earlier fast phase, eject heavy PRs conflicting with it.
    runnable: list[Candidate] = []
    pre_batch_ejected: list[EjectedPR] = []
    for cand in batch:
        mt = run_merge_tree(repo, stage_base_sha, cand.sha)
        if not mt["clean"]:
            pre_batch_ejected.append(
                EjectedPR(
                    branch=cand.branch,
                    sha=cand.sha,
                    reason="merge_conflict_with_base",
                    detail=mt,
                )
            )
        else:
            runnable.append(cand)

    bisect_trace: list[dict[str, object]] = []
    last_good_diag: dict[str, object] = {}
    prefix = list(dry_run_prefix or [])

    def test_fn(sub: list[Candidate]) -> tuple[bool, dict[str, object]]:
        if dry_run:
            ok, diag = dry_run_test_subset(repo, stage_base_sha, prefix + sub)
        else:
            ok, diag = stage_and_verify_subset(
                repo, worktree, stage_base_sha, sub, build_lane=build_lane
            )
        if ok:
            last_good_diag.clear()
            last_good_diag.update(diag)
        return ok, diag

    accepted, bisect_bad = bisect_candidates(runnable, test_fn, trace=bisect_trace)
    ejected = pre_batch_ejected + [
        EjectedPR(
            branch=c.branch,
            sha=c.sha,
            reason=str(diag.get("reason", "bisect_failure")),
            detail=diag,
        )
        for c, diag in bisect_bad
    ]

    merged_sha: str | None = None
    if not dry_run and accepted:
        if len(ejected) > len(pre_batch_ejected) or not last_good_diag.get("merged_sha"):
            ok, final_diag = stage_and_verify_subset(
                repo, worktree, stage_base_sha, accepted, build_lane=build_lane
            )
            if ok:
                merged_sha = str(final_diag.get("merged_sha"))
                last_good_diag.clear()
                last_good_diag.update(final_diag)
        else:
            merged_sha = str(last_good_diag.get("merged_sha"))

    fast_land_res: dict[str, object] | None = None
    cas_res: dict[str, object] | None = None
    branch_ref = _try_resolve_branch_ref(repo, base_ref)
    if execute and merged_sha:
        if branch_ref is not None:
            cur_ref_sha = _try_resolve_commit(repo, branch_ref)
            if cur_ref_sha != stage_base_sha:
                cas_res = {
                    "status": "fail",
                    "reason": "cas_mismatch",
                    "ref": branch_ref,
                    "expected": stage_base_sha,
                    "actual": cur_ref_sha,
                }
                fast_land_res = {
                    "status": "fail",
                    "reason": "cas_mismatch",
                    "build_lane": build_lane,
                }
        if cas_res is None:
            fast_land_res = invoke_fast_land(
                repo,
                worktree,
                merged_sha,
                base_branch=base_ref,
                fast=fast_land_skip_tests,
                build_lane=build_lane,
            )
            if fast_land_res["status"] == "pass" and branch_ref is not None:
                post_sha = _try_resolve_commit(repo, branch_ref)
                if post_sha == stage_base_sha:
                    cas_res = cas_update_ref(
                        repo, branch_ref, merged_sha, stage_base_sha
                    )
                    if cas_res["status"] != "pass":
                        fast_land_res["status"] = "fail"
                        fast_land_res["cas_error"] = cas_res
                elif post_sha == merged_sha:
                    cas_res = {
                        "status": "pass",
                        "ref": branch_ref,
                        "old_sha": stage_base_sha,
                        "new_sha": merged_sha,
                        "updated_by": "fast_land",
                    }
                else:
                    cas_res = {
                        "status": "fail",
                        "reason": "cas_mismatch_post_fast_land",
                        "ref": branch_ref,
                        "expected": merged_sha,
                        "actual": post_sha,
                    }
                    fast_land_res["status"] = "fail"

    land_ok = (fast_land_res is None or fast_land_res["status"] == "pass") and (
        cas_res is None or cas_res["status"] == "pass"
    )
    ok_batch = bool(accepted) and land_ok
    return {
        "status": "pass" if ok_batch else "fail",
        "build_lane": build_lane,
        "check_build_lane": str(build_lane),
        "base_sha": stage_base_sha,
        "accepted": accepted,
        "ejected": ejected,
        "bisect_steps": len(bisect_trace),
        "bisect_trace": bisect_trace,
        "merged_sha": merged_sha,
        "summary_diag": last_good_diag,
        "fast_land": fast_land_res,
        "cas": cas_res,
    }


def run_merge_train(
    repo: Path,
    branches: list[str],
    *,
    base_ref: str = "leanqbe/main",
    worktree: Path = DEFAULT_WORKTREE,
    dry_run: bool = False,
    execute: bool = False,
    fast_land_skip_tests: bool = False,
    allow_shard: bool = False,
    lane: str = "auto",
    small_rdeps_cap: int = SMALL_RDEPS_MAX,
) -> dict[str, object]:
    """Execute N10 + N8 bisecting merge train with HoL bypass partitioning."""
    if execute and dry_run:
        raise ValueError("--execute cannot be combined with --dry-run")
    if lane not in LANE_CHOICES:
        raise ValueError(f"invalid lane '{lane}' (expected one of {LANE_CHOICES})")

    initial_base_sha = resolve_commit(repo, base_ref)
    candidates, pre_ejected = prescreen_candidates(
        repo, initial_base_sha, branches, allow_shard=allow_shard
    )
    part = partition_lanes(
        repo, initial_base_sha, candidates, small_rdeps_cap=small_rdeps_cap
    )
    ordered: list[Candidate] = part["ordered"]  # type: ignore[assignment]
    fast_batch: list[Candidate] = part["fast_batch"]  # type: ignore[assignment]
    heavy_batch: list[Candidate] = part["heavy_batch"]  # type: ignore[assignment]
    deferred_to_heavy: list[dict[str, object]] = (
        part["deferred_to_heavy"]  # type: ignore[assignment]
    )
    classifications: dict[str, dict[str, object]] = (
        part["classifications"]  # type: ignore[assignment]
    )

    eff_wt = worktree
    if lane in ("fast", "heavy") and worktree == DEFAULT_WORKTREE:
        eff_wt = Path(f"{DEFAULT_WORKTREE}-{lane}")

    all_accepted: list[Candidate] = []
    all_ejected: list[EjectedPR] = list(pre_ejected)
    bisect_trace: list[dict[str, object]] = []
    lanes_report: dict[str, dict[str, object]] = {}
    last_good_diag: dict[str, object] = {}
    final_merged_sha: str | None = None
    last_fast_land: dict[str, object] | None = None
    deferred_fast: list[str] = []
    deferred_heavy: list[str] = []
    land_failed = False
    active_count = 0

    def record_lane(name: str, rep: dict[str, object]) -> None:
        nonlocal final_merged_sha, last_good_diag, last_fast_land, land_failed
        acc: list[Candidate] = rep["accepted"]  # type: ignore[assignment]
        ej: list[EjectedPR] = rep["ejected"]  # type: ignore[assignment]
        all_accepted.extend(acc)
        all_ejected.extend(ej)
        bisect_trace.extend(rep["bisect_trace"])  # type: ignore[arg-type]
        if rep["merged_sha"]:
            final_merged_sha = str(rep["merged_sha"])
        if rep["summary_diag"]:
            last_good_diag = rep["summary_diag"]  # type: ignore[assignment]
        if rep["fast_land"] is not None:
            last_fast_land = rep["fast_land"]  # type: ignore[assignment]
        fl = rep["fast_land"]
        if isinstance(fl, dict) and fl.get("status") == "fail":
            land_failed = True
        lanes_report[name] = {
            **rep,
            "accepted": [asdict(c) for c in acc],
            "ejected": [asdict(e) for e in ej],
        }

    if lane == "all":
        active_count = len(ordered)
        batch_lane = max((c.build_lane for c in ordered), default=1)
        rep_all = _execute_lane_batch(
            repo,
            ordered,
            base_ref=base_ref,
            stage_base_sha=initial_base_sha,
            build_lane=batch_lane,
            worktree=eff_wt,
            dry_run=dry_run,
            execute=execute,
            fast_land_skip_tests=fast_land_skip_tests,
        )
        record_lane("all", rep_all)
    else:
        run_fast = lane in ("auto", "fast")
        run_heavy = lane in ("auto", "heavy")
        if lane == "fast":
            deferred_heavy = [c.branch for c in heavy_batch]
        elif lane == "heavy":
            deferred_fast = [c.branch for c in fast_batch]

        fast_accepted: list[Candidate] = []
        heavy_base_sha = initial_base_sha

        if run_fast:
            active_count += len(fast_batch)
            rep_fast = _execute_lane_batch(
                repo,
                fast_batch,
                base_ref=base_ref,
                stage_base_sha=initial_base_sha,
                build_lane=1,
                worktree=eff_wt,
                dry_run=dry_run,
                execute=execute,
                fast_land_skip_tests=fast_land_skip_tests,
            )
            record_lane("fast", rep_fast)
            fast_accepted = rep_fast["accepted"]  # type: ignore[assignment]
            if not dry_run and rep_fast["merged_sha"] and not land_failed:
                # Phase 2 stages atop fast_merged_sha (already CAS-landed if execute).
                heavy_base_sha = (
                    resolve_commit(repo, base_ref)
                    if execute
                    else str(rep_fast["merged_sha"])
                )

        if run_heavy:
            active_count += len(heavy_batch)
            dry_prefix = fast_accepted if (dry_run and run_fast) else None
            rep_heavy = _execute_lane_batch(
                repo,
                heavy_batch,
                base_ref=base_ref,
                stage_base_sha=heavy_base_sha,
                build_lane=2,
                worktree=eff_wt,
                dry_run=dry_run,
                execute=execute,
                fast_land_skip_tests=fast_land_skip_tests,
                dry_run_prefix=dry_prefix,
            )
            record_lane("heavy", rep_heavy)
            if (
                not dry_run
                and not execute
                and final_merged_sha
                and not rep_heavy["merged_sha"]
            ):
                ensure_staging_worktree(repo, eff_wt, final_merged_sha)

    final_base_sha = resolve_commit(repo, base_ref)
    if land_failed:
        ok_overall = False
    elif active_count == 0 and not all_ejected:
        ok_overall = True
    else:
        ok_overall = bool(all_accepted)

    return {
        "ok": ok_overall,
        "mode": "dry-run" if dry_run else ("execute" if execute else "stage"),
        "lane_mode": lane,
        "base_ref": base_ref,
        "base_sha": initial_base_sha,
        "final_base_sha": final_base_sha,
        "accepted": [asdict(c) for c in all_accepted],
        "ejected": [asdict(e) for e in all_ejected],
        "deferred_fast": deferred_fast,
        "deferred_heavy": deferred_heavy,
        "partition": {
            "ordered": [c.branch for c in ordered],
            "fast_batch": [c.branch for c in fast_batch],
            "heavy_batch": [c.branch for c in heavy_batch],
            "deferred_to_heavy": deferred_to_heavy,
            "classifications": classifications,
        },
        "lanes": lanes_report,
        "bisect_steps": len(bisect_trace),
        "bisect_trace": bisect_trace,
        "merged_sha": final_merged_sha,
        "summary_diag": last_good_diag,
        "fast_land": last_fast_land,
    }


def format_human(report: dict[str, object]) -> str:
    """Render concise human-readable merge-train report."""
    acc = [c["branch"] for c in report["accepted"]]  # type: ignore[index]
    ej = [
        f"{e['branch']} ({e['reason']})"
        for e in report["ejected"]  # type: ignore[index]
    ]
    part = report.get("partition", {})
    lines = [
        f"merge_train ({report['mode']}, lane={report.get('lane_mode', 'auto')}, "
        f"base={report['base_ref']}): accepted={len(acc)}, ejected={len(ej)}, "
        f"bisect_steps={report['bisect_steps']}",
        f"  fast_batch: {part.get('fast_batch', [])}",  # type: ignore[union-attr]
        f"  heavy_batch: {part.get('heavy_batch', [])}",  # type: ignore[union-attr]
        f"  accepted: {acc}",
    ]
    if ej:
        lines.append(f"  ejected:  {ej}")
    if report["merged_sha"]:
        lines.append(f"  merged_sha: {report['merged_sha']}")
    if report["fast_land"]:
        lines.append(f"  fast_land: {report['fast_land']['status']}")  # type: ignore[index]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for `scripts/merge_train.py`."""
    ap = argparse.ArgumentParser(
        description="Deterministic O(log k) bisecting merge train (N10 + N8 + P2-2)."
    )
    ap.add_argument("--root", default=".", help="Repository root (default: .)")
    ap.add_argument(
        "--base",
        default="leanqbe/main",
        help="Target integration branch/commit (default: leanqbe/main).",
    )
    ap.add_argument(
        "--lane",
        choices=LANE_CHOICES,
        default="auto",
        help="Lane partitioning mode: auto (fast-first HoL bypass), fast, heavy, or all.",
    )
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="Simulate merge-tree, Canary Frontier, and bisection with 0 mutations.",
    )
    ap.add_argument(
        "--worktree",
        default=str(DEFAULT_WORKTREE),
        help=f"Staging worktree path (default: {DEFAULT_WORKTREE}).",
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
        lane=args.lane,
    )
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(format_human(report))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
