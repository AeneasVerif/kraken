#!/usr/bin/env python3
"""Safe stale `.lake/build` artifact pruning tool (G5-A3).

Default mode is strictly `--dry-run` (`0` filesystem mutations).
With `--apply`, removes ONLY orphaned per-module build artifacts under
`<root>/.lake/build/{lib/lean,ir}` whose corresponding source `.lean` file
no longer exists in `git ls-files --cached -- '*.lean'`:

  - `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`,
    `.trace`, and their `.hash` / `.olean.private.tmp.<pid>` siblings under
    `.lake/build/lib/lean/`
  - `.c`, `.c.hash`, `.c.o.export*`, `.c.o.noexport*`, and `.setup.json` under
    `.lake/build/ir/`

Safety guards:
  - Fails closed (`0` deletions) if `git ls-files` fails or returns 0 files.
  - NEVER touches `bv_decide_qbe/` (or any `--build-dir` inside it).
  - NEVER touches `.lake/packages/`, `.lake/manifest.json`, `.lake/build/bin/`,
    `.lake/build/lib/*.a*`, or unrecognized non-module files.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import re
import subprocess
import sys

MIB = float(1024**2)

LIB_LEAN_SUFFIXES: tuple[str, ...] = tuple(
    sorted(
        (
            ".olean.private.hash",
            ".olean.private",
            ".olean.server.hash",
            ".olean.server",
            ".olean.hash",
            ".olean",
            ".ilean.hash",
            ".ilean",
            ".ir.sig.hash",
            ".ir.sig",
            ".ir.hash",
            ".ir",
            ".trace",
        ),
        key=len,
        reverse=True,
    )
)

IR_SUFFIXES: tuple[str, ...] = tuple(
    sorted(
        (
            ".c.o.export.hash",
            ".c.o.export.trace",
            ".c.o.export",
            ".c.o.noexport.hash",
            ".c.o.noexport.trace",
            ".c.o.noexport",
            ".c.hash",
            ".c",
            ".setup.json",
        ),
        key=len,
        reverse=True,
    )
)

TMP_PRIVATE_RE = re.compile(r"\.olean\.private\.tmp\.\d+$")


@dataclass
class StaleArtifact:
    """Single orphaned per-module artifact under `.lake/build`."""

    area: str  # "lib/lean" | "ir"
    rel_path: str
    module_stem: str
    suffix: str
    size_bytes: int
    untracked_on_disk: bool


def resolve_repo_root(raw_root: str | None) -> Path:
    """Resolve the git worktree top-level directory from `raw_root` or cwd."""
    start = Path(raw_root).resolve() if raw_root else Path.cwd().resolve()
    res = subprocess.run(
        ["git", "-C", str(start), "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0 or not res.stdout.strip():
        msg = res.stderr.strip() or f"not a git worktree: {start}"
        raise RuntimeError(msg)
    return Path(res.stdout.strip()).resolve()


def validate_build_dir(repo_root: Path, raw_build_dir: str | None) -> Path:
    """Resolve `.lake/build` and guard against `bv_decide_qbe/` or repo escape."""
    build_dir = (
        Path(raw_build_dir).resolve()
        if raw_build_dir
        else (repo_root / ".lake" / "build").resolve()
    )
    bv_sub = (repo_root / "bv_decide_qbe").resolve()
    if build_dir == bv_sub or build_dir.is_relative_to(bv_sub):
        raise ValueError(
            f"refusing to scan protected subproject build dir: {build_dir}"
        )
    if build_dir.name != "build" and not (build_dir / "lib").exists():
        raise ValueError(
            f"build-dir does not look like a Lake build dir: {build_dir}"
        )
    return build_dir


def load_tracked_lean_sources(repo_root: Path) -> set[str]:
    """Return tracked `.lean` paths (POSIX relative) excluding `bv_decide_qbe/`."""
    res = subprocess.run(
        ["git", "-C", str(repo_root), "ls-files", "--cached", "-z", "--", "*.lean"],
        capture_output=True,
        check=False,
    )
    if res.returncode != 0:
        err = res.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git ls-files failed: {err}")
    entries = [
        e for e in res.stdout.decode("utf-8", errors="replace").split("\0") if e
    ]
    tracked = {e for e in entries if not e.startswith("bv_decide_qbe/")}
    if not tracked:
        raise RuntimeError(
            f"git ls-files returned zero tracked .lean sources under {repo_root}"
        )
    return tracked


def strip_artifact_suffix(
    rel_posix: str,
    suffixes: tuple[str, ...],
    *,
    allow_tmp: bool,
) -> tuple[str, str] | None:
    """Split `<ModPath><suffix>` into `(ModPath, suffix)` or `None`."""
    for sfx in suffixes:
        if rel_posix.endswith(sfx) and len(rel_posix) > len(sfx):
            return rel_posix[: -len(sfx)], sfx
    if allow_tmp:
        match = TMP_PRIVATE_RE.search(rel_posix)
        if match and match.start() > 0:
            return rel_posix[: match.start()], match.group(0)
    return None


def scan_area(
    repo_root: Path,
    area_dir: Path,
    area_name: str,
    suffixes: tuple[str, ...],
    tracked: set[str],
    *,
    allow_tmp: bool,
    keep_untracked: bool,
) -> tuple[list[StaleArtifact], list[str], int]:
    """Scan `lib/lean` or `ir` for orphaned module artifacts without mutating."""
    stale: list[StaleArtifact] = []
    skipped_unknown: list[str] = []
    scanned_count = 0
    if not area_dir.is_dir():
        return stale, skipped_unknown, scanned_count

    area_resolved = area_dir.resolve()
    for path in sorted(area_dir.rglob("*")):
        if path.is_symlink() or not path.is_file():
            continue
        if not path.resolve().is_relative_to(area_resolved):
            continue
        scanned_count += 1
        rel = path.relative_to(area_dir).as_posix()
        parsed = strip_artifact_suffix(rel, suffixes, allow_tmp=allow_tmp)
        if parsed is None:
            skipped_unknown.append(f"{area_name}/{rel}")
            continue
        mod_stem, sfx = parsed
        src_rel = f"{mod_stem}.lean"
        if src_rel in tracked:
            continue
        untracked_on_disk = (repo_root / src_rel).is_file()
        if keep_untracked and untracked_on_disk:
            continue
        stale.append(
            StaleArtifact(
                area=area_name,
                rel_path=f"{area_name}/{rel}",
                module_stem=mod_stem,
                suffix=sfx,
                size_bytes=path.stat().st_size,
                untracked_on_disk=untracked_on_disk,
            )
        )
    return stale, skipped_unknown, scanned_count


def remove_empty_subdirs(area_dir: Path) -> int:
    """Remove empty directories strictly beneath `area_dir` (bottom-up)."""
    if not area_dir.is_dir():
        return 0
    removed = 0
    dirs = sorted(
        (p for p in area_dir.rglob("*") if p.is_dir() and not p.is_symlink()),
        key=lambda p: len(p.parts),
        reverse=True,
    )
    for d in dirs:
        try:
            next(d.iterdir())
        except StopIteration:
            d.rmdir()
            removed += 1
        except OSError:
            continue
    return removed


def apply_pruning(
    build_dir: Path, stale: list[StaleArtifact]
) -> tuple[int, int, list[dict[str, str]]]:
    """Delete approved orphaned artifact files and empty subdirs."""
    deleted_files = 0
    deleted_bytes = 0
    errors: list[dict[str, str]] = []
    build_resolved = build_dir.resolve()
    allowed_roots = (
        (build_dir / "lib" / "lean").resolve(),
        (build_dir / "ir").resolve(),
    )

    for item in stale:
        target = build_dir / item.rel_path
        try:
            resolved = target.resolve()
            if not resolved.is_relative_to(build_resolved):
                raise ValueError(f"path escaped build dir: {target}")
            if not any(resolved.is_relative_to(r) for r in allowed_roots):
                raise ValueError(f"path outside lib/lean or ir: {target}")
            target.unlink()
            deleted_files += 1
            deleted_bytes += item.size_bytes
        except OSError as exc:
            errors.append({"path": str(target), "error": str(exc)})
        except ValueError as exc:
            errors.append({"path": str(target), "error": str(exc)})

    pruned_dirs = remove_empty_subdirs(build_dir / "lib" / "lean")
    pruned_dirs += remove_empty_subdirs(build_dir / "ir")
    _ = pruned_dirs
    return deleted_files, deleted_bytes, errors


def build_summary(
    *,
    repo_root: Path,
    build_dir: Path,
    apply: bool,
    keep_untracked: bool,
    tracked_count: int,
    scanned_count: int,
    stale: list[StaleArtifact],
    skipped_unknown: list[str],
    deleted_files: int,
    deleted_bytes: int,
    errors: list[dict[str, str]],
) -> dict[str, object]:
    """Build structured JSON/human summary report."""
    total_bytes = sum(s.size_bytes for s in stale)
    stale_modules = sorted({s.module_stem for s in stale})
    by_prefix: Counter[str] = Counter()
    bytes_by_prefix: Counter[str] = Counter()
    by_suffix: Counter[str] = Counter()
    untracked_hits = sorted(
        {s.module_stem for s in stale if s.untracked_on_disk}
    )

    for item in stale:
        top = item.module_stem.split("/", 1)[0]
        by_prefix[top] += 1
        bytes_by_prefix[top] += item.size_bytes
        sfx_key = ".olean.private.tmp.*" if ".tmp." in item.suffix else item.suffix
        by_suffix[sfx_key] += 1

    return {
        "mode": "apply" if apply else "dry-run",
        "repo_root": str(repo_root),
        "build_dir": str(build_dir),
        "build_dir_exists": build_dir.is_dir(),
        "keep_untracked": keep_untracked,
        "tracked_lean_count": tracked_count,
        "scanned_file_count": scanned_count,
        "stale_file_count": len(stale),
        "stale_module_count": len(stale_modules),
        "stale_bytes": total_bytes,
        "stale_mib": round(total_bytes / MIB, 2),
        "untracked_on_disk_modules": untracked_hits,
        "skipped_unknown_count": len(skipped_unknown),
        "skipped_unknown_sample": skipped_unknown[:20],
        "by_prefix_files": dict(sorted(by_prefix.items())),
        "by_prefix_mib": {
            k: round(v / MIB, 2) for k, v in sorted(bytes_by_prefix.items())
        },
        "by_suffix_files": dict(sorted(by_suffix.items())),
        "sample_stale_modules": stale_modules[:30],
        "deleted_files": deleted_files,
        "deleted_bytes": deleted_bytes,
        "deleted_mib": round(deleted_bytes / MIB, 2),
        "errors": errors,
    }


def format_human(summary: dict[str, object], stale: list[StaleArtifact], verbose: bool) -> str:
    """Format concise human-readable report."""
    lines = [
        f"prune_lake_stale ({summary['mode']}, build_dir={summary['build_dir']}):",
        f"  tracked .lean={summary['tracked_lean_count']}, "
        f"scanned={summary['scanned_file_count']}, "
        f"skipped_unknown={summary['skipped_unknown_count']}",
        f"  stale: {summary['stale_file_count']} files across "
        f"{summary['stale_module_count']} orphaned modules "
        f"({summary['stale_mib']:.2f} MiB)",
    ]
    by_prefix = summary["by_prefix_files"]
    by_prefix_mib = summary["by_prefix_mib"]
    if isinstance(by_prefix, dict) and by_prefix:
        parts = [
            f"{k}: {v} files ({by_prefix_mib[k]:.2f} MiB)"  # type: ignore[index]
            for k, v in by_prefix.items()
        ]
        lines.append("  by prefix: " + ", ".join(parts))
    untracked = summary["untracked_on_disk_modules"]
    if isinstance(untracked, list) and untracked:
        lines.append(
            f"  note: {len(untracked)} stale module(s) have untracked .lean on disk "
            f"(pass --keep-untracked to preserve): {untracked[:10]}"
        )
    if summary["mode"] == "apply":
        lines.append(
            f"  deleted: {summary['deleted_files']} files "
            f"({summary['deleted_mib']:.2f} MiB), "
            f"errors={len(summary['errors'])}"  # type: ignore[arg-type]
        )
    if verbose:
        for item in stale:
            lines.append(f"  - {item.rel_path} ({item.size_bytes} B)")
    else:
        sample = summary["sample_stale_modules"]
        if isinstance(sample, list) and sample:
            lines.append("  sample modules: " + ", ".join(sample[:10]))
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for `scripts/prune_lake_stale.py`."""
    ap = argparse.ArgumentParser(
        description=(
            "Find and optionally prune orphaned .lake/build module artifacts "
            "whose source .lean file no longer exists in git tracked files."
        )
    )
    ap.add_argument(
        "--root",
        default=None,
        help="Git repository/worktree root (default: resolved from cwd).",
    )
    ap.add_argument(
        "--build-dir",
        default=None,
        help="Lake build dir to inspect (default: <root>/.lake/build).",
    )
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument(
        "--dry-run",
        action="store_true",
        help="Report stale artifacts without deleting anything (default).",
    )
    mode.add_argument(
        "--apply",
        action="store_true",
        help="Delete orphaned module artifacts under .lake/build/{lib/lean,ir}.",
    )
    ap.add_argument(
        "--keep-untracked",
        action="store_true",
        help="Keep artifacts if an untracked .lean source exists on disk.",
    )
    ap.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="List every matched stale artifact in human output.",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON output.",
    )
    args = ap.parse_args(argv)

    try:
        repo_root = resolve_repo_root(args.root)
        build_dir = validate_build_dir(repo_root, args.build_dir)
        tracked = load_tracked_lean_sources(repo_root)
    except (RuntimeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    lib_stale, lib_unk, lib_scanned = scan_area(
        repo_root,
        build_dir / "lib" / "lean",
        "lib/lean",
        LIB_LEAN_SUFFIXES,
        tracked,
        allow_tmp=True,
        keep_untracked=bool(args.keep_untracked),
    )
    ir_stale, ir_unk, ir_scanned = scan_area(
        repo_root,
        build_dir / "ir",
        "ir",
        IR_SUFFIXES,
        tracked,
        allow_tmp=False,
        keep_untracked=bool(args.keep_untracked),
    )

    stale = lib_stale + ir_stale
    skipped_unknown = lib_unk + ir_unk
    scanned_count = lib_scanned + ir_scanned

    deleted_files = 0
    deleted_bytes = 0
    errors: list[dict[str, str]] = []
    if args.apply and stale:
        deleted_files, deleted_bytes, errors = apply_pruning(build_dir, stale)

    summary = build_summary(
        repo_root=repo_root,
        build_dir=build_dir,
        apply=bool(args.apply),
        keep_untracked=bool(args.keep_untracked),
        tracked_count=len(tracked),
        scanned_count=scanned_count,
        stale=stale,
        skipped_unknown=skipped_unknown,
        deleted_files=deleted_files,
        deleted_bytes=deleted_bytes,
        errors=errors,
    )
    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        print(format_human(summary, stale, verbose=bool(args.verbose)))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
