#!/usr/bin/env python3
"""Check and generate LeanQbe barrel and subsystem hub modules.

Inspects tracked `.lean` files under `LeanQbe/` and validates or generates the
12 pure re-export barrel/hub files (`LeanQbe.lean`, `LeanQbeAmd64.lean`,
`LeanQbeArm64.lean`, `LeanQbeBootstrap0.lean`, and the 8 subsystem `*Hub.lean`
files), respecting the exact arch-isolation partition from `lakefile.toml` and
`scripts/check.sh`.

Usage:
  python3 -B scripts/sync_hubs.py --check [--strict] [--root .]
  python3 -B scripts/sync_hubs.py --write [--root .]
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_imports import (
    ALL_HUBS,
    ARM_PFX,
    IMPORT_LINE_RE,
    KISSAT_ARM_PFX,
    KISSAT_X64_PFX,
    ROOT_LIBS,
    SUBSYSTEM_HUBS,
    X64_PFX,
    ImportStmt,
    compute_import_closure,
    mod_to_rel_path,
    rel_path_to_mod,
    strip_comments_line,
)

HUB_DOCSTRINGS: dict[str, str] = {
    "LeanQbe": (
        "/-! Root of the generic library. Imports neither `Kraken.X64` nor "
        "`Kraken.AArch64`. -/"
    ),
    "LeanQbeAmd64": (
        "/-! Root of the x64 library: imports `Kraken.X64` and "
        "`LeanQbe.T.Amd64.*` modules. -/"
    ),
    "LeanQbeArm64": (
        "/-!\nRoot of the AArch64 library: imports `Kraken.AArch64` and "
        "`LeanQbe.T.Arm64.*`\nmodules.\n-/"
    ),
    "LeanQbeBootstrap0": (
        "/-! Root of the optional Stage-A bootstrap compiler library "
        "(`LeanQbe.T.Bootstrap0.*`). -/"
    ),
    "LeanQbe.T.CoreHub": (
        "/-! Subsystem hub re-exporting core compiler IR, passes, lemmas, "
        "linking, and driver modules. -/"
    ),
    "LeanQbe.T.Logic.ExtraHub": (
        "/-! Subsystem hub re-exporting non-core Logic helper and layout "
        "modules. -/"
    ),
    "LeanQbe.T.Unified.Hub": (
        "/-! Subsystem hub re-exporting Unified CFG recovery and contification "
        "modules (`LeanQbe.T.Unified.*`). -/"
    ),
    "LeanQbe.T.Wasm.Hub": (
        "/-! Subsystem hub re-exporting WebAssembly AST, decoder, lowering, and "
        "safety modules (`LeanQbe.T.Wasm.*`). -/"
    ),
    "LeanQbe.T.Frontend.C0.Hub": (
        "/-! Subsystem hub re-exporting C0 frontend modules "
        "(`LeanQbe.T.Frontend.C0.*`). -/"
    ),
    "LeanQbe.T.LeanLCNF.Hub": (
        "/-! Subsystem hub re-exporting LeanLCNF frontend and coverage "
        "modules. -/"
    ),
    "LeanQbe.T.Examples.Hub": (
        "/-! Subsystem hub re-exporting non-Kissat example, LRAT, and "
        "benchmark program modules. -/"
    ),
    "LeanQbe.T.Examples.Kissat.BaseHub": (
        "/-!\nSubsystem hub re-exporting Kissat Src, Proof, Ref, Build, Core, "
        "LayerA, Dimacs,\nPlain, Solver, and ExportCnf modules.\n-/"
    ),
}


def parse_barrel_file(path: Path) -> tuple[list[ImportStmt], list[str]]:
    """Validate that `path` is a pure re-export barrel/hub file."""
    imports: list[ImportStmt] = []
    errors: list[str] = []
    seen_module = False
    depth = 0
    seen_mods: set[str] = set()

    with path.open("r", encoding="utf-8") as fh:
        for lineno, raw_line in enumerate(fh, start=1):
            s, depth, _ = strip_comments_line(raw_line, depth)
            if not s:
                continue
            if s == "module":
                if seen_module:
                    errors.append(f"{path}:{lineno}: duplicate `module` line")
                seen_module = True
                continue
            if s == "set_option autoImplicit false":
                continue
            m = IMPORT_LINE_RE.match(s)
            if m:
                vis, is_meta, is_all, mod = (
                    m.group(1),
                    m.group(2),
                    m.group(3),
                    m.group(4),
                )
                if vis != "public" or is_meta is not None or is_all is not None:
                    errors.append(
                        f"{path}:{lineno}: hub import `{s}` must be plain "
                        f"`public import {mod}`"
                    )
                if mod in seen_mods:
                    errors.append(
                        f"{path}:{lineno}: duplicate import `{mod}`"
                    )
                seen_mods.add(mod)
                imports.append(
                    ImportStmt(
                        line=lineno,
                        module=mod,
                        is_public=(vis == "public"),
                        is_meta=(is_meta is not None),
                        is_all=(is_all is not None),
                    )
                )
                continue
            errors.append(
                f"{path}:{lineno}: non-barrel statement in hub file: `{s}`"
            )
    if not seen_module:
        errors.append(f"{path}: missing `module` header")
    if depth != 0:
        errors.append(f"{path}: unclosed block comment")
    return imports, errors


def verify_lakefile(root: Path) -> list[str]:
    """Verify `lakefile.toml` exists and defines all expected root libraries."""
    lakefile = root / "lakefile.toml"
    if not lakefile.is_file():
        return ["missing lakefile.toml"]
    data = tomllib.loads(lakefile.read_text(encoding="utf-8"))
    libs = {entry.get("name") for entry in data.get("lean_lib", [])}
    missing = [lib for lib in ROOT_LIBS if lib not in libs]
    if missing:
        return [f"lakefile.toml missing [[lean_lib]] target(s): {', '.join(missing)}"]
    return []


def list_tracked_lean_modules(root: Path) -> dict[str, Path]:
    """Return `{module_name: abs_path}` for tracked `.lean` files under `LeanQbe/`."""
    inside_git = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "--is-inside-work-tree"],
        capture_output=True,
        text=True,
        check=False,
    )
    rel_paths: list[Path] = []
    if inside_git.returncode == 0 and inside_git.stdout.strip() == "true":
        res = subprocess.run(
            ["git", "-C", str(root), "ls-files", "--cached", "-z", "--", "LeanQbe"],
            capture_output=True,
            check=True,
        )
        for raw in res.stdout.split(b"\0"):
            if not raw:
                continue
            rel = Path(raw.decode("utf-8"))
            if rel.suffix == ".lean":
                rel_paths.append(rel)
    else:
        lean_dir = root / "LeanQbe"
        if lean_dir.is_dir():
            for p in sorted(lean_dir.rglob("*.lean")):
                rel_paths.append(p.relative_to(root))

    out: dict[str, Path] = {}
    for rel in sorted(set(rel_paths)):
        out[rel_path_to_mod(rel)] = root / rel
    return out


NONCORE_LOGIC_MODULES: frozenset[str] = frozenset(
    {
        "LeanQbe.T.Logic.CanonicalEnv",
        "LeanQbe.T.Logic.MemAlgebra",
        "LeanQbe.T.Logic.SlabLayoutElab",
        "LeanQbe.T.Logic.U32",
    }
)


def classify_module(mod: str) -> str | None:
    """Assign a tracked `LeanQbe.*` module to its exact hub/barrel partition."""
    if mod in SUBSYSTEM_HUBS:
        return None
    if mod.startswith(("LeanQbe.T.Amd64.", *KISSAT_X64_PFX)):
        return "LeanQbeAmd64"
    if mod.startswith(("LeanQbe.T.Arm64.", *KISSAT_ARM_PFX)):
        return "LeanQbeArm64"
    if mod in NONCORE_LOGIC_MODULES:
        return "LeanQbe.T.Logic.ExtraHub"
    if mod.startswith("LeanQbe.T.Unified."):
        return "LeanQbe.T.Unified.Hub"
    if mod.startswith("LeanQbe.T.Wasm."):
        return "LeanQbe.T.Wasm.Hub"
    if mod == "LeanQbe.T.Frontend.C0" or mod.startswith("LeanQbe.T.Frontend.C0."):
        return "LeanQbe.T.Frontend.C0.Hub"
    if mod.startswith("LeanQbe.T.LeanLCNF."):
        return "LeanQbe.T.LeanLCNF.Hub"
    if mod.startswith("LeanQbe.T.Examples.Kissat."):
        return "LeanQbe.T.Examples.Kissat.BaseHub"
    if mod.startswith("LeanQbe.T.Examples."):
        return "LeanQbe.T.Examples.Hub"
    if mod.startswith("LeanQbe.T.Bootstrap0."):
        return "LeanQbeBootstrap0"
    if mod.startswith("LeanQbe.T."):
        return "LeanQbe.T.CoreHub"
    return "E1_FORBIDDEN"


def compute_closure(
    root_mod: str,
    root: Path,
    import_cache: dict[str, list[ImportStmt]],
) -> set[str]:
    """Compute transitive import closure of `root_mod` across local files."""
    return compute_import_closure([root_mod], root, import_cache=import_cache)


ARCH_FORBIDDEN: dict[str, tuple[str, tuple[str, ...]]] = {
    "LeanQbeAmd64": ("x64", ARM_PFX),
    "LeanQbeBootstrap0": ("x64", ARM_PFX),
    "LeanQbeArm64": ("Arm64", X64_PFX),
}


def check_isolation(hub: str, closure: set[str]) -> list[str]:
    """Enforce arch isolation invariants on `closure`."""
    errors: list[str] = []
    if hub in ("LeanQbe", *SUBSYSTEM_HUBS):
        bad = sorted(m for m in closure if m.startswith((*X64_PFX, *ARM_PFX)))
        if bad:
            errors.append(
                f"{hub}: generic closure leaks arch module(s): "
                + ", ".join(bad[:5])
            )
        return errors

    if hub in ARCH_FORBIDDEN:
        label, opp_prefixes = ARCH_FORBIDDEN[hub]
        opp_name = "Arm64" if label == "x64" else "x64"
        bad_arch = sorted(m for m in closure if m.startswith(opp_prefixes))
        if bad_arch:
            errors.append(
                f"{hub}: {label} closure leaks {opp_name} module(s): "
                + ", ".join(bad_arch[:5])
            )
    return errors


def build_partitions(
    tracked: dict[str, Path],
) -> tuple[dict[str, list[str]], list[str]]:
    """Partition all tracked `LeanQbe.*` modules into their designated hubs."""
    partitions: dict[str, list[str]] = {h: [] for h in ALL_HUBS if h != "LeanQbe"}
    errors: list[str] = []
    for mod in sorted(tracked):
        dest = classify_module(mod)
        if dest is None:
            continue
        if dest == "E1_FORBIDDEN":
            errors.append(
                f"untyped E1 module outside LeanQbe/T/: {mod_to_rel_path(mod)}"
            )
            continue
        partitions[dest].append(mod)
    return partitions, errors


def expected_direct_imports(
    hub: str, partitions: dict[str, list[str]]
) -> list[str]:
    """Return canonical sorted direct imports for `hub`."""
    if hub == "LeanQbe":
        return list(SUBSYSTEM_HUBS)
    if hub in ("LeanQbeAmd64", "LeanQbeArm64"):
        return ["LeanQbe.T.CoreHub", *sorted(partitions[hub])]
    return sorted(partitions[hub])


def render_hub(hub: str, imports: list[str]) -> str:
    """Render deterministic canonical Lean source text for `hub`."""
    lines: list[str] = ["module", ""]
    for mod in imports:
        lines.append(f"public import {mod}")
    lines.extend(["", "set_option autoImplicit false", "", HUB_DOCSTRINGS[hub], ""])
    return "\n".join(lines)


def run_check(root: Path, strict: bool) -> int:
    """Verify all 12 hub/barrel files against tracked modules and invariants."""
    errors = verify_lakefile(root)
    tracked = list_tracked_lean_modules(root)
    partitions, part_errors = build_partitions(tracked)
    errors.extend(part_errors)

    import_cache: dict[str, list[ImportStmt]] = {}
    summary: list[str] = []

    for hub in ALL_HUBS:
        hub_path = root / mod_to_rel_path(hub)
        if not hub_path.is_file():
            errors.append(f"missing hub file: {mod_to_rel_path(hub)}")
            continue
        direct_imps, parse_errs = parse_barrel_file(hub_path)
        errors.extend(parse_errs)
        import_cache[hub] = direct_imps
        direct_mods = [imp.module for imp in direct_imps]
        direct_set = set(direct_mods)

        if hub == "LeanQbe":
            want = set(SUBSYSTEM_HUBS)
            missing = sorted(want - direct_set)
            extra = sorted(direct_set - want)
            if missing:
                errors.append(f"{hub}: missing subsystem hub(s): {', '.join(missing)}")
            if extra:
                errors.append(f"{hub}: unexpected direct import(s): {', '.join(extra)}")
        else:
            if hub in ("LeanQbeAmd64", "LeanQbeArm64"):
                if "LeanQbe.T.CoreHub" not in direct_set:
                    errors.append(
                        f"{hub}: missing required `public import LeanQbe.T.CoreHub`"
                    )
                allowed_base = {"LeanQbe.T.CoreHub"}
            else:
                allowed_base = set()
            for mod in direct_mods:
                if mod in allowed_base:
                    continue
                if mod not in tracked:
                    errors.append(
                        f"{hub}: extra/non-existent tracked module `{mod}`"
                    )
                    continue
                owner = classify_module(mod)
                if owner != hub:
                    errors.append(
                        f"{hub}: misplaced module `{mod}` (belongs to `{owner}`)"
                    )

            closure = compute_closure(hub, root, import_cache)
            missing_cov = [m for m in partitions[hub] if m not in closure]
            if missing_cov:
                errors.append(
                    f"{hub}: missing {len(missing_cov)} module(s) from closure: "
                    + ", ".join(missing_cov[:8])
                )
            errors.extend(check_isolation(hub, closure))

        if strict:
            want_txt = render_hub(hub, expected_direct_imports(hub, partitions))
            got_txt = hub_path.read_text(encoding="utf-8")
            if got_txt != want_txt:
                errors.append(
                    f"{hub}: non-canonical direct imports/formatting (--strict)"
                )

        summary.append(f"{hub} ({len(direct_mods)} direct)")

    if errors:
        for err in errors:
            print(f"FAIL: {err}", file=sys.stderr)
        print(
            f"sync_hubs --check: FAILED ({len(errors)} error(s))",
            file=sys.stderr,
        )
        return 1

    print(
        f"sync_hubs --check: OK ({len(ALL_HUBS)} hubs, "
        f"{len(tracked)} tracked modules): " + ", ".join(summary)
    )
    return 0


def run_write(root: Path) -> int:
    """Regenerate all 12 hub/barrel files deterministically from tracked files."""
    errors = verify_lakefile(root)
    tracked = list_tracked_lean_modules(root)
    partitions, part_errors = build_partitions(tracked)
    errors.extend(part_errors)
    if errors:
        for err in errors:
            print(f"FAIL: {err}", file=sys.stderr)
        return 1

    updated = 0
    for hub in ALL_HUBS:
        hub_path = root / mod_to_rel_path(hub)
        hub_path.parent.mkdir(parents=True, exist_ok=True)
        imps = expected_direct_imports(hub, partitions)
        new_txt = render_hub(hub, imps)
        old_txt = hub_path.read_text(encoding="utf-8") if hub_path.is_file() else None
        if old_txt != new_txt:
            hub_path.write_text(new_txt, encoding="utf-8")
            updated += 1
            print(f"UPDATED {mod_to_rel_path(hub)} ({len(imps)} imports)")
        else:
            print(f"OK      {mod_to_rel_path(hub)} ({len(imps)} imports)")

    print(f"sync_hubs --write: {updated}/{len(ALL_HUBS)} hub file(s) updated")
    return 0


def default_root() -> Path:
    """Resolve repo root, preferring cwd when inside a checkout copy."""
    cwd = Path.cwd()
    if (cwd / "lakefile.toml").is_file() and (cwd / "LeanQbe").is_dir():
        return cwd
    return Path(__file__).resolve().parent.parent


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for `sync_hubs.py`."""
    ap = argparse.ArgumentParser(
        description="Check or generate LeanQbe barrel and subsystem hub files."
    )
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--check",
        action="store_true",
        help="Validate hub files against tracked modules and exit 0/1.",
    )
    mode.add_argument(
        "--write",
        action="store_true",
        help="Deterministically write sorted pure re-export hub files.",
    )
    ap.add_argument(
        "--strict",
        action="store_true",
        help="With --check, require byte-identical canonical sorted output.",
    )
    ap.add_argument(
        "--root",
        default=None,
        help="Repository root (default: cwd if LeanQbe checkout, else script parent).",
    )
    args = ap.parse_args(argv)
    root = Path(args.root).resolve() if args.root else default_root()

    if args.check:
        return run_check(root, strict=args.strict)
    return run_write(root)


if __name__ == "__main__":
    sys.exit(main())
