#!/usr/bin/env python3
"""Check and generate LeanQbe barrel and subsystem hub modules.

Inspects tracked `.lean` files under `LeanQbe/` and validates or generates the
13 pure re-export barrel/hub files (`LeanQbe.lean`, `LeanQbeAmd64.lean`,
`LeanQbeArm64.lean`, `LeanQbeLegacyAmd64.lean`, `LeanQbeLegacyArm64.lean`, and
the 8 subsystem `*Hub.lean` files), respecting the exact active-vs-legacy and
arch-isolation partition from `lakefile.toml` and `scripts/check.sh`.

Usage:
  python3 -B scripts/sync_hubs.py --check [--strict] [--root .]
  python3 -B scripts/sync_hubs.py --write [--root .]
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

LEGACY_CERT_DEFAULT = (
    r"^LeanQbe\.T\.(Amd64|Arm64)\."
    r"(Kissat|KissatCorePlus|KissatFull.*|KissatFastSched.*|KissatFast.*)$"
)

IMPORT_LINE_RE = re.compile(
    r"^\s*(?:(public|private)\s+)?(?:(meta)\s+)?import\s+(?:(all)\s+)?"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\s*$"
)

SUBSYSTEM_HUBS: tuple[str, ...] = (
    "LeanQbe.T.CoreHub",
    "LeanQbe.T.Frontend.C0.Hub",
    "LeanQbe.T.LeanLCNF.Hub",
    "LeanQbe.T.LeanLRC.Hub",
    "LeanQbe.T.Examples.Hub",
    "LeanQbe.T.Examples.Kissat.BaseHub",
    "LeanQbe.T.Examples.Kissat.M3Hub",
    "LeanQbe.T.Examples.Kissat.M4Hub",
)

ROOT_LIBS: tuple[str, ...] = (
    "LeanQbe",
    "LeanQbeAmd64",
    "LeanQbeArm64",
    "LeanQbeLegacyAmd64",
    "LeanQbeLegacyArm64",
)

HUB_DOCSTRINGS: dict[str, str] = {
    "LeanQbe": (
        "/-! Root of the generic library. Imports neither `Kraken.X64` nor "
        "`Kraken.AArch64`. -/"
    ),
    "LeanQbeAmd64": (
        "/-! Root of the active x64 library: imports `Kraken.X64` and active "
        "`LeanQbe.T.Amd64.*` modules. -/"
    ),
    "LeanQbeArm64": (
        "/-! Root of the active AArch64 library: imports `Kraken.AArch64` and "
        "active `LeanQbe.T.Arm64.*` modules. -/"
    ),
    "LeanQbeLegacyAmd64": (
        "/-! Root of the optional legacy x64 Kissat certificate library. -/"
    ),
    "LeanQbeLegacyArm64": (
        "/-! Root of the optional legacy AArch64 Kissat certificate library. -/"
    ),
    "LeanQbe.T.CoreHub": (
        "/-! Subsystem hub re-exporting core compiler IR, passes, lemmas, "
        "linking, and driver modules. -/"
    ),
    "LeanQbe.T.Frontend.C0.Hub": (
        "/-! Subsystem hub re-exporting C0 frontend modules "
        "(`LeanQbe.T.Frontend.C0.*`). -/"
    ),
    "LeanQbe.T.LeanLCNF.Hub": (
        "/-! Subsystem hub re-exporting LeanLCNF frontend and coverage "
        "modules. -/"
    ),
    "LeanQbe.T.LeanLRC.Hub": (
        "/-! Subsystem hub re-exporting LeanLRC IR, runtime, and lowering "
        "modules. -/"
    ),
    "LeanQbe.T.Examples.Hub": (
        "/-! Subsystem hub re-exporting non-Kissat example, LRAT, and "
        "benchmark program modules. -/"
    ),
    "LeanQbe.T.Examples.Kissat.BaseHub": (
        "/-!\nSubsystem hub re-exporting Kissat Core, LayerA, Dimacs, Plain, "
        "CorePlus, Full, FastCore,\nFastSched, Fast, Kitten, and DefSweep "
        "modules.\n-/"
    ),
    "LeanQbe.T.Examples.Kissat.M3Hub": (
        "/-! Subsystem hub re-exporting all Kissat M3 (`FullM3*`) "
        "specification and proof modules. -/"
    ),
    "LeanQbe.T.Examples.Kissat.M4Hub": (
        "/-! Subsystem hub re-exporting all Kissat M4 (`FullM4*`) "
        "specification and proof modules. -/"
    ),
}

ALL_HUBS: tuple[str, ...] = ROOT_LIBS + SUBSYSTEM_HUBS


@dataclass(frozen=True)
class ImportStmt:
    """Parsed import statement from a Lean source file."""

    line: int
    module: str
    is_public: bool
    is_meta: bool
    is_all: bool


def mod_to_rel_path(mod: str) -> Path:
    """Convert a Lean module name into its relative `.lean` path."""
    return Path(*mod.split(".")).with_suffix(".lean")


def rel_path_to_mod(rel: Path) -> str:
    """Convert a relative `.lean` path into its Lean module name."""
    return ".".join(rel.with_suffix("").parts)


def strip_comments_line(
    raw_line: str, depth: int
) -> tuple[str, int, bool]:
    """Strip `--` and nested `/- ... -/` comments from a single line."""
    out: list[str] = []
    i = 0
    n = len(raw_line)
    saw_doc_open = False
    while i < n:
        ch = raw_line[i]
        nxt = raw_line[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if ch == "-" and nxt == "-":
            break
        if ch == "/" and nxt == "-":
            if i + 2 < n and raw_line[i + 2] == "!":
                saw_doc_open = True
            depth = 1
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out).strip(), depth, saw_doc_open


def parse_imports(path: Path) -> tuple[bool, list[ImportStmt]]:
    """Parse header import statements from a Lean file quickly."""
    uses_module_system = False
    seen_header = False
    imports: list[ImportStmt] = []
    depth = 0

    with path.open("r", encoding="utf-8") as fh:
        for lineno, raw_line in enumerate(fh, start=1):
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
                vis = m.group(1)
                is_public = (vis == "public") if uses_module_system else True
                imports.append(
                    ImportStmt(
                        line=lineno,
                        module=m.group(4),
                        is_public=is_public,
                        is_meta=m.group(2) is not None,
                        is_all=m.group(3) is not None,
                    )
                )
                continue
            if seen_header or depth == 0:
                break
    return uses_module_system, imports


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


def load_legacy_regex(root: Path) -> re.Pattern[str]:
    """Read `legacy_cert_re` from `scripts/check.sh` or use canonical default."""
    check_sh = root / "scripts" / "check.sh"
    if check_sh.is_file():
        lines = check_sh.read_text(encoding="utf-8").splitlines()
        parts: list[str] = []
        for line in lines:
            s = line.strip()
            if s.startswith("legacy_cert_re='") and s.endswith("'"):
                parts = [s[len("legacy_cert_re='") : -1]]
            elif parts and s.startswith("legacy_cert_re+='") and s.endswith("'"):
                parts.append(s[len("legacy_cert_re+='") : -1])
            elif parts:
                break
        if parts:
            return re.compile("".join(parts))
    return re.compile(LEGACY_CERT_DEFAULT)


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


def classify_module(mod: str, legacy_re: re.Pattern[str]) -> str | None:
    """Assign a tracked `LeanQbe.*` module to its exact hub/barrel partition."""
    if mod in SUBSYSTEM_HUBS:
        return None
    if mod.startswith("LeanQbe.T.Amd64."):
        return "LeanQbeLegacyAmd64" if legacy_re.match(mod) else "LeanQbeAmd64"
    if mod.startswith("LeanQbe.T.Arm64."):
        return "LeanQbeLegacyArm64" if legacy_re.match(mod) else "LeanQbeArm64"
    if mod == "LeanQbe.T.Frontend.C0" or mod.startswith("LeanQbe.T.Frontend.C0."):
        return "LeanQbe.T.Frontend.C0.Hub"
    if mod.startswith("LeanQbe.T.LeanLCNF."):
        return "LeanQbe.T.LeanLCNF.Hub"
    if mod.startswith("LeanQbe.T.LeanLRC."):
        return "LeanQbe.T.LeanLRC.Hub"
    if mod.startswith("LeanQbe.T.Examples.Kissat."):
        sub = mod[len("LeanQbe.T.Examples.Kissat.") :]
        if sub.startswith("FullM3"):
            return "LeanQbe.T.Examples.Kissat.M3Hub"
        if sub.startswith("FullM4"):
            return "LeanQbe.T.Examples.Kissat.M4Hub"
        return "LeanQbe.T.Examples.Kissat.BaseHub"
    if mod.startswith("LeanQbe.T.Examples."):
        return "LeanQbe.T.Examples.Hub"
    if mod.startswith("LeanQbe.T."):
        return "LeanQbe.T.CoreHub"
    return "E1_FORBIDDEN"


def compute_closure(
    root_mod: str,
    root: Path,
    import_cache: dict[str, list[ImportStmt]],
) -> set[str]:
    """Compute transitive import closure of `root_mod` across local files."""
    seen: set[str] = set()
    stack: list[str] = [root_mod]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        if mod not in import_cache:
            path = root / mod_to_rel_path(mod)
            if not path.is_file():
                continue
            _, imps = parse_imports(path)
            import_cache[mod] = imps
        for imp in import_cache[mod]:
            if imp.module not in seen:
                stack.append(imp.module)
    return seen


ARCH_FORBIDDEN: dict[str, tuple[str, tuple[str, ...], bool]] = {
    "LeanQbeAmd64": ("x64", ("Kraken.AArch64", "LeanQbe.T.Arm64."), True),
    "LeanQbeLegacyAmd64": ("x64", ("Kraken.AArch64", "LeanQbe.T.Arm64."), False),
    "LeanQbeArm64": ("Arm64", ("Kraken.X64", "LeanQbe.T.Amd64."), True),
    "LeanQbeLegacyArm64": ("Arm64", ("Kraken.X64", "LeanQbe.T.Amd64."), False),
}


def check_isolation(
    hub: str,
    closure: set[str],
    legacy_re: re.Pattern[str],
) -> list[str]:
    """Enforce arch and active-vs-legacy isolation invariants on `closure`."""
    errors: list[str] = []
    if hub in ("LeanQbe", *SUBSYSTEM_HUBS):
        bad = sorted(
            m
            for m in closure
            if m.startswith(
                (
                    "Kraken.X64",
                    "Kraken.AArch64",
                    "LeanQbe.T.Amd64.",
                    "LeanQbe.T.Arm64.",
                )
            )
        )
        if bad:
            errors.append(
                f"{hub}: generic closure leaks arch module(s): "
                + ", ".join(bad[:5])
            )
        return errors

    if hub in ARCH_FORBIDDEN:
        label, opp_prefixes, forbid_legacy = ARCH_FORBIDDEN[hub]
        opp_name = "Arm64" if label == "x64" else "x64"
        bad_arch = sorted(m for m in closure if m.startswith(opp_prefixes))
        if bad_arch:
            errors.append(
                f"{hub}: {label} closure leaks {opp_name} module(s): "
                + ", ".join(bad_arch[:5])
            )
        if forbid_legacy:
            bad_leg = sorted(m for m in closure if legacy_re.match(m))
            if bad_leg:
                errors.append(
                    f"{hub}: active closure leaks legacy cert(s): "
                    + ", ".join(bad_leg[:5])
                )
    return errors


def build_partitions(
    tracked: dict[str, Path], legacy_re: re.Pattern[str]
) -> tuple[dict[str, list[str]], list[str]]:
    """Partition all tracked `LeanQbe.*` modules into their designated hubs."""
    partitions: dict[str, list[str]] = {h: [] for h in ALL_HUBS if h != "LeanQbe"}
    errors: list[str] = []
    for mod in sorted(tracked):
        dest = classify_module(mod, legacy_re)
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
    if hub in ("LeanQbeAmd64", "LeanQbeArm64", "LeanQbeLegacyAmd64", "LeanQbeLegacyArm64"):
        return ["LeanQbe", *sorted(partitions[hub])]
    return sorted(partitions[hub])


def render_hub(hub: str, imports: list[str]) -> str:
    """Render deterministic canonical Lean source text for `hub`."""
    lines: list[str] = ["module", ""]
    for mod in imports:
        lines.append(f"public import {mod}")
    lines.extend(["", "set_option autoImplicit false", "", HUB_DOCSTRINGS[hub], ""])
    return "\n".join(lines)


def run_check(root: Path, strict: bool) -> int:
    """Verify all 13 hub/barrel files against tracked modules and invariants."""
    errors = verify_lakefile(root)
    legacy_re = load_legacy_regex(root)
    tracked = list_tracked_lean_modules(root)
    partitions, part_errors = build_partitions(tracked, legacy_re)
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
            if hub in (
                "LeanQbeAmd64",
                "LeanQbeArm64",
                "LeanQbeLegacyAmd64",
                "LeanQbeLegacyArm64",
            ):
                if "LeanQbe" not in direct_set:
                    errors.append(f"{hub}: missing required `public import LeanQbe`")
                allowed_base = {"LeanQbe"}
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
                owner = classify_module(mod, legacy_re)
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
            errors.extend(check_isolation(hub, closure, legacy_re))

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
    """Regenerate all 13 hub/barrel files deterministically from tracked files."""
    errors = verify_lakefile(root)
    legacy_re = load_legacy_regex(root)
    tracked = list_tracked_lean_modules(root)
    partitions, part_errors = build_partitions(tracked, legacy_re)
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
