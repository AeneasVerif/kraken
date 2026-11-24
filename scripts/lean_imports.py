#!/usr/bin/env python3
"""Shared Lean 4 module import, comment, and header parsing utilities."""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

IMPORT_LINE_RE = re.compile(
    r"^\s*(?:(public|private)\s+)?(?:(meta)\s+)?import\s+(?:(all)\s+)?"
    r"([A-Za-z_][A-Za-z0-9_'.]*)(?:\s+(--.*))?\s*$"
)

IMPORT_RE = IMPORT_LINE_RE


@dataclass(frozen=True)
class ImportEntry:
    """Single parsed Lean import statement for 3-way merge algebra."""

    module: str
    is_public: bool
    is_meta: bool = False
    is_all: bool = False
    comment: str | None = None

    @property
    def key(self) -> tuple[str, bool]:
        """Identity key `(module, is_meta)` allowing normal + meta import pairs."""
        return (self.module, self.is_meta)

    @property
    def tier(self) -> tuple[int, bool, bool]:
        """Deterministic formatting tier matching LeanQbe conventions."""
        if self.is_public and not self.is_meta and not self.is_all:
            return (0, False, False)
        if self.is_public and self.is_meta and not self.is_all:
            return (1, False, False)
        if not self.is_public and not self.is_meta and not self.is_all:
            return (2, False, False)
        if not self.is_public and not self.is_meta and self.is_all:
            return (3, False, False)
        if not self.is_public and self.is_meta and not self.is_all:
            return (4, False, False)
        if not self.is_public and self.is_meta and self.is_all:
            return (5, False, False)
        return (6 if not self.is_public else 1, self.is_meta, self.is_all)

    def format_line(self) -> str:
        """Render canonical Lean import line."""
        parts: list[str] = []
        if self.is_public:
            parts.append("public")
        if self.is_meta:
            parts.append("meta")
        parts.append("import")
        if self.is_all:
            parts.append("all")
        parts.append(self.module)
        line = " ".join(parts)
        if self.comment:
            line = f"{line} {self.comment}"
        return line


@dataclass(frozen=True)
class ImportStmt:
    """Parsed Lean import statement with line number and visibility."""

    line: int
    module: str
    is_public: bool
    is_meta: bool = False
    is_all: bool = False
    comment: str | None = None

    def to_entry(self) -> ImportEntry:
        """Convert to line-free `ImportEntry`."""
        return ImportEntry(
            module=self.module,
            is_public=self.is_public,
            is_meta=self.is_meta,
            is_all=self.is_all,
            comment=self.comment,
        )


@dataclass
class ParsedLeanFile:
    """Split representation of a Lean file's top header and body."""

    preamble: str
    has_module: bool
    has_prelude: bool
    blank_after_module: bool
    imports: dict[tuple[str, bool], ImportEntry]
    sep_blank_lines: int
    body: str
    has_header: bool


def mod_to_rel_path(mod: str) -> Path:
    """Convert a Lean module name into its relative `.lean` path."""
    return Path(*mod.split(".")).with_suffix(".lean")


def rel_path_to_mod(rel: Path) -> str:
    """Convert a relative `.lean` path into its Lean module name."""
    return ".".join(rel.with_suffix("").parts)


def module_to_path(root: Path, mod: str) -> Path | None:
    """Resolve a workspace-local Lean module name to a `.lean` path."""
    candidate = root / mod_to_rel_path(mod)
    return candidate if candidate.is_file() else None


def advance_block_comment(raw: str, depth: int) -> int:
    """Update nested `/- ... -/` comment depth across one line."""
    i = 0
    n = len(raw)
    while i < n:
        ch = raw[i]
        nxt = raw[i + 1] if i + 1 < n else ""
        if ch == "/" and nxt == "-":
            depth += 1
            i += 2
            continue
        if ch == "-" and nxt == "/":
            depth = max(0, depth - 1)
            i += 2
            continue
        i += 1
    return depth


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
                depth = max(0, depth - 1)
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
    """Parse header import statements from a Lean file quickly.

    Stops immediately at the first non-comment, non-import line so large proof
    or data modules are scanned in microseconds.
    """
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
                is_public = (vis == "public") if uses_module_system else (vis != "private")
                imports.append(
                    ImportStmt(
                        line=lineno,
                        module=m.group(4),
                        is_public=is_public,
                        is_meta=m.group(2) is not None,
                        is_all=m.group(3) is not None,
                        comment=m.group(5),
                    )
                )
                continue
            if seen_header or depth == 0:
                break
    return uses_module_system, imports


def seen_module_or_import(has_module: bool, seen_import: bool) -> bool:
    """Return True if `module` or any `import` has already been parsed."""
    return has_module or seen_import


def split_lean_file(text: str) -> ParsedLeanFile:
    """Parse top-of-file module/prelude/import header separately from the body."""
    lines = text.splitlines(keepends=True)
    n = len(lines)
    preamble_lines: list[str] = []
    pending: list[str] = []
    imports: dict[tuple[str, bool], ImportEntry] = {}
    has_module = False
    has_prelude = False
    seen_header_token = False
    seen_import = False
    blank_after_module = False
    last_hdr_idx = -1
    depth = 0

    for i, raw in enumerate(lines):
        if depth > 0:
            pending.append(raw)
            depth = advance_block_comment(raw, depth)
            continue
        s = raw.strip()
        if not s:
            pending.append(raw)
            continue
        if s.startswith("--"):
            pending.append(raw)
            continue
        if s.startswith("/-!"):
            break
        if s.startswith("/-"):
            depth = advance_block_comment(raw, 0)
            pending.append(raw)
            continue
        if s == "module" and not seen_module_or_import(has_module, seen_import):
            preamble_lines.extend(pending)
            pending.clear()
            has_module = True
            seen_header_token = True
            last_hdr_idx = i
            continue
        if s == "prelude" and not seen_import:
            if not seen_header_token:
                preamble_lines.extend(pending)
            pending.clear()
            has_prelude = True
            seen_header_token = True
            last_hdr_idx = i
            continue
        m = IMPORT_LINE_RE.match(raw)
        if m:
            if not seen_header_token:
                preamble_lines.extend(pending)
            elif not seen_import and any(not p.strip() for p in pending):
                blank_after_module = True
            pending.clear()
            seen_header_token = True
            seen_import = True
            last_hdr_idx = i
            entry = ImportEntry(
                module=m.group(4),
                is_public=(m.group(1) == "public"),
                is_meta=(m.group(2) is not None),
                is_all=(m.group(3) is not None),
                comment=m.group(5),
            )
            prev = imports.get(entry.key)
            if prev is None:
                imports[entry.key] = entry
            else:
                imports[entry.key] = ImportEntry(
                    module=entry.module,
                    is_public=(prev.is_public and entry.is_public),
                    is_meta=entry.is_meta,
                    is_all=(prev.is_all or entry.is_all),
                    comment=prev.comment or entry.comment,
                )
            continue
        break

    if last_hdr_idx == -1:
        return ParsedLeanFile(
            preamble="",
            has_module=False,
            has_prelude=False,
            blank_after_module=False,
            imports={},
            sep_blank_lines=0,
            body=text,
            has_header=False,
        )

    body_start = last_hdr_idx + 1
    sep_blanks = 0
    while body_start < n and not lines[body_start].strip():
        sep_blanks += 1
        body_start += 1
    body = "".join(lines[body_start:])
    return ParsedLeanFile(
        preamble="".join(preamble_lines),
        has_module=has_module,
        has_prelude=has_prelude,
        blank_after_module=blank_after_module,
        imports=imports,
        sep_blank_lines=sep_blanks,
        body=body,
        has_header=True,
    )
