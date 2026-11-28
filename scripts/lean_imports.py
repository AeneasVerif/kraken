#!/usr/bin/env python3
"""Shared Lean 4 module import, comment, and header parsing utilities."""

from __future__ import annotations

import collections
import re
import subprocess
import sys
from collections.abc import Callable, Iterable, Mapping
from collections.abc import Set as AbstractSet
from dataclasses import dataclass
from pathlib import Path

IMPORT_LINE_RE = re.compile(
    r"^\s*(?:(public|private)\s+)?(?:(meta)\s+)?import\s+(?:(all)\s+)?"
    r"([A-Za-z_][A-Za-z0-9_'.]*)(?:\s+(--.*))?\s*$"
)

IMPORT_RE = IMPORT_LINE_RE

DEFAULT_MAX_LOC = 2500
DEFAULT_MAX_COL = 100
DEFAULT_MAX_DECL_LOC = 450
DEFAULT_MAX_PROOF_THM_LOC = DEFAULT_MAX_DECL_LOC

PROOF_SHARD_PREFIXES: tuple[str, ...] = (
    "LeanQbe/T/Examples/Kissat/Proof/",
    "LeanQbe/T/Examples/Bitblast/Proof/",
)
LEGACY_FULL_PATH_RE = re.compile(r"^LeanQbe/T/Examples/Kissat/Full[^/]*\.lean$")
LOCAL_MODULE_ROOTS: frozenset[str] = frozenset({
    "LeanQbe",
    "LeanQbeAmd64",
    "LeanQbeArm64",
    "LeanQbeBootstrap0",
    "LeanQbeTest",
    "LeanQbeBootstrap0Test",
    "Kraken",
    "KrakenAArch64",
    "KrakenBedrock2",
})
HUNK_NEW_RE = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")

BANNED_TOKEN_RE = re.compile(
    r"\b(?:sorry|admit|bv_decide|native_decide|ofReduceBool|ofReduceNat"
    r"|trustCompiler)\b"
    r"|decide\s+\+native"
)
BANNED_ATTR_RE = re.compile(r"@\[[^\]]*\b(?:implemented_by|extern)\b")
AXIOM_DECL_RE = re.compile(
    r"(?:^|;|\bin\s+)\s*(?:(?:@\[[^\]]*\]|public|private|protected|unsafe|"
    r"noncomputable|local|scoped|meta)\s+)*axiom\b"
)
BAD_IMPORT_ALL_RE = re.compile(
    r"^\s*(?:public\s+(?:meta\s+)?import\s+all\b"
    r"|(?:meta\s+)?import\s+all\s+LeanQbe\b)"
)
ANY_IMPORT_ALL_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+all\b"
)
CONFLICT_RE = re.compile(r"^(?:<{7}|={7}|>{7})(?: |$)")
EXPOSE_ATTR_RE = re.compile(r"@\[[^\]]*\bexpose\b[^\]]*\]")
ANY_ATTR_RE = re.compile(r"@\[[^\]]*\]")
THM_DECL_RE = re.compile(
    r"^(?:(?:public|private|protected|noncomputable|unsafe|local|scoped|"
    r"meta|nonrec)\s+)*(?:theorem|lemma)\b(?:\s+([^\s:({\[<\"|]+))?"
)
DECL_RE = re.compile(
    r"^(?:(?:public|private|protected|noncomputable|unsafe|partial|local|"
    r"scoped|meta|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class|"
    r"opaque|macro|macro_rules|elab|elab_rules)\b(?:\s+([^\s:({\[<\"|]+))?"
)
MODIFIER_ONLY_RE = re.compile(
    r"^(?:(?:@\[[^\]]*\]|public|private|protected|noncomputable|unsafe|"
    r"partial|local|scoped|meta|nonrec)(?:\s+|$))+$"
)
NS_OPEN_RE = re.compile(r"^namespace\s+(\S+)")
SEC_OPEN_RE = re.compile(
    r"^(?:(?:@\[[^\]]*\]|public|private|protected|noncomputable)\s+)*"
    r"section(?:\s+(\S+))?(?:\s|$)"
)
MUTUAL_OPEN_RE = re.compile(r"^mutual(?:\s|$)")
END_SCOPE_RE = re.compile(r"^end(?:\s+(\S+))?(?:\s|$)")
TOP_DECL_RE = re.compile(
    r"^(?:(?:public|private|protected|noncomputable|unsafe|partial|local|"
    r"scoped|meta|nonrec)\s+)*(?:(?:theorem|lemma|def|abbrev|structure|"
    r"inductive|class|instance|axiom|opaque|example|macro|macro_rules|syntax|"
    r"elab|elab_rules|declare_syntax_cat|section|namespace|end|open|variable|"
    r"universe|set_option|attribute|mutual|initialize|builtin_initialize|"
    r"register_simp_attr|deriving|export|notation|infix|infixl|infixr|"
    r"prefix|postfix|run_cmd|#print|#check|#guard|#eval|#reduce)\b"
    r"|c0_[A-Za-z0-9_]*!(?:\s|$))"
)


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


def _parse_imports_lines(lines: Iterable[str]) -> tuple[bool, list[ImportStmt]]:
    """Parse header import statements from an iterable of raw Lean lines."""
    uses_module_system = False
    seen_header = False
    imports: list[ImportStmt] = []
    depth = 0

    for lineno, raw_line in enumerate(lines, start=1):
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


def parse_imports_text(text: str) -> tuple[bool, list[ImportStmt]]:
    """Parse header import statements from an in-memory Lean source string."""
    return _parse_imports_lines(text.splitlines())


def parse_imports(path: Path) -> tuple[bool, list[ImportStmt]]:
    """Parse header import statements from a Lean file quickly.

    Stops immediately at the first non-comment, non-import line so large proof
    or data modules are scanned in microseconds.
    """
    with path.open("r", encoding="utf-8") as fh:
        return _parse_imports_lines(fh)


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


def _strip_lean_lines(src: str) -> tuple[str, list[bool]]:
    """Strip Lean comments, strings, and char literals; also flag top-level doc opens."""
    out: list[str] = []
    doc_opens: list[bool] = []
    cur_doc = False
    i = 0
    n = len(src)
    depth = 0
    in_str = False
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
                doc_opens.append(cur_doc)
                cur_doc = False
            i += 1
            continue
        if in_str:
            if ch == "\\" and i + 1 < n:
                if src[i + 1] == "\n":
                    out.append("\n")
                    doc_opens.append(cur_doc)
                    cur_doc = False
                i += 2
                continue
            if ch == '"':
                in_str = False
                i += 1
                continue
            if ch == "\n":
                out.append("\n")
                doc_opens.append(cur_doc)
                cur_doc = False
            i += 1
            continue
        if ch == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if ch == "/" and nxt == "-":
            if i + 2 < n and src[i + 2] in ("!", "-"):
                cur_doc = True
            depth = 1
            i += 2
            continue
        if ch == '"':
            in_str = True
            out.append('""')
            i += 1
            continue
        if ch == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'")):
            if i + 2 < n and src[i + 1] == "\\":
                j = i + 2
                while j < n and src[j] != "\n" and src[j] != "'" and j - i < 12:
                    j += 1
                if j < n and src[j] == "'":
                    out.append("''")
                    i = j + 1
                    continue
            elif i + 2 < n and src[i + 1] != "\n" and src[i + 2] == "'":
                out.append("''")
                i += 3
                continue
        if ch == "\n":
            out.append("\n")
            doc_opens.append(cur_doc)
            cur_doc = False
            i += 1
            continue
        out.append(ch)
        i += 1
    doc_opens.append(cur_doc)
    return "".join(out), doc_opens


def strip_lean_code(src: str) -> str:
    """Strip Lean comments, strings, and char literals, preserving line numbers."""
    cleaned, _ = _strip_lean_lines(src)
    return cleaned


def is_proof_shard_path(rel_path: str) -> bool:
    """Return True if `rel_path` is a P0-5 `Kissat/Proof/` or `Bitblast/Proof/` shard."""
    return rel_path.startswith(PROOF_SHARD_PREFIXES)


def is_legacy_full_path(rel_path: str) -> bool:
    """Return True if `rel_path` is a legacy top-level `Kissat/Full*.lean` file."""
    return bool(LEGACY_FULL_PATH_RE.match(rel_path))


def is_local_module(mod: str) -> bool:
    """Return True if `mod` belongs to a repo-local Lake library root."""
    return mod.split(".", 1)[0] in LOCAL_MODULE_ROOTS


def parse_diff_changed_lines(diff_text: str) -> dict[str, set[int]]:
    """Parse `git diff -U0 --no-renames` into `{rel_path: {1-based changed lines}}`."""
    out: dict[str, set[int]] = {}
    cur_file: str | None = None
    for raw in diff_text.splitlines():
        if raw.startswith("+++ "):
            if raw == "+++ /dev/null":
                cur_file = None
            elif raw.startswith("+++ b/"):
                cur_file = raw[6:]
                out.setdefault(cur_file, set())
            else:
                cur_file = None
            continue
        if cur_file is None:
            continue
        m = HUNK_NEW_RE.match(raw)
        if m:
            start = int(m.group(1))
            count = 1 if m.group(2) is None else int(m.group(2))
            if count > 0:
                out[cur_file].update(range(start, start + count))
    return out


def check_tracked_local_imports(
    root: Path,
    rel_path: str,
    text: str,
    tracked_files: AbstractSet[str],
) -> list[str]:
    """Verify every local `LeanQbe*`/`Kraken*` import in `text` is git-tracked and present."""
    errs: list[str] = []
    _, imps = parse_imports_text(text)
    for imp in imps:
        if not is_local_module(imp.module):
            continue
        imp_rel = mod_to_rel_path(imp.module).as_posix()
        on_disk = (root / imp_rel).is_file()
        if imp_rel not in tracked_files:
            if on_disk:
                errs.append(
                    f"{rel_path}:{imp.line}: imported local module `{imp.module}` "
                    f"({imp_rel}) is untracked (exists on disk but not git-tracked)"
                )
            else:
                errs.append(
                    f"{rel_path}:{imp.line}: imported local module `{imp.module}` "
                    f"({imp_rel}) is missing / not git-tracked"
                )
        elif not on_disk:
            errs.append(
                f"{rel_path}:{imp.line}: imported local module `{imp.module}` "
                f"({imp_rel}) is tracked in git but missing from working tree"
            )
    return errs


def _pop_scope(scopes: list[tuple[str, str | None, bool, int]], end_name: str | None) -> None:
    """Pop matching Lean `namespace`/`section`/`mutual` scope(s) from stack."""
    if not scopes:
        return
    if end_name is not None:
        for pos in range(len(scopes) - 1, -1, -1):
            if scopes[pos][1] == end_name:
                del scopes[pos:]
                return
    scopes.pop()


def audit_lean_source(
    rel_path: str,
    text: str,
    *,
    max_loc: int = DEFAULT_MAX_LOC,
    max_col: int = DEFAULT_MAX_COL,
    max_proof_thm_loc: int = DEFAULT_MAX_PROOF_THM_LOC,
    max_decl_loc: int | None = None,
) -> dict[str, object]:
    """Audit a single `.lean` source string for hygiene and P0-5 rules."""
    eff_max_decl_loc = max_proof_thm_loc if max_decl_loc is None else max_decl_loc
    raw_lines = text.splitlines()
    loc = len(raw_lines)
    over_loc = loc >= max_loc
    long_lines: list[dict[str, object]] = []
    expose_on_thm: list[int] = []
    banned_by_line: dict[int, str] = {}
    bad_import_all: list[int] = []
    total_import_all = 0
    conflicts: list[int] = []

    is_proof_shard = is_proof_shard_path(rel_path)
    proof_import_all: list[int] = []
    proof_expose_section: list[dict[str, int]] = []
    proof_long_theorems: list[dict[str, object]] = []
    long_decls: list[dict[str, object]] = []

    cleaned, doc_opens = _strip_lean_lines(text)
    for m in BANNED_ATTR_RE.finditer(cleaned):
        lineno = cleaned[: m.start()].count("\n") + 1
        banned_by_line.setdefault(lineno, m.group(0).replace("\n", " ")[:90])

    cleaned_lines = cleaned.splitlines()
    # Pad if trailing newline edge cases cause a mismatch.
    while len(cleaned_lines) < loc:
        cleaned_lines.append("")
    while len(doc_opens) < loc:
        doc_opens.append(False)

    pending_expose = False
    scopes: list[tuple[str, str | None, bool, int]] = []
    flagged_expose_secs: set[int] = set()
    in_decl: tuple[str, str, str, int, int] | None = None
    last_decl_code_ln = 0

    def _flush_decl() -> None:
        nonlocal in_decl
        if in_decl is None:
            return
        decl_kind, decl_name, decl_ns, decl_start, _ = in_decl
        span = last_decl_code_ln - decl_start + 1
        if span > eff_max_decl_loc:
            long_decls.append(
                {
                    "kind": decl_kind,
                    "name": decl_name,
                    "ns": decl_ns,
                    "start_line": decl_start,
                    "end_line": last_decl_code_ln,
                    "lines": span,
                }
            )
        if (
            is_proof_shard
            and decl_kind in ("theorem", "lemma")
            and span > max_proof_thm_loc
        ):
            proof_long_theorems.append(
                {
                    "name": decl_name,
                    "start_line": decl_start,
                    "end_line": last_decl_code_ln,
                    "lines": span,
                }
            )
        in_decl = None

    for idx, raw in enumerate(raw_lines, 1):
        if CONFLICT_RE.match(raw):
            conflicts.append(idx)
        if len(raw) > max_col:
            long_lines.append({"line": idx, "cols": len(raw)})

        raw_clean = cleaned_lines[idx - 1]
        code = raw_clean.strip()
        indent = len(raw) - len(raw.lstrip())
        is_doc_start = doc_opens[idx - 1]
        without_attrs = ANY_ATTR_RE.sub("", code).strip() if code else ""

        if in_decl is not None:
            decl_indent = in_decl[4]
            # Close declaration before the next top-level command, attribute, or doc comment.
            if indent <= decl_indent and (
                is_doc_start
                or code.startswith("@[")
                or (without_attrs and TOP_DECL_RE.match(without_attrs))
            ):
                _flush_decl()

        if not code:
            continue

        if BAD_IMPORT_ALL_RE.match(code):
            bad_import_all.append(idx)
        if ANY_IMPORT_ALL_RE.match(code):
            total_import_all += 1
            if is_proof_shard:
                proof_import_all.append(idx)
        if BANNED_TOKEN_RE.search(code) or AXIOM_DECL_RE.search(code):
            banned_by_line.setdefault(idx, code[:90])

        # Track section/namespace/mutual scopes when not inside a declaration body.
        if in_decl is None:
            m_ns = NS_OPEN_RE.match(code)
            m_sec = SEC_OPEN_RE.match(code)
            if m_ns:
                scopes.append(("ns", m_ns.group(1), False, idx))
            elif MUTUAL_OPEN_RE.match(code):
                scopes.append(("mutual", None, False, idx))
            elif m_sec:
                sec_expose = bool(EXPOSE_ATTR_RE.search(code)) or pending_expose
                scopes.append(("sec", m_sec.group(1), sec_expose, idx))
                pending_expose = False
            else:
                m_end = END_SCOPE_RE.match(code)
                if m_end:
                    _pop_scope(scopes, m_end.group(1))

        has_expose = bool(EXPOSE_ATTR_RE.search(code))
        m_decl = DECL_RE.match(without_attrs)
        is_thm = bool(
            in_decl is None and m_decl and m_decl.group(1) in ("theorem", "lemma")
        )

        if is_thm:
            if has_expose or pending_expose:
                expose_on_thm.append(idx)
            pending_expose = False
            if is_proof_shard:
                for kind, _sname, sec_exp, sec_ln in scopes:
                    if kind == "sec" and sec_exp and sec_ln not in flagged_expose_secs:
                        flagged_expose_secs.add(sec_ln)
                        proof_expose_section.append(
                            {"section_line": sec_ln, "theorem_line": idx}
                        )
        else:
            if has_expose:
                if (
                    not SEC_OPEN_RE.match(code)
                    and (not without_attrs or MODIFIER_ONLY_RE.match(without_attrs))
                ):
                    pending_expose = True
                else:
                    pending_expose = False
            elif pending_expose:
                if not (not without_attrs or MODIFIER_ONLY_RE.match(without_attrs)):
                    pending_expose = False

        if m_decl and in_decl is None:
            ns_prefix = ".".join(
                sname for skind, sname, _, _ in scopes if skind == "ns" and sname
            )
            in_decl = (
                m_decl.group(1),
                m_decl.group(2) or "<anon>",
                ns_prefix,
                idx,
                indent,
            )
            last_decl_code_ln = idx
        elif in_decl is not None:
            last_decl_code_ln = idx

    _flush_decl()

    banned_hits = [
        {"line": ln, "text": banned_by_line[ln]} for ln in sorted(banned_by_line)
    ]
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
        "proof_import_all": proof_import_all,
        "proof_expose_section": proof_expose_section,
        "proof_long_theorems": proof_long_theorems,
        "long_decls": long_decls,
    }


SUBSYSTEM_HUBS: tuple[str, ...] = (
    "LeanQbe.T.CoreHub", "LeanQbe.T.Logic.ExtraHub", "LeanQbe.T.Unified.Hub",
    "LeanQbe.T.Wasm.Hub", "LeanQbe.T.Frontend.C0.Hub", "LeanQbe.T.LeanLCNF.Hub",
    "LeanQbe.T.Examples.Hub", "LeanQbe.T.Examples.Kissat.BaseHub",
)
ROOT_LIBS: tuple[str, ...] = (
    "LeanQbe", "LeanQbeAmd64", "LeanQbeArm64", "LeanQbeBootstrap0",
)
ALL_HUBS: tuple[str, ...] = ROOT_LIBS + SUBSYSTEM_HUBS
BARRELS: frozenset[str] = frozenset(ALL_HUBS)
BARREL_PATHS: frozenset[str] = frozenset(mod_to_rel_path(m).as_posix() for m in ALL_HUBS)
KRAKEN_ROOT_FILES: frozenset[str] = frozenset({
    "Kraken.lean", "KrakenAArch64.lean", "KrakenBedrock2.lean",
    "KrakenRunnerX64.lean", "KrakenRunnerAArch64.lean", "Att2Intel.lean", "Bedrock2C.lean",
})
KISSAT_X64_PFX: tuple[str, ...] = (
    "LeanQbe.T.Examples.Kissat.Build.Amd64.",
    "LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.",
)
KISSAT_ARM_PFX: tuple[str, ...] = (
    "LeanQbe.T.Examples.Kissat.Build.Arm64.",
    "LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.",
)
X64_PFX: tuple[str, ...] = ("Kraken.X64", "LeanQbe.T.Amd64.", *KISSAT_X64_PFX)
ARM_PFX: tuple[str, ...] = ("Kraken.AArch64", "LeanQbe.T.Arm64.", *KISSAT_ARM_PFX)
EXE_ROOT_TO_TARGET: dict[str, str] = {"Main": "leanqbe", "MainArm64": "leanqbe-arm64"}

FORBIDDEN_TOKENS_PRE_RE = re.compile(
    r"\b(?:sorry|admit|bv_decide|native_decide|ofReduceBool|ofReduceNat"
    r"|trustCompiler|axiom|implemented_by|extern)\b|\+native"
)
FORBIDDEN_CLASS0_RE = re.compile(
    r"^(?:lakefile\.toml|lean-toolchain|lake-manifest\.json"
    r"|scripts/(?:check\.sh|common\.sh|_common\.py|lean_imports\.py|headline\.txt|headlines\.d/))"
)
CLASS0_RE = re.compile(
    r"^(?:(?:LeanQbe-)?README\.md|NOTES\.md|DEVELOPER\.md|CONTRIBUTING\.md|docs/.*|img/.*|bench/.*"
    r"|test/.*\.(?:c|h|py|sh|cnf|lrat)|scripts/(?:fast_land|all|preflight)\.sh"
    r"|scripts/(?:gen_cert_slices|test_gen_cert_slices|test_infra_speedup"
    r"|merge_lean_imports|select_tests)\.py)$"
)
X64_LEAN_RE = re.compile(
    r"^(?:LeanQbe/T/Amd64/.*|LeanQbe/T/Examples/Kissat/Build/(?:Oracle/)?Amd64/.*"
    r"|LeanQbeTest/T/[^/]*(?:X64|Amd64)[^/]*)\.lean$"
)
ARM64_LEAN_RE = re.compile(
    r"^(?:LeanQbe/T/Arm64/.*|LeanQbe/T/Examples/Kissat/Build/(?:Oracle/)?Arm64/.*"
    r"|LeanQbeTest/T/[^/]*Arm64[^/]*)\.lean$"
)
_ARCH_NONLEAN_TAIL = r"(?:LeanQbe-)?README\.md|NOTES\.md|DEVELOPER\.md|CONTRIBUTING\.md|docs/.*"
X64_NONLEAN_RE = re.compile(rf"^(?:{_ARCH_NONLEAN_TAIL}|scripts/headlines\.d/amd64\.txt)$")
ARM64_NONLEAN_RE = re.compile(rf"^(?:{_ARCH_NONLEAN_TAIL}|scripts/headlines\.d/arm64\.txt)$")


def run_git(
    repo: Path, *args: str, check: bool = False, text: bool = True
) -> subprocess.CompletedProcess:
    """Execute `git -C <repo> <args...>` capturing stdout/stderr."""
    return subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, text=text, check=check
    )


def is_kraken_path(rel: Path | str) -> bool:
    """Return True if `rel` resides under `Kraken/` or is a root Kraken file."""
    p = rel if isinstance(rel, Path) else Path(rel)
    return (bool(p.parts) and p.parts[0] == "Kraken") or (p.name in KRAKEN_ROOT_FILES)


def modules_to_lake_targets(mods: Iterable[str]) -> list[str]:
    """Map executable root modules (`Main`, `MainArm64`) to Lake exe targets."""
    return sorted({EXE_ROOT_TO_TARGET.get(m, m) for m in mods})


def list_lean_files(
    root: Path, *paths: str, include_untracked: bool = True, excludes: tuple[str, ...] = ()
) -> list[Path]:
    """List `.lean` repo-relative paths via `git ls-files` (with `rglob` fallback)."""
    cmd = ["ls-files", "-z", "--cached"]
    if include_untracked:
        cmd.extend(["--others", "--exclude-standard"])
    cmd.extend(paths if paths else ("*.lean",))
    cmd.extend(f":(exclude){ex}" for ex in excludes)
    res = run_git(root, *cmd, text=False)
    if res.returncode == 0:
        rels = (Path(b.decode("utf-8")) for b in res.stdout.split(b"\0") if b)
        return sorted({r for r in rels if r.suffix == ".lean"})
    bases = [root / p for p in paths] if paths else [root]
    out = {
        p.relative_to(root)
        for base in bases if base.is_dir()
        for p in base.rglob("*.lean")
        if not any(p.relative_to(root).parts[:1] == (ex,) for ex in excludes)
    }
    return sorted(out)


def compute_import_closure(
    roots: Iterable[str], root: Path, *, import_cache: dict[str, list[ImportStmt]] | None = None
) -> set[str]:
    """Compute transitive import closure of `roots` across local `.lean` files."""
    cache = import_cache if import_cache is not None else {}
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        if mod not in cache:
            path = root / mod_to_rel_path(mod)
            if not path.is_file():
                continue
            _, cache[mod] = parse_imports(path)
        for imp in cache[mod]:
            if imp.module not in seen:
                stack.append(imp.module)
    return seen


def bfs_rdeps(
    seeds: Iterable[str], rgraph: Mapping[str, Iterable[str]], *, max_rdeps: int | None = None
) -> list[str] | None:
    """Run BFS over `rgraph` from `seeds`, returning `None` if `max_rdeps` exceeded."""
    seed_list = sorted(set(seeds))
    if not seed_list:
        return []
    if max_rdeps is not None and len(seed_list) > max_rdeps:
        return None
    seen = set(seed_list)
    q: collections.deque[str] = collections.deque(seed_list)
    while q:
        cur = q.popleft()
        for nxt in rgraph.get(cur, ()):
            if nxt not in seen:
                seen.add(nxt)
                if max_rdeps is not None and len(seen) > max_rdeps:
                    return None
                q.append(nxt)
    return sorted(seen)


def collect_lean_rdeps(
    root: Path,
    seeds: Iterable[str],
    *,
    lean_rel_paths: Iterable[Path | str] | None = None,
    read_imports_fn: Callable[[Path], Iterable[str]] | None = None,
    barrels: AbstractSet[str] = BARRELS,
    max_rdeps: int | None = None,
) -> list[str] | None:
    """Build non-barrel reverse-import graph and return BFS closure of `seeds`."""
    seed_set = set(seeds)
    if not seed_set:
        return []
    if max_rdeps is not None and len(seed_set) > max_rdeps:
        return None
    raw_paths = list(lean_rel_paths) if lean_rel_paths is not None else list_lean_files(root)
    rgraph: dict[str, list[str]] = collections.defaultdict(list)
    for raw_rel in raw_paths:
        rel = raw_rel if isinstance(raw_rel, Path) else Path(raw_rel)
        if is_kraken_path(rel):
            continue
        mod = rel_path_to_mod(rel)
        if mod in barrels:
            continue
        if read_imports_fn is not None:
            imps = read_imports_fn(rel)
        else:
            full = root / rel
            if not full.is_file():
                continue
            imps = (imp.module for imp in parse_imports(full)[1])
        for imp_mod in imps:
            if imp_mod not in barrels:
                rgraph[imp_mod].append(mod)
    return bfs_rdeps(seed_set, rgraph, max_rdeps=max_rdeps)


def classify_module_arch(
    root: Path,
    mod: str,
    cache: dict[str, str],
    stack: set[str] | None = None,
    *,
    c_gen: AbstractSet[str] = frozenset(),
    x64_only: AbstractSet[str] = frozenset(),
    arm_only: AbstractSet[str] = frozenset(),
    recurse_prefixes: tuple[str, ...] | None = None,
    missing_status: str = "generic",
    import_cache: dict[str, list[ImportStmt]] | None = None,
) -> str:
    """Classify a Lean module as `generic`, `x64`, `arm64`, or `conflict`."""
    if mod in cache:
        return cache[mod]
    if mod in c_gen:
        cache[mod] = "generic"
        return "generic"
    if mod in x64_only or mod == "LeanQbeAmd64" or mod.startswith(X64_PFX):
        cache[mod] = "x64"
        return "x64"
    if mod in arm_only or mod == "LeanQbeArm64" or mod.startswith(ARM_PFX):
        cache[mod] = "arm64"
        return "arm64"
    cur_stack = stack if stack is not None else set()
    if mod in cur_stack:
        return "generic"
    p = root / mod_to_rel_path(mod)
    if not p.is_file():
        return missing_status
    if import_cache is not None and mod in import_cache:
        imps = import_cache[mod]
    else:
        _, imps = parse_imports(p)
        if import_cache is not None:
            import_cache[mod] = imps

    arches: set[str] = set()
    nxt = cur_stack | {mod}
    for imp in imps:
        im = imp.module
        if im in c_gen:
            continue
        is_direct = (
            im in ("LeanQbeAmd64", "LeanQbeArm64") or im in x64_only or im in arm_only
            or im.startswith(X64_PFX) or im.startswith(ARM_PFX)
        )
        if recurse_prefixes is not None and not is_direct and not im.startswith(recurse_prefixes):
            continue
        sub = classify_module_arch(
            root, im, cache, nxt, c_gen=c_gen, x64_only=x64_only, arm_only=arm_only,
            recurse_prefixes=recurse_prefixes, missing_status=missing_status,
            import_cache=import_cache,
        )
        if sub in ("x64", "arm64", "conflict"):
            arches.add(sub)
    res = (
        "conflict" if ("conflict" in arches or {"x64", "arm64"} <= arches)
        else "x64" if "x64" in arches
        else "arm64" if "arm64" in arches
        else "generic"
    )
    cache[mod] = res
    return res


def read_headline_entries(lines: Iterable[str]) -> list[tuple[str, str]]:
    """Parse `<module> <constant>` pairs from headline lines."""
    entries: list[tuple[str, str]] = []
    for raw in lines:
        s = raw.strip()
        if s and not s.startswith("#"):
            parts = s.split()
            if len(parts) >= 2:
                entries.append((parts[0], parts[1]))
    return entries


def collect_active_headlines(root: Path) -> list[tuple[str, str]]:
    """Collect `<module> <constant>` entries from `scripts/headlines.d/` or `headline.txt`."""
    hdir = root / "scripts" / "headlines.d"
    files = sorted(hdir.glob("*.txt")) if hdir.is_dir() else []
    if not files:
        single = root / "scripts" / "headline.txt"
        files = [single] if single.is_file() else []
    out: list[tuple[str, str]] = []
    for fp in files:
        out.extend(read_headline_entries(fp.read_text(encoding="utf-8").splitlines()))
    return out


def collect_hygiene_violations(
    rel_path: str,
    rep: Mapping[str, object],
    *,
    base_loc: int | None = None,
    changed_lines: AbstractSet[int] | None = None,
    base_long_decls: Mapping[tuple[str, str, str], int] | None = None,
    max_loc: int = DEFAULT_MAX_LOC,
    max_col: int = DEFAULT_MAX_COL,
    max_proof_thm_loc: int = DEFAULT_MAX_PROOF_THM_LOC,
    max_decl_loc: int | None = None,
    first_long_line_only: bool = False,
    banned_label: str = "forbidden token",
) -> list[str]:
    """Format static hygiene violations from an `audit_lean_source` report."""
    eff_max_decl = max_proof_thm_loc if max_decl_loc is None else max_decl_loc
    errs: list[str] = []
    loc = int(rep["loc"])  # type: ignore[arg-type]
    if rep["over_loc"]:
        if base_loc is not None and base_loc >= max_loc:
            if loc > base_loc:
                errs.append(
                    f"{rel_path}: grandfathered file grew {base_loc} -> {loc} LOC (>= {max_loc})"
                )
        else:
            errs.append(f"{rel_path}: {loc} LOC >= {max_loc}")

    long_lines: list[dict[str, object]] = rep["long_lines"]  # type: ignore[assignment]
    if changed_lines is not None and not is_proof_shard_path(rel_path):
        active_long_lines = [
            ln_info for ln_info in long_lines if int(ln_info["line"]) in changed_lines
        ]
    else:
        active_long_lines = long_lines
    for ln_info in (active_long_lines[:1] if first_long_line_only else active_long_lines):
        errs.append(f"{rel_path}:{ln_info['line']}: line width {ln_info['cols']} > {max_col}")

    errs.extend(
        f"{rel_path}:{ln}: merge conflict marker"
        for ln in rep["conflicts"]  # type: ignore[attr-defined]
    )
    bad_all: list[int] = rep["bad_import_all"]  # type: ignore[assignment]
    errs.extend(f"{rel_path}:{ln}: forbidden `import all`" for ln in bad_all)
    errs.extend(
        f"{rel_path}:{ln}: forbidden `import all` in Proof/ shard"
        for ln in rep["proof_import_all"] if ln not in bad_all  # type: ignore[attr-defined]
    )
    errs.extend(
        f"{rel_path}:{hit['line']}: {banned_label} in `{hit['text']}`"
        for hit in rep["banned_hits"]  # type: ignore[attr-defined]
    )
    errs.extend(
        f"{rel_path}:{ln}: @[expose] on theorem/lemma"
        for ln in rep["expose_on_thm"]  # type: ignore[attr-defined]
    )
    errs.extend(
        f"{rel_path}:{s['theorem_line']}: theorem/lemma inside file-level "
        f"`@[expose] public section` (line {s['section_line']})"
        for s in rep["proof_expose_section"]  # type: ignore[attr-defined]
    )

    if not is_legacy_full_path(rel_path):
        raw_long_decls = rep.get("long_decls")
        if raw_long_decls is not None:
            is_proof_shard = is_proof_shard_path(rel_path)
            for d in raw_long_decls:  # type: ignore[attr-defined]
                d_kind = str(d["kind"])
                d_name = str(d["name"])
                d_ns = str(d.get("ns", ""))
                d_start = int(d["start_line"])
                d_end = int(d["end_line"])
                d_lines = int(d["lines"])
                if not is_proof_shard and changed_lines is not None:
                    if not any(d_start <= ln <= d_end for ln in changed_lines):
                        continue
                    key = (d_ns, d_kind, d_name)
                    if (
                        base_long_decls is not None
                        and d_name != "<anon>"
                        and key in base_long_decls
                        and base_long_decls[key] > eff_max_decl
                    ):
                        if d_lines > base_long_decls[key]:
                            errs.append(
                                f"{rel_path}:{d_start}: grandfathered {d_kind} `{d_name}` "
                                f"grew {base_long_decls[key]} -> {d_lines} lines "
                                f"(> {eff_max_decl})"
                            )
                        continue
                errs.append(
                    f"{rel_path}:{d_start}: {d_kind} `{d_name}` is "
                    f"{d_lines} lines > {eff_max_decl} (L{d_start}-L{d_end})"
                )
        else:
            errs.extend(
                f"{rel_path}:{t['start_line']}: theorem `{t['name']}` is "
                f"{t['lines']} lines > {max_proof_thm_loc} (L{t['start_line']}-L{t['end_line']})"
                for t in rep["proof_long_theorems"]  # type: ignore[attr-defined]
            )
    return errs


def scan_forbidden_tokens(root: Path) -> list[str]:
    """Scan all tracked/untracked non-Kraken `.lean` files for banned tokens/axioms."""
    excludes = ("Kraken", "Kraken*.lean", "Att2Intel.lean", "Bedrock2C.lean", "bv_decide_qbe")
    hits: list[str] = []
    for rel in list_lean_files(root, excludes=excludes):
        p = root / rel
        if not p.is_file():
            hits.append(f"{rel}: tracked file missing from working tree")
            continue
        raw_txt = p.read_text(encoding="utf-8")
        if not FORBIDDEN_TOKENS_PRE_RE.search(raw_txt):
            continue
        cleaned = strip_lean_code(raw_txt)
        for lineno, line in enumerate(cleaned.splitlines(), 1):
            if BANNED_TOKEN_RE.search(line) or AXIOM_DECL_RE.search(line):
                hits.append(f"{rel}:{lineno}: {line.strip()}")
        for m in BANNED_ATTR_RE.finditer(cleaned):
            hits.append(f"{rel}:{cleaned[: m.start()].count(chr(10)) + 1}: {m.group(0)}")
    return hits


def classify_scope_paths(files: Iterable[str]) -> str:
    """Classify changed paths into `class0`, `x64`, `arm64`, or `full`."""
    items = [ln.strip() for ln in files if ln.strip()]
    if not items:
        return "full"
    if all(
        (not f.endswith(".lean")) and (not FORBIDDEN_CLASS0_RE.match(f)) and CLASS0_RE.fullmatch(f)
        for f in items
    ):
        return "class0"
    lean_files = [f for f in items if f.endswith(".lean")]
    nonlean_files = [f for f in items if not f.endswith(".lean")]
    if (
        lean_files
        and all(X64_LEAN_RE.fullmatch(f) and "Arm64" not in f for f in lean_files)
        and all(X64_NONLEAN_RE.fullmatch(f) for f in nonlean_files)
    ):
        return "x64"
    if (
        lean_files
        and all(
            ARM64_LEAN_RE.fullmatch(f) and "X64" not in f and "Amd64" not in f for f in lean_files
        )
        and all(ARM64_NONLEAN_RE.fullmatch(f) for f in nonlean_files)
    ):
        return "arm64"
    return "full"


def run_preflight_lean_hygiene(root: Path, base: str) -> tuple[int, list[str]]:
    """Run static `.lean` hygiene over files changed since `base` + working tree."""
    changed: set[str] = set()
    cmds = [("diff", "--name-only", "HEAD"), ("ls-files", "--others", "--exclude-standard")]
    base_tree_ref: str | None = None
    if run_git(root, "rev-parse", "--verify", f"{base}^{{commit}}").returncode == 0:
        cmds.insert(0, ("diff", "--name-only", f"{base}...HEAD"))
        mb = run_git(root, "merge-base", base, "HEAD")
        base_tree_ref = mb.stdout.strip() if mb.returncode == 0 else base
    elif run_git(root, "rev-parse", "--verify", "HEAD^{commit}").returncode == 0:
        base_tree_ref = "HEAD"

    for git_args in cmds:
        r = run_git(root, *git_args)
        if r.returncode == 0:
            changed.update(
                ln.strip() for ln in r.stdout.splitlines()
                if ln.strip().endswith(".lean") and not ln.strip().startswith("bv_decide_qbe/")
            )

    changed = {f for f in changed if not f.startswith("archive/")}

    tracked_lean: set[str] | None = None
    tr_res = run_git(root, "ls-files", "-z", "--cached", text=False)
    if tr_res.returncode == 0:
        tracked_lean = {
            b.decode("utf-8")
            for b in tr_res.stdout.split(b"\0")
            if b and b.endswith(b".lean")
        }

    errs: list[str] = []
    for f in sorted(changed):
        p = root / f
        if not p.is_file():
            continue
        text = p.read_text(encoding="utf-8")
        rep = audit_lean_source(
            f, text, max_loc=DEFAULT_MAX_LOC, max_col=DEFAULT_MAX_COL,
            max_proof_thm_loc=DEFAULT_MAX_PROOF_THM_LOC,
            max_decl_loc=DEFAULT_MAX_DECL_LOC,
        )
        base_loc: int | None = None
        changed_lines: set[int] | None = None
        base_long_decls: dict[tuple[str, str, str], int] | None = None
        needs_base = bool(rep["over_loc"] or rep["long_lines"] or rep["long_decls"])
        if needs_base and base_tree_ref is not None:
            res = run_git(root, "show", f"{base_tree_ref}:{f}")
            if res.returncode == 0:
                base_txt = res.stdout
                base_loc = len(base_txt.splitlines())
                if rep["long_lines"] or rep["long_decls"]:
                    d_res = run_git(
                        root, "-c", "core.quotepath=false", "diff", "-U0",
                        "--no-renames", "--src-prefix=a/", "--dst-prefix=b/",
                        base_tree_ref, "--", f,
                    )
                    if d_res.returncode == 0:
                        changed_lines = parse_diff_changed_lines(d_res.stdout).get(f, set())
                    if rep["long_decls"] and not is_legacy_full_path(f):
                        base_rep = audit_lean_source(
                            f, base_txt, max_loc=DEFAULT_MAX_LOC,
                            max_col=DEFAULT_MAX_COL,
                            max_proof_thm_loc=DEFAULT_MAX_PROOF_THM_LOC,
                            max_decl_loc=DEFAULT_MAX_DECL_LOC,
                        )
                        base_long_decls = {}
                        for bd in base_rep["long_decls"]:  # type: ignore[attr-defined]
                            bname = str(bd["name"])
                            if bname == "<anon>":
                                continue
                            bkey = (str(bd.get("ns", "")), str(bd["kind"]), bname)
                            blines = int(bd["lines"])
                            if blines > base_long_decls.get(bkey, 0):
                                base_long_decls[bkey] = blines
        errs.extend(
            collect_hygiene_violations(
                f, rep, base_loc=base_loc, changed_lines=changed_lines,
                base_long_decls=base_long_decls,
            )
        )
        if tracked_lean is not None:
            errs.extend(check_tracked_local_imports(root, f, text, tracked_lean))
    return len(changed), errs


def _cli_main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args:
        print(
            "Usage: lean_imports.py <preflight-hygiene|classify-stdin|scan-forbidden>",
            file=sys.stderr,
        )
        return 2
    cmd = args[0]
    if cmd == "preflight-hygiene":
        base = args[1] if len(args) > 1 else "HEAD~1"
        root = Path(args[2]).resolve() if len(args) > 2 else Path.cwd()
        count, errs = run_preflight_lean_hygiene(root, base)
        if errs:
            print("\n".join(f"FAIL: {e}" for e in errs[:40]), file=sys.stderr)
            return 1
        print(f"preflight .lean hygiene: OK ({count} changed file(s))")
        return 0
    if cmd == "classify-stdin":
        print(classify_scope_paths(sys.stdin))
        return 0
    if cmd == "scan-forbidden":
        hits = scan_forbidden_tokens(Path(args[1]).resolve() if len(args) > 1 else Path.cwd())
        if hits:
            print("\n".join(hits[:50]), file=sys.stderr)
            return 1
        return 0
    print(f"unknown subcommand: {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(_cli_main())
