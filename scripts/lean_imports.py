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

# Stage A: M5, M6, and non-reused M7Plus certs move to LeanQbeLegacy* (Tier 3).
# Keep KissatM7PlusBounds + the 38 KissatM7PlusCert* slices imported by
# KissatM7FidelityCert active until Stage B (standalone KissatFidelity certs).
LEGACY_CERT_DEFAULT = (
    r"^LeanQbe\.T\.(Amd64|Arm64)\."
    r"(Kissat|KissatCorePlus|KissatFull.*|KissatFastSched.*|KissatFast.*"
    r"|KissatPlain.*|KissatM3.*|KissatM4.*|KissatM5.*|KissatM6.*"
    r"|KissatM7Plus(?:Cert|CertLink|Cert(?:1|14|15|18|21|22|4[5-9]|5[0-6]))?)$"
)

LEGACY_CERT_RE = re.compile(LEGACY_CERT_DEFAULT)

DEFAULT_MAX_LOC = 2500
DEFAULT_MAX_COL = 100
DEFAULT_MAX_PROOF_THM_LOC = 450

PROOF_SHARD_PREFIXES: tuple[str, ...] = (
    "LeanQbe/T/Examples/Kissat/Proof/",
    "LeanQbe/T/Examples/Bitblast/Proof/",
)

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
    r"^(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma)\b(?:\s+([^\s:({\[<]+))?"
)
MODIFIER_ONLY_RE = re.compile(
    r"^(?:(?:@\[[^\]]*\]|public|private|protected|noncomputable|unsafe)(?:\s+|$))+$"
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
    r"scoped|meta)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class|"
    r"instance|axiom|opaque|example|macro|macro_rules|syntax|elab|elab_rules|"
    r"declare_syntax_cat|section|namespace|end|open|variable|universe|"
    r"set_option|attribute|mutual|initialize|builtin_initialize|"
    r"register_simp_attr|deriving|#print|#check|#guard|#eval|#reduce)\b"
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
) -> dict[str, object]:
    """Audit a single `.lean` source string for hygiene and P0-5 Proof shard rules."""
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
    in_thm: tuple[str, int, int] | None = None
    last_thm_code_ln = 0

    for idx, raw in enumerate(raw_lines, 1):
        if CONFLICT_RE.match(raw):
            conflicts.append(idx)
        if len(raw) > max_col and not raw.strip().startswith(("--", "/-", '"')):
            long_lines.append({"line": idx, "cols": len(raw)})

        raw_clean = cleaned_lines[idx - 1]
        code = raw_clean.strip()
        indent = len(raw) - len(raw.lstrip())
        is_doc_start = doc_opens[idx - 1]

        if in_thm is not None:
            thm_name, thm_start, thm_indent = in_thm
            # Close theorem before the next top-level command, attribute, or doc comment.
            if indent <= thm_indent and (
                is_doc_start
                or code.startswith("@[")
                or (code and TOP_DECL_RE.match(code))
            ):
                span = last_thm_code_ln - thm_start + 1
                if is_proof_shard and span > max_proof_thm_loc:
                    proof_long_theorems.append(
                        {
                            "name": thm_name,
                            "start_line": thm_start,
                            "end_line": last_thm_code_ln,
                            "lines": span,
                        }
                    )
                in_thm = None

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

        # Track section/namespace/mutual scopes when not inside a theorem body.
        if in_thm is None:
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
        without_attrs = ANY_ATTR_RE.sub("", code).strip()
        m_thm = THM_DECL_RE.match(without_attrs)

        if m_thm:
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
            if in_thm is None:
                in_thm = (m_thm.group(1) or "<anon>", idx, indent)
                last_thm_code_ln = idx
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
            if in_thm is not None:
                last_thm_code_ln = idx

    if in_thm is not None:
        thm_name, thm_start, _ = in_thm
        span = last_thm_code_ln - thm_start + 1
        if is_proof_shard and span > max_proof_thm_loc:
            proof_long_theorems.append(
                {
                    "name": thm_name,
                    "start_line": thm_start,
                    "end_line": last_thm_code_ln,
                    "lines": span,
                }
            )

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
    }
