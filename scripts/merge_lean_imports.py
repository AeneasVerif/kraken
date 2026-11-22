#!/usr/bin/env python3
"""Deterministic 3-way Lean 4 module header import-set merger.

Merges Lean module headers (`module`, `prelude`, `import` / `public import` /
`meta import` / `public meta import` / `import all` lines) via exact 3-way set
algebra while delegating the file body (`set_option autoImplicit false`,
docstrings, declarations) to `git merge-file`.

Privacy firewall rule:
  If one side explicitly downgrades `public import X` -> `import X` while the
  other kept `public import X` (or if two newly added imports disagree on
  visibility), the stricter private `import X` wins (zero firewall regression).

Usage:
  Standalone (e.g. from mq_batch.sh):
    python3 -B scripts/merge_lean_imports.py <base> <ours> <theirs> --out <path>
  Git custom merge driver (%O %A %B, updates %A in place):
    python3 -B scripts/merge_lean_imports.py %O %A %B
  Self-test suite:
    python3 -B scripts/merge_lean_imports.py --self-test
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

IMPORT_LINE_RE = re.compile(
    r"^\s*(?:(public|private)\s+)?(?:(meta)\s+)?import\s+(?:(all)\s+)?"
    r"([A-Za-z_][A-Za-z0-9_'.]*)(?:\s+(--.*))?\s*$"
)


@dataclass(frozen=True)
class ImportEntry:
    """Single parsed Lean import statement."""

    module: str
    is_public: bool
    is_meta: bool
    is_all: bool
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


def _advance_block_comment(raw: str, depth: int) -> int:
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
            depth = _advance_block_comment(raw, depth)
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
            depth = _advance_block_comment(raw, 0)
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


def seen_module_or_import(has_module: bool, seen_import: bool) -> bool:
    """Return True if `module` or any `import` has already been parsed."""
    return has_module or seen_import


def merge_bool_3way(
    base: bool, ours: bool, theirs: bool, *, conflict_value: bool
) -> bool:
    """Merge a boolean header flag with deterministic 3-way semantics."""
    if ours == theirs:
        return ours
    if ours == base:
        return theirs
    if theirs == base:
        return ours
    return conflict_value


def resolve_import_entry(
    base: ImportEntry | None,
    ours: ImportEntry | None,
    theirs: ImportEntry | None,
) -> ImportEntry:
    """Merge attributes of a retained import key `(module, is_meta)`.

    When one side downgrades `public import X` -> `import X` while the other
    keeps `public import X`, or when both newly add `X` with differing
    visibility, keeps the stricter private `import X` (`is_public=False`).
    """
    if ours is not None and theirs is not None:
        if base is not None:
            is_public = merge_bool_3way(
                base.is_public,
                ours.is_public,
                theirs.is_public,
                conflict_value=(ours.is_public and theirs.is_public),
            )
            is_all = merge_bool_3way(
                base.is_all,
                ours.is_all,
                theirs.is_all,
                conflict_value=(ours.is_all or theirs.is_all),
            )
            if ours.comment != base.comment and theirs.comment == base.comment:
                comment = ours.comment
            elif theirs.comment != base.comment and ours.comment == base.comment:
                comment = theirs.comment
            else:
                comment = ours.comment or theirs.comment
        else:
            is_public = ours.is_public and theirs.is_public
            is_all = ours.is_all or theirs.is_all
            comment = ours.comment or theirs.comment
        return ImportEntry(
            module=ours.module,
            is_public=is_public,
            is_meta=ours.is_meta,
            is_all=is_all,
            comment=comment,
        )
    chosen = ours if ours is not None else theirs
    assert chosen is not None
    return chosen


def merge_imports_3way(
    base: ParsedLeanFile, ours: ParsedLeanFile, theirs: ParsedLeanFile
) -> list[ImportEntry]:
    """Compute 3-way import set merge preserving tier grouping & `ours` order."""
    b_keys = set(base.imports)
    o_keys = set(ours.imports)
    t_keys = set(theirs.imports)

    added_ours = o_keys - b_keys
    added_theirs = t_keys - b_keys
    common = o_keys & t_keys
    deleted_by_either = (b_keys - o_keys) | (b_keys - t_keys)
    kept_keys = added_ours | added_theirs | (common - deleted_by_either)

    resolved: dict[tuple[str, bool], ImportEntry] = {
        k: resolve_import_entry(
            base.imports.get(k), ours.imports.get(k), theirs.imports.get(k)
        )
        for k in kept_keys
    }

    ordered_keys: list[tuple[str, bool]] = []
    seen: set[tuple[str, bool]] = set()
    for k in ours.imports:
        if k in resolved:
            ordered_keys.append(k)
            seen.add(k)
    for k in theirs.imports:
        if k in resolved and k not in seen:
            ordered_keys.append(k)
            seen.add(k)

    by_tier: dict[tuple[int, bool, bool], list[ImportEntry]] = {}
    for k in ordered_keys:
        entry = resolved[k]
        by_tier.setdefault(entry.tier, []).append(entry)

    result: list[ImportEntry] = []
    for tier in sorted(by_tier):
        result.extend(by_tier[tier])
    return result


def git_merge_file_text(
    base_txt: str,
    ours_txt: str,
    theirs_txt: str,
    labels: tuple[str, str, str] = ("ours", "base", "theirs"),
) -> tuple[int, str]:
    """Run `git merge-file -p` on three text blobs, returning `(rc, merged)`."""
    if ours_txt == theirs_txt:
        return 0, ours_txt
    if base_txt == ours_txt:
        return 0, theirs_txt
    if base_txt == theirs_txt:
        return 0, ours_txt

    with tempfile.TemporaryDirectory(prefix="lean-merge-") as td:
        tmp = Path(td)
        b_path = tmp / "base"
        o_path = tmp / "ours"
        t_path = tmp / "theirs"
        b_path.write_text(base_txt, encoding="utf-8")
        o_path.write_text(ours_txt, encoding="utf-8")
        t_path.write_text(theirs_txt, encoding="utf-8")
        res = subprocess.run(
            [
                "git",
                "merge-file",
                "-p",
                "-L",
                labels[0],
                "-L",
                labels[1],
                "-L",
                labels[2],
                str(o_path),
                str(b_path),
                str(t_path),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        if res.returncode < 0 or res.returncode >= 128:
            raise RuntimeError(
                f"git merge-file failed (rc={res.returncode}): {res.stderr}"
            )
        return res.returncode, res.stdout


def merge_lean_texts(
    base_txt: str,
    ours_txt: str,
    theirs_txt: str,
    labels: tuple[str, str, str] = ("ours", "base", "theirs"),
) -> tuple[int, str]:
    """Perform 3-way merge of Lean module header imports + `git merge-file` body."""
    b = split_lean_file(base_txt)
    o = split_lean_file(ours_txt)
    t = split_lean_file(theirs_txt)

    if not (b.has_header or o.has_header or t.has_header):
        rc, merged = git_merge_file_text(base_txt, ours_txt, theirs_txt, labels)
        return (1 if rc > 0 else 0), merged

    rc_pre, merged_preamble = git_merge_file_text(
        b.preamble, o.preamble, t.preamble, labels
    )
    rc_body, merged_body = git_merge_file_text(b.body, o.body, t.body, labels)

    has_module = merge_bool_3way(
        b.has_module, o.has_module, t.has_module, conflict_value=True
    )
    has_prelude = merge_bool_3way(
        b.has_prelude, o.has_prelude, t.has_prelude, conflict_value=True
    )
    merged_imports = merge_imports_3way(b, o, t)

    header_parts: list[str] = []
    if merged_preamble:
        header_parts.append(merged_preamble.rstrip("\n"))
    if has_module:
        header_parts.append("module")
    if has_prelude:
        header_parts.append("prelude")

    blank_after_mod = merge_bool_3way(
        b.blank_after_module,
        o.blank_after_module,
        t.blank_after_module,
        conflict_value=(o.blank_after_module or t.blank_after_module),
    )
    if merged_imports:
        if (has_module or has_prelude) and blank_after_mod:
            header_parts.append("")
        for entry in merged_imports:
            header_parts.append(entry.format_line())

    header_text = "\n".join(header_parts)
    if header_text and merged_body:
        if o.sep_blank_lines == t.sep_blank_lines:
            sep_blanks = o.sep_blank_lines
        elif o.sep_blank_lines != b.sep_blank_lines:
            sep_blanks = o.sep_blank_lines
        elif t.sep_blank_lines != b.sep_blank_lines:
            sep_blanks = t.sep_blank_lines
        else:
            sep_blanks = max(o.sep_blank_lines, t.sep_blank_lines)
        out_text = header_text + "\n" * (sep_blanks + 1) + merged_body
    elif header_text:
        out_text = header_text + "\n"
    else:
        out_text = merged_body

    has_conflict = (rc_pre > 0) or (rc_body > 0)
    return (1 if has_conflict else 0), out_text


def _git_show(ref: str, rel_path: str) -> str | None:
    """Return blob text from git if `ref:rel_path` exists locally."""
    res = subprocess.run(
        ["git", "show", f"{ref}:{rel_path}"],
        capture_output=True,
        text=True,
        check=False,
    )
    return res.stdout if res.returncode == 0 else None


def run_self_test() -> int:
    """Run comprehensive standalone and real-world self-tests."""
    # 1. Exact real-world p2a-firewall x p2c-legacy-whales conflict on
    #    LeanQbe/T/Amd64/KissatCorePlus.lean (from git if present, plus inline).
    real_pairs = [
        ("merge/p2a-firewall", "merge/p2c-legacy-whales", f)
        for f in (
            "LeanQbe/T/Amd64/KissatCorePlus.lean",
            "LeanQbe/T/Amd64/Kissat.lean",
            "LeanQbe/T/Arm64/KissatCorePlus.lean",
            "LeanQbe/T/Arm64/Kissat.lean",
        )
    ]
    git_checked = 0
    for r_ours, r_theirs, rel in real_pairs:
        mb = subprocess.run(
            ["git", "merge-base", r_ours, r_theirs],
            capture_output=True,
            text=True,
            check=False,
        )
        if mb.returncode != 0:
            continue
        b_txt = _git_show(mb.stdout.strip(), rel)
        o_txt = _git_show(r_ours, rel)
        t_txt = _git_show(r_theirs, rel)
        if b_txt is None or o_txt is None or t_txt is None:
            continue
        rc, merged = merge_lean_texts(b_txt, o_txt, t_txt)
        assert rc == 0, f"expected clean merge on {rel}, got rc={rc}"
        assert "<<<<<<<" not in merged, f"unexpected conflict markers in {rel}"
        assert "public import LeanQbe.T.MainCert\n" in merged
        assert "meta import LeanQbe.T.MainCert\n" in merged
        assert "MainSplice" not in merged
        assert "import LeanQbe.T.Logic.MemLemmas\n" in merged
        if "CorePlus" in rel:
            assert "import LeanQbe.T.AbiLemmas\n" in merged
            assert "compile_linked_chunks! cpCert" in merged
        else:
            assert "compile_linked_chunks! kissatCert" in merged
        git_checked += 1

    # Always run inline exact KissatCorePlus.lean conflict test too.
    kcp_base = (
        "module\n\n"
        "public import LeanQbe.T.Amd64.TargLemmas\n"
        "public import LeanQbe.T.Examples.Kissat.CorePlusLemmas\n"
        "public import LeanQbe.T.MainSplice\n"
        "import all Kraken.Mem\n"
        "import all Kraken.Separation\n"
        "meta import Lean\n"
        "meta import LeanQbe.T.MainSplice\n"
        "meta import LeanQbe.T.Amd64.Targ\n"
        "meta import LeanQbe.T.Examples.Kissat.Dimacs\n"
        "meta import LeanQbe.T.Examples.Kissat.CorePlus\n\n"
        "set_option autoImplicit false\n\n"
        "splice_module_hints cpHints (x64Target.toIsa) x64LegalTarget coreplusFns\n"
    )
    kcp_ours = (
        "module\n\n"
        "public import LeanQbe.T.Amd64.TargLemmas\n"
        "public import LeanQbe.T.Examples.Kissat.CorePlusLemmas\n"
        "public import LeanQbe.T.MainSplice\n"
        "import LeanQbe.T.Logic.MemLemmas\n"
        "import LeanQbe.T.AbiLemmas\n"
        "import all Kraken.Mem\n"
        "import all Kraken.Separation\n"
        "meta import Lean\n"
        "meta import LeanQbe.T.MainSplice\n"
        "meta import LeanQbe.T.Amd64.Targ\n"
        "meta import LeanQbe.T.Examples.Kissat.Dimacs\n"
        "meta import LeanQbe.T.Examples.Kissat.CorePlus\n\n"
        "set_option autoImplicit false\n\n"
        "splice_module_hints cpHints (x64Target.toIsa) x64LegalTarget coreplusFns\n"
    )
    kcp_theirs = (
        "module\n\n"
        "public import LeanQbe.T.MainCert\n"
        "public import LeanQbe.T.Amd64.TargLemmas\n"
        "public import LeanQbe.T.Examples.Kissat.CorePlusLemmas\n"
        "import all Kraken.Mem\n"
        "import all Kraken.Separation\n"
        "meta import Lean\n"
        "meta import LeanQbe.T.MainCert\n"
        "meta import LeanQbe.T.Amd64.Targ\n"
        "meta import LeanQbe.T.Examples.Kissat.Dimacs\n"
        "meta import LeanQbe.T.Examples.Kissat.CorePlus\n\n"
        "set_option autoImplicit false\n\n"
        "compile_linked_chunks! cpCert x64Target coreplusModule 1\n"
    )
    rc, merged = merge_lean_texts(kcp_base, kcp_ours, kcp_theirs)
    assert rc == 0
    assert "public import LeanQbe.T.MainCert\n" in merged
    assert "meta import LeanQbe.T.MainCert\n" in merged
    assert "MainSplice" not in merged
    assert "import LeanQbe.T.Logic.MemLemmas\n" in merged
    assert "import LeanQbe.T.AbiLemmas\n" in merged
    assert "set_option autoImplicit false\n" in merged
    assert "compile_linked_chunks! cpCert" in merged

    # 2. Privacy firewall downgrade must keep private `import X` either way.
    fw_base = (
        "module\n\n"
        "public import LeanQbe.T.Amd64.Targ\n"
        "public import LeanQbe.T.RegaLemmas\n\n"
        "set_option autoImplicit false\n\n"
        "def f := 1\n"
    )
    fw_ours = (
        "module\n\n"
        "public import LeanQbe.T.Amd64.Targ\n"
        "import LeanQbe.T.RegaLemmas\n"
        "import LeanQbe.T.Logic.MemLemmas\n\n"
        "set_option autoImplicit false\n\n"
        "def f := 1\n"
    )
    fw_theirs = (
        "module\n\n"
        "public import LeanQbe.T.Amd64.Targ\n"
        "public import LeanQbe.T.RegaLemmas\n"
        "public import LeanQbe.T.MainLemmas\n\n"
        "set_option autoImplicit false\n\n"
        "def f := 2\n"
    )
    # Conflict on def f -> test clean header with non-conflicting body first:
    fw_theirs_clean = fw_theirs.replace("def f := 2", "def f := 1\ndef g := 2")
    rc, m_fw1 = merge_lean_texts(fw_base, fw_ours, fw_theirs_clean)
    assert rc == 0
    assert "\nimport LeanQbe.T.RegaLemmas\n" in m_fw1
    assert "public import LeanQbe.T.RegaLemmas" not in m_fw1
    assert "\npublic import LeanQbe.T.MainLemmas\n" in m_fw1
    assert "\nimport LeanQbe.T.Logic.MemLemmas\n" in m_fw1
    # Symmetric swap (ours kept public, theirs downgraded):
    rc, m_fw2 = merge_lean_texts(fw_base, fw_theirs_clean, fw_ours)
    assert rc == 0
    assert "\nimport LeanQbe.T.RegaLemmas\n" in m_fw2
    assert "public import LeanQbe.T.RegaLemmas" not in m_fw2

    # 3. Both sides add same module with conflicting visibility -> private wins.
    add_base = "module\n\nset_option autoImplicit false\n"
    add_ours = "module\n\npublic import Foo.Bar\n\nset_option autoImplicit false\n"
    add_theirs = "module\n\nimport Foo.Bar\n\nset_option autoImplicit false\n"
    rc, m_add = merge_lean_texts(add_base, add_ours, add_theirs)
    assert rc == 0
    assert "\nimport Foo.Bar\n" in m_add
    assert "public import Foo.Bar" not in m_add
    assert "set_option autoImplicit false\n" in m_add

    # 4. Real body conflict returns rc=1 and preserves clean header + markers.
    fw_ours_conf = fw_ours.replace("def f := 1", "def f := 10")
    rc, m_conf = merge_lean_texts(fw_base, fw_ours_conf, fw_theirs)
    assert rc == 1
    assert "<<<<<<<" in m_conf and ">>>>>>>" in m_conf
    assert "\nimport LeanQbe.T.RegaLemmas\n" in m_conf
    assert "public import LeanQbe.T.RegaLemmas" not in m_conf

    # 5. Tightly packed header (no blank lines, KissatFull style) preserved.
    tight_b = "module\npublic import A\nset_option autoImplicit false\ndef x := 1\n"
    tight_o = (
        "module\npublic import A\nimport B\n"
        "set_option autoImplicit false\ndef x := 1\n"
    )
    tight_t = (
        "module\npublic import A\npublic import C\n"
        "set_option autoImplicit false\ndef x := 1\n"
    )
    rc, m_tight = merge_lean_texts(tight_b, tight_o, tight_t)
    assert rc == 0
    assert m_tight == (
        "module\npublic import A\npublic import C\nimport B\n"
        "set_option autoImplicit false\ndef x := 1\n"
    )

    # 6. Multi-phase same-module (public import X + meta import X) & import all.
    mp_b = "module\n\npublic import X\nimport all Y\nmeta import X\n\ndef z := 0\n"
    mp_o = (
        "module\n\nimport X\nimport all Y\nmeta import X\n\n"
        "set_option autoImplicit false\ndef z := 0\n"
    )
    mp_t = (
        "module\n\npublic import X\nimport Y\nmeta import X\nmeta import Z\n\n"
        "def z := 0\n"
    )
    rc, m_mp = merge_lean_texts(mp_b, mp_o, mp_t)
    assert rc == 0
    assert "\nimport X\n" in m_mp
    assert "public import X" not in m_mp
    assert "\nimport Y\n" in m_mp
    assert "import all Y" not in m_mp
    assert "\nmeta import X\n" in m_mp
    assert "\nmeta import Z\n" in m_mp
    assert "set_option autoImplicit false\n" in m_mp

    # 7. CLI subprocess (--out & exit 1) + git merge driver end-to-end test.
    with tempfile.TemporaryDirectory(prefix="lean-driver-test-") as td:
        tmp = Path(td)
        b_f, o_f, t_f, out_f = (
            tmp / "b.lean",
            tmp / "o.lean",
            tmp / "t.lean",
            tmp / "out.lean",
        )
        b_f.write_text(kcp_base, encoding="utf-8")
        o_f.write_text(kcp_ours, encoding="utf-8")
        t_f.write_text(kcp_theirs, encoding="utf-8")
        cli_ok = subprocess.run(
            [
                sys.executable,
                "-B",
                str(Path(__file__).resolve()),
                str(b_f),
                str(o_f),
                str(t_f),
                "--out",
                str(out_f),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        assert cli_ok.returncode == 0
        assert "public import LeanQbe.T.MainCert\n" in out_f.read_text(encoding="utf-8")

        b_f.write_text(fw_base, encoding="utf-8")
        o_f.write_text(fw_ours_conf, encoding="utf-8")
        t_f.write_text(fw_theirs, encoding="utf-8")
        cli_fail = subprocess.run(
            [
                sys.executable,
                "-B",
                str(Path(__file__).resolve()),
                str(b_f),
                str(o_f),
                str(t_f),
                "--out",
                str(out_f),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        assert cli_fail.returncode == 1
        assert "<<<<<<<" in out_f.read_text(encoding="utf-8")

        repo = tmp / "repo"
        repo.mkdir()

        def git(*args: str) -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                ["git", "-C", str(repo), *args],
                capture_output=True,
                text=True,
                check=True,
            )

        git("init", "-q")
        git("config", "user.email", "test@example.com")
        git("config", "user.name", "Test")
        git(
            "config",
            "merge.lean-imports.driver",
            f"{sys.executable} -B {Path(__file__).resolve()} %O %A %B",
        )
        (repo / ".gitattributes").write_text(
            "*.lean merge=lean-imports\n", encoding="utf-8"
        )
        (repo / "KissatCorePlus.lean").write_text(kcp_base, encoding="utf-8")
        git("add", ".gitattributes", "KissatCorePlus.lean")
        git("commit", "-qm", "base")
        git("checkout", "-qb", "side-theirs")
        (repo / "KissatCorePlus.lean").write_text(kcp_theirs, encoding="utf-8")
        git("commit", "-qam", "theirs")
        main_br = "master" if _branch_exists(repo, "master") else "main"
        git("checkout", "-q", main_br)
        (repo / "KissatCorePlus.lean").write_text(kcp_ours, encoding="utf-8")
        git("commit", "-qam", "ours")
        git("merge", "-q", "--no-edit", "side-theirs")
        got = (repo / "KissatCorePlus.lean").read_text(encoding="utf-8")
        assert "public import LeanQbe.T.MainCert\n" in got
        assert "import LeanQbe.T.Logic.MemLemmas\n" in got
        assert "MainSplice" not in got
        assert "compile_linked_chunks! cpCert" in got

    print(
        f"merge_lean_imports --self-test: ALL PASSED "
        f"(7 synthetic/CLI/driver + {git_checked} live git branch conflict checks)"
    )
    return 0


def _branch_exists(repo: Path, name: str) -> bool:
    """Return True if local branch `name` exists in `repo`."""
    res = subprocess.run(
        ["git", "-C", str(repo), "show-ref", "--verify", f"refs/heads/{name}"],
        capture_output=True,
        check=False,
    )
    return res.returncode == 0


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for standalone and git-driver 3-way Lean import merges."""
    ap = argparse.ArgumentParser(
        description="Deterministic 3-way Lean header import-set merger."
    )
    ap.add_argument(
        "paths",
        nargs="*",
        help="<base> <ours> <theirs> (and optional git driver %%P path)",
    )
    ap.add_argument(
        "--out",
        "-o",
        default=None,
        help="Output path (`-` for stdout; default overwrites <ours> in place).",
    )
    ap.add_argument(
        "--stdout",
        "-p",
        action="store_true",
        help="Write merged output to stdout instead of updating <ours>.",
    )
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="Run built-in unit and real-world conflict self-tests.",
    )
    args = ap.parse_args(argv)

    if args.self_test:
        return run_self_test()

    if len(args.paths) < 3 or len(args.paths) > 4:
        ap.error("expected <base> <ours> <theirs> (or --self-test)")

    base_p, ours_p, theirs_p = (Path(p) for p in args.paths[:3])
    label = args.paths[3] if len(args.paths) == 4 else str(ours_p)
    rc, merged = merge_lean_texts(
        base_p.read_text(encoding="utf-8"),
        ours_p.read_text(encoding="utf-8"),
        theirs_p.read_text(encoding="utf-8"),
        labels=(f"ours:{label}", "base", f"theirs:{label}"),
    )

    if args.stdout or args.out == "-":
        sys.stdout.write(merged)
    elif args.out is not None:
        out_p = Path(args.out)
        out_p.parent.mkdir(parents=True, exist_ok=True)
        out_p.write_text(merged, encoding="utf-8")
    else:
        ours_p.write_text(merged, encoding="utf-8")
    return rc


if __name__ == "__main__":
    sys.exit(main())
