#!/usr/bin/env python3
"""Extract spliced Kissat C0 functions (fidelity|m8opt|plain|m7fidelity|m7plus|m7|m6|m5) to C99."""
import argparse
import hashlib
import io
import json
import os
import pathlib
import re
import subprocess
import sys
import tarfile
import tempfile

SKIP_SUFFIXES = ("Lemmas", "Proof", "Spec", "Arena", "SatNv", "InlB5")
KISSAT_NS = "LeanQbe.T.Examples.Kissat"


def _strip_comments(src):
    return re.sub(r"//[^\n]*", "", re.sub(r"/\*.*?\*/", "", src, flags=re.S))


def _norm_typedef(txt):
    """Canonicalize multi-declarator struct fields so `,` vs `;` layouts compare equal."""
    s = " ".join(txt.split())
    return re.sub(r"\b(u8|u16|u32|u64|i8|i16|i32|i64|KissatDimacs)\s+([^;{}]+);",
                  lambda m: " ".join(f"{m.group(1)} {v.strip()};"
                                     for v in m.group(2).split(",")), s)


def parse_c0_block(src, bid):
    """Parse #defines, typedefs, statics, and function definitions from one kissat_c0! block."""
    lines = _strip_comments(src).splitlines()
    macros, tdefs, statics, fns = {}, [], [], []
    i, n = 0, len(lines)
    while i < n:
        s = lines[i].strip()
        if not s:
            i += 1
        elif s.startswith("#define"):
            parts = s.split(None, 2)
            macros[parts[1]] = parts[2] if len(parts) > 2 else ""
            i += 1
        elif s.startswith("extern "):
            while not lines[i].strip().endswith(";") and i + 1 < n:
                i += 1
            i += 1
        else:
            chunk = [lines[i]]
            depth = lines[i].count("{") - lines[i].count("}")
            brace = "{" in lines[i]
            while i + 1 < n and ((not brace) or depth > 0):
                if not brace and lines[i].strip().endswith(";"):
                    break
                i += 1
                chunk.append(lines[i])
                brace = brace or ("{" in lines[i])
                depth += lines[i].count("{") - lines[i].count("}")
            text = "\n".join(chunk)
            if s.startswith("typedef "):
                m = re.search(r"(\w+)\s*;\s*$", text)
                tdefs.append((m.group(1) if m else text, text))
            elif brace and not s.startswith("static "):
                sig = text[:text.index("{")].strip()
                m = re.match(r"^(.*?)\b([A-Za-z_]\w*)\s*\((.*)\)$", sig, re.S)
                if not m:
                    raise ValueError(f"Unparsed C0 signature in {bid}: {text[:80]!r}")
                fns.append({
                    "block": bid, "orig": m.group(2), "name": m.group(2),
                    "ret": m.group(1).strip(), "params": " ".join(m.group(3).split()),
                    "text": text, "macros": macros, "tdefs": tdefs, "statics": statics,
                })
            else:
                statics.append(text)
            i += 1
    return fns


def _ns_at(txt, pos):
    ns = KISSAT_NS
    for m in re.finditer(r"^namespace\s+(LeanQbe\.\S+)", txt[:pos], re.M):
        ns = m.group(1)
    return ns


def load_kissat(kdir):
    """Scan Kissat/*.lean for kissat_c0! blocks, Fn aliases, and List Fn splice definitions."""
    body_map, fn_envs, list_envs, before_envs, rename_maps, files = {}, {}, {}, {}, {}, []
    for fp in sorted(kdir.glob("*.lean")):
        if any(x in fp.name for x in SKIP_SUFFIXES):
            continue
        txt = fp.read_text()
        opens = [KISSAT_NS] + [
            t for m in re.finditer(r"^open\s+(.*)$", txt, re.M)
            for t in m.group(1).split() if t.startswith(KISSAT_NS)
        ]
        files.append((fp.name, txt, opens))
        for m in re.finditer(r'kissat_c0!\s+(\w+)\s+"(.*?)\n"', txt, re.S):
            ns, pfx = _ns_at(txt, m.start()), m.group(1)
            fns = parse_c0_block(m.group(2), f"{fp.name}:{pfx}")
            for f in fns:
                body_map[f"{ns}.{f['orig']}_body"] = f
                fn_envs.setdefault(f"{ns}.{f['orig']}", {**f, "name": f["orig"]})
            list_envs[f"{ns}.{pfx}_fns"] = fns
    ren_map_re = re.compile(
        r"^def\s+(\w+)\s*:\s*Sym\s*→\s*Sym\s*(.*?)"
        r"(?=\n(?:def|theorem|private|end|kissat_c0!|/-|\Z))", re.M | re.S)
    ren_body_re = re.compile(
        r"^def\s+(\w+)\s*:\s*Func\b[^:=]*:=\s*renameFuncCalls\s+(\w+)\s+([A-Za-z0-9_.]+_body)",
        re.M | re.S)
    fn_re = re.compile(
        r'def\s+(\w+)\s*:\s*Fn\s*:=\s*⟨"([^"]+)"[^⟩]*?([A-Za-z0-9_.]+)⟩', re.S)
    fn_rec_re = re.compile(
        r'def\s+(\w+)\s*:\s*Fn\s*:=\s*\{\s*name\s*:=\s*"([^"]+)"[^{}]*?'
        r'\bbody\s*:=\s*([A-Za-z0-9_.]+)\s*\}', re.S)
    fn_alias_re = re.compile(
        r"^\s*(?:private\s+|protected\s+)?(?:def|abbrev)\s+([A-Za-z0-9_]+)\s*:\s*Fn\s*:=\s*"
        r"([A-Za-z0-9_.]+)(?:\s*--[^\n]*)?$", re.M)
    list_re = re.compile(
        r"^def\s+(\w+)\s*:\s*List\s+Fn\s*:=\s*(.*?)"
        r"(?=\n(?:def|theorem|private|end|kissat_c0!|/-|\Z))", re.M | re.S)
    before_re = re.compile(
        r"^def\s+(\w+)\s*:\s*List\s*\(Sym\s*×\s*List\s+Fn\)\s*:=\s*(.*?)"
        r"(?=\n(?:def|theorem|private|end|kissat_c0!|/-|\Z))", re.M | re.S)

    def _resolve_body(bref, ns, opens):
        for c in (bref, f"{ns}.{bref}", *(f"{o}.{bref}" for o in opens), f"{KISSAT_NS}.{bref}"):
            if c in body_map:
                return body_map[c]
        return None

    for _, txt, opens in files:
        for m in ren_map_re.finditer(txt):
            ns = _ns_at(txt, m.start())
            pairs = re.findall(r'\|\s*"([^"]+)"\s*=>\s*"([^"]+)"', m.group(2))
            rename_maps[f"{ns}.{m.group(1)}"] = pairs
    for _, txt, opens in files:
        for m in ren_body_re.finditer(txt):
            ns, bname, rname, bref = _ns_at(txt, m.start()), m.group(1), m.group(2), m.group(3)
            base = _resolve_body(bref, ns, opens)
            pairs = rename_maps.get(f"{ns}.{rname}", [])
            if base is not None:
                code = base["text"]
                for old, new in pairs:
                    code = re.sub(rf"\b{re.escape(old)}(?=\s*\()", new, code)
                body_map[f"{ns}.{bname}"] = {**base, "text": code}
    alias_defs = []
    for _, txt, opens in files:
        for m in (*fn_re.finditer(txt), *fn_rec_re.finditer(txt)):
            ns, fvar, exp, bref = _ns_at(txt, m.start()), m.group(1), m.group(2), m.group(3)
            base = _resolve_body(bref, ns, opens)
            if base is not None:
                fn_envs[f"{ns}.{fvar}"] = {**base, "name": exp}
        for m in fn_alias_re.finditer(txt):
            alias_defs.append((_ns_at(txt, m.start()), opens, m.group(1), m.group(2)))
        for m in list_re.finditer(txt):
            ns = _ns_at(txt, m.start())
            list_envs[f"{ns}.{m.group(1)}"] = (ns, opens, m.group(2))
        for m in before_re.finditer(txt):
            ns = _ns_at(txt, m.start())
            before_envs[f"{ns}.{m.group(1)}"] = (ns, opens, m.group(2))
    for _ in range(4):
        progressed = False
        for ns, opens, lhs, rhs in alias_defs:
            q_lhs = f"{ns}.{lhs}"
            if q_lhs in fn_envs:
                continue
            for c in (rhs, f"{ns}.{rhs}", *(f"{o}.{rhs}" for o in opens), f"{KISSAT_NS}.{rhs}"):
                if c in fn_envs:
                    fn_envs[q_lhs] = fn_envs[c]
                    progressed = True
                    break
        if not progressed:
            break
    return fn_envs, list_envs, before_envs


def eval_befores(qname, before_envs, fn_envs, cache, list_eval=None):
    """Evaluate a List (Sym × List Fn) expression built from ++ and [("anchor", hs)].

    `hs` is a `++`-chain of `[fn, ...]` literals and List Fn names; names are
    resolved via `list_eval(name, ns, opens)`.
    """
    tok_pat = r'\+\+|"[^"]*"|[()\[\],]|[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*'

    def res(nm, ns, opens, env):
        for c in (nm, f"{ns}.{nm}", *(f"{o}.{nm}" for o in opens), f"{KISSAT_NS}.{nm}"):
            if c in env:
                return c, env[c]
        raise KeyError(f"Unresolved symbol {nm!r} in {ns}")

    def eval_nm(nm, ns, opens):
        qn, v = res(nm, ns, opens, before_envs)
        if qn not in cache:
            cache[qn] = eval_expr(*v)
        return cache[qn]

    def eval_expr(ns, opens, expr):
        toks = re.findall(tok_pat, expr)
        pos = [0]
        pk = lambda: toks[pos[0]] if pos[0] < len(toks) else None
        nx = lambda: (pk(), pos.__setitem__(0, pos[0] + 1))[0]

        def parse_term():
            if pk() == "[":
                nx()
                val = []
                while pk() != "]":
                    assert nx() == "("
                    anchor = nx().strip('"')
                    assert nx() == ","
                    hs = []
                    while True:
                        if pk() == "[":
                            nx()
                            while pk() != "]":
                                hs.append(res(nx(), ns, opens, fn_envs)[1])
                                if pk() == ",":
                                    nx()
                            nx()  # ']'
                        else:
                            if list_eval is None:
                                raise KeyError(f"List-valued helpers need list_eval in {ns}")
                            hs.extend(list_eval(nx(), ns, opens))
                        if pk() != "++":
                            break
                        nx()
                    assert nx() == ")"
                    val.append((anchor, hs))
                    if pk() == ",":
                        nx()
                nx()  # ']'
                return val
            return eval_nm(nx(), ns, opens)

        val = parse_term()
        while pk() == "++":
            nx()
            val = val + parse_term()
        return val

    return eval_nm(qname, KISSAT_NS, [])


def eval_list(qname, list_envs, fn_envs, cache, before_envs=None):
    """Evaluate a Lean List Fn splice expression built from ++, .take, .drop, splice/patch, [...]."""
    tok_pat = (r"\+\+|\.take\b|\.drop\b|[()\[\],]|"
               r"[A-Za-z0-9_]+(?:\.(?!take\b|drop\b)[A-Za-z0-9_]+)*")
    bcache = {}

    def res(nm, ns, opens, env):
        cands = [nm, f"{ns}.{nm}", *(f"{o}.{nm}" for o in opens), f"{KISSAT_NS}.{nm}"]
        for c in cands:
            if c in env:
                return c, env[c]
        raise KeyError(f"Unresolved symbol {nm!r} in {ns}")

    def eval_nm(nm, ns, opens):
        qn, v = res(nm, ns, opens, list_envs)
        if qn not in cache:
            cache[qn] = v if isinstance(v, list) else eval_expr(*v)
        return cache[qn]

    def eval_expr(ns, opens, expr):
        toks = re.findall(tok_pat, expr)
        pos = [0]
        pk = lambda: toks[pos[0]] if pos[0] < len(toks) else None
        nx = lambda: (pk(), pos.__setitem__(0, pos[0] + 1))[0]

        def parse_term():
            if pk() == "(":
                nx()
                val = parse_expr()
                assert nx() == ")"
            elif pk() == "[":
                nx()
                val = []
                while pk() != "]":
                    val.append(res(nx(), ns, opens, fn_envs)[1])
                    if pk() == ",":
                        nx()
                nx()
            elif pk() in (
                "mpSpliceFns", "spliceFns",
                "FullM7Splice.mpSpliceFns", "FullM7Splice.spliceFns",
                "PatchModule.spliceFns",
            ):
                nx()
                repls = parse_term()
                base = parse_term()
                rmap = {f["name"]: f for f in repls}
                val = [rmap.get(f["name"], f) for f in base]
            elif pk() in (
                "mfPatchFns", "patchFns", "fidPatchFns",
                "FullM7Splice.mfPatchFns", "FullM7Splice.patchFns",
                "PatchModule.patchFns",
            ):
                nx()
                repls = parse_term()
                if pk() == "[":
                    depth, btoks = 0, []
                    while pk() is not None:
                        t = nx()
                        btoks.append(t)
                        depth += (t == "[") - (t == "]")
                        if depth == 0:
                            break
                    assert depth == 0, f"unclosed '[' in befores for {ns}"
                    if btoks == ["[", "]"]:
                        befores = []
                    else:
                        benv = {**(before_envs or {}), "__inline__": (ns, opens, " ".join(btoks))}
                        befores = eval_befores("__inline__", benv, fn_envs, dict(bcache), eval_nm)
                else:
                    bq, _ = res(nx(), ns, opens, before_envs or {})
                    befores = eval_befores(bq, before_envs or {}, fn_envs, bcache, eval_nm)
                base = parse_term()
                rmap = {f["name"]: f for f in repls}
                bmap = {}
                for anchor, hs in befores:
                    bmap.setdefault(anchor, []).extend(hs)
                val = []
                for f in base:
                    val.extend(bmap.get(f["name"], ()))
                    val.append(rmap.get(f["name"], f))
            else:
                val = eval_nm(nx(), ns, opens)
            while pk() in (".take", ".drop"):
                op, n = nx(), int(nx())
                val = val[:n] if op == ".take" else val[n:]
            return val

        def parse_expr():
            val = parse_term()
            while pk() == "++":
                nx()
                val = val + parse_term()
            return val

        return parse_expr()

    return eval_nm(qname, KISSAT_NS, [])


def _prep_body(f):
    code = f["text"]
    if f["name"] != f["orig"]:
        code = re.sub(rf"\b{re.escape(f['orig'])}(?=\s*\()", f["name"], code, count=1)
    bi = code.index("{")
    body = code[bi + 1:]
    if f["params"] not in ("", "void"):
        ps = [m.group(1) for p in f["params"].split(",")
              for m in [re.search(r"([A-Za-z_]\w*)\s*$", p)] if m]
        unused = [p for p in ps if not re.search(rf"\b{re.escape(p)}\b", body)]
        if unused:
            code = code[:bi + 1] + " " + " ".join(f"(void){p};" for p in unused) + body
    return code


def _collect_decls(fns):
    """Deduplicate typedefs (with block alias disambiguation), statics, and forward prototypes."""
    tdefs_out, statics_out, seen_td, seen_st, td_alias = [], [], {}, set(), {}
    for f in fns:
        for nm, txt in f["tdefs"]:
            norm = _norm_typedef(txt)
            if nm not in seen_td:
                seen_td[nm] = norm
                tdefs_out.append(txt)
            elif seen_td[nm] != norm and (f["block"], nm) not in td_alias:
                alias = f"{nm}__{len(td_alias)}"
                td_alias[(f["block"], nm)] = alias
                tdefs_out.append(re.sub(rf"\b{re.escape(nm)}\s*;\s*$", f"{alias};", txt))
    for f in fns:
        for st in f["statics"]:
            if st not in seen_st:
                seen_st.add(st)
                statics_out.append(st)
    protos_out = [f"{f['ret']} {f['name']}({f['params']});" for f in fns]
    return tdefs_out, statics_out, protos_out, td_alias


def _effective_macros(f, td_alias):
    return {**f["macros"], **{nm: al for (blk, nm), al in td_alias.items() if blk == f["block"]}}


def _emit_fn_block(f, active, td_alias, out):
    """Emit minimal macro #undef/#define delta for `f`, followed by its prepared body."""
    m = _effective_macros(f, td_alias)
    for k in [k for k in active if k not in m or active[k] != m[k]]:
        out.append(f"#undef {k}")
        del active[k]
    for k, v in m.items():
        if k not in active:
            out.append(f"#define {k} {v}")
            active[k] = v
    out += [_prep_body(f), ""]


def emit_c99(fns):
    """Render deduplicated typedefs, prototypes, scoped #defines, and C99 function bodies."""
    tdefs_out, statics_out, protos_out, td_alias = _collect_decls(fns)
    out = ['#include "c0.h"', "", *tdefs_out, *statics_out, "", *protos_out, ""]
    active = {}
    for f in fns:
        _emit_fn_block(f, active, td_alias, out)
    return "\n".join(out)


def _tu_stem(f):
    fname = f["block"].split(":", 1)[0]
    return fname[:-5] if fname.endswith(".lean") else fname


def _tu_filename(f):
    return f"src_{_tu_stem(f)}.c"


def canonical_fn_hash(f, td_alias):
    """Compute canonical SHA256 digest of a C0 function and its effective block context."""
    eff_macros = sorted(_effective_macros(f, td_alias).items())
    tdefs_norm = [
        td_alias[(f["block"], nm)] + ":" + _norm_typedef(txt)
        if (f["block"], nm) in td_alias else _norm_typedef(txt)
        for nm, txt in f["tdefs"]
    ]
    payload = json.dumps(
        {
            "name": f["name"],
            "ret": f["ret"],
            "params": f["params"],
            "body": _prep_body(f),
            "macros": eff_macros,
            "tdefs": tdefs_norm,
            "statics": list(f["statics"]),
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def compute_fn_hashes(fns, td_alias):
    """Return `(c0_sha256, fn_hashes, tu_hashes)` in canonical assembly order."""
    fn_hashes = {}
    tu_pairs = {}
    all_pairs = []
    for f in fns:
        fh = canonical_fn_hash(f, td_alias)
        tu = _tu_filename(f)
        fn_hashes[f["name"]] = {"sha256": fh, "tu": tu, "block": f["block"]}
        tu_pairs.setdefault(tu, []).append([f["name"], fh])
        all_pairs.append([f["name"], fh])
    tu_hashes = {
        tu: {
            "sha256": hashlib.sha256(
                json.dumps(pairs, separators=(",", ":")).encode("utf-8")
            ).hexdigest(),
            "fn_count": len(pairs),
        }
        for tu, pairs in tu_pairs.items()
    }
    c0_sha256 = hashlib.sha256(
        json.dumps(all_pairs, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return c0_sha256, fn_hashes, tu_hashes


def _write_if_changed(path, text):
    """Write `text` only if bytes differ so timestamps remain untouched on no-op extracts."""
    if path.is_file() and path.read_text(encoding="utf-8") == text:
        return False
    path.write_text(text, encoding="utf-8")
    return True


def emit_split_dir(fns, split_dir, target, module_sym):
    """Emit shared `kissat_common.h`, per-source `src_<Stem>.c` TUs, and `c0_fn_hashes.json`."""
    split_dir.mkdir(parents=True, exist_ok=True)
    tdefs_out, _, protos_out, td_alias = _collect_decls(fns)
    c0_sha256, fn_hashes, tu_hashes = compute_fn_hashes(fns, td_alias)

    hdr_lines = [
        "#ifndef KISSAT_C0_COMMON_H",
        "#define KISSAT_C0_COMMON_H",
        '#include "c0.h"',
        "",
        *tdefs_out,
        "",
        *protos_out,
        "",
        "#endif /* KISSAT_C0_COMMON_H */",
        "",
    ]
    written_hdr = _write_if_changed(split_dir / "kissat_common.h", "\n".join(hdr_lines))

    grouped = {}
    for f in fns:
        grouped.setdefault(_tu_filename(f), []).append(f)

    written_tus = []
    for tu_name, tu_fns in grouped.items():
        lines = ['#include "kissat_common.h"', ""]
        seen_tu_st = set()
        tu_statics = []
        for f in tu_fns:
            for st in f["statics"]:
                if st not in seen_tu_st:
                    seen_tu_st.add(st)
                    tu_statics.append(st)
        if tu_statics:
            lines += [*tu_statics, ""]
        active = {}
        for f in tu_fns:
            _emit_fn_block(f, active, td_alias, lines)
        for k in list(active):
            lines.append(f"#undef {k}")
        if active:
            lines.append("")
        if _write_if_changed(split_dir / tu_name, "\n".join(lines) + "\n"):
            written_tus.append(tu_name)

    expected_tus = set(grouped)
    removed_tus = []
    for old_src in sorted(split_dir.glob("src_*.c")):
        if old_src.name not in expected_tus:
            old_src.unlink()
            removed_tus.append(old_src.name)

    hashes_doc = {
        "schema_version": 1,
        "target": target,
        "module": module_sym,
        "fn_count": len(fns),
        "tu_count": len(grouped),
        "c0_sha256": c0_sha256,
        "tus": tu_hashes,
        "functions": fn_hashes,
    }
    _write_if_changed(
        split_dir / "c0_fn_hashes.json",
        json.dumps(hashes_doc, indent=2) + "\n",
    )
    return {
        "written_hdr": written_hdr,
        "written_tus": written_tus,
        "removed_tus": removed_tus,
        "tu_count": len(grouped),
        "c0_sha256": c0_sha256,
        "fn_hashes": fn_hashes,
        "tu_hashes": tu_hashes,
    }


def check_fns(fns, spec, root, imp_mod, open_ns, sym):
    """Assert 1-to-1 ordered name parity against an expected file, 'lean', or CSV list."""
    got = [f["name"] for f in fns]
    if spec == "lean":
        code = (f"import {imp_mod}\nopen {open_ns} in #eval show IO Unit from do\n"
                f"  for f in {sym} do IO.println f.name")
        stage_lp = os.environ.get("STAGE_LEAN_PATH")
        if stage_lp:
            cmd = ["timeout", "60", "lean", "--stdin"]
            env = {**os.environ, "LEAN_PATH": stage_lp}
        else:
            cmd = ["timeout", "60", "lake", "env", "lean", "--stdin"]
            env = None
        r = subprocess.run(cmd, cwd=root, env=env, input=code, text=True, capture_output=True)
        if r.returncode != 0:
            sys.exit(f"ERROR: Lean check failed:\n{r.stderr or r.stdout}")
        exp = [l.strip() for l in r.stdout.splitlines() if l.strip()]
    elif pathlib.Path(spec).is_file():
        exp = [l.split()[0] for l in pathlib.Path(spec).read_text().splitlines()
               if l.strip() and not l.startswith(("COUNT=", "#"))]
    else:
        exp = [s.strip() for s in spec.split(",") if s.strip()]
    if got != exp:
        sys.exit(f"ERROR: fn parity mismatch (got {len(got)} vs exp {len(exp)})")


BASE_TARGET_SPECS = {
    "plain": ("Plain", "Plain", "plainFns"),
    "fidelity-step7": ("FullFidelityAssemblyStep7", "FullFidelityAssemblyStep7", "fidStep7Fns"),
    "fidelity-step6": ("FullFidelityAssembly", "FullFidelityAssembly", "fidFns"),
    "fidelity-c0": ("FullFidelityC0Assembly", "FullFidelityC0Assembly", "fidC0Fns"),
    "m8opt": ("FullM8OptAssembly", "FullM8OptAssembly", "m8OptFns"),
    "opt": ("FullM8OptAssembly", "FullM8OptAssembly", "m8OptFns"),
    "m8": ("FullM8OptAssembly", "FullM8OptAssembly", "m8OptFns"),
    "m5": ("FullM5", "FullM5", "m5Fns"),
    "m6": ("FullM6", "FullM6", "m6Fns"),
    "m7": ("FullM7", "FullM7", "m7Fns"),
    "m7plus": ("FullM7PlusAssembly", "FullM7Plus", "m7PlusFns"),
    "m7fidelity": ("FullM7FidelityAssembly", "FullM7Fidelity", "m7FidelityFns"),
    "m7plus-memshrink": (
        "FullM7MemShrinkAssembly", "FullM7MemShrinkV5", "m7PlusMemShrinkFns"
    ),
    "m7fidelity-memshrink": (
        "FullM7MemShrinkAssembly", "FullM7MemShrinkV5", "m7FidelityMemShrinkFns"
    ),
}

ALL_TARGET_CHOICES = [
    "plain", "fidelity", "fid", "fidelity-step7", "fidelity-step6", "fidelity-c0",
    "m8opt", "opt", "m8", "m5", "m6", "m7", "m7plus", "m7fidelity",
    "m7plus-memshrink", "m7fidelity-memshrink",
]


def resolve_target_spec(kdir, target):
    """Resolve CLI target name to `(file_mod, ns_mod, fn_list_sym)` in `kdir`."""
    if target in ("fidelity", "fid"):
        if (kdir / "FullFidelityAssemblyStep7.lean").is_file():
            return BASE_TARGET_SPECS["fidelity-step7"]
        return BASE_TARGET_SPECS["fidelity-step6"]
    return BASE_TARGET_SPECS[target]


def default_target_for_kdir(kdir):
    """Select the highest landed fidelity target in `kdir`."""
    if ((kdir / "FullFidelityAssemblyStep7.lean").is_file()
            or (kdir / "FullFidelityAssembly.lean").is_file()):
        return "fidelity"
    if (kdir / "FullM7FidelityAssembly.lean").is_file():
        return "m7fidelity"
    return "m5"


def load_fns_for_target(kdir, target):
    """Load and evaluate the spliced C0 function list for `target` under `kdir`."""
    file_mod, ns_mod, sym = resolve_target_spec(kdir, target)
    if not (kdir / f"{file_mod}.lean").exists():
        raise FileNotFoundError(
            f"{kdir / f'{file_mod}.lean'} not found (--target {target} not landed yet)"
        )
    fn_envs, list_envs, before_envs = load_kissat(kdir)
    fns = eval_list(f"{ns_mod}.{sym}", list_envs, fn_envs, {}, before_envs)
    return fns, file_mod, ns_mod, sym


def _extract_git_kissat_tree(root, base_rev, dst_dir):
    r = subprocess.run(
        [
            "git", "-C", str(root), "archive", "--format=tar", base_rev, "--",
            "LeanQbe/T/Examples/Kissat",
        ],
        capture_output=True,
    )
    if r.returncode != 0:
        err = r.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git archive {base_rev} failed: {err}")
    with tarfile.open(fileobj=io.BytesIO(r.stdout), mode="r:") as tf:
        for member in tf.getmembers():
            mp = pathlib.PurePosixPath(member.name)
            if mp.is_absolute() or ".." in mp.parts:
                raise RuntimeError(f"unsafe path in git archive: {member.name}")
        extract_kw = {"filter": "data"} if sys.version_info >= (3, 12) else {}
        tf.extractall(dst_dir, **extract_kw)
    return dst_dir / "LeanQbe/T/Examples/Kissat"


def diff_against_base(cur_fns, root, target, base_rev):
    """Compare current extracted C0 functions against git `base_rev`."""
    _, _, _, cur_td_alias = _collect_decls(cur_fns)
    cur_sha, cur_hashes, _ = compute_fn_hashes(cur_fns, cur_td_alias)
    with tempfile.TemporaryDirectory(prefix="c0d-diffbase-") as td:
        base_kdir = _extract_git_kissat_tree(root, base_rev, pathlib.Path(td))
        base_fns, _, _, _ = load_fns_for_target(base_kdir, target)
    _, _, _, base_td_alias = _collect_decls(base_fns)
    base_sha, base_hashes, _ = compute_fn_hashes(base_fns, base_td_alias)

    added_fns = [f["name"] for f in cur_fns if f["name"] not in base_hashes]
    modified_fns = [
        f["name"]
        for f in cur_fns
        if f["name"] in base_hashes
        and cur_hashes[f["name"]]["sha256"] != base_hashes[f["name"]]["sha256"]
    ]
    cur_names = set(cur_hashes)
    removed_fns = [name for name in base_hashes if name not in cur_names]
    changed_fns = modified_fns + added_fns
    changed_tus = sorted({
        *(cur_hashes[nm]["tu"] for nm in changed_fns),
        *(base_hashes[nm]["tu"] for nm in removed_fns),
    })
    unchanged = (cur_sha == base_sha and not changed_fns and not removed_fns)
    return {
        "schema_version": 1,
        "base_rev": base_rev,
        "target": target,
        "unchanged": unchanged,
        "cur_c0_sha256": cur_sha,
        "base_c0_sha256": base_sha,
        "cur_fn_count": len(cur_fns),
        "base_fn_count": len(base_fns),
        "changed_fns": changed_fns,
        "modified_fns": modified_fns,
        "added_fns": added_fns,
        "removed_fns": removed_fns,
        "changed_tus": changed_tus,
    }


def main():
    root = pathlib.Path(__file__).resolve().parents[2]
    kdir = root / "LeanQbe/T/Examples/Kissat"
    default_target = default_target_for_kdir(kdir)
    ap = argparse.ArgumentParser(description="Extract spliced Kissat C0 functions to C99.")
    ap.add_argument("--target", choices=ALL_TARGET_CHOICES, default=default_target)
    ap.add_argument("--out", default=None, help="Single-TU C99 output file")
    ap.add_argument(
        "--split-dir", default=None,
        help="Directory for kissat_common.h + per-file src_*.c TUs",
    )
    ap.add_argument(
        "--check-fns", default=None,
        help="Assert fn parity against file, 'lean', or CSV",
    )
    ap.add_argument(
        "--diff-base", default=None,
        help="Compare extracted C0 functions against git revision",
    )
    ap.add_argument("--diff-json", default=None, help="Write per-function diff summary JSON")
    args = ap.parse_args()
    if not args.out and not args.split_dir and not args.diff_base:
        ap.error("specify at least one of --out, --split-dir, or --diff-base")

    try:
        fns, file_mod, ns_mod, sym = load_fns_for_target(kdir, args.target)
    except FileNotFoundError as exc:
        sys.exit(f"ERROR: {exc}")

    if args.check_fns:
        check_fns(
            fns, args.check_fns, root,
            f"{KISSAT_NS}.{file_mod}", f"{KISSAT_NS}.{ns_mod}", sym,
        )

    if args.out:
        out = pathlib.Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(emit_c99(fns), encoding="utf-8")
        print(f"Extracted {len(fns)} functions ({args.target}, {ns_mod}.{sym}) -> {out}")

    if args.split_dir:
        split_info = emit_split_dir(
            fns, pathlib.Path(args.split_dir), args.target, f"{ns_mod}.{sym}",
        )
        print(
            f"Split {len(fns)} fns ({args.target}, {ns_mod}.{sym}) across "
            f"{split_info['tu_count']} TUs -> {args.split_dir} "
            f"(hdr_changed={int(split_info['written_hdr'])}, "
            f"tus_written={len(split_info['written_tus'])}, "
            f"removed={len(split_info['removed_tus'])}, "
            f"sha256={split_info['c0_sha256'][:12]})"
        )

    if args.diff_base:
        try:
            diff_doc = diff_against_base(fns, root, args.target, args.diff_base)
        except (RuntimeError, FileNotFoundError) as exc:
            sys.exit(f"ERROR: {exc}")
        if args.diff_json:
            dp = pathlib.Path(args.diff_json)
            dp.parent.mkdir(parents=True, exist_ok=True)
            dp.write_text(json.dumps(diff_doc, indent=2) + "\n", encoding="utf-8")
        if diff_doc["unchanged"]:
            print(
                f"UNCHANGED vs {args.diff_base}: 0/{len(fns)} C0 functions changed "
                f"(c0_sha256={diff_doc['cur_c0_sha256'][:12]})"
            )
            return
        preview = ", ".join(diff_doc["changed_fns"][:12])
        if len(diff_doc["changed_fns"]) > 12:
            preview += f", ... (+{len(diff_doc['changed_fns']) - 12} more)"
        print(
            f"CHANGED vs {args.diff_base}: {len(diff_doc['modified_fns'])} modified, "
            f"{len(diff_doc['added_fns'])} added, {len(diff_doc['removed_fns'])} removed "
            f"across {len(diff_doc['changed_tus'])} TU(s) "
            f"(c0_sha256={diff_doc['cur_c0_sha256'][:12]}): {preview}"
        )


if __name__ == "__main__":
    main()
