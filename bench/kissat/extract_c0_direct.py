#!/usr/bin/env python3
"""Extract spliced Kissat C0 functions (fidelity|m8opt|plain|m7fidelity|m7plus|m7|m6|m5) into a standalone C99 translation unit."""
import argparse
import os
import pathlib
import re
import subprocess
import sys

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


def emit_c99(fns):
    """Render deduplicated typedefs, prototypes, scoped #defines, and C99 function bodies."""
    out, seen_td, seen_st, td_alias = ['#include "c0.h"', ""], {}, set(), {}
    for f in fns:
        for nm, txt in f["tdefs"]:
            norm = _norm_typedef(txt)
            if nm not in seen_td:
                seen_td[nm] = norm
                out.append(txt)
            elif seen_td[nm] != norm and (f["block"], nm) not in td_alias:
                alias = f"{nm}__{len(td_alias)}"
                td_alias[(f["block"], nm)] = alias
                out.append(re.sub(rf"\b{re.escape(nm)}\s*;\s*$", f"{alias};", txt))
    for f in fns:
        for st in f["statics"]:
            if st not in seen_st:
                seen_st.add(st)
                out.append(st)
    out += ["", *(f"{f['ret']} {f['name']}({f['params']});" for f in fns), ""]
    active = {}
    for f in fns:
        m = {**f["macros"], **{nm: al for (blk, nm), al in td_alias.items() if blk == f["block"]}}
        for k in [k for k in active if k not in m or active[k] != m[k]]:
            out.append(f"#undef {k}")
            del active[k]
        for k, v in m.items():
            if k not in active:
                out.append(f"#define {k} {v}")
                active[k] = v
        out += [_prep_body(f), ""]
    return "\n".join(out)


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


def main():
    root = pathlib.Path(__file__).resolve().parents[2]
    kdir = root / "LeanQbe/T/Examples/Kissat"
    default_target = (
        "fidelity" if (kdir / "FullFidelityAssembly.lean").is_file()
        else ("m7fidelity" if (kdir / "FullM7FidelityAssembly.lean").is_file() else "m5")
    )
    target_specs = {
        "plain": ("Plain", "Plain", "plainFns"),
        "fidelity": ("FullFidelityAssembly", "FullFidelityAssembly", "fidFns"),
        "fid": ("FullFidelityAssembly", "FullFidelityAssembly", "fidFns"),
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
    ap = argparse.ArgumentParser(description="Extract spliced Kissat C0 functions to C99.")
    ap.add_argument(
        "--target",
        choices=list(target_specs),
        default=default_target,
    )
    ap.add_argument("--out", required=True)
    ap.add_argument("--check-fns", default=None)
    args = ap.parse_args()
    file_mod, ns_mod, sym = target_specs[args.target]
    if not (kdir / f"{file_mod}.lean").exists():
        sys.exit(f"ERROR: {kdir / f'{file_mod}.lean'} not found (--target {args.target} not landed yet)")
    fn_envs, list_envs, before_envs = load_kissat(kdir)
    fns = eval_list(f"{ns_mod}.{sym}", list_envs, fn_envs, {}, before_envs)
    if args.check_fns:
        check_fns(fns, args.check_fns, root, f"{KISSAT_NS}.{file_mod}", f"{KISSAT_NS}.{ns_mod}", sym)
    out = pathlib.Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(emit_c99(fns))
    print(f"Extracted {len(fns)} functions ({args.target}) -> {out}")


if __name__ == "__main__":
    main()
