#!/usr/bin/env python3
"""Extract spliced Kissat C0 functions (m5|m6|m7|m7plus) into a standalone C99 translation unit."""
import argparse
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
    body_map, fn_envs, list_envs, files = {}, {}, {}, []
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
            list_envs[f"{ns}.{pfx}_fns"] = fns
    fn_re = re.compile(
        r'def\s+(\w+)\s*:\s*Fn\s*:=\s*⟨"([^"]+)"[^⟩]*?([A-Za-z0-9_.]+_body)⟩', re.S)
    list_re = re.compile(
        r"^def\s+(\w+)\s*:\s*List\s+Fn\s*:=\s*(.*?)"
        r"(?=\n(?:def|theorem|private|end|kissat_c0!|/-|\Z))", re.M | re.S)
    for _, txt, opens in files:
        for m in fn_re.finditer(txt):
            ns, fvar, exp, bref = _ns_at(txt, m.start()), m.group(1), m.group(2), m.group(3)
            if bref.startswith("LeanQbe."):
                bkey = bref
            elif "." in bref:
                bkey = f"{KISSAT_NS}.{bref}"
            else:
                bkey = f"{ns}.{bref}"
            if bkey in body_map:
                fn_envs[f"{ns}.{fvar}"] = {**body_map[bkey], "name": exp}
        for m in list_re.finditer(txt):
            ns = _ns_at(txt, m.start())
            list_envs[f"{ns}.{m.group(1)}"] = (ns, opens, m.group(2))
    return fn_envs, list_envs


def eval_list(qname, list_envs, fn_envs, cache):
    """Evaluate a Lean List Fn splice expression built from ++, .take, .drop, and [...]."""
    tok_pat = (r"\+\+|\.take\b|\.drop\b|[()\[\],]|"
               r"[A-Za-z0-9_]+(?:\.(?!take\b|drop\b)[A-Za-z0-9_]+)*")

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


def check_fns(fns, spec, root, mod, sym):
    """Assert 1-to-1 ordered name parity against an expected file, 'lean', or CSV list."""
    got = [f["name"] for f in fns]
    if spec == "lean":
        code = (f"import {mod}\nopen {mod} in #eval show IO Unit from do\n"
                f"  for f in {sym} do IO.println f.name")
        r = subprocess.run(["timeout", "60", "lake", "env", "lean", "--stdin"],
                           cwd=root, input=code, text=True, capture_output=True)
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
    ap = argparse.ArgumentParser(description="Extract spliced Kissat C0 functions to C99.")
    ap.add_argument("--target", choices=["m5", "m6", "m7", "m7plus"], default="m5")
    ap.add_argument("--out", required=True)
    ap.add_argument("--check-fns", default=None)
    args = ap.parse_args()
    root = pathlib.Path(__file__).resolve().parents[2]
    kdir = root / "LeanQbe/T/Examples/Kissat"
    mod, sym = {
        "m5": ("FullM5", "m5Fns"),
        "m6": ("FullM6", "m6Fns"),
        "m7": ("FullM7", "m7Fns"),
        "m7plus": ("FullM7Plus", "m7PlusFns"),
    }[args.target]
    if not (kdir / f"{mod}.lean").exists():
        sys.exit(f"ERROR: {kdir / f'{mod}.lean'} not found (--target {args.target} not landed yet)")
    fn_envs, list_envs = load_kissat(kdir)
    fns = eval_list(f"{mod}.{sym}", list_envs, fn_envs, {})
    if args.check_fns:
        check_fns(fns, args.check_fns, root, f"{KISSAT_NS}.{mod}", sym)
    out = pathlib.Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(emit_c99(fns))
    print(f"Extracted {len(fns)} functions ({args.target}) -> {out}")


if __name__ == "__main__":
    main()
