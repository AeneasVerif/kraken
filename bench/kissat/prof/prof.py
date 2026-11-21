#!/usr/bin/env python3
"""Shared objdump/callgrind loaders, x86-64 instruction classifier, and single-binary profiler."""

import sys

sys.dont_write_bytecode = True

import argparse
import collections
import os
import re
import subprocess

_STK_RE = re.compile(r"\(%rsp\)|\(%rbp\)")
_LABEL_RE = re.compile(r"^([0-9a-f]+) <([^>]+)>:$")
_INSN_RE = re.compile(r"^\s*([0-9a-f]+):\s+(.*)$")
_TQBE_RE = re.compile(r"^_ZN8tqbe_gen(\d+)")
_MEM_MODRM_RE = re.compile(r"(-?(?:0x)?[0-9a-f]*)\(([^)]*)\)")

_REG64_MAP = {
    "eax": "rax", "ax": "rax", "al": "rax", "ah": "rax",
    "ebx": "rbx", "bx": "rbx", "bl": "rbx", "bh": "rbx",
    "ecx": "rcx", "cx": "rcx", "cl": "rcx", "ch": "rcx",
    "edx": "rdx", "dx": "rdx", "dl": "rdx", "dh": "rdx",
    "esi": "rsi", "si": "rsi", "sil": "rsi",
    "edi": "rdi", "di": "rdi", "dil": "rdi",
    "ebp": "rbp", "bp": "rbp", "bpl": "rbp",
    "esp": "rsp", "sp": "rsp", "spl": "rsp",
}

CLASS_GROUPS = [
    ("stack", ["stk_load", "stk_store", "stk_rmw_or_use", "pushpop"]),
    ("addr-arith(shl/add/sub/lea)", ["shl_imm", "addsub_imm", "addsub_rr", "lea"]),
    ("mov_rr", ["mov_rr"]),
    ("zext/ext rr", ["mov_rr_same(zext)", "mov_ext_rr"]),
    ("mem(non-stack)", ["mem_mov(nonstk)", "alu_mem(nonstk)"]),
    ("cmp/test+jcc", ["cmp/test", "jcc"]),
    ("jmp", ["jmp"]),
    ("mov_imm", ["mov_imm"]),
    ("call+ret", ["call", "ret"]),
    ("setcc+cmov", ["setcc", "cmov"]),
    ("alu_other", ["alu_other", "shl_var"]),
]

TOP_FN_CLASS_COLS = [
    "stk_load", "stk_store", "stk_rmw_or_use", "mov_rr", "mov_rr_same(zext)",
    "mem_plain(%r)", "mem_disp(%r)", "mem_sib", "shl_imm", "addsub_imm",
    "addsub_rr", "lea", "call", "ret", "pushpop", "jcc", "jmp",
    "cmp/test", "mov_imm", "setcc", "cmov",
]


def demangle_symbol(name):
    """Strip C4 `.L<n>` block suffixes and demangle QBE `_ZN8tqbe_gen<len><sym>` names."""
    base = re.sub(r"\.L\d+$", "", name.strip())
    m = _TQBE_RE.match(base)
    if m:
        k = int(m.group(1))
        st = len("_ZN8tqbe_gen") + len(m.group(1))
        return base[st : st + k]
    if base.startswith("(") and base.endswith(")"):
        return base
    return base.split("(")[0] or base


def canon_reg64(reg):
    """Map an x86-64 AT&T register operand to its canonical 64-bit register name."""
    r = reg.strip().lstrip("%")
    if r in _REG64_MAP:
        return _REG64_MAP[r]
    m = re.match(r"^(r\d+)[dwb]?$", r)
    return m.group(1) if m else r


def _run_objdump(binp):
    proc = subprocess.run(
        ["objdump", "-d", "--no-show-raw-insn", binp],
        capture_output=True,
        text=True,
        timeout=120,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"objdump failed on {binp}: {proc.stderr.strip()}")
    return proc.stdout


def load_objdump(binp):
    """Return `(insn_by_addr, ordered_addrs)` mapping address -> `(fn_name, disasm_text)`."""
    insn = {}
    order = []
    cur = None
    for line in _run_objdump(binp).splitlines():
        m = _LABEL_RE.match(line)
        if m:
            cur = demangle_symbol(m.group(2))
            continue
        m = _INSN_RE.match(line)
        if m and cur is not None:
            addr = int(m.group(1), 16)
            insn[addr] = (cur, m.group(2).strip())
            order.append(addr)
    return insn, order


def load_blocks(binp):
    """Return an OrderedDict mapping raw block label -> `[(addr, disasm_text), ...]`."""
    blocks = collections.OrderedDict()
    cur = None
    for line in _run_objdump(binp).splitlines():
        m = _LABEL_RE.match(line)
        if m:
            cur = m.group(2)
            blocks.setdefault(cur, [])
            continue
        m = _INSN_RE.match(line)
        if m and cur is not None:
            blocks[cur].append((int(m.group(1), 16), m.group(2).strip()))
    return blocks


def load_cg(path, binp):
    """Sum Callgrind self-Ir per instruction address in `binp`, plus non-target object Ir."""
    cost = collections.Counter()
    other = 0
    after_calls = False
    in_main = False
    base = os.path.basename(os.path.abspath(binp))
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            if line.startswith("ob="):
                ob_name = os.path.basename(line[3:].strip())
                in_main = ob_name == base
                continue
            if line.startswith("calls="):
                after_calls = True
                continue
            if line.startswith("0x"):
                if after_calls:
                    after_calls = False
                    continue
                parts = line.split()
                if len(parts) >= 2:
                    ir = int(parts[-1])
                    if in_main:
                        cost[int(parts[0], 16)] += ir
                    else:
                        other += ir
    return cost, other


def classify(text):
    """Assign x86-64 AT&T instruction disassembly into dynamic cost categories."""
    t = text.split("#")[0].strip()
    parts = t.split(None, 1)
    op = parts[0] if parts else ""
    args = parts[1] if len(parts) > 1 else ""
    cls = []
    if op.startswith("call"):
        return ["call"]
    if op.startswith("ret"):
        return ["ret"]
    if op.startswith("push") or op.startswith("pop"):
        return ["pushpop"]
    if op.startswith("j"):
        return ["jmp" if op == "jmp" else "jcc"]
    if op.startswith("lea"):
        return ["lea"]
    if op.startswith("set"):
        return ["setcc"]
    if op.startswith("cmov"):
        cls.append("cmov")
    if op.startswith("cmp") or op.startswith("test"):
        cls.append("cmp/test")
    if _STK_RE.search(args):
        dst = args.rsplit(",", 1)[-1].strip() if "," in args else args
        if _STK_RE.search(dst) and op.startswith("mov"):
            cls.append("stk_store")
        elif op.startswith("mov"):
            cls.append("stk_load")
        else:
            cls.append("stk_rmw_or_use")
        return cls
    if op.startswith("mov"):
        if "(" in args:
            cls.append("mem_mov(nonstk)")
            m = _MEM_MODRM_RE.search(args)
            if m:
                disp, inner = m.group(1), m.group(2)
                if "," in inner:
                    cls.append("mem_sib")
                elif disp in ("", "0", "0x0"):
                    cls.append("mem_plain(%r)")
                else:
                    cls.append("mem_disp(%r)")
        elif args.startswith("$"):
            cls.append("mov_imm")
        else:
            ops = [x.strip() for x in args.split(",")]
            if len(ops) == 2 and ops[0] == ops[1]:
                cls.append("mov_rr_same(zext)")
            elif op in (
                "movzbl", "movzwl", "movsbl", "movswl", "movslq",
                "movzbq", "movzwq", "movsbq", "movswq", "movzbw", "movsbw",
            ):
                cls.append("mov_ext_rr")
            else:
                cls.append("mov_rr")
        return cls
    if "(" in args and not cls:
        cls.append("alu_mem(nonstk)")
    if op.startswith("shl") or op.startswith("sal"):
        cls.append("shl_imm" if args.startswith("$") else "shl_var")
    elif op.startswith("add") or op.startswith("sub"):
        cls.append("addsub_imm" if args.startswith("$") else "addsub_rr")
    elif op.startswith((
        "and", "or", "xor", "not", "neg", "shr", "sar", "imul", "mul", "div",
        "idiv", "inc", "dec", "rol", "ror", "bt", "adc", "sbb", "cltq", "cqto",
        "cdq", "cwtl", "bsf", "bsr", "tzcnt", "lzcnt", "popcnt",
    )):
        cls.append("alu_other")
    if not cls:
        cls.append("other:" + op)
    return cls


def profile_binary(binp, cg_path, insn=None):
    """Aggregate self-Ir by function and instruction class for `(binp, cg_path)`."""
    if insn is None:
        insn, _ = load_objdump(binp)
    cost, other = load_cg(cg_path, binp)
    total = sum(cost.values())
    by_fn = collections.Counter()
    by_cls = collections.Counter()
    by_fn_cls = collections.defaultdict(collections.Counter)
    unk = 0
    for addr, ir in cost.items():
        if addr not in insn:
            unk += ir
            continue
        fn, text = insn[addr]
        by_fn[fn] += ir
        for k in classify(text):
            by_cls[k] += ir
            by_fn_cls[fn][k] += ir
    return total, other, unk, by_fn, by_cls, by_fn_cls


def main():
    ap = argparse.ArgumentParser(
        description="Attribute Callgrind self-Ir to functions and x86-64 instruction classes."
    )
    ap.add_argument("binary", help="Path to profiled ELF binary")
    ap.add_argument("callgrind_out", help="Path to uncompressed Callgrind output file")
    ap.add_argument("top_pos", nargs="?", type=int, help="Optional positional top-N override")
    ap.add_argument("--top", type=int, default=30, help="Number of functions to display (default: 30)")
    args = ap.parse_args()
    topn = args.top_pos if args.top_pos is not None else args.top

    total, other, unk, by_fn, by_cls, by_fn_cls = profile_binary(args.binary, args.callgrind_out)
    denom = max(total, 1)
    print(f"main-object Ir {total}; other objects (libc/ld) Ir {other}")
    print(f"TOTAL_IR {total}  (unattributed: {unk} = {100.0 * unk / denom:.2f}%)")
    print("--- classes (% of total Ir; an insn may be in >1 class)")
    for k, c in by_cls.most_common():
        print(f"  {k:24s} {c:14d} {100.0 * c / denom:6.2f}%")
    print(f"--- top {topn} functions by self Ir")
    header = "  " + "fn".ljust(28) + "Ir".rjust(13) + "  %tot  " + " ".join(
        k[:9].rjust(9) for k in TOP_FN_CLASS_COLS
    )
    print(header)
    for fn, c in by_fn.most_common(topn):
        if c == 0:
            continue
        row = " ".join(f"{100.0 * by_fn_cls[fn][k] / c:8.1f}%" for k in TOP_FN_CLASS_COLS)
        print(f"  {fn[:28]:28s}{c:13d} {100.0 * c / denom:5.1f}%  {row}")


if __name__ == "__main__":
    main()
