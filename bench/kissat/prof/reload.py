#!/usr/bin/env python3
"""Estimate dynamically-redundant `%rsp` stack reloads within C4 straight-line regions."""

import sys

sys.dont_write_bytecode = True

import argparse
import collections
import os
import re

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prof

_LOAD_RE = re.compile(r"^mov[lqwb]? (-?(?:0x)?[0-9a-f]*)\(%rsp\),(%\w+)$")
_STORE_RE = re.compile(r"^mov[lqwb]? (%\w+),(-?(?:0x)?[0-9a-f]*)\(%rsp\)$")
_SLOT_RE = re.compile(r"^(-?(?:0x)?[0-9a-f]*)\(%rsp\)$")
_CALLER_SAVED = {"rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"}


def main():
    ap = argparse.ArgumentParser(
        description="Estimate intra-block redundant `%rsp` reloads from a Callgrind profile."
    )
    ap.add_argument("binary", help="Path to C4 ELF binary")
    ap.add_argument("callgrind_out", help="Path to Callgrind output file")
    ap.add_argument("--top", type=int, default=8, help="Top N functions to report (default: 8)")
    args = ap.parse_args()

    blocks = prof.load_blocks(args.binary)
    cost, _ = prof.load_cg(args.callgrind_out, args.binary)
    total = sum(cost.values())
    denom = max(total, 1)

    tot_load = red_load = 0
    fn_red = collections.Counter()
    fn_load = collections.Counter()

    for label, insns in blocks.items():
        cur = prof.demangle_symbol(label)
        avail = collections.defaultdict(set)
        for addr, raw_t in insns:
            c = cost.get(addr, 0)
            t1 = re.sub(r"\s+", " ", raw_t.split("#")[0].strip())
            ml = _LOAD_RE.match(t1)
            ms = _STORE_RE.match(t1)
            op = t1.split(" ", 1)[0]
            if ml:
                slot = ml.group(1) or "0"
                reg = prof.canon_reg64(ml.group(2))
                tot_load += c
                fn_load[cur] += c
                if avail[slot]:
                    red_load += c
                    fn_red[cur] += c
                for s in avail.values():
                    s.discard(reg)
                avail[slot].add(reg)
                continue
            if ms:
                reg = prof.canon_reg64(ms.group(1))
                slot = ms.group(2) or "0"
                avail[slot] = {reg}
                continue
            if op.startswith("call"):
                for s in avail.values():
                    s.difference_update(_CALLER_SAVED)
                continue
            if op.startswith(("cmp", "test", "j", "push", "ret", "nop")):
                continue
            ins_args = t1.split(" ", 1)[1] if " " in t1 else ""
            dst = ins_args.rsplit(",", 1)[-1].strip() if ins_args else ""
            if "(%rsp)" in dst:
                mm = _SLOT_RE.match(dst)
                if mm:
                    avail[mm.group(1) or "0"] = set()
            elif dst.startswith("%"):
                r = prof.canon_reg64(dst)
                for s in avail.values():
                    s.discard(r)
            if (op.startswith(("mul", "div", "idiv", "imul")) and "," not in ins_args) or op.startswith(
                ("cltq", "cqto", "cdq")
            ):
                for s in avail.values():
                    s.difference_update({"rax", "rdx"})

    print(
        f"total Ir {total / 1e6:.1f}M; stack loads {tot_load / 1e6:.1f}M "
        f"({100.0 * tot_load / denom:.1f}%); redundant-in-block reloads {red_load / 1e6:.1f}M "
        f"({100.0 * red_load / denom:.2f}% of total, {100.0 * red_load / max(tot_load, 1):.0f}% of loads)"
    )
    for fn, c in fn_red.most_common(args.top):
        print(f"   {fn:26s} redundant {c / 1e6:9.1f}M of {fn_load[fn] / 1e6:9.1f}M loads")


if __name__ == "__main__":
    main()
