#!/usr/bin/env python3
"""Per-block (C4 `.L` labels) self-Ir + estimated execution counts for selected functions."""

import sys

sys.dont_write_bytecode = True

import argparse
import os
import re

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prof


def main():
    ap = argparse.ArgumentParser(
        description="Print per-basic-block self-Ir, approx executions, and stack% for functions."
    )
    ap.add_argument("binary", help="Path to ELF binary")
    ap.add_argument("callgrind_out", help="Path to Callgrind output file")
    ap.add_argument("functions", nargs="+", help="Demangled/raw function names to inspect")
    args = ap.parse_args()

    blocks = prof.load_blocks(args.binary)
    cost, _ = prof.load_cg(args.callgrind_out, args.binary)
    total = max(sum(cost.values()), 1)

    for fn in args.functions:
        fn_blocks = [
            (lbl, ins)
            for lbl, ins in blocks.items()
            if prof.demangle_symbol(lbl) == fn or re.sub(r"\.L\d+$", "", lbl) == fn
        ]
        ftot = sum(cost.get(a, 0) for _, ins in fn_blocks for a, _ in ins)
        print(f"=== {fn}: self Ir {ftot} ({100.0 * ftot / total:.1f}% of total)")
        if ftot == 0:
            continue
        for lbl, ins in fn_blocks:
            if not ins:
                continue
            bt = sum(cost.get(a, 0) for a, _ in ins)
            if bt == 0:
                continue
            ex = max((cost.get(a, 0) for a, _ in ins), default=0)
            stk = sum(
                cost.get(a, 0)
                for a, t in ins
                if "(%rsp)" in t and not t.startswith(("lea", "call"))
            )
            print(
                f"  {lbl:34s} n_insn={len(ins):3d} exec~{ex:10d} "
                f"Ir={bt:11d} {100.0 * bt / ftot:5.1f}%fn  stk={100.0 * stk / max(bt, 1):4.1f}%"
            )


if __name__ == "__main__":
    main()
