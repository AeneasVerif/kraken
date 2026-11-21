#!/usr/bin/env python3
"""Print the hottest instructions of a function filtered by fraction of peak execution count."""

import sys

sys.dont_write_bytecode = True

import argparse
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prof


def main():
    ap = argparse.ArgumentParser(
        description="Print hottest instructions in a function above `lo * max_ir`."
    )
    ap.add_argument("binary", help="Path to ELF binary")
    ap.add_argument("callgrind_out", help="Path to Callgrind output file")
    ap.add_argument("function", help="Function name (demangled)")
    ap.add_argument("--lo", type=float, default=0.1, help="Min fraction of max insn Ir (default: 0.1)")
    ap.add_argument("--max-lines", type=int, default=60, help="Max instructions to print (default: 60)")
    args = ap.parse_args()

    insn, order = prof.load_objdump(args.binary)
    cost, _ = prof.load_cg(args.callgrind_out, args.binary)
    addrs = [a for a in order if insn[a][0] == args.function]
    if not addrs:
        print(f"No instructions found for function: {args.function}", file=sys.stderr)
        sys.exit(1)

    mx = max((cost.get(a, 0) for a in addrs), default=0)
    if mx == 0:
        print(f"Function {args.function} has 0 recorded Ir.")
        return

    printed = 0
    for a in addrs:
        c = cost.get(a, 0)
        if c >= args.lo * mx:
            print(f"{a:8x} {c:12d}  {insn[a][1]}")
            printed += 1
            if printed >= args.max_lines:
                break


if __name__ == "__main__":
    main()
