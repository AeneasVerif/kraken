#!/usr/bin/env python3
"""Inclusive Ir and call counts per callee from an uncompressed Callgrind output file."""

import sys

sys.dont_write_bytecode = True

import argparse
import collections
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prof


def main():
    ap = argparse.ArgumentParser(
        description="Report inclusive Ir and call counts per callee (C3b symbols recommended)."
    )
    ap.add_argument("callgrind_out", help="Path to uncompressed Callgrind output file")
    ap.add_argument("patterns", nargs="*", help="Optional substring filters on callee names")
    ap.add_argument("--edges", action="store_true", help="Also print hottest caller -> callee edges")
    ap.add_argument("--top", type=int, default=60, help="Top callees to display (default: 60)")
    ap.add_argument("--edge-top", type=int, default=40, help="Top edges with --edges (default: 40)")
    args = ap.parse_args()

    incl = collections.Counter()
    calls = collections.Counter()
    edge = collections.Counter()
    total = 0
    cur = cfn = None
    pending = None

    with open(args.callgrind_out, encoding="utf-8", errors="replace") as f:
        for line in f:
            if line.startswith("fn="):
                cur = prof.demangle_symbol(line[3:])
            elif line.startswith("cfn="):
                cfn = prof.demangle_symbol(line[4:])
            elif line.startswith("calls="):
                pending = int(line[6:].split()[0])
            elif line.startswith("0x"):
                ir = int(line.split()[-1])
                if pending is not None:
                    incl[cfn] += ir
                    calls[cfn] += pending
                    edge[(cur, cfn)] += ir
                    pending = None
                else:
                    total += ir

    denom = max(total, 1)
    print(f"total self Ir {total}")
    names = [
        n for n in incl if not args.patterns or any(p in n for p in args.patterns)
    ]
    for name in sorted(names, key=lambda n: -incl[n])[: args.top]:
        print(
            f"  {name[:34]:34s} incl={incl[name] / 1e6:10.1f}M "
            f"{100.0 * incl[name] / denom:6.2f}%  calls={calls[name]}"
        )
    if args.edges:
        edges = [
            ((a, b), c)
            for (a, b), c in edge.items()
            if not args.patterns or any(p in a or p in b for p in args.patterns)
        ]
        for (a, b), c in sorted(edges, key=lambda kv: -kv[1])[: args.edge_top]:
            print(f"    {a[:28]:28s} -> {b[:28]:28s} {c / 1e6:10.1f}M {100.0 * c / denom:6.2f}%")


if __name__ == "__main__":
    main()
