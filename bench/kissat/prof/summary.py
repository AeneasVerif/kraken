#!/usr/bin/env python3
"""Compare C4 vs C3b Callgrind profiles across CNFs (instruction-class + per-function)."""

import sys

sys.dont_write_bytecode = True

import argparse
import collections
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prof


def _print_comparison(label, t4, f4, c4, t3, f3, c3, topn):
    if t4 == 0 or t3 == 0:
        print(f"\n##### {label}: missing Ir samples (C4={t4}, C3b={t3})")
        return
    gap = t4 - t3
    gap_denom = gap if gap != 0 else 1
    print(
        f"\n##### {label}: Ir C4={t4 / 1e6:.1f}M C3b={t3 / 1e6:.1f}M "
        f"ratio={t4 / t3:.2f}x  gap={gap / 1e6:.1f}M"
    )
    print("  class-group                     C4(M)   C3b(M)  delta(M)  %gap")
    for name, ks in prof.CLASS_GROUPS:
        a = sum(c4[k] for k in ks)
        b = sum(c3[k] for k in ks)
        print(
            f"  {name:30s}{a / 1e6:8.1f} {b / 1e6:8.1f} "
            f"{(a - b) / 1e6:8.1f}  {100.0 * (a - b) / gap_denom:5.1f}%"
        )
    print(f"  calls: C4={c4['call']} C3b={c3['call']}")
    print("  top fns C4 (%, M) | same fn in C3b (%, M) | fn ratio")
    for fn, c in f4.most_common(topn):
        b = f3.get(fn, 0)
        ratio = f"{c / b:.2f}x" if b else "inlined"
        print(
            f"    {fn[:26]:26s} {100.0 * c / t4:5.1f}% {c / 1e6:8.1f} | "
            f"{100.0 * b / t3:5.1f}% {b / 1e6:8.1f} | {ratio}"
        )


def _cg_stem(cnf_arg):
    base = os.path.basename(cnf_arg)
    return base[:-4] if base.endswith(".cnf") else base


def main():
    ap = argparse.ArgumentParser(
        description="Produce dynamic C4 vs C3b per-function and per-instruction-class reports."
    )
    ap.add_argument("--c4", required=True, help="Path to C4 binary")
    ap.add_argument("--c3b", required=True, help="Path to C3b binary")
    ap.add_argument("--cg-dir", help="Directory containing <bin>.<cnf_stem>.out Callgrind files")
    ap.add_argument("--c4-out", help="Explicit Callgrind .out file for C4 (single-pair mode)")
    ap.add_argument("--c3b-out", help="Explicit Callgrind .out file for C3b (single-pair mode)")
    ap.add_argument("--label", default="profile", help="Label for single-pair mode")
    ap.add_argument("--top", type=int, default=14, help="Top N functions per CNF (default: 14)")
    ap.add_argument("cnfs", nargs="*", help="CNF path(s) or stem(s) matching <cg-dir> files")
    args = ap.parse_args()

    insn4, _ = prof.load_objdump(args.c4)
    insn3, _ = prof.load_objdump(args.c3b)

    pairs = []
    if args.c4_out or args.c3b_out:
        if not (args.c4_out and args.c3b_out):
            ap.error("--c4-out and --c3b-out must be supplied together")
        pairs.append((args.label, args.c4_out, args.c3b_out))
    else:
        if not args.cg_dir or not args.cnfs:
            ap.error("Provide either (--c4-out and --c3b-out) or (--cg-dir and at least one CNF)")
        b4 = os.path.basename(os.path.abspath(args.c4))
        b3 = os.path.basename(os.path.abspath(args.c3b))
        for cnf in args.cnfs:
            stem = _cg_stem(cnf)
            pairs.append((
                stem,
                os.path.join(args.cg_dir, f"{b4}.{stem}.out"),
                os.path.join(args.cg_dir, f"{b3}.{stem}.out"),
            ))

    agg_t4 = agg_t3 = 0
    agg_f4, agg_c4 = collections.Counter(), collections.Counter()
    agg_f3, agg_c3 = collections.Counter(), collections.Counter()

    for label, out4, out3 in pairs:
        t4, _, _, f4, c4, _ = prof.profile_binary(args.c4, out4, insn=insn4)
        t3, _, _, f3, c3, _ = prof.profile_binary(args.c3b, out3, insn=insn3)
        _print_comparison(label, t4, f4, c4, t3, f3, c3, args.top)
        agg_t4 += t4
        agg_t3 += t3
        agg_f4.update(f4)
        agg_c4.update(c4)
        agg_f3.update(f3)
        agg_c3.update(c3)

    if len(pairs) > 1:
        _print_comparison("AGGREGATE", agg_t4, agg_f4, agg_c4, agg_t3, agg_f3, agg_c3, args.top)


if __name__ == "__main__":
    main()
