#!/usr/bin/env python3
"""Classify dynamic register-to-register `mov` instructions in C4 binaries."""

import sys

sys.dont_write_bytecode = True

import argparse
import collections
import os
import re

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prof

_RR_RE = re.compile(r"^mov[lq]? (%\w+),(%\w+)$")
_CHAIN_OPS = (
    "add", "shl", "sub", "and", "or", "xor", "imul",
    "shr", "sar", "neg", "not", "inc", "dec",
)


def main():
    ap = argparse.ArgumentParser(
        description="Classify C4 dynamic reg-reg `mov` instructions by idiom."
    )
    ap.add_argument("binary", help="Path to C4 ELF binary")
    ap.add_argument("callgrind_out", help="Path to Callgrind output file")
    args = ap.parse_args()

    blocks = prof.load_blocks(args.binary)
    cost, _ = prof.load_cg(args.callgrind_out, args.binary)
    total = sum(cost.values())
    denom = max(total, 1)

    cls = collections.Counter()
    for insns in blocks.values():
        b = [(a, re.sub(r"\s+", " ", t.split("#")[0].strip())) for a, t in insns]
        n = len(b)
        for i, (a, t) in enumerate(b):
            m = _RR_RE.match(t)
            if not m:
                continue
            c = cost.get(a, 0)
            s = prof.canon_reg64(m.group(1))
            d = prof.canon_reg64(m.group(2))
            if s == d:
                cls["zext-self"] += c
                continue

            j = i + 1
            chain = mod = False
            reg32 = d.replace("r", "e", 1) if d.startswith("r") and d in (
                "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"
            ) else d + "d"
            addr_pat = re.compile(r"\(%%?(?:%s|%s[dwb]?)\)" % (re.escape(reg32), re.escape(d)))
            while j < n and j <= i + 6:
                tj = b[j][1]
                opj = tj.split(" ", 1)[0]
                argj = tj.split(" ", 1)[1] if " " in tj else ""
                dstj = argj.rsplit(",", 1)[-1].strip()
                if addr_pat.search(tj) or f"(%{d})" in tj:
                    chain = mod
                    break
                if dstj.startswith("%") and prof.canon_reg64(dstj) == d and opj.startswith(_CHAIN_OPS):
                    mod = True
                    j += 1
                    continue
                if dstj.startswith("%") and prof.canon_reg64(dstj) == d:
                    break
                j += 1

            if chain:
                kind = "addr-chain copy (mov;add/shl..;(%d))"
            elif mod:
                kind = "2-address copy (dst then modified)"
            else:
                k = i + 1
                ok = True
                while k < n:
                    opk = b[k][1].split(" ", 1)[0]
                    if opk.startswith(("jmp", "call", "ret")):
                        break
                    if not opk.startswith("mov"):
                        ok = False
                        break
                    k += 1
                if ok and k < n and b[k][1].startswith("call"):
                    kind = "call-arg/ABI shuffle"
                elif ok:
                    kind = "block-edge shuffle (before jmp/ret/fallthrough)"
                else:
                    kind = "other copy"
            cls[kind] += c

    tot_rr = sum(cls.values())
    print(f"total Ir {total / 1e6:.1f}M; reg-reg movs {tot_rr / 1e6:.1f}M ({100.0 * tot_rr / denom:.1f}%)")
    for k, c in cls.most_common():
        print(f"   {k:48s} {c / 1e6:9.1f}M  {100.0 * c / denom:5.2f}% of total")


if __name__ == "__main__":
    main()
