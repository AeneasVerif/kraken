#!/usr/bin/env python3
"""Batched differential fuzzer: runs random x86_64 sequences that Kraken deems deterministic
(krakenrunner_x64 --generate) on hardware and compares with Kraken's prediction (--batch)."""

import argparse
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from asm_tests import KRAKEN_RUNNER, REGS, SAFE_YMMS, ExecutionState, compare_states, parse_raw_state

YMM_BASE = (len(REGS) + 1) * 8  # GPRs, then rflags, then ymms
STATE_BYTES = YMM_BASE + 32 * len(SAFE_YMMS)
ZERO_GPRS = "\n    ".join(f"movq $0, %{r}" for r in REGS if r != "rsp")
STACK = 0x7ffecafee200  # Kraken's initial rsp (`stackLocation`); [rsp - 800, rsp) is mapped


def kraken(*args, inp=None):
    res = subprocess.run([KRAKEN_RUNNER, *map(str, args)], input=inp, stdout=subprocess.PIPE, check=True)
    return json.loads(res.stdout)


def hardware_asm(seqs):
    """One binary running every sequence from the same initial state as Kraken, dumping each final state."""
    blocks = []
    for idx, seq in enumerate(seqs):
        out = f"_final_states + {idx * STATE_BYTES}"
        saves = [f"movq %{r}, {out} + {i * 8}(%rip)" for i, r in enumerate(REGS)]
        saves += [f"vmovups %{y}, {out} + {YMM_BASE + i * 32}(%rip)" for i, y in enumerate(SAFE_YMMS)]
        # The sequence may have moved rsp.
        saves += [f"movq ${STACK}, %rsp", "pushfq", "popq %rax", f"movq %rax, {out} + {len(REGS) * 8}(%rip)"]
        blocks.append(f"""
    movq ${STACK}, %rsp
    pushq $0
    popfq
    leaq -800(%rsp), %rdi
    movb $0xff, %al
    movq $800, %rcx
    rep stosb
    vzeroall
    {ZERO_GPRS}
{seq}
    """ + "\n    ".join(saves))
    total = STATE_BYTES * len(seqs)
    return f"""
.bss
_final_states: .space {total}
.section .stack, "aw", @nobits  # Kraken's stack [STACK - 800, STACK), placed by ld
.space 800
.text
.globl _start
_start:
{"".join(blocks)}
    movq $1, %rax
    movq $1, %rdi
    leaq _final_states(%rip), %rsi
    movq ${total}, %rdx
    syscall
    movq $60, %rax
    xorq %rdi, %rdi
    syscall
"""


def run_hardware(seqs):
    with tempfile.TemporaryDirectory() as tmp:
        src, obj, exe = (Path(tmp) / f"batch.{ext}" for ext in ("S", "o", "bin"))
        src.write_text(hardware_asm(seqs))
        subprocess.run(["as", "-o", obj, src], check=True)
        subprocess.run(["ld", f"--section-start=.stack={STACK - 800:#x}", "-o", exe, obj], check=True)
        raw = subprocess.run([exe], check=True, capture_output=True, timeout=30).stdout
    return [parse_raw_state(raw[i * STATE_BYTES:(i + 1) * STATE_BYTES]) for i in range(len(seqs))]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--batches", type=int, default=5)
    p.add_argument("--batch-size", type=int, default=100)
    p.add_argument("--length", type=int, default=12)
    p.add_argument("--hardware", type=argparse.FileType(), metavar="JSON",
                   help="only run a JSON array of sequences ('-' for stdin) on hardware")
    args = p.parse_args()

    if args.hardware:
        seqs = json.load(args.hardware)
        print(json.dumps([vars(s) for s in run_hardware(seqs)]))
        return 0

    failures = total = 0
    start = time.perf_counter()
    for b in range(args.batches):
        seed = args.seed + b
        seqs = kraken("--generate", seed, args.batch_size, args.length)
        preds = kraken("--batch", inp=json.dumps(seqs).encode())
        for i, (seq, hw, k) in enumerate(zip(seqs, run_hardware(seqs), preds, strict=True)):
            diffs = compare_states(hw, ExecutionState(**k["state"]), []) if k["ok"] else [f"Kraken: {k['error']}"]
            if k["ok"] and (hr := hw.regs["rsp"]) != (kr := k["state"]["regs"].get("rsp", 0)):  # compare_states skips rsp
                diffs.append(f"rsp: x86={hr:#x}, kraken={kr:#x}")
            if diffs:
                failures += 1
                print(f"\n[FAIL] seed={seed} seq={i}:\n{seq}\n" + "\n".join(diffs))
        total += len(seqs)
        print(f"batch {b + 1}/{args.batches}: {total} seqs, {total / (time.perf_counter() - start):.0f} seq/s, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
