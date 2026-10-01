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

from asm_tests import (KRAKEN_RUNNER, REGS, SAFE_YMMS, ExecutionState, compare_states, parse_raw_state,
                       write_and_exit)

YMM_BASE = (len(REGS) + 1) * 8  # GPRs, then rflags, then ymms
STATE_BYTES = YMM_BASE + 32 * len(SAFE_YMMS)
ZERO_GPRS = "\n    ".join(f"movq $0, %{r}" for r in REGS if r != "rsp")
# Kraken's initial rsp and its stack mapping [STACK - STACK_SIZE, STACK), filled with 0xff
# (`stackLocation`, `stackSize` and `initStack` in KrakenRunnerX64.lean).
STACK = 0x7ffecafee200
STACK_SIZE = 800


def kraken(*args, inp=None):
    res = subprocess.run([KRAKEN_RUNNER, *map(str, args)], input=inp, stdout=subprocess.PIPE, check=True)
    return json.loads(res.stdout)


def hardware_asm(seqs):
    """One binary that runs every sequence from Kraken's initial state (`initData`) and writes each
    final state to stdout, in the layout `parse_raw_state` reads."""
    blocks = []
    for idx, seq in enumerate(seqs):
        out = f"_final_states + {idx * STATE_BYTES}"
        saves = [f"movq %{r}, {out} + {i * 8}(%rip)" for i, r in enumerate(REGS)]
        saves += [f"vmovups %{y}, {out} + {YMM_BASE + i * 32}(%rip)" for i, y in enumerate(SAFE_YMMS)]
        # rflags can only be read via the stack, and the sequence may have moved rsp.
        saves += [f"movq ${STACK}, %rsp", "pushfq", "popq %rax", f"movq %rax, {out} + {len(REGS) * 8}(%rip)"]
        blocks.append(f"""
    # Reset to Kraken's initial state: rsp = STACK, rflags = 0, the stack filled with 0xff, and all
    # other GPRs and ymm registers zero.
    movq ${STACK}, %rsp
    pushq $0
    popfq                       # rflags = 0
    leaq -{STACK_SIZE}(%rsp), %rdi
    movb $0xff, %al
    movq ${STACK_SIZE}, %rcx
    rep stosb                   # memset(rdi, al, rcx)
    vzeroall
    {ZERO_GPRS}
{seq}
    # Save the final state: GPRs, ymm registers, rflags.
    """ + "\n    ".join(saves))
    total = STATE_BYTES * len(seqs)
    return f"""
.bss
_final_states: .space {total}
# Kraken's stack; `run_hardware` has ld place it at [STACK - STACK_SIZE, STACK).
.section .stack, "aw", @nobits
.space {STACK_SIZE}
.text
.globl _start
_start:
{"".join(blocks)}
{write_and_exit("_final_states", total)}"""


def run_hardware(seqs):
    with tempfile.TemporaryDirectory() as tmp:
        src, obj, exe = (Path(tmp) / f"batch.{ext}" for ext in ("S", "o", "bin"))
        src.write_text(hardware_asm(seqs))
        subprocess.run(["as", "-o", obj, src], check=True)
        # `--section-start` maps the `.stack` section at a fixed address, giving the binary exactly
        # Kraken's stack, so rsp (and anything computed from it, e.g. PF of `subq $8, %rsp`) matches.
        subprocess.run(["ld", f"--section-start=.stack={STACK - STACK_SIZE:#x}", "-o", exe, obj], check=True)
        raw = subprocess.run([exe], check=True, capture_output=True, timeout=30).stdout
    return [parse_raw_state(raw[i * STATE_BYTES:(i + 1) * STATE_BYTES]) for i in range(len(seqs))]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--batches", type=int, default=5)
    p.add_argument("--batch-size", type=int, default=100)
    p.add_argument("--length", type=int, default=12)
    args = p.parse_args()

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
