#!/usr/bin/env python3
"""Batched differential fuzzer: runs random AArch64 sequences that Kraken deems deterministic
(krakenrunner_aarch64 --generate) on QEMU and compares with Kraken's prediction (--batch)."""

import argparse
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from asm_tests import (KRAKEN_RUNNER_AARCH64, LD_STACK, STACK_SECTION, STATE_BYTES, ExecutionState,
                       compare_states, find_tool, get_assembler, get_linker, parse_raw_state,
                       reset_state, save_state, write_and_exit)


def kraken(*args, inp=None):
    res = subprocess.run([KRAKEN_RUNNER_AARCH64, *map(str, args)], input=inp, stdout=subprocess.PIPE, check=True)
    return json.loads(res.stdout)


def hardware_asm(seqs):
    """One binary that runs every sequence from Kraken's initial state and writes each final state
    to stdout, in the layout `parse_raw_state` reads."""
    blocks = [reset_state() + seq + save_state(f"_final_states + {i * STATE_BYTES}") for i, seq in enumerate(seqs)]
    total = STATE_BYTES * len(seqs)
    return f"""
.bss
.align 8
_final_states: .space {total}
{STACK_SECTION}
.text
.globl _start
_start:
{"".join(blocks)}
{write_and_exit("_final_states", total)}"""


def run_hardware(seqs):
    as_cmd = get_assembler()
    ld_cmd = get_linker()
    qemu_bin = find_tool(["qemu-aarch64", "qemu-aarch64-static"])
    if not as_cmd or not ld_cmd or not qemu_bin:
        raise RuntimeError("Missing AArch64 assembler, linker, or qemu-aarch64.")
    with tempfile.TemporaryDirectory() as tmp:
        src, obj, exe = (Path(tmp) / f"batch.{ext}" for ext in ("S", "o", "bin"))
        src.write_text(hardware_asm(seqs))
        subprocess.run(as_cmd + ["-o", str(obj), str(src)], check=True)
        subprocess.run(ld_cmd + [LD_STACK, "-o", str(exe), str(obj)], check=True)
        raw = subprocess.run([qemu_bin, str(exe)], check=True, capture_output=True, timeout=30).stdout
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
            if diffs:
                failures += 1
                print(f"\n[FAIL] seed={seed} seq={i}:\n{seq}\n" + "\n".join(diffs))
        total += len(seqs)
        print(f"batch {b + 1}/{args.batches}: {total} seqs, {total / (time.perf_counter() - start):.0f} seq/s, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
