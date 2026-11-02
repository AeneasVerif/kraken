"""Common batched differential fuzzer harness shared between x86_64 and AArch64."""

import argparse
import json
import subprocess
import tempfile
import time
from pathlib import Path


def kraken(runner, *args, inp=None):
    res = subprocess.run([runner, *map(str, args)], input=inp, stdout=subprocess.PIPE, check=True)
    return json.loads(res.stdout)


def hardware_asm(asm_tests, seqs):
    """One binary that runs every sequence from Kraken's initial state and writes each final state
    to stdout, in the layout `parse_raw_state` reads."""
    state_bytes = asm_tests.STATE_BYTES
    blocks = [
        asm_tests.reset_state() + seq + asm_tests.save_state(f"_final_states + {i * state_bytes}")
        for i, seq in enumerate(seqs)
    ]
    total = state_bytes * len(seqs)
    return f"""
.bss
.balign 8
_final_states: .space {total}
{asm_tests.STACK_SECTION}
.text
.globl _start
_start:
{"".join(blocks)}
{asm_tests.write_and_exit("_final_states", total)}"""


def run_hardware(asm_tests, seqs, as_cmd, ld_cmd, emu_cmd=()):
    state_bytes = asm_tests.STATE_BYTES
    with tempfile.TemporaryDirectory() as tmp:
        src, obj, exe = (Path(tmp) / f"batch.{ext}" for ext in ("S", "o", "bin"))
        src.write_text(hardware_asm(asm_tests, seqs))
        subprocess.run([*as_cmd, "-o", obj, src], check=True)
        subprocess.run([*ld_cmd, asm_tests.LD_STACK, "-o", exe, obj], check=True)
        raw = subprocess.run([*emu_cmd, exe], check=True, capture_output=True, timeout=30).stdout
    return [asm_tests.parse_raw_state(raw[i * state_bytes:(i + 1) * state_bytes]) for i in range(len(seqs))]


def run_fuzzer(asm_tests, as_cmd, ld_cmd, emu_cmd=(), description=None):
    p = argparse.ArgumentParser(description=description)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--batches", type=int, default=5)
    p.add_argument("--batch-size", type=int, default=100)
    p.add_argument("--length", type=int, default=12)
    args = p.parse_args()

    failures = total = 0
    start = time.perf_counter()
    for b in range(args.batches):
        seed = args.seed + b
        seqs = kraken(asm_tests.KRAKEN_RUNNER, "--generate", seed, args.batch_size, args.length)
        preds = kraken(asm_tests.KRAKEN_RUNNER, "--batch", inp=json.dumps(seqs).encode())
        hw_states = run_hardware(asm_tests, seqs, as_cmd, ld_cmd, emu_cmd)
        for i, (seq, hw, k) in enumerate(zip(seqs, hw_states, preds, strict=True)):
            diffs = (
                asm_tests.compare_states(hw, asm_tests.ExecutionState(**k["state"]), [])
                if k["ok"]
                else [f"Kraken: {k['error']}"]
            )
            if diffs:
                failures += 1
                print(f"\n[FAIL] seed={seed} seq={i}:\n{seq}\n" + "\n".join(diffs))
        total += len(seqs)
        print(f"batch {b + 1}/{args.batches}: {total} seqs, {total / (time.perf_counter() - start):.0f} seq/s, {failures} failures")
    return 1 if failures else 0
