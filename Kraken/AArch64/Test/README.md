# Kraken AArch64 Assembly Test Suite

This directory contains the assembly-level test suite used to validate Kraken’s AArch64 semantics against native execution.

## Writing Tests

Tests are written as sequences of ARM64/AArch64 instructions.

### Handling Undefined Flags

If an instruction leaves flags undefined, exclude them using a preamble comment:
```assembly
# Undefined flags: n, z, c, v
add x1, x1, #10
```

## Running Tests

### Execution Commands
```bash
# Run all AArch64 tests
python3 Kraken/AArch64/Test/asm_tests.py Kraken/AArch64/Test/asm

# Run a specific test
python3 Kraken/AArch64/Test/asm_tests.py Kraken/AArch64/Test/asm/test_add.S

# Manual inspection of Kraken output
./.lake/build/bin/krakenrunner_aarch64 Kraken/AArch64/Test/asm/test_add.S
```

## Differential Fuzzing

`fuzz_aarch64.py` runs random sequences under `qemu-aarch64` and compares the final state with
Kraken's prediction. It shares its harness and options with the x64 fuzzer; see the "Differential
Fuzzing" section of `Kraken/X64/Test/README.md` for how the per-mnemonic pool is built and
sampled. In short:

```bash
# Default run; reports the pool size and the mnemonics run least often.
python3 Kraken/AArch64/Test/fuzz_aarch64.py --batches 1 --batch-size 50
#   pool: 98 mnemonics
#   batch 1/1: 50 seqs, 21 seq/s, 0 failures
#   never accepted into a sequence (jumps, or every form faults): b, b.al, b.ls, b.nv, b.pl, b.vc, bl, blr, br, ret
#   least run: b.ge (1), b.cc (1), tbz (2), lslv (2), ldursw (2)
# (the fuzzer runs straight-line code only: a branch is accepted only when it is not taken)

# Only mnemonics with one of the given prefixes.
python3 Kraken/AArch64/Test/fuzz_aarch64.py --only ldr,str

# The pool's mnemonics with their number of distinct forms.
./.lake/build/bin/krakenrunner_aarch64 --mnemonics
./.lake/build/bin/krakenrunner_aarch64 --mnemonics ldr
```
