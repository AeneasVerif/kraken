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

`fuzz_aarch64.py` runs semi-random sequences of instructions under qemu, checking them
against Kraken semantics. More details are in `Kraken/X64/Test/README.md`.

```bash
# Default run; reports the pool size and the mnemonics run least often.
python3 Kraken/AArch64/Test/fuzz_aarch64.py --batches 1 --batch-size 50
#   pool: 97 mnemonics
#   batch 1/1: 50 seqs, 90 seq/s, 0 failures
#   never accepted into a sequence (jumps, or every form faults): b, b.al, b.ls, b.nv, b.vc, bl, blr, br, ret
#   least run: ldursb (1), b.cc (1), b.pl (2), b.ne (2), b.gt (2)
# (the fuzzer runs straight-line code only: a branch is accepted only when it is not taken)

# Fuzz only mnemonics that start with one of the given prefixes.
python3 Kraken/AArch64/Test/fuzz_aarch64.py --only ldr,str

# Reports what would be included in the pool (e.g., {"pool":["ldr","ldrb","ldrh","ldrsb","ldrsh","ldrsw"],"runs":{},"seqs":[]})
echo '{"seed": 42, "count": 0, "length": 12, "only": ["ldr"]}' | ./.lake/build/bin/krakenrunner_aarch64 --generate
```
