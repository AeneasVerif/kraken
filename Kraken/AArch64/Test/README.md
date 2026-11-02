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
