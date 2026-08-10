# Kraken Assembly Test Suite

This directory contains the assembly-level test suite used to validate Kraken’s x86 semantics. It compares Kraken's internal state transitions against native execution using the GNU Assembler (`as`).

## Writing Tests

Tests are written as sequences of x86 instructions using **AT&T syntax**. The test runner executes these instructions through both Kraken and the host hardware, reporting a failure if the resulting register or flag states diverge.

### Best Practices

- **Keep tests atomic**: Write small, self-contained unit tests. Each file should target a single behavior or instruction variant.
- **Prioritize debuggability**: If a test fails, the culprit instruction should be immediately obvious. Avoid long, complex instruction chains that obfuscate the point of failure.
- **Isolate state**: Ensure the test clearly sets up the necessary register values before executing the target instruction.

### Handling Undefined Flags

Many x86 instructions leave specific status flags (e.g., `AF`, `OF`) in an undefined state. To prevent test flakes, use a preamble to exclude these flags from the comparison:
```
# Undefined flags: sf, zf, af, pf

movq $100, %rax
movq $7, %rbx
mulq %rbx 
```
Note: Always consult the [instruction manual](https://www.felixcloutier.com/x86/) to identify which flags are architecturally undefined for a given instruction.

## Running Tests

Ensure you have `binutils` (specifically `as` and `ld`) installed. Currently, the test suite is verified on **Ubuntu (latest)**; other platforms may produce incompatible results.

### Execution Commands
```bash
# Run all tests
python3 Kraken/X64/Test/asm_tests.py Kraken/X64/Test/asm

# Run a specific test
python3 Kraken/X64/Test/asm_tests.py Kraken/X64/Test/asm/test_arithmetic.S

# Manual inspection of Kraken output
./.lake/build/bin/krakenrunner_x64 Kraken/X64/Test/asm/test_arithmetic.S
```