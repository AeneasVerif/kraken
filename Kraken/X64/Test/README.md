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
Note: Always consult the [Intel SDM](https://intel.github.io/SDM/sdm.html) to identify which flags are architecturally undefined for a given instruction.

### Vector registers

Under Intel SDE, or natively on a host with AVX-512F, the runner compares all of `zmm0` to `zmm31`; native execution on other hosts compares `ymm0` to `ymm15`.

A test that needs AVX-512 says so on one of its comment lines:
```
# Requires: avx512f
```
On hosts without AVX-512F, native execution is skipped and the test still runs under Intel SDE (skipping altogether only with `--skip-sde`).

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
## Differential Fuzzing

`fuzz_x64.py` runs random instruction sequences on the host and compares the final register, flag
and vector state with Kraken's prediction. Each batch asks `krakenrunner_x64 --generate` for its
sequences; the generator builds a **pool** of random instructions that the assembler accepts,
**grouped by mnemonic**, keeping up to 64 distinct operand forms per mnemonic. A sequence draws a
mnemonic uniformly and then one of its forms (retrying within the mnemonic if a form faults or is
non-deterministic), so every mnemonic is run about equally often, however many syntactic forms it
has and however rarely the random generator happens to produce it.

The unit of fairness is the printed AT&T mnemonic: each width (`addb`, `addw`, `addl`, `addq`) and
each condition code (`seta`, `setb`, …) is its own group. A condition-code instruction therefore
gets sixteen shares of the run and a vector instruction one, so `setcc` and `cmovcc` together take
a large share of the instructions.

A prefix the printer puts in front of the name is part of the mnemonic, except an address-size
prefix: `rep movsb` is its own mnemonic, because `rep` changes what the instruction does, while
`addr32 rep movsb` is one of the forms of `rep movsb`, as `(%eax)` versus `(%rax)` is a form of any
memory instruction (`x64Mnemonic` in `KrakenRunnerX64.lean`). Most `rep` forms run with a zero
count, since `rcx` is usually zero or large after seeding, and do nothing.

### Default run

```bash
python3 Kraken/X64/Test/fuzz_x64.py --batches 3 --batch-size 100 --length 12
```
```
pool: 190 mnemonics
batch 1/3: 100 seqs, 67 seq/s, 0 failures
batch 2/3: 200 seqs, 67 seq/s, 0 failures
batch 3/3: 300 seqs, 57 seq/s, 0 failures
never accepted into a sequence (jumps, or every form faults): call, jmp, movzbq, movzbw, movzwl, rep stosw, ret
least run: rep movsq (2), popw (2), popq (2), movsb (2), movsl (3)
```

The first line is the size of the pool. The last two name the pool mnemonics that were never, or
least often, accepted into a sequence; the counts come from the generator and leave out the
register seeding. `call`/`jmp`/`ret` are never accepted because the fuzzer runs straight-line code
only. `movzbq`, `movzbw` and `movzwl` are mnemonics the generator rarely produces, so the pool holds
only a few forms of them, and here those few all touch unmapped memory. A string instruction is
accepted only when its pointers and count are usable, so `rep stosw` and the other string forms
land on these lines often in a short run. A mnemonic you expect to be exercised showing up on these
lines is the signal to give it a focused run. A `[FAIL]` block prints the sequence and the
differing state; the exit status is 1 if any sequence failed.

### Focused run: `--only`

`--only` takes comma-separated mnemonic prefixes and restricts the pool to the mnemonics that start
with one of them, or have a word that does: `movs` selects `movsb` and `rep movsb`, `rep` selects
the `rep` forms, and `rep movs` only `rep movsb` to `rep movsq`. `addr32` selects nothing, since it
is not part of any mnemonic. A focused pool is built from more rounds of generation (64 instead of
8), so even a rarely generated mnemonic gets a varied set of forms. Use it when adding or changing
an instruction:

```bash
python3 Kraken/X64/Test/fuzz_x64.py --batches 2 --batch-size 100 --only pshuf,palignr
```
```
pool: 3 mnemonics matching pshuf,palignr
batch 1/2: 100 seqs, 60 seq/s, 0 failures
batch 2/2: 200 seqs, 53 seq/s, 0 failures
least run: palignr (782), pshufb (802), pshufd (816)
```

Two hundred sequences of twelve instructions gave each of the three mnemonics about 800 runs, with
random `xmm` contents from the seeding at the start of every sequence. The `movzbq` that the default
run never accepted has 24 forms in a focused pool, against 2 in the default pool for seed 0:

```
$ python3 Kraken/X64/Test/fuzz_x64.py --batches 1 --batch-size 100 --only movzbq
pool: 1 mnemonics matching movzbq
batch 1/1: 100 seqs, 28 seq/s, 0 failures
least run: movzbq (367)
```

A prefix that matches nothing is an error (exit status 2):

```
$ python3 Kraken/X64/Test/fuzz_x64.py --only nosuch
no assemblable instruction has a mnemonic matching nosuch (see --mnemonics)
```

### Inspecting the pool: `--mnemonics`

`krakenrunner_x64 --mnemonics [<prefixes>]` builds the pool (for seed 0) and prints each mnemonic
with the number of distinct forms it holds, up to 64:

```
$ ./.lake/build/bin/krakenrunner_x64 --mnemonics | head -5
adcb 46
adcl 57
adcq 64
adcw 64
adcx 64
$ ./.lake/build/bin/krakenrunner_x64 --mnemonics pshuf,palignr
palignr 64
pshufb 64
pshufd 64
$ ./.lake/build/bin/krakenrunner_x64 --mnemonics "rep movs"
rep movsb 2
rep movsl 2
rep movsq 2
rep movsw 2
```

A newly added instruction is picked up automatically if it is a constructor of `Operation` or
`AvxOperation`: it appears in `--mnemonics` as soon as the assembler accepts the printed form. A
count well below 64 means the generator rarely produces an assemblable form of it (it is still
drawn as often as the others, from fewer forms); its absence means every generated form was
rejected by `as`, which usually points at the printer or at an operand kind the generator never
produces.

### Generator CLI

The Python driver uses two runner commands, which can also be called directly:

```bash
# <count> sequences of <length> pool instructions each (after 4 register seeds), as
# {"seqs": [...], "runs": {mnemonic: count}}, "runs" counting the instructions drawn per mnemonic
./.lake/build/bin/krakenrunner_x64 --generate <seed> <count> <length> [<prefixes>] > sequences.json
# Kraken's prediction for each sequence, read from stdin as --generate's output or a bare JSON array
./.lake/build/bin/krakenrunner_x64 --batch < sequences.json
```
