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

`fuzz_x64.py` checks Kraken's semantics against the host using semi-random sequences of
instructions. These sequences start with random register values, end by fixing up any
nondeterministic flags, and sandwich instructions that:

  * are generally equally distributed among mnemonics
    * `rep` + a mnemonic counts as a new unique mnemonic
    * `addr32` does not make a mnemonic unique
    * condition codes distinguish mnemonics
  * are well-behaved
    * they assemble
    * they do not fault
    * they do not take branches
    * they do not rely on nondeterministic state

Various instruction forms for each mnemonic are included in the random pool.

### Default run

```bash
python3 Kraken/X64/Test/fuzz_x64.py --batches 3 --batch-size 100 --length 12
```
```
pool: 189 mnemonics
batch 1/3: 100 seqs, 71 seq/s, 0 failures
batch 2/3: 200 seqs, 69 seq/s, 0 failures
batch 3/3: 300 seqs, 69 seq/s, 0 failures
never accepted into a sequence (jumps, or every form faults): call, jmp, movzbq, movzbw, movzwl, rep stosw, ret
least run: rep movsq (2), popw (2), popq (2), movsb (2), movsl (3)
```

If any sequence of instructions fails, the tool exits with nonzero status and prints the sequence
and the disagreeing state.

### Focused run: `--only`

`--only` takes comma-separated prefixes and restricts the pool to the mnemonics that start with one
of them. `rep` selects the eight `rep` forms; `movs` selects `movsb` to `movsq` (and `movsbl`,
`movslq`, `movsx`, …) but not `rep movsb`. A focused pool is built from more rounds of generation
(64 instead of 8), so even a rarely generated mnemonic gets a varied set of forms. This is most
useful when you're adding a new instruction or adjusting the semantics of an existing one (or maybe
testing things out on a new emulator or hardware).

```bash
python3 Kraken/X64/Test/fuzz_x64.py --batches 2 --batch-size 100 --only pshuf,palignr
```
```
pool: 3 mnemonics matching pshuf,palignr
batch 1/2: 100 seqs, 39 seq/s, 0 failures
batch 2/2: 200 seqs, 39 seq/s, 0 failures
least run: palignr (790), pshufd (802), pshufb (808)
```

In this run, two hundred sequences of (the default) twelve instructions gave each of the three
mnemonics about 800 runs, with random `xmm` contents from the seeding at the start of every sequence.

In the full run above, `movzbq` never appeared in a sequence. We can run it in its own pool:

```
$ python3 Kraken/X64/Test/fuzz_x64.py --batches 1 --batch-size 100 --only movzbq
pool: 1 mnemonics matching movzbq
batch 1/1: 100 seqs, 28 seq/s, 0 failures
least run: movzbq (367)
```

Every prefix has to match a mnemonic in the pool of every batch; otherwise the run stops with exit
status 2. `addr32` is not part of any mnemonic, so it matches nothing:

```
$ python3 Kraken/X64/Test/fuzz_x64.py --only lea,addr32
seed 42: no assemblable instruction has a mnemonic starting with addr32
```

### Generator CLI

The Python driver uses two runner commands, which can also be called directly. Both read JSON from
stdin:

```bash
# Generate sequences of instructions.
echo '{"seed": 42, "count": 100, "length": 12, "only": []}' \
  | ./.lake/build/bin/krakenrunner_x64 --generate > generated.json

# Run Kraken's semantics on sequences of instructions.
python3 -c 'import json; print(json.dumps(json.load(open("generated.json"))["seqs"]))' \
  | ./.lake/build/bin/krakenrunner_x64 --batch
```

A request with `"count": 0` lists the mnemonics that would be used without generating sequences:

```
$ echo '{"seed": 42, "count": 0, "length": 12, "only": ["pshuf", "palignr"]}' | ./.lake/build/bin/krakenrunner_x64 --generate
{"pool":["palignr","pshufb","pshufd"],"runs":{},"seqs":[]}
```

The generator is derived from the constructors of `Instr` (`gen_ctors%` in `KrakenRunnerX64.lean`),
so a new instruction normally enters the pool as soon as the assembler accepts its printed form. If
it is missing from `"pool"` (and the generator actually produced it), every generated form of it
was rejected by `as`, which usually means that there is something wrong with the printer, or
that it needs an operand kind that the generator doesn't produce.
