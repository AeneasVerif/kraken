# Kraken

Kraken provides executable Lean models and proof infrastructure for x86-64 and
AArch64 assembly.

## Compiler-to-proof example

The `sum_to_n` example verifies the same functional specification on both
architectures. Clang compiles one shared GNU C function to checked-in x86-64
and AArch64 assembly. Lean parses each artifact and proves, for every 64-bit
input, that execution reaches the return instruction with the unsigned sum in
the architecture's return register (`rax` or `x0`). Arithmetic is modulo
`2^64`, as it is for C's `uint64_t`. The source contains an empty volatile
assembly statement that emits no instruction but keeps the proof-oriented loop
from being replaced by a closed-form optimization.

The proofs are in
[`Kraken/X64/Examples/SumToN.lean`](Kraken/X64/Examples/SumToN.lean) and
[`Kraken/AArch64/Examples/SumToN.lean`](Kraken/AArch64/Examples/SumToN.lean).
Their architecture-independent `Eventually` machinery lives in
[`Kraken/OmniSemantics.lean`](Kraken/OmniSemantics.lean).

The artifact checker recompiles the C source, compares exact instruction
offsets and encodings with the checked-in assembly, and checks that the
assembler-derived instruction sizes match the layout used by Lean:

```shell
python3 Kraken/Examples/check_sum_to_n.py --arch x64
python3 Kraken/Examples/check_sum_to_n.py --arch aarch64 \
  --objdump aarch64-linux-gnu-objdump
```

The Lean theorems verify the parsed, checked-in assembly under Kraken's
semantics. The artifact checker establishes reproducible compiler provenance;
it is not a proof of Clang, the assembler, the parser, or Kraken's instruction
semantics. Both theorems stop with the program counter at the return
instruction rather than executing the caller-dependent return itself.

## Executable layout and stepping

An `Executable` consists of parsed directives plus a base address and one
encoded size per directive. `Executable.locatedDirectives` assigns every source
directive its actual starting address and half-open address range. In a
well-formed layout labels have size zero, so any number of labels may alias the
following instruction.

`Executable.step` fetches the first non-label directive beginning exactly at
the machine's program counter and interprets only that directive. In contrast,
`Executable.straightline` continues through successive directives until a jump
or the end of the supplied suffix. The layout is currently trusted post-assembly
input; the compiler example checks its concrete layouts against assembled
machine code.

## X64 model scope

The x64 model is intended for verifying sequential software
that performs computations using common registers and memory.
Operating-systems and concurrency features currently out of scope.

Included

- 64-bit mode, including 32-bit and smaller operations available in this mode
- All 64-bit registers and [partial-register access](https://en.wikipedia.org/wiki/X86#Structure)
- Status flags
- Memory access, including avoidance of faults
- ADX, BMI, BMI2, and similar extensions
- Assembler features: labels, arithmetic on immediates, rodata

Excluded

- Handling of most exceptions and faults
- Virtual memory
- Segment registers
- MSRs
- Other execution modes, such as 32-bit and 16-bit modes
- Mutable globals (bss and data)

### Incidental extensions to x64

While the model is centrally a subset of x64, we work with assembly, and
we do not seek to model [which assembly programs are encodable](https://godbolt.org/z/Mb5YzbxMG),
and instead give semantics to some instructions that cannot be assembled.
For example, a `mov` from memory to memory is interpreted in the obvious way,
even though an assembler would reject it.
(We do model restrictions on operands where they simplify the semantics,
e.g. entirely ruling out a memory operand in a particular position
to make its evaluation infallible).
However, if code proven against our semantics assembles for a real x64 target,
we want to be sure that it will satisfy the proven specification.
Thus incidental extensions to x64 must not clash with actual features of x64,
or undefined behavior in x64 (e.g. bswap r16).

More guidance on reviewing semantics is in [CONTRIBUTING.md](CONTRIBUTING.md).
