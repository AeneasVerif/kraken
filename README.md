# Kraken

## X64 model scope

The x64 model is intended for verifying sequential software
that performs computations using common registers and memory.
Operating-systems features, concurrency, and I/O are currently out of scope.

Included
- 64-bit mode, incljuding 32-bit and smaller operations available in this mode
- All 64-bit registers and [partial-register access](https://en.wikipedia.org/wiki/X86#Structure)
- Status flags
- Memory access, including avoidance of faults
- ADX, BMI, BMI2, and similar extensions
- Assembler features: labels, arithmetic on immediates, rodata

Excluded
- Non-8-byte-aligned memory access (for now, to support eventually)
- Handling of exceptions and faults
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

More guidance on revieweing semantics is in [CONTRIBUTING.md](CONTRIBUTING.md).
