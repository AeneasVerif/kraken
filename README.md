# Kraken

Kraken is a Lean framework for verifying assembly programs, either hand-written
(`.S` files), or disassembled from compiler output (`.o` files). We currently
support x64, aarch64, and have plans for risc-v.

We emphasize careful design, well-audited semantics, and excellent proof
automation. Our work on prover performance and automation has led to numerous
improvements in upstream Lean, such as `SymM`, `grind hom`, and improvements in
`vcgen` as well.

The largest program we have processed to date is over 10,000 instructions, and
we continue to scale up.

Kraken is a joint project between the Lean FRO, Google, and INRIA.

## Design

The distinguishing features of Kraken are as follows.
- We verify code that is one level of abstraction above binary code, i.e.,
  before the assembly and linking steps. This means we do not make any concrete
  assumptions about program layouts, instruction sizes, or memory addresses --
  we can reason about a library in the abstract, without making assumptions
  about how it will be laid out in memory.
- We emphasize proof efficiency: we investigate agent-generated proofs and
  tweak automation to leverage e.g. `grind`, rather than have low-level manual
  proofs that break at the slightest change in input ASM.
- We evolve Lean to support better automation for program proof: `SymM` and `grind
  hom` are joint work between Google and the Lean FRO, and we are currently
  collaborating on connecting our semantics to `mvcgen`.
- Our semantics are carefully designed, by hand, to support both efficient
  testing and theorem proving.

## Status

We are currently connecting Kraken to `mvcgen` to leverage the automation and
program proof facilities provided by Lean itself. The latest snapshot is on
[Sebastian Graf's branch](https://github.com/sgraf812/kraken/blob/vcgen/), and
this is where we managed to scale past 10,000 instructions -- using agents, of
course.

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
