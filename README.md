# Kraken

## Reviewing semantics

All changes to semantics should be thoroughly checked against the [Intel SDM](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf) by two maintainers. As a maintainer proposing a change, please review your own edits and flag TODOs for anything not corroborated by an authoritative reference.

Here are some common but easy-to-forget considerations to look out for:

- Some operations have multiple outputs -- and all effects observable through modeled state need to be captured correctly
- Outputs may be implicit (not apparent from the syntax), for example to flag registers or for the high half of a function with double-wide output
- Multiple destinations of the same kind (e.g. registers or memory), if one or more of these is selectable, need a decisiion about which write wins if the same destination is selected
- For operations that write to registers and memory, are do the writes to registers affect the calculation of the destination address?
- When accessing memory, what width is used for code-address computations?
- For control instructions, what width is used for code-address computations?
- When using different-width inputs, is the shorter one sign-extende or zero-extended?
- When computing immediates during assembly, is there overflow, at what width, and is it signed or unsigned?
- Can the isntruction trap or raise an exception or fault?

## X64 model scope

The x64 model is intended for verifying sequential software that performs computations using common registers and memory. Operating-systems features, concurrency, and I/O are currently out of scope.

Included
- 64-bit mode, incljuding 32-bit and smaller operations available in this mode
- All 64-bit registers
- [Partial-register access](https://en.wikipedia.org/wiki/X86#Structure)
- Status flags
- Memory access, including avoidance of faults
- ADX, BMI, BMI2, and similar extensions
- Assembler features: labels (relative and absolute references), arithmetic on immediates, rodata

Excluded
- Non-8-byte-aligned memory access (for now, to support eventually)
- Handling of exceptions and faults
- Virtual memory
- Segment registers
- MSRs
- Other execution modes, such as 32-bit and 16-bit modes
- Mutable globals (bss and data)

### Incidental extensions to x64

While the model is centrally a subset of real x64, we do not go out of our way to model whether particular cobinations of operands are encodable, and instead give semantics to some instructions that cannot be assembled. For example, a `mov` from memory to memory is interpreted in the obvious way, even though an assembler would reject it. (We do model restrictions on operands where they simplify the semantics, e.g. entirely ruling out a memory operand in a particular position to make its evaluation infallible). However, we want to maintain the standard that if code proven against our semantics assembles for a real x64 target, then it will satisfy the proven specification. Thus we must make sure the incidental extensions to x64 do not clash with actual features of x64, or undefined behavior in x64 (e.g. bswap r16).
