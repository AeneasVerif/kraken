# Some notes on the design of Kraken

## Current executable boundary

Kraken currently treats assembly layout as post-assembly input. A `Program` is
a list of parsed directives; a `Layout` supplies a base address and an encoded
size for each list position; applying it produces an `Executable`. The core
instruction semantics do not attempt to verify an assembler or linker.

`Executable.locatedDirectives` computes one explicit location for every source
directive by advancing a cursor by each encoded size. Its main consumers have
different granularities:

- `labels` resolves a label to its directive's starting address.
- `fetch?` skips zero-sized labels and selects at most one non-label directive
  whose starting address equals the current program counter.
- `step` interprets that one directive over its half-open address range.
- `straightline` interprets the suffix beginning at the current address until
  control flow transfers or the suffix ends.

This keeps labels, instruction starts, instruction stops, and source-list
positions distinct. Multiple consecutive labels assigned size zero remain
supported and resolve to the same address.

The layout itself is still a trust boundary. Concrete verification examples
should obtain sizes from assembled code and check them against the Lean list,
as `Kraken/Examples/check_sum_to_n.py` does. Formally verified assembly or
linking would require an additional correspondence theorem and is not part of
the instruction-step semantics.

This design deliberately leaves unrelated behavior unchanged: a missing
instruction at the current address returns the current state to the
continuation, and a missing label resolves to `-1`. Explicit execution faults
and proof-carrying label/layout invariants are separate possible extensions.

## Earlier design motivation

Unlike prior work, we do not want to rely on the invariant that every potential
jump location comes with a label. (Because, among other things, we want to stick
to assembly source as it is written, and we want to deal with cases that are
found in the wild, such as multiple identical consecutive labels.)

We have two concepts:

- a position, which is used by the semantics to indicate where we are in the
  program execution (think of it as a symbolic program counter) and
- a layout, which maps a position to an actual address (unknown at proof-time)

We allow a wide variety of rip-relative jump destinations, relying on two
special constructors in our semantics: `.{before,after}_current_instruction`.
Those constructors are thus interpreted in the semantics as `layout p` and
`layout p.next` -- they evaluate to the location in memory of the current
instruction pointer, and past the current current instruction.

This design makes modularity difficult, as in: we want to prove that if `p1` and
`p2` execute independently, then their concatenation also executes identically.
This is because we would need separation lemmas to express that layouts of `p1`
and `p2` do not overlap, and that the semantics of `p1` and `p2` could not
possibly rely on "talking" about concrete locations (layout) past their
footprint. At a meta-theoretical level, this seems valid, but conducting this
proof concretely seems nebulous.

But we notice that the only calls to layout are ever of the form `layout p` and
`layout p.next` (or `layout ("label", 0)` for known static labels), meaning that
we do not actually need to pass a layout *function* to the semantics; we simply
need to evaluate the semantics in a context where we have access to the address
of the current PC, and the address past the current instruction pointed to by
the PC.

FIXME: what about the case of static labels?

Thus, if we rewrite our semantics to take two *values*, then the composition of
two programs boils down to proving a "shifting" lemma, which is that running the
outer parts of the semantics (straightline, etc.) over `p1 ++ p2` boils down to
running the semantics on `p1` and `p2`, where the virtual program counter is
offset by `p1.length` for `p2`. Because the usage of the virtual program counter
(i.e., the position) is confined to the outer three functions (`eval`,
`straightline`, `straightline'`), this shifting lemma should be easy to
establish.

This now means that we are no longer beholden to using relative positions for
the outer parts of the semantics (via the pair `Label × Nat`), we could simply
use indices into the directive list to simplify the machinery.
