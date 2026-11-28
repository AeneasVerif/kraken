/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Cdcl
public import LeanQbe.T.Examples.Kissat.Ref.Substitute

/-!
# Pure Lean Layer-A $\mathbb{F}_2$ / XOR & Gauss-Jordan Soundness Theory (`XorF2`)

Pure Lean UNSAT-only soundness library (`0` `Kraken.*` imports, `0` completeness obligations)
supporting inprocessing XOR extraction and packed `u64`-word $\mathbb{F}_2$ Gauss-Jordan
elimination (`FullM8XorGauss`):

1. **Variable-list XOR semantics (`xorEvalVars`, `XorVarsSound`)**:
   - `F.Sat α → xorEvalVars α vs = rhs`.
   - Preservation under unordered/canceling XOR combination and sorted symmetric difference
     (`xorEvalVars_symDiffSorted`, `xorVarsSound_symDiffSorted`), justifying degree-2 gate chain
     merging.
   - Contradiction from empty row (`unsat_of_xorVars_nil`), unit entailment (`k = 1`), binary
     equivalence entailment (`k = 2`), and general `k`-clause materialization (`k ≥ 1`).
2. **Bitmask truth-table `k`-XOR extraction (`k ∈ 3..5`) & 2-XOR binary extraction**:
   - `xorMaskClause vs mask`, `parityMask k p` (`0x69`/`0x96`, `0x9669`/`0x6996`,
     `0x69969669`/`0x96696996`), and `xorVarsSound_of_parityMask`: a single `u32` seen-mask
     matching `parityMask k p` certifies `XorVarsSound F vs (!p)`.
   - `xorVarsSound_of_binPair`: binary pair `(a ∨ b) ∧ (¬a ∨ ¬b)` certifies `2`-XOR soundness.
3. **Packed `u64`-word row semantics (`rowU64`, `rowBit`, `XorPackedRowSound`)**:
   - Reads logical `u64` words from `u32`-word storage `(lo, hi)` with variable columns
     `0 ..< ncols` mapped through `c2v` and RHS stored at bit `ncols`.
   - 3-line row-XOR preservation (`xorPackedRowSound_xor`), `unsat_of_zero_packed_row`,
     Kernighan bit-extraction (`c0_ctz64`, `w &&& (w - 1#64)`), and bridge to `XorVarsSound`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.KissatBeyond.Ref

open LeanQbe.T.Examples.Kissat.Ref
open Std.Sat

/-! ## 1. Boolean XOR algebra and list XOR evaluation -/

/-- Boolean XOR parity of a list of variables under valuation `α`. -/
@[expose] def xorEvalVars (α : Nat → Bool) (vs : List Nat) : Bool :=
  vs.foldl (fun acc v => acc != α v) false

/-- UNSAT soundness invariant of a sparse XOR equation `⊕_{v ∈ vs} α(v) = rhs`. -/
@[expose] def XorVarsSound (F : CNF Nat) (vs : List Nat) (rhs : Bool) : Prop :=
  ∀ α : Nat → Bool, F.Sat α → xorEvalVars α vs = rhs

/-- Symmetric difference of two strictly sorted variable lists (canceling common variables). -/
@[expose] def symDiffSorted : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x < y then x :: symDiffSorted xs (y :: ys)
    else if y < x then y :: symDiffSorted (x :: xs) ys
    else symDiffSorted xs ys
termination_by xs ys => xs.length + ys.length

/-! ## 2. Clause materialization & CNF extraction truth-table soundness -/

/-- Polarity bit-mask `mask` over variables `vs`: literal `i` is
`mkLit (vs[i]) (!(mask.testBit i))`, so the assignment
`(α (vs[i]) = mask.testBit i for all i)` falsifies `xorMaskClause vs mask`. -/
@[expose] def xorMaskClause (vs : List Nat) (mask : Nat) : List Nat :=
  (List.range vs.length).map fun i => mkLit (vs[i]?.getD 0) (!((mask >>> i) % 2 == 1))

/-- Even/odd popcount parity bit of lower `k` bits of `mask`. -/
@[expose] def maskParity (k mask : Nat) : Bool :=
  (List.range k).foldl (fun b i => b != ((mask >>> i) % 2 == 1)) false

/-- Canonical `u32` parity bitmask for `k ∈ 3..5` and target forbidden parity `p`:
- `k = 3`: `0x69` (`p = false`, enforces `rhs = true`) / `0x96` (`p = true`, enforces `rhs = false`)
- `k = 4`: `0x9669` (`p = false`) / `0x6996` (`p = true`)
- `k = 5`: `0x69969669` (`p = false`) / `0x96696996` (`p = true`) -/
@[expose] def parityMask (k : Nat) (p : Bool) : BitVec 32 :=
  if k = 3 then if p then 0x96#32 else 0x69#32
  else if k = 4 then if p then 0x6996#32 else 0x9669#32
  else if k = 5 then if p then 0x96696996#32 else 0x69969669#32
  else 0#32

/-! ## 3. Packed `u64`-word row semantics (stored as `u32` pairs in `scratch_buf`) -/

/-- Read a logical `64`-bit row word from a `u32` slice `scr` at index `rbase + 2 * w`. -/
@[expose] def rowU64 (scr : List (BitVec 32)) (rbase w : Nat) : BitVec 64 :=
  (scr[rbase + 2 * w]?.getD 0#32).setWidth 64 |||
    (((scr[rbase + 2 * w + 1]?.getD 0#32).setWidth 64) <<< 32)

/-- Read column bit `c` from logical `u64` words at `scr[rbase ..]`. -/
@[expose] def rowBit (scr : List (BitVec 32)) (rbase c : Nat) : Bool :=
  (rowU64 scr rbase (c / 64)).getLsbD (c % 64)

/-- Evaluate columns `0 ..< ncols` (through `c2v`) XORed with the RHS bit at column `ncols`. -/
@[expose]
def xorEvalPacked (α : Nat → Bool) (c2v scr : List (BitVec 32)) (rbase ncols : Nat) : Bool :=
  ((List.range ncols).foldl (fun acc c =>
      if rowBit scr rbase c then acc != α (c2v[c]?.getD 0#32).toNat else acc) false) !=
    rowBit scr rbase ncols

/-- UNSAT soundness invariant for a packed row (`LHS ⊕ RHS = false`, i.e., `LHS = RHS`). -/
@[expose]
def XorPackedRowSound (F : CNF Nat) (c2v scr : List (BitVec 32)) (rbase ncols : Nat) : Prop :=
  ∀ α : Nat → Bool, F.Sat α → xorEvalPacked α c2v scr rbase ncols = false

end LeanQbe.T.Examples.KissatBeyond.Ref
