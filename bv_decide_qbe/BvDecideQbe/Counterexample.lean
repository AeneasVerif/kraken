module

public import BvDecideQbe.Encode
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Tactic.BVDecide.Bitblast.EfficientEval
public import Std.Data.HashMap
public import Lean.Expr
public import Lean.Data.RArray

/-!
# Direct SAT Counterexample Decoding and Validation (`S3a`)

Decodes a SAT model `ByteArray` returned by `SolveResult.sat model` directly at
`model[atomBase[k] + j]` into `Std.Tactic.BVDecide.BVExpr.Assignment` (`PackedBitVec`s) with
zero Lean bitblasting, and validates every assignment with `BVLogicalExpr.evalEfficient`.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Std.Tactic.BVDecide

/-- Decode a little-endian `width`-bit `Nat` value starting at `model[base .. base + width)`.
Out-of-bounds bits (e.g. `ByteArray.empty` for trivial SAT) default to `0`. -/
def decodeSlotValue (model : ByteArray) (base width : Nat) : Nat := Id.run do
  let mut val : Nat := 0
  for j in [0:width] do
    let idx := base + j
    if h : idx < model.size then
      if model[idx] != 0 then
        val := val ||| (1 <<< j)
  return val

/-- Decode all `(bvIdx, PackedBitVec)` entries from `(varTable, atomBase, model)`. -/
def decodeVarValues (varTable : Array (Nat × Nat)) (atomBase : Array Nat)
    (model : ByteArray) : Array (Nat × BVExpr.PackedBitVec) := Id.run do
  let n := min varTable.size atomBase.size
  let mut out : Array (Nat × BVExpr.PackedBitVec) := Array.emptyWithCapacity n
  for h : k in [0:n] do
    have hk1 : k < varTable.size := Nat.lt_of_lt_of_le h.upper (Nat.min_le_left _ _)
    have hk2 : k < atomBase.size := Nat.lt_of_lt_of_le h.upper (Nat.min_le_right _ _)
    let (bvIdx, width) := varTable[k]
    let base := atomBase[k]
    let rawVal := decodeSlotValue model base width
    out := out.push (bvIdx, ⟨BitVec.ofNat width rawVal⟩)
  return out

private def dedupSortedPairs (sorted : Array (Nat × BVExpr.PackedBitVec)) :
    Array (Nat × BVExpr.PackedBitVec) := Id.run do
  let mut out : Array (Nat × BVExpr.PackedBitVec) := Array.emptyWithCapacity sorted.size
  for entry in sorted do
    if h : 0 < out.size then
      let last := out[out.size - 1]
      if last.1 == entry.1 then
        if entry.2.w > last.2.w then
          out := out.set (out.size - 1) entry
      else
        out := out.push entry
    else
      out := out.push entry
  return out

private def rarrayOfSortedAux (xs : Array (Nat × BVExpr.PackedBitVec))
    (lo hi : Nat) (hlo : lo < hi) (hhi : hi ≤ xs.size) : BVExpr.Assignment :=
  if h : lo + 1 = hi then
    .leaf xs[lo].2
  else
    let mid := (lo + hi) / 2
    .branch xs[mid].1
      (rarrayOfSortedAux xs lo mid (by omega) (by omega))
      (rarrayOfSortedAux xs mid hi (by omega) hhi)

/-- Build a balanced `BVExpr.Assignment` (`Lean.RArray BVExpr.PackedBitVec`) keyed by `bvIdx`,
supporting arbitrary sparse variable indices without dense array allocation. -/
def assignmentOfPairs (pairs : Array (Nat × BVExpr.PackedBitVec)) : BVExpr.Assignment :=
  if pairs.isEmpty then
    .leaf ⟨BitVec.ofNat 0 0⟩
  else
    let sorted := pairs.qsort (fun a b => a.1 < b.1)
    let dedup := dedupSortedPairs sorted
    if h : 0 < dedup.size then
      rarrayOfSortedAux dedup 0 dedup.size h (Nat.le_refl _)
    else
      .leaf ⟨BitVec.ofNat 0 0⟩

/-- Decode `SolveResult.sat model` directly into `Std.Tactic.BVDecide.BVExpr.Assignment`. -/
def decodeAssignment (varTable : Array (Nat × Nat)) (atomBase : Array Nat)
    (model : ByteArray) : BVExpr.Assignment :=
  assignmentOfPairs (decodeVarValues varTable atomBase model)

/-- Validate an assignment against `expr` using `BVLogicalExpr.evalEfficient`. -/
def validateAssignment (expr : BVLogicalExpr) (assign : BVExpr.Assignment) : Bool :=
  EfficientEval.BVLogicalExpr.evalEfficient assign.get expr

/-- Decode `model` from `(enc.varTable, enc.atomBase)` and validate via
`BVLogicalExpr.evalEfficient`. Returns `none` if `evalEfficient` rejects the decoded assignment. -/
def decodeAndValidate (expr : BVLogicalExpr) (enc : EncodedProg) (model : ByteArray) :
    Option BVExpr.Assignment :=
  let assign := decodeAssignment enc.varTable enc.atomBase model
  if validateAssignment expr assign then
    some assign
  else
    none

/-- Decode `model`, validate via `BVLogicalExpr.evalEfficient`, and reconstruct
`(Expr × Bool × BVExpr.PackedBitVec)` equations for `Lean.Meta.Tactic.BVDecide.CounterExample`.
Fails with an error if `evalEfficient` returns `false` or an atom ID is missing from
`atomsAssignment`. -/
def reconstructValidatedCounterExampleCore (expr : BVLogicalExpr)
    (varTable : Array (Nat × Nat)) (atomBase : Array Nat)
    (model : ByteArray) (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) :
    Except String (BVExpr.Assignment × Array (Expr × Bool × BVExpr.PackedBitVec)) := do
  let pairs := decodeVarValues varTable atomBase model
  let assign := assignmentOfPairs pairs
  if !validateAssignment expr assign then
    throw "decoded SAT model failed BVLogicalExpr.evalEfficient validation"
  let mut seen : Std.HashMap Nat BVExpr.PackedBitVec := {}
  let mut eqs : Array (Expr × Bool × BVExpr.PackedBitVec) := #[]
  for (bvIdx, packed) in pairs do
    if !seen.contains bvIdx then
      seen := seen.insert bvIdx packed
      match atomsAssignment.get? bvIdx with
      | some (_, atomExpr, synthetic) =>
        eqs := eqs.push (atomExpr, synthetic, packed)
      | none =>
        throw s!"decoded variable index {bvIdx} missing from atomsAssignment"
  for (atomId, (width, atomExpr, synthetic)) in atomsAssignment do
    if !seen.contains atomId then
      eqs := eqs.push (atomExpr, synthetic, ⟨BitVec.ofNat width 0⟩)
  return (assign, eqs)

/-- Convenience wrapper over `reconstructValidatedCounterExampleCore` for `EncodedProg`. -/
def reconstructValidatedCounterExample (expr : BVLogicalExpr) (enc : EncodedProg)
    (model : ByteArray) (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) :
    Except String (BVExpr.Assignment × Array (Expr × Bool × BVExpr.PackedBitVec)) :=
  reconstructValidatedCounterExampleCore expr enc.varTable enc.atomBase model atomsAssignment

end BvDecideQbe
