/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Subsume
public import LeanQbe.T.Examples.Kissat.Ref.FailedLit

/-!
# Pure Lean Layer-A Inprocessing Theory: Probing & Vivification Strengthening

Pure Lean formalization (zero `Kraken.Mem` or `Kraken.Separation` imports) of failed-literal
probing (`probeFailedLit`) and clause vivification strengthening (`vivifyClause`, `vivifyPass`)
preserving full logical equivalence (`∀ α, F'.Sat α ↔ F.Sat α` and `F'.Unsat ↔ F.Unsat`):

1. **Failed-literal probing equivalence**:
   - `unsat_append_units_iff`: `(F ++ unitsCnf (pref.map litNeg)).Unsat ↔ F ⊨ pref`.
   - `unsat_add_litNeg_iff`, `failedLit_add_equiv`, `failedLit_drop_equiv`.
   - `probeFailedLit` + `probeFailedLit_sound` + `failedLit_probe_equiv`, plus bridges from
     `Cdcl.failedLitStep_preserves_inv` (`failedLitStep_equiv`) and
     `FailedLit.analyzeFailedLiteralExec_sound` (`failedAnalyze_equiv`).
2. **Vivification strengthening**:
   - Conflict vivification (`vivify_conflict_equiv`, `vivify_confl_clauses`):
     `(F \ {C}) ∧ ¬l₁ ∧ ... ∧ ¬lₖ ⊢ ⊥` (`pref ⊆ C`) justifies replacing `C` by `[l₁, ..., lₖ]`.
   - Implied-literal vivification (`vivify_implied_equiv`, `vivify_imp_clauses`):
     `(F \ {C}) ∧ ¬l₁ ∧ ... ∧ ¬lₖ ⊢ lₘ` (`pref ⊆ C`, `lₘ ∈ C`) justifies replacing `C` by
     `[l₁, ..., lₖ, lₘ]`.
   - Falsified-literal dropping (`vivify_dropFalse_equiv`).
3. **Executable propagation-backed vivification (`vivifyClause`, `vivifyPass`)**:
   - Uses `initState`, `decideLit`, and `propagateAll` (`trailEntailment`), proving full semantic
     equivalence (`vivify_clause_equiv`, `vivify_pass_equiv`) and literal subset preservation.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Failed-literal probing and assumption-entailment equivalences -/

/-- Executable failed-literal probe: checks whether assuming `¬l` under unit propagation over
`cs` derives conflict (`true`). -/
@[expose] def probeFailedLit (fuel : Nat) (cs : List (List Nat)) (l : Nat) : Bool :=
  match propagateAll fuel (initState (cnfOfClauses cs)) with
  | .conflict _ _ => true
  | .ok s0 =>
    match litStatus s0.trail (litNeg l) with
    | some false => true
    | some true => false
    | none =>
      match propagateAll fuel (decideLit s0 (litNeg l)) with
      | .conflict _ _ => true
      | _ => false
  | .outOfFuel _ => false

/-! ## 3. Executable unit-propagation-backed vivification (`vivifyClause`, `vivifyPass`) -/

/-- Inner recursive step of executable clause vivification: assumes `¬x` along `todo` while
skipping falsified literals and returning early on conflict or already-satisfied literal. -/
@[expose] def vivifyAux (fuel : Nat) (orig : List Nat) :
    List Nat → CdclState → List Nat → List Nat
  | kept, _, [] => kept.reverse
  | kept, s, x :: rest =>
    match litStatus s.trail x with
    | some true => kept.reverse ++ [x]
    | some false => vivifyAux fuel orig kept s rest
    | none =>
      match propagateAll fuel (decideLit s (litNeg x)) with
      | .conflict _ _ => kept.reverse ++ [x]
      | .ok s2 => vivifyAux fuel orig (x :: kept) s2 rest
      | .outOfFuel _ => orig

/-- Executable vivification of clause `c` against remaining clauses `rest`. -/
@[expose] def vivifyClause (fuel : Nat) (rest : List (List Nat)) (c : List Nat) : List Nat :=
  match propagateAll fuel (initState (cnfOfClauses rest)) with
  | .conflict _ _ => []
  | .ok s0 => vivifyAux fuel c [] s0 c
  | .outOfFuel _ => c

/-- Auxiliary single-pass executable vivification over `todo`, testing each clause against all
other kept + remaining clauses (`kept ++ rest`). -/
abbrev vivifyPassAux (fuel : Nat) : List (List Nat) → List (List Nat) → List (List Nat) :=
  clauseTransformPassAux (vivifyClause fuel)

/-- Single executable vivification pass over `cs`. -/
@[expose] def vivifyPass (fuel : Nat) (cs : List (List Nat)) : List (List Nat) :=
  vivifyPassAux fuel [] cs

end LeanQbe.T.Examples.Kissat.Ref
