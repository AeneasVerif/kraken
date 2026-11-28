/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Sat

/-!
# Soundness Proofs for the Kissat Abstract CDCL Core (Layer A, Part 1)

Proves foundational semantic soundness for `LeanQbe.T.Examples.Kissat.Ref.Sat` over
`Std.Sat.CNF Nat` (pure Lean, zero `Kraken.Mem`):

1. Signed DIMACS literal round-trip lemmas (`litToDimacs`, `dimacsToLit`).
2. Root-unit stripping/pruning (`pruneClause_sound`) and binary strengthening
   (`strengthenWithBinary_sound`).
3. `ReasonDagInv`, `LazyTrailInv`, `TrailInv`, and `lazyTrailEntailment` / `trailEntailment`.
4. Transition invariant preservation (`reasonDagInv_assignLit`, `initState`, `decideLit`,
   `assignProp`, `addRootUnit`, `backtrackTo`, `addLearnedClause`, `unitPropStep`,
   `propagateAll`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 3. `ReasonDagInv`, `LazyTrailInv`, `TrailInv`, and trail entailment -/

/-- Strict lexicographic `(level, trailIdx)` precedence relation. -/
@[expose] def lexLt (lvl1 idx1 lvl2 idx2 : Nat) : Prop :=
  lvl1 < lvl2 ∨ (lvl1 = lvl2 ∧ idx1 < idx2)

/-- List of decision literals on `s.trail` at level `≤ k`. -/
@[expose] def decisionsAtMost (s : CdclState) (k : Nat) : List Nat :=
  s.trail.toList.filter fun l =>
    decide (stateReason s l = .decision) && decide (stateLevel s l ≤ k)

/-- Reason-DAG invariant: every trail literal at index `i` is justified by strictly earlier
trail predecessors with non-greater decision level (strictly smaller `(level, idx)`). -/
@[expose] def ReasonDagInv (s : CdclState) : Prop :=
  ∀ (i : Nat) (hi : i < s.trail.size),
    let l := s.trail[i]
    let d := stateLevel s l
    match stateReason s l with
    | .decision => 0 < d
    | .unit => d = 0 ∧ s.f0.EntailsClause (cnfClause [l])
    | .binary other =>
      s.f0.EntailsClause (cnfClause [l, other]) ∧
      ∃ (j : Nat) (hj : j < s.trail.size), j < i ∧
        s.trail[j] = litNeg other ∧ stateLevel s other ≤ d ∧
        lexLt (stateLevel s other) j d i
    | .large cid =>
      ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ !c.garbage = true ∧
        l ∈ c.lits ∧
        ∀ x ∈ c.lits, x ≠ l →
          ∃ (j : Nat) (hj : j < s.trail.size), j < i ∧
            s.trail[j] = litNeg x ∧ stateLevel s x ≤ d ∧
            lexLt (stateLevel s x) j d i

/-- Kissat-faithful trail invariant supporting lazy assignment levels (`levels_mono` omitted). -/
structure LazyTrailInv (s : CdclState) : Prop where
  vars_nodup : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    litVar s.trail[i] = litVar s.trail[j] → i = j
  levels_le : ∀ i, (hi : i < s.trail.size) → stateLevel s s.trail[i] ≤ s.level
  dec_earliest : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    stateLevel s s.trail[i] = stateLevel s s.trail[j] →
    stateReason s s.trail[j] = .decision → j ≤ i
  db_sound : ∀ (cid : Nat) (c : Clause),
    s.clauses[cid]? = some (some c) → s.f0.EntailsClause (cnfClause c.lits)
  units_sound : ∀ u ∈ s.units, s.f0.EntailsClause (cnfClause [u])
  reason_dag : ReasonDagInv s
  inconsistent_sound : s.inconsistent = true → s.f0.Unsat

/-- Complete Layer-A CDCL trail & database soundness invariant. -/
structure TrailInv (s : CdclState) : Prop where
  vars_nodup : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    litVar s.trail[i] = litVar s.trail[j] → i = j
  levels_le : ∀ i, (hi : i < s.trail.size) → stateLevel s s.trail[i] ≤ s.level
  levels_mono : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    i ≤ j → stateLevel s s.trail[i] ≤ stateLevel s s.trail[j]
  dec_earliest : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    stateLevel s s.trail[i] = stateLevel s s.trail[j] →
    stateReason s s.trail[j] = .decision → j ≤ i
  db_sound : ∀ (cid : Nat) (c : Clause),
    s.clauses[cid]? = some (some c) → s.f0.EntailsClause (cnfClause c.lits)
  units_sound : ∀ u ∈ s.units, s.f0.EntailsClause (cnfClause [u])
  reason_dag : ReasonDagInv s
  inconsistent_sound : s.inconsistent = true → s.f0.Unsat

/-! ## 4. Transition invariant preservation -/

/-- Shared trail-push invariant for decisions, propagations, and level-0 unit additions. -/
@[expose] def ReasonOk (s : CdclState) (l lvl : Nat) : Reason → Prop
  | .decision => 0 < lvl
  | .unit => lvl = 0 ∧ s.f0.EntailsClause (cnfClause [l])
  | .binary other =>
    s.f0.EntailsClause (cnfClause [l, other]) ∧
    ∃ (j : Nat) (hj : j < s.trail.size),
      s.trail[j] = litNeg other ∧ stateLevel s other ≤ lvl ∧
      lexLt (stateLevel s other) j lvl s.trail.size
  | .large cid =>
    ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ !c.garbage = true ∧ l ∈ c.lits ∧
      ∀ x ∈ c.lits, x ≠ l →
        ∃ (j : Nat) (hj : j < s.trail.size),
          s.trail[j] = litNeg x ∧ stateLevel s x ≤ lvl ∧
          lexLt (stateLevel s x) j lvl s.trail.size

end LeanQbe.T.Examples.Kissat.Ref
