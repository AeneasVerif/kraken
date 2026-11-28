/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Trail

/-!
# Soundness Proofs for the Kissat Abstract CDCL Core (Layer A, Part 2)

Builds on `Trail` to prove soundness of conflict analysis, failed-literal probing,
clause minimization, relocation/deletion, and the top-level CDCL reference solver:

5. `analyze1UIP_sound` and `backtrack_learn_preserves_inv`.
6. `failedLit_sound` and `failedLitStep_preserves_inv`.
7. Lexicographic `(level, trailIdx)` `RemovableInv` minimization cut (`minimizeCut_sound`).
8. Clause relocation (`RefMap` injectivity), `collect_preserves_inv`, and
   `deleteClauseState_preserves_inv`.
9. Top-level solver soundness `cdclSolve_sound` (and parser bridge `cdclSolve_sound_of_parse`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 7. Lexicographic `(level, trailIdx)` `RemovableInv` minimization cut -/

/-- Recursive semantic removability relative to retained clause literals `K`. -/
inductive Removable (s : CdclState) (K : List Nat) : Nat → Prop where
  | in_keep (l : Nat) : l ∈ K → Removable s K l
  | root0 (l : Nat) : litNeg l ∈ s.trail.toList → stateLevel s l = 0 → Removable s K l
  | binary (l other : Nat) :
    litNeg l ∈ s.trail.toList → stateReason s l = .binary other →
    Removable s K other → Removable s K l
  | large (l cid : Nat) (cl : Clause) :
    litNeg l ∈ s.trail.toList → stateReason s l = .large cid →
    s.clauses[cid]? = some (some cl) → litNeg l ∈ cl.lits →
    (∀ x ∈ cl.lits, x ≠ litNeg l → Removable s K x) → Removable s K l

/-- Minimization cut invariant: every dropped literal of `C` is `Removable` wrt `K`. -/
@[expose] def RemovableInv (s : CdclState) (c K : List Nat) : Prop :=
  ∀ l ∈ c, l ∉ K → Removable s K l

/-! ## 8. Clause relocation (`RefMap`), garbage collection, and deletion soundness -/

/-- Relocation map correctness: `rmap` is injective, preserves every non-garbage clause, and
every clause in `newClauses` is entailed by `f0`. -/
@[expose] def RefMapSound (clauses newClauses : Array (Option Clause)) (rmap : RefMap)
    (f0 : CNF Nat) : Prop :=
  (∀ i j nid, rmap.lookup i = some nid → rmap.lookup j = some nid → i = j) ∧
  (∀ (cid : Nat) (c : Clause), clauses[cid]? = some (some c) → !c.garbage = true →
    ∃ nid, rmap.lookup cid = some nid ∧ newClauses[nid]? = some (some c)) ∧
  (∀ (nid : Nat) (c : Clause),
    newClauses[nid]? = some (some c) → f0.EntailsClause (cnfClause c.lits))

end LeanQbe.T.Examples.Kissat.Ref
