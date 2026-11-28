/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Minimize

/-!
# Pure Lean Layer-A CDCL Theory for Clause Collection & Relocation (Part 1)

Pure Lean theory (zero `Kraken.Mem` or `Kraken.Separation` imports) for clause-ID remapping,
deletion of unreferenced clauses, and `reduce` garbage marking (`collect.c`, `reduce.c`,
`trail.c`):

1. **CNF views & active-reason predicate (`survivingCnf`, `binariesCnf`,
   `isActiveLargeReason`)**.
2. **Generalized `RefTarget` relocation (`collect_remap_sound`,
   `collect_remap_preserves_trailInv`, `core_collect_lazy_sound`)**:
   Deleting unreferenced clauses, injectively remapping surviving clause IDs (`RefTarget.moved`),
   and promoting size-2 clauses (`RefTarget.toBinary`) preserves `LazyTrailInv` (`ReasonDagInv`),
   `lazyTrailEntailment`, surviving/binary `F₀.EntailsClause`, and satisfiability (`Sat F₀ → Sat`).
3. **Unreferenced deletion & garbage marking (`deleteUnreferencedClauses_sound`,
   `markGarbageIf_sound`)** plus `ReasonLevelsPos` / `ReasonHasNonRootAntecedent`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. CNF views, active trail reasons, and generalized `RefTarget` relocation -/

/-- Conjunction of all non-garbage clauses stored in `clauses`. -/
@[expose] def survivingCnf (clauses : Array (Option Clause)) : CNF Nat :=
  clauses.foldl (init := CNF.empty) fun acc opt =>
    match opt with
    | some c => if c.garbage then acc else acc.add (cnfClause c.lits)
    | none => acc

/-- Conjunction of promoted binary watch pairs `(a, b)`. -/
@[expose] def binariesCnf (bins : List (Nat × Nat)) : CNF Nat :=
  bins.foldl (init := CNF.empty) fun acc p => acc.add (cnfClause [p.1, p.2])

/-- Active-reason predicate (`trail.c:26-43`): `true` iff some trail literal cites `.large cid`
as its `stateReason`. -/
@[expose] def isActiveLargeReason (s : CdclState) (cid : Nat) : Bool :=
  s.trail.any fun l => stateReason s l == .large cid

/-- Relocation/promotion target for an old clause slot `cid`. -/
inductive RefTarget where
  | dropped
  | toBinary (a b : Nat)
  | moved (newCid : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Remap a reason belonging to trail literal `lit` through `targets`. -/
@[expose] def remapReasonTarget (targets : Array RefTarget) (lit : Nat) : Reason → Reason
  | .large cid =>
    match targets[cid]? with
    | some (.moved newCid) => .large newCid
    | some (.toBinary a b) => .binary (if lit == a then b else a)
    | _ => .large cid
  | r => r

@[expose] def remapReasonStep (targets : Array RefTarget) (rs : Array Reason)
    (lit : Nat) : Array Reason :=
  let v := litVar lit
  if h : v < rs.size then rs.set v (remapReasonTarget targets lit rs[v]) else rs

/-- Update trail reason entries for every variable assigned on `trail`. -/
@[expose] def remapReasons (trail : Array Nat) (reasons : Array Reason)
    (targets : Array RefTarget) : Array Reason :=
  trail.foldl (remapReasonStep targets) reasons

/-- Apply relocated/compacted clause database and target reason mapping to `CdclState`. -/
@[expose] def applyRefTargets (s : CdclState) (newClauses : Array (Option Clause))
    (targets : Array RefTarget) : CdclState :=
  { s with
    clauses := newClauses
    reasons := remapReasons s.trail s.reasons targets }

/-- Generalized soundness contract for clause relocation, deletion, and size-2 binary promotion:
- `inj_moved`: distinct original IDs never collide at the same new clause ID.
- `active_preserved`: every active trail `.large cid` reason either moves to a non-garbage clause
  `c'` containing `trail[i]` with `c'.lits ⊆ old_c.lits`, or becomes a binary watch `[a, b]`
  preserving `trail[i]`, its sibling literal `oth ≠ trail[i]` from `old_c.lits`, and `f0`-entailment
  of `[trail[i], oth]`.
- `clauses_entailed`: every non-empty clause slot in `newClauses` is entailed by `s.f0`.
- `binaries_entailed`: every promoted binary pair in `newBinaries` is entailed by `s.f0`. -/
structure RefTargetSound (s : CdclState) (newClauses : Array (Option Clause))
    (newBinaries : List (Nat × Nat)) (targets : Array RefTarget) : Prop where
  inj_moved : ∀ (i j nid : Nat),
    targets[i]? = some (RefTarget.moved nid) →
    targets[j]? = some (RefTarget.moved nid) → i = j
  active_preserved :
    ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat),
      stateReason s s.trail[i] = .large cid →
      (∃ newCid c', targets[cid]? = some (RefTarget.moved newCid) ∧
        newClauses[newCid]? = some (some c') ∧ !c'.garbage = true ∧
        s.trail[i] ∈ c'.lits ∧
        ∀ x ∈ c'.lits, x ≠ s.trail[i] →
          ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ x ∈ c.lits) ∨
      (∃ a b, targets[cid]? = some (RefTarget.toBinary a b) ∧ (a, b) ∈ newBinaries ∧
        ((s.trail[i] = a ∧ b ≠ a ∧ s.f0.EntailsClause (cnfClause [a, b]) ∧
            ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ b ∈ c.lits) ∨
         (s.trail[i] = b ∧ a ≠ b ∧ s.f0.EntailsClause (cnfClause [b, a]) ∧
            ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ a ∈ c.lits)))
  clauses_entailed :
    ∀ (nid : Nat) (c : Clause), newClauses[nid]? = some (some c) →
      s.f0.EntailsClause (cnfClause c.lits)
  binaries_entailed :
    ∀ p ∈ newBinaries, s.f0.EntailsClause (cnfClause [p.1, p.2])

/-! ## 2. Deletion of unreferenced clauses and `reduce` garbage marking -/

/-- Delete every clause slot satisfying `dropPred cid c` that is NOT an active trail reason
(`trail.c:26-43`, `!isActiveLargeReason s cid`). -/
@[expose]
def deleteUnreferencedClauses (s : CdclState) (dropPred : Nat → Clause → Bool) : CdclState :=
  let clauses' := Array.ofFn fun (i : Fin s.clauses.size) =>
    match s.clauses[i.1] with
    | some c => if dropPred i.1 c && !isActiveLargeReason s i.1 then none else some c
    | none => none
  { s with clauses := clauses' }

/-- Every `.large` trail reason points to a strictly positive decision level (`unflushed == 0` /
level-0 unit propagation flushed). -/
@[expose] def ReasonLevelsPos (s : CdclState) : Prop :=
  ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat),
    stateReason s s.trail[i] = .large cid → 0 < stateLevel s s.trail[i]

/-- Every `.large` trail reason clause contains at least one strictly non-level-0 antecedent
besides its forced literal (`collect.c:422`, `new_size > 1`). -/
@[expose] def ReasonHasNonRootAntecedent (s : CdclState) : Prop :=
  ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat) (c : Clause),
    stateReason s s.trail[i] = .large cid →
    s.clauses[cid]? = some (some c) →
    ∃ x ∈ c.lits, x ≠ s.trail[i] ∧ 0 < stateLevel s x

/-- Mark clauses matching `markPred cid c` as `garbage := true` when not referenced as an active
trail reason (`reduce.c` + `trail.c:26-43`). -/
@[expose] def markGarbageIf (s : CdclState) (markPred : Nat → Clause → Bool) : CdclState :=
  let clauses' := Array.ofFn fun (i : Fin s.clauses.size) =>
    match s.clauses[i.1] with
    | some c =>
      if markPred i.1 c && !isActiveLargeReason s i.1 then some { c with garbage := true }
      else some c
    | none => none
  { s with clauses := clauses' }

/-! ## 3. Flushing root-level & root-antecedent trail reasons (`flushRootReasons`) -/

/-- Check whether trail literal `l` sits at level `0` with non-`.unit` reason, or sits at a
positive level with all `.binary`/`.large` antecedents already at level `0`. -/
@[expose] def shouldFlushReason (s : CdclState) (l : Nat) : Bool :=
  let rsn := stateReason s l
  if stateLevel s l == 0 then rsn != .unit
  else match rsn with
  | .binary other => stateLevel s other == 0
  | .large cid =>
    match s.clauses[cid]? with
    | some (some c) => c.lits.all (fun x => x == l || stateLevel s x == 0)
    | _ => false
  | .decision | .unit => false

/-- Demote literal `l` to decision level `0` with reason `.unit` and record it in `units`. -/
@[expose] def flushLitToUnit (s : CdclState) (l : Nat) : CdclState :=
  let v := litVar l
  { s with
    units := if s.units.contains l then s.units else l :: s.units
    levels := arraySetPad s.levels v 0 0
    reasons := arraySetPad s.reasons v .unit .unit }

/-- Single step of `flushRootReasons` at trail position `i`. -/
@[expose] def flushRootReasonStep (s : CdclState) (i : Nat) : CdclState :=
  if h : i < s.trail.size then
    if shouldFlushReason s s.trail[i] then flushLitToUnit s s.trail[i] else s
  else s

/-- Left-to-right loop flushing root-level and all-root-antecedent reasons to `.unit`. -/
@[expose] def flushRootReasonsAux (s : CdclState) (i : Nat) : CdclState :=
  if i < s.trail.size then
    flushRootReasonsAux (flushRootReasonStep s i) (i + 1)
  else s
termination_by s.trail.size - i
decreasing_by
  have htr : (flushRootReasonStep s i).trail = s.trail := by
    unfold flushRootReasonStep
    by_cases h : i < s.trail.size
    · simp only [dite_eq_left h]; split <;> rfl
    · simp only [dite_eq_right h]
  simp only [htr]
  omega

/-- Flush all root-level and all-root-antecedent trail reasons to `.unit` at level `0`,
establishing `ReasonLevelsPos` and `ReasonHasNonRootAntecedent` (`trail.c`, `unflushed == 0`). -/
@[expose] def flushRootReasons (s : CdclState) : CdclState :=
  flushRootReasonsAux s 0

end LeanQbe.T.Examples.Kissat.Ref
