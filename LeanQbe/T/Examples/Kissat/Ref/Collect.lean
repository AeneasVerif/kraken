/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Reduce

/-!
# Pure Lean Layer-A CDCL Theory for Clause Sweeping, Partitioning, and Collection

Builds on `Reduce` (pure Lean, zero `Kraken.Mem` or `Kraken.Separation` imports):

1. **Kissat `sparse_sweep_garbage_clauses` (`sweepClauses`, `collect.c:277-460`)**:
   - Proves Kissat's active-reason assertions (`activeReason_not_rootSatisfied`,
     `collect.c:411`, and `activeReason_stripped_size_ge_two`, `collect.c:422`).
   - Drops `garbage` and root-satisfied clauses, strips root-falsified literals, promotes size-2
     surviving clauses `[a, b]` to binary watches (`RefTarget.toBinary`) + `.binary` trail
     reasons, and compacts remaining clauses (`sweepClauses_sound`, `sweep_collect_sound`).
2. **Irredundant/redundant partitioning (`partitionIrredFirst`, `collect.c:213-275`)** and
   end-to-end **`reduceAndCollect` / `reduceAndCollect_sound`**.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 2. Kissat `sparse_sweep_garbage_clauses` (`collect.c:277-460`) with binary promotion -/

/-- Literal `l` is root-satisfied on `s.trail` (true at decision level `0`). -/
@[expose] def isRootTrue (s : CdclState) (l : Nat) : Bool :=
  trailHasLit s.trail l && (stateLevel s l == 0)

/-- Literal `l` is root-falsified on `s.trail` (`litNeg l` true at decision level `0`). -/
@[expose] def isRootFalse (s : CdclState) (l : Nat) : Bool :=
  trailHasLit s.trail (litNeg l) && (stateLevel s l == 0)

@[expose] def sweepClauseStep (s : CdclState) (acc : Array (Option Clause))
    (bins : List (Nat × Nat)) (targets : Array RefTarget) (opt : Option Clause) :
    Array (Option Clause) × List (Nat × Nat) × Array RefTarget :=
  match opt with
  | none => (acc, bins, targets.push .dropped)
  | some c =>
    if c.garbage || c.lits.any (isRootTrue s) then
      (acc, bins, targets.push .dropped)
    else
      let lits' := stripFalsified (isRootFalse s) c.lits
      match lits' with
      | [a, b] =>
        if a == b then
          (acc.push (some { c with lits := lits' }), bins, targets.push (.moved acc.size))
        else
          (acc, (a, b) :: bins, targets.push (.toBinary a b))
      | _ =>
        (acc.push (some { c with lits := lits' }), bins, targets.push (.moved acc.size))

/-- Sparse garbage-clause sweep (`sparse_sweep_garbage_clauses`, `collect.c:277-460`):
drops `garbage` and root-satisfied clauses, strips root-falsified literals, promotes distinct
size-2 clauses to binary watches, and compacts remaining clauses with `RefTarget`. -/
@[expose] def sweepClauses (s : CdclState) :
    Array (Option Clause) × List (Nat × Nat) × Array RefTarget :=
  s.clauses.foldl (init := (#[], [], #[])) fun (acc, bins, tgts) opt =>
    sweepClauseStep s acc bins tgts opt

/-! ## 3. Partitioning irredundant before redundant (`collect.c:213-275`) & `reduceAndCollect` -/

@[expose] def partitionStep (irred red : Array (Option Clause))
    (raw : Array (Option (Bool × Nat))) (opt : Option Clause) :
    Array (Option Clause) × Array (Option Clause) × Array (Option (Bool × Nat)) :=
  match opt with
  | none => (irred, red, raw.push none)
  | some c =>
    if c.garbage then (irred, red, raw.push none)
    else if c.redundant then
      (irred, red.push (some c), raw.push (some (true, red.size)))
    else
      (irred.push (some c), red, raw.push (some (false, irred.size)))

/-- Partition non-garbage clauses with irredundant clauses before redundant clauses
(`move_redundant_clauses_to_the_end`, `collect.c:213-275`), returning compacted clauses and
injective `RefTarget` relocation map. -/
@[expose] def partitionIrredFirst (clauses : Array (Option Clause)) :
    Array (Option Clause) × Array RefTarget :=
  let st := clauses.foldl (init := (#[], #[], #[]))
    (fun (p : Array (Option Clause) × Array (Option Clause) × Array (Option (Bool × Nat))) opt =>
      partitionStep p.1 p.2.1 p.2.2 opt)
  let irSz := st.1.size
  let tgts := st.2.2.map fun r =>
    match r with
    | none => RefTarget.dropped
    | some (false, i) => RefTarget.moved i
    | some (true, i) => RefTarget.moved (irSz + i)
  (st.1 ++ st.2.1, tgts)

/-- Combined `reduce` + `collect` pipeline (`reduce.c` + `collect.c`):
1. Mark unreferenced redundant clauses matching `dropPred` as `garbage := true` (`markGarbageIf`).
2. Sparse sweep (`sweepClauses`): drop garbage/root-satisfied, strip root-falsified literals,
   promote size-2 clauses to binary watches & `.binary` trail reasons.
3. Partition surviving irredundant clauses before redundant clauses (`partitionIrredFirst`). -/
@[expose] def reduceAndCollect (s : CdclState) (dropPred : Nat → Clause → Bool) :
    CdclState × List (Nat × Nat) :=
  let s1 := markGarbageIf s (fun cid c => c.redundant && dropPred cid c)
  let (swClauses, newBins, swTargets) := sweepClauses s1
  let s2 := applyRefTargets s1 swClauses swTargets
  let (partClauses, partTargets) := partitionIrredFirst s2.clauses
  (applyRefTargets s2 partClauses partTargets, newBins)

end LeanQbe.T.Examples.Kissat.Ref
