/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Minimize

/-!
# Pure Lean Layer-A CDCL Theory for Clause Minimization (Part 2: Iterative DFS Worklist)

Builds on `Minimize` to formalize and verify (pure Lean, zero `Kraken.Mem`):
- Explicit iterative DFS worklist (`min_stk`) (`minimizeLiteralWorklist`, `minimizeClauseWorklist`,
  `minimizeLiteralWorklist_sound`, `minimize_worklist_sound`) matching C0 execution with
  `minimizedepth` cap, `poisoned`, `frameUsed ≤ 1`, and binary-chain caching, proved terminating
  and sound against `MinState.RemovableInv` and `F₀.EntailsClause`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Iterative DFS worklist (`min_stk`) for recursive clause minimization -/

/-- Maximum literal count across all clauses in `clauses` (used for DFS termination measure). -/
@[expose] def maxClauseLen (clauses : Array (Option Clause)) : Nat :=
  clauses.foldl (fun m opt =>
    match opt with
    | some c => Nat.max m c.lits.length
    | none => m) 0

/-- Explicit DFS worklist frame matching C0 `min_stk` execution. -/
structure MinFrame where
  notLit : Nat
  remLits : List Nat
  depth : Nat
  binChain : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Leaf check corresponding to `minimized_index` (`minimize.c:4-40`):
returns `some true` (removable/root0), `some false` (decision/poisoned/singleton frame/untrail),
or `none` (descend into reason). -/
@[expose]
def checkLeafNode (s : MinState) (minimizing : Bool) (lit : Nat) (depth : Nat) : Option Bool :=
  if !trailHasLit s.cdcl.trail (litNeg lit) then some false
  else if s.litLevel lit == 0 then some true
  else if decide (0 < depth) && s.isRemovable (litVar lit) then some true
  else if s.isPoisoned (litVar lit) then some false
  else
    match stateReason s.cdcl lit with
    | .decision | .unit => some false
    | .binary _ | .large _ =>
      if (minimizing || depth == 0) && decide (s.getFrameUsed (s.litLevel lit) ≤ 1) then
        some false
      else
        none

/-- Result of iteratively walking a binary reason chain (`minimize_binary`, `minimize.c:60-93`). -/
inductive FollowBinaryRes where
  | leaf (ok : Bool) (chain : List Nat)
  | push (chain : List Nat) (notLit : Nat) (lits : List Nat) (pushDepth : Nat)
  deriving Repr, DecidableEq

/-- Iteratively follow binary reasons from `next` (bounded by `fuel`), stopping on leaf status
or a large reason clause (if `refDepth < maxDepth`). -/
@[expose] def followBinary (s : MinState) (minimizing : Bool) (maxDepth : Nat)
    (fuel : Nat) (next : Nat) (refDepth : Nat) (chain : List Nat) : FollowBinaryRes :=
  match fuel with
  | 0 => .leaf false chain
  | fuel + 1 =>
    match checkLeafNode s minimizing next 1 with
    | some ok => .leaf ok chain
    | none =>
      let v := litVar next
      match stateReason s.cdcl next with
      | .binary other =>
        if varLtLit s other next then
          followBinary s minimizing maxDepth fuel other refDepth (v :: chain)
        else
          .leaf false (v :: chain)
      | .large cid =>
        if refDepth < maxDepth then
          match s.cdcl.clauses[cid]? with
          | some (some cl) =>
            if !cl.garbage && cl.lits.contains (litNeg next) then
              .push (v :: chain) (litNeg next) cl.lits refDepth
            else
              .leaf false (v :: chain)
          | _ => .leaf false (v :: chain)
        else
          .leaf false (v :: chain)
      | _ => .leaf false chain

/-- Mark a list of variables as `poisoned := true`. -/
@[expose] def setPoisonedList (s : MinState) (vs : List Nat) : MinState :=
  vs.foldl (fun st v => st.setPoisoned v true) s

/-- Weight of a single `MinFrame` in base `base ≥ 2`. -/
@[expose] def frameWeight (maxDepth base : Nat) (f : MinFrame) : Nat :=
  (f.remLits.length + 1) * base ^ (maxDepth - f.depth)

/-- Explicit `Nat` termination measure for the iterative DFS worklist `minWorklist`. -/
@[expose] def worklistMeasure (maxDepth base : Nat) (stk : List MinFrame) : Nat :=
  stk.foldl (fun acc f => acc + frameWeight maxDepth base f) 0

/-- Poison all queued `binChain` variables across remaining stack frames on failure. -/
@[expose] def poisonStack (s : MinState) (stk : List MinFrame) : MinState :=
  stk.foldl (fun st f => setPoisonedList st f.binChain) s

/-- Iterative DFS worklist loop (`min_stk`) verifying clause minimization without recursion. -/
@[expose] def minWorklist (minimizing : Bool) (maxDepth : Nat) (s : MinState) :
    List MinFrame → Bool × MinState
  | [] => (true, s)
  | f :: rest =>
    let base := maxClauseLen s.cdcl.clauses + 2
    match hrl : f.remLits with
    | [] =>
      let _ := hrl
      let s1 := setRemovableList s f.binChain
      minWorklist minimizing maxDepth s1 rest
    | y :: ys =>
      if y == f.notLit then
        minWorklist minimizing maxDepth s (⟨f.notLit, ys, f.depth, f.binChain⟩ :: rest)
      else
        match followBinary s minimizing maxDepth (s.cdcl.trail.size + 1) y (f.depth + 1) [] with
        | .leaf true ch =>
          let s1 := setRemovableList s ch
          minWorklist minimizing maxDepth s1 (⟨f.notLit, ys, f.depth, f.binChain⟩ :: rest)
        | .leaf false ch =>
          (false, poisonStack (setPoisonedList s ch)
            (⟨f.notLit, ys, f.depth, f.binChain⟩ :: rest))
        | .push ch notLit' lits' pushDepth =>
          if hl : lits'.length + 1 < base ∧ f.depth + 1 < maxDepth ∧ pushDepth = f.depth + 1 then
            minWorklist minimizing maxDepth s
              (⟨notLit', lits', f.depth + 1, ch⟩ :: ⟨f.notLit, ys, f.depth, f.binChain⟩ :: rest)
          else
            (false, poisonStack (setPoisonedList s ch)
              (⟨f.notLit, ys, f.depth, f.binChain⟩ :: rest))
termination_by stk => worklistMeasure maxDepth (maxClauseLen s.cdcl.clauses + 2) stk
decreasing_by
  all_goals
    have hwm_cons : ∀ (md b : Nat) (fr : MinFrame) (rs : List MinFrame),
        worklistMeasure md b (fr :: rs) = frameWeight md b fr + worklistMeasure md b rs := by
      intro md b fr rs
      have hgen : ∀ (xs : List MinFrame) (init : Nat),
          xs.foldl (fun acc g => acc + frameWeight md b g) init =
            init + xs.foldl (fun acc g => acc + frameWeight md b g) 0 := by
        intro xs
        induction xs with
        | nil => intro init; simp
        | cons x xs ih =>
          intro init; simp only [List.foldl_cons]
          rw [ih (init + frameWeight md b x), ih (0 + frameWeight md b x)]; omega
      simpa [worklistMeasure] using hgen rs (frameWeight md b fr)
  · have hset_cdcl :
        ∀ (st : MinState) (vs : List Nat), (setRemovableList st vs).cdcl = st.cdcl := by
      intro st vs
      unfold setRemovableList
      induction vs generalizing st with
      | nil => rfl
      | cons _ _ ih => simp only [List.foldl_cons]; exact ih _
    simp only [hset_cdcl, hwm_cons]
    have hw : 0 < frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f := by
      unfold frameWeight
      exact Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by omega))
    omega
  · have hstep_lt : ∀ {md b : Nat}, 2 ≤ b →
        ∀ {nl y : Nat} {ys : List Nat} {d : Nat} {ch : List Nat},
          frameWeight md b ⟨nl, ys, d, ch⟩ < frameWeight md b ⟨nl, y :: ys, d, ch⟩ := by
      intro md b hb nl y ys d ch
      unfold frameWeight; dsimp only
      have hp : 0 < b ^ (md - d) := Nat.pow_pos (by omega)
      simp only [List.length_cons]
      have h2 : (ys.length + 1 + 1) * b ^ (md - d) =
          (ys.length + 1) * b ^ (md - d) + b ^ (md - d) := Nat.succ_mul _ _
      rw [h2]; omega
    rw [hwm_cons, hwm_cons]
    have hlt := @hstep_lt maxDepth (maxClauseLen s.cdcl.clauses + 2) (by omega)
      f.notLit y ys f.depth f.binChain
    have hfeq : frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f =
        frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2)
          ⟨f.notLit, y :: ys, f.depth, f.binChain⟩ := by simp [frameWeight, hrl]
    rw [hfeq]; omega
  · have hstep_lt : ∀ {md b : Nat}, 2 ≤ b →
        ∀ {nl y : Nat} {ys : List Nat} {d : Nat} {ch : List Nat},
          frameWeight md b ⟨nl, ys, d, ch⟩ < frameWeight md b ⟨nl, y :: ys, d, ch⟩ := by
      intro md b hb nl y ys d ch
      unfold frameWeight; dsimp only
      have hp : 0 < b ^ (md - d) := Nat.pow_pos (by omega)
      simp only [List.length_cons]
      have h2 : (ys.length + 1 + 1) * b ^ (md - d) =
          (ys.length + 1) * b ^ (md - d) + b ^ (md - d) := Nat.succ_mul _ _
      rw [h2]; omega
    have hset_cdcl :
        ∀ (st : MinState) (vs : List Nat), (setRemovableList st vs).cdcl = st.cdcl := by
      intro st vs
      unfold setRemovableList
      induction vs generalizing st with
      | nil => rfl
      | cons _ _ ih => simp only [List.foldl_cons]; exact ih _
    simp only [hset_cdcl, hwm_cons]
    have hlt := @hstep_lt maxDepth (maxClauseLen s.cdcl.clauses + 2) (by omega)
      f.notLit y ys f.depth f.binChain
    have hfeq : frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f =
        frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2)
          ⟨f.notLit, y :: ys, f.depth, f.binChain⟩ := by simp [frameWeight, hrl]
    rw [hfeq]; omega
  · have hpush_lt : ∀ {md b : Nat}, 2 ≤ b →
        ∀ {nl y nl' : Nat} {ys lits : List Nat} {d : Nat} {ch ch' : List Nat},
          d + 1 < md → lits.length + 1 < b →
          frameWeight md b ⟨nl, ys, d, ch⟩ + frameWeight md b ⟨nl', lits, d + 1, ch'⟩ <
            frameWeight md b ⟨nl, y :: ys, d, ch⟩ := by
      intro md b hb nl y nl' ys lits d ch ch' hd hlits
      unfold frameWeight; dsimp only
      have hp : 0 < b ^ (md - (d + 1)) := Nat.pow_pos (by omega)
      have heq : b ^ (md - d) = b * b ^ (md - (d + 1)) := by
        rw [show md - d = (md - (d + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      have h1 : (lits.length + 1) * b ^ (md - (d + 1)) < b * b ^ (md - (d + 1)) :=
        Nat.mul_lt_mul_of_pos_right hlits hp
      have h2 : (ys.length + 1 + 1) * b ^ (md - d) =
          (ys.length + 1) * b ^ (md - d) + b ^ (md - d) := Nat.succ_mul _ _
      simp only [List.length_cons]; rw [h2, heq]; omega
    rw [hwm_cons, hwm_cons, hwm_cons]
    have hlt := @hpush_lt maxDepth (maxClauseLen s.cdcl.clauses + 2) (by omega)
      f.notLit y notLit' ys lits' f.depth f.binChain ch hl.2.1 hl.1
    have hfeq : frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f =
        frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2)
          ⟨f.notLit, y :: ys, f.depth, f.binChain⟩ := by simp [frameWeight, hrl]
    rw [hfeq]; omega

/-- Iterative literal minimization matching `kissat_minimize_literal(solver, lit, inClause)`
via explicit DFS worklist `minWorklist`. -/
@[expose] def minimizeLiteralWorklist (s : MinState) (minimizing : Bool) (maxDepth : Nat)
    (lit : Nat) (depth0 : Nat := 0) : Bool × MinState :=
  if maxDepth == 0 then (false, s)
  else if maxDepth ≤ depth0 then (false, s)
  else
    match checkLeafNode s minimizing lit depth0 with
    | some ok => (ok, s)
    | none =>
      let initChain := if depth0 == 0 then [] else [litVar lit]
      match stateReason s.cdcl lit with
      | .binary other =>
        if varLtLit s other lit then
          match followBinary s minimizing maxDepth (s.cdcl.trail.size + 1)
              other (depth0 + 1) initChain with
          | .leaf true ch => (true, setRemovableList s ch)
          | .leaf false ch => (false, setPoisonedList s ch)
          | .push ch notLit' lits' pushDepth =>
            minWorklist minimizing maxDepth s [⟨notLit', lits', pushDepth, ch⟩]
        else (false, setPoisonedList s initChain)
      | .large cid =>
        match s.cdcl.clauses[cid]? with
        | some (some cl) =>
          if !cl.garbage && cl.lits.contains (litNeg lit) then
            minWorklist minimizing maxDepth s [⟨litNeg lit, cl.lits, depth0, initChain⟩]
          else (false, setPoisonedList s initChain)
        | _ => (false, setPoisonedList s initChain)
      | _ => (false, s)

/-- Iterative DFS clause minimization (`kissat_minimize_clause`, `minimize.c:155-211`):
seeds every literal onto `removable`, checks each non-pivot literal at depth 0, drops minimized
literals while preserving `RemovableInv`, and resets `poisoned`. -/
@[expose] def minimizeClauseWorklist (s : MinState) (maxDepth : Nat) (C : List Nat) :
    List Nat × MinState :=
  let s0 := seedRemovable s C
  let (keptRev, sEnd) := C.foldl (init := ([], s0)) fun (acc, st) lit =>
    let (ok, st') := minimizeLiteralWorklist st true maxDepth lit 0
    if ok then (acc, st') else (lit :: acc, st')
  (keptRev.reverse, sEnd.resetPoisoned)

end LeanQbe.T.Examples.Kissat.Ref
