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

private theorem maxClauseLen_foldl_ge (xs : List (Option Clause)) (init : Nat) :
    init ≤ xs.foldl (fun m opt =>
      match opt with
      | some c => Nat.max m c.lits.length
      | none => m) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    cases x with
    | none => exact ih init
    | some c => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem maxClauseLen_foldl_mem (xs : List (Option Clause)) :
    ∀ (idx : Nat) (c : Clause) (init : Nat), xs[idx]? = some (some c) →
      c.lits.length ≤ xs.foldl (fun m opt =>
        match opt with
        | some cl => Nat.max m cl.lits.length
        | none => m) init := by
  induction xs with
  | nil => intro idx _ _ h; simp at h
  | cons x xs ih =>
    intro idx c init h
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_right _ _) (maxClauseLen_foldl_ge xs _)
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.foldl_cons]
      exact ih k c _ h

theorem clause_len_le_maxClauseLen {clauses : Array (Option Clause)} {cid : Nat} {c : Clause}
    (h : clauses[cid]? = some (some c)) : c.lits.length ≤ maxClauseLen clauses := by
  rw [maxClauseLen, ← Array.foldl_toList]
  exact maxClauseLen_foldl_mem clauses.toList cid c 0 (by simpa [Array.getElem?_toList] using h)

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

theorem setPoisonedList_cdcl (s : MinState) (vs : List Nat) :
    (setPoisonedList s vs).cdcl = s.cdcl := by
  unfold setPoisonedList
  induction vs generalizing s with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem setPoisonedList_trailPos (s : MinState) (vs : List Nat) :
    (setPoisonedList s vs).trailPos = s.trailPos := by
  unfold setPoisonedList
  induction vs generalizing s with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons, ih]; rfl

theorem setPoisonedList_isRemovable (s : MinState) (vs : List Nat) (w : Nat) :
    (setPoisonedList s vs).isRemovable w = s.isRemovable w := by
  unfold setPoisonedList
  induction vs generalizing s with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons, ih, MinState.isRemovable_setPoisoned]

theorem MinBaseInv.setPoisonedList {s : MinState} (h : MinBaseInv s) (vs : List Nat) :
    MinBaseInv (setPoisonedList s vs) :=
  ⟨by rw [setPoisonedList_cdcl]; exact h.trail_inv,
   by rw [setPoisonedList_cdcl, setPoisonedList_trailPos]; exact h.pos_inv⟩

theorem removableInv_setPoisonedList {s : MinState} {C : List Nat} (vs : List Nat) :
    (setPoisonedList s vs).RemovableInv C ↔ s.RemovableInv C :=
  removableInv_congr (setPoisonedList_cdcl _ _) (setPoisonedList_trailPos _ _)
    (setPoisonedList_isRemovable s vs)

/-- Weight of a single `MinFrame` in base `base ≥ 2`. -/
@[expose] def frameWeight (maxDepth base : Nat) (f : MinFrame) : Nat :=
  (f.remLits.length + 1) * base ^ (maxDepth - f.depth)

/-- Explicit `Nat` termination measure for the iterative DFS worklist `minWorklist`. -/
@[expose] def worklistMeasure (maxDepth base : Nat) (stk : List MinFrame) : Nat :=
  stk.foldl (fun acc f => acc + frameWeight maxDepth base f) 0

private theorem worklistMeasure_cons (maxDepth base : Nat) (f : MinFrame)
    (rest : List MinFrame) :
    worklistMeasure maxDepth base (f :: rest) =
      frameWeight maxDepth base f + worklistMeasure maxDepth base rest := by
  have hgen : ∀ (xs : List MinFrame) (init : Nat),
      xs.foldl (fun acc g => acc + frameWeight maxDepth base g) init =
        init + xs.foldl (fun acc g => acc + frameWeight maxDepth base g) 0 := by
    intro xs
    induction xs with
    | nil => intro init; simp
    | cons x xs ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih (init + frameWeight maxDepth base x), ih (0 + frameWeight maxDepth base x)]
      omega
  simpa [worklistMeasure] using hgen rest (frameWeight maxDepth base f)

private theorem frameWeight_push_lt {maxDepth base : Nat} (hbase : 2 ≤ base)
    {notLit y notLit' : Nat} {ys lits : List Nat} {d : Nat} {ch ch' : List Nat}
    (hd : d + 1 < maxDepth) (hlits : lits.length + 1 < base) :
    frameWeight maxDepth base ⟨notLit, ys, d, ch⟩ +
      frameWeight maxDepth base ⟨notLit', lits, d + 1, ch'⟩ <
      frameWeight maxDepth base ⟨notLit, y :: ys, d, ch⟩ := by
  unfold frameWeight
  dsimp only
  have hpow_pos : 0 < base ^ (maxDepth - (d + 1)) := Nat.pow_pos (by omega)
  have hpow_eq : base ^ (maxDepth - d) = base * base ^ (maxDepth - (d + 1)) := by
    rw [show maxDepth - d = (maxDepth - (d + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have h1 : (lits.length + 1) * base ^ (maxDepth - (d + 1)) <
      base * base ^ (maxDepth - (d + 1)) := Nat.mul_lt_mul_of_pos_right hlits hpow_pos
  have h2 : (ys.length + 1 + 1) * base ^ (maxDepth - d) =
      (ys.length + 1) * base ^ (maxDepth - d) + base ^ (maxDepth - d) := Nat.succ_mul _ _
  simp only [List.length_cons]
  rw [h2, hpow_eq]
  omega

private theorem frameWeight_step_lt {maxDepth base : Nat} (hbase : 2 ≤ base)
    {notLit y : Nat} {ys : List Nat} {d : Nat} {ch : List Nat} :
    frameWeight maxDepth base ⟨notLit, ys, d, ch⟩ <
      frameWeight maxDepth base ⟨notLit, y :: ys, d, ch⟩ := by
  unfold frameWeight
  dsimp only
  have hpow_pos : 0 < base ^ (maxDepth - d) := Nat.pow_pos (by omega)
  simp only [List.length_cons]
  have h2 : (ys.length + 1 + 1) * base ^ (maxDepth - d) =
      (ys.length + 1) * base ^ (maxDepth - d) + base ^ (maxDepth - d) := Nat.succ_mul _ _
  rw [h2]; omega

/-- Poison all queued `binChain` variables across remaining stack frames on failure. -/
@[expose] def poisonStack (s : MinState) (stk : List MinFrame) : MinState :=
  stk.foldl (fun st f => setPoisonedList st f.binChain) s

theorem poisonStack_cdcl (s : MinState) (stk : List MinFrame) :
    (poisonStack s stk).cdcl = s.cdcl := by
  unfold poisonStack
  induction stk generalizing s with
  | nil => rfl
  | cons f fs ih => simp [ih, setPoisonedList_cdcl]

theorem poisonStack_trailPos (s : MinState) (stk : List MinFrame) :
    (poisonStack s stk).trailPos = s.trailPos := by
  unfold poisonStack
  induction stk generalizing s with
  | nil => rfl
  | cons f fs ih => simp [ih, setPoisonedList_trailPos]

theorem poisonStack_isRemovable (s : MinState) (stk : List MinFrame) (w : Nat) :
    (poisonStack s stk).isRemovable w = s.isRemovable w := by
  unfold poisonStack
  induction stk generalizing s with
  | nil => rfl
  | cons f fs ih => simp [ih, setPoisonedList_isRemovable]

theorem MinBaseInv.poisonStack {s : MinState} (h : MinBaseInv s) (stk : List MinFrame) :
    MinBaseInv (poisonStack s stk) :=
  ⟨by rw [poisonStack_cdcl]; exact h.trail_inv,
   by rw [poisonStack_cdcl, poisonStack_trailPos]; exact h.pos_inv⟩

theorem removableInv_poisonStack {s : MinState} {C : List Nat} (stk : List MinFrame) :
    (poisonStack s stk).RemovableInv C ↔ s.RemovableInv C :=
  removableInv_congr (poisonStack_cdcl _ _) (poisonStack_trailPos _ _)
    (poisonStack_isRemovable s stk)

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
    try simp only [setRemovableList_cdcl]
  · rw [worklistMeasure_cons]
    have hw : 0 < frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f := by
      unfold frameWeight
      exact Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by omega))
    omega
  · rw [worklistMeasure_cons, worklistMeasure_cons]
    have hlt := frameWeight_step_lt (maxDepth := maxDepth)
      (base := maxClauseLen s.cdcl.clauses + 2) (by omega)
      (notLit := f.notLit) (y := y) (ys := ys) (d := f.depth) (ch := f.binChain)
    have hfeq : frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f =
        frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2)
          ⟨f.notLit, y :: ys, f.depth, f.binChain⟩ := by simp [frameWeight, hrl]
    rw [hfeq]; omega
  · rw [worklistMeasure_cons, worklistMeasure_cons]
    have hlt := frameWeight_step_lt (maxDepth := maxDepth)
      (base := maxClauseLen s.cdcl.clauses + 2) (by omega)
      (notLit := f.notLit) (y := y) (ys := ys) (d := f.depth) (ch := f.binChain)
    have hfeq : frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f =
        frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2)
          ⟨f.notLit, y :: ys, f.depth, f.binChain⟩ := by simp [frameWeight, hrl]
    rw [hfeq]; omega
  · rw [worklistMeasure_cons, worklistMeasure_cons, worklistMeasure_cons]
    have hlt := frameWeight_push_lt (maxDepth := maxDepth)
      (base := maxClauseLen s.cdcl.clauses + 2) (by omega)
      (notLit := f.notLit) (y := y) (notLit' := notLit') (ys := ys) (lits := lits')
      (d := f.depth) (ch := f.binChain) (ch' := ch) hl.2.1 hl.1
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

/-! ### Soundness proofs for `followBinary`, `minWorklist`, and `minimizeClauseWorklist` -/

/-- Binary-chain invariant for `chain` leading into current literal `next`. -/
private def BinChainInv (s : MinState) (next : Nat) (chain : List Nat) : Prop :=
  ∀ w ∈ chain, 0 < s.varLevel w ∧
    ∃ (i : Nat) (_hi : i < s.cdcl.trail.size), litVar s.cdcl.trail[i] = w ∧
      ∃ other : Nat, stateReason s.cdcl s.cdcl.trail[i] = .binary other ∧
        (litVar other = litVar next ∨ litVar other ∈ chain)

/-- Stack frame invariant wrt root literal `rootLit` and pending child variables `pending`. -/
private def FramePendingInv (s : MinState) (rootLit : Nat) (pending : List Nat)
    (f : MinFrame) : Prop :=
  (∀ x ∈ f.binChain, 0 < s.varLevel x) ∧
  (∃ (cid : Nat) (cl : Clause),
    s.cdcl.clauses[cid]? = some (some cl) ∧ !cl.garbage = true ∧
    f.notLit ∈ cl.lits ∧
    (∀ x ∈ cl.lits, x ∉ f.remLits →
      x = f.notLit ∨ s.litLevel x = 0 ∨ s.isRemovable (litVar x) = true ∨
      litVar x ∈ pending) ∧
    (f.binChain = [] →
      f.notLit = litNeg rootLit ∧ stateReason s.cdcl (litNeg rootLit) = .large cid) ∧
    (f.binChain ≠ [] →
      f.notLit ∈ s.cdcl.trail.toList ∧
      stateReason s.cdcl f.notLit = .large cid ∧
      ∀ w ∈ f.binChain, 0 < s.varLevel w ∧
        ∃ (i : Nat) (_hi : i < s.cdcl.trail.size), litVar s.cdcl.trail[i] = w ∧
          (s.cdcl.trail[i] = f.notLit ∨
            ∃ other : Nat, stateReason s.cdcl s.cdcl.trail[i] = .binary other ∧
              litVar other ∈ f.binChain)))

/-- Whole-stack invariant connecting each frame's `remLits` progress to its child's `binChain`. -/
private def StackInvWith (s : MinState) (rootLit : Nat) (pending : List Nat) :
    List MinFrame → Prop
  | [] => True
  | f :: rest =>
    FramePendingInv s rootLit pending f ∧
    (rest ≠ [] → f.binChain ≠ []) ∧
    StackInvWith s rootLit f.binChain rest

private theorem FramePendingInv.mono {s s1 : MinState} {rootLit : Nat} {pending pending1 : List Nat}
    {f : MinFrame} (hf : FramePendingInv s rootLit pending f)
    (hcdcl : s1.cdcl = s.cdcl)
    (hrem : ∀ w, s.isRemovable w = true → s1.isRemovable w = true)
    (hpend : ∀ v ∈ pending, s1.isRemovable v = true ∨ v ∈ pending1) :
    FramePendingInv s1 rootLit pending1 f := by
  obtain ⟨hpos, cid, cl, hget, hng, hmem, hdone, hnil, hcons⟩ := hf
  refine ⟨by simpa [MinState.varLevel, hcdcl] using hpos,
    cid, cl, by simpa [hcdcl] using hget, hng, hmem, fun x hx hnot => ?_,
    by simpa [hcdcl] using hnil, by simpa [hcdcl, MinState.varLevel] using hcons⟩
  rcases hdone x hx hnot with rfl | hl0 | hr | hp
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by simpa [MinState.litLevel, MinState.varLevel, hcdcl] using hl0))
  · exact Or.inr (Or.inr (Or.inl (hrem _ hr)))
  · rcases hpend _ hp with hr1 | hp1
    · exact Or.inr (Or.inr (Or.inl hr1))
    · exact Or.inr (Or.inr (Or.inr hp1))

private theorem StackInvWith.mono {s s1 : MinState} {rootLit : Nat} {pending : List Nat} :
    ∀ stk : List MinFrame,
      StackInvWith s rootLit pending stk →
      s1.cdcl = s.cdcl →
      (∀ w, s.isRemovable w = true → s1.isRemovable w = true) →
      StackInvWith s1 rootLit pending stk
  | [], _, _, _ => trivial
  | _ :: _, ⟨hf, hne, hrest⟩, hcdcl, hrem =>
    ⟨hf.mono hcdcl hrem (fun _ hv => Or.inr hv), hne, hrest.mono _ hcdcl hrem⟩

private theorem checkLeafNode_true_sound {s : MinState} (_h : MinBaseInv s)
    {minimizing : Bool} {lit depth : Nat}
    (hok : checkLeafNode s minimizing lit depth = some true) :
    litNeg lit ∈ s.cdcl.trail.toList ∧
      (s.litLevel lit = 0 ∨ (0 < depth ∧ s.isRemovable (litVar lit) = true)) := by
  unfold checkLeafNode at hok
  by_cases htrl : trailHasLit s.cdcl.trail (litNeg lit) = true
  · have htrlf : (!trailHasLit s.cdcl.trail (litNeg lit)) = false := by simp [htrl]
    rw [htrlf, ite_eq_right (by simp)] at hok
    have hmem : litNeg lit ∈ s.cdcl.trail.toList := trailHasLit_iff.mp htrl
    by_cases hl0 : s.litLevel lit = 0
    · exact ⟨hmem, Or.inl hl0⟩
    · have hl0b : (s.litLevel lit == 0) = false := beq_false_of_ne hl0
      rw [hl0b, ite_eq_right (by simp)] at hok
      by_cases hrem : (decide (0 < depth) && s.isRemovable (litVar lit)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hrem
        exact ⟨hmem, Or.inr hrem⟩
      · have hremf : (decide (0 < depth) && s.isRemovable (litVar lit)) = false :=
          Bool.eq_false_iff.mpr hrem
        rw [hremf, ite_eq_right (by simp)] at hok
        by_cases hp : s.isPoisoned (litVar lit) = true
        · rw [ite_eq_left hp] at hok; cases hok
        · rw [ite_eq_right hp] at hok
          cases hrsn : stateReason s.cdcl lit with
          | decision | unit => rw [hrsn] at hok; cases hok
          | binary _ | large _ =>
            rw [hrsn] at hok; dsimp only at hok
            split at hok <;> cases hok
  · have htrlt : (!trailHasLit s.cdcl.trail (litNeg lit)) = true := by simp [htrl]
    rw [htrlt, ite_eq_left rfl] at hok; cases hok

private theorem checkLeafNode_none_props {s : MinState}
    {minimizing : Bool} {lit depth : Nat}
    (hnone : checkLeafNode s minimizing lit depth = none) :
    litNeg lit ∈ s.cdcl.trail.toList ∧ 0 < s.litLevel lit ∧
      (stateReason s.cdcl lit ≠ .decision ∧ stateReason s.cdcl lit ≠ .unit) := by
  unfold checkLeafNode at hnone
  by_cases htrl : trailHasLit s.cdcl.trail (litNeg lit) = true
  · have htrlf : (!trailHasLit s.cdcl.trail (litNeg lit)) = false := by simp [htrl]
    rw [htrlf, ite_eq_right (by simp)] at hnone
    have hmem := trailHasLit_iff.mp htrl
    by_cases hl0 : s.litLevel lit = 0
    · simp [hl0] at hnone
    · have hl0b : (s.litLevel lit == 0) = false := beq_false_of_ne hl0
      rw [hl0b, ite_eq_right (by simp)] at hnone
      split at hnone
      · cases hnone
      · split at hnone
        · cases hnone
        · refine ⟨hmem, Nat.pos_of_ne_zero hl0, ?_⟩
          cases hrsn : stateReason s.cdcl lit with
          | decision | unit => rw [hrsn] at hnone; simp at hnone
          | binary _ | large _ => simp
  · have htrlt : (!trailHasLit s.cdcl.trail (litNeg lit)) = true := by simp [htrl]
    rw [htrlt, ite_eq_left rfl] at hnone; cases hnone

private theorem binChainInv_closed_of_leaf {s : MinState} (h : MinBaseInv s)
    {C : List Nat} (hrem : s.RemovableInv C) {next : Nat} {chain : List Nat}
    (hchain : BinChainInv s next chain)
    (_hnext_trl : litNeg next ∈ s.cdcl.trail.toList)
    (hnext_ok : s.litLevel next = 0 ∨ s.isRemovable (litVar next) = true) :
    (setRemovableList s chain).RemovableInv C := by
  refine setRemovableList_of_closed_justified h hrem chain fun w hw _ => ?_
  obtain ⟨_, i, hi, hweq, other, hrsn, hor⟩ := hchain w hw
  refine ⟨i, hi, hweq, ?_⟩
  have hsr : stateReason (setRemovableList s chain).cdcl s.cdcl.trail[i] = .binary other := by
    unfold stateReason; rw [setRemovableList_cdcl]; exact hrsn
  unfold AntecedentsRemovable
  rw [hsr]
  rcases hor with heq_next | hmem_ch
  · rcases hnext_ok with hl0_n | hrem_n
    · exact Or.inl (by
        simpa [MinState.litLevel, MinState.varLevel, setRemovableList_cdcl, heq_next] using hl0_n)
    · exact Or.inr ((setRemovableList_isRemovable s chain _).mpr
        (Or.inl (by simpa [heq_next] using hrem_n)))
  · exact Or.inr ((setRemovableList_isRemovable s chain _).mpr (Or.inr hmem_ch))

private theorem followBinary_sound {s : MinState} (h : MinBaseInv s)
    {C : List Nat} (hrem : s.RemovableInv C) {minimizing : Bool} {maxDepth rootLit : Nat} :
    ∀ fuel next refDepth chain,
      BinChainInv s next chain →
      match followBinary s minimizing maxDepth fuel next refDepth chain with
      | .leaf true ch =>
        (setRemovableList s ch).RemovableInv C ∧
        ((litNeg next ∈ s.cdcl.trail.toList ∧
          (s.litLevel next = 0 ∨ s.isRemovable (litVar next) = true)) ∨ litVar next ∈ ch) ∧
        (∀ w ∈ chain, w ∈ ch)
      | .leaf false _ => True
      | .push ch notLit' lits' pushDepth =>
        pushDepth = refDepth ∧ refDepth < maxDepth ∧
        lits'.length ≤ maxClauseLen s.cdcl.clauses ∧
        ch ≠ [] ∧ litVar next ∈ ch ∧
        (∀ w ∈ chain, w ∈ ch) ∧
        FramePendingInv s rootLit [] ⟨notLit', lits', pushDepth, ch⟩ := by
  intro fuel
  induction fuel with
  | zero =>
    intro next refDepth chain _
    simp [followBinary]
  | succ fuel ih =>
    intro next refDepth chain hchain
    unfold followBinary
    cases hleaf : checkLeafNode s minimizing next 1 with
    | some ok =>
      dsimp only
      cases ok
      · trivial
      · obtain ⟨hmem, hok⟩ := checkLeafNode_true_sound h hleaf
        have hok' : s.litLevel next = 0 ∨ s.isRemovable (litVar next) = true := by
          rcases hok with h0 | ⟨_, hr⟩; exact Or.inl h0; exact Or.inr hr
        exact ⟨binChainInv_closed_of_leaf h hrem hchain hmem hok',
          Or.inl ⟨hmem, hok'⟩, fun _ hw => hw⟩
    | none =>
      dsimp only
      obtain ⟨hmem, hl0, _⟩ := checkLeafNode_none_props hleaf
      cases hrsn : stateReason s.cdcl next with
      | decision | unit => trivial
      | binary other =>
        dsimp only
        by_cases hlt : varLtLit s other next = true
        · rw [ite_eq_left hlt]
          have hchain' : BinChainInv s other (litVar next :: chain) := by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hprev
            · obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hmem
              refine ⟨by simpa [MinState.litLevel] using hl0, i, hi,
                by rw [hieq, litVar_litNeg], other, ?_, Or.inl rfl⟩
              have hsr : stateReason s.cdcl s.cdcl.trail[i] = stateReason s.cdcl next := by
                unfold stateReason; rw [hieq, litVar_litNeg]
              rw [hsr, hrsn]
            · obtain ⟨wl0, i, hi, hweq, oth, hoth, hor⟩ := hchain w hprev
              refine ⟨wl0, i, hi, hweq, oth, hoth, ?_⟩
              rcases hor with heq_n | hmem_c
              · exact Or.inr (List.mem_cons.mpr (Or.inl heq_n))
              · exact Or.inr (List.mem_cons_of_mem _ hmem_c)
          have hih := ih other refDepth (litVar next :: chain) hchain'
          cases hres : followBinary s minimizing maxDepth fuel
              other refDepth (litVar next :: chain) <;> rw [hres] at hih
          · cases ‹Bool›
            · trivial
            · dsimp only at hih
              exact ⟨hih.1, Or.inr (hih.2.2 (litVar next) (by simp)),
                fun w hw => hih.2.2 w (List.mem_cons_of_mem _ hw)⟩
          · dsimp only at hih
            refine ⟨hih.1, hih.2.1, hih.2.2.1, hih.2.2.2.1,
              hih.2.2.2.2.2.1 (litVar next) (by simp),
              fun w hw => hih.2.2.2.2.2.1 w (List.mem_cons_of_mem _ hw), hih.2.2.2.2.2.2⟩
        · rw [ite_eq_right hlt]; trivial
      | large cid =>
        dsimp only
        by_cases hdep : refDepth < maxDepth
        · rw [ite_eq_left hdep]
          cases hget : s.cdcl.clauses[cid]? with
          | none => trivial
          | some opt =>
            cases opt with
            | none => trivial
            | some cl =>
              dsimp only
              by_cases hok : (!cl.garbage && cl.lits.contains (litNeg next)) = true
              · rw [ite_eq_left hok]
                simp only [Bool.and_eq_true, List.contains_iff_mem] at hok
                refine ⟨rfl, hdep, clause_len_le_maxClauseLen hget, by simp, by simp,
                  fun _ hw => List.mem_cons_of_mem _ hw, ?_⟩
                refine ⟨fun x hx => ?_, cid, cl, hget, hok.1, hok.2,
                  fun x hx hnot => absurd hx hnot, fun hne => by simp at hne, fun _ => ?_⟩
                · rcases List.mem_cons.mp hx with rfl | hprev
                  · simpa [MinState.litLevel] using hl0
                  · exact (hchain x hprev).1
                · refine ⟨hmem, ?_, fun w hw => ?_⟩
                  · have hsr : stateReason s.cdcl (litNeg next) = stateReason s.cdcl next := by
                      simp [stateReason]
                    rw [hsr, hrsn]
                  · rcases List.mem_cons.mp hw with rfl | hprev
                    · obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hmem
                      exact ⟨by simpa [MinState.litLevel] using hl0, i, hi,
                        by rw [hieq, litVar_litNeg], Or.inl hieq⟩
                    · obtain ⟨wl0, i, hi, hweq, oth, hoth, hor⟩ := hchain w hprev
                      refine ⟨wl0, i, hi, hweq, Or.inr ⟨oth, hoth, ?_⟩⟩
                      rcases hor with heq_n | hmem_c
                      · exact List.mem_cons.mpr (Or.inl heq_n)
                      · exact List.mem_cons_of_mem _ hmem_c
              · rw [ite_eq_right hok]; trivial
        · rw [ite_eq_right hdep]; trivial

/-- Every popped frame `f` (`f.remLits = []`) preserves `RemovableInv` when marking `f.binChain`
(for `f.binChain ≠ []`) and provides `AntecedentsRemovable` for `litNeg rootLit` (or caches
`f.binChain`). -/
private theorem frame_finish_sound {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hrem : s.RemovableInv C) {rootLit : Nat} {f : MinFrame}
    (hf : FramePendingInv s rootLit [] f) (hnil_lits : f.remLits = []) :
    let s1 := setRemovableList s f.binChain
    s1.RemovableInv C ∧
    (f.binChain = [] → AntecedentsRemovable s1 (litNeg rootLit)) ∧
    (f.binChain ≠ [] → ∀ v ∈ f.binChain, s1.isRemovable v = true) := by
  obtain ⟨_, cid, cl, hget, hng, hmem, hdone, hnil, hcons⟩ := hf
  have hant_fn : AntecedentsRemovable (setRemovableList s f.binChain) f.notLit := by
    have hget' : (setRemovableList s f.binChain).cdcl.clauses[cid]? = some (some cl) := by
      simpa [setRemovableList_cdcl] using hget
    cases hbc : f.binChain with
    | nil =>
      obtain ⟨hnl, hrsn⟩ := hnil hbc
      unfold AntecedentsRemovable
      have hsr : stateReason (setRemovableList s []).cdcl f.notLit = .large cid := by
        rw [setRemovableList_cdcl, hnl]; exact hrsn
      rw [hsr]
      refine ⟨cl, by simpa [← hbc] using hget', hng, hnl ▸ hmem, fun x hx hne => ?_⟩
      rcases hdone x hx (by simp [hnil_lits]) with rfl | hl0 | hrem_x | hpend
      · exact absurd rfl hne
      · exact Or.inl (by simpa [MinState.litLevel, MinState.varLevel,
          setRemovableList_cdcl] using hl0)
      · exact Or.inr ((setRemovableList_isRemovable s [] _).mpr (Or.inl hrem_x))
      · cases hpend
    | cons hd tl =>
      have hne : f.binChain ≠ [] := by simp [hbc]
      obtain ⟨_, hrsn, _⟩ := hcons hne
      unfold AntecedentsRemovable
      have hsr : stateReason (setRemovableList s (hd :: tl)).cdcl f.notLit = .large cid := by
        rw [setRemovableList_cdcl]; exact hrsn
      rw [hsr]
      refine ⟨cl, by simpa [← hbc] using hget', hng, hmem, fun x hx hne' => ?_⟩
      rcases hdone x hx (by simp [hnil_lits]) with rfl | hl0 | hrem_x | hpend
      · exact absurd rfl hne'
      · exact Or.inl (by simpa [MinState.litLevel, MinState.varLevel,
          setRemovableList_cdcl] using hl0)
      · exact Or.inr ((setRemovableList_isRemovable s (hd :: tl) _).mpr (Or.inl hrem_x))
      · cases hpend
  have hrem1 : (setRemovableList s f.binChain).RemovableInv C := by
    cases hbc : f.binChain with
    | nil =>
      have hext : ∀ w, (setRemovableList s []).isRemovable w = s.isRemovable w := fun _ => rfl
      exact (removableInv_congr (setRemovableList_cdcl _ _) (setRemovableList_trailPos _ _)
        hext).mpr hrem
    | cons _ _ =>
      have hne : f.binChain ≠ [] := by simp [hbc]
      obtain ⟨_, _, hall⟩ := hcons hne
      rw [← hbc]
      refine setRemovableList_of_closed_justified h hrem f.binChain fun v hv _ => ?_
      obtain ⟨_, i, hi, hweq, hkind⟩ := hall v hv
      refine ⟨i, hi, hweq, ?_⟩
      rcases hkind with htr_eq | ⟨other, hoth, hoth_mem⟩
      · rw [htr_eq]; exact hant_fn
      · have hsr : stateReason (setRemovableList s f.binChain).cdcl s.cdcl.trail[i] =
            .binary other := by
          unfold stateReason; rw [setRemovableList_cdcl]; exact hoth
        unfold AntecedentsRemovable
        rw [hsr]
        exact Or.inr ((setRemovableList_isRemovable s f.binChain _).mpr (Or.inr hoth_mem))
  refine ⟨hrem1, fun hbc => ?_, fun _ v hv => (setRemovableList_isRemovable s f.binChain _).mpr
    (Or.inr hv)⟩
  obtain ⟨hnl, _⟩ := hnil hbc
  simpa [hnl] using hant_fn

/-- Soundness of `minWorklist` starting from a valid stack `stk`: preserves `MinBaseInv` and
`RemovableInv C`, and if `minWorklist` returns `(true, s')`, then the bottom frame's
`binChain` (or `AntecedentsRemovable s' (litNeg rootLit)`) is certified. -/
private theorem minWorklist_inv {minimizing : Bool} {maxDepth rootLit : Nat} {C : List Nat} :
    ∀ (m : Nat) (s : MinState) (stk : List MinFrame),
      worklistMeasure maxDepth (maxClauseLen s.cdcl.clauses + 2) stk = m →
      MinBaseInv s → s.RemovableInv C →
      StackInvWith s rootLit [] stk →
      let (ok, s') := minWorklist minimizing maxDepth s stk
      MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
      s'.RemovableInv C ∧ (∀ w, s.isRemovable w = true → s'.isRemovable w = true) ∧
      (ok = true → ∀ fbot, stk.getLast? = some fbot →
        (fbot.binChain = [] → AntecedentsRemovable s' (litNeg rootLit)) ∧
        (fbot.binChain ≠ [] → ∀ v ∈ fbot.binChain, s'.isRemovable v = true)) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro s stk hm hbase hrem hstk
    cases stk with
    | nil =>
      rw [minWorklist]
      exact ⟨hbase, rfl, rfl, hrem, fun _ hw => hw, fun _ _ h => by simp at h⟩
    | cons f rest =>
      rw [minWorklist]
      dsimp only
      obtain ⟨hf, hne_f, hrest_inv⟩ := hstk
      cases hrl : f.remLits with
      | nil =>
        obtain ⟨hrem1, hnil1, hcons1⟩ := frame_finish_sound hbase hrem hf hrl
        let s1 := setRemovableList s f.binChain
        have hbase1 : MinBaseInv s1 := hbase.setRemovableList f.binChain
        have hmono1 : ∀ w, s.isRemovable w = true → s1.isRemovable w = true :=
          fun w hw => (setRemovableList_isRemovable s f.binChain w).mpr (Or.inl hw)
        have hstk1 : StackInvWith s1 rootLit [] rest := by
          cases rest with
          | nil => trivial
          | cons f' rest' =>
            obtain ⟨hf', hne', hrest'⟩ := hrest_inv
            exact ⟨hf'.mono (setRemovableList_cdcl _ _) hmono1
              (fun v hv => Or.inl ((setRemovableList_isRemovable s f.binChain v).mpr
                (Or.inr hv))),
              hne', hrest'.mono _ (setRemovableList_cdcl _ _) hmono1⟩
        have hm1 : worklistMeasure maxDepth (maxClauseLen s1.cdcl.clauses + 2) rest < m := by
          rw [← hm, worklistMeasure_cons, setRemovableList_cdcl]
          have hw : 0 < frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f := by
            unfold frameWeight
            exact Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by omega))
          omega
        have hih := ih _ hm1 s1 rest rfl hbase1 hrem1 hstk1
        cases hres : minWorklist minimizing maxDepth s1 rest with
        | mk ok s' =>
          rw [hres] at hih
          refine ⟨hih.1, hih.2.1.trans (setRemovableList_cdcl _ _),
            hih.2.2.1.trans (setRemovableList_trailPos _ _), hih.2.2.2.1,
            fun w hw => hih.2.2.2.2.1 w (hmono1 w hw), fun hok fbot hbot => ?_⟩
          cases rest with
          | nil =>
            simp only [List.getLast?_singleton, Option.some.injEq] at hbot; subst hbot
            have hs'eq : s' = s1 := by simp [minWorklist] at hres; exact hres.2.symm
            subst hs'eq
            exact ⟨hnil1, hcons1⟩
          | cons g gs =>
            have hbot' : (g :: gs).getLast? = some fbot := by
              simpa [List.getLast?_cons_cons] using hbot
            exact hih.2.2.2.2.2 hok fbot hbot'
      | cons y ys =>
        dsimp only
        let f' : MinFrame := { f with remLits := ys }
        have hstep_f' : ∀ (st : MinState) (pend : List Nat),
            st.cdcl = s.cdcl →
            (∀ w, s.isRemovable w = true → st.isRemovable w = true) →
            (y = f.notLit ∨ st.litLevel y = 0 ∨ st.isRemovable (litVar y) = true ∨
              litVar y ∈ pend) →
            FramePendingInv st rootLit pend f' := by
          intro st pend hst_cdcl hst_mono hyok
          obtain ⟨hpos, cid, cl, hget, hng, hmem, hdone, hnil, hcons⟩ := hf
          refine ⟨by simpa [MinState.varLevel, hst_cdcl] using hpos,
            cid, cl, by simpa [hst_cdcl] using hget, hng, hmem, fun x hx hnot => ?_,
            by simpa [hst_cdcl] using hnil,
            by simpa [hst_cdcl, MinState.varLevel] using hcons⟩
          by_cases hxy : x = y
          · subst hxy
            rcases hyok with rfl | hl0 | hrm | hp
            · exact Or.inl rfl
            · exact Or.inr (Or.inl hl0)
            · exact Or.inr (Or.inr (Or.inl hrm))
            · exact Or.inr (Or.inr (Or.inr hp))
          · have hnot_f : x ∉ f.remLits := by
              rw [hrl]; intro hm; rcases List.mem_cons.mp hm with rfl | hys
              · exact hxy rfl
              · exact hnot hys
            rcases hdone x hx hnot_f with rfl | hl0 | hrm | hpend
            · exact Or.inl rfl
            · exact Or.inr (Or.inl (by simpa [MinState.litLevel, MinState.varLevel, hst_cdcl]
                using hl0))
            · exact Or.inr (Or.inr (Or.inl (hst_mono _ hrm)))
            · cases hpend
        by_cases hy_eq : y = f.notLit
        · have hyb : (y == f.notLit) = true := by simp [hy_eq]
          rw [ite_eq_left hyb]
          have hstk' : StackInvWith s rootLit [] (f' :: rest) :=
            ⟨hstep_f' s [] rfl (fun _ hw => hw) (Or.inl hy_eq),
              hne_f, hrest_inv⟩
          have hm' : worklistMeasure maxDepth
              (maxClauseLen s.cdcl.clauses + 2) (f' :: rest) < m := by
            rw [← hm, worklistMeasure_cons, worklistMeasure_cons]
            have hlt := frameWeight_step_lt (maxDepth := maxDepth)
              (base := maxClauseLen s.cdcl.clauses + 2) (by omega)
              (notLit := f.notLit) (y := y) (ys := ys) (d := f.depth) (ch := f.binChain)
            have hfeq : frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f =
                frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2)
                  ⟨f.notLit, y :: ys, f.depth, f.binChain⟩ := by simp [frameWeight, hrl]
            rw [hfeq]
            simpa [f'] using Nat.add_lt_add_right hlt
              (worklistMeasure maxDepth (maxClauseLen s.cdcl.clauses + 2) rest)
          have hih := ih _ hm' s (f' :: rest) rfl hbase hrem hstk'
          cases hres : minWorklist minimizing maxDepth s (f' :: rest) with
          | mk ok s' =>
            rw [hres] at hih
            refine ⟨hih.1, hih.2.1, hih.2.2.1, hih.2.2.2.1, hih.2.2.2.2.1, fun hok fbot hbot => ?_⟩
            cases rest with
            | nil =>
              simp only [List.getLast?_singleton, Option.some.injEq] at hbot; subst hbot
              exact hih.2.2.2.2.2 hok f' (by simp)
            | cons g gs =>
              have hbot' : (f' :: g :: gs).getLast? = some fbot := by
                simpa [List.getLast?_cons_cons] using hbot
              exact hih.2.2.2.2.2 hok fbot hbot'
        · have hyb : ¬ ((y == f.notLit) = true) := by simp [hy_eq]
          rw [ite_eq_right hyb]
          have hfb := followBinary_sound hbase hrem (minimizing := minimizing)
            (maxDepth := maxDepth) (rootLit := rootLit)
            (s.cdcl.trail.size + 1) y (f.depth + 1) [] (fun _ h => by cases h)
          cases hfb_res : followBinary s minimizing maxDepth (s.cdcl.trail.size + 1)
              y (f.depth + 1) [] with
          | leaf ok ch =>
            rw [hfb_res] at hfb
            cases ok with
            | false =>
              dsimp only
              exact ⟨(hbase.setPoisonedList ch).poisonStack _,
                (poisonStack_cdcl _ _).trans (setPoisonedList_cdcl _ _),
                (poisonStack_trailPos _ _).trans (setPoisonedList_trailPos _ _),
                (removableInv_poisonStack (C := C) _).mpr
                  ((removableInv_setPoisonedList (C := C) _).mpr hrem),
                fun w hw => by
                  rw [poisonStack_isRemovable, setPoisonedList_isRemovable]; exact hw,
                fun hfalse => by cases hfalse⟩
            | true =>
              dsimp only
              let s1 := setRemovableList s ch
              have hbase1 : MinBaseInv s1 := hbase.setRemovableList ch
              have hrem1 : s1.RemovableInv C := hfb.1
              have hmono1 : ∀ w, s.isRemovable w = true → s1.isRemovable w = true :=
                fun w hw => (setRemovableList_isRemovable s ch w).mpr (Or.inl hw)
              have hyok : s1.litLevel y = 0 ∨ s1.isRemovable (litVar y) = true := by
                rcases hfb.2.1 with ⟨_, h0 | hr⟩ | hmem
                · exact Or.inl (by simpa [s1, MinState.litLevel, MinState.varLevel,
                    setRemovableList_cdcl] using h0)
                · exact Or.inr (hmono1 _ hr)
                · exact Or.inr ((setRemovableList_isRemovable s ch _).mpr (Or.inr hmem))
              have hstk1 : StackInvWith s1 rootLit [] (f' :: rest) :=
                ⟨hstep_f' s1 [] (setRemovableList_cdcl _ _) hmono1
                  (hyok.elim (fun a => Or.inr (Or.inl a))
                    (fun b => Or.inr (Or.inr (Or.inl b)))),
                  hne_f, hrest_inv.mono _ (setRemovableList_cdcl _ _) hmono1⟩
              have hm1 : worklistMeasure maxDepth (maxClauseLen s1.cdcl.clauses + 2)
                  (f' :: rest) < m := by
                rw [← hm, setRemovableList_cdcl, worklistMeasure_cons, worklistMeasure_cons]
                have hlt := frameWeight_step_lt (maxDepth := maxDepth)
                  (base := maxClauseLen s.cdcl.clauses + 2) (by omega)
                  (notLit := f.notLit) (y := y) (ys := ys) (d := f.depth) (ch := f.binChain)
                have hfeq : frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f =
                    frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2)
                      ⟨f.notLit, y :: ys, f.depth, f.binChain⟩ := by simp [frameWeight, hrl]
                rw [hfeq]
                simpa [f'] using Nat.add_lt_add_right hlt
                  (worklistMeasure maxDepth (maxClauseLen s.cdcl.clauses + 2) rest)
              have hih := ih _ hm1 s1 (f' :: rest) rfl hbase1 hrem1 hstk1
              cases hres : minWorklist minimizing maxDepth s1 (f' :: rest) with
              | mk ok s' =>
                rw [hres] at hih
                refine ⟨hih.1, hih.2.1.trans (setRemovableList_cdcl _ _),
                  hih.2.2.1.trans (setRemovableList_trailPos _ _), hih.2.2.2.1,
                  fun w hw => hih.2.2.2.2.1 w (hmono1 w hw), fun hok fbot hbot => ?_⟩
                cases rest with
                | nil =>
                  simp only [List.getLast?_singleton, Option.some.injEq] at hbot; subst hbot
                  exact hih.2.2.2.2.2 hok f' (by simp)
                | cons g gs =>
                  have hbot' : (f' :: g :: gs).getLast? = some fbot := by
                    simpa [List.getLast?_cons_cons] using hbot
                  exact hih.2.2.2.2.2 hok fbot hbot'
          | push ch notLit' lits' pushDepth =>
            rw [hfb_res] at hfb
            obtain ⟨rfl, hdep, hlen, hch_ne, hy_ch, _, hg_inv⟩ := hfb
            dsimp only
            by_cases hcond : (lits'.length + 1 < maxClauseLen s.cdcl.clauses + 2 ∧
                f.depth + 1 < maxDepth ∧ f.depth + 1 = f.depth + 1)
            · rw [dite_eq_left hcond]
              let g : MinFrame := ⟨notLit', lits', f.depth + 1, ch⟩
              have hf'_pend : FramePendingInv s rootLit ch f' :=
                hstep_f' s ch rfl (fun _ hw => hw) (Or.inr (Or.inr (Or.inr hy_ch)))
              have hstk' : StackInvWith s rootLit [] (g :: f' :: rest) :=
                ⟨hg_inv, fun _ => hch_ne, ⟨hf'_pend, hne_f, hrest_inv⟩⟩
              have hm' : worklistMeasure maxDepth (maxClauseLen s.cdcl.clauses + 2)
                  (g :: f' :: rest) < m := by
                rw [← hm, worklistMeasure_cons, worklistMeasure_cons, worklistMeasure_cons]
                have hlt := frameWeight_push_lt (maxDepth := maxDepth)
                  (base := maxClauseLen s.cdcl.clauses + 2) (by omega)
                  (notLit := f.notLit) (y := y) (notLit' := notLit') (ys := ys)
                  (lits := lits') (d := f.depth) (ch := f.binChain) (ch' := ch)
                  hcond.2.1 hcond.1
                have hfeq : frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2) f =
                    frameWeight maxDepth (maxClauseLen s.cdcl.clauses + 2)
                      ⟨f.notLit, y :: ys, f.depth, f.binChain⟩ := by simp [frameWeight, hrl]
                rw [hfeq]
                have hadd := Nat.add_lt_add_right hlt
                  (worklistMeasure maxDepth (maxClauseLen s.cdcl.clauses + 2) rest)
                dsimp only [f', g]; omega
              have hih := ih _ hm' s (g :: f' :: rest) rfl hbase hrem hstk'
              cases hres : minWorklist minimizing maxDepth s (g :: f' :: rest) with
              | mk ok s' =>
                rw [hres] at hih
                refine ⟨hih.1, hih.2.1, hih.2.2.1, hih.2.2.2.1, hih.2.2.2.2.1,
                  fun hok fbot hbot => ?_⟩
                cases rest with
                | nil =>
                  simp only [List.getLast?_singleton, Option.some.injEq] at hbot; subst hbot
                  exact hih.2.2.2.2.2 hok f' (by simp [List.getLast?_cons_cons])
                | cons k ks =>
                  have hbot' : (g :: f' :: k :: ks).getLast? = some fbot := by
                    simpa [List.getLast?_cons_cons] using hbot
                  exact hih.2.2.2.2.2 hok fbot hbot'
            · exfalso; exact hcond ⟨by omega, hdep, rfl⟩

/-- Unified soundness of `minimizeLiteralWorklist` for both `depth0 = 0` (cut deletion) and
`depth0 > 0` (marking `litVar lit` as `removable`). -/
theorem minimizeLiteralWorklist_gen_sound {s : MinState} (h : MinBaseInv s)
    {C : List Nat} (hrem : s.RemovableInv C) (minimizing : Bool) (maxDepth lit depth0 : Nat) :
    let (ok, s') := minimizeLiteralWorklist s minimizing maxDepth lit depth0
    MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
    s'.RemovableInv C ∧ (∀ w, s.isRemovable w = true → s'.isRemovable w = true) ∧
    (ok = true → litNeg lit ∈ s'.cdcl.trail.toList ∧
      (s'.litLevel lit = 0 ∨
        (0 < depth0 ∧ s'.isRemovable (litVar lit) = true) ∨
        (depth0 = 0 ∧ AntecedentsRemovable s' (litNeg lit)))) := by
  unfold minimizeLiteralWorklist
  by_cases hmd : maxDepth = 0
  · rw [ite_eq_left (beq_iff_eq.mpr hmd)]; dsimp only
    exact ⟨h, rfl, rfl, hrem, fun _ hw => hw, fun hf => by cases hf⟩
  · by_cases hge : maxDepth ≤ depth0
    · rw [ite_eq_right (by simp [hmd]), ite_eq_left hge]; dsimp only
      exact ⟨h, rfl, rfl, hrem, fun _ hw => hw, fun hf => by cases hf⟩
    · rw [ite_eq_right (by simp [hmd]), ite_eq_right hge]
      cases hleaf : checkLeafNode s minimizing lit depth0 with
      | some ok =>
        cases ok
        · dsimp only; exact ⟨h, rfl, rfl, hrem, fun _ hw => hw, fun hf => by cases hf⟩
        · obtain ⟨hmem, hok⟩ := checkLeafNode_true_sound h hleaf
          refine ⟨h, rfl, rfl, hrem, fun _ hw => hw, fun _ => ⟨hmem, ?_⟩⟩
          rcases hok with h0 | ⟨hd, hr⟩
          · exact Or.inl h0
          · exact Or.inr (Or.inl ⟨hd, hr⟩)
      | none =>
        obtain ⟨hmem, hl0, _⟩ := checkLeafNode_none_props hleaf
        dsimp only
        let initChain := if depth0 == 0 then [] else [litVar lit]
        have hinit_bin : ∀ other, stateReason s.cdcl lit = .binary other →
            BinChainInv s other initChain := by
          intro other hrsn w hw
          by_cases hd0 : depth0 = 0
          · simp [initChain, hd0] at hw
          · have hdb : (depth0 == 0) = false := beq_false_of_ne hd0
            simp only [initChain, hdb, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hw
            subst hw
            obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hmem
            refine ⟨by simpa [MinState.litLevel] using hl0, i, hi, by rw [hieq, litVar_litNeg],
              other, ?_, Or.inl rfl⟩
            have hsr : stateReason s.cdcl s.cdcl.trail[i] = stateReason s.cdcl lit := by
              unfold stateReason; rw [hieq, litVar_litNeg]
            rw [hsr, hrsn]
        cases hrsn : stateReason s.cdcl lit with
        | decision | unit =>
          dsimp only; exact ⟨h, rfl, rfl, hrem, fun _ hw => hw, fun hf => by cases hf⟩
        | binary other =>
          dsimp only
          by_cases hlt : varLtLit s other lit = true
          · rw [ite_eq_left hlt]
            have hfb := followBinary_sound h hrem (minimizing := minimizing)
              (maxDepth := maxDepth) (rootLit := lit) (s.cdcl.trail.size + 1)
              other (depth0 + 1) initChain (hinit_bin other hrsn)
            cases hfb_res : followBinary s minimizing maxDepth (s.cdcl.trail.size + 1)
                other (depth0 + 1) initChain with
            | leaf ok ch =>
              rw [hfb_res] at hfb
              cases ok with
              | false =>
                dsimp only
                exact ⟨h.setPoisonedList ch, setPoisonedList_cdcl _ _,
                  setPoisonedList_trailPos _ _,
                  (removableInv_setPoisonedList (C := C) _).mpr hrem,
                  fun w hw => by rw [setPoisonedList_isRemovable]; exact hw,
                  fun hf => by cases hf⟩
              | true =>
                dsimp only
                let s1 := setRemovableList s ch
                have hbase1 : MinBaseInv s1 := h.setRemovableList ch
                have hmono1 : ∀ w, s.isRemovable w = true → s1.isRemovable w = true :=
                  fun w hw => (setRemovableList_isRemovable s ch w).mpr (Or.inl hw)
                refine ⟨hbase1, setRemovableList_cdcl _ _, setRemovableList_trailPos _ _,
                  hfb.1, hmono1, fun _ => ⟨by simpa [s1, setRemovableList_cdcl] using hmem, ?_⟩⟩
                by_cases hd0 : depth0 = 0
                · have hant : AntecedentsRemovable s1 (litNeg lit) := by
                    unfold AntecedentsRemovable
                    have hsr : stateReason s1.cdcl (litNeg lit) = .binary other := by
                      simp only [s1, setRemovableList_cdcl, stateReason, litVar_litNeg]
                      simpa [stateReason] using hrsn
                    rw [hsr]
                    rcases hfb.2.1 with ⟨_, h0 | hr⟩ | hmem_ch
                    · exact Or.inl (by simpa [s1, MinState.litLevel, MinState.varLevel,
                        setRemovableList_cdcl] using h0)
                    · exact Or.inr (hmono1 _ hr)
                    · exact Or.inr ((setRemovableList_isRemovable s ch _).mpr (Or.inr hmem_ch))
                  exact Or.inr (Or.inr ⟨hd0, hant⟩)
                · have hdb : (depth0 == 0) = false := beq_false_of_ne hd0
                  have hlit_in : litVar lit ∈ ch :=
                    hfb.2.2 (litVar lit) (by simp [initChain, hdb])
                  exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero hd0,
                    (setRemovableList_isRemovable s ch _).mpr (Or.inr hlit_in)⟩)
            | push ch notLit' lits' pushDepth =>
              rw [hfb_res] at hfb
              dsimp only
              obtain ⟨rfl, _, _, hch_ne, hoth_ch, hinit_ch, hg_inv⟩ := hfb
              have hinv := minWorklist_inv (minimizing := minimizing) (maxDepth := maxDepth)
                (rootLit := lit) (C := C) _ s [⟨notLit', lits', depth0 + 1, ch⟩] rfl h hrem
                ⟨hg_inv, fun hne => absurd rfl hne, trivial⟩
              cases hmw : minWorklist minimizing maxDepth s [⟨notLit', lits', depth0 + 1, ch⟩] with
              | mk ok s' =>
                rw [hmw] at hinv
                refine ⟨hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1,
                  fun hok => ⟨by simpa [hinv.2.1] using hmem, ?_⟩⟩
                have hbot := (hinv.2.2.2.2.2 hok ⟨notLit', lits', depth0 + 1, ch⟩
                  (by simp)).2 hch_ne
                by_cases hd0 : depth0 = 0
                · have hant : AntecedentsRemovable s' (litNeg lit) := by
                    unfold AntecedentsRemovable
                    have hsr : stateReason s'.cdcl (litNeg lit) = .binary other := by
                      rw [hinv.2.1]; simpa [stateReason] using hrsn
                    rw [hsr]
                    exact Or.inr (hbot _ hoth_ch)
                  exact Or.inr (Or.inr ⟨hd0, hant⟩)
                · have hdb : (depth0 == 0) = false := beq_false_of_ne hd0
                  exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero hd0,
                    hbot _ (hinit_ch (litVar lit) (by simp [initChain, hdb]))⟩)
          · rw [ite_eq_right hlt]
            exact ⟨h.setPoisonedList initChain, setPoisonedList_cdcl _ _,
              setPoisonedList_trailPos _ _,
              (removableInv_setPoisonedList (C := C) _).mpr hrem,
              fun w hw => by rw [setPoisonedList_isRemovable]; exact hw,
              fun hf => by cases hf⟩
        | large cid =>
          dsimp only
          cases hget : s.cdcl.clauses[cid]? with
          | none =>
            dsimp only
            exact ⟨h.setPoisonedList initChain, setPoisonedList_cdcl _ _,
              setPoisonedList_trailPos _ _,
              (removableInv_setPoisonedList (C := C) _).mpr hrem,
              fun w hw => by rw [setPoisonedList_isRemovable]; exact hw,
              fun hf => by cases hf⟩
          | some opt =>
            cases opt with
            | none =>
              dsimp only
              exact ⟨h.setPoisonedList initChain, setPoisonedList_cdcl _ _,
                setPoisonedList_trailPos _ _,
                (removableInv_setPoisonedList (C := C) _).mpr hrem,
                fun w hw => by rw [setPoisonedList_isRemovable]; exact hw,
                fun hf => by cases hf⟩
            | some cl =>
              dsimp only
              by_cases hok : (!cl.garbage && cl.lits.contains (litNeg lit)) = true
              · rw [ite_eq_left hok]
                simp only [Bool.and_eq_true, List.contains_iff_mem] at hok
                have hf0 : FramePendingInv s lit [] ⟨litNeg lit, cl.lits, depth0, initChain⟩ := by
                  refine ⟨fun x hx => ?_, cid, cl, hget, hok.1, hok.2,
                    fun x hx hnot => absurd hx hnot, fun _ => ⟨rfl, ?_⟩, fun _ => ?_⟩
                  · by_cases hd0 : depth0 = 0
                    · simp [initChain, hd0] at hx
                    · have hdb : (depth0 == 0) = false := beq_false_of_ne hd0
                      simp only [initChain, hdb, Bool.false_eq_true, ↓reduceIte,
                        List.mem_singleton] at hx
                      subst hx; simpa [MinState.litLevel] using hl0
                  · simpa [stateReason] using hrsn
                  · refine ⟨hmem, by simpa [stateReason] using hrsn, fun w hw => ?_⟩
                    by_cases hd0 : depth0 = 0
                    · simp [initChain, hd0] at hw
                    · have hdb : (depth0 == 0) = false := beq_false_of_ne hd0
                      simp only [initChain, hdb, Bool.false_eq_true, ↓reduceIte,
                        List.mem_singleton] at hw
                      subst hw
                      obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hmem
                      exact ⟨by simpa [MinState.litLevel] using hl0, i, hi,
                        by rw [hieq, litVar_litNeg], Or.inl hieq⟩
                have hinv := minWorklist_inv (minimizing := minimizing) (maxDepth := maxDepth)
                  (rootLit := lit) (C := C) _ s
                  [⟨litNeg lit, cl.lits, depth0, initChain⟩] rfl h hrem
                  ⟨hf0, fun hne => absurd rfl hne, trivial⟩
                cases hmw : minWorklist minimizing maxDepth s
                    [⟨litNeg lit, cl.lits, depth0, initChain⟩] with
                | mk ok s' =>
                  rw [hmw] at hinv
                  refine ⟨hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1,
                    fun htok => ⟨by simpa [hinv.2.1] using hmem, ?_⟩⟩
                  have hbot := hinv.2.2.2.2.2 htok ⟨litNeg lit, cl.lits, depth0, initChain⟩
                    (by simp)
                  by_cases hd0 : depth0 = 0
                  · have hbc : initChain = [] := by simp [initChain, hd0]
                    exact Or.inr (Or.inr ⟨hd0, hbot.1 hbc⟩)
                  · have hdb : (depth0 == 0) = false := beq_false_of_ne hd0
                    have hbc : initChain ≠ [] := by simp [initChain, hdb]
                    exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero hd0,
                      hbot.2 hbc (litVar lit) (by simp [initChain, hdb])⟩)
              · rw [ite_eq_right hok]
                exact ⟨h.setPoisonedList initChain, setPoisonedList_cdcl _ _,
                  setPoisonedList_trailPos _ _,
                  (removableInv_setPoisonedList (C := C) _).mpr hrem,
                  fun w hw => by rw [setPoisonedList_isRemovable]; exact hw,
                  fun hf => by cases hf⟩

/-- Soundness of depth-0 `minimizeLiteralWorklist` (`cut_delete_sound`): preserves `MinBaseInv`
and `RemovableInv C`, and when returning `(true, s')`, deleting `lit` from `C` preserves both
`F₀.EntailsClause` and `s'.RemovableInv (C.filter (· != lit))`. -/
theorem minimizeLiteralWorklist_sound {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause C))
    (hrem : s.RemovableInv C) (minimizing : Bool) (maxDepth lit : Nat) :
    let (ok, s') := minimizeLiteralWorklist s minimizing maxDepth lit 0
    MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
    s'.RemovableInv C ∧ (∀ w, s.isRemovable w = true → s'.isRemovable w = true) ∧
    (ok = true →
      let C' := C.filter (· != lit)
      s'.cdcl.f0.EntailsClause (cnfClause C') ∧ s'.RemovableInv C') := by
  have hg := minimizeLiteralWorklist_gen_sound h hrem minimizing maxDepth lit 0
  cases hres : minimizeLiteralWorklist s minimizing maxDepth lit 0 with
  | mk ok s' =>
    rw [hres] at hg
    refine ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, fun hok => ?_⟩
    obtain ⟨hmem, hkind⟩ := hg.2.2.2.2.2 hok
    have hjust : s'.litLevel lit = 0 ∨ AntecedentsRemovable s' (litNeg lit) := by
      rcases hkind with h0 | ⟨hpos, _⟩ | ⟨_, ha⟩
      · exact Or.inl h0
      · omega
      · exact Or.inr ha
    exact cut_delete_sound hg.1 (by simpa [hg.2.1] using hent) hg.2.2.2.1 hmem hjust

/-- Soundness of non-root `minimizeLiteralWorklist` (`depth0 = 1`, used by `shrink_literal`):
preserves `MinBaseInv` and `RemovableInv C`, and certifies `litLevel lit = 0 ∨ isRemovable`. -/
theorem minimizeLiteralWorklist_sub_sound {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hrem : s.RemovableInv C) (minimizing : Bool) (maxDepth lit : Nat) :
    let (ok, s') := minimizeLiteralWorklist s minimizing maxDepth lit 1
    MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
    s'.RemovableInv C ∧ (∀ w, s.isRemovable w = true → s'.isRemovable w = true) ∧
    (ok = true → litNeg lit ∈ s'.cdcl.trail.toList ∧
      (s'.litLevel lit = 0 ∨ s'.isRemovable (litVar lit) = true)) := by
  have hg := minimizeLiteralWorklist_gen_sound h hrem minimizing maxDepth lit 1
  cases hres : minimizeLiteralWorklist s minimizing maxDepth lit 1 with
  | mk ok s' =>
    rw [hres] at hg
    refine ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, fun hok => ?_⟩
    obtain ⟨hmem, hkind⟩ := hg.2.2.2.2.2 hok
    refine ⟨hmem, ?_⟩
    rcases hkind with h0 | ⟨_, hr⟩ | ⟨hd0, _⟩
    · exact Or.inl h0
    · exact Or.inr hr
    · omega

/-- Shared soundness induction for greedy left-to-right clause/block literal minimization
folds inside surrounding literals `pref ++ acc.reverse ++ xs ++ suff`. -/
theorem minimizeLiteralFold_sound {s : MinState}
    {pref suff B : List Nat} (maxDepth : Nat) :
    ∀ (xs acc : List Nat) (st : MinState),
      MinBaseInv st → st.cdcl = s.cdcl → st.trailPos = s.trailPos →
      st.cdcl.f0.EntailsClause (cnfClause (pref ++ acc.reverse ++ xs ++ suff)) →
      st.RemovableInv (pref ++ acc.reverse ++ xs ++ suff) →
      (∀ l ∈ acc, litNeg l ∈ st.cdcl.trail.toList ∧ l ∈ B) →
      (∀ l ∈ xs, litNeg l ∈ st.cdcl.trail.toList ∧ l ∈ B) →
      let res := xs.foldl (fun (p : List Nat × MinState) lit =>
        let (ok, st') := minimizeLiteralWorklist p.2 true maxDepth lit 0
        if ok then (p.1, st') else (lit :: p.1, st')) (acc, st)
      MinBaseInv res.2 ∧ res.2.cdcl = s.cdcl ∧ res.2.trailPos = s.trailPos ∧
      res.2.cdcl.f0.EntailsClause (cnfClause (pref ++ res.1.reverse ++ suff)) ∧
      res.2.RemovableInv (pref ++ res.1.reverse ++ suff) ∧
      (∀ l ∈ res.1.reverse, litNeg l ∈ res.2.cdcl.trail.toList ∧ l ∈ B) ∧
      (∀ w, st.isRemovable w = true → res.2.isRemovable w = true)
  | [] => by
    intro acc st hst hcdcl htp hent' hrem' hacc _
    simp only [List.foldl_nil]
    refine ⟨hst, hcdcl, htp, by simpa using hent', by simpa using hrem', fun l hl => ?_,
      fun _ hw => hw⟩
    exact hacc l (List.mem_reverse.mp hl)
  | x :: xs => by
    intro acc st hst hcdcl htp hent' hrem' hacc hxs
    have hml := minimizeLiteralWorklist_sound hst hent' hrem' true maxDepth x
    cases hres : minimizeLiteralWorklist st true maxDepth x 0 with
    | mk ok st1 =>
      rw [hres] at hml
      obtain ⟨hb1, hcd1, htp1, hr1, hm1, hcut1⟩ := hml
      simp only [List.foldl_cons, hres]
      have hxs' : ∀ l ∈ xs, litNeg l ∈ st1.cdcl.trail.toList ∧ l ∈ B := fun l hl => by
        simpa [hcd1] using hxs l (List.mem_cons_of_mem _ hl)
      cases ok with
      | true =>
        have hcut := hcut1 rfl
        have hsub : ∀ y ∈ (pref ++ acc.reverse ++ (x :: xs) ++ suff).filter (· != x),
            y ∈ pref ++ acc.reverse ++ xs ++ suff := by
          intro y hy
          rw [List.mem_filter] at hy
          rcases List.mem_append.mp hy.1 with hpa | hsuf
          · rcases List.mem_append.mp hpa with hpa0 | hcons
            · exact List.mem_append_left _ (List.mem_append_left _ hpa0)
            · rcases List.mem_cons.mp hcons with rfl | hxs_m
              · simp at hy
              · exact List.mem_append_left _ (List.mem_append_right _ hxs_m)
          · exact List.mem_append_right _ hsuf
        have hsub_ent :
            st1.cdcl.f0.EntailsClause (cnfClause (pref ++ acc.reverse ++ xs ++ suff)) := by
          have hce := hcut.1
          rw [CNF.entails_clause_def] at hce ⊢
          intro α hα
          obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (hce α hα)
          exact (clause_sat_cnfClause_iff α _).mpr ⟨y, hsub y hy, hys⟩
        have hsub_rem : st1.RemovableInv (pref ++ acc.reverse ++ xs ++ suff) :=
          removableInv_mono_clause hsub hcut.2
        have hacc1 : ∀ l ∈ acc, litNeg l ∈ st1.cdcl.trail.toList ∧ l ∈ B := fun l hl => by
          simpa [hcd1] using hacc l hl
        have hih := minimizeLiteralFold_sound maxDepth xs acc st1 hb1 (hcd1.trans hcdcl)
          (htp1.trans htp) hsub_ent hsub_rem hacc1 hxs'
        exact ⟨hih.1, hih.2.1, hih.2.2.1, hih.2.2.2.1, hih.2.2.2.2.1, hih.2.2.2.2.2.1,
          fun w hw => hih.2.2.2.2.2.2 w (hm1 w hw)⟩
      | false =>
        have heq_list : pref ++ (x :: acc).reverse ++ xs ++ suff =
            pref ++ acc.reverse ++ (x :: xs) ++ suff := by
          simp [List.reverse_cons, List.append_assoc]
        have hent1 : st1.cdcl.f0.EntailsClause
            (cnfClause (pref ++ (x :: acc).reverse ++ xs ++ suff)) := by
          rw [heq_list, hcd1]; exact hent'
        have hrem1 : st1.RemovableInv (pref ++ (x :: acc).reverse ++ xs ++ suff) := by
          rw [heq_list]; exact hr1
        have hacc1 : ∀ l ∈ x :: acc, litNeg l ∈ st1.cdcl.trail.toList ∧ l ∈ B := by
          intro l hl; rcases List.mem_cons.mp hl with rfl | ha
          · simpa [hcd1] using hxs l (by simp)
          · simpa [hcd1] using hacc l ha
        have hih := minimizeLiteralFold_sound maxDepth xs (x :: acc) st1 hb1 (hcd1.trans hcdcl)
          (htp1.trans htp) hent1 hrem1 hacc1 hxs'
        exact ⟨hih.1, hih.2.1, hih.2.2.1, hih.2.2.2.1, hih.2.2.2.2.1, hih.2.2.2.2.2.1,
          fun w hw => hih.2.2.2.2.2.2 w (hm1 w hw)⟩

/-- Full iterative clause minimization soundness (`minimize_worklist_sound`). -/
theorem minimize_worklist_sound {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause C))
    (hrem : s.RemovableInv C)
    (hfals : ∀ l ∈ C, litNeg l ∈ s.cdcl.trail.toList)
    (maxDepth : Nat) :
    let (C', s') := minimizeClauseWorklist s maxDepth C
    MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
    s'.cdcl.f0.EntailsClause (cnfClause C') ∧ s'.RemovableInv C' ∧
    (∀ l ∈ C', litNeg l ∈ s'.cdcl.trail.toList) ∧
    (∀ l ∈ C', l ∈ C) ∧
    (∀ w, s.isRemovable w = true → s'.isRemovable w = true) := by
  have hs0_base : MinBaseInv (seedRemovable s C) := h.seedRemovable C
  have hs0_rem : (seedRemovable s C).RemovableInv C := seedRemovable_preserves hrem hfals
  have hs0_ent : (seedRemovable s C).cdcl.f0.EntailsClause (cnfClause C) := by
    simpa [seedRemovable_cdcl] using hent
  have hmain := minimizeLiteralFold_sound (s := s) (pref := []) (suff := []) (B := C) maxDepth
    C [] (seedRemovable s C) hs0_base (seedRemovable_cdcl s C) (seedRemovable_trailPos s C)
    (by simpa using hs0_ent) (by simpa using hs0_rem) (fun _ h => by cases h)
    (fun l hl => ⟨by simpa [seedRemovable_cdcl] using hfals l hl, hl⟩)
  unfold minimizeClauseWorklist
  dsimp only
  cases hres : C.foldl (fun (p : List Nat × MinState) lit =>
      let (ok, st') := minimizeLiteralWorklist p.2 true maxDepth lit 0
      if ok then (p.1, st') else (lit :: p.1, st')) ([], seedRemovable s C) with
  | mk keptRev sEnd =>
    rw [hres] at hmain
    refine ⟨hmain.1.resetPoisoned, ?_, ?_, ?_, ?_, ?_, ?_, fun w hw => ?_⟩
    · simpa [MinState.cdcl_resetPoisoned] using hmain.2.1
    · simpa [MinState.trailPos_resetPoisoned] using hmain.2.2.1
    · simpa [MinState.cdcl_resetPoisoned, List.nil_append, List.append_nil] using hmain.2.2.2.1
    · exact removableInv_resetPoisoned.mpr (by simpa using hmain.2.2.2.2.1)
    · intro l hl; simpa [MinState.cdcl_resetPoisoned] using (hmain.2.2.2.2.2.1 l hl).1
    · intro l hl; exact (hmain.2.2.2.2.2.1 l hl).2
    · rw [MinState.isRemovable_resetPoisoned]
      exact hmain.2.2.2.2.2.2 w ((seedRemovable_isRemovable s C w).mpr (Or.inl hw))

end LeanQbe.T.Examples.Kissat.Ref
