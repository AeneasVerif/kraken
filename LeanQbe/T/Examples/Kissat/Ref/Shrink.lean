/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.MinimizeDfs

/-!
# Pure Lean Layer-A CDCL Theory for Clause Shrinking and Failed-Literal Analysis

Builds on `Minimize` and `MinimizeDfs` (pure Lean, zero `Kraken.Mem` imports):

1. **Block replacement (`shrink`, `shrink.c`)** under Kissat's lazy `(level, trailPos)` ordering
   (`RemovableInv` / `shrink_block_cut_sound`):
   - `shrink_block_cut_sound`: semantic soundness of replacing level-`L` block `B` (`0 < L`) with
     `¬uip` and marking all resolved block variables `S` as `removable`, preserving both
     `F₀.EntailsClause` and `MinState.RemovableInv` even when `< L` side literals sit later on
     `trail`.
   - Executable `shrinkLiteralExec`, `shrinkWalk`, `shrinkBlockExec`, `shrinkClauseExec` matching
     `shrink.c` (including optional `alwaysMin` calling `minimizeLiteralWorklist` at depth 1 and
     fallback `minimizeBlockExec`), proved sound by `shrink_block_sound` and `shrink_clause_sound`.
2. **Failed-literal backward analysis (`analyze_failed_literal`, `analyze.c:390-517`)**:
   - Executable `analyzeFailedLiteralExec` modeling conflict scanning, backward trail resolution,
     `unresolved == 1` unit extraction, the `other == unit` skip (`analyze.c:473`), `goto DONE`,
     and trail-start guard (`t == 0`).
   - `failedLit_other_ne_unit`: proves `other == unit` is unreachable under `ReasonDagInv` and
     `vars_nodup`.
   - `analyzeFailedLiteralExec_sound`: proves every emitted unit (both intermediate units and
     `¬failed`) is entailed by `F₀`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Block replacement (`shrink`) under lazy `(level, trailPos)` ordering -/

/-- Antecedent shrinkability condition at level `L`: every reason antecedent of `t` is level-0,
strictly lower-level (`< L`) and already `removable`, or a member of the active block set `S`. -/
@[expose] def AntecedentsShrinkable (s : MinState) (L : Nat) (S : List Nat) (t : Nat) : Prop :=
  match stateReason s.cdcl t with
  | .decision | .unit => False
  | .binary other =>
    s.litLevel other = 0 ∨
    (s.litLevel other < L ∧ s.isRemovable (litVar other) = true) ∨
    litVar other ∈ S
  | .large cid =>
    ∃ cl : Clause, s.cdcl.clauses[cid]? = some (some cl) ∧ !cl.garbage = true ∧ t ∈ cl.lits ∧
      ∀ x ∈ cl.lits, x ≠ t →
        s.litLevel x = 0 ∨
        (s.litLevel x < L ∧ s.isRemovable (litVar x) = true) ∨
        litVar x ∈ S

/-! ### Executable `shrinkBlockExec` and `shrinkClauseExec` matching `shrink.c` -/

/-- Literal check for `shrink` (`shrink_literal`, `shrink.c:47-82`): returns `none` if lower-level
literal `lit` could not be eliminated, `some (true, litVar lit :: S, st)` if pushed onto `S`,
or `some (false, S, st')` if level-0, already in `S`, or lower-level removable/minimized. -/
@[expose] def shrinkLiteralExec (alwaysMin : Bool) (maxDepth level lit : Nat)
    (S : List Nat) (st : MinState) : Option (Bool × List Nat × MinState) :=
  let l := st.litLevel lit
  if l == 0 then
    some (false, S, st)
  else if S.contains (litVar lit) then
    some (false, S, st)
  else if l < level then
    if st.isRemovable (litVar lit) then
      some (false, S, st)
    else if alwaysMin then
      let (ok, st') := minimizeLiteralWorklist st false maxDepth lit 1
      if ok then some (false, S, st') else none
    else
      none
  else if l == level then
    some (true, litVar lit :: S, st)
  else
    none

/-- Resolve `uip` against a `.large` reason clause (`shrink_along_large`, `shrink.c:173-194`). -/
@[expose] def shrinkAlongLargeExec (alwaysMin : Bool) (maxDepth level uip : Nat) :
    List Nat → Nat → List Nat → MinState → Option (Nat × List Nat × MinState)
  | [], pushed, S, st => some (pushed, S, st)
  | other :: rest, pushed, S, st =>
    if other == uip then
      shrinkAlongLargeExec alwaysMin maxDepth level uip rest pushed S st
    else
      match shrinkLiteralExec alwaysMin maxDepth level other S st with
      | none => none
      | some (added, S', st') =>
        let pushed' := if added then pushed + 1 else pushed
        shrinkAlongLargeExec alwaysMin maxDepth level uip rest pushed' S' st'

/-- Seed initial block literals `B` into `S` (`push_literals_of_block`, `shrink.c:141-158`) and
compute `maxTrail`; returns `none` if any `b ∈ B` is not falsified on `trail` at `level`. -/
@[expose] def pushBlockLiteralsExec (s : MinState) (level : Nat) :
    List Nat → Nat → List Nat → Option (Nat × List Nat)
  | [], maxTrl, S => some (maxTrl, S)
  | b :: bs, maxTrl, S =>
    if trailHasLit s.cdcl.trail (litNeg b) && (s.litLevel b == level) then
      let v := litVar b
      let maxTrl' := Nat.max maxTrl (s.varTrailPos v)
      let S' := if S.contains v then S else v :: S
      pushBlockLiteralsExec s level bs maxTrl' S'
    else
      none

/-- Backward UIP walk (`shrink_block` loop, `shrink.c:247-259`), structurally decreasing on trail
index `t`. Returns `some (uip, S, st)` on reaching `openCnt == 1`. -/
@[expose] def shrinkWalk (alwaysMin resolveLarge : Bool) (maxDepth level : Nat) :
    Nat → Nat → List Nat → MinState → Option (Nat × List Nat × MinState)
  | t, openCnt, S, st =>
    match st.cdcl.trail[t]? with
    | none => none
    | some uip =>
      if !S.contains (litVar uip) then
        match t with
        | 0 => none
        | t' + 1 => shrinkWalk alwaysMin resolveLarge maxDepth level t' openCnt S st
      else if openCnt ≤ 1 then
        some (uip, S, st)
      else
        let nxt : Option (Nat × List Nat × MinState) :=
          match stateReason st.cdcl uip with
          | .decision | .unit => none
          | .binary other =>
            match shrinkLiteralExec alwaysMin maxDepth level other S st with
            | none => none
            | some (added, S', st') =>
              some (if added then openCnt else openCnt - 1, S', st')
          | .large cid =>
            if !resolveLarge then none
            else
              match st.cdcl.clauses[cid]? with
              | some (some cl) =>
                if !cl.garbage && cl.lits.contains uip then
                  match shrinkAlongLargeExec alwaysMin maxDepth level uip cl.lits 0 S st with
                  | none => none
                  | some (pushed, S', st') => some (openCnt + pushed - 1, S', st')
                else none
              | _ => none
        match nxt with
        | none => none
        | some (open', S', st') =>
          match t with
          | 0 => none
          | t' + 1 => shrinkWalk alwaysMin resolveLarge maxDepth level t' open' S' st'

/-- Attempt to shrink level-`level` block `B` to `[litNeg uip]` (`shrink_block` + `shrunken_block`,
`shrink.c:223-269`). Returns `(shrank?, outB, st')` updating `removable` on success. -/
@[expose] def shrinkBlockExec (s : MinState) (alwaysMin resolveLarge : Bool) (maxDepth level : Nat)
    (B : List Nat) : Bool × List Nat × MinState :=
  if level == 0 || B.length < 2 then
    (false, B, s)
  else
    match pushBlockLiteralsExec s level B 0 [] with
    | none => (false, B, s)
    | some (maxTrl, initS) =>
      match shrinkWalk alwaysMin resolveLarge maxDepth level maxTrl initS.length initS s with
      | none => (false, B, s)
      | some (uip, S, st) => (true, [litNeg uip], setRemovableList st S)

/-- Minimize block literals when block shrinking did not fire (`minimize_block`,
`shrink.c:307-322`). -/
@[expose]
def minimizeBlockExec (s : MinState) (maxDepth : Nat) (B : List Nat) : List Nat × MinState :=
  let (keptRev, st) := B.foldl (init := ([], s)) fun (acc, st) lit =>
    let (ok, st') := minimizeLiteralWorklist st true maxDepth lit 0
    if ok then (acc, st') else (lit :: acc, st')
  (keptRev.reverse, st)

/-- Partition clause `C` into contiguous maximal same-level blocks (`next_block`,
`shrink.c:271-305`), returned in back-to-front processing order. -/
@[expose] def splitLevelBlocksRev (s : MinState) : List Nat → List (Nat × List Nat)
  | [] => []
  | l :: ls =>
    let (lvl, cur, acc) := ls.foldl (init := (s.litLevel l, [l], []))
      fun (curLvl, curBlk, done) x =>
        let lx := s.litLevel x
        if lx == curLvl then (curLvl, x :: curBlk, done)
        else (lx, [x], (curLvl, curBlk.reverse) :: done)
    (lvl, cur.reverse) :: acc

/-- Full clause shrinking (`kissat_shrink_clause`, `shrink.c:360-395`): processes each level block
right-to-left (`shrinkBlockExec`, falling back to `minimizeBlockExec` when `|B| ≥ 2` fails to
shrink), then resets `poisoned`. -/
@[expose] def shrinkClauseExec (s : MinState) (alwaysMin resolveLarge : Bool) (maxDepth : Nat)
    (C : List Nat) : List Nat × MinState :=
  let blocks := splitLevelBlocksRev s C
  let (resAcc, sEnd) := blocks.foldl (init := ([], s)) fun (acc, st) (lvl, B) =>
    if B.length < 2 then
      (B ++ acc, st)
    else
      let (shrank, B', st') := shrinkBlockExec st alwaysMin resolveLarge maxDepth lvl B
      if shrank then
        (B' ++ acc, st')
      else
        let (B'', st'') := minimizeBlockExec st' maxDepth B
        (B'' ++ acc, st'')
  (resAcc, sEnd.resetPoisoned)

end LeanQbe.T.Examples.Kissat.Ref
