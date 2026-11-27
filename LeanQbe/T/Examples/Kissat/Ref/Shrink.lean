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

private theorem AntecedentsShrinkable.mono {s s1 : MinState} {L : Nat} {S S1 : List Nat}
    {t : Nat} (ha : AntecedentsShrinkable s L S t) (hcdcl : s1.cdcl = s.cdcl)
    (hrem : ∀ w, s.isRemovable w = true → s1.isRemovable w = true)
    (hS : ∀ v ∈ S, v ∈ S1) :
    AntecedentsShrinkable s1 L S1 t := by
  unfold AntecedentsShrinkable at ha ⊢
  have hsr : stateReason s1.cdcl t = stateReason s.cdcl t :=
    congrArg (fun c => stateReason c t) hcdcl
  rw [hsr]
  cases hrsn : stateReason s.cdcl t with
  | decision | unit => rw [hrsn] at ha; exact ha
  | binary other =>
    rw [hrsn] at ha
    rcases ha with h0 | ⟨hlt, hr⟩ | hm
    · exact Or.inl (by simpa [MinState.litLevel, MinState.varLevel, hcdcl] using h0)
    · exact Or.inr (Or.inl ⟨by simpa [MinState.litLevel, MinState.varLevel, hcdcl] using hlt,
        hrem _ hr⟩)
    · exact Or.inr (Or.inr (hS _ hm))
  | large cid =>
    rw [hrsn] at ha
    obtain ⟨cl, hget, hng, hmem, hall⟩ := ha
    refine ⟨cl, by simpa [hcdcl] using hget, hng, hmem, fun x hx hne => ?_⟩
    rcases hall x hx hne with h0 | ⟨hlt, hr⟩ | hm
    · exact Or.inl (by simpa [MinState.litLevel, MinState.varLevel, hcdcl] using h0)
    · exact Or.inr (Or.inl ⟨by simpa [MinState.litLevel, MinState.varLevel, hcdcl] using hlt,
        hrem _ hr⟩)
    · exact Or.inr (Or.inr (hS _ hm))

private theorem antecedentShrinkable_falsified {s : MinState} (h : MinBaseInv s)
    {C B : List Nat} (hrem : s.RemovableInv C) {L v x : Nat}
    (hB_lvl : ∀ b ∈ B, s.litLevel b = L)
    (hx_trl : ∃ (j : Nat) (_hj : j < s.cdcl.trail.size), s.cdcl.trail[j] = litNeg x)
    (hlt : varLt s (litVar x) v)
    (hok : s.litLevel x = 0 ∨ (s.litLevel x < L ∧ s.isRemovable (litVar x) = true))
    {α : Nat → Bool} (hα : s.cdcl.f0.Sat α)
    (hsub : ∀ l ∈ C, l ∉ B → varLe s (litVar l) v → ¬ (cnfClause [l]).Sat α) :
    ¬ (cnfClause [x]).Sat α :=
  antecedent_falsified h hrem hx_trl (hok.elim Or.inl (fun hp => Or.inr hp.2)) hα
    (fun hpos l hl hle => hsub l hl (fun hlB => by
      rcases hok with h0 | ⟨hltL, _⟩
      · simp [MinState.litLevel] at h0; omega
      · have hbl : s.varLevel (litVar l) = L := by simpa [MinState.litLevel] using hB_lvl l hlB
        have hxl : s.varLevel (litVar x) < L := by simpa [MinState.litLevel] using hltL
        rcases hle with hlt1 | ⟨heq1, _⟩ <;> omega) (varLe_trans hle hlt.to_varLe))

/-- Key inductive helper for `shrink_block_cut_sound`: every resolved variable `v ∈ S` has its
true trail literal entailed under `F₀` plus falsification of
`{litNeg uip} ∪ {l ∈ C \ B | var l ⪯ v}`. -/
private theorem shrink_S_entailed {s : MinState} (h : MinBaseInv s) {C B : List Nat}
    (hrem : s.RemovableInv C) {L uip : Nat} (_hL : 0 < L)
    (huip_trl : uip ∈ s.cdcl.trail.toList)
    {S : List Nat}
    (hB_lvl : ∀ b ∈ B, s.litLevel b = L)
    (hS : ∀ v ∈ S, s.varLevel v = L ∧ varLe s (litVar uip) v ∧
      (v ≠ litVar uip → ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
        litVar s.cdcl.trail[i] = v ∧ AntecedentsShrinkable s L S s.cdcl.trail[i]))
    {α : Nat → Bool} (hα : s.cdcl.f0.Sat α)
    (hnu : ¬ (cnfClause [litNeg uip]).Sat α) :
    ∀ (m v : Nat), varLexMeasure s v = m → v ∈ S →
      (∀ l ∈ C, l ∉ B → varLe s (litVar l) v → ¬ (cnfClause [l]).Sat α) →
      ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
        litVar s.cdcl.trail[i] = v ∧ (cnfClause [s.cdcl.trail[i]]).Sat α := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro v hm hvS hsub
    by_cases hvu : v = litVar uip
    · obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp huip_trl
      refine ⟨j, hj, by rw [hjeq, hvu], ?_⟩
      rw [hjeq]
      exact Classical.byContradiction fun hns =>
        hnu ((sat_cnfClause_litNeg_iff α uip).mpr hns)
    · obtain ⟨_, _, htr_ex⟩ := hS v hvS
      obtain ⟨i, hi, hveq, hant⟩ := htr_ex hvu
      refine ⟨i, hi, hveq, ?_⟩
      have hrd := reason_antecedent_varLt h hi
      unfold AntecedentsShrinkable at hant
      generalize hrsn : stateReason s.cdcl s.cdcl.trail[i] = rsn
      rw [hrsn] at hrd hant
      have hne_ant : ∀ x,
          (∃ (j : Nat) (_hj : j < s.cdcl.trail.size), s.cdcl.trail[j] = litNeg x) →
          varLt s (litVar x) v →
          (s.litLevel x = 0 ∨ (s.litLevel x < L ∧ s.isRemovable (litVar x) = true) ∨
            litVar x ∈ S) →
          ¬ (cnfClause [x]).Sat α := by
        intro x hx_trl hlt hkind
        rcases hkind with hl0 | ⟨hltL, hr⟩ | hxS
        · exact antecedentShrinkable_falsified h hrem hB_lvl hx_trl hlt (Or.inl hl0) hα hsub
        · exact antecedentShrinkable_falsified h hrem hB_lvl hx_trl hlt
            (Or.inr ⟨hltL, hr⟩) hα hsub
        · obtain ⟨j, hj, hjeq⟩ := hx_trl
          have hm_lt : varLexMeasure s (litVar x) < m := by
            rw [← hm]
            exact varLexMeasure_lt h ⟨j, hj, by rw [hjeq, litVar_litNeg]⟩ hlt
          obtain ⟨j', hj', hj'var, hj'sat⟩ := ih _ hm_lt (litVar x) rfl hxS fun l hlC hnb hle =>
            hsub l hlC hnb (varLe_trans hle hlt.to_varLe)
          have hj_eq : j' = j :=
            h.trail_inv.vars_nodup j' j hj' hj (by rw [hj'var, hjeq, litVar_litNeg])
          subst hj_eq
          rw [hjeq] at hj'sat
          exact (sat_cnfClause_litNeg_iff α x).mp hj'sat
      cases rsn with
      | decision | unit => exact False.elim hant
      | binary other =>
        obtain ⟨hbin, j, hj, _, hjeq, _, hlt⟩ := hrd
        rw [hveq] at hlt
        have hnf := hne_ant other ⟨j, hj, hjeq⟩ hlt hant
        obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp hbin α hα)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact (sat_cnfClause_singleton α _).mpr hys
        · exact absurd ((sat_cnfClause_singleton α _).mpr hys) hnf
      | large cid =>
        obtain ⟨c, hget, _, _, hall⟩ := hrd
        obtain ⟨cl, hget_cl, _, _, hall_ant⟩ := hant
        rw [hget] at hget_cl; cases hget_cl
        obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α c.lits).mp
          (CNF.entails_clause_def.mp (h.trail_inv.db_sound cid c hget) α hα)
        by_cases hxeq : x = s.cdcl.trail[i]
        · rw [hxeq] at hxs; exact (sat_cnfClause_singleton α _).mpr hxs
        · obtain ⟨j, hj, _, hjeq, _, hlt⟩ := hall x hx hxeq
          rw [hveq] at hlt
          have hnf := hne_ant x ⟨j, hj, hjeq⟩ hlt (hall_ant x hx hxeq)
          exact absurd ((sat_cnfClause_singleton α _).mpr hxs) hnf

/-- **Section 1(f) `shrink` block replacement theorem** under lazy `(level, trailPos)` ordering:
replacing level-`L` block `B ⊆ C` with `litNeg uip` and marking all resolved variables `S` as
`removable` preserves `MinBaseInv`, `F₀.EntailsClause`, and `RemovableInv`. -/
theorem shrink_block_cut_sound {s : MinState} (h : MinBaseInv s) {C B : List Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause C))
    (hrem : s.RemovableInv C) {L : Nat} (hL : 0 < L)
    {uip : Nat} (huip_trl : uip ∈ s.cdcl.trail.toList)
    (_huip_lvl : stateLevel s.cdcl uip = L)
    {S : List Nat}
    (hB : ∀ b ∈ B, litNeg b ∈ s.cdcl.trail.toList ∧ s.litLevel b = L ∧ litVar b ∈ S)
    (hS : ∀ v ∈ S, s.varLevel v = L ∧ varLe s (litVar uip) v ∧
      (v ≠ litVar uip → ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
        litVar s.cdcl.trail[i] = v ∧ AntecedentsShrinkable s L S s.cdcl.trail[i])) :
    let C' := litNeg uip :: C.filter (fun l => !B.contains l)
    let s' := setRemovableList s S
    MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
    s'.cdcl.f0.EntailsClause (cnfClause C') ∧ s'.RemovableInv C' ∧
    (∀ w, s.isRemovable w = true → s'.isRemovable w = true) := by
  have hB_lvl : ∀ b ∈ B, s.litLevel b = L := fun b hb => (hB b hb).2.1
  have hcut_b : ∀ {α : Nat → Bool}, s.cdcl.f0.Sat α →
      ¬ (cnfClause [litNeg uip]).Sat α →
      ∀ {b w : Nat}, b ∈ B →
        (∀ l ∈ C, l ∉ B → varLe s (litVar l) w → ¬ (cnfClause [l]).Sat α) →
        varLe s (litVar b) w → ¬ (cnfClause [b]).Sat α := by
    intro α hα hnu b w hbB hsub hbw
    have hb_trl : litNeg b ∈ s.cdcl.trail.toList := (hB b hbB).1
    have hbS : litVar b ∈ S := (hB b hbB).2.2
    obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hb_trl
    obtain ⟨j, hj, hjvar, hjsat⟩ := shrink_S_entailed h hrem hL huip_trl hB_lvl hS hα hnu
      (varLexMeasure s (litVar b)) (litVar b) rfl hbS
      fun l hlC hnb hlb => hsub l hlC hnb (varLe_trans hlb hbw)
    have hij : j = i := h.trail_inv.vars_nodup j i hj hi (by rw [hjvar, hieq, litVar_litNeg])
    subst hij; rw [hieq] at hjsat
    exact (sat_cnfClause_litNeg_iff α b).mp hjsat
  refine ⟨h.setRemovableList S, setRemovableList_cdcl s S, setRemovableList_trailPos s S, ?_, ?_,
    fun w hw => (setRemovableList_isRemovable s S w).mpr (Or.inl hw)⟩
  · rw [setRemovableList_cdcl, CNF.entails_clause_def]
    intro α hα
    exact Classical.byContradiction fun hnot => by
      have hC' : ∀ l ∈ litNeg uip :: C.filter (fun x => !B.contains x),
          ¬ (cnfClause [l]).Sat α := fun l hl hs =>
        hnot ((clause_sat_cnfClause_iff α _).mpr ⟨l, hl, (sat_cnfClause_singleton α l).mp hs⟩)
      have hnu : ¬ (cnfClause [litNeg uip]).Sat α := hC' _ (by simp)
      obtain ⟨l, hlC, hlsat⟩ :=
        (clause_sat_cnfClause_iff α C).mp (CNF.entails_clause_def.mp hent α hα)
      have hls : (cnfClause [l]).Sat α := (sat_cnfClause_singleton α l).mpr hlsat
      by_cases hlB : l ∈ B
      · exact hcut_b hα hnu hlB (fun x hx hxnb _ =>
          hC' x (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hx, by simp [hxnb]⟩)))
          (varLe_refl s (litVar l)) hls
      · exact hC' l (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hlC, by simp [hlB]⟩)) hls
  · intro w hw hl0
    rw [setRemovableList_isRemovable] at hw
    have hl0' : 0 < s.varLevel w := by
      simpa [MinState.varLevel, setRemovableList_cdcl] using hl0
    have htr_eq : ∀ i (hi1 : i < (setRemovableList s S).cdcl.trail.size)
        (hi2 : i < s.cdcl.trail.size),
        (setRemovableList s S).cdcl.trail[i] = s.cdcl.trail[i] := by
      intro i hi1 hi2
      have hc : (setRemovableList s S).cdcl = s.cdcl := setRemovableList_cdcl s S
      exact trail_getElem_of_eq hc hi1 hi2
    rcases hw with hws | hwS
    · obtain ⟨i, hi, hveq, himp⟩ := hrem w hws hl0'
      have hi' : i < (setRemovableList s S).cdcl.trail.size := by
        simpa [setRemovableList_cdcl] using hi
      refine ⟨i, hi', by rw [htr_eq i hi' hi, hveq], fun α hα hC' => ?_⟩
      rw [htr_eq i hi' hi]
      apply himp α (by simpa [setRemovableList_cdcl] using hα)
      intro l hlC hle
      have hle' : varLe s (litVar l) w := by
        simpa [varLe, MinState.varLevel, MinState.varTrailPos, setRemovableList_cdcl,
          setRemovableList_trailPos] using hle
      have hC'_s : ∀ x ∈ litNeg uip :: C.filter (fun y => !B.contains y),
          varLe s (litVar x) w → ¬ (cnfClause [x]).Sat α := fun x hx hxw =>
        hC' x hx (by simpa [varLe, MinState.varLevel, MinState.varTrailPos,
          setRemovableList_cdcl, setRemovableList_trailPos] using hxw)
      by_cases hlB : l ∈ B
      · have huip_le_l : varLe s (litVar uip) (litVar l) := (hS (litVar l) (hB l hlB).2.2).2.1
        have hnu : ¬ (cnfClause [litNeg uip]).Sat α :=
          hC'_s (litNeg uip) (by simp)
            (by simpa [litVar_litNeg] using varLe_trans huip_le_l hle')
        exact hcut_b (by simpa [setRemovableList_cdcl] using hα) hnu hlB
          (fun x hx hxnb hxw => hC'_s x
            (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hx, by simp [hxnb]⟩)) hxw)
          hle'
      · exact hC'_s l (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hlC, by simp [hlB]⟩)) hle'
    · have huip_le_w : varLe s (litVar uip) w := (hS w hwS).2.1
      by_cases hwu : w = litVar uip
      · obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp huip_trl
        have hi' : i < (setRemovableList s S).cdcl.trail.size := by
          simpa [setRemovableList_cdcl] using hi
        refine ⟨i, hi', by rw [htr_eq i hi' hi, hieq, hwu], fun α _ hC' => ?_⟩
        rw [htr_eq i hi' hi, hieq]
        have hnu : ¬ (cnfClause [litNeg uip]).Sat α :=
          hC' (litNeg uip) (by simp) (by
            simp [varLe, MinState.varLevel, MinState.varTrailPos, setRemovableList_cdcl,
              setRemovableList_trailPos, litVar_litNeg, hwu])
        exact Classical.byContradiction fun hnsat =>
          hnu ((sat_cnfClause_litNeg_iff α uip).mpr hnsat)
      · have hα_help : ∀ α : Nat → Bool, (setRemovableList s S).cdcl.f0.Sat α →
            (∀ l ∈ litNeg uip :: C.filter (fun y => !B.contains y),
              varLe (setRemovableList s S) (litVar l) w → ¬ (cnfClause [l]).Sat α) →
            ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
              litVar s.cdcl.trail[i] = w ∧ (cnfClause [s.cdcl.trail[i]]).Sat α := by
          intro α hα hC'
          have hC'_s : ∀ x ∈ litNeg uip :: C.filter (fun y => !B.contains y),
              varLe s (litVar x) w → ¬ (cnfClause [x]).Sat α := fun x hx hxw =>
            hC' x hx (by simpa [varLe, MinState.varLevel, MinState.varTrailPos,
              setRemovableList_cdcl, setRemovableList_trailPos] using hxw)
          have hnu : ¬ (cnfClause [litNeg uip]).Sat α :=
            hC'_s (litNeg uip) (by simp) (by simpa [litVar_litNeg] using huip_le_w)
          exact shrink_S_entailed h hrem hL huip_trl hB_lvl hS
            (by simpa [setRemovableList_cdcl] using hα) hnu
            (varLexMeasure s w) w rfl hwS fun x hx hxnb hxw =>
            hC'_s x (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hx, by simp [hxnb]⟩)) hxw
        obtain ⟨i, hi, hveq, _⟩ := (hS w hwS).2.2 hwu
        have hi' : i < (setRemovableList s S).cdcl.trail.size := by
          simpa [setRemovableList_cdcl] using hi
        refine ⟨i, hi', by rw [htr_eq i hi' hi, hveq], fun α hα hC' => ?_⟩
        obtain ⟨j, hj, hjvar, hjsat⟩ := hα_help α hα hC'
        have hij : j = i := h.trail_inv.vars_nodup j i hj hi (by rw [hjvar, hveq])
        subst hij
        rw [htr_eq j hi' hi]; exact hjsat

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

/-! ### Proofs for `shrinkLiteralExec`, `shrinkWalk`, `shrinkBlockExec`, `shrinkClauseExec` -/

private theorem shrinkLiteralExec_sound {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hrem : s.RemovableInv C) {alwaysMin : Bool} {maxDepth level t lit : Nat}
    {S : List Nat} (hnodup : S.Nodup)
    (_hlit_trl : litNeg lit ∈ s.cdcl.trail.toList)
    (hlt_pos : s.litLevel lit = level → s.varTrailPos (litVar lit) ≤ t) :
    match shrinkLiteralExec alwaysMin maxDepth level lit S s with
    | none => True
    | some (added, S', st') =>
      MinBaseInv st' ∧ st'.cdcl = s.cdcl ∧ st'.trailPos = s.trailPos ∧ st'.RemovableInv C ∧
      (∀ w, s.isRemovable w = true → st'.isRemovable w = true) ∧
      S'.Nodup ∧ (∀ v ∈ S, v ∈ S') ∧
      (st'.litLevel lit = 0 ∨ (st'.litLevel lit < level ∧ st'.isRemovable (litVar lit) = true) ∨
        litVar lit ∈ S') ∧
      (added = true →
        st'.varLevel (litVar lit) = level ∧ litVar lit ∉ S ∧ S' = litVar lit :: S ∧
        st'.varTrailPos (litVar lit) ≤ t) ∧
      (added = false → S' = S) ∧
      ((S'.filter (fun v => decide (st'.varTrailPos v ≤ t))).length =
        (if added then 1 else 0) + (S.filter (fun v => decide (s.varTrailPos v ≤ t))).length) := by
  unfold shrinkLiteralExec
  by_cases hl0 : s.litLevel lit = 0
  · have hl0b : (s.litLevel lit == 0) = true := beq_iff_eq.mpr hl0
    rw [ite_eq_left hl0b]; dsimp only
    exact ⟨h, rfl, rfl, hrem, fun _ hw => hw, hnodup, fun _ hv => hv, Or.inl hl0,
      (fun hf => by cases hf), fun _ => rfl, by simp⟩
  · have hl0b : (s.litLevel lit == 0) = false := beq_false_of_ne hl0
    rw [ite_eq_right (by simp [hl0b])]; dsimp only
    by_cases hcont : S.contains (litVar lit) = true
    · rw [ite_eq_left hcont]; dsimp only
      have hmem : litVar lit ∈ S := List.contains_iff_mem.mp hcont
      exact ⟨h, rfl, rfl, hrem, fun _ hw => hw, hnodup, fun _ hv => hv, Or.inr (Or.inr hmem),
        (fun hf => by cases hf), fun _ => rfl, by simp⟩
    · have hnot_mem : litVar lit ∉ S := by
        intro hm; exact hcont (List.contains_iff_mem.mpr hm)
      rw [ite_eq_right hcont]
      by_cases hlt : s.litLevel lit < level
      · rw [ite_eq_left hlt]
        by_cases hr : s.isRemovable (litVar lit) = true
        · rw [ite_eq_left hr]; dsimp only
          exact ⟨h, rfl, rfl, hrem, fun _ hw => hw, hnodup, fun _ hv => hv,
            Or.inr (Or.inl ⟨hlt, hr⟩), (fun hf => by cases hf), fun _ => rfl, by simp⟩
        · rw [ite_eq_right hr]
          by_cases ham : alwaysMin = true
          · rw [ite_eq_left ham]
            have hm := minimizeLiteralWorklist_sub_sound h hrem false maxDepth lit
            cases hres : minimizeLiteralWorklist s false maxDepth lit 1 with
            | mk ok st' =>
              rw [hres] at hm
              cases ok with
              | false => rw [ite_eq_right (by simp)]; trivial
              | true =>
                rw [ite_eq_left rfl]; dsimp only
                obtain ⟨hb', hcd', htp', hrem', hmono', hok⟩ := hm
                obtain ⟨_, hkind⟩ := hok rfl
                refine ⟨hb', hcd', htp', hrem', hmono', hnodup, fun _ hv => hv, ?_,
                  (fun hf => by cases hf), fun _ => rfl, ?_⟩
                · rcases hkind with h0 | hr'
                  · exact Or.inl h0
                  · exact Or.inr (Or.inl ⟨by simpa [MinState.litLevel, MinState.varLevel,
                      hcd'] using hlt, hr'⟩)
                · simp [MinState.varTrailPos, htp']
          · rw [ite_eq_right ham]; trivial
      · rw [ite_eq_right hlt]
        by_cases heq : s.litLevel lit = level
        · have heqb : (s.litLevel lit == level) = true := beq_iff_eq.mpr heq
          rw [ite_eq_left heqb]; dsimp only
          have hpos : s.varTrailPos (litVar lit) ≤ t := hlt_pos heq
          have hp_true : decide (s.varTrailPos (litVar lit) ≤ t) = true := decide_eq_true hpos
          refine ⟨h, rfl, rfl, hrem, fun _ hw => hw, List.nodup_cons.mpr ⟨hnot_mem, hnodup⟩,
            fun _ hv => List.mem_cons_of_mem _ hv, Or.inr (Or.inr (by simp)),
            fun _ => ⟨by simpa [MinState.litLevel] using heq, hnot_mem, rfl, hpos⟩,
            (fun hf => by cases hf), ?_⟩
          simp [hp_true, Nat.add_comm]
        · have heqb : (s.litLevel lit == level) = false := beq_false_of_ne heq
          rw [ite_eq_right (by simp [heqb])]; trivial

private theorem shrinkAlongLargeExec_props {C : List Nat} {alwaysMin : Bool}
    {maxDepth level uip t : Nat} (lits : List Nat) :
    ∀ (pushed : Nat) (S : List Nat) (st : MinState),
      MinBaseInv st → st.RemovableInv C → S.Nodup →
      (∀ v ∈ S, st.varLevel v = level ∧
        ∃ (i : Nat) (_hi : i < st.cdcl.trail.size), litVar st.cdcl.trail[i] = v) →
      (∀ x ∈ lits, x ≠ uip → litNeg x ∈ st.cdcl.trail.toList) →
      (∀ x ∈ lits, x ≠ uip → st.litLevel x = level → st.varTrailPos (litVar x) ≤ t) →
      match shrinkAlongLargeExec alwaysMin maxDepth level uip lits pushed S st with
      | none => True
      | some (pushed', S', st') =>
        MinBaseInv st' ∧ st'.cdcl = st.cdcl ∧ st'.trailPos = st.trailPos ∧ st'.RemovableInv C ∧
        (∀ w, st.isRemovable w = true → st'.isRemovable w = true) ∧
        S'.Nodup ∧ (∀ v ∈ S, v ∈ S') ∧
        (∀ v ∈ S', st'.varLevel v = level ∧
          ∃ (i : Nat) (_hi : i < st'.cdcl.trail.size), litVar st'.cdcl.trail[i] = v) ∧
        (∀ x ∈ lits, x ≠ uip →
          st'.litLevel x = 0 ∨
          (st'.litLevel x < level ∧ st'.isRemovable (litVar x) = true) ∨
          litVar x ∈ S') ∧
        (∀ v ∈ S', v ∉ S → st'.varTrailPos v ≤ t) ∧
        (S'.filter (fun v => decide (st'.varTrailPos v ≤ t))).length + pushed =
          pushed' + (S.filter (fun v => decide (st.varTrailPos v ≤ t))).length := by
  induction lits with
  | nil =>
    intro pushed S st hst hrm hnd hS _ _
    unfold shrinkAlongLargeExec; dsimp only
    exact ⟨hst, rfl, rfl, hrm, fun _ hw => hw, hnd, fun _ hv => hv, hS,
      (fun _ hm => by cases hm), (fun _ hv hnv => absurd hv hnv), Nat.add_comm _ pushed⟩
  | cons x xs ih =>
    intro pushed S st hst hrm hnd hS hl1 hl2
    unfold shrinkAlongLargeExec
    by_cases hxu : x = uip
    · have hxub : (x == uip) = true := beq_iff_eq.mpr hxu
      rw [ite_eq_left hxub]
      have hih := ih pushed S st hst hrm hnd hS
        (fun y hy => hl1 y (List.mem_cons_of_mem _ hy))
        (fun y hy => hl2 y (List.mem_cons_of_mem _ hy))
      cases hres : shrinkAlongLargeExec alwaysMin maxDepth level uip xs pushed S st with
      | none => rw [hres] at hih; trivial
      | some res =>
        rw [hres] at hih
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hih
        refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun y hy hyne => ?_, a10, a11⟩
        rcases List.mem_cons.mp hy with rfl | hyxs
        · exact absurd hxu hyne
        · exact a9 y hyxs hyne
    · have hxub : (x == uip) = false := beq_false_of_ne hxu
      rw [ite_eq_right (by simp [hxub])]; dsimp only
      have hx_trl : litNeg x ∈ st.cdcl.trail.toList := hl1 x (by simp) hxu
      have hx_pos : st.litLevel x = level → st.varTrailPos (litVar x) ≤ t :=
        hl2 x (by simp) hxu
      have hsl := shrinkLiteralExec_sound hst hrm (alwaysMin := alwaysMin) (maxDepth := maxDepth)
        (level := level) (t := t) (lit := x) hnd hx_trl hx_pos
      cases hsl_res : shrinkLiteralExec alwaysMin maxDepth level x S st with
      | none => trivial
      | some res1 =>
        rw [hsl_res] at hsl; dsimp only
        obtain ⟨added, S1, st1⟩ := res1
        obtain ⟨hb1, hcd1, htp1, hr1, hm1, hnd1, hsub1, hx_kind, hadd_t, hadd_f, hflen⟩ := hsl
        have hS1 : ∀ v ∈ S1, st1.varLevel v = level ∧
            ∃ (i : Nat) (_hi : i < st1.cdcl.trail.size), litVar st1.cdcl.trail[i] = v := by
          intro v hv1
          cases added
          · rw [hadd_f rfl] at hv1
            obtain ⟨hlvlv, i, hi, hieq⟩ := hS v hv1
            have hi1 : i < st1.cdcl.trail.size := by simpa [hcd1] using hi
            refine ⟨by simpa [MinState.varLevel, hcd1] using hlvlv, i, hi1, ?_⟩
            rw [trail_getElem_of_eq hcd1 hi1 hi, hieq]
          · obtain ⟨hlvlx, _, hS1eq, _⟩ := hadd_t rfl
            rw [hS1eq] at hv1
            rcases List.mem_cons.mp hv1 with rfl | hvS
            · obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hx_trl
              have hi1 : i < st1.cdcl.trail.size := by simpa [hcd1] using hi
              exact ⟨hlvlx, i, hi1, by rw [trail_getElem_of_eq hcd1 hi1 hi, hieq, litVar_litNeg]⟩
            · obtain ⟨hlvlv, i, hi, hieq⟩ := hS v hvS
              have hi1 : i < st1.cdcl.trail.size := by simpa [hcd1] using hi
              refine ⟨by simpa [MinState.varLevel, hcd1] using hlvlv, i, hi1, ?_⟩
              rw [trail_getElem_of_eq hcd1 hi1 hi, hieq]
        let pushed1 := if added then pushed + 1 else pushed
        have hih := ih pushed1 S1 st1 hb1 hr1 hnd1 hS1
          (fun y hy hyne => by rw [hcd1]; exact hl1 y (List.mem_cons_of_mem _ hy) hyne)
          (fun y hy hyne hly => by
            rw [MinState.varTrailPos, htp1]
            exact hl2 y (List.mem_cons_of_mem _ hy) hyne
              (by simpa [MinState.litLevel, MinState.varLevel, hcd1] using hly))
        cases hres : shrinkAlongLargeExec alwaysMin maxDepth level uip xs pushed1 S1 st1 with
        | none => rw [hres] at hih; trivial
        | some res2 =>
          rw [hres] at hih; dsimp only
          obtain ⟨pushed', S', st'⟩ := res2
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hih
          refine ⟨a1, a2.trans hcd1, a3.trans htp1, a4, fun w hw => a5 w (hm1 w hw), a6,
            fun v hv => a7 v (hsub1 v hv), a8, fun y hy hyne => ?_, fun v hv hnv => ?_, ?_⟩
          · rcases List.mem_cons.mp hy with rfl | hyxs
            · rcases hx_kind with h0 | ⟨hlt, hr⟩ | hmS1
              · exact Or.inl (by simpa [MinState.litLevel, MinState.varLevel, a2] using h0)
              · exact Or.inr (Or.inl ⟨by simpa [MinState.litLevel, MinState.varLevel, a2] using hlt,
                  a5 _ hr⟩)
              · exact Or.inr (Or.inr (a7 _ hmS1))
            · exact a9 y hyxs hyne
          · by_cases hv1 : v ∈ S1
            · cases added
              · exact absurd (hadd_f rfl ▸ hv1) hnv
              · obtain ⟨_, _, hS1eq, hpos_x⟩ := hadd_t rfl
                rw [hS1eq] at hv1
                rcases List.mem_cons.mp hv1 with rfl | hvS
                · simpa [MinState.varTrailPos, a3] using hpos_x
                · exact absurd hvS hnv
            · exact a10 v hv hv1
          · have hst1_tp : (S1.filter (fun v => decide (st1.varTrailPos v ≤ t))).length =
                (S1.filter (fun v => decide (st'.varTrailPos v ≤ t))).length := by
              congr 1; apply List.filter_congr; intro v _
              simp [MinState.varTrailPos, a3]
            cases added <;> simp only [pushed1, Bool.false_eq_true, ↓reduceIte] at a11 hflen ⊢ <;>
              omega

private theorem pushBlockLiteralsExec_props {s : MinState} (h : MinBaseInv s) (level : Nat) :
    ∀ bs maxTrl S,
      S.Nodup →
      (∀ v ∈ S, s.varLevel v = level ∧
        ∃ (i : Nat) (_hi : i < s.cdcl.trail.size), litVar s.cdcl.trail[i] = v ∧ i ≤ maxTrl) →
      match pushBlockLiteralsExec s level bs maxTrl S with
      | none => True
      | some (maxTrl', S') =>
        S'.Nodup ∧ (∀ v ∈ S, v ∈ S') ∧ (∀ b ∈ bs, litNeg b ∈ s.cdcl.trail.toList ∧
          s.litLevel b = level ∧ litVar b ∈ S') ∧
        (∀ v ∈ S', s.varLevel v = level ∧
          ∃ (i : Nat) (_hi : i < s.cdcl.trail.size), litVar s.cdcl.trail[i] = v ∧ i ≤ maxTrl') := by
  intro bs
  induction bs with
  | nil =>
    intro maxTrl S hnd hS
    simp only [pushBlockLiteralsExec]
    exact ⟨hnd, fun _ hv => hv, (fun _ hb => by cases hb), hS⟩
  | cons b bs ih =>
    intro maxTrl S hnd hS
    unfold pushBlockLiteralsExec
    by_cases hok : (trailHasLit s.cdcl.trail (litNeg b) && (s.litLevel b == level)) = true
    · rw [ite_eq_left hok]; dsimp only
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      have hb_trl : litNeg b ∈ s.cdcl.trail.toList := trailHasLit_iff.mp hok.1
      obtain ⟨ib, hib, hib_eq⟩ := trail_mem_iff_exists.mp hb_trl
      have hib_pos : s.varTrailPos (litVar b) = ib := by
        unfold MinState.varTrailPos
        rw [← litVar_litNeg b, ← hib_eq]
        exact h.pos_inv ib hib
      let maxTrl' := Nat.max maxTrl (s.varTrailPos (litVar b))
      let S1 := if S.contains (litVar b) then S else litVar b :: S
      have hnd1 : S1.Nodup := by
        by_cases hmem : litVar b ∈ S
        · have hc : S.contains (litVar b) = true := List.contains_iff_mem.mpr hmem
          simp only [S1, hc, ↓reduceIte]; exact hnd
        · have hc : S.contains (litVar b) = false := by simp [hmem]
          simp only [S1, hc, Bool.false_eq_true, ↓reduceIte]
          exact List.nodup_cons.mpr ⟨hmem, hnd⟩
      have hS1 : ∀ v ∈ S1, s.varLevel v = level ∧
          ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
            litVar s.cdcl.trail[i] = v ∧ i ≤ maxTrl' := by
        intro v hv1
        have hv_or : v = litVar b ∨ v ∈ S := by
          by_cases hmem : litVar b ∈ S
          · have hc : S.contains (litVar b) = true := List.contains_iff_mem.mpr hmem
            simp only [S1, hc, ↓reduceIte] at hv1; exact Or.inr hv1
          · have hc : S.contains (litVar b) = false := by simp [hmem]
            simp only [S1, hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hv1
            exact hv1
        rcases hv_or with rfl | hvS
        · refine ⟨by simpa [MinState.litLevel] using hok.2, ib, hib,
            by rw [hib_eq, litVar_litNeg], ?_⟩
          simp only [maxTrl', hib_pos]; exact Nat.le_max_right _ _
        · obtain ⟨hlvl, i, hi, hieq, hle⟩ := hS v hvS
          exact ⟨hlvl, i, hi, hieq, Nat.le_trans hle (Nat.le_max_left _ _)⟩
      have hih := ih maxTrl' S1 hnd1 hS1
      cases hres : pushBlockLiteralsExec s level bs maxTrl' S1 with
      | none => rw [hres] at hih; trivial
      | some res =>
        rw [hres] at hih
        obtain ⟨a1, a2, a3, a4⟩ := hih
        refine ⟨a1, fun v hv => a2 v ?_, fun x hx => ?_, a4⟩
        · by_cases hmem : litVar b ∈ S
          · have hc : S.contains (litVar b) = true := List.contains_iff_mem.mpr hmem
            simp only [S1, hc, ↓reduceIte]; exact hv
          · have hc : S.contains (litVar b) = false := by simp [hmem]
            simp only [S1, hc, Bool.false_eq_true, ↓reduceIte]
            exact List.mem_cons_of_mem _ hv
        · rcases List.mem_cons.mp hx with rfl | hxbs
          · refine ⟨hb_trl, hok.2, a2 _ ?_⟩
            by_cases hmem : litVar x ∈ S
            · have hc : S.contains (litVar x) = true := List.contains_iff_mem.mpr hmem
              simp only [S1, hc, ↓reduceIte]; exact hmem
            · have hc : S.contains (litVar x) = false := by simp [hmem]
              simp only [S1, hc, Bool.false_eq_true, ↓reduceIte]; exact List.mem_cons_self
          · exact a3 x hxbs
    · rw [ite_eq_right hok]; trivial

private theorem shrinkWalk_props {C : List Nat} {alwaysMin resolveLarge : Bool}
    {maxDepth level : Nat} (_hL : 0 < level) (B : List Nat) :
    ∀ (t openCnt : Nat) (S : List Nat) (st : MinState),
      MinBaseInv st → st.RemovableInv C → S.Nodup →
      (∀ b ∈ B, litVar b ∈ S) →
      openCnt = (S.filter (fun v => decide (st.varTrailPos v ≤ t))).length →
      (∀ v ∈ S, st.varLevel v = level ∧
        ∃ (i : Nat) (_hi : i < st.cdcl.trail.size), litVar st.cdcl.trail[i] = v) →
      (∀ v ∈ S, t < st.varTrailPos v →
        ∃ (i : Nat) (_hi : i < st.cdcl.trail.size),
          litVar st.cdcl.trail[i] = v ∧ AntecedentsShrinkable st level S st.cdcl.trail[i]) →
      match shrinkWalk alwaysMin resolveLarge maxDepth level t openCnt S st with
      | none => True
      | some (uip, S', st') =>
        MinBaseInv st' ∧ st'.cdcl = st.cdcl ∧ st'.trailPos = st.trailPos ∧
        st'.RemovableInv C ∧ (∀ w, st.isRemovable w = true → st'.isRemovable w = true) ∧
        uip ∈ st'.cdcl.trail.toList ∧ stateLevel st'.cdcl uip = level ∧
        litVar uip ∈ S' ∧ (∀ b ∈ B, litVar b ∈ S') ∧
        (∀ v ∈ S', st'.varLevel v = level ∧ varLe st' (litVar uip) v ∧
          (v ≠ litVar uip → ∃ (i : Nat) (_hi : i < st'.cdcl.trail.size),
            litVar st'.cdcl.trail[i] = v ∧
            AntecedentsShrinkable st' level S' st'.cdcl.trail[i])) := by
  intro t
  induction t with
  | zero =>
    intro openCnt S st hst hrm hnd hBS hcnt hS hgt
    unfold shrinkWalk
    cases hget : st.cdcl.trail[0]? with
    | none => simp
    | some uip =>
      dsimp only
      rw [Array.getElem?_eq_some_iff] at hget
      obtain ⟨ht0, htuip⟩ := hget
      by_cases hcont : S.contains (litVar uip) = true
      · have hnot_cont : ¬ ((!S.contains (litVar uip)) = true) := by rw [hcont]; simp
        rw [ite_eq_right hnot_cont]
        by_cases hole : openCnt ≤ 1
        · rw [ite_eq_left hole]; dsimp only
          have huip_in : litVar uip ∈ S := List.contains_iff_mem.mp hcont
          have huip_trl : uip ∈ st.cdcl.trail.toList :=
            trail_mem_iff_exists.mpr ⟨0, ht0, htuip⟩
          have huip_pos : st.varTrailPos (litVar uip) = 0 := by
            unfold MinState.varTrailPos; rw [← htuip]; exact hst.pos_inv 0 ht0
          have hall_eq : ∀ v ∈ S, decide (st.varTrailPos v ≤ 0) = true → v = litVar uip :=
            nodup_filter_length_one hnd huip_in (by simp [huip_pos]) (hcnt ▸ hole)
          refine ⟨hst, rfl, rfl, hrm, fun _ hw => hw, huip_trl,
            by simpa [MinState.varLevel, stateLevel] using (hS _ huip_in).1,
            huip_in, hBS, fun v hv => ?_⟩
          refine ⟨(hS v hv).1, ?_, fun hvne => ?_⟩
          · by_cases hv0 : st.varTrailPos v ≤ 0
            · rw [hall_eq v hv (decide_eq_true hv0)]; exact varLe_refl _ _
            · exact (Or.inr ⟨by rw [(hS v hv).1, (hS _ huip_in).1], by omega⟩)
          · by_cases hv0 : st.varTrailPos v ≤ 0
            · exact absurd (hall_eq v hv (decide_eq_true hv0)) hvne
            · exact hgt v hv (by omega)
        · rw [ite_eq_right hole]
          cases stateReason st.cdcl uip with
          | decision | unit => simp
          | binary other =>
            dsimp only
            cases shrinkLiteralExec alwaysMin maxDepth level other S st with
            | none => simp
            | some _ => simp
          | large cid =>
            dsimp only
            by_cases hr : (!resolveLarge) = true
            · rw [ite_eq_left hr]; simp
            · rw [ite_eq_right hr]
              cases st.cdcl.clauses[cid]? with
              | none => simp
              | some opt =>
                cases opt with
                | none => simp
                | some cl =>
                  dsimp only
                  by_cases hc : (!cl.garbage && cl.lits.contains uip) = true
                  · rw [ite_eq_left hc]
                    cases shrinkAlongLargeExec alwaysMin maxDepth level uip cl.lits 0 S st with
                    | none => simp
                    | some _ => simp
                  · rw [ite_eq_right hc]; simp
      · have hnot_cont : (!S.contains (litVar uip)) = true := by
          rw [Bool.eq_false_iff.mpr hcont]; rfl
        rw [ite_eq_left hnot_cont]; trivial
  | succ t' ih =>
    intro openCnt S st hst hrm hnd hBS hcnt hS hgt
    unfold shrinkWalk
    cases hget : st.cdcl.trail[t' + 1]? with
    | none => simp
    | some uip =>
      dsimp only
      rw [Array.getElem?_eq_some_iff] at hget
      obtain ⟨ht_lt, htuip⟩ := hget
      have hpos_uip : st.varTrailPos (litVar uip) = t' + 1 := by
        unfold MinState.varTrailPos; rw [← htuip]; exact hst.pos_inv (t' + 1) ht_lt
      by_cases hcont : S.contains (litVar uip) = true
      · have hnot_cont : ¬ ((!S.contains (litVar uip)) = true) := by rw [hcont]; simp
        rw [ite_eq_right hnot_cont]
        have huip_in : litVar uip ∈ S := List.contains_iff_mem.mp hcont
        by_cases hole : openCnt ≤ 1
        · rw [ite_eq_left hole]; dsimp only
          have huip_trl : uip ∈ st.cdcl.trail.toList :=
            trail_mem_iff_exists.mpr ⟨t' + 1, ht_lt, htuip⟩
          have hall_eq : ∀ v ∈ S, decide (st.varTrailPos v ≤ t' + 1) = true → v = litVar uip :=
            nodup_filter_length_one hnd huip_in (by simp [hpos_uip]) (hcnt ▸ hole)
          refine ⟨hst, rfl, rfl, hrm, fun _ hw => hw, huip_trl,
            by simpa [MinState.varLevel, stateLevel] using (hS _ huip_in).1,
            huip_in, hBS, fun v hv => ?_⟩
          refine ⟨(hS v hv).1, ?_, fun hvne => ?_⟩
          · by_cases hvt : st.varTrailPos v ≤ t' + 1
            · rw [hall_eq v hv (decide_eq_true hvt)]; exact varLe_refl _ _
            · exact Or.inr ⟨by rw [(hS v hv).1, (hS _ huip_in).1], by omega⟩
          · by_cases hvt : st.varTrailPos v ≤ t' + 1
            · exact absurd (hall_eq v hv (decide_eq_true hvt)) hvne
            · exact hgt v hv (by omega)
        · rw [ite_eq_right hole]
          have hS_pos_ne : ∀ v ∈ S, v ≠ litVar uip → st.varTrailPos v ≠ t' + 1 := by
            intro v hv hvne heqp
            obtain ⟨i, hi, hieq⟩ := (hS v hv).2
            have hip : st.varTrailPos v = i := by
              unfold MinState.varTrailPos; rw [← hieq]; exact hst.pos_inv i hi
            have hieqt : i = t' + 1 := by omega
            subst hieqt
            exact hvne (by rw [← hieq, htuip])
          have hdrop : (S.filter (fun v => decide (st.varTrailPos v ≤ t' + 1))).length =
              (S.filter (fun v => decide (st.varTrailPos v ≤ t'))).length + 1 := by
            refine filter_nodup_drop_one hnd huip_in (by simp [hpos_uip]) (by simp [hpos_uip])
              fun v hv hvne => ?_
            have hne := hS_pos_ne v hv hvne
            by_cases h1 : st.varTrailPos v ≤ t' <;> simp [h1, hne, show st.varTrailPos v ≤ t' + 1 ↔
              st.varTrailPos v ≤ t' ∨ st.varTrailPos v = t' + 1 from by omega]
          have hcnt_drop : (S.filter (fun v => decide (st.varTrailPos v ≤ t'))).length =
              openCnt - 1 := by omega
          have hrd := reason_antecedent_varLt hst ht_lt
          rw [htuip] at hrd
          cases hrsn : stateReason st.cdcl uip with
          | decision | unit => simp
          | binary other =>
            dsimp only
            rw [hrsn] at hrd
            obtain ⟨_, j, hj, hjlt, hjeq, _, hlt_v⟩ := hrd
            have hoth_trl : litNeg other ∈ st.cdcl.trail.toList :=
              trail_mem_iff_exists.mpr ⟨j, hj, hjeq⟩
            have hoth_pos : st.litLevel other = level → st.varTrailPos (litVar other) ≤ t' := by
              intro hlo
              have heql : st.varLevel (litVar other) = st.varLevel (litVar uip) := by
                rw [show st.varLevel (litVar other) = st.litLevel other from rfl, hlo,
                  (hS _ huip_in).1]
              rcases hlt_v with hlt_l | ⟨_, hp_lt⟩
              · omega
              · rw [hpos_uip] at hp_lt; omega
            have hsl := shrinkLiteralExec_sound hst hrm (alwaysMin := alwaysMin)
              (maxDepth := maxDepth) (level := level) (t := t') (lit := other)
              hnd hoth_trl hoth_pos
            cases hsl_res : shrinkLiteralExec alwaysMin maxDepth level other S st with
            | none => trivial
            | some res1 =>
              rw [hsl_res] at hsl; dsimp only
              obtain ⟨added, S1, st1⟩ := res1
              obtain ⟨hb1, hcd1, htp1, hr1, hm1, hnd1, hsub1, hoth_k, hadd_t, hadd_f, hflen⟩ := hsl
              have hS1 : ∀ v ∈ S1, st1.varLevel v = level ∧
                  ∃ (i : Nat) (_hi : i < st1.cdcl.trail.size), litVar st1.cdcl.trail[i] = v := by
                intro v hv1
                cases added
                · rw [hadd_f rfl] at hv1
                  obtain ⟨hlvl, i, hi, hieq⟩ := hS v hv1
                  have hi1 : i < st1.cdcl.trail.size := by simpa [hcd1] using hi
                  refine ⟨by simpa [MinState.varLevel, hcd1] using hlvl, i, hi1, ?_⟩
                  rw [trail_getElem_of_eq hcd1 hi1 hi, hieq]
                · obtain ⟨hlvlo, _, hS1eq, _⟩ := hadd_t rfl
                  rw [hS1eq] at hv1
                  rcases List.mem_cons.mp hv1 with rfl | hvS
                  · have hj1 : j < st1.cdcl.trail.size := by simpa [hcd1] using hj
                    exact ⟨hlvlo, j, hj1,
                      by rw [trail_getElem_of_eq hcd1 hj1 hj, hjeq, litVar_litNeg]⟩
                  · obtain ⟨hlvl, i, hi, hieq⟩ := hS v hvS
                    have hi1 : i < st1.cdcl.trail.size := by simpa [hcd1] using hi
                    refine ⟨by simpa [MinState.varLevel, hcd1] using hlvl, i, hi1, ?_⟩
                    rw [trail_getElem_of_eq hcd1 hi1 hi, hieq]
              let open1 := if added then openCnt else openCnt - 1
              have hcnt1 :
                  open1 = (S1.filter (fun v => decide (st1.varTrailPos v ≤ t'))).length := by
                cases added <;>
                  simp only [open1, Bool.false_eq_true, ↓reduceIte] at hflen ⊢ <;> omega
              have hgt1 : ∀ v ∈ S1, t' < st1.varTrailPos v →
                  ∃ (i : Nat) (_hi : i < st1.cdcl.trail.size),
                    litVar st1.cdcl.trail[i] = v ∧
                    AntecedentsShrinkable st1 level S1 st1.cdcl.trail[i] := by
                intro v hv1 hvp
                have hvS : v ∈ S := by
                  cases added
                  · rwa [hadd_f rfl] at hv1
                  · obtain ⟨_, _, hS1eq, hpos_o⟩ := hadd_t rfl
                    rw [hS1eq] at hv1
                    rcases List.mem_cons.mp hv1 with rfl | hvS
                    · omega
                    · exact hvS
                have hvp_s : t' < st.varTrailPos v := by
                  simpa [MinState.varTrailPos, htp1] using hvp
                by_cases hveq_u : v = litVar uip
                · have ht1_lt : t' + 1 < st1.cdcl.trail.size := by simpa [hcd1] using ht_lt
                  refine ⟨t' + 1, ht1_lt, ?_, ?_⟩
                  · rw [trail_getElem_of_eq hcd1 ht1_lt ht_lt, htuip, hveq_u]
                  · unfold AntecedentsShrinkable
                    have hsr1 : stateReason st1.cdcl st1.cdcl.trail[t' + 1] = .binary other := by
                      rw [trail_getElem_of_eq hcd1 ht1_lt ht_lt, htuip]
                      unfold stateReason; rw [hcd1]; exact hrsn
                    rw [hsr1]; exact hoth_k
                · have hne_t : st.varTrailPos v ≠ t' + 1 := hS_pos_ne v hvS hveq_u
                  obtain ⟨i, hi, hiveq, ha⟩ := hgt v hvS (by omega)
                  have hi1 : i < st1.cdcl.trail.size := by simpa [hcd1] using hi
                  refine ⟨i, hi1, ?_, ?_⟩
                  · rw [trail_getElem_of_eq hcd1 hi1 hi, hiveq]
                  · rw [trail_getElem_of_eq hcd1 hi1 hi]
                    exact ha.mono hcd1 hm1 hsub1
              have hih := ih open1 S1 st1 hb1 hr1 hnd1 (fun b hb => hsub1 _ (hBS b hb))
                hcnt1 hS1 hgt1
              cases hres : shrinkWalk alwaysMin resolveLarge maxDepth level t' open1 S1 st1 with
              | none => rw [hres] at hih; trivial
              | some res2 =>
                rw [hres] at hih
                obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hih
                exact ⟨a1, a2.trans hcd1, a3.trans htp1, a4, fun w hw => a5 w (hm1 w hw),
                  a6, a7, a8, a9, a10⟩
          | large cid =>
            dsimp only
            by_cases hrl : resolveLarge = true
            · have hnrl : (!resolveLarge) = false := by simp [hrl]
              rw [ite_eq_right (by simp [hnrl])]
              rw [hrsn] at hrd
              obtain ⟨c, hget_c, _, _, hall_c⟩ := hrd
              cases hget_cl : st.cdcl.clauses[cid]? with
              | none => simp [hget_cl] at hget_c
              | some opt =>
                cases opt with
                | none => simp [hget_cl] at hget_c
                | some cl =>
                  have hcleq : cl = c := by
                    rw [hget_cl] at hget_c; injection hget_c with h1; injection h1
                  subst hcleq
                  dsimp only
                  by_cases hcond : (!cl.garbage && cl.lits.contains uip) = true
                  · rw [ite_eq_left hcond]
                    have hsal := shrinkAlongLargeExec_props (C := C) (alwaysMin := alwaysMin)
                      (maxDepth := maxDepth) (level := level) (uip := uip) (t := t') cl.lits
                      0 S st hst hrm hnd hS
                      (fun x hx hxne => by
                        obtain ⟨j, hj, _, hjeq, _, _⟩ := hall_c x hx hxne
                        exact trail_mem_iff_exists.mpr ⟨j, hj, hjeq⟩)
                      (fun x hx hxne hlx => by
                        obtain ⟨j, hj, hjlt, hjeq, _, hlt_v⟩ := hall_c x hx hxne
                        have heql : st.varLevel (litVar x) = st.varLevel (litVar uip) := by
                          rw [show st.varLevel (litVar x) = st.litLevel x from rfl, hlx,
                            (hS _ huip_in).1]
                        rcases hlt_v with hlt_l | ⟨_, hp_lt⟩
                        · omega
                        · rw [hpos_uip] at hp_lt; omega)
                    cases hsal_res :
                        shrinkAlongLargeExec alwaysMin maxDepth level uip cl.lits 0 S st with
                    | none => trivial
                    | some res1 =>
                      rw [hsal_res] at hsal; dsimp only
                      obtain ⟨pushed, S1, st1⟩ := res1
                      obtain ⟨hb1, hcd1, htp1, hr1, hm1, hnd1, hsub1, hS1, hlits1, hnew1,
                        hflen1⟩ := hsal
                      have hcnt1 : openCnt + pushed - 1 =
                          (S1.filter (fun v => decide (st1.varTrailPos v ≤ t'))).length := by
                        omega
                      have hgt1 : ∀ v ∈ S1, t' < st1.varTrailPos v →
                          ∃ (i : Nat) (_hi : i < st1.cdcl.trail.size),
                            litVar st1.cdcl.trail[i] = v ∧
                            AntecedentsShrinkable st1 level S1 st1.cdcl.trail[i] := by
                        intro v hv1 hvp
                        have hvp_s : t' < st.varTrailPos v := by
                          simpa [MinState.varTrailPos, htp1] using hvp
                        by_cases hveq_u : v = litVar uip
                        · have ht1_lt : t' + 1 < st1.cdcl.trail.size := by
                            simpa [hcd1] using ht_lt
                          refine ⟨t' + 1, ht1_lt, ?_, ?_⟩
                          · rw [trail_getElem_of_eq hcd1 ht1_lt ht_lt, htuip, hveq_u]
                          · unfold AntecedentsShrinkable
                            have hsr1 : stateReason st1.cdcl st1.cdcl.trail[t' + 1] =
                                .large cid := by
                              rw [trail_getElem_of_eq hcd1 ht1_lt ht_lt, htuip]
                              unfold stateReason; rw [hcd1]; exact hrsn
                            rw [hsr1]
                            simp only [Bool.and_eq_true, List.contains_iff_mem] at hcond
                            refine ⟨cl, by simpa [hcd1] using hget_cl, hcond.1, ?_,
                              fun x hx hxne => ?_⟩
                            · rw [trail_getElem_of_eq hcd1 ht1_lt ht_lt, htuip]; exact hcond.2
                            · have hxne' : x ≠ uip := by
                                rwa [trail_getElem_of_eq hcd1 ht1_lt ht_lt, htuip] at hxne
                              exact hlits1 x hx hxne'
                        · have hvS : v ∈ S := Classical.byContradiction fun hnv => by
                            have hpos_v : st1.varTrailPos v ≤ t' := hnew1 v hv1 hnv
                            omega
                          have hne_t : st.varTrailPos v ≠ t' + 1 := hS_pos_ne v hvS hveq_u
                          obtain ⟨i, hi, hiveq, ha⟩ := hgt v hvS (by omega)
                          have hi1 : i < st1.cdcl.trail.size := by simpa [hcd1] using hi
                          refine ⟨i, hi1, ?_, ?_⟩
                          · rw [trail_getElem_of_eq hcd1 hi1 hi, hiveq]
                          · rw [trail_getElem_of_eq hcd1 hi1 hi]
                            exact ha.mono hcd1 hm1 hsub1
                      have hih := ih (openCnt + pushed - 1) S1 st1 hb1 hr1 hnd1
                        (fun b hb => hsub1 _ (hBS b hb)) hcnt1 hS1 hgt1
                      cases hres : shrinkWalk alwaysMin resolveLarge maxDepth level t'
                          (openCnt + pushed - 1) S1 st1 with
                      | none => rw [hres] at hih; trivial
                      | some res2 =>
                        rw [hres] at hih
                        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hih
                        exact ⟨a1, a2.trans hcd1, a3.trans htp1, a4, fun w hw => a5 w (hm1 w hw),
                          a6, a7, a8, a9, a10⟩
                  · rw [ite_eq_right hcond]; trivial
            · have hnrl : (!resolveLarge) = true := by simp [hrl]
              rw [ite_eq_left hnrl]; trivial
      · have hnot_cont : (!S.contains (litVar uip)) = true := by
          rw [Bool.eq_false_iff.mpr hcont]; rfl
        rw [ite_eq_left hnot_cont]
        have hnuip : litVar uip ∉ S := fun hm => hcont (List.contains_iff_mem.mpr hm)
        have hcnt' : openCnt = (S.filter (fun v => decide (st.varTrailPos v ≤ t'))).length := by
          rw [hcnt]; congr 1; apply List.filter_congr; intro v hv
          have hvne : v ≠ litVar uip := fun heq => hnuip (heq ▸ hv)
          obtain ⟨i, hi, hieq⟩ := (hS v hv).2
          have hpi : st.varTrailPos v = i := by
            unfold MinState.varTrailPos; rw [← hieq]; exact hst.pos_inv i hi
          have hne_pos : st.varTrailPos v ≠ t' + 1 := by
            intro heqp
            have hieqt : i = t' + 1 := by omega
            subst hieqt
            exact hvne (by rw [← hieq, htuip])
          have hle_iff : st.varTrailPos v ≤ t' + 1 ↔ st.varTrailPos v ≤ t' := by omega
          by_cases h1 : st.varTrailPos v ≤ t' <;> simp [h1, hle_iff]
        have hgt' : ∀ v ∈ S, t' < st.varTrailPos v →
            ∃ (i : Nat) (_hi : i < st.cdcl.trail.size),
              litVar st.cdcl.trail[i] = v ∧ AntecedentsShrinkable st level S st.cdcl.trail[i] := by
          intro v hv hvp
          have hvne : v ≠ litVar uip := fun heq => hnuip (heq ▸ hv)
          obtain ⟨i, hi, hieq⟩ := (hS v hv).2
          have hpi : st.varTrailPos v = i := by
            unfold MinState.varTrailPos; rw [← hieq]; exact hst.pos_inv i hi
          have hne_pos : st.varTrailPos v ≠ t' + 1 := by
            intro heqp
            have hieqt : i = t' + 1 := by omega
            subst hieqt
            exact hvne (by rw [← hieq, htuip])
          exact hgt v hv (by omega)
        exact ih openCnt S st hst hrm hnd hBS hcnt' hS hgt'


/-- Executable soundness of `shrinkBlockExec`: preserves `MinBaseInv`, `cdcl`, `trailPos`,
`RemovableInv`, `F₀.EntailsClause`, trail falsification, and `isRemovable` monotonicity. -/
theorem shrink_block_sound {s : MinState} (h : MinBaseInv s) {C B : List Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause C))
    (hrem : s.RemovableInv C)
    (_hfals : ∀ l ∈ C, litNeg l ∈ s.cdcl.trail.toList)
    (alwaysMin resolveLarge : Bool) (maxDepth level : Nat) :
    let (shrank, B', s') := shrinkBlockExec s alwaysMin resolveLarge maxDepth level B
    MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
    (∀ w, s.isRemovable w = true → s'.isRemovable w = true) ∧
    (shrank = true →
      let C' := B' ++ C.filter (fun l => !B.contains l)
      s'.cdcl.f0.EntailsClause (cnfClause C') ∧ s'.RemovableInv C' ∧
      ∀ l ∈ B', litNeg l ∈ s'.cdcl.trail.toList) ∧
    (shrank = false → B' = B ∧ s' = s) := by
  unfold shrinkBlockExec
  by_cases hguard : (level == 0 || B.length < 2) = true
  · rw [ite_eq_left hguard]; dsimp only
    exact ⟨h, rfl, rfl, fun _ hw => hw, (fun hf => by cases hf), fun _ => ⟨rfl, rfl⟩⟩
  · have hguard_f : (level == 0 || B.length < 2) = false := Bool.eq_false_iff.mpr hguard
    rw [ite_eq_right (by simp [hguard_f])]; dsimp only
    have hL : 0 < level := by
      rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hguard_f
      exact Nat.pos_of_ne_zero hguard_f.1
    have hpush := pushBlockLiteralsExec_props h level B 0 [] List.nodup_nil
      (fun _ hm => by cases hm)
    cases hpres : pushBlockLiteralsExec s level B 0 [] with
    | none =>
      dsimp only
      exact ⟨h, rfl, rfl, fun _ hw => hw, (fun hf => by cases hf), fun _ => ⟨rfl, rfl⟩⟩
    | some p =>
      rw [hpres] at hpush; dsimp only
      obtain ⟨maxTrl, initS⟩ := p
      obtain ⟨hnd_i, _, hB_i, hS_i⟩ := hpush
      have hcnt_i : initS.length =
          (initS.filter (fun v => decide (s.varTrailPos v ≤ maxTrl))).length := by
        have hf : initS.filter (fun v => decide (s.varTrailPos v ≤ maxTrl)) = initS := by
          apply List.filter_eq_self.mpr
          intro v hv
          obtain ⟨_, i, hi, hieq, hle⟩ := hS_i v hv
          have hp : s.varTrailPos v = i := by
            unfold MinState.varTrailPos; rw [← hieq]; exact h.pos_inv i hi
          exact decide_eq_true (hp ▸ hle)
        rw [hf]
      have hgt_i : ∀ v ∈ initS, maxTrl < s.varTrailPos v →
          ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
            litVar s.cdcl.trail[i] = v ∧ AntecedentsShrinkable s level initS s.cdcl.trail[i] := by
        intro v hv hlt
        obtain ⟨_, i, hi, hieq, hle⟩ := hS_i v hv
        have hp : s.varTrailPos v = i := by
          unfold MinState.varTrailPos; rw [← hieq]; exact h.pos_inv i hi
        omega
      have hwalk := shrinkWalk_props (C := C) (alwaysMin := alwaysMin)
        (resolveLarge := resolveLarge) (maxDepth := maxDepth) hL B maxTrl initS.length initS s h
        hrem hnd_i (fun b hb => (hB_i b hb).2.2) hcnt_i
        (fun v hv => let ⟨hl, i, hi, heq, _⟩ := hS_i v hv; ⟨hl, i, hi, heq⟩)
        hgt_i
      cases hw_res :
          shrinkWalk alwaysMin resolveLarge maxDepth level maxTrl initS.length initS s with
      | none =>
        dsimp only
        exact ⟨h, rfl, rfl, fun _ hw => hw, (fun hf => by cases hf), fun _ => ⟨rfl, rfl⟩⟩
      | some wres =>
        rw [hw_res] at hwalk; dsimp only
        obtain ⟨uip, S, st⟩ := wres
        obtain ⟨hst_b, hst_cd, hst_tp, hst_rem, hst_mn, huip_trl, huip_lvl, _, hB_S, hS_all⟩ :=
          hwalk
        have hB_st : ∀ b ∈ B, litNeg b ∈ st.cdcl.trail.toList ∧ st.litLevel b = level ∧
            litVar b ∈ S := by
          intro b hb
          have hb0 := hB_i b hb
          refine ⟨by rw [hst_cd]; exact hb0.1,
            by simpa [MinState.litLevel, MinState.varLevel, hst_cd] using hb0.2.1, hB_S b hb⟩
        have hcut := shrink_block_cut_sound hst_b (by simpa [hst_cd] using hent) hst_rem hL
          huip_trl huip_lvl hB_st hS_all
        refine ⟨hcut.1, hcut.2.1.trans hst_cd, hcut.2.2.1.trans hst_tp,
          fun w hw => hcut.2.2.2.2.2 w (hst_mn w hw), fun _ => ?_, (fun hf => by cases hf)⟩
        refine ⟨hcut.2.2.2.1, hcut.2.2.2.2.1, fun l hl => ?_⟩
        simp only [List.mem_singleton] at hl; subst hl
        rw [litNeg_litNeg, hcut.2.1]; exact huip_trl

end LeanQbe.T.Examples.Kissat.Ref
