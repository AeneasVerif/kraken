module

public import LeanQbe.T.Examples.Kissat.LayerAMinimize3

/-!
# Pure Lean Layer-A CDCL Theory: Clause Shrinking & Failed-Literal Analysis

Builds on `LayerAMinimize3` (pure Lean, zero `Kraken.Mem` imports):

1. **`minimizeBlockExec_sound` and `shrink_clause_sound`** (`kissat_shrink_clause`, `shrink.c`):
   end-to-end soundness of `splitLevelBlocksRev`, `shrinkBlockExec`, and `minimizeBlockExec`
   fallback across all maximal level blocks, plus `resetPoisoned`.
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

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std.Sat

/-- Soundness of `minimizeBlockExec` inside a surrounding clause `pref ++ B ++ suff`. -/
theorem minimizeBlockExec_sound {s : MinState} (h : MinBaseInv s)
    {pref B suff : List Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause (pref ++ B ++ suff)))
    (hrem : s.RemovableInv (pref ++ B ++ suff))
    (hfals : ∀ l ∈ pref ++ B ++ suff, litNeg l ∈ s.cdcl.trail.toList)
    (maxDepth : Nat) :
    let (B', s') := minimizeBlockExec s maxDepth B
    MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
    s'.cdcl.f0.EntailsClause (cnfClause (pref ++ B' ++ suff)) ∧
    s'.RemovableInv (pref ++ B' ++ suff) ∧
    (∀ l ∈ B', l ∈ B) ∧
    (∀ l ∈ pref ++ B' ++ suff, litNeg l ∈ s'.cdcl.trail.toList) ∧
    (∀ w, s.isRemovable w = true → s'.isRemovable w = true) := by
  have hfold : ∀ (xs acc : List Nat) (st : MinState),
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
      (∀ w, st.isRemovable w = true → res.2.isRemovable w = true) := by
    intro xs
    induction xs with
    | nil =>
      intro acc st hst hcdcl htp hent' hrem' hacc _
      simp only [List.foldl_nil]
      refine ⟨hst, hcdcl, htp, by simpa using hent', by simpa using hrem', fun l hl => ?_,
        fun _ hw => hw⟩
      exact hacc l (List.mem_reverse.mp hl)
    | cons x xs ih =>
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
          have hih := ih acc st1 hb1 (hcd1.trans hcdcl) (htp1.trans htp)
            hsub_ent hsub_rem hacc1 hxs'
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
          have hih := ih (x :: acc) st1 hb1 (hcd1.trans hcdcl) (htp1.trans htp)
            hent1 hrem1 hacc1 hxs'
          exact ⟨hih.1, hih.2.1, hih.2.2.1, hih.2.2.2.1, hih.2.2.2.2.1, hih.2.2.2.2.2.1,
            fun w hw => hih.2.2.2.2.2.2 w (hm1 w hw)⟩
  have hmain := hfold B [] s h rfl rfl (by simpa using hent) (by simpa using hrem)
    (fun _ hl => by cases hl)
    (fun l hl => ⟨hfals l (List.mem_append_left _ (List.mem_append_right _ hl)), hl⟩)
  unfold minimizeBlockExec
  dsimp only
  cases hres : B.foldl (fun (p : List Nat × MinState) lit =>
      let (ok, st') := minimizeLiteralWorklist p.2 true maxDepth lit 0
      if ok then (p.1, st') else (lit :: p.1, st')) ([], s) with
  | mk keptRev sEnd =>
    rw [hres] at hmain
    refine ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2.1,
      fun l hl => (hmain.2.2.2.2.2.1 l hl).2, fun l hl => ?_, hmain.2.2.2.2.2.2⟩
    rw [hmain.2.1]
    rcases List.mem_append.mp hl with hpb | hsuf
    · rcases List.mem_append.mp hpb with hp | hb'
      · exact hfals l (List.mem_append_left _ (List.mem_append_left _ hp))
      · exact (by rw [← hmain.2.1]; exact (hmain.2.2.2.2.2.1 l hb').1)
    · exact hfals l (List.mem_append_right _ hsuf)

private theorem splitLevelBlocksRev_foldl (s : MinState) (C : List Nat) :
    (splitLevelBlocksRev s C).foldl (fun acc (_, B) => B ++ acc) [] = C := by
  cases C with
  | nil => simp [splitLevelBlocksRev]
  | cons l ls =>
    have hgen : ∀ (xs : List Nat) (curLvl : Nat) (curBlk : List Nat)
        (done : List (Nat × List Nat)) (init : List Nat),
        ((xs.foldl (init := (curLvl, curBlk, done))
          (fun (curLvl, curBlk, done) x =>
            let lx := s.litLevel x
            if lx == curLvl then (curLvl, x :: curBlk, done)
            else (lx, [x], (curLvl, curBlk.reverse) :: done))).2.2.foldl
            (fun acc (_, B) => B ++ acc)
            ((xs.foldl (init := (curLvl, curBlk, done))
              (fun (curLvl, curBlk, done) x =>
                let lx := s.litLevel x
                if lx == curLvl then (curLvl, x :: curBlk, done)
                else (lx, [x], (curLvl, curBlk.reverse) :: done))).2.1.reverse ++ init)) =
          done.foldl (fun acc (_, B) => B ++ acc) (curBlk.reverse ++ xs ++ init) := by
      intro xs
      induction xs with
      | nil => intro curLvl curBlk done init; simp
      | cons x xs ih =>
        intro curLvl curBlk done init
        simp only [List.foldl_cons]
        by_cases h : (s.litLevel x == curLvl) = true
        · simp only [h, ↓reduceIte]
          rw [ih curLvl (x :: curBlk) done init]
          simp [List.reverse_cons, List.append_assoc]
        · have hf : (s.litLevel x == curLvl) = false := Bool.eq_false_iff.mpr h
          simp only [hf, Bool.false_eq_true, ↓reduceIte]
          rw [ih (s.litLevel x) [x] ((curLvl, curBlk.reverse) :: done) init]
          simp [List.foldl_cons, List.append_assoc]
    have h0 := hgen ls (s.litLevel l) [l] [] []
    simp only [splitLevelBlocksRev, List.foldl_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.append_nil] at h0 ⊢
    cases hfl : ls.foldl (init := (s.litLevel l, [l], [])) (fun p x =>
        let lx := s.litLevel x
        if lx == p.1 then (p.1, x :: p.2.1, p.2.2)
        else (lx, [x], (p.1, p.2.1.reverse) :: p.2.2)) with
    | mk a b =>
      cases b with
      | mk curBlk done =>
        simp only [hfl, List.foldl_cons, List.append_nil] at h0 ⊢
        exact h0

/-- Full clause-shrinking soundness (`kissat_shrink_clause`, `shrink_clause_sound`):
preserves `MinBaseInv`, `cdcl`, `trailPos`, `F₀.EntailsClause`, `RemovableInv`, trail falsification
of literals, and monotonically preserves cached `removable` flags (resetting `poisoned`). -/
theorem shrink_clause_sound {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause C))
    (hrem : s.RemovableInv C)
    (hfals : ∀ l ∈ C, litNeg l ∈ s.cdcl.trail.toList)
    (alwaysMin resolveLarge : Bool) (maxDepth : Nat) :
    let (C', s') := shrinkClauseExec s alwaysMin resolveLarge maxDepth C
    MinBaseInv s' ∧ s'.cdcl = s.cdcl ∧ s'.trailPos = s.trailPos ∧
    s'.cdcl.f0.EntailsClause (cnfClause C') ∧ s'.RemovableInv C' ∧
    (∀ l ∈ C', litNeg l ∈ s'.cdcl.trail.toList) ∧
    (∀ w, s.isRemovable w = true → s'.isRemovable w = true) := by
  have hfold : ∀ (blocks : List (Nat × List Nat)) (acc : List Nat) (st : MinState),
      MinBaseInv st → st.cdcl = s.cdcl → st.trailPos = s.trailPos →
      let curC := blocks.foldl (fun a (_, B) => B ++ a) [] ++ acc
      st.cdcl.f0.EntailsClause (cnfClause curC) →
      st.RemovableInv curC →
      (∀ l ∈ curC, litNeg l ∈ st.cdcl.trail.toList) →
      let res := blocks.foldl (init := (acc, st)) fun (a, st1) (lvl, B) =>
        if B.length < 2 then (B ++ a, st1)
        else
          let (shrank, B', st') := shrinkBlockExec st1 alwaysMin resolveLarge maxDepth lvl B
          if shrank then (B' ++ a, st')
          else
            let (B'', st'') := minimizeBlockExec st' maxDepth B
            (B'' ++ a, st'')
      MinBaseInv res.2 ∧ res.2.cdcl = s.cdcl ∧ res.2.trailPos = s.trailPos ∧
      res.2.cdcl.f0.EntailsClause (cnfClause res.1) ∧ res.2.RemovableInv res.1 ∧
      (∀ l ∈ res.1, litNeg l ∈ res.2.cdcl.trail.toList) ∧
      (∀ w, st.isRemovable w = true → res.2.isRemovable w = true) := by
    intro blocks
    induction blocks with
    | nil =>
      intro acc st hst hcdcl htp _ hent' hrem' hfals'
      simp only [List.foldl_nil] at hent' hrem' hfals' ⊢
      exact ⟨hst, hcdcl, htp, hent', hrem', hfals', fun _ hw => hw⟩
    | cons p rest ih =>
      intro acc st hst hcdcl htp curC hent' hrem' hfals'
      obtain ⟨lvl, B⟩ := p
      have hfold_rest : rest.foldl (fun a (_, b) => b ++ a) B =
          rest.foldl (fun a (_, b) => b ++ a) [] ++ B := by
        have hgen : ∀ (bs : List (Nat × List Nat)) (init1 init2 : List Nat),
            bs.foldl (fun a (_, b) => b ++ a) (init1 ++ init2) =
              bs.foldl (fun a (_, b) => b ++ a) init1 ++ init2 := by
          intro bs
          induction bs with
          | nil => intro i1 i2; simp
          | cons q qs ihq =>
            intro i1 i2; simp only [List.foldl_cons]
            rw [← List.append_assoc]
            exact ihq (q.2 ++ i1) i2
        exact hgen rest [] B
      have hcur : curC = rest.foldl (fun a (_, b) => b ++ a) [] ++ B ++ acc := by
        dsimp only [curC]
        simp only [List.foldl_cons, List.append_nil]
        rw [hfold_rest, List.append_assoc]
      rw [hcur] at hent' hrem' hfals'
      simp only [List.foldl_cons]
      by_cases hlt2 : B.length < 2
      · rw [ite_eq_left hlt2]
        have hih := ih (B ++ acc) st hst hcdcl htp (by simpa [List.append_assoc] using hent')
          (by simpa [List.append_assoc] using hrem') (by simpa [List.append_assoc] using hfals')
        exact hih
      · rw [ite_eq_right (by simp [hlt2])]
        have hsb := shrink_block_sound hst (B := B) hent' hrem' hfals'
          alwaysMin resolveLarge maxDepth lvl
        cases hres : shrinkBlockExec st alwaysMin resolveLarge maxDepth lvl B with
        | mk shrank p2 =>
          obtain ⟨B', st'⟩ := p2
          rw [hres] at hsb
          obtain ⟨hb1, hcd1, htp1, hm1, hs_t, hs_f⟩ := hsb
          cases shrank with
          | true =>
            dsimp only
            obtain ⟨hent_cut, hrem_cut, hfals_B'⟩ := hs_t rfl
            let remL := rest.foldl (fun a (_, b) => b ++ a) []
            let nxtC := remL ++ (B' ++ acc)
            have hsub :
                ∀ x ∈ B' ++ (remL ++ B ++ acc).filter (fun l => !B.contains l), x ∈ nxtC := by
              intro x hx
              rcases List.mem_append.mp hx with hxb | hxf
              · exact List.mem_append_right _ (List.mem_append_left _ hxb)
              · rw [List.mem_filter] at hxf
                rcases List.mem_append.mp hxf.1 with hrb | ha
                · rcases List.mem_append.mp hrb with hr | hb
                  · exact List.mem_append_left _ hr
                  · simp [hb] at hxf
                · exact List.mem_append_right _ (List.mem_append_right _ ha)
            have hent_nxt : st'.cdcl.f0.EntailsClause (cnfClause nxtC) := by
              rw [CNF.entails_clause_def] at hent_cut ⊢
              intro α hα
              obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (hent_cut α hα)
              exact (clause_sat_cnfClause_iff α _).mpr ⟨y, hsub y hy, hys⟩
            have hrem_nxt : st'.RemovableInv nxtC := removableInv_mono_clause hsub hrem_cut
            have hfals_nxt : ∀ l ∈ nxtC, litNeg l ∈ st'.cdcl.trail.toList := by
              intro l hl
              rcases List.mem_append.mp hl with hrem_l | hba
              · rw [hcd1]; exact hfals' l (List.mem_append_left _ (List.mem_append_left _ hrem_l))
              · rcases List.mem_append.mp hba with hb' | ha
                · exact hfals_B' l hb'
                · rw [hcd1]; exact hfals' l (List.mem_append_right _ ha)
            have hih := ih (B' ++ acc) st' hb1 (hcd1.trans hcdcl) (htp1.trans htp)
              hent_nxt hrem_nxt hfals_nxt
            exact ⟨hih.1, hih.2.1, hih.2.2.1, hih.2.2.2.1, hih.2.2.2.2.1, hih.2.2.2.2.2.1,
              fun w hw => hih.2.2.2.2.2.2 w (hm1 w hw)⟩
          | false =>
            dsimp only
            obtain ⟨_, hsteq⟩ := hs_f rfl
            rw [hsteq]
            have hmb := minimizeBlockExec_sound hst hent' hrem' hfals' maxDepth
            cases hmres : minimizeBlockExec st maxDepth B with
            | mk B'' st'' =>
              rw [hmres] at hmb
              obtain ⟨hb'', hcd'', htp'', hent'', hrem'', _, hfals'', hm''⟩ := hmb
              have hih := ih (B'' ++ acc) st'' hb'' (hcd''.trans hcdcl) (htp''.trans htp)
                (by simpa [List.append_assoc] using hent'')
                (by simpa [List.append_assoc] using hrem'')
                (by simpa [List.append_assoc] using hfals'')
              exact ⟨hih.1, hih.2.1, hih.2.2.1, hih.2.2.2.1, hih.2.2.2.2.1, hih.2.2.2.2.2.1,
                fun w hw => hih.2.2.2.2.2.2 w (hm'' w hw)⟩
  have hfl := splitLevelBlocksRev_foldl s C
  have hmain := hfold (splitLevelBlocksRev s C) [] s h rfl rfl
    (by simp only [hfl, List.append_nil]; exact hent)
    (by simp only [hfl, List.append_nil]; exact hrem)
    (by simp only [hfl, List.append_nil]; exact hfals)
  unfold shrinkClauseExec
  dsimp only
  cases hres : (splitLevelBlocksRev s C).foldl (init := ([], s)) (fun (a, st1) (lvl, B) =>
      if B.length < 2 then (B ++ a, st1)
      else
        let (shrank, B', st') := shrinkBlockExec st1 alwaysMin resolveLarge maxDepth lvl B
        if shrank then (B' ++ a, st')
        else
          let (B'', st'') := minimizeBlockExec st' maxDepth B
          (B'' ++ a, st'')) with
  | mk resAcc sEnd =>
    rw [hres] at hmain
    refine ⟨hmain.1.resetPoisoned, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [MinState.cdcl_resetPoisoned] using hmain.2.1
    · simpa [MinState.trailPos_resetPoisoned] using hmain.2.2.1
    · simpa [MinState.cdcl_resetPoisoned] using hmain.2.2.2.1
    · exact removableInv_resetPoisoned.mpr hmain.2.2.2.2.1
    · intro l hl; simpa [MinState.cdcl_resetPoisoned] using hmain.2.2.2.2.2.1 l hl
    · intro w hw; rw [MinState.isRemovable_resetPoisoned]; exact hmain.2.2.2.2.2.2 w hw

/-! ## 2. Failed-literal backward analysis (`analyze.c:390-517`) -/

/-- Scan conflict clause in `analyze_failed_literal` (`analyze.c:410-426`), collecting level-1
falsified trail literals in `A` or returning `none` (`goto DONE`) if `notFailed ∈ conflict`. -/
def scanFailedConflict (s : CdclState) (notFailed : Nat) :
    List Nat → List Nat → Option (List Nat)
  | [], A => some A
  | lit :: rest, A =>
    if lit == notFailed then none
    else if stateLevel s lit == 0 then scanFailedConflict s notFailed rest A
    else
      let t := litNeg lit
      let A' := if A.any (fun a => litVar a == litVar t) then A else t :: A
      scanFailedConflict s notFailed rest A'

/-- Scan a `.large` reason clause in `analyze_failed_literal` (`analyze.c:468-491`), skipping
`other == lit`, skipping `prevUnit == some other` (`other == unit`, proved unreachable by
`failedLit_other_ne_unit`), returning `none` on `other == notFailed` (`goto DONE`), skipping
level-0 literals, and collecting new level-1 antecedents. -/
def resolveLargeFailed (s : CdclState) (lit notFailed : Nat) (prevUnit : Option Nat) :
    List Nat → List Nat → Option (List Nat)
  | [], A => some A
  | other :: rest, A =>
    if other == lit then
      resolveLargeFailed s lit notFailed prevUnit rest A
    else if prevUnit == some other then
      resolveLargeFailed s lit notFailed prevUnit rest A
    else if other == notFailed then
      none
    else if stateLevel s other == 0 then
      resolveLargeFailed s lit notFailed prevUnit rest A
    else
      let t := litNeg other
      let A' := if A.any (fun a => litVar a == litVar t) then A else t :: A
      resolveLargeFailed s lit notFailed prevUnit rest A'

/-- Backward trail walk in `analyze_failed_literal` (`analyze.c:428-497`), stopping at `t == 0`,
emitting additional units when `unresolved == 1` (`A_rest.isEmpty`), and appending `notFailed` at
`DONE`. -/
def analyzeFailedLoop (s : CdclState) (notFailed : Nat) :
    Nat → List Nat → List Nat → Option Nat → List Nat
  | t, A, units, prevUnit =>
    match s.trail[t]? with
    | none => units ++ [notFailed]
    | some lit =>
      if !A.any (fun a => litVar a == litVar lit) then
        match t with
        | 0 => units ++ [notFailed]
        | t' + 1 => analyzeFailedLoop s notFailed t' A units prevUnit
      else
        let A_rest := A.filter (fun a => litVar a != litVar lit)
        let emit := A_rest.isEmpty
        let prevUnit' := if emit then some (litNeg lit) else prevUnit
        let units' := if emit then units ++ [litNeg lit] else units
        match stateReason s lit with
        | .decision | .unit => units' ++ [notFailed]
        | .binary other =>
          if prevUnit' == some other then
            units' ++ [notFailed]
          else if other == notFailed then
            units' ++ [notFailed]
          else if stateLevel s other == 0 then
            match t with
            | 0 => units' ++ [notFailed]
            | t' + 1 => analyzeFailedLoop s notFailed t' A_rest units' prevUnit'
          else
            let tOth := litNeg other
            let A' :=
              if A_rest.any (fun a => litVar a == litVar tOth) then A_rest else tOth :: A_rest
            match t with
            | 0 => units' ++ [notFailed]
            | t' + 1 => analyzeFailedLoop s notFailed t' A' units' prevUnit'
        | .large cid =>
          match s.clauses[cid]? with
          | some (some cl) =>
            if !cl.garbage && cl.lits.contains lit then
              match resolveLargeFailed s lit notFailed prevUnit' cl.lits A_rest with
              | none => units' ++ [notFailed]
              | some A' =>
                match t with
                | 0 => units' ++ [notFailed]
                | t' + 1 => analyzeFailedLoop s notFailed t' A' units' prevUnit'
            else
              units' ++ [notFailed]
          | _ => units' ++ [notFailed]

/-- Full executable model of `analyze_failed_literal` (`analyze.c:390-517`): returns all learned
unit literals (intermediate units followed by `litNeg failed`). -/
def analyzeFailedLiteralExec (s : CdclState) (failed : Nat) (conflict : List Nat) : List Nat :=
  let notFailed := litNeg failed
  match scanFailedConflict s notFailed conflict [] with
  | none => [notFailed]
  | some A =>
    if s.trail.size == 0 then [notFailed]
    else analyzeFailedLoop s notFailed (s.trail.size - 1) A [] none

/-- Exact justification for `analyze.c:447,473` (`assert(other != unit)` / `if (other == unit)`):
since any emitted `unit = NOT(trail[j])` came from `j ≥ t`, while every antecedent `other ≠ lit`
of `lit = trail[t]` has `litNeg other = trail[k]` with `k < t`, `other ≠ unit` unconditionally under
`ReasonDagInv` + `vars_nodup`. -/
theorem failedLit_other_ne_unit {s : CdclState} (hinv : LazyTrailInv s)
    {t j : Nat} (ht : t < s.trail.size) (hj : j < s.trail.size) (htj : t ≤ j)
    {other : Nat}
    (hant : (∃ other0, stateReason s s.trail[t] = .binary other0 ∧ other = other0) ∨
      (∃ cid cl, stateReason s s.trail[t] = .large cid ∧
        s.clauses[cid]? = some (some cl) ∧ other ∈ cl.lits ∧ other ≠ s.trail[t])) :
    other ≠ litNeg s.trail[j] := by
  intro heq
  have hrd := hinv.reason_dag t ht
  dsimp only at hrd
  have hneg_lt : ∃ (k : Nat) (_hk : k < s.trail.size), k < t ∧ s.trail[k] = litNeg other := by
    rcases hant with ⟨other0, hrsn, rfl⟩ | ⟨cid, cl, hrsn, hget, hx, hne⟩
    · rw [hrsn] at hrd
      obtain ⟨_, k, hk, hklt, hkeq, _, _⟩ := hrd
      exact ⟨k, hk, hklt, hkeq⟩
    · rw [hrsn] at hrd
      obtain ⟨c, hgetc, _, _, hall⟩ := hrd
      rw [hget] at hgetc; injection hgetc with h1; injection h1 with hc
      subst hc
      obtain ⟨k, hk, hklt, hkeq, _, _⟩ := hall other hx hne
      exact ⟨k, hk, hklt, hkeq⟩
  obtain ⟨k, hk, hklt, hkeq⟩ := hneg_lt
  have hv : litVar s.trail[k] = litVar s.trail[j] := by
    rw [hkeq, heq, litVar_litNeg, litVar_litNeg]
  have hkj := hinv.vars_nodup k j hk hj hv
  omega

/-- Semantic soundness of `litNeg failed` (`¬failed`) at any level-1 conflict (`analyze.c:499-500`):
holds independently of how many backward resolution steps occur before `DONE`. -/
theorem failedLit_not_failed_sound {s : CdclState} (hinv : LazyTrailInv s)
    (hlvl : s.level = 1) {failed : Nat}
    (hf_trl : failed ∈ s.trail.toList)
    (hf_lvl : stateLevel s failed = 1)
    (hf_dec : stateReason s failed = .decision)
    {conflict : List Nat}
    (hconfl : s.f0.EntailsClause (cnfClause conflict))
    (hfals : ∀ l ∈ conflict, litNeg l ∈ s.trail.toList) :
    s.f0.EntailsClause (cnfClause [litNeg failed]) := by
  have hdec_uniq : ∀ d ∈ decisionsAtMost s 1, d = failed := by
    intro d hd
    rw [mem_decisionsAtMost_iff] at hd
    obtain ⟨id_, hid, hid_eq⟩ := trail_mem_iff_exists.mp hd.1
    obtain ⟨if_, hif, hif_eq⟩ := trail_mem_iff_exists.mp hf_trl
    have hrd := hinv.reason_dag id_ hid
    dsimp only at hrd
    rw [hid_eq, hd.2.1] at hrd
    have hdl : stateLevel s s.trail[id_] = stateLevel s s.trail[if_] := by
      have : stateLevel s s.trail[id_] ≤ 1 := by simpa [hid_eq] using hd.2.2
      rw [hid_eq, hif_eq]; omega
    have h1 := hinv.dec_earliest id_ if_ hid hif hdl (by rw [hif_eq]; exact hf_dec)
    have h2 := hinv.dec_earliest if_ id_ hif hid hdl.symm (by rw [hid_eq]; exact hd.2.1)
    have heq : id_ = if_ := by omega
    subst heq
    rw [← hid_eq, hif_eq]
  rw [CNF.entails_clause_def]
  intro α hα
  rw [sat_cnfClause_litNeg_iff]
  intro hfsat
  have hall_trl : ∀ (i : Nat) (hi : i < s.trail.size), (cnfClause [s.trail[i]]).Sat α := by
    intro i hi
    have hle : stateLevel s s.trail[i] ≤ 1 := by simpa [hlvl] using hinv.levels_le i hi
    have hent := CNF.entails_clause_trans (unitsCnf_decisionsAtMost_mono hle)
      (lazyTrailEntailment hinv i hi)
    apply CNF.entails_clause_def.mp hent α
    rw [CNF.sat_append, sat_unitsCnf_iff]
    refine ⟨hα, fun d hd => ?_⟩
    rw [hdec_uniq d hd]
    exact hfsat
  obtain ⟨l, hlC, hls⟩ :=
    (clause_sat_cnfClause_iff α conflict).mp (CNF.entails_clause_def.mp hconfl α hα)
  obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp (hfals l hlC)
  have htsat := hall_trl i hi
  rw [hieq] at htsat
  exact (sat_cnfClause_litNeg_iff α l).mp htsat ((sat_cnfClause_singleton α l).mpr hls)

private theorem nodup_litVar_any_iff (A : List Nat) (lit : Nat) :
    A.any (fun a => litVar a == litVar lit) = true ↔ ∃ a ∈ A, litVar a = litVar lit := by
  simp [List.any_eq_true, beq_iff_eq]

private theorem scanFailedConflict_props {s : CdclState} (hinv : LazyTrailInv s) {notFailed : Nat} :
    ∀ lits A,
      (∀ a ∈ A, ∃ (i : Nat) (_hi : i < s.trail.size), s.trail[i] = a) →
      (A.map litVar).Nodup →
      s.f0.EntailsClause (cnfClause (A.map litNeg ++ lits)) →
      (∀ l ∈ lits, litNeg l ∈ s.trail.toList) →
      match scanFailedConflict s notFailed lits A with
      | none => True
      | some A' =>
        (∀ a ∈ A', ∃ (i : Nat) (_hi : i < s.trail.size), s.trail[i] = a) ∧
        (A'.map litVar).Nodup ∧
        s.f0.EntailsClause (cnfClause (A'.map litNeg)) := by
  intro lits
  induction lits with
  | nil =>
    intro A hA hnd hent _
    simp only [scanFailedConflict, List.append_nil] at hent ⊢
    exact ⟨hA, hnd, hent⟩
  | cons l ls ih =>
    intro A hA hnd hent hl_trl
    unfold scanFailedConflict
    by_cases hnf : l = notFailed
    · rw [ite_eq_left (beq_iff_eq.mpr hnf)]; trivial
    · rw [ite_eq_right (by simp [beq_false_of_ne hnf])]; dsimp only
      have hl_mem : litNeg l ∈ s.trail.toList := hl_trl l (by simp)
      obtain ⟨il, hil, hil_eq⟩ := trail_mem_iff_exists.mp hl_mem
      by_cases hl0 : stateLevel s l = 0
      · rw [ite_eq_left (beq_iff_eq.mpr hl0)]
        have hl0' : stateLevel s s.trail[il] = 0 := by
          rw [hil_eq, stateLevel_litNeg]; exact hl0
        have hent_l := lazyTrailEntailment_level0 hinv hil hl0'
        rw [hil_eq] at hent_l
        have hent' : s.f0.EntailsClause (cnfClause (A.map litNeg ++ ls)) := by
          rw [CNF.entails_clause_def] at hent hent_l ⊢
          intro α hα
          have hnl := (sat_cnfClause_litNeg_iff α l).mp (hent_l α hα)
          obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (hent α hα)
          refine (clause_sat_cnfClause_iff α _).mpr ⟨y, ?_, hys⟩
          rcases List.mem_append.mp hy with ha | hcons
          · exact List.mem_append_left _ ha
          · rcases List.mem_cons.mp hcons with rfl | hls
            · exact absurd ((sat_cnfClause_singleton α _).mpr hys) hnl
            · exact List.mem_append_right _ hls
        exact ih A hA hnd hent' (fun x hx => hl_trl x (List.mem_cons_of_mem _ hx))
      · rw [ite_eq_right (by simp [beq_false_of_ne hl0])]
        by_cases hany : A.any (fun a => litVar a == litVar (litNeg l)) = true
        · rw [ite_eq_left hany]
          obtain ⟨a, haA, hvar⟩ := (nodup_litVar_any_iff A (litNeg l)).mp hany
          obtain ⟨ia, hia, hia_eq⟩ := hA a haA
          have heq_idx : ia = il := hinv.vars_nodup ia il hia hil
            (by rw [hia_eq, hil_eq, litVar_litNeg, hvar, litVar_litNeg])
          have ha_eq : a = litNeg l := by
            subst heq_idx
            exact hia_eq.symm.trans hil_eq
          have hl_mem_A : l ∈ A.map litNeg :=
            List.mem_map.mpr ⟨a, haA, by rw [ha_eq, litNeg_litNeg]⟩
          have hent' : s.f0.EntailsClause (cnfClause (A.map litNeg ++ ls)) := by
            rw [CNF.entails_clause_def] at hent ⊢
            intro α hα
            obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (hent α hα)
            refine (clause_sat_cnfClause_iff α _).mpr ⟨y, ?_, hys⟩
            rcases List.mem_append.mp hy with ha | hcons
            · exact List.mem_append_left _ ha
            · rcases List.mem_cons.mp hcons with rfl | hls
              · exact List.mem_append_left _ hl_mem_A
              · exact List.mem_append_right _ hls
          exact ih A hA hnd hent' (fun x hx => hl_trl x (List.mem_cons_of_mem _ hx))
        · rw [ite_eq_right hany]
          have hnot_var : litVar (litNeg l) ∉ A.map litVar := by
            intro hm
            obtain ⟨a, haA, hveq⟩ := List.mem_map.mp hm
            exact hany ((nodup_litVar_any_iff A (litNeg l)).mpr ⟨a, haA, hveq⟩)
          have hA1 : ∀ a ∈ litNeg l :: A, ∃ (i : Nat) (_hi : i < s.trail.size), s.trail[i] = a := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | haA
            · exact ⟨il, hil, hil_eq⟩
            · exact hA a haA
          have hnd1 : ((litNeg l :: A).map litVar).Nodup :=
            List.nodup_cons.mpr ⟨hnot_var, hnd⟩
          have hent1 : s.f0.EntailsClause (cnfClause ((litNeg l :: A).map litNeg ++ ls)) := by
            rw [CNF.entails_clause_def] at hent ⊢
            intro α hα
            obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (hent α hα)
            refine (clause_sat_cnfClause_iff α _).mpr ⟨y, ?_, hys⟩
            rcases List.mem_append.mp hy with ha | hcons
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ ha)
            · rcases List.mem_cons.mp hcons with rfl | hls
              · exact List.mem_append_left _ (by simp [litNeg_litNeg])
              · exact List.mem_append_right _ hls
          exact ih (litNeg l :: A) hA1 hnd1 hent1 (fun x hx => hl_trl x (List.mem_cons_of_mem _ hx))

private theorem resolveLargeFailed_props {s : CdclState} (hinv : LazyTrailInv s)
    {t : Nat} (ht : t < s.trail.size) {notFailed : Nat}
    {prevUnit : Option Nat}
    (hpunit : ∀ u, prevUnit = some u →
      ∃ (j : Nat) (_hj : j < s.trail.size), t ≤ j ∧ u = litNeg s.trail[j])
    {cid : Nat} {cl : Clause} (hrsn : stateReason s s.trail[t] = .large cid)
    (hget : s.clauses[cid]? = some (some cl)) :
    ∀ rest A,
      (∀ x ∈ rest, x ≠ s.trail[t] → x ∈ cl.lits) →
      (∀ a ∈ A, ∃ (k : Nat) (_hk : k < t) (_hkt : k < s.trail.size), s.trail[k] = a) →
      (A.map litVar).Nodup →
      (∀ α : Nat → Bool, s.f0.Sat α → ¬ (cnfClause [s.trail[t]]).Sat α →
        (∃ x ∈ rest, x ≠ s.trail[t] ∧ (cnfClause [x]).Sat α) ∨ (cnfClause (A.map litNeg)).Sat α) →
      (∀ α : Nat → Bool, s.f0.Sat α → (cnfClause [s.trail[t]]).Sat α →
        (cnfClause (A.map litNeg)).Sat α) →
      match resolveLargeFailed s s.trail[t] notFailed prevUnit rest A with
      | none => True
      | some A' =>
        (∀ a ∈ A', ∃ (k : Nat) (_hk : k < t) (_hkt : k < s.trail.size), s.trail[k] = a) ∧
        (A'.map litVar).Nodup ∧
        s.f0.EntailsClause (cnfClause (A'.map litNeg)) := by
  intro rest
  induction rest with
  | nil =>
    intro A _ hA hnd hfalse htrue
    simp only [resolveLargeFailed]
    refine ⟨hA, hnd, CNF.entails_clause_def.mpr fun α hα => ?_⟩
    by_cases he : (cnfClause [s.trail[t]]).Sat α
    · exact htrue α hα he
    · rcases hfalse α hα he with ⟨_, hm, _⟩ | hsat
      · cases hm
      · exact hsat
  | cons other rest ih =>
    intro A hmem hA hnd hfalse htrue
    unfold resolveLargeFailed
    by_cases heq_lit : other = s.trail[t]
    · rw [ite_eq_left (beq_iff_eq.mpr heq_lit)]
      refine ih A (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) hA hnd (fun α hα he => ?_)
        htrue
      rcases hfalse α hα he with ⟨x, hx, hxne, hxs⟩ | hsat
      · rcases List.mem_cons.mp hx with rfl | hrest
        · exact absurd heq_lit hxne
        · exact Or.inl ⟨x, hrest, hxne, hxs⟩
      · exact Or.inr hsat
    · rw [ite_eq_right (by simp [beq_false_of_ne heq_lit])]
      have hoth_cl : other ∈ cl.lits := hmem other (by simp) heq_lit
      by_cases hpu : (prevUnit == some other) = true
      · exfalso
        simp only [beq_iff_eq] at hpu
        cases prevUnit with
        | none => simp at hpu
        | some u =>
          injection hpu with hu
          subst hu
          obtain ⟨j, hj, htj, rfl⟩ := hpunit u rfl
          exact failedLit_other_ne_unit hinv ht hj htj
            (Or.inr ⟨cid, cl, hrsn, hget, hoth_cl, heq_lit⟩) rfl
      · rw [ite_eq_right hpu]
        by_cases hnf : other = notFailed
        · rw [ite_eq_left (beq_iff_eq.mpr hnf)]; trivial
        · rw [ite_eq_right (by simp [beq_false_of_ne hnf])]
          have hrd := hinv.reason_dag t ht
          dsimp only at hrd
          rw [hrsn] at hrd
          obtain ⟨c, hgetc, _, _, hall⟩ := hrd
          rw [hget] at hgetc; injection hgetc with h1; injection h1 with hc
          subst hc
          obtain ⟨k, hk, hklt, hkeq, _, _⟩ := hall other hoth_cl heq_lit
          by_cases hl0 : stateLevel s other = 0
          · rw [ite_eq_left (beq_iff_eq.mpr hl0)]
            have hl0' : stateLevel s s.trail[k] = 0 := by
              rw [hkeq, stateLevel_litNeg]; exact hl0
            have hent_o := lazyTrailEntailment_level0 hinv hk hl0'
            rw [hkeq] at hent_o
            refine ih A (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) hA hnd
              (fun α hα he => ?_) htrue
            rcases hfalse α hα he with ⟨x, hx, hxne, hxs⟩ | hsat
            · rcases List.mem_cons.mp hx with hxo | hrest
              · rw [hxo] at hxs
                exact absurd hxs
                  ((sat_cnfClause_litNeg_iff α other).mp (CNF.entails_clause_def.mp hent_o α hα))
              · exact Or.inl ⟨x, hrest, hxne, hxs⟩
            · exact Or.inr hsat
          · rw [ite_eq_right (by simp [beq_false_of_ne hl0])]; dsimp only
            by_cases hany : A.any (fun a => litVar a == litVar (litNeg other)) = true
            · rw [ite_eq_left hany]
              obtain ⟨a, haA, hvar⟩ := (nodup_litVar_any_iff A (litNeg other)).mp hany
              obtain ⟨ka, _, hka, hka_eq⟩ := hA a haA
              have heqk : ka = k := hinv.vars_nodup ka k hka hk
                (by rw [hka_eq, hkeq, litVar_litNeg, hvar, litVar_litNeg])
              have ha_eq : a = litNeg other := by
                subst heqk
                exact hka_eq.symm.trans hkeq
              have hoth_mem : other ∈ A.map litNeg :=
                List.mem_map.mpr ⟨a, haA, by rw [ha_eq, litNeg_litNeg]⟩
              refine ih A (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) hA hnd
                (fun α hα he => ?_) htrue
              rcases hfalse α hα he with ⟨x, hx, hxne, hxs⟩ | hsat
              · rcases List.mem_cons.mp hx with hxo | hrest
                · rw [hxo] at hxs
                  exact Or.inr ((clause_sat_cnfClause_iff α _).mpr
                    ⟨other, hoth_mem, (sat_cnfClause_singleton α other).mp hxs⟩)
                · exact Or.inl ⟨x, hrest, hxne, hxs⟩
              · exact Or.inr hsat
            · rw [ite_eq_right hany]
              have hnot_var : litVar (litNeg other) ∉ A.map litVar := by
                intro hm
                obtain ⟨a, haA, hveq⟩ := List.mem_map.mp hm
                exact hany ((nodup_litVar_any_iff A (litNeg other)).mpr ⟨a, haA, hveq⟩)
              have hA1 : ∀ a ∈ litNeg other :: A,
                  ∃ (k1 : Nat) (_hk1 : k1 < t) (_hk1t : k1 < s.trail.size), s.trail[k1] = a := by
                intro a ha
                rcases List.mem_cons.mp ha with rfl | haA
                · exact ⟨k, hklt, hk, hkeq⟩
                · exact hA a haA
              have hnd1 : ((litNeg other :: A).map litVar).Nodup :=
                List.nodup_cons.mpr ⟨hnot_var, hnd⟩
              refine ih (litNeg other :: A) (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
                hA1 hnd1 (fun α hα he => ?_) (fun α hα he => ?_)
              · rcases hfalse α hα he with ⟨x, hx, hxne, hxs⟩ | hsat
                · rcases List.mem_cons.mp hx with hxo | hrest
                  · rw [hxo] at hxs
                    exact Or.inr ((clause_sat_cnfClause_iff α _).mpr
                      ⟨other, by simp [litNeg_litNeg], (sat_cnfClause_singleton α other).mp hxs⟩)
                  · exact Or.inl ⟨x, hrest, hxne, hxs⟩
                · exact Or.inr ((clause_sat_cnfClause_iff α _).mpr
                    (let ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp hsat
                     ⟨y, List.mem_cons_of_mem _ hy, hys⟩))
              · obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (htrue α hα he)
                exact (clause_sat_cnfClause_iff α _).mpr ⟨y, List.mem_cons_of_mem _ hy, hys⟩

private theorem analyzeFailedLoop_sound {s : CdclState} (hinv : LazyTrailInv s)
    {notFailed : Nat} (hnf_ent : s.f0.EntailsClause (cnfClause [notFailed])) :
    ∀ (t : Nat) (A units : List Nat) (prevUnit : Option Nat),
      (∀ u ∈ units, s.f0.EntailsClause (cnfClause [u])) →
      (∀ u, prevUnit = some u →
        ∃ (j : Nat) (_hj : j < s.trail.size), t < j ∧ u = litNeg s.trail[j]) →
      (∀ a ∈ A, ∃ (k : Nat) (_hk : k ≤ t) (_hkt : k < s.trail.size), s.trail[k] = a) →
      (A.map litVar).Nodup →
      s.f0.EntailsClause (cnfClause (A.map litNeg)) →
      ∀ u ∈ analyzeFailedLoop s notFailed t A units prevUnit,
        s.f0.EntailsClause (cnfClause [u]) := by
  intro t
  induction t with
  | zero =>
    intro A units prevUnit hu_ent hpu hA hnd hent u hu_mem
    unfold analyzeFailedLoop at hu_mem
    cases hget : s.trail[0]? with
    | none =>
      simp only [hget, List.mem_append, List.mem_singleton] at hu_mem
      rcases hu_mem with hu | rfl
      · exact hu_ent u hu
      · exact hnf_ent
    | some lit =>
      rw [hget] at hu_mem; dsimp only at hu_mem
      rw [Array.getElem?_eq_some_iff] at hget
      obtain ⟨ht0, hlit_eq⟩ := hget
      by_cases hany : A.any (fun a => litVar a == litVar lit) = true
      · have hany_f : (!A.any (fun a => litVar a == litVar lit)) = false := by simp [hany]
        rw [ite_eq_right (by simp [hany_f])] at hu_mem
        obtain ⟨a0, ha0, hva0⟩ := (nodup_litVar_any_iff A lit).mp hany
        obtain ⟨k0, hk0_le, hk0_lt, hk0_eq⟩ := hA a0 ha0
        have hk0_z : k0 = 0 := by omega
        subst hk0_z
        have ha0_eq : a0 = lit := by rw [← hk0_eq, hlit_eq]
        have hnil_rest : A.filter (fun a => litVar a != litVar lit) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro x hx
          rw [List.mem_filter] at hx
          obtain ⟨kx, hkx_le, hkx_lt, hkx_eq⟩ := hA x hx.1
          have hkx_z : kx = 0 := by omega
          subst hkx_z
          have hxe : litVar x = litVar lit := by rw [← hkx_eq, hlit_eq]
          simp [hxe] at hx
        have hemit : (A.filter (fun a => litVar a != litVar lit)).isEmpty = true := by
          simp [hnil_rest]
        have hunit_ent : s.f0.EntailsClause (cnfClause [litNeg lit]) := by
          rw [CNF.entails_clause_def] at hent ⊢
          intro α hα
          obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α (A.map litNeg)).mp (hent α hα)
          obtain ⟨x, hxA, rfl⟩ := List.mem_map.mp hy
          obtain ⟨kx, hkx_le, _, hkx_eq⟩ := hA x hxA
          have hkx_z : kx = 0 := by omega
          subst hkx_z
          rw [← hkx_eq, hlit_eq] at hys
          exact (sat_cnfClause_singleton α _).mpr hys
        have hu'_ent : ∀ v ∈ units ++ [litNeg lit], s.f0.EntailsClause (cnfClause [v]) := by
          intro v hv
          rcases List.mem_append.mp hv with hv1 | hv2
          · exact hu_ent v hv1
          · simp only [List.mem_singleton] at hv2; subst hv2; exact hunit_ent
        simp only [hemit, ↓reduceIte] at hu_mem
        cases hrsn : stateReason s lit with
        | decision | unit =>
          rw [hrsn] at hu_mem
          rcases List.mem_append.mp hu_mem with hv1 | hv2
          · exact hu'_ent u hv1
          · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
        | binary other =>
          rw [hrsn] at hu_mem; dsimp only at hu_mem
          split at hu_mem
          · rcases List.mem_append.mp hu_mem with hv1 | hv2
            · exact hu'_ent u hv1
            · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
          · split at hu_mem
            · rcases List.mem_append.mp hu_mem with hv1 | hv2
              · exact hu'_ent u hv1
              · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
            · split at hu_mem <;> rcases List.mem_append.mp hu_mem with hv1 | hv2
              · exact hu'_ent u hv1
              · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
              · exact hu'_ent u hv1
              · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
        | large cid =>
          rw [hrsn] at hu_mem; dsimp only at hu_mem
          cases hgc : s.clauses[cid]? with
          | none =>
            rw [hgc] at hu_mem
            rcases List.mem_append.mp hu_mem with hv1 | hv2
            · exact hu'_ent u hv1
            · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
          | some opt =>
            cases opt with
            | none =>
              rw [hgc] at hu_mem
              rcases List.mem_append.mp hu_mem with hv1 | hv2
              · exact hu'_ent u hv1
              · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
            | some cl =>
              rw [hgc] at hu_mem; dsimp only at hu_mem
              split at hu_mem
              · cases hrl : resolveLargeFailed s lit notFailed (some (litNeg lit)) cl.lits [] with
                | none =>
                  rw [hnil_rest, hrl] at hu_mem
                  rcases List.mem_append.mp hu_mem with hv1 | hv2
                  · exact hu'_ent u hv1
                  · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
                | some A' =>
                  rw [hnil_rest, hrl] at hu_mem
                  rcases List.mem_append.mp hu_mem with hv1 | hv2
                  · exact hu'_ent u hv1
                  · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
              · rcases List.mem_append.mp hu_mem with hv1 | hv2
                · exact hu'_ent u hv1
                · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
      · have hany_t : (!A.any (fun a => litVar a == litVar lit)) = true := by simp [hany]
        rw [ite_eq_left hany_t] at hu_mem
        rcases List.mem_append.mp hu_mem with hv1 | hv2
        · exact hu_ent u hv1
        · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
  | succ t' ih =>
    intro A units prevUnit hu_ent hpu hA hnd hent u hu_mem
    unfold analyzeFailedLoop at hu_mem
    cases hget : s.trail[t' + 1]? with
    | none =>
      rw [hget] at hu_mem
      rcases List.mem_append.mp hu_mem with hv1 | hv2
      · exact hu_ent u hv1
      · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
    | some lit =>
      rw [hget] at hu_mem; dsimp only at hu_mem
      rw [Array.getElem?_eq_some_iff] at hget
      obtain ⟨ht_lt, hlit_eq⟩ := hget
      by_cases hany : A.any (fun a => litVar a == litVar lit) = true
      · have hany_f : (!A.any (fun a => litVar a == litVar lit)) = false := by simp [hany]
        rw [ite_eq_right (by simp [hany_f])] at hu_mem
        let A_rest := A.filter (fun a => litVar a != litVar lit)
        have hA_rest_lt : ∀ a ∈ A_rest,
            ∃ (k : Nat) (_hk : k ≤ t') (_hkt : k < s.trail.size), s.trail[k] = a := by
          intro a ha
          rw [List.mem_filter] at ha
          obtain ⟨k, hk_le, hk_lt, hk_eq⟩ := hA a ha.1
          have hne_k : k ≠ t' + 1 := by
            intro hkt; subst hkt
            have hv : litVar a = litVar lit := by rw [← hk_eq, hlit_eq]
            simp [hv] at ha
          exact ⟨k, by omega, hk_lt, hk_eq⟩
        have hnd_rest : (A_rest.map litVar).Nodup :=
          hnd.sublist (List.filter_sublist.map litVar)
        have hres_lit : ∀ α : Nat → Bool, s.f0.Sat α → (cnfClause [lit]).Sat α →
            (cnfClause (A_rest.map litNeg)).Sat α := by
          intro α hα hev
          obtain ⟨y, hy, hys⟩ :=
            (clause_sat_cnfClause_iff α (A.map litNeg)).mp (CNF.entails_clause_def.mp hent α hα)
          obtain ⟨a, haA, rfl⟩ := List.mem_map.mp hy
          by_cases hvar : litVar a = litVar lit
          · obtain ⟨ka, _, hka, hka_eq⟩ := hA a haA
            have heqk : ka = t' + 1 :=
              hinv.vars_nodup ka (t' + 1) hka ht_lt (by rw [hka_eq, hlit_eq, hvar])
            have ha_eq : a = lit := by
              subst heqk
              exact hka_eq.symm.trans hlit_eq
            have hneg_sat : (cnfClause [litNeg lit]).Sat α := by
              rw [← ha_eq]
              exact (sat_cnfClause_singleton α (litNeg a)).mpr hys
            exact absurd hev ((sat_cnfClause_litNeg_iff α lit).mp hneg_sat)
          · have ha_rest : a ∈ A_rest := List.mem_filter.mpr ⟨haA, by simp [hvar]⟩
            exact (clause_sat_cnfClause_iff α _).mpr
              ⟨litNeg a, List.mem_map.mpr ⟨a, ha_rest, rfl⟩, hys⟩
        let emit := A_rest.isEmpty
        let prevUnit' := if emit then some (litNeg lit) else prevUnit
        let units' := if emit then units ++ [litNeg lit] else units
        have hu'_ent : ∀ v ∈ units', s.f0.EntailsClause (cnfClause [v]) := by
          by_cases he : emit = true
          · simp only [units', he, ↓reduceIte]
            have hA_nil : A_rest = [] := List.isEmpty_iff.mp he
            have hent_u : s.f0.EntailsClause (cnfClause [litNeg lit]) := by
              rw [CNF.entails_clause_def]
              intro α hα
              exact Classical.byContradiction fun hns => by
                have hlit_t : (cnfClause [lit]).Sat α :=
                  Classical.byContradiction fun hn => hns ((sat_cnfClause_litNeg_iff α lit).mpr hn)
                have hs := hres_lit α hα hlit_t
                rw [hA_nil, List.map_nil] at hs
                obtain ⟨_, hm, _⟩ := (clause_sat_cnfClause_iff α []).mp hs
                cases hm
            intro v hv
            rcases List.mem_append.mp hv with hv1 | hv2
            · exact hu_ent v hv1
            · simp only [List.mem_singleton] at hv2; subst hv2; exact hent_u
          · have hef : emit = false := Bool.eq_false_iff.mpr he
            simp only [units', hef, Bool.false_eq_true, ↓reduceIte]
            exact hu_ent
        have hpu' : ∀ v, prevUnit' = some v →
            ∃ (j : Nat) (_hj : j < s.trail.size), t' + 1 ≤ j ∧ v = litNeg s.trail[j] := by
          intro v hv
          by_cases he : emit = true
          · simp only [prevUnit', he, ↓reduceIte, Option.some.injEq] at hv
            exact ⟨t' + 1, ht_lt, Nat.le_refl _, by rw [hlit_eq, hv]⟩
          · have hef : emit = false := Bool.eq_false_iff.mpr he
            simp only [prevUnit', hef, Bool.false_eq_true, ↓reduceIte] at hv
            obtain ⟨j, hj, hltj, rfl⟩ := hpu v hv
            exact ⟨j, hj, by omega, rfl⟩
        have hpu_next : ∀ v, prevUnit' = some v →
            ∃ (j : Nat) (_hj : j < s.trail.size), t' < j ∧ v = litNeg s.trail[j] := by
          intro v hv
          obtain ⟨j, hj, htj, hveq⟩ := hpu' v hv
          exact ⟨j, hj, by omega, hveq⟩
        have hA_rest_t : ∀ a ∈ A_rest,
            ∃ (k : Nat) (_hk : k < t' + 1) (_hkt : k < s.trail.size), s.trail[k] = a := by
          intro a ha
          obtain ⟨k, hkle, hklt, hkeq⟩ := hA_rest_lt a ha
          exact ⟨k, by omega, hklt, hkeq⟩
        have hrd := hinv.reason_dag (t' + 1) ht_lt
        dsimp only at hrd
        rw [hlit_eq] at hrd
        cases hrsn : stateReason s lit with
        | decision | unit =>
          rw [hrsn] at hu_mem; dsimp only at hu_mem
          rcases List.mem_append.mp hu_mem with hv1 | hv2
          · exact hu'_ent u hv1
          · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
        | binary other =>
          rw [hrsn] at hrd hu_mem; dsimp only at hu_mem
          obtain ⟨hbin, k, hk, hklt, hkeq, _, _⟩ := hrd
          by_cases hpu_o : (prevUnit' == some other) = true
          · rw [ite_eq_left hpu_o] at hu_mem
            rcases List.mem_append.mp hu_mem with hv1 | hv2
            · exact hu'_ent u hv1
            · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
          · have hpu_ne :
                ¬ (((if (A.filter (fun a => litVar a != litVar lit)).isEmpty then some (litNeg lit)
                  else prevUnit) == some other) = true) := hpu_o
            rw [ite_eq_right hpu_ne] at hu_mem
            by_cases hnf : (other == notFailed) = true
            · rw [ite_eq_left hnf] at hu_mem
              rcases List.mem_append.mp hu_mem with hv1 | hv2
              · exact hu'_ent u hv1
              · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
            · rw [ite_eq_right hnf] at hu_mem
              have hres_bin : ∀ α : Nat → Bool, s.f0.Sat α → ¬ (cnfClause [lit]).Sat α →
                  (cnfClause [other]).Sat α ∨ (cnfClause (A_rest.map litNeg)).Sat α := by
                intro α hα hfl
                obtain ⟨y, hy, hys⟩ :=
                  (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hbin α hα)
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
                rcases hy with rfl | rfl
                · exact absurd ((sat_cnfClause_singleton α _).mpr hys) hfl
                · exact Or.inl ((sat_cnfClause_singleton α _).mpr hys)
              by_cases hl0 : stateLevel s other = 0
              · rw [ite_eq_left (beq_iff_eq.mpr hl0)] at hu_mem
                have hl0' : stateLevel s s.trail[k] = 0 := by
                  rw [hkeq, stateLevel_litNeg]; exact hl0
                have hent_o := lazyTrailEntailment_level0 hinv hk hl0'
                rw [hkeq] at hent_o
                have hent_next : s.f0.EntailsClause (cnfClause (A_rest.map litNeg)) := by
                  rw [CNF.entails_clause_def]
                  intro α hα
                  by_cases hev : (cnfClause [lit]).Sat α
                  · exact hres_lit α hα hev
                  · rcases hres_bin α hα hev with ho | hs
                    · exact absurd ho
                        ((sat_cnfClause_litNeg_iff α other).mp
                          (CNF.entails_clause_def.mp hent_o α hα))
                    · exact hs
                exact ih A_rest units' prevUnit' hu'_ent hpu_next hA_rest_lt hnd_rest hent_next u
                  hu_mem
              · have hl0b : ¬ ((stateLevel s other == 0) = true) := by simp [hl0]
                rw [ite_eq_right hl0b] at hu_mem
                by_cases hany_o :
                    A_rest.any (fun a => litVar a == litVar (litNeg other)) = true
                · rw [ite_eq_left hany_o] at hu_mem
                  obtain ⟨a, haA, hvar⟩ := (nodup_litVar_any_iff A_rest (litNeg other)).mp hany_o
                  obtain ⟨ka, _, hka, hka_eq⟩ := hA_rest_lt a haA
                  have heqk : ka = k := hinv.vars_nodup ka k hka hk
                    (by rw [hka_eq, hkeq, litVar_litNeg, hvar, litVar_litNeg])
                  have ha_eq : a = litNeg other := by
                    subst heqk
                    exact hka_eq.symm.trans hkeq
                  have hoth_mem : other ∈ A_rest.map litNeg :=
                    List.mem_map.mpr ⟨a, haA, by rw [ha_eq, litNeg_litNeg]⟩
                  have hent_next : s.f0.EntailsClause (cnfClause (A_rest.map litNeg)) := by
                    rw [CNF.entails_clause_def]
                    intro α hα
                    by_cases hev : (cnfClause [lit]).Sat α
                    · exact hres_lit α hα hev
                    · rcases hres_bin α hα hev with ho | hs
                      · exact (clause_sat_cnfClause_iff α _).mpr
                          ⟨other, hoth_mem, (sat_cnfClause_singleton α _).mp ho⟩
                      · exact hs
                  exact ih A_rest units' prevUnit' hu'_ent hpu_next hA_rest_lt hnd_rest hent_next
                    u hu_mem
                · have hany_ne :
                      ¬ ((A.filter (fun a => litVar a != litVar lit)).any
                        (fun a => litVar a == litVar (litNeg other)) = true) := hany_o
                  rw [ite_eq_right hany_ne] at hu_mem
                  have hnot_var : litVar (litNeg other) ∉ A_rest.map litVar := by
                    intro hm
                    obtain ⟨a, haA, hveq⟩ := List.mem_map.mp hm
                    exact hany_o ((nodup_litVar_any_iff A_rest (litNeg other)).mpr ⟨a, haA, hveq⟩)
                  have hA_next : ∀ a ∈ litNeg other :: A_rest,
                      ∃ (k1 : Nat) (_hk1 : k1 ≤ t') (_hk1t : k1 < s.trail.size),
                        s.trail[k1] = a := by
                    intro a ha
                    rcases List.mem_cons.mp ha with rfl | haR
                    · exact ⟨k, by omega, hk, hkeq⟩
                    · exact hA_rest_lt a haR
                  have hnd_next : ((litNeg other :: A_rest).map litVar).Nodup :=
                    List.nodup_cons.mpr ⟨hnot_var, hnd_rest⟩
                  have hent_next :
                      s.f0.EntailsClause (cnfClause ((litNeg other :: A_rest).map litNeg)) := by
                    rw [CNF.entails_clause_def]
                    intro α hα
                    by_cases hev : (cnfClause [lit]).Sat α
                    · obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (hres_lit α hα hev)
                      exact (clause_sat_cnfClause_iff α _).mpr ⟨y, List.mem_cons_of_mem _ hy, hys⟩
                    · rcases hres_bin α hα hev with ho | hs
                      · exact (clause_sat_cnfClause_iff α _).mpr
                          ⟨other, by simp [litNeg_litNeg], (sat_cnfClause_singleton α _).mp ho⟩
                      · obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp hs
                        exact (clause_sat_cnfClause_iff α _).mpr ⟨y, List.mem_cons_of_mem _ hy, hys⟩
                  exact ih (litNeg other :: A_rest) units' prevUnit' hu'_ent hpu_next hA_next
                    hnd_next hent_next u hu_mem
        | large cid =>
          rw [hrsn] at hu_mem; dsimp only at hu_mem
          cases hgc : s.clauses[cid]? with
          | none =>
            rw [hgc] at hu_mem
            rcases List.mem_append.mp hu_mem with hv1 | hv2
            · exact hu'_ent u hv1
            · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
          | some opt =>
            cases opt with
            | none =>
              rw [hgc] at hu_mem
              rcases List.mem_append.mp hu_mem with hv1 | hv2
              · exact hu'_ent u hv1
              · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
            | some cl =>
              rw [hgc] at hu_mem; dsimp only at hu_mem
              by_cases hok : (!cl.garbage && cl.lits.contains lit) = true
              · rw [ite_eq_left hok] at hu_mem
                have hrl_p := resolveLargeFailed_props hinv ht_lt (notFailed := notFailed) hpu'
                  (by rw [hlit_eq]; exact hrsn) hgc cl.lits A_rest
                  (fun x hx _ => hx) hA_rest_t hnd_rest
                  (fun α hα hev => by
                    rw [hlit_eq] at hev
                    obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α cl.lits).mp
                      (CNF.entails_clause_def.mp (hinv.db_sound cid cl hgc) α hα)
                    have hx_sat : (cnfClause [x]).Sat α := (sat_cnfClause_singleton α _).mpr hxs
                    have hxne : x ≠ s.trail[t' + 1] := by
                      intro hxe; rw [hxe] at hx_sat; rw [hlit_eq] at hx_sat; exact hev hx_sat
                    exact Or.inl ⟨x, hx, hxne, hx_sat⟩)
                  (fun α hα hev => by rw [hlit_eq] at hev; exact hres_lit α hα hev)
                rw [hlit_eq] at hrl_p
                cases hrl : resolveLargeFailed s lit notFailed prevUnit' cl.lits A_rest with
                | none =>
                  rw [hrl] at hu_mem
                  rcases List.mem_append.mp hu_mem with hv1 | hv2
                  · exact hu'_ent u hv1
                  · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
                | some A' =>
                  rw [hrl] at hrl_p hu_mem
                  obtain ⟨hA', hnd', hent'⟩ := hrl_p
                  have hA'_le : ∀ a ∈ A',
                      ∃ (k : Nat) (_hk : k ≤ t') (_hkt : k < s.trail.size), s.trail[k] = a := by
                    intro a ha; obtain ⟨k, hk, hkt, hke⟩ := hA' a ha; exact ⟨k, by omega, hkt, hke⟩
                  exact ih A' units' prevUnit' hu'_ent hpu_next hA'_le hnd' hent' u hu_mem
              · rw [ite_eq_right hok] at hu_mem
                rcases List.mem_append.mp hu_mem with hv1 | hv2
                · exact hu'_ent u hv1
                · simp only [List.mem_singleton] at hv2; subst hv2; exact hnf_ent
      · have hany_t : (!A.any (fun a => litVar a == litVar lit)) = true := by simp [hany]
        rw [ite_eq_left hany_t] at hu_mem
        have hA' : ∀ a ∈ A,
            ∃ (k : Nat) (_hk : k ≤ t') (_hkt : k < s.trail.size), s.trail[k] = a := by
          intro a ha
          obtain ⟨k, hk_le, hk_lt, hk_eq⟩ := hA a ha
          have hne_k : k ≠ t' + 1 := by
            intro hkt; subst hkt
            exact hany ((nodup_litVar_any_iff A lit).mpr ⟨a, ha, by rw [← hk_eq, hlit_eq]⟩)
          exact ⟨k, by omega, hk_lt, hk_eq⟩
        have hpu' : ∀ v, prevUnit = some v →
            ∃ (j : Nat) (_hj : j < s.trail.size), t' < j ∧ v = litNeg s.trail[j] := by
          intro v hv; obtain ⟨j, hj, hlt, he⟩ := hpu v hv; exact ⟨j, hj, by omega, he⟩
        exact ih A units prevUnit hu_ent hpu' hA' hnd hent u hu_mem

/-- **End-to-end failed-literal analysis soundness**: every unit literal produced by
`analyzeFailedLiteralExec` (both intermediate `unresolved == 1` units and `litNeg failed`) is
entailed by `F₀`, with `other == unit` (`analyze.c:473`) proved unreachable by
`failedLit_other_ne_unit`. -/
theorem analyzeFailedLiteralExec_sound {s : CdclState} (hinv : LazyTrailInv s)
    (hlvl : s.level = 1) {failed : Nat}
    (hf_trl : failed ∈ s.trail.toList)
    (hf_lvl : stateLevel s failed = 1)
    (hf_dec : stateReason s failed = .decision)
    {conflict : List Nat}
    (hconfl : s.f0.EntailsClause (cnfClause conflict))
    (hfals : ∀ l ∈ conflict, litNeg l ∈ s.trail.toList) :
    ∀ u ∈ analyzeFailedLiteralExec s failed conflict, s.f0.EntailsClause (cnfClause [u]) := by
  have hnf_ent := failedLit_not_failed_sound hinv hlvl hf_trl hf_lvl hf_dec hconfl hfals
  have hscan := scanFailedConflict_props hinv (notFailed := litNeg failed) conflict []
    (fun _ h => by cases h) List.nodup_nil (by simpa using hconfl) hfals
  unfold analyzeFailedLiteralExec
  dsimp only
  cases hs_res : scanFailedConflict s (litNeg failed) conflict [] with
  | none =>
    intro u hu; simp only [List.mem_singleton] at hu; subst hu; exact hnf_ent
  | some A =>
    rw [hs_res] at hscan; dsimp only
    obtain ⟨hA, hnd, hent⟩ := hscan
    by_cases hsz : s.trail.size = 0
    · have hszb : (s.trail.size == 0) = true := beq_iff_eq.mpr hsz
      rw [ite_eq_left hszb]
      intro u hu; simp only [List.mem_singleton] at hu; subst hu; exact hnf_ent
    · have hszb : (s.trail.size == 0) = false := beq_false_of_ne hsz
      rw [ite_eq_right (by simp [hszb])]
      refine analyzeFailedLoop_sound hinv hnf_ent (s.trail.size - 1) A [] none
        (fun _ h => by cases h) (fun _ h => by cases h) (fun a ha => ?_) hnd hent
      obtain ⟨k, hk, hkeq⟩ := hA a ha
      exact ⟨k, by omega, hk, hkeq⟩

end LeanQbe.T.Examples.Kissat
