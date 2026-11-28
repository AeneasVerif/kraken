/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Cdcl
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Trail

/-!
# Soundness Proofs for `Cdcl`

Extracted pure-Lean proofs for `Cdcl` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 5. 1UIP conflict analysis soundness -/

@[simp] theorem stateLevel_litNeg (s : CdclState) (l : Nat) :
    stateLevel s (litNeg l) = stateLevel s l := by simp [stateLevel]

private theorem analyze1UIPAux_inv {s : CdclState} (hinv : TrailInv s) (hlvl_pos : 0 < s.level) :
    ∀ (i : Nat), i ≤ s.trail.size → ∀ (cl : List Nat),
      s.f0.EntailsClause (cnfClause cl) →
      (∀ x ∈ cl, ∃ (j : Nat) (_hj : j < s.trail.size),
        s.trail[j] = litNeg x ∧ (stateLevel s x = s.level → j < i)) →
      let out := analyze1UIPAux s i cl
      s.f0.EntailsClause (cnfClause out) ∧
      (∀ x ∈ out, ∃ (j : Nat) (_hj : j < s.trail.size), s.trail[j] = litNeg x) ∧
      countAtLevel s out s.level ≤ 1 ∧ (cl ≠ [] → out ≠ []) := by
  intro i
  induction i with
  | zero =>
    intro _ cl hent htrl
    simp only [analyze1UIPAux]
    have hnil : (dedupLits cl).filter (fun l => stateLevel s l == s.level) = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
        rw [List.mem_filter] at hx
        obtain ⟨j, _, _, hlt⟩ := htrl x (mem_dedupLits_iff.mp hx.1)
        have h0 := hlt (by simpa using hx.2); omega
    refine ⟨entails_dedupLits hent, fun x hx => ?_, by simp [countAtLevel, hnil], dedupLits_ne_nil⟩
    obtain ⟨j, hj, hjeq, _⟩ := htrl x (mem_dedupLits_iff.mp hx)
    exact ⟨j, hj, hjeq⟩
  | succ i ih =>
    intro hi cl hent htrl
    let cl' := dedupLits cl
    have hnd : cl'.Nodup := nodup_dedupLits cl
    have hent' : s.f0.EntailsClause (cnfClause cl') := entails_dedupLits hent
    have htrl' : ∀ x ∈ cl', ∃ (j : Nat) (_hj : j < s.trail.size),
        s.trail[j] = litNeg x ∧ (stateLevel s x = s.level → j < i + 1) :=
      fun x hx => htrl x (mem_dedupLits_iff.mp hx)
    rw [analyze1UIPAux]; dsimp only
    by_cases hcnt : countAtLevel s cl' s.level ≤ 1
    · rw [ite_eq_left hcnt]
      exact ⟨hent', fun x hx => let ⟨j, hj, heq, _⟩ := htrl' x hx; ⟨j, hj, heq⟩, hcnt,
        fun h => dedupLits_ne_nil h⟩
    · have hi' : i < s.trail.size := by omega
      rw [ite_eq_right hcnt, dite_eq_left hi']
      let p := s.trail[i]
      let np := litNeg p
      by_cases hres : (cl'.contains np && stateLevel s p == s.level) = true
      · rw [ite_eq_left hres]
        simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hres
        have hne_step : ∀ (r : List Nat), resolveOn np cl' r ≠ [] := fun r => by
          obtain ⟨q, hq, _, hqne⟩ := exists_ne_of_filter_gt_one
            (P := fun l => stateLevel s l == s.level) (np := np) hnd
            (by unfold countAtLevel at hcnt; omega)
          exact List.ne_nil_of_mem
            (List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simp [hqne]⟩))
        have hkeep : ∀ x ∈ cl'.filter (· != np), ∃ (j : Nat) (_hj : j < s.trail.size),
            s.trail[j] = litNeg x ∧ (stateLevel s x = s.level → j < i) := by
          intro x hx
          rw [List.mem_filter, bne_iff_ne] at hx
          obtain ⟨j, hj, hjeq, hjlt⟩ := htrl' x hx.1
          refine ⟨j, hj, hjeq, fun hlvl => ?_⟩
          have hji : j ≠ i := by
            rintro rfl
            have hxeq : x = np := by dsimp only [np, p]; rw [hjeq, litNeg_litNeg]
            exact hx.2 hxeq
          have := hjlt hlvl; omega
        have hrd := hinv.reason_dag i hi'; dsimp only at hrd
        generalize hrsn : stateReason s s.trail[i] = rsn; rw [hrsn] at hrd
        cases rsn with
        | decision =>
          have hall_eq : ∀ x ∈ cl', (stateLevel s x == s.level) = true → x = np := by
            intro x hx hxl
            obtain ⟨j, hj, hjeq, hjlt⟩ := htrl' x hx
            have hxl' : stateLevel s x = s.level := by simpa using hxl
            have hleq : stateLevel s s.trail[j] = stateLevel s s.trail[i] := by
              rw [hjeq, stateLevel_litNeg, hxl', hres.2]
            have hle_ij := hinv.dec_earliest j i hj hi' hleq hrsn
            have hj_eq : j = i := by have := hjlt hxl'; omega
            subst hj_eq; dsimp only [np, p]; rw [hjeq, litNeg_litNeg]
          exact absurd (filter_nodup_singleton_le_one hnd hall_eq) hcnt
        | unit =>
          have h0 : stateLevel s s.trail[i] = 0 := hrd.1
          have hpl : stateLevel s p = s.level := hres.2
          dsimp only [p] at hpl; omega
        | binary other =>
          obtain ⟨hbin, j0, hj0, hj0lt, hj0eq, _⟩ := hrd
          refine ih (Nat.le_of_lt hi') _
            (entails_dedupLits (entails_resolve hent' hbin)) (fun x hx => ?_) |>
            fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, fun _ => h4 (dedupLits_ne_nil (hne_step _))⟩
          rcases List.mem_append.mp (mem_dedupLits_iff.mp hx) with hx1 | hx2
          · exact hkeep x hx1
          · rw [List.mem_filter, bne_iff_ne] at hx2
            have hx_eq : x = other := by
              have hnp : litNeg np = p := by simp [np]
              have hmem := hx2.1; rw [hnp] at hx2
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
              exact hmem.elim (fun h => absurd h hx2.2) id
            subst hx_eq
            exact ⟨j0, hj0, hj0eq, fun _ => hj0lt⟩
        | large cid =>
          obtain ⟨c, hget, _, _, hall⟩ := hrd
          dsimp only; rw [hget]; dsimp only
          refine ih (Nat.le_of_lt hi') _
            (entails_dedupLits (entails_resolve hent' (hinv.db_sound cid c hget)))
            (fun x hx => ?_) |>
            fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, fun _ => h4 (dedupLits_ne_nil (hne_step _))⟩
          rcases List.mem_append.mp (mem_dedupLits_iff.mp hx) with hx1 | hx2
          · exact hkeep x hx1
          · rw [List.mem_filter, bne_iff_ne] at hx2
            have hnp : litNeg np = p := by simp [np]
            rw [hnp] at hx2
            obtain ⟨j0, hj0, hj0lt, hj0eq, _⟩ := hall x hx2.1 hx2.2
            exact ⟨j0, hj0, hj0eq, fun _ => hj0lt⟩
      · rw [ite_eq_right hres]
        refine ih (Nat.le_of_lt hi') cl' hent' (fun x hx => ?_) |>
          fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, fun hne => h4 (dedupLits_ne_nil hne)⟩
        obtain ⟨j, hj, hjeq, hjlt⟩ := htrl' x hx
        refine ⟨j, hj, hjeq, fun hlvl => ?_⟩
        have hji : j ≠ i := by
          rintro rfl
          have hnp_eq : x = np := by dsimp only [np, p]; rw [hjeq, litNeg_litNeg]
          have hnp_mem : np ∈ cl' := hnp_eq ▸ hx
          have hpl : stateLevel s p = s.level := by
            simpa [show stateLevel s p = stateLevel s x from by
              dsimp only [p]; rw [hjeq, stateLevel_litNeg]] using hlvl
          exact hres (by simp [hnp_mem, hpl])
        have := hjlt hlvl; omega

/-- Soundness of 1UIP conflict analysis: the learned clause is entailed by `s.f0`, all literals
are falsified on `s.trail`, at most one literal is at `s.level` when `0 < s.level`, and it is
non-empty unless `s.level = 0` or `confl = []`. -/
theorem analyze1UIP_sound {s : CdclState} (hinv : TrailInv s) {confl : List Nat}
    (hconfl : s.f0.EntailsClause (cnfClause confl))
    (hfals : ∀ l ∈ confl, litNeg l ∈ s.trail.toList) :
    s.f0.EntailsClause (cnfClause (analyze1UIP s confl)) ∧
    (∀ x ∈ analyze1UIP s confl, litNeg x ∈ s.trail.toList) ∧
    (0 < s.level → countAtLevel s (analyze1UIP s confl) s.level ≤ 1 ∧
      (confl ≠ [] → analyze1UIP s confl ≠ [])) ∧
    (s.level = 0 → analyze1UIP s confl = [] ∧ s.f0.Unsat) := by
  by_cases hl0 : s.level = 0
  · have hunsat := unsat_of_conflict hinv hl0 hconfl hfals
    have heq : analyze1UIP s confl = [] := by simp [analyze1UIP, hl0]
    refine ⟨?_, by simp [heq], fun h => by omega, fun _ => ⟨heq, hunsat⟩⟩
    rw [heq, cnfClause_nil]
    exact CNF.entails_clause_def.mpr fun α hα => absurd hα (CNF.unsat_iff_not_sat.mp hunsat α)
  · have hlpos : 0 < s.level := Nat.pos_of_ne_zero hl0
    have hl0f : (s.level == 0) = false := beq_false_of_ne hl0
    have hinit : ∀ x ∈ dedupLits confl, ∃ (j : Nat) (_hj : j < s.trail.size),
        s.trail[j] = litNeg x ∧ (stateLevel s x = s.level → j < s.trail.size) := fun x hx =>
      let ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp (hfals x (mem_dedupLits_iff.mp hx))
      ⟨j, hj, hjeq, fun _ => hj⟩
    have haux := analyze1UIPAux_inv hinv hlpos s.trail.size (Nat.le_refl _) (dedupLits confl)
      (entails_dedupLits hconfl) hinit
    have heq : analyze1UIP s confl = analyze1UIPAux s s.trail.size (dedupLits confl) := by
      simp [analyze1UIP, hl0f]
    rw [← heq] at haux
    exact ⟨haux.1, fun x hx => let ⟨j, hj, heq⟩ := haux.2.1 x hx;
      trail_mem_iff_exists.mpr ⟨j, hj, heq⟩,
      fun _ => ⟨haux.2.2.1, fun hne => haux.2.2.2 (dedupLits_ne_nil hne)⟩,
      fun h => absurd h hl0⟩

/-- Backtracking and adding an entailed learned clause preserves `TrailInv` and `f0`. -/
theorem backtrack_learn_preserves_inv {s : CdclState} (hinv : TrailInv s) (blevel : Nat)
    {learned : List Nat} {glue : Nat} (hent : s.f0.EntailsClause (cnfClause learned)) :
    let s' := addLearnedClause (backtrackTo s blevel) learned glue
    TrailInv s' ∧ s'.f0 = s.f0 := by
  have hb := backtrackTo_inv hinv blevel
  have ha := addLearnedClause_inv hb.1 (lits := learned) (glue := glue) (hb.2 ▸ hent)
  exact ⟨ha.1, ha.2.trans hb.2⟩

/-! ## 6. Failed-literal probing soundness -/

/-- Failed-literal probing soundness: propagating decision `l` at level `1` to conflict entails
`s.f0 ⊨ ¬l`. -/
theorem failedLit_sound {fuel : Nat} {s s2 : CdclState} {l : Nat} {confl : List Nat}
    (hinv : TrailInv s) (hl0 : s.level = 0) (hun : litStatus s.trail l = none)
    (hprop : propagateAll fuel (decideLit s l) = .conflict confl s2) :
    s.f0.EntailsClause (cnfClause [litNeg l]) := by
  have hdec := decideLit_inv hinv hun
  have hpi := propagateAll_inv (fuel := fuel) hdec.1
  rw [hprop] at hpi
  obtain ⟨hinv2, hf02, hlvl2, hconfl2, hfals2, hdam2⟩ := hpi
  have hlvl1 : (decideLit s l).level = 1 := by simp [decideLit, hl0]
  have hf0eq : s2.f0 = s.f0 := hf02.trans hdec.2
  have hdam_eq : ∀ d ∈ decisionsAtMost s2 1, d = l := by
    intro d hd
    have hdam1 := hdam2 1
    rw [hdam1, mem_decisionsAtMost_iff] at hd
    have hvar : ∀ (i : Nat) (hi : i < s.trail.size),
        stateReason (decideLit s l) s.trail[i] ≠ .decision := fun i hi hrsn => by
      have hnv := litStatus_none_no_var hun _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
      simp only [decideLit, stateReason_assignLit] at hrsn
      have hnv' : litVar s.trail[i] ≠ litVar l := hnv
      have hsr : stateReason s s.trail[i] = .decision := by
        simpa [hnv', stateReason] using hrsn
      have hrd := hinv.reason_dag i hi; dsimp only at hrd; rw [hsr] at hrd
      have hle := hinv.levels_le i hi; omega
    obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp hd.1
    simp only [decideLit, trail_assignLit, Array.size_push] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · simp only [decideLit, trail_assignLit, Array.getElem_push_lt hj'] at hjeq
      exact absurd (hjeq ▸ hd.2.1) (hvar j hj')
    · simp only [decideLit, trail_assignLit, Array.getElem_push_eq] at hjeq
      exact hjeq.symm
  rw [CNF.entails_clause_def]
  intro α hα
  exact Classical.byContradiction fun hnot => by
    have hlsat : (cnfClause [l]).Sat α := Classical.byContradiction fun hn =>
      hnot ((sat_cnfClause_litNeg_iff α l).mpr hn)
    have husat : (unitsCnf (decisionsAtMost s2 1)).Sat α :=
      (sat_unitsCnf_iff α _).mpr fun d hd => (hdam_eq d hd) ▸ hlsat
    have hboth : (s2.f0 ++ unitsCnf (decisionsAtMost s2 1)).Sat α :=
      CNF.sat_append.mpr ⟨hf0eq ▸ hα, husat⟩
    obtain ⟨x, hx, hxsat⟩ := (clause_sat_cnfClause_iff α confl).mp
      (CNF.entails_clause_def.mp hconfl2 α (hf0eq ▸ hα))
    obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp (hfals2 x hx)
    have hle1 : stateLevel s2 s2.trail[j] ≤ 1 := by
      have := hinv2.levels_le j hj; omega
    have hent_x := trailEntailment_le hinv2 hj hle1
    rw [hjeq] at hent_x
    exact (sat_cnfClause_litNeg_iff α x).mp (CNF.entails_clause_def.mp hent_x α hboth)
      ((sat_cnfClause_singleton α x).mpr hxsat)

/-- Failed-literal probing step preserves `TrailInv` and `f0`. -/
theorem failedLitStep_preserves_inv {fuel : Nat} {s : CdclState} (hinv : TrailInv s) (l : Nat) :
    match failedLitStep fuel s l with
    | .normal s' | .conflict s' => TrailInv s' ∧ s'.f0 = s.f0
    | .learnedUnit u s' =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.f0.EntailsClause (cnfClause [u]) ∧
      s.level = 0 ∧ litStatus s'.trail u = some true := by
  unfold failedLitStep
  by_cases hl0 : s.level = 0
  · have hl0f : (s.level != 0) = false := by simp [hl0]
    simp only [hl0f, Bool.false_eq_true, ↓reduceIte]
    cases hun : litStatus s.trail l with
    | some b => cases b <;> exact ⟨hinv, rfl⟩
    | none =>
      dsimp only
      cases hprop : propagateAll fuel (decideLit s l) with
      | ok _ | outOfFuel _ => exact ⟨hinv, rfl⟩
      | conflict confl s2 =>
        dsimp only
        have hent := failedLit_sound hinv hl0 hun hprop
        have hun_neg : litStatus s.trail (litNeg l) = none := by
          rw [litStatus_eq_none] at hun ⊢; simpa [litNeg_litNeg] using hun.symm
        have hpush := addRootUnit_inv hinv hl0 hun_neg hent
        have htr : litStatus (assignLit { s with units := litNeg l :: s.units }
            (litNeg l) 0 .unit).trail (litNeg l) = some true :=
          litStatus_eq_some_true.mpr (by simp [assignLit])
        exact ⟨hpush.1, hpush.2, hpush.2 ▸ hent, hl0, htr⟩
  · have hl0t : (s.level != 0) = true := by simp [hl0]
    rw [ite_eq_left hl0t]; exact ⟨hinv, rfl⟩

/-! ## 7. Lexicographic `(level, trailIdx)` `RemovableInv` minimization cut -/

theorem removable_sound {s : CdclState} (hinv : TrailInv s) {K : List Nat} {α : Nat → Bool}
    (hα : s.f0.Sat α) (hK : ∀ k ∈ K, ¬ (cnfClause [k]).Sat α) {l : Nat}
    (hrem : Removable s K l) : ¬ (cnfClause [l]).Sat α := by
  induction hrem with
  | in_keep _ hk => exact hK _ hk
  | root0 l hmem hl0 =>
    obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hmem
    have hli : stateLevel s s.trail[i] = 0 := by simpa [hieq, stateLevel] using hl0
    have hent := trailEntailment_level0 hinv hi hli; rw [hieq] at hent
    exact (sat_cnfClause_litNeg_iff α l).mp (CNF.entails_clause_def.mp hent α hα)
  | binary l other hmem hrsn _ ih =>
    obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hmem
    have hrd := hinv.reason_dag i hi; dsimp only at hrd
    have hrsni : stateReason s s.trail[i] = .binary other := by
      simpa [hieq, stateReason] using hrsn
    rw [hrsni] at hrd; rw [hieq] at hrd
    obtain ⟨y, hy, hysat⟩ :=
      (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hrd.1 α hα)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | hyeq
    · exact (sat_cnfClause_litNeg_iff α l).mp ((sat_cnfClause_singleton α _).mpr hysat)
    · rw [hyeq] at hysat
      exact absurd ((sat_cnfClause_singleton α other).mpr hysat) ih
  | large l _ cl hmem _ hget _ _ ih =>
    obtain ⟨x, hx, hxsat⟩ := (clause_sat_cnfClause_iff α _).mp
      (CNF.entails_clause_def.mp (hinv.db_sound _ _ hget) α hα)
    by_cases hxeq : x = litNeg l
    · rw [hxeq] at hxsat
      exact (sat_cnfClause_litNeg_iff α l).mp ((sat_cnfClause_singleton α (litNeg l)).mpr hxsat)
    · exact absurd ((sat_cnfClause_singleton α x).mpr hxsat) (ih x hx hxeq)

/-- Abstract `RemovableInv` minimization cut theorem. -/
theorem minimizeCut_sound_of_removable {s : CdclState} (hinv : TrailInv s) {c K : List Nat}
    (hc : s.f0.EntailsClause (cnfClause c)) (hcut : RemovableInv s c K) :
    s.f0.EntailsClause (cnfClause K) := by
  rw [CNF.entails_clause_def]
  intro α hα
  exact Classical.byContradiction fun hnot => by
    have hK : ∀ k ∈ K, ¬ (cnfClause [k]).Sat α := fun k hk hks =>
      hnot ((clause_sat_cnfClause_iff α K).mpr ⟨k, hk, (sat_cnfClause_singleton α k).mp hks⟩)
    obtain ⟨l, hl, hlsat⟩ := (clause_sat_cnfClause_iff α c).mp (CNF.entails_clause_def.mp hc α hα)
    have hls : (cnfClause [l]).Sat α := (sat_cnfClause_singleton α l).mpr hlsat
    by_cases hlK : l ∈ K
    · exact hK l hlK hls
    · exact removable_sound hinv hα hK (hcut l hl hlK) hls

private theorem trailIdxOf?_getD_lt {arr : Array Nat} {x : Nat} :
    (trailIdxOf? arr x).getD arr.size ≤ arr.size := by
  cases h : trailIdxOf? arr x with
  | none => simp
  | some i =>
    have hlt := (Array.findIdx?_eq_some_iff_findIdx_eq.mp h).1
    simp [Nat.le_of_lt hlt]

theorem lexLtBool_sound {s : CdclState} {l1 l2 : Nat}
    (h : lexLtBool s l1 l2 = true) : lexMeasure s l1 < lexMeasure s l2 := by
  unfold lexLtBool at h; unfold lexMeasure
  dsimp only at h ⊢
  by_cases h12 : stateLevel s l1 < stateLevel s l2
  · have hle1 : (trailIdxOf? s.trail (litNeg l1)).getD s.trail.size ≤ s.trail.size :=
      trailIdxOf?_getD_lt
    have hmul : (stateLevel s l1 + 1) * (s.trail.size + 1) ≤ stateLevel s l2 * (s.trail.size + 1) :=
      Nat.mul_le_mul_right _ h12
    have hsucc : (stateLevel s l1 + 1) * (s.trail.size + 1) =
        stateLevel s l1 * (s.trail.size + 1) + (s.trail.size + 1) := Nat.succ_mul _ _
    omega
  · simp only [ite_eq_right h12] at h
    by_cases heq : stateLevel s l1 = stateLevel s l2
    · have heqb : (stateLevel s l1 == stateLevel s l2) = true := by simp [heq]
      simp only [heqb, ↓reduceIte] at h
      cases ht1 : trailIdxOf? s.trail (litNeg l1) <;>
        cases ht2 : trailIdxOf? s.trail (litNeg l2) <;> simp [ht1, ht2] at h
      simp only [Option.getD_some, heq]; omega
    · have heqf : (stateLevel s l1 == stateLevel s l2) = false := beq_false_of_ne heq
      simp [heqf] at h

private theorem litMinSubAux_removable {s : CdclState} {c K : List Nat} {rootLit : Nat}
    (hsmaller : ∀ y ∈ c, lexLtBool s y rootLit = true → Removable s K y) :
    ∀ fuel curr allowSelf,
      litMinSubAux s c rootLit fuel curr allowSelf = true → Removable s K curr := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; simp [litMinSubAux] at h
  | succ fuel ih =>
    intro curr allowSelf h
    simp only [litMinSubAux] at h
    by_cases htrl : trailHasLit s.trail (litNeg curr) = true
    · have htrl_neg : (!trailHasLit s.trail (litNeg curr)) = false := by simp [htrl]
      have hmem : litNeg curr ∈ s.trail.toList := trailHasLit_iff.mp htrl
      simp only [htrl_neg, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hl0 : stateLevel s curr = 0
      · exact .root0 curr hmem hl0
      · have hl0f : (stateLevel s curr == 0) = false := beq_false_of_ne hl0
        simp only [hl0f, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hsub : (allowSelf && c.contains curr && lexLtBool s curr rootLit) = true
        · simp only [Bool.and_eq_true, List.contains_iff_mem] at hsub
          exact hsmaller curr hsub.1.2 hsub.2
        · have hsubf : (allowSelf && c.contains curr && lexLtBool s curr rootLit) = false :=
            Bool.eq_false_iff.mpr hsub
          simp only [hsubf, Bool.false_eq_true, ↓reduceIte] at h
          cases hrsn : stateReason s curr with
          | decision => rw [hrsn] at h; simp at h
          | unit => rw [hrsn] at h; simp at h
          | binary other =>
            rw [hrsn] at h; simp only [Bool.and_eq_true] at h
            exact .binary curr other hmem hrsn (ih other true h.2)
          | large cid =>
            rw [hrsn] at h; dsimp only at h
            cases hget : s.clauses[cid]? with
            | none => rw [hget] at h; simp at h
            | some opt =>
              cases opt with
              | none => rw [hget] at h; simp at h
              | some cl =>
                rw [hget] at h
                simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
                  Bool.or_eq_true, beq_iff_eq] at h
                exact .large curr cid cl hmem hrsn hget h.1.2 fun x hx hne =>
                  ih x true (((h.2 x hx).resolve_left hne).2)
    · have htrl_pos : (!trailHasLit s.trail (litNeg curr)) = true := by simp [htrl]
      simp [htrl_pos] at h

theorem minimizeClause_removableInv {s : CdclState} {c : List Nat} :
    RemovableInv s c (minimizeClause s c) := by
  have hstrong : ∀ (m : Nat) (l : Nat), l ∈ c → lexMeasure s l = m →
      Removable s (minimizeClause s c) l := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro l hl hmeas
      by_cases hmin : isMinimizable s c l = true
      · have hsmaller : ∀ y ∈ c, lexLtBool s y l = true → Removable s (minimizeClause s c) y :=
          fun y hy hlt => ih (lexMeasure s y) (hmeas ▸ lexLtBool_sound hlt) y hy rfl
        exact litMinSubAux_removable hsmaller _ l false hmin
      · exact .in_keep l (List.mem_filter.mpr ⟨hl, by simp [Bool.eq_false_iff.mpr hmin]⟩)
  intro l hl _; exact hstrong (lexMeasure s l) l hl rfl

/-- Executable `minimizeClause` soundness (`minimizeCut_sound`). -/
theorem minimizeCut_sound {s : CdclState} (hinv : TrailInv s) {c : List Nat}
    (hc : s.f0.EntailsClause (cnfClause c)) :
    s.f0.EntailsClause (cnfClause (minimizeClause s c)) :=
  minimizeCut_sound_of_removable hinv hc minimizeClause_removableInv

/-! ## 8. Clause relocation (`RefMap`), garbage collection, and deletion soundness -/

private def collectStep (acc : Array (Option Clause)) (rmap : RefMap)
    (opt : Option Clause) : Array (Option Clause) × RefMap :=
  match opt with
  | some c =>
    if c.garbage then (acc, rmap.push none)
    else (acc.push (some c), rmap.push (some acc.size))
  | none => (acc, rmap.push none)

private structure CollectAccInv (f0 : CNF Nat)
    (acc : Array (Option Clause)) (rmap : RefMap) : Prop where
  bound : ∀ (k nid : Nat), rmap[k]? = some (some nid) → nid < acc.size
  inj : ∀ (i j nid : Nat), rmap[i]? = some (some nid) → rmap[j]? = some (some nid) → i = j
  sound : ∀ (k : Nat) (c : Clause), acc[k]? = some (some c) → f0.EntailsClause (cnfClause c.lits)

private theorem collectStep_preserves {f0 : CNF Nat} {acc : Array (Option Clause)}
    {rmap : RefMap} {opt : Option Clause}
    (hinv : CollectAccInv f0 acc rmap)
    (hopt : ∀ (c : Clause), opt = some c → f0.EntailsClause (cnfClause c.lits)) :
    let res := collectStep acc rmap opt
    CollectAccInv f0 res.1 res.2 ∧
    res.2.size = rmap.size + 1 ∧ acc.size ≤ res.1.size ∧
    (∀ (k : Nat), k < rmap.size → res.2[k]? = rmap[k]?) ∧
    (∀ (k : Nat), k < acc.size → res.1[k]? = acc[k]?) ∧
    (∀ (c : Clause), opt = some c → !c.garbage = true →
      ∃ nid < res.1.size, res.2[rmap.size]? = some (some nid) ∧ res.1[nid]? = some (some c)) := by
  cases opt with
  | none =>
    refine ⟨⟨fun k nid hk => ?_, fun i j nid hi hj => ?_, hinv.sound⟩,
      by simp [collectStep], by simp [collectStep], fun k hk => ?_, fun _ _ => rfl,
      fun _ h => by cases h⟩
    · simp only [collectStep, Array.getElem?_push] at hk
      split at hk
      · cases hk
      · exact hinv.bound k nid hk
    · simp only [collectStep, Array.getElem?_push] at hi hj
      split at hi <;> split at hj <;> first | cases hi | cases hj | exact hinv.inj i j nid hi hj
    · simp [collectStep, Array.getElem?_push, Nat.ne_of_lt hk]
  | some c =>
    by_cases hg : c.garbage = true
    · simp only [collectStep, hg, ↓reduceIte]
      refine ⟨⟨fun k nid hk => ?_, fun i j nid hi hj => ?_, hinv.sound⟩,
        by simp, Nat.le_refl _, fun k hk => ?_,
        fun _ _ => trivial, fun d h heq => by cases h; simp [hg] at heq⟩
      · simp only [Array.getElem?_push] at hk
        split at hk
        · cases hk
        · exact hinv.bound k nid hk
      · simp only [Array.getElem?_push] at hi hj
        split at hi <;> split at hj <;> first | cases hi | cases hj | exact hinv.inj i j nid hi hj
      · simp [Array.getElem?_push, Nat.ne_of_lt hk]
    · have hgf : c.garbage = false := Bool.eq_false_iff.mpr hg
      simp only [collectStep, hgf, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨fun k nid hk => ?_, fun i j nid hi hj => ?_, fun k d hk => ?_⟩,
        by simp, by simp, fun k hk => ?_, fun k hk => ?_, fun d h _ => ?_⟩
      · simp only [Array.getElem?_push] at hk
        split at hk
        · simp at hk; subst hk; rw [Array.size_push]; exact Nat.lt_succ_self _
        · rw [Array.size_push]; exact Nat.lt_succ_of_lt (hinv.bound k nid hk)
      · simp only [Array.getElem?_push] at hi hj
        split at hi <;> split at hj
        · simp_all
        · simp only [Option.some.injEq] at hi; subst hi
          exact absurd (hinv.bound j acc.size hj) (Nat.lt_irrefl _)
        · simp only [Option.some.injEq] at hj; subst hj
          exact absurd (hinv.bound i acc.size hi) (Nat.lt_irrefl _)
        · exact hinv.inj i j nid hi hj
      · simp only [Array.getElem?_push] at hk
        split at hk
        · simp only [Option.some.injEq] at hk; subst hk; exact hopt c rfl
        · exact hinv.sound k d hk
      · simp [Array.getElem?_push, Nat.ne_of_lt hk]
      · simp [Array.getElem?_push, Nat.ne_of_lt hk]
      · cases h; exact ⟨acc.size, by simp, by simp, by simp⟩

private theorem collectStep_mono (acc : Array (Option Clause)) (rmap : RefMap)
    (opt : Option Clause) :
    let res := collectStep acc rmap opt
    rmap.size ≤ res.2.size ∧ acc.size ≤ res.1.size ∧
    (∀ k, k < rmap.size → res.2[k]? = rmap[k]?) ∧
    (∀ k, k < acc.size → res.1[k]? = acc[k]?) := by
  cases opt with
  | none =>
    simp only [collectStep]
    refine ⟨by simp, Nat.le_refl _, fun k hk => ?_, fun _ _ => trivial⟩
    simp [Array.getElem?_push, Nat.ne_of_lt hk]
  | some c =>
    by_cases hg : c.garbage = true
    · simp only [collectStep, hg, ↓reduceIte]
      refine ⟨by simp, Nat.le_refl _, fun k hk => ?_, fun _ _ => trivial⟩
      simp [Array.getElem?_push, Nat.ne_of_lt hk]
    · have hgf : c.garbage = false := Bool.eq_false_iff.mpr hg
      simp only [collectStep, hgf, Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp, by simp, fun k hk => ?_, fun k hk => ?_⟩ <;>
        simp [Array.getElem?_push, Nat.ne_of_lt hk]

private theorem collectClauses_foldl_mono (xs : List (Option Clause)) :
    ∀ (acc : Array (Option Clause)) (rmap : RefMap),
      let res := xs.foldl (fun (p : Array (Option Clause) × RefMap) opt =>
        collectStep p.1 p.2 opt) (acc, rmap)
      rmap.size ≤ res.2.size ∧ acc.size ≤ res.1.size ∧
      (∀ k, k < rmap.size → res.2[k]? = rmap[k]?) ∧
      (∀ k, k < acc.size → res.1[k]? = acc[k]?) := by
  induction xs with
  | nil => intro acc rmap; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x xs ih =>
    intro acc rmap
    have hm := collectStep_mono acc rmap x
    have ih' := ih (collectStep acc rmap x).1 (collectStep acc rmap x).2
    refine ⟨Nat.le_trans hm.1 ih'.1, Nat.le_trans hm.2.1 ih'.2.1, fun k hk => ?_, fun k hk => ?_⟩
    · rw [List.foldl_cons]; exact (ih'.2.2.1 k (Nat.lt_of_lt_of_le hk hm.1)).trans (hm.2.2.1 k hk)
    · rw [List.foldl_cons]; exact (ih'.2.2.2 k (Nat.lt_of_lt_of_le hk hm.2.1)).trans (hm.2.2.2 k hk)

private theorem collectClauses_foldl_inv {f0 : CNF Nat} (xs : List (Option Clause)) :
    ∀ (acc : Array (Option Clause)) (rmap : RefMap),
      CollectAccInv f0 acc rmap →
      (∀ (idx : Nat) (c : Clause), xs[idx]? = some (some c) → f0.EntailsClause (cnfClause c.lits)) →
      let res := xs.foldl (fun (p : Array (Option Clause) × RefMap) opt =>
        collectStep p.1 p.2 opt) (acc, rmap)
      CollectAccInv f0 res.1 res.2 ∧
      (∀ (idx : Nat) (c : Clause), xs[idx]? = some (some c) → !c.garbage = true →
        ∃ nid, res.2[rmap.size + idx]? = some (some nid) ∧ res.1[nid]? = some (some c)) := by
  induction xs with
  | nil => intro acc rmap hinv _; exact ⟨hinv, fun idx _ h => by simp at h⟩
  | cons x xs ih =>
    intro acc rmap hinv hxs
    have hx_ok : ∀ (c : Clause), x = some c → f0.EntailsClause (cnfClause c.lits) :=
      fun c hc => hxs 0 c (by simp [hc])
    have hstep := collectStep_preserves hinv hx_ok
    have ih_res := ih (collectStep acc rmap x).1 (collectStep acc rmap x).2 hstep.1
      (fun idx c hc => hxs (idx + 1) c (by simpa using hc))
    have hmono := collectClauses_foldl_mono xs (collectStep acc rmap x).1 (collectStep acc rmap x).2
    refine ⟨ih_res.1, fun idx c hget hng => ?_⟩
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      obtain ⟨nid, hnlt, hrm, hacc⟩ := hstep.2.2.2.2.2 c hget hng
      refine ⟨nid, ?_, ?_⟩
      · simp only [List.foldl_cons, Nat.add_zero]
        exact (hmono.2.2.1 rmap.size (by omega)).trans hrm
      · simp only [List.foldl_cons]
        exact (hmono.2.2.2 nid hnlt).trans hacc
    | succ k =>
      simp only [List.getElem?_cons_succ] at hget
      obtain ⟨nid, hrm, hacc⟩ := ih_res.2 k c hget hng
      refine ⟨nid, ?_, hacc⟩
      simp only [List.foldl_cons]
      rwa [hstep.2.1, Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc] at hrm

@[simp] theorem RefMap.lookup_eq_some_iff (rmap : RefMap) (cid nid : Nat) :
    rmap.lookup cid = some nid ↔ rmap[cid]? = some (some nid) := by
  unfold RefMap.lookup; cases rmap[cid]? <;> simp

theorem collectClauses_sound {clauses : Array (Option Clause)} {f0 : CNF Nat}
    (hsound : ∀ (cid : Nat) (c : Clause), clauses[cid]? = some (some c) →
      f0.EntailsClause (cnfClause c.lits)) :
    RefMapSound clauses (collectClauses clauses).1 (collectClauses clauses).2 f0 := by
  have hinit : CollectAccInv f0 #[] #[] :=
    ⟨fun k _ hk => by simp at hk, fun i _ _ hi => by simp at hi, fun k _ hk => by simp at hk⟩
  have hfold := collectClauses_foldl_inv clauses.toList #[] #[] hinit
    (fun idx c hc => hsound idx c (by simpa [Array.getElem?_toList] using hc))
  have heq : collectClauses clauses = clauses.toList.foldl
      (fun (p : Array (Option Clause) × RefMap) opt => collectStep p.1 p.2 opt) (#[], #[]) := by
    rw [collectClauses, ← Array.foldl_toList]
    rfl
  rw [heq]
  refine ⟨fun i j nid hi hj => ?_, fun cid c hget hng => ?_, hfold.1.sound⟩
  · exact hfold.1.inj i j nid ((RefMap.lookup_eq_some_iff _ _ _).mp hi)
      ((RefMap.lookup_eq_some_iff _ _ _).mp hj)
  · obtain ⟨nid, hrm, hacc⟩ := hfold.2 cid c (by simpa [Array.getElem?_toList] using hget) hng
    exact ⟨nid, (RefMap.lookup_eq_some_iff _ _ _).mpr (by simpa using hrm), hacc⟩

theorem stateReason_map {s : CdclState} {cls : Array (Option Clause)} {f : Reason → Reason}
    (hf : f .unit = .unit) (x : Nat) :
    stateReason { s with clauses := cls, reasons := s.reasons.map f } x = f (stateReason s x) := by
  simp only [stateReason, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases s.reasons[litVar x]? <;> simp [hf]

theorem remapReason_eq_decision {rmap : RefMap} {r : Reason} :
    remapReason rmap r = .decision ↔ r = .decision := by
  cases r <;> simp [remapReason]
  split <;> simp

theorem collect_preserves_lazyInv {s : CdclState} (hinv : LazyTrailInv s) :
    let (s', rmap) := collect s
    LazyTrailInv s' ∧ s'.f0 = s.f0 ∧ RefMapSound s.clauses s'.clauses rmap s.f0 := by
  have hrs := collectClauses_sound hinv.db_sound
  let rmap := (collectClauses s.clauses).2
  let s' : CdclState :=
    { s with
      clauses := (collectClauses s.clauses).1
      reasons := s.reasons.map (remapReason rmap) }
  change LazyTrailInv s' ∧ s'.f0 = s.f0 ∧ RefMapSound s.clauses s'.clauses rmap s.f0
  refine ⟨⟨hinv.vars_nodup, hinv.levels_le, ?_, hrs.2.2,
    hinv.units_sound, ?_, hinv.inconsistent_sound⟩, rfl, hrs⟩
  · intro i j hi hj hleq hrsn_j
    have hsr : stateReason s' s'.trail[j] = remapReason rmap (stateReason s s.trail[j]) :=
      stateReason_map (by rfl) _
    rw [hsr, remapReason_eq_decision] at hrsn_j
    exact hinv.dec_earliest i j hi hj hleq hrsn_j
  · intro i hi
    have hrd := hinv.reason_dag i hi; dsimp only at hrd
    have htr : s'.trail = s.trail := rfl
    have hf0 : s'.f0 = s.f0 := rfl
    have hsl : ∀ x, stateLevel s' x = stateLevel s x := fun _ => rfl
    have hsr : stateReason s' s.trail[i] = remapReason rmap (stateReason s s.trail[i]) :=
      stateReason_map (by rfl) _
    change match stateReason s' s'.trail[i] with | _ => _
    simp only [htr, hf0, hsl, hsr]
    generalize hrsn : stateReason s s.trail[i] = rsn; rw [hrsn] at hrd
    cases rsn with
    | decision | unit | binary _ => exact hrd
    | large cid =>
      obtain ⟨c, hget, hng, hlmem, hall⟩ := hrd
      obtain ⟨nid, hlkp, hnew⟩ := hrs.2.1 cid c hget hng
      dsimp only [remapReason]
      rw [show (collectClauses s.clauses).2.lookup cid = some nid from hlkp]
      exact ⟨c, hnew, hng, hlmem, hall⟩

theorem collect_preserves_inv {s : CdclState} (hinv : TrailInv s) :
    let (s', rmap) := collect s
    TrailInv s' ∧ s'.f0 = s.f0 ∧ RefMapSound s.clauses s'.clauses rmap s.f0 := by
  have hc := collect_preserves_lazyInv hinv.toLazy
  refine ⟨⟨hc.1.vars_nodup, hc.1.levels_le, hinv.levels_mono, hc.1.dec_earliest,
    hc.1.db_sound, hc.1.units_sound, hc.1.reason_dag, hc.1.inconsistent_sound⟩, hc.2⟩

theorem deleteClauseState_preserves_inv {s : CdclState} (hinv : TrailInv s) (cid : Nat)
    (hunused : ∀ i (hi : i < s.trail.size), stateReason s s.trail[i] ≠ .large cid) :
    TrailInv (deleteClauseState s cid) ∧ (deleteClauseState s cid).f0 = s.f0 := by
  have hlazy := lazyTrailInv_withClauses hinv.toLazy (deleteClauseState s cid).clauses
    (fun k c hk => by
      simp only [deleteClauseState, Array.getElem?_setIfInBounds] at hk
      split at hk
      · split at hk <;> cases hk
      · exact hinv.db_sound k c hk)
    (fun i hi cid' c hrsn hget _ => by
      have hne : cid ≠ cid' := Ne.symm (by simpa [hrsn] using hunused i hi)
      simp only [deleteClauseState, Array.getElem?_setIfInBounds, hne, ↓reduceIte]; exact hget)
  exact ⟨⟨hlazy.vars_nodup, hlazy.levels_le, hinv.levels_mono, hlazy.dec_earliest,
    hlazy.db_sound, hlazy.units_sound, hlazy.reason_dag, hlazy.inconsistent_sound⟩, rfl⟩

/-! ## 9. Top-level CDCL reference solver soundness (`cdclSolve_sound`) -/

private theorem pickVarFrom?_unassigned (s : CdclState) :
    ∀ n idx l, s.numVars - idx ≤ n → pickVarFrom? s idx = some l → litStatus s.trail l = none := by
  intro n
  induction n with
  | zero =>
    intro idx l hn h
    unfold pickVarFrom? at h
    rw [dite_eq_right (by omega : ¬ idx < s.numVars)] at h; cases h
  | succ n ih =>
    intro idx l hn h
    unfold pickVarFrom? at h
    by_cases hlt : idx < s.numVars
    · rw [dite_eq_left hlt] at h; dsimp only at h
      cases hst : litStatus s.trail (mkLit idx false) with
      | none => rw [hst] at h; simp at h; subst h; exact hst
      | some b => rw [hst] at h; exact ih (idx + 1) l (by omega) h
    · rw [dite_eq_right hlt] at h; cases h

theorem pickBranchLit?_unassigned {s : CdclState} {l : Nat}
    (h : pickBranchLit? s = some l) : litStatus s.trail l = none := by
  unfold pickBranchLit? at h; dsimp only at h
  split at h
  · rename_i w hfc
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨_, opt, _, _, hopt, _⟩ := Array.findSome?_eq_some_iff.mp hfc
    cases opt with
    | none => simp at hopt
    | some c =>
      dsimp only at hopt
      split at hopt
      · simp at hopt
      · split at hopt
        · simp at hopt
        · have hnone := List.find?_some hopt
          cases hst : litStatus s.trail w <;> simp_all
  · exact pickVarFrom?_unassigned s s.numVars 0 l (Nat.le_refl _) h

theorem cdclLoop_sound_full {fuel : Nat} {s : CdclState} (hinv : TrailInv s) :
    match cdclLoop fuel s with
    | .unsat => s.f0.Unsat
    | .sat σ => checkModel s.f0 σ = true
    | .unknown => True := by
  induction fuel generalizing s with
  | zero => simp [cdclLoop]
  | succ fuel ih =>
    simp only [cdclLoop]
    by_cases hinc : s.inconsistent = true
    · simp only [hinc, ↓reduceIte]; exact hinv.inconsistent_sound hinc
    · have hincf : s.inconsistent = false := Bool.eq_false_iff.mpr hinc
      simp only [hincf, Bool.false_eq_true, ↓reduceIte]
      let propFuel := s.numVars + s.clauses.size + s.units.length + 16
      have hprop := propagateAll_inv (fuel := propFuel) hinv
      cases hp : propagateAll propFuel s with
      | outOfFuel _ => simp
      | conflict confl s1 =>
        rw [hp] at hprop; obtain ⟨hinv1, hf01, _, hconfl1, hfals1, _⟩ := hprop
        dsimp only [propFuel]
        by_cases hl0 : s1.level = 0
        · simp only [show (s1.level == 0) = true by simp [hl0], ↓reduceIte]
          rw [← hf01]; exact unsat_of_conflict hinv1 hl0 hconfl1 hfals1
        · have hl0f : (s1.level == 0) = false := beq_false_of_ne hl0
          simp only [hl0f, Bool.false_eq_true, ↓reduceIte]
          have h1uip := analyze1UIP_sound hinv1 hconfl1 hfals1
          have hmin := minimizeCut_sound hinv1 h1uip.1
          by_cases he : (minimizeClause s1 (analyze1UIP s1 confl)).isEmpty = true
          · simp only [he, ↓reduceIte]
            have hnil : minimizeClause s1 (analyze1UIP s1 confl) = [] := by
              simpa [List.isEmpty_iff] using he
            rw [hnil] at hmin; rw [← hf01]; exact unsat_of_entails_nil hmin
          · have hef : (minimizeClause s1 (analyze1UIP s1 confl)).isEmpty = false :=
              Bool.eq_false_iff.mpr he
            simp only [hef, Bool.false_eq_true, ↓reduceIte]
            have hbl := backtrack_learn_preserves_inv hinv1
              (Nat.min (s1.level - 1)
                (backtrackLevel s1 (minimizeClause s1 (analyze1UIP s1 confl))))
              (glue := 0) hmin
            have hih := ih hbl.1
            simpa [hbl.2, hf01] using hih
      | ok s1 =>
        rw [hp] at hprop; obtain ⟨hinv1, hf01, _⟩ := hprop
        dsimp only [propFuel]
        cases hpick : pickBranchLit? s1 with
        | some l =>
          have hdec := decideLit_inv hinv1 (pickBranchLit?_unassigned hpick)
          have hih := ih hdec.1
          simpa [hdec.2, hf01] using hih
        | none =>
          dsimp only
          by_cases hchk : checkModel s1.f0 (modelFromTrail s1.numVars s1.trail) = true
          · rw [ite_eq_left hchk, ← hf01]; exact hchk
          · have hchkf : checkModel s1.f0 (modelFromTrail s1.numVars s1.trail) = false :=
              Bool.eq_false_iff.mpr hchk
            simp [hchkf]

theorem cdclLoop_sound {fuel : Nat} {s : CdclState} (hinv : TrailInv s) :
    match cdclLoop fuel s with
    | .unsat => s.f0.Unsat
    | .sat _ => ¬ s.f0.Unsat ∧ ∃ α, s.f0.Sat α
    | .unknown => True := by
  have h := cdclLoop_sound_full (fuel := fuel) hinv
  cases hres : cdclLoop fuel s with
  | unsat => rw [hres] at h; exact h
  | unknown => trivial
  | sat σ => rw [hres] at h; exact checkModel_sound h

theorem cdclSolve_sat_model {fuel : Nat} {cnf : CNF Nat} {σ : Array Bool}
    (h : cdclSolve fuel cnf = .sat σ) : checkModel cnf σ = true := by
  have hm := cdclLoop_sound_full (fuel := fuel) (initState_inv cnf).1
  unfold cdclSolve at h; rw [h, (initState_inv cnf).2] at hm; exact hm

/-- Refutation soundness of `cdclSolve`. -/
theorem cdclSolve_unsat_sound {fuel : Nat} {cnf : CNF Nat}
    (h : cdclSolve fuel cnf = .unsat) : cnf.Unsat := by
  have hloop := cdclLoop_sound (fuel := fuel) (initState_inv cnf).1
  unfold cdclSolve at h; rw [h, (initState_inv cnf).2] at hloop; exact hloop

/-- Satisfiability soundness of `cdclSolve`. -/
theorem cdclSolve_sat_sound {fuel : Nat} {cnf : CNF Nat} {σ : Array Bool}
    (h : cdclSolve fuel cnf = .sat σ) : ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α :=
  checkModel_sound (cdclSolve_sat_model h)

/-- Combined top-level Layer-A solver soundness theorem (`cdclSolve_sound`). -/
theorem cdclSolve_sound (fuel : Nat) (cnf : CNF Nat) :
    match cdclSolve fuel cnf with
    | .unsat => cnf.Unsat
    | .sat _ => ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α
    | .unknown => True := by
  cases h : cdclSolve fuel cnf with
  | unsat => exact cdclSolve_unsat_sound h
  | sat σ => exact cdclSolve_sat_sound h
  | unknown => trivial

/-- Parametric parser bridge for `cdclSolve_sound`. -/
theorem cdclSolve_sound_of_parse {parse : List UInt8 → Option (CNF Nat)}
    {bs : List UInt8} {cnf : CNF Nat} (fuel : Nat)
    (_hp : parse bs = some cnf) :
    match cdclSolve fuel cnf with
    | .unsat => cnf.Unsat
    | .sat _ => ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α
    | .unknown => True :=
  cdclSolve_sound fuel cnf

end LeanQbe.T.Examples.Kissat.Ref
