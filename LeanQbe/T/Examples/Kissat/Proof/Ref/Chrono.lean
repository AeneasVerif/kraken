/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Chrono
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Sweep

/-!
# Soundness Proofs for `Chrono`

Extracted pure-Lean proofs for `Chrono` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. `ChronoState`, explicit `isDecision` markers, `ChronoTrailInv`, & entailment -/

theorem mem_chronoDecisionsAtMost_iff {s : ChronoState} {k l : Nat} :
    l ∈ chronoDecisionsAtMost s k ↔
      l ∈ s.cdcl.trail.toList ∧ s.isDecision l = true ∧ stateLevel s.cdcl l ≤ k := by
  simp [chronoDecisionsAtMost]

theorem unitsCnf_chronoDecisionsAtMost_mono {s : ChronoState} {k1 k2 : Nat} (hle : k1 ≤ k2) :
    (s.cdcl.f0 ++ unitsCnf (chronoDecisionsAtMost s k2)).Entails
      (s.cdcl.f0 ++ unitsCnf (chronoDecisionsAtMost s k1)) := by
  rw [CNF.entails_def]
  intro α hα
  rw [CNF.sat_append, sat_unitsCnf_iff] at hα ⊢
  refine ⟨hα.1, fun l hl => hα.2 l ?_⟩
  rw [mem_chronoDecisionsAtMost_iff] at hl ⊢
  exact ⟨hl.1, hl.2.1, Nat.le_trans hl.2.2 hle⟩

/-- Every `ChronoTrailInv` state projects directly to `Minimize.LazyTrailInv`. -/
theorem ChronoTrailInv.toLazy {s : ChronoState} (h : ChronoTrailInv s) : LazyTrailInv s.cdcl := by
  refine ⟨h.vars_nodup, h.levels_le, fun i j hi hj hleq hrsn => ?_,
    h.db_sound, h.units_sound, h.reason_dag, h.inconsistent_sound⟩
  have hdec : s.isDecision s.cdcl.trail[j] = true := by
    rw [h.dec_sync j hj, hrsn]; exact decide_eq_true rfl
  exact h.dec_earliest i j hi hj hleq hdec

theorem LazyTrailInv.toChrono {cdcl : CdclState} (h : LazyTrailInv cdcl)
    (frames : Array Nat := #[]) : ChronoTrailInv (ChronoState.ofCdcl cdcl frames) := by
  have hisdec : ∀ i (hi : i < cdcl.trail.size),
      (ChronoState.ofCdcl cdcl frames).isDecision cdcl.trail[i] =
        decide (stateReason cdcl cdcl.trail[i] = .decision) := by
    intro i _
    simp only [ChronoState.isDecision, ChronoState.ofCdcl, Array.getD_eq_getD_getElem?,
      Array.getElem?_map, stateReason]
    cases hget : cdcl.reasons[litVar cdcl.trail[i]]? with
    | none => simp
    | some r => simp
  refine ⟨h.vars_nodup, h.levels_le, hisdec, fun i j hi hj hleq hdec => ?_,
    h.db_sound, h.units_sound, h.reason_dag, h.inconsistent_sound⟩
  have hdec' : (ChronoState.ofCdcl cdcl frames).isDecision cdcl.trail[j] = true := hdec
  rw [hisdec j hj] at hdec'
  exact h.dec_earliest i j hi hj hleq (of_decide_eq_true hdec')

theorem ChronoTrailInv.dec_unique_level {s : ChronoState} (h : ChronoTrailInv s) {i j : Nat}
    (hi : i < s.cdcl.trail.size) (hj : j < s.cdcl.trail.size)
    (hleq : stateLevel s.cdcl s.cdcl.trail[i] = stateLevel s.cdcl s.cdcl.trail[j])
    (hdi : s.isDecision s.cdcl.trail[i] = true) (hdj : s.isDecision s.cdcl.trail[j] = true) :
    i = j :=
  Nat.le_antisymm (h.dec_earliest j i hj hi hleq.symm hdi) (h.dec_earliest i j hi hj hleq hdj)

theorem chronoDecisionsAtMost_eq {s : ChronoState} (h : ChronoTrailInv s) (k : Nat) :
    chronoDecisionsAtMost s k = decisionsAtMost s.cdcl k := by
  unfold chronoDecisionsAtMost decisionsAtMost
  apply List.filter_congr
  intro l hl
  obtain ⟨i, hi, rfl⟩ := trail_mem_iff_exists.mp hl
  rw [h.dec_sync i hi]

/-- Direct trail entailment under chronological levels using explicit `isDecision` markers
(`F₀ ∧ decisions ≤_k ⊨ literal`). -/
theorem chronoTrailEntailment {s : ChronoState} (hinv : ChronoTrailInv s) :
    ∀ (i : Nat) (hi : i < s.cdcl.trail.size),
      (s.cdcl.f0 ++ unitsCnf
        (chronoDecisionsAtMost s (stateLevel s.cdcl s.cdcl.trail[i]))).EntailsClause
        (cnfClause [s.cdcl.trail[i]]) := by
  intro i hi
  rw [chronoDecisionsAtMost_eq hinv]
  exact lazyTrailEntailment hinv.toLazy i hi

theorem chronoDecisionsAtMost_zero_empty {s : ChronoState} (hinv : ChronoTrailInv s) :
    chronoDecisionsAtMost s 0 = [] := by
  rw [chronoDecisionsAtMost_eq hinv]
  exact lazyDecisionsAtMost_zero_empty hinv.toLazy

theorem chronoTrailEntailment_level0 {s : ChronoState} (hinv : ChronoTrailInv s) {i : Nat}
    (hi : i < s.cdcl.trail.size) (hlvl : stateLevel s.cdcl s.cdcl.trail[i] = 0) :
    s.cdcl.f0.EntailsClause (cnfClause [s.cdcl.trail[i]]) := by
  have h := chronoTrailEntailment hinv i hi
  rw [hlvl, chronoDecisionsAtMost_zero_empty hinv] at h
  exact CNF.entails_clause_def.mpr fun α hα =>
    CNF.entails_clause_def.mp h α (by simpa [unitsCnf] using hα)

theorem chronoUnsat_of_conflict {s : ChronoState} (hinv : ChronoTrailInv s) {confl : List Nat}
    (hlvl : s.cdcl.level = 0) (hconfl : s.cdcl.f0.EntailsClause (cnfClause confl))
    (hfals : ∀ l ∈ confl, litNeg l ∈ s.cdcl.trail.toList) : s.cdcl.f0.Unsat :=
  lazyUnsat_of_conflict hinv.toLazy hlvl hconfl hfals

/-! ## 2. Chronological transitions (`chronoBacktrack`, `chronoAssignUip`, `restartReuseTrail`) -/

theorem chronoInit_inv (cnf : CNF Nat) :
    ChronoTrailInv (chronoInit cnf) ∧ (chronoInit cnf).cdcl.f0 = cnf :=
  ⟨(initState_inv cnf).1.toLazy.toChrono #[], (initState_inv cnf).2⟩

private def chronoWithLvlUnits (s : ChronoState) (nl : Nat) (us : List Nat)
    (fs : Array Nat) : ChronoState :=
  { s with cdcl := { s.cdcl with level := nl, units := us }, frames := fs }

@[simp] private theorem f0_chronoWlu (s : ChronoState) (nl : Nat) (us : List Nat)
    (fs : Array Nat) : (chronoWithLvlUnits s nl us fs).cdcl.f0 = s.cdcl.f0 := rfl

@[simp] private theorem clauses_chronoWlu (s : ChronoState) (nl : Nat) (us : List Nat)
    (fs : Array Nat) : (chronoWithLvlUnits s nl us fs).cdcl.clauses = s.cdcl.clauses := rfl

@[simp] private theorem trail_chronoWlu (s : ChronoState) (nl : Nat) (us : List Nat)
    (fs : Array Nat) : (chronoWithLvlUnits s nl us fs).cdcl.trail = s.cdcl.trail := rfl

@[simp] private theorem isDec_chronoWlu (s : ChronoState) (nl : Nat) (us : List Nat)
    (fs : Array Nat) : (chronoWithLvlUnits s nl us fs).isDec = s.isDec := rfl

@[simp] private theorem stateLevel_chronoWlu (s : ChronoState) (nl : Nat) (us : List Nat)
    (fs : Array Nat) (x : Nat) :
    stateLevel (chronoWithLvlUnits s nl us fs).cdcl x = stateLevel s.cdcl x := rfl

@[simp] private theorem stateReason_chronoWlu (s : ChronoState) (nl : Nat) (us : List Nat)
    (fs : Array Nat) (x : Nat) :
    stateReason (chronoWithLvlUnits s nl us fs).cdcl x = stateReason s.cdcl x := rfl

private def chronoPushRaw (s : ChronoState) (l lvl newLvl : Nat) (rsn : Reason)
    (us : List Nat) (fs : Array Nat) : ChronoState :=
  let base := chronoWithLvlUnits s newLvl us fs
  { base with
    cdcl := assignLit base.cdcl l lvl rsn
    isDec := arraySetPad base.isDec (litVar l) (decide (rsn = .decision)) false }

private theorem chronoPush_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    {l lvl newLvl : Nat} {rsn : Reason} {us : List Nat} {fs : Array Nat}
    (hun : litStatus s.cdcl.trail l = none)
    (hs_lvl : s.cdcl.level ≤ newLvl) (hlvl_le : lvl ≤ newLvl)
    (hdec_ne : rsn = .decision → ∀ i (hi : i < s.cdcl.trail.size),
      stateLevel s.cdcl s.cdcl.trail[i] ≠ lvl)
    (hrsn : ReasonOk s.cdcl l lvl rsn)
    (hunits : ∀ u ∈ us, s.cdcl.f0.EntailsClause (cnfClause [u])) :
    let s' := chronoPushRaw s l lvl newLvl rsn us fs
    ChronoTrailInv s' ∧ s'.cdcl.f0 = s.cdcl.f0 := by
  have hold_lt : ∀ {i : Nat} (hi : i < s.cdcl.trail.size), litVar s.cdcl.trail[i] ≠ litVar l :=
    fun hi => litStatus_none_no_var hun _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
  refine ⟨⟨?_, ?_, ?_, ?_, hinv.db_sound, hunits, ?_, hinv.inconsistent_sound⟩, rfl⟩
  · intro i j hi hj hvar
    simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.size_push] at hi hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.getElem_push_lt hi',
        Array.getElem_push_lt hj'] at hvar
      exact hinv.vars_nodup i j hi' hj' hvar
    · simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.getElem_push_lt hi',
        Array.getElem_push_eq] at hvar
      exact absurd hvar (hold_lt hi')
    · simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.getElem_push_eq,
        Array.getElem_push_lt hj'] at hvar
      exact absurd hvar.symm (hold_lt hj')
    · rfl
  · intro i hi
    simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.size_push] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.getElem_push_lt hi',
        stateLevel_assignLit, stateLevel_chronoWlu, hold_lt hi', ↓reduceIte, level_assignLit]
      exact Nat.le_trans (hinv.levels_le i hi') hs_lvl
    · simp [chronoPushRaw, chronoWithLvlUnits, hlvl_le]
  · intro i hi
    simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.size_push] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · have hnv := hold_lt hi'
      simp only [chronoPushRaw, trail_chronoWlu, isDec_chronoWlu, trail_assignLit,
        Array.getElem_push_lt hi', ChronoState.isDecision, arraySetPad_getD,
        stateReason_assignLit, stateReason_chronoWlu, hnv, ↓reduceIte]
      exact hinv.dec_sync i hi'
    · simp only [chronoPushRaw, trail_chronoWlu, isDec_chronoWlu, trail_assignLit,
        Array.getElem_push_eq, ChronoState.isDecision, arraySetPad_getD,
        stateReason_assignLit, ↓reduceIte]
  · intro i j hi hj hleq hdj
    simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.size_push] at hi hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · simp only [chronoPushRaw, trail_chronoWlu, isDec_chronoWlu, trail_assignLit,
          Array.getElem_push_lt hi', Array.getElem_push_lt hj', stateLevel_assignLit,
          stateLevel_chronoWlu, ChronoState.isDecision, arraySetPad_getD,
          hold_lt hi', hold_lt hj', ↓reduceIte] at hleq hdj
        exact hinv.dec_earliest i j hi' hj' hleq hdj
      · omega
    · simp only [chronoPushRaw, isDec_chronoWlu, trail_chronoWlu, trail_assignLit,
        Array.getElem_push_eq, ChronoState.isDecision, arraySetPad_getD, ↓reduceIte] at hdj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · simp only [chronoPushRaw, trail_chronoWlu, trail_assignLit, Array.getElem_push_lt hi',
          Array.getElem_push_eq, stateLevel_assignLit, stateLevel_chronoWlu,
          hold_lt hi', ↓reduceIte] at hleq
        exact absurd hleq (hdec_ne (of_decide_eq_true hdj) i hi')
      · exact Nat.le_refl _
  · exact reasonDagInv_assignLit (s := chronoWithLvlUnits s newLvl us fs |>.cdcl)
      hinv.reason_dag hun hrsn

theorem chronoDecide_inv {s : ChronoState} (hinv : ChronoTrailInv s) {l : Nat}
    (hun : litStatus s.cdcl.trail l = none) :
    ChronoTrailInv (chronoDecide s l) ∧ (chronoDecide s l).cdcl.f0 = s.cdcl.f0 := by
  have heq : chronoDecide s l = chronoPushRaw s l (s.cdcl.level + 1) (s.cdcl.level + 1)
      .decision s.cdcl.units (s.frames.push s.cdcl.trail.size) := by
    cases s; simp [chronoDecide, decideLit, chronoPushRaw, chronoWithLvlUnits]
  rw [heq]
  exact chronoPush_inv hinv hun (Nat.le_succ _) (Nat.le_refl _)
    (fun _ i hi heql => by have := hinv.levels_le i hi; omega)
    (Nat.zero_lt_succ _) hinv.units_sound

theorem chronoAssignProp_inv {s : ChronoState} (hinv : ChronoTrailInv s) {l : Nat} {rsn : Reason}
    (hun : litStatus s.cdcl.trail l = none) (hrsn_ne : rsn ≠ .decision)
    (hrsn : ReasonOk s.cdcl l s.cdcl.level rsn) :
    ChronoTrailInv (chronoAssignProp s l rsn) ∧ (chronoAssignProp s l rsn).cdcl.f0 = s.cdcl.f0 := by
  have hdecb : (decide (rsn = .decision)) = false := decide_eq_false hrsn_ne
  have heq : chronoAssignProp s l rsn = chronoPushRaw s l s.cdcl.level s.cdcl.level
      rsn s.cdcl.units s.frames := by
    cases s; simp [chronoAssignProp, chronoPushRaw, chronoWithLvlUnits, hdecb]
  rw [heq]
  exact chronoPush_inv hinv hun (Nat.le_refl _) (Nat.le_refl _)
    (fun h => absurd h hrsn_ne) hrsn hinv.units_sound

theorem chronoAssignUip_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    {uip uipLevel : Nat} {rsn : Reason}
    (hun : litStatus s.cdcl.trail uip = none) (hle : uipLevel ≤ s.cdcl.level)
    (hrsn_ne : rsn ≠ .decision) (hrsn : ReasonOk s.cdcl uip uipLevel rsn) :
    ChronoTrailInv (chronoAssignUip s uip uipLevel rsn) ∧
      (chronoAssignUip s uip uipLevel rsn).cdcl.f0 = s.cdcl.f0 := by
  have hdecb : (decide (rsn = .decision)) = false := decide_eq_false hrsn_ne
  have heq : chronoAssignUip s uip uipLevel rsn = chronoPushRaw s uip uipLevel s.cdcl.level
      rsn s.cdcl.units s.frames := by
    cases s; simp [chronoAssignUip, chronoPushRaw, chronoWithLvlUnits, hdecb]
  rw [heq]
  exact chronoPush_inv hinv hun (Nat.le_refl _) hle
    (fun h => absurd h hrsn_ne) hrsn hinv.units_sound

theorem chronoAddRootUnit_inv {s : ChronoState} (hinv : ChronoTrailInv s) {l : Nat}
    (hun : litStatus s.cdcl.trail l = none) (hent : s.cdcl.f0.EntailsClause (cnfClause [l])) :
    ChronoTrailInv (chronoAddRootUnit s l) ∧ (chronoAddRootUnit s l).cdcl.f0 = s.cdcl.f0 := by
  have heq : chronoAddRootUnit s l = chronoPushRaw s l 0 s.cdcl.level
      .unit (l :: s.cdcl.units) s.frames := by
    cases s; simp [chronoAddRootUnit, chronoPushRaw, chronoWithLvlUnits]
  rw [heq]
  exact chronoPush_inv hinv hun (Nat.le_refl _) (Nat.zero_le _)
    (fun h => by cases h) ⟨rfl, hent⟩
    (fun u hu => (List.mem_cons.mp hu).elim (· ▸ hent) (hinv.units_sound u))

theorem chronoBacktrack_preserves_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    (targetLevel : Nat) :
    ChronoTrailInv (chronoBacktrack s targetLevel) ∧
      (chronoBacktrack s targetLevel).cdcl.f0 = s.cdcl.f0 := by
  have hb := backtrackFilter_preserves_lazyInv hinv.toLazy targetLevel
  have hisdec : ∀ i (hi : i < (chronoBacktrack s targetLevel).cdcl.trail.size),
      (chronoBacktrack s targetLevel).isDecision (chronoBacktrack s targetLevel).cdcl.trail[i] =
        decide (stateReason (chronoBacktrack s targetLevel).cdcl
          (chronoBacktrack s targetLevel).cdcl.trail[i] = .decision) := by
    intro i hi
    have hmem : (chronoBacktrack s targetLevel).cdcl.trail[i] ∈
        (backtrackFilter s.cdcl targetLevel).trail.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem hi)
    rw [Array.mem_toList_iff] at hmem
    simp only [backtrackFilter, List.mem_toArray, List.mem_filter] at hmem
    obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp hmem.1
    have h_lhs : (chronoBacktrack s targetLevel).isDecision
        (chronoBacktrack s targetLevel).cdcl.trail[i] =
        s.isDecision s.cdcl.trail[j] := congrArg s.isDecision hjeq.symm
    have h_rhs : stateReason (chronoBacktrack s targetLevel).cdcl
        (chronoBacktrack s targetLevel).cdcl.trail[i] =
        stateReason s.cdcl s.cdcl.trail[j] := congrArg (stateReason s.cdcl) hjeq.symm
    rw [h_lhs, h_rhs]
    exact hinv.dec_sync j hj
  refine ⟨⟨hb.1.vars_nodup, hb.1.levels_le, hisdec, fun i j hi hj hleq hdj => ?_,
    hb.1.db_sound, hb.1.units_sound, hb.1.reason_dag, hb.1.inconsistent_sound⟩, hb.2⟩
  rw [hisdec j hj] at hdj
  exact hb.1.dec_earliest i j hi hj hleq (of_decide_eq_true hdj)

theorem restartReuseTrail_preserves_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    (reuseLevel : Nat) :
    ChronoTrailInv (restartReuseTrail s reuseLevel) ∧
      (restartReuseTrail s reuseLevel).cdcl.f0 = s.cdcl.f0 :=
  chronoBacktrack_preserves_inv hinv reuseLevel

theorem restartReusePrefix_preserves_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    {reuseLevel prefixLen : Nat} (hpre : prefixLen ≤ s.cdcl.trail.size)
    (hle : ∀ (i : Nat) (_hi : i < prefixLen) (hs : i < s.cdcl.trail.size),
      stateLevel s.cdcl s.cdcl.trail[i] ≤ reuseLevel) :
    ChronoTrailInv (restartReusePrefix s reuseLevel prefixLen) ∧
      (restartReusePrefix s reuseLevel prefixLen).cdcl.f0 = s.cdcl.f0 := by
  have hsz : (restartReusePrefix s reuseLevel prefixLen).cdcl.trail.size = prefixLen := by
    simp [restartReusePrefix, hpre]
  have hget : ∀ i (hi : i < (restartReusePrefix s reuseLevel prefixLen).cdcl.trail.size),
      (restartReusePrefix s reuseLevel prefixLen).cdcl.trail[i] =
        s.cdcl.trail[i]'(by omega) := by
    intro i hi; simp [restartReusePrefix]
  have hf0 : (restartReusePrefix s reuseLevel prefixLen).cdcl.f0 = s.cdcl.f0 := rfl
  have hcls : (restartReusePrefix s reuseLevel prefixLen).cdcl.clauses = s.cdcl.clauses := rfl
  have hsl : ∀ x, stateLevel (restartReusePrefix s reuseLevel prefixLen).cdcl x =
      stateLevel s.cdcl x := fun _ => rfl
  have hsr : ∀ x, stateReason (restartReusePrefix s reuseLevel prefixLen).cdcl x =
      stateReason s.cdcl x := fun _ => rfl
  refine ⟨⟨?_, ?_, ?_, ?_, hinv.db_sound, hinv.units_sound, ?_, hinv.inconsistent_sound⟩, rfl⟩
  · intro i j hi hj hvar
    rw [hget i hi, hget j hj] at hvar
    exact hinv.vars_nodup i j _ _ hvar
  · intro i hi
    change stateLevel s.cdcl (restartReusePrefix s reuseLevel prefixLen).cdcl.trail[i] ≤
      Nat.min s.cdcl.level reuseLevel
    rw [hget i hi]
    exact Nat.le_min.mpr ⟨hinv.levels_le i (by omega), hle i (by omega) (by omega)⟩
  · intro i hi
    change s.isDecision (restartReusePrefix s reuseLevel prefixLen).cdcl.trail[i] =
      decide (stateReason s.cdcl (restartReusePrefix s reuseLevel prefixLen).cdcl.trail[i] =
        .decision)
    rw [hget i hi]
    exact hinv.dec_sync i (by omega)
  · intro i j hi hj hleq hdj
    change stateLevel s.cdcl (restartReusePrefix s reuseLevel prefixLen).cdcl.trail[i] =
      stateLevel s.cdcl (restartReusePrefix s reuseLevel prefixLen).cdcl.trail[j] at hleq
    change s.isDecision (restartReusePrefix s reuseLevel prefixLen).cdcl.trail[j] = true at hdj
    rw [hget i hi, hget j hj] at hleq
    rw [hget j hj] at hdj
    exact hinv.dec_earliest i j _ _ hleq hdj
  · intro i hi
    have hi' : i < s.cdcl.trail.size := by omega
    have hrd := hinv.reason_dag i hi'; dsimp only at hrd
    change match stateReason (restartReusePrefix s reuseLevel prefixLen).cdcl
        (restartReusePrefix s reuseLevel prefixLen).cdcl.trail[i] with | _ => _
    simp only [hf0, hcls, hsl, hsr, hget i hi]
    generalize hrs : stateReason s.cdcl s.cdcl.trail[i] = rsn
    rw [hrs] at hrd
    cases rsn with
    | decision | unit => exact hrd
    | binary other =>
      obtain ⟨hbin, j, hj, hjlt, hjeq, hle', hlex⟩ := hrd
      have hj_sz : j < (restartReusePrefix s reuseLevel prefixLen).cdcl.trail.size := by omega
      exact ⟨hbin, j, hj_sz, hjlt, by rw [hget j hj_sz]; exact hjeq, hle', hlex⟩
    | large cid =>
      obtain ⟨c, hget_c, hng, hlmem, hall⟩ := hrd
      refine ⟨c, hget_c, hng, hlmem, fun x hx hne => ?_⟩
      obtain ⟨j, hj, hjlt, hjeq, hle', hlex⟩ := hall x hx hne
      have hj_sz : j < (restartReusePrefix s reuseLevel prefixLen).cdcl.trail.size := by omega
      exact ⟨j, hj_sz, hjlt, by rw [hget j hj_sz]; exact hjeq, hle', hlex⟩

/-! ## 3. 1UIP + OTFS resolution, lexicographic minimization & shrinking, and conflict step -/

private theorem chronoAnalyze1UIPAux_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    (hlvl_pos : 0 < s.cdcl.level) :
    ∀ (i : Nat), i ≤ s.cdcl.trail.size → ∀ (cl : List Nat) (ups : List OtfsUpdate),
      s.cdcl.f0.EntailsClause (cnfClause cl) →
      (∀ x ∈ cl, ∃ (j : Nat) (_hj : j < s.cdcl.trail.size),
        s.cdcl.trail[j] = litNeg x ∧ (stateLevel s.cdcl x = s.cdcl.level → j < i)) →
      (∀ u ∈ ups, OtfsValidAt s s.cdcl.level u) →
      let out := chronoAnalyze1UIPAux s i cl ups
      s.cdcl.f0.EntailsClause (cnfClause out.learned) ∧
      (∀ x ∈ out.learned, ∃ (j : Nat) (_hj : j < s.cdcl.trail.size),
        s.cdcl.trail[j] = litNeg x) ∧
      countAtLevel s.cdcl out.learned s.cdcl.level ≤ 1 ∧
      (cl ≠ [] → out.learned ≠ []) ∧
      (∀ u ∈ out.otfs, OtfsValidAt s s.cdcl.level u) := by
  intro i
  induction i with
  | zero =>
    intro _ cl ups hent htrl hups
    simp only [chronoAnalyze1UIPAux]
    have hnil : (dedupLits cl).filter (fun l => stateLevel s.cdcl l == s.cdcl.level) = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
        rw [List.mem_filter] at hx
        obtain ⟨j, _, _, hlt⟩ := htrl x (mem_dedupLits_iff.mp hx.1)
        have h0 := hlt (by simpa using hx.2); omega
    refine ⟨entails_dedupLits hent, fun x hx => ?_, by simp [countAtLevel, hnil],
      dedupLits_ne_nil, hups⟩
    obtain ⟨j, hj, hjeq, _⟩ := htrl x (mem_dedupLits_iff.mp hx)
    exact ⟨j, hj, hjeq⟩
  | succ i ih =>
    intro hi cl ups hent htrl hups
    let cl' := dedupLits cl
    have hnd : cl'.Nodup := nodup_dedupLits cl
    have hent' : s.cdcl.f0.EntailsClause (cnfClause cl') := entails_dedupLits hent
    have htrl' : ∀ x ∈ cl', ∃ (j : Nat) (_hj : j < s.cdcl.trail.size),
        s.cdcl.trail[j] = litNeg x ∧ (stateLevel s.cdcl x = s.cdcl.level → j < i + 1) :=
      fun x hx => htrl x (mem_dedupLits_iff.mp hx)
    rw [chronoAnalyze1UIPAux]; dsimp only
    by_cases hcnt : countAtLevel s.cdcl cl' s.cdcl.level ≤ 1
    · rw [ite_eq_left hcnt]
      exact ⟨hent', fun x hx => let ⟨j, hj, heq, _⟩ := htrl' x hx; ⟨j, hj, heq⟩,
        hcnt, fun h => dedupLits_ne_nil h, hups⟩
    · have hi' : i < s.cdcl.trail.size := by omega
      rw [ite_eq_right hcnt, dite_eq_left hi']
      let p := s.cdcl.trail[i]
      let np := litNeg p
      have hp_not_cl : p ∉ cl' := fun hp_mem => by
        obtain ⟨j, hj, hjeq, _⟩ := htrl' p hp_mem
        have hij := hinv.vars_nodup j i hj hi' (by rw [hjeq, litVar_litNeg])
        subst hij
        exact absurd hjeq.symm (litNeg_ne_self p)
      by_cases hres :
          (cl'.contains np && stateLevel s.cdcl p == s.cdcl.level && !s.isDecision p) = true
      · rw [ite_eq_left hres]
        simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, Bool.not_eq_true'] at hres
        obtain ⟨⟨hnp_mem, hplvl⟩, hnotdec⟩ := hres
        have hne_step : ∀ (r : List Nat), resolveOn np cl' r ≠ [] := fun r => by
          obtain ⟨q, hq, _, hqne⟩ := exists_ne_of_filter_gt_one
            (P := fun l => stateLevel s.cdcl l == s.cdcl.level) (np := np) hnd
            (by unfold countAtLevel at hcnt; omega)
          exact List.ne_nil_of_mem
            (List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simp [hqne]⟩))
        have hkeep : ∀ x ∈ cl'.filter (· != np),
            ∃ (j : Nat) (_hj : j < s.cdcl.trail.size),
              s.cdcl.trail[j] = litNeg x ∧ (stateLevel s.cdcl x = s.cdcl.level → j < i) := by
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
        generalize hrsn : stateReason s.cdcl s.cdcl.trail[i] = rsn
        rw [hrsn] at hrd
        cases rsn with
        | decision =>
          have hds := hinv.dec_sync i hi'
          rw [hrsn] at hds
          have hds' : s.isDecision p = true := hds.trans (decide_eq_true rfl)
          rw [hds'] at hnotdec; cases hnotdec
        | unit =>
          have h0 : stateLevel s.cdcl s.cdcl.trail[i] = 0 := hrd.1
          have hpl : stateLevel s.cdcl p = s.cdcl.level := hplvl
          dsimp only [p] at hpl; omega
        | binary other =>
          obtain ⟨hbin, j0, hj0, hj0lt, hj0eq, _⟩ := hrd
          refine ih (Nat.le_of_lt hi') _ ups
            (entails_dedupLits (entails_resolve hent' hbin)) (fun x hx => ?_) hups |>
            fun ⟨h1, h2, h3, h4, h5⟩ =>
              ⟨h1, h2, h3, fun _ => h4 (dedupLits_ne_nil (hne_step _)), h5⟩
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
          obtain ⟨c, hget, hng, hpmem, hall⟩ := hrd
          dsimp only; rw [hget]; dsimp only
          let res := dedupLits (resolveOn np cl' c.lits)
          have hres_ent : s.cdcl.f0.EntailsClause (cnfClause res) :=
            entails_dedupLits (entails_resolve hent' (hinv.db_sound cid c hget))
          have hres_trl : ∀ x ∈ res, ∃ (j : Nat) (_hj : j < s.cdcl.trail.size),
              s.cdcl.trail[j] = litNeg x ∧ (stateLevel s.cdcl x = s.cdcl.level → j < i) := by
            intro x hx
            rcases List.mem_append.mp (mem_dedupLits_iff.mp hx) with hx1 | hx2
            · exact hkeep x hx1
            · rw [List.mem_filter, bne_iff_ne] at hx2
              have hnp : litNeg np = p := by simp [np]
              rw [hnp] at hx2
              obtain ⟨j0, hj0, hj0lt, hj0eq, _⟩ := hall x hx2.1 hx2.2
              exact ⟨j0, hj0, hj0eq, fun _ => hj0lt⟩
          have hp_not_res : p ∉ res := by
            intro hp_r
            have hm := mem_dedupLits_iff.mp hp_r
            unfold resolveOn at hm
            rcases List.mem_append.mp hm with h1 | h2
            · exact hp_not_cl (List.mem_filter.mp h1).1
            · rw [List.mem_filter, bne_iff_ne, show litNeg np = p by simp [np]] at h2
              exact h2.2 rfl
          have hups' : ∀ u ∈ (if clauseSubset res c.lits then
              { cid := cid, pivot := p, newLits := res } :: ups else ups),
              OtfsValidAt s s.cdcl.level u := by
            by_cases hsub : clauseSubset res c.lits = true
            · simp only [hsub, ↓reduceIte, List.mem_cons]
              intro u hu
              rcases hu with rfl | hu_old
              · refine ⟨hres_ent, fun x hx => ?_, c, hget, hng, hpmem, hp_not_res, hplvl,
                  (clauseSubset_iff res c.lits).mp hsub⟩
                obtain ⟨j, hj, hjeq, _⟩ := hres_trl x hx
                exact trail_mem_iff_exists.mpr ⟨j, hj, hjeq⟩
              · exact hups u hu_old
            · have hsubf : clauseSubset res c.lits = false := Bool.eq_false_iff.mpr hsub
              simp only [hsubf, Bool.false_eq_true, ↓reduceIte]
              exact hups
          exact ih (Nat.le_of_lt hi') res _ hres_ent hres_trl hups' |>
            fun ⟨h1, h2, h3, h4, h5⟩ =>
              ⟨h1, h2, h3, fun _ => h4 (dedupLits_ne_nil (hne_step _)), h5⟩
      · rw [ite_eq_right hres]
        refine ih (Nat.le_of_lt hi') cl' ups hent' (fun x hx => ?_) hups |>
          fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, fun hne => h4 (dedupLits_ne_nil hne), h5⟩
        obtain ⟨j, hj, hjeq, hjlt⟩ := htrl' x hx
        refine ⟨j, hj, hjeq, fun hlvl => ?_⟩
        have hji : j ≠ i := by
          intro heq
          subst heq
          have hnp_eq : x = np := by dsimp only [np, p]; rw [hjeq, litNeg_litNeg]
          have hnp_mem : np ∈ cl' := hnp_eq ▸ hx
          have hpl : stateLevel s.cdcl p = s.cdcl.level := by
            simpa [show stateLevel s.cdcl p = stateLevel s.cdcl x from by
              dsimp only [p]; rw [hjeq, stateLevel_litNeg]] using hlvl
          have hnd_dec : s.isDecision p = false := by
            by_cases hd : s.isDecision p = true
            · exfalso
              have hall_eq : ∀ y ∈ cl', (stateLevel s.cdcl y == s.cdcl.level) = true → y = np := by
                intro y hy hyl
                obtain ⟨jy, hjy, hjyeq, hjylt⟩ := htrl' y hy
                have hyl' : stateLevel s.cdcl y = s.cdcl.level := by simpa using hyl
                have hleq : stateLevel s.cdcl s.cdcl.trail[jy] =
                    stateLevel s.cdcl (s.cdcl.trail[j]'hi') := by
                  rw [hjyeq, stateLevel_litNeg, hyl', hpl]
                have hle_ij := hinv.dec_earliest jy j hjy hi' hleq hd
                have hjy_eq : jy = j := by have := hjylt hyl'; omega
                subst hjy_eq; dsimp only [np, p]; rw [hjyeq, litNeg_litNeg]
              exact hcnt (filter_nodup_singleton_le_one hnd hall_eq)
            · exact Bool.eq_false_iff.mpr hd
          exact hres (by simp [hnp_mem, hpl, hnd_dec])
        have := hjlt hlvl; omega

/-- **End-to-end 1UIP + OTFS conflict analysis soundness** under `ChronoTrailInv`:
learns an `f0`-entailed 1UIP clause with `≤ 1` literal at `s.cdcl.level` and certifies every
OTFS database update `u ∈ out.otfs`. -/
theorem chronoAnalyze1UIP_sound {s : ChronoState} (hinv : ChronoTrailInv s) {confl : List Nat}
    (hconfl : s.cdcl.f0.EntailsClause (cnfClause confl))
    (hfals : ∀ l ∈ confl, litNeg l ∈ s.cdcl.trail.toList) :
    let out := chronoAnalyze1UIP s confl
    s.cdcl.f0.EntailsClause (cnfClause out.learned) ∧
    (∀ x ∈ out.learned, litNeg x ∈ s.cdcl.trail.toList) ∧
    (0 < s.cdcl.level → countAtLevel s.cdcl out.learned s.cdcl.level ≤ 1 ∧
      (confl ≠ [] → out.learned ≠ [])) ∧
    (s.cdcl.level = 0 → out.learned = [] ∧ s.cdcl.f0.Unsat) ∧
    (∀ u ∈ out.otfs, OtfsValidAt s s.cdcl.level u) := by
  by_cases hl0 : s.cdcl.level = 0
  · have hunsat := chronoUnsat_of_conflict hinv hl0 hconfl hfals
    have heq : chronoAnalyze1UIP s confl = { learned := [], otfs := [] } := by
      simp [chronoAnalyze1UIP, hl0]
    rw [heq]; dsimp only
    refine ⟨?_, by simp, fun h => by omega, fun _ => ⟨rfl, hunsat⟩, by simp⟩
    rw [cnfClause_nil]
    exact CNF.entails_clause_def.mpr fun α hα => absurd hα (CNF.unsat_iff_not_sat.mp hunsat α)
  · have hlpos : 0 < s.cdcl.level := Nat.pos_of_ne_zero hl0
    have hl0f : (s.cdcl.level == 0) = false := beq_false_of_ne hl0
    have hinit : ∀ x ∈ dedupLits confl, ∃ (j : Nat) (_hj : j < s.cdcl.trail.size),
        s.cdcl.trail[j] = litNeg x ∧ (stateLevel s.cdcl x = s.cdcl.level → j < s.cdcl.trail.size) :=
      fun x hx =>
        let ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp (hfals x (mem_dedupLits_iff.mp hx))
        ⟨j, hj, hjeq, fun _ => hj⟩
    have haux := chronoAnalyze1UIPAux_inv hinv hlpos s.cdcl.trail.size (Nat.le_refl _)
      (dedupLits confl) [] (entails_dedupLits hconfl) hinit (fun _ h => by cases h)
    have heq : chronoAnalyze1UIP s confl =
        chronoAnalyze1UIPAux s s.cdcl.trail.size (dedupLits confl) [] := by
      simp [chronoAnalyze1UIP, hl0f]
    rw [← heq] at haux
    exact ⟨haux.1, fun x hx => let ⟨j, hj, heq⟩ := haux.2.1 x hx;
      trail_mem_iff_exists.mpr ⟨j, hj, heq⟩,
      fun _ => ⟨haux.2.2.1, fun hne => haux.2.2.2.1 (dedupLits_ne_nil hne)⟩,
      fun h => absurd h hl0, haux.2.2.2.2⟩

theorem otfsUpdate_unused_after_backtrack {s : ChronoState} (hinv : ChronoTrailInv s)
    {targetLevel : Nat} (hlt : targetLevel < s.cdcl.level) {u : OtfsUpdate}
    (hu : OtfsValidAt s s.cdcl.level u) :
    ∀ k (hk : k < (chronoBacktrack s targetLevel).cdcl.trail.size),
      stateReason (chronoBacktrack s targetLevel).cdcl
        (chronoBacktrack s targetLevel).cdcl.trail[k] ≠ .large u.cid := by
  intro k hk hrsn
  let sb := chronoBacktrack s targetLevel
  have hmem : sb.cdcl.trail[k] ∈ sb.cdcl.trail.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem hk)
  change sb.cdcl.trail[k] ∈ (s.cdcl.trail.toList.filter _ ).toArray.toList at hmem
  rw [Array.mem_toList_iff, List.mem_toArray, List.mem_filter] at hmem
  obtain ⟨k0, hk0, hk0eq⟩ := trail_mem_iff_exists.mp hmem.1
  have hlev_k : stateLevel s.cdcl s.cdcl.trail[k0] ≤ targetLevel := by
    have hmem2 := hmem.2
    rw [← hk0eq] at hmem2
    simpa using hmem2
  have hrsn0 : stateReason s.cdcl s.cdcl.trail[k0] = .large u.cid := by
    change stateReason s.cdcl sb.cdcl.trail[k] = .large u.cid at hrsn
    rwa [← hk0eq] at hrsn
  have hrd := hinv.reason_dag k0 hk0; dsimp only at hrd
  rw [hrsn0] at hrd
  obtain ⟨c0, hc0_get, _, _, hall⟩ := hrd
  obtain ⟨oldC, hold_get, _, hp_mem, _, hp_lvl, _⟩ := hu.2.2
  rw [hold_get] at hc0_get
  simp only [Option.some.injEq] at hc0_get
  subst hc0_get
  have hp_ne : u.pivot ≠ s.cdcl.trail[k0] := by
    intro heq
    have := congrArg (stateLevel s.cdcl) heq
    rw [hp_lvl] at this
    omega
  obtain ⟨_, _, _, _, hle, _⟩ := hall u.pivot hp_mem hp_ne
  omega

private theorem applyOtfsUpdate_preserves_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    {u : OtfsUpdate} (hent : s.cdcl.f0.EntailsClause (cnfClause u.newLits))
    (hnonact : ∀ k (hk : k < s.cdcl.trail.size),
      stateReason s.cdcl s.cdcl.trail[k] ≠ .large u.cid) :
    let s' := { s with cdcl := { s.cdcl with clauses := applyOtfsUpdate s.cdcl.clauses u } }
    ChronoTrailInv s' ∧ s'.cdcl.f0 = s.cdcl.f0 ∧
    (∀ k (hk : k < s'.cdcl.trail.size) (cid : Nat),
      stateReason s'.cdcl s'.cdcl.trail[k] = .large cid → cid ≠ u.cid) := by
  let s' : ChronoState :=
    { s with cdcl := { s.cdcl with clauses := applyOtfsUpdate s.cdcl.clauses u } }
  have hdb : ∀ (cid : Nat) (c : Clause),
      s'.cdcl.clauses[cid]? = some (some c) → s.cdcl.f0.EntailsClause (cnfClause c.lits) := by
    intro cid c hget
    change (applyOtfsUpdate s.cdcl.clauses u)[cid]? = some (some c) at hget
    unfold applyOtfsUpdate at hget
    cases huc : s.cdcl.clauses[u.cid]? with
    | none => rw [huc] at hget; exact hinv.db_sound cid c hget
    | some opt =>
      cases opt with
      | none => rw [huc] at hget; exact hinv.db_sound cid c hget
      | some oldC =>
        rw [huc, getElem?_setIfInBounds] at hget
        split at hget
        · simp only [Option.some.injEq] at hget; subst hget; exact hent
        · exact hinv.db_sound cid c hget
  have hf0 : s'.cdcl.f0 = s.cdcl.f0 := rfl
  have htrl : s'.cdcl.trail = s.cdcl.trail := rfl
  have hsl : ∀ x, stateLevel s'.cdcl x = stateLevel s.cdcl x := fun _ => rfl
  have hsr : ∀ x, stateReason s'.cdcl x = stateReason s.cdcl x := fun _ => rfl
  have hinv' : ChronoTrailInv s' :=
    ⟨hinv.vars_nodup, hinv.levels_le, hinv.dec_sync, hinv.dec_earliest, hdb, hinv.units_sound,
      reasonDagInv_withClauses hinv.reason_dag s'.cdcl.clauses (fun i hi cid c hrsn hget _ => by
        have hne : cid ≠ u.cid := fun h => hnonact i hi (h ▸ hrsn)
        change (applyOtfsUpdate s.cdcl.clauses u)[cid]? = some (some c)
        unfold applyOtfsUpdate
        cases huc : s.cdcl.clauses[u.cid]? with
        | none => exact hget
        | some opt =>
          cases opt with
          | none => exact hget
          | some _ => rw [getElem?_setIfInBounds, ite_eq_right (by simp [hne])]; exact hget),
      hinv.inconsistent_sound⟩
  exact ⟨hinv', rfl, fun k hk cid hrsn heq => hnonact k hk (heq ▸ hrsn)⟩

/-- Applying OTFS database clause updates after chronological backtrack (leaving `level < oldLvl`)
preserves `ChronoTrailInv` and `ReasonDagInv`. -/
theorem applyOtfsUpdates_preserves_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    (ups : List OtfsUpdate)
    (hent : ∀ u ∈ ups, s.cdcl.f0.EntailsClause (cnfClause u.newLits))
    (hnonact : ∀ u ∈ ups, ∀ k (hk : k < s.cdcl.trail.size),
      stateReason s.cdcl s.cdcl.trail[k] ≠ .large u.cid) :
    let s' := { s with cdcl := { s.cdcl with clauses := applyOtfsUpdates s.cdcl.clauses ups } }
    ChronoTrailInv s' ∧ s'.cdcl.f0 = s.cdcl.f0 := by
  induction ups generalizing s with
  | nil => exact ⟨hinv, rfl⟩
  | cons u rest ih =>
    have h1 := applyOtfsUpdate_preserves_inv hinv (hent u List.mem_cons_self)
      (hnonact u List.mem_cons_self)
    have hih := ih h1.1
      (fun w hw => h1.2.1 ▸ hent w (List.mem_cons_of_mem u hw))
      (fun w hw k hk => hnonact w (List.mem_cons_of_mem u hw) k hk)
    exact ⟨hih.1, hih.2.trans h1.2.1⟩

theorem chronoAddLearnedClause_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    {lits : List Nat} {glue : Nat} (hent : s.cdcl.f0.EntailsClause (cnfClause lits)) :
    ChronoTrailInv (chronoAddLearnedClause s lits glue) ∧
      (chronoAddLearnedClause s lits glue).cdcl.f0 = s.cdcl.f0 := by
  have hdb : ∀ (cid : Nat) (c : Clause),
      (addLearnedClause s.cdcl lits glue).clauses[cid]? = some (some c) →
      s.cdcl.f0.EntailsClause (cnfClause c.lits) := fun cid c hget => by
    simp only [addLearnedClause, Array.getElem?_push] at hget
    split at hget
    · simp only [Option.some.injEq] at hget; subst hget; exact hent
    · exact hinv.db_sound cid c hget
  exact ⟨⟨hinv.vars_nodup, hinv.levels_le, hinv.dec_sync, hinv.dec_earliest, hdb,
    hinv.units_sound,
    reasonDagInv_withClauses hinv.reason_dag (addLearnedClause s.cdcl lits glue).clauses
      (fun _ _ cid c _ hget _ => by
        have hne : cid ≠ s.cdcl.clauses.size :=
          Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp hget).1
        simp only [addLearnedClause, Array.getElem?_push, hne, ↓reduceIte]; exact hget),
    hinv.inconsistent_sound⟩, rfl⟩

/-- Soundness of recursive lexicographic `(level, trailPos)` minimization under `ChronoTrailInv`. -/
theorem chronoMinimize_sound {s : ChronoState} (hinv : ChronoTrailInv s) {c : List Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause c))
    (hfals : ∀ l ∈ c, litNeg l ∈ s.cdcl.trail.toList)
    (maxDepth : Nat) :
    s.cdcl.f0.EntailsClause (cnfClause (chronoMinimize s maxDepth c)) ∧
    (∀ l ∈ chronoMinimize s maxDepth c, litNeg l ∈ s.cdcl.trail.toList) ∧
    (∀ l ∈ chronoMinimize s maxDepth c, l ∈ c) := by
  have hm := minimize_worklist_sound (MinBaseInv.ofCdcl hinv.toLazy) hent
    (removableInv_of_ofCdcl s.cdcl #[] c) hfals maxDepth
  unfold chronoMinimize
  dsimp only at hm ⊢
  rw [hm.2.1] at hm
  exact ⟨hm.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2.1⟩

/-- Soundness of block shrinking (`shrink.c`, `FailedLit`) under `ChronoTrailInv`. -/
theorem chronoShrink_sound {s : ChronoState} (hinv : ChronoTrailInv s) {c : List Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause c))
    (hfals : ∀ l ∈ c, litNeg l ∈ s.cdcl.trail.toList)
    (alwaysMin resolveLarge : Bool) (maxDepth : Nat) :
    s.cdcl.f0.EntailsClause (cnfClause (chronoShrink s alwaysMin resolveLarge maxDepth c)) ∧
    (∀ l ∈ chronoShrink s alwaysMin resolveLarge maxDepth c, litNeg l ∈ s.cdcl.trail.toList) := by
  have hs := shrink_clause_sound (MinBaseInv.ofCdcl hinv.toLazy) hent
    (removableInv_of_ofCdcl s.cdcl #[] c) hfals alwaysMin resolveLarge maxDepth
  unfold chronoShrink
  dsimp only at hs ⊢
  rw [hs.2.1] at hs
  exact ⟨hs.2.2.2.1, hs.2.2.2.2.2.1⟩

private theorem mem_backtrackFilter_of_mem_le {s : ChronoState} {targetLevel l : Nat}
    (hl : l ∈ s.cdcl.trail.toList) (hle : stateLevel s.cdcl l ≤ targetLevel) :
    l ∈ (backtrackFilter s.cdcl targetLevel).trail.toList := by
  rw [Array.mem_toList_iff]
  simp only [backtrackFilter, List.mem_toArray, List.mem_filter, decide_eq_true_eq]
  exact ⟨hl, hle⟩

private theorem litStatus_none_after_backtrackFilter {s : ChronoState} (hinv : ChronoTrailInv s)
    {targetLevel uip : Nat} (hfals : litNeg uip ∈ s.cdcl.trail.toList)
    (hgt : targetLevel < stateLevel s.cdcl uip) :
    litStatus (backtrackFilter s.cdcl targetLevel).trail uip = none := by
  rw [litStatus_eq_none, Array.mem_toList_iff, Array.mem_toList_iff]
  simp only [backtrackFilter, List.mem_toArray, List.mem_filter, decide_eq_true_eq, not_and]
  refine ⟨fun huip hle => ?_, fun _ hle => ?_⟩
  · obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hfals
    obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp huip
    have hij := hinv.vars_nodup i j hi hj (by rw [hieq, hjeq, litVar_litNeg])
    subst hij
    exact absurd hjeq (hieq ▸ litNeg_ne_self uip)
  · rw [stateLevel_litNeg] at hle
    omega

/-- End-to-end invariant preservation (`ChronoTrailInv` + `ReasonDagInv` + `f0`) across
out-of-order `chronoBacktrack`, OTFS clause strengthening, learned clause insertion, and
out-of-order `chronoAssignUip`. -/
theorem chronoConflictStep_preserves_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    {targetLevel uipLevel : Nat} {ups : List OtfsUpdate}
    {learned : List Nat} {glue uip : Nat}
    (hle_ut : uipLevel ≤ targetLevel) (hlt_ts : targetLevel < s.cdcl.level)
    (hlearned_ent : s.cdcl.f0.EntailsClause (cnfClause learned))
    (hlearned_fals : ∀ x ∈ learned, litNeg x ∈ s.cdcl.trail.toList)
    (huip_mem : uip ∈ learned) (huip_lvl : stateLevel s.cdcl uip = s.cdcl.level)
    (hother_lvl : ∀ x ∈ learned, x ≠ uip → stateLevel s.cdcl x ≤ uipLevel)
    (hups : ∀ u ∈ ups, OtfsValidAt s s.cdcl.level u) :
    let s' := chronoConflictStep s targetLevel ups learned glue uip uipLevel
    ChronoTrailInv s' ∧ s'.cdcl.f0 = s.cdcl.f0 := by
  let s1 := chronoBacktrack s targetLevel
  have h1 := chronoBacktrack_preserves_inv hinv targetLevel
  have hnonact : ∀ u ∈ ups, ∀ k (hk : k < s1.cdcl.trail.size),
      stateReason s1.cdcl s1.cdcl.trail[k] ≠ .large u.cid :=
    fun u hu k hk => otfsUpdate_unused_after_backtrack hinv hlt_ts (hups u hu) k hk
  let s2 : ChronoState :=
    { s1 with cdcl := { s1.cdcl with clauses := applyOtfsUpdates s1.cdcl.clauses ups } }
  have h2 := applyOtfsUpdates_preserves_inv h1.1 ups
    (fun u hu => h1.2 ▸ (hups u hu).1) hnonact
  have h2_f0 : s2.cdcl.f0 = s.cdcl.f0 := h2.2.trans h1.2
  have h2_trl : s2.cdcl.trail = (backtrackFilter s.cdcl targetLevel).trail := rfl
  have h2_lvl : s2.cdcl.level = targetLevel := by
    change Nat.min s.cdcl.level targetLevel = targetLevel
    exact Nat.min_eq_right (Nat.le_of_lt hlt_ts)
  let newCid := s2.cdcl.clauses.size
  let s3 := chronoAddLearnedClause s2 learned glue
  have h3 := chronoAddLearnedClause_inv h2.1 (lits := learned) (glue := glue)
    (h2_f0 ▸ hlearned_ent)
  have h3_f0 : s3.cdcl.f0 = s.cdcl.f0 := h3.2.trans h2_f0
  have h3_trl : s3.cdcl.trail = (backtrackFilter s.cdcl targetLevel).trail := rfl
  have h3_lvl : s3.cdcl.level = targetLevel := h2_lvl
  have hun : litStatus s3.cdcl.trail uip = none := by
    rw [h3_trl]
    exact litStatus_none_after_backtrackFilter hinv (hlearned_fals uip huip_mem) (by omega)
  have hnew_get : s3.cdcl.clauses[newCid]? =
      some (some { lits := learned, redundant := true, glue := glue }) := by
    simp [s3, chronoAddLearnedClause, addLearnedClause, newCid]
  have hr_ok : ReasonOk s3.cdcl uip uipLevel
      (if learned.length ≤ 1 && uipLevel == 0 then .unit else .large newCid) := by
    by_cases hunit : (learned.length ≤ 1 && uipLevel == 0) = true
    · simp only [hunit, ↓reduceIte, ReasonOk]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hunit
      refine ⟨hunit.2, ?_⟩
      rw [h3_f0]
      have hsub_uip : ∀ x ∈ learned, x ∈ [uip] := fun x hx => by
        cases learned with
        | nil => cases hx
        | cons a rest =>
          cases rest with
          | nil =>
            have ha1 : x = a := by simpa using hx
            have ha2 : uip = a := by simpa using huip_mem
            simp [ha1, ha2]
          | cons _ _ => simp at hunit
      exact CNF.entails_clause_def.mpr fun α hα =>
        sat_clause_of_subset hsub_uip (CNF.entails_clause_def.mp hlearned_ent α hα)
    · have hunitf : (learned.length ≤ 1 && uipLevel == 0) = false :=
        Bool.eq_false_iff.mpr hunit
      simp only [hunitf, Bool.false_eq_true, ↓reduceIte, ReasonOk]
      refine ⟨{ lits := learned, redundant := true, glue := glue },
        hnew_get, by simp, huip_mem, fun x hx hne => ?_⟩
      have hx_le := Nat.le_trans (hother_lvl x hx hne) hle_ut
      have hmem_s3 : litNeg x ∈ s3.cdcl.trail.toList := by
        rw [h3_trl]
        exact mem_backtrackFilter_of_mem_le (hlearned_fals x hx)
          (by simpa [stateLevel_litNeg] using hx_le)
      obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp hmem_s3
      have hle_u : stateLevel s3.cdcl x ≤ uipLevel := by
        change stateLevel s.cdcl x ≤ uipLevel
        exact hother_lvl x hx hne
      refine ⟨j, hj, hjeq, hle_u, ?_⟩
      by_cases hlt_lvl : stateLevel s3.cdcl x < uipLevel
      · exact Or.inl hlt_lvl
      · exact Or.inr ⟨by omega, hj⟩
  have hne_dec :
      (if learned.length ≤ 1 && uipLevel == 0 then Reason.unit else Reason.large newCid) ≠
        .decision := by
    split <;> simp
  have h4 := chronoAssignUip_inv h3.1 hun (by rw [h3_lvl]; exact hle_ut) hne_dec hr_ok
  exact ⟨h4.1, h4.2.trans h3_f0⟩

private theorem backtrackLevel_le_of_mem_lt {s : CdclState} {learned : List Nat} {x : Nat}
    (hx : x ∈ learned) (hlt : stateLevel s x < s.level) :
    stateLevel s x ≤ backtrackLevel s learned := by
  have hgen : ∀ (xs : List Nat) (init : Nat),
      init ≤ xs.foldl (fun acc l =>
        let lvl := stateLevel s l; if lvl < s.level then Nat.max acc lvl else acc) init ∧
      (x ∈ xs →
        stateLevel s x ≤ xs.foldl (fun acc l =>
          let lvl := stateLevel s l; if lvl < s.level then Nat.max acc lvl else acc) init) := by
    intro xs
    induction xs with
    | nil => intro init; simp
    | cons y ys ih =>
      intro init
      simp only [List.foldl_cons, List.mem_cons]
      by_cases hy : stateLevel s y < s.level
      · rw [ite_eq_left hy]
        have hstep := ih (Nat.max init (stateLevel s y))
        refine ⟨Nat.le_trans (Nat.le_max_left _ _) hstep.1, fun hm => ?_⟩
        rcases hm with rfl | hys
        · exact Nat.le_trans (Nat.le_max_right _ _) hstep.1
        · exact hstep.2 hys
      · rw [ite_eq_right hy]
        have hstep := ih init
        refine ⟨hstep.1, fun hm => ?_⟩
        rcases hm with rfl | hys
        · exact absurd hlt hy
        · exact hstep.2 hys
  exact (hgen learned 0).2 hx

private theorem chronoAnalyze1UIPAux_nodup (s : ChronoState) :
    ∀ (k : Nat) (cl : List Nat) (ups : List OtfsUpdate),
      (chronoAnalyze1UIPAux s k cl ups).learned.Nodup
  | 0, cl, ups => nodup_dedupLits cl
  | k + 1, cl, ups => by
    rw [chronoAnalyze1UIPAux]; dsimp only
    split
    · exact nodup_dedupLits cl
    · split
      · split
        · cases stateReason s.cdcl _ with
          | decision | unit => dsimp only; exact nodup_dedupLits cl
          | binary _ => dsimp only; exact chronoAnalyze1UIPAux_nodup s k _ ups
          | large cid =>
            dsimp only
            cases s.cdcl.clauses[cid]? with
            | none => exact nodup_dedupLits cl
            | some opt =>
              cases opt with
              | none => exact nodup_dedupLits cl
              | some _ => exact chronoAnalyze1UIPAux_nodup s k _ _
        · exact chronoAnalyze1UIPAux_nodup s k _ ups
      · exact chronoAnalyze1UIPAux_nodup s k _ ups

/-- Direct bridge from `chronoAnalyze1UIP` (plus subset-preserving `chronoMinimize` /
`chronoShrink`) into `chronoConflictStep_preserves_inv` at any chronological `targetLevel` with
`backtrackLevel s.cdcl learned ≤ targetLevel < s.cdcl.level`. -/
theorem chronoAnalyzeAndStep_preserves_inv {s : ChronoState} (hinv : ChronoTrailInv s)
    (hpos : 0 < s.cdcl.level) {confl learned : List Nat}
    (hconfl : s.cdcl.f0.EntailsClause (cnfClause confl))
    (hfals : ∀ l ∈ confl, litNeg l ∈ s.cdcl.trail.toList)
    (hsub : ∀ l ∈ learned, l ∈ (chronoAnalyze1UIP s confl).learned)
    (hle : s.cdcl.f0.EntailsClause (cnfClause learned))
    {uip targetLevel glue : Nat}
    (huip_mem : uip ∈ learned) (huip_lvl : stateLevel s.cdcl uip = s.cdcl.level)
    (hle_bt : backtrackLevel s.cdcl learned ≤ targetLevel)
    (hlt_ts : targetLevel < s.cdcl.level) :
    let uipLevel := backtrackLevel s.cdcl learned
    let s' := chronoConflictStep s targetLevel (chronoAnalyze1UIP s confl).otfs
      learned glue uip uipLevel
    ChronoTrailInv s' ∧ s'.cdcl.f0 = s.cdcl.f0 := by
  have ha := chronoAnalyze1UIP_sound hinv hconfl hfals
  dsimp only at ha
  have hcnt1 := (ha.2.2.1 hpos).1
  have hnd_out : (chronoAnalyze1UIP s confl).learned.Nodup := by
    have hposf : (s.cdcl.level == 0) = false := beq_false_of_ne (Nat.ne_of_gt hpos)
    simpa [chronoAnalyze1UIP, hposf] using
      chronoAnalyze1UIPAux_nodup s s.cdcl.trail.size (dedupLits confl) []
  have hlt_other : ∀ x ∈ learned, x ≠ uip → stateLevel s.cdcl x < s.cdcl.level := by
    intro x hx hne
    have hle_s : stateLevel s.cdcl x ≤ s.cdcl.level := by
      obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp (ha.2.1 x (hsub x hx))
      simpa [hjeq, stateLevel_litNeg] using hinv.levels_le j hj
    refine Nat.lt_of_le_of_ne hle_s fun heq => ?_
    have hgt := mem_two_filter_length_gt_one
      (P := fun l => stateLevel s.cdcl l == s.cdcl.level)
      hne.symm (by simp [huip_lvl]) (by simp [heq]) hnd_out (hsub uip huip_mem) (hsub x hx)
    unfold countAtLevel at hcnt1
    omega
  exact chronoConflictStep_preserves_inv hinv hle_bt hlt_ts hle
    (fun x hx => ha.2.1 x (hsub x hx)) huip_mem huip_lvl
    (fun x hx hne => backtrackLevel_le_of_mem_lt hx (hlt_other x hx hne))
    ha.2.2.2.2

end LeanQbe.T.Examples.Kissat.Ref
