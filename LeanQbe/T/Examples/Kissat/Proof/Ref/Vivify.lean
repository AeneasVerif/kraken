/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Vivify
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Subsume
public import LeanQbe.T.Examples.Kissat.Proof.Ref.FailedLit

/-!
# Soundness Proofs for `Vivify`

Extracted pure-Lean proofs for `Vivify` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Failed-literal probing and assumption-entailment equivalences -/

/-- Assumed negated prefix unsatisfiability is equivalent to clause entailment:
`(f ++ unitsCnf (pref.map litNeg)).Unsat ↔ f.EntailsClause (cnfClause pref)`. -/
theorem unsat_append_units_iff (f : CNF Nat) (pref : List Nat) :
    (f ++ unitsCnf (pref.map litNeg)).Unsat ↔ f.EntailsClause (cnfClause pref) := by
  rw [CNF.unsat_iff_not_sat, CNF.entails_clause_def]
  constructor
  · intro hnot α hα
    exact Classical.byContradiction fun hnpref => by
      apply hnot α
      rw [CNF.sat_append, sat_unitsCnf_iff]
      refine ⟨hα, fun u hu => ?_⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
      exact (sat_cnfClause_litNeg_iff α l).mpr fun hsl =>
        hnpref (sat_clause_of_subset (fun x hx => by
          simp only [List.mem_singleton] at hx; rw [hx]; exact hl) hsl)
  · intro hent α hα
    rw [CNF.sat_append, sat_unitsCnf_iff] at hα
    obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α pref).mp (hent α hα.1)
    have hneg := hα.2 (litNeg l) (List.mem_map.mpr ⟨l, hl, rfl⟩)
    exact (sat_cnfClause_litNeg_iff α l).mp hneg ((sat_cnfClause_singleton α l).mpr hsat)

/-- Assumed negated prefix entailing unit `[lm]` is equivalent to entailing `pref ++ [lm]`. -/
theorem entails_unit_append_iff (f : CNF Nat) (pref : List Nat) (lm : Nat) :
    (f ++ unitsCnf (pref.map litNeg)).EntailsClause (cnfClause [lm]) ↔
      f.EntailsClause (cnfClause (pref ++ [lm])) := by
  simp only [CNF.entails_clause_def, CNF.sat_append, sat_unitsCnf_iff]
  constructor
  · intro h α hα
    by_cases hpref : (cnfClause pref).Sat α
    · exact sat_clause_of_subset (fun x hx => List.mem_append_left [lm] hx) hpref
    · have hun : ∀ u ∈ pref.map litNeg, (cnfClause [u]).Sat α := fun u hu => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
        exact (sat_cnfClause_litNeg_iff α l).mpr fun hsl =>
          hpref (sat_clause_of_subset (fun x hx => by
            simp only [List.mem_singleton] at hx; rw [hx]; exact hl) hsl)
      exact sat_clause_of_subset (fun x hx => List.mem_append_right pref hx) (h α ⟨hα, hun⟩)
  · intro h α ⟨hα, hun⟩
    obtain ⟨x, hx, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
    rcases List.mem_append.mp hx with hp | hm
    · have hneg := hun (litNeg x) (List.mem_map.mpr ⟨x, hp, rfl⟩)
      exact absurd ((sat_cnfClause_singleton α x).mpr hsat)
        ((sat_cnfClause_litNeg_iff α x).mp hneg)
    · simp only [List.mem_singleton] at hm; subst hm
      exact (sat_cnfClause_singleton α x).mpr hsat

/-- Adding `¬l` yielding `⊥` is equivalent to entailing unit `l`. -/
theorem unsat_add_litNeg_iff (f : CNF Nat) (l : Nat) :
    (f.add (cnfClause [litNeg l])).Unsat ↔ f.EntailsClause (cnfClause [l]) := by
  have hun := unsat_append_units_iff f [l]
  have heq : ∀ α : Nat → Bool,
      (f.add (cnfClause [litNeg l])).Sat α ↔ (f ++ unitsCnf ([l].map litNeg)).Sat α := fun α => by
    simp only [CNF.sat_add, CNF.sat_append, sat_unitsCnf_iff, List.map_cons, List.map_nil,
      List.mem_singleton, forall_eq]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [cnf_unsat_iff_of_sat_iff heq]
  exact hun

/-- **Failed-literal unit-addition equivalence**: if `f ∧ ¬l ⊢ ⊥`, adding unit `(l)` preserves
both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem failedLit_add_equiv {f : CNF Nat} {l : Nat}
    (hfail : (f.add (cnfClause [litNeg l])).Unsat) :
    (∀ α : Nat → Bool, (f.add (cnfClause [l])).Sat α ↔ f.Sat α) ∧
      ((f.add (cnfClause [l])).Unsat ↔ f.Unsat) :=
  entailed_del_equiv ((unsat_add_litNeg_iff f l).mp hfail)

/-- **Failed-literal clause-strengthening equivalence**: if `f ∧ ¬l ⊢ ⊥` and `¬l ∈ c`,
dropping `¬l` from `c` in `f.add c` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem failedLit_drop_equiv {f : CNF Nat} {l : Nat} {c : List Nat}
    (hfail : (f.add (cnfClause [litNeg l])).Unsat) (_hmem : litNeg l ∈ c) :
    (∀ α : Nat → Bool,
      (f.add (cnfClause (removeLit c (litNeg l)))).Sat α ↔ (f.add (cnfClause c)).Sat α) ∧
      ((f.add (cnfClause (removeLit c (litNeg l)))).Unsat ↔ (f.add (cnfClause c)).Unsat) := by
  have hent_l := (unsat_add_litNeg_iff f l).mp hfail
  have hsat : ∀ α : Nat → Bool,
      (f.add (cnfClause (removeLit c (litNeg l)))).Sat α ↔ (f.add (cnfClause c)).Sat α := by
    intro α
    simp only [CNF.sat_add]
    constructor
    · rintro ⟨hc', hf⟩
      exact ⟨sat_clause_of_subset (removeLit_subset c (litNeg l)) hc', hf⟩
    · rintro ⟨hc, hf⟩
      refine ⟨?_, hf⟩
      have hl_sat := CNF.entails_clause_def.mp hent_l α hf
      obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α c).mp hc
      have hne : x ≠ litNeg l := by
        rintro rfl
        exact (sat_cnfClause_litNeg_iff α l).mp ((sat_cnfClause_singleton α _).mpr hxs) hl_sat
      exact (clause_sat_cnfClause_iff α _).mpr ⟨x, mem_removeLit_iff.mpr ⟨hx, hne⟩, hxs⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **Failed-literal probing soundness**: whenever `probeFailedLit fuel cs l = true`,
`cnfOfClauses cs` entails `[l]` and `(cnfOfClauses cs).add [¬l]` is unsat. -/
theorem probeFailedLit_sound {fuel : Nat} {cs : List (List Nat)} {l : Nat}
    (hp : probeFailedLit fuel cs l = true) :
    (cnfOfClauses cs).EntailsClause (cnfClause [l]) := by
  have h0 := initState_inv (cnfOfClauses cs)
  have hpi := propagateAll_inv (fuel := fuel) h0.1
  unfold probeFailedLit at hp
  cases hprop0 : propagateAll fuel (initState (cnfOfClauses cs)) with
  | outOfFuel s0 => simp [hprop0] at hp
  | conflict confl s0 =>
    rw [hprop0] at hpi
    obtain ⟨hinv0, hf0, hl0, hconfl, hfals, _⟩ := hpi
    have hunsat : (cnfOfClauses cs).Unsat := by
      have := unsat_of_conflict hinv0 (by simp [hl0, initState]) hconfl hfals
      rwa [hf0, h0.2] at this
    exact CNF.entails_clause_def.mpr fun α hα => absurd hα (CNF.unsat_iff_not_sat.mp hunsat α)
  | ok s0 =>
    rw [hprop0] at hpi hp
    dsimp only at hp
    obtain ⟨hinv0, hf0, hl0, _⟩ := hpi
    have hf0' : s0.f0 = cnfOfClauses cs := hf0.trans h0.2
    have hls0 : s0.level = 0 := by simpa [initState] using hl0
    cases hst : litStatus s0.trail (litNeg l) with
    | some b =>
      rw [hst] at hp
      cases b
      · obtain ⟨i, hi, hieq⟩ :=
          trail_mem_iff_exists.mp ((litStatus_eq_some_false hinv0.vars_nodup).mp hst)
        have hlvl_i : stateLevel s0 s0.trail[i] = 0 := by
          have := hinv0.levels_le i hi; omega
        have hent := trailEntailment_level0 hinv0 hi hlvl_i
        rwa [hieq, litNeg_litNeg, hf0'] at hent
      · simp at hp
    | none =>
      rw [hst] at hp; dsimp only at hp
      cases hprop1 : propagateAll fuel (decideLit s0 (litNeg l)) with
      | ok _ => simp [hprop1] at hp
      | outOfFuel _ => simp [hprop1] at hp
      | conflict confl s2 =>
        have hfl := failedLit_sound hinv0 hls0 hst hprop1
        rwa [litNeg_litNeg, hf0'] at hfl

/-- **Executable failed-literal probe equivalence**: adding probed unit `[l]` preserves both
`Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem failedLit_probe_equiv {fuel : Nat} {cs : List (List Nat)} {l : Nat}
    (hp : probeFailedLit fuel cs l = true) :
    (∀ α : Nat → Bool, (cnfOfClauses ([l] :: cs)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses ([l] :: cs)).Unsat ↔ (cnfOfClauses cs).Unsat) := by
  have hent := probeFailedLit_sound hp
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses ([l] :: cs)).Sat α ↔ (cnfOfClauses cs).Sat α := fun α => by
    simp only [cnf_sat_cnfOfClauses_iff, List.mem_cons, forall_eq_or_imp]
    exact ⟨fun h => h.2, fun hcs =>
      ⟨CNF.entails_clause_def.mp hent α ((cnf_sat_cnfOfClauses_iff α cs).mpr hcs), hcs⟩⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- Bridge from `Cdcl.failedLitStep_preserves_inv` to CNF equivalence when a unit is
learned. -/
theorem failedLitStep_equiv {fuel : Nat} {s s' : CdclState} {l u : Nat}
    (hinv : TrailInv s) (hstep : failedLitStep fuel s l = .learnedUnit u s') :
    TrailInv s' ∧ s'.f0 = s.f0 ∧
    (∀ α : Nat → Bool, (s.f0.add (cnfClause [u])).Sat α ↔ s.f0.Sat α) ∧
    ((s.f0.add (cnfClause [u])).Unsat ↔ s.f0.Unsat) := by
  have hp := failedLitStep_preserves_inv hinv l (fuel := fuel)
  rw [hstep] at hp
  have hent : s.f0.EntailsClause (cnfClause [u]) := hp.2.1 ▸ hp.2.2.1
  have heq := entailed_del_equiv hent
  exact ⟨hp.1, hp.2.1, heq.1, heq.2⟩

/-- Bridge from `FailedLit.analyzeFailedLiteralExec_sound` to CNF equivalence for every
emitted unit literal. -/
theorem failedAnalyze_equiv {s : CdclState} (hinv : LazyTrailInv s)
    (hlvl : s.level = 1) {failed : Nat}
    (hf_trl : failed ∈ s.trail.toList) (hf_lvl : stateLevel s failed = 1)
    (hf_dec : stateReason s failed = .decision) {conflict : List Nat}
    (hconfl : s.f0.EntailsClause (cnfClause conflict))
    (hfals : ∀ l ∈ conflict, litNeg l ∈ s.trail.toList)
    {u : Nat} (hu : u ∈ analyzeFailedLiteralExec s failed conflict) :
    (∀ α : Nat → Bool, (s.f0.add (cnfClause [u])).Sat α ↔ s.f0.Sat α) ∧
      ((s.f0.add (cnfClause [u])).Unsat ↔ s.f0.Unsat) :=
  entailed_del_equiv
    (analyzeFailedLiteralExec_sound hinv hlvl hf_trl hf_lvl hf_dec hconfl hfals u hu)

/-! ## 2. Vivification clause strengthening soundness -/

/-- **Vivification conflict strengthening (`CNF Nat`)**: if `(F \ {C}) ∧ ¬l₁ ∧ ... ∧ ¬lₖ ⊢ ⊥`
where `pref ⊆ c`, strengthening `c` to `pref` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem vivify_conflict_equiv {f : CNF Nat} {pref c : List Nat}
    (hsub : ∀ l ∈ pref, l ∈ c) (hunsat : (f ++ unitsCnf (pref.map litNeg)).Unsat) :
    (∀ α : Nat → Bool, (f.add (cnfClause pref)).Sat α ↔ (f.add (cnfClause c)).Sat α) ∧
      ((f.add (cnfClause pref)).Unsat ↔ (f.add (cnfClause c)).Unsat) := by
  have hpref_ent : f.EntailsClause (cnfClause pref) := (unsat_append_units_iff f pref).mp hunsat
  have hc_ent : f.EntailsClause (cnfClause c) :=
    CNF.entails_clause_def.mpr fun α hα =>
      sat_clause_of_subset hsub (CNF.entails_clause_def.mp hpref_ent α hα)
  have hsat : ∀ α : Nat → Bool,
      (f.add (cnfClause pref)).Sat α ↔ (f.add (cnfClause c)).Sat α := fun α =>
    ((entailed_del_equiv hpref_ent).1 α).trans ((entailed_del_equiv hc_ent).1 α).symm
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **Vivification implied-literal strengthening (`CNF Nat`)**: if `(F \ {C}) ∧ ¬l₁ ∧ ... ∧ ¬lₖ`
entails `lₘ` where `pref ⊆ c` and `lm ∈ c`, strengthening `c` to `pref ++ [lm]` preserves both
`Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem vivify_implied_equiv {f : CNF Nat} {pref c : List Nat} {lm : Nat}
    (hsub : ∀ l ∈ pref, l ∈ c) (hlm : lm ∈ c)
    (hent : (f ++ unitsCnf (pref.map litNeg)).EntailsClause (cnfClause [lm])) :
    (∀ α : Nat → Bool,
      (f.add (cnfClause (pref ++ [lm]))).Sat α ↔ (f.add (cnfClause c)).Sat α) ∧
      ((f.add (cnfClause (pref ++ [lm]))).Unsat ↔ (f.add (cnfClause c)).Unsat) := by
  have hpl_ent : f.EntailsClause (cnfClause (pref ++ [lm])) :=
    (entails_unit_append_iff f pref lm).mp hent
  have hpl_sub : ∀ l ∈ pref ++ [lm], l ∈ c := fun l hl => by
    rcases List.mem_append.mp hl with hp | hm
    · exact hsub l hp
    · simp only [List.mem_singleton] at hm; exact hm ▸ hlm
  have hc_ent : f.EntailsClause (cnfClause c) :=
    CNF.entails_clause_def.mpr fun α hα =>
      sat_clause_of_subset hpl_sub (CNF.entails_clause_def.mp hpl_ent α hα)
  have hsat : ∀ α : Nat → Bool,
      (f.add (cnfClause (pref ++ [lm]))).Sat α ↔ (f.add (cnfClause c)).Sat α := fun α =>
    ((entailed_del_equiv hpl_ent).1 α).trans ((entailed_del_equiv hc_ent).1 α).symm
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **Vivification conflict strengthening (clause list)**: replacing `cs[i]` with `pref` when
`(cnfOfClauses (deleteIdx cs i)) ∧ ¬pref ⊢ ⊥` preserves `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem vivify_confl_clauses {cs : List (List Nat)} {i : Nat} {pref : List Nat}
    (hi : i < cs.length) (hsub : ∀ l ∈ pref, l ∈ cs[i])
    (hunsat : ((cnfOfClauses (deleteIdx cs i)) ++ unitsCnf (pref.map litNeg)).Unsat) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i pref)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (replaceIdx cs i pref)).Unsat ↔ (cnfOfClauses cs).Unsat) :=
  sat_cnfOfClauses_replaceIdx_equiv hi
    (fun _ _ hp => sat_clause_of_subset hsub hp)
    (fun α hall =>
      let hget := (sat_cnfOfClauses_iff_getElem α cs).mp hall
      let hdel : (cnfOfClauses (deleteIdx cs i)).Sat α :=
        (sat_cnfOfClauses_deleteIdx_iff α cs i).mpr fun j hj _ => hget j hj
      (((vivify_conflict_equiv hsub hunsat).1 α).mpr
        (CNF.sat_add.mpr ⟨hget i hi, hdel⟩) |> CNF.sat_add.mp).1)

/-- **Vivification implied-literal strengthening (clause list)**: replacing `cs[i]` with
`pref ++ [lm]` when `(cnfOfClauses (deleteIdx cs i)) ∧ ¬pref ⊨ lm` preserves `Sat α` (`↔`)
and `Unsat` (`↔`). -/
theorem vivify_imp_clauses {cs : List (List Nat)} {i : Nat} {pref : List Nat} {lm : Nat}
    (hi : i < cs.length) (hsub : ∀ l ∈ pref, l ∈ cs[i]) (hlm : lm ∈ cs[i])
    (hent : ((cnfOfClauses (deleteIdx cs i)) ++ unitsCnf (pref.map litNeg)).EntailsClause
      (cnfClause [lm])) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i (pref ++ [lm]))).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (replaceIdx cs i (pref ++ [lm]))).Unsat ↔ (cnfOfClauses cs).Unsat) :=
  sat_cnfOfClauses_replaceIdx_equiv hi
    (fun _ _ hp => sat_clause_of_subset
      (fun x hx => (List.mem_append.mp hx).elim (hsub x)
        (fun hm => by simp only [List.mem_singleton] at hm; exact hm ▸ hlm)) hp)
    (fun α hall =>
      let hget := (sat_cnfOfClauses_iff_getElem α cs).mp hall
      let hdel : (cnfOfClauses (deleteIdx cs i)).Sat α :=
        (sat_cnfOfClauses_deleteIdx_iff α cs i).mpr fun j hj _ => hget j hj
      (((vivify_implied_equiv hsub hlm hent).1 α).mpr
        (CNF.sat_add.mpr ⟨hget i hi, hdel⟩) |> CNF.sat_add.mp).1)

/-- Dropping a falsified literal `x` when `f ∧ ¬pref ⊨ ¬x`: preserves satisfaction of
`pref ++ x :: rest` relative to `f`. -/
theorem vivify_dropFalse_equiv {f : CNF Nat} {pref rest : List Nat} {x : Nat}
    (hx : (f ++ unitsCnf (pref.map litNeg)).EntailsClause (cnfClause [litNeg x]))
    {α : Nat → Bool} (hf : f.Sat α) :
    (cnfClause (pref ++ rest)).Sat α ↔ (cnfClause (pref ++ x :: rest)).Sat α := by
  constructor
  · exact sat_clause_of_subset fun y hy => by
      rcases List.mem_append.mp hy with hp | hr
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (List.mem_cons_of_mem x hr)
  · intro hc
    by_cases hpref : (cnfClause pref).Sat α
    · exact sat_clause_of_subset (fun y hy => List.mem_append_left rest hy) hpref
    · have hun : (unitsCnf (pref.map litNeg)).Sat α :=
        (sat_unitsCnf_iff α _).mpr fun u hu => by
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
          exact (sat_cnfClause_litNeg_iff α l).mpr fun hsl =>
            hpref (sat_clause_of_subset (fun y hy => by
              simp only [List.mem_singleton] at hy; rw [hy]; exact hl) hsl)
      have hnegx := CNF.entails_clause_def.mp hx α (CNF.sat_append.mpr ⟨hf, hun⟩)
      obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp hc
      rcases List.mem_append.mp hy with hp | hr
      · exact absurd (sat_clause_of_subset (fun z hz => by
          simp only [List.mem_singleton] at hz; rw [hz]; exact hp)
          ((sat_cnfClause_singleton α y).mpr hys)) hpref
      · rcases List.mem_cons.mp hr with rfl | hrt
        · exact absurd ((sat_cnfClause_singleton α y).mpr hys)
            ((sat_cnfClause_litNeg_iff α y).mp hnegx)
        · exact (clause_sat_cnfClause_iff α _).mpr ⟨y, List.mem_append_right pref hrt, hys⟩

/-! ## 3. Executable unit-propagation-backed vivification (`vivifyClause`, `vivifyPass`) -/

private theorem decisionsAtMost_initState (f : CNF Nat) (k : Nat) :
    decisionsAtMost (initState f) k = [] := by
  simp [decisionsAtMost, initState]

private theorem decisionsAtMost_decideLit_subset {s : CdclState} (hinv : TrailInv s) {l : Nat}
    (hun : litStatus s.trail l = none) (k : Nat) :
    ∀ d ∈ decisionsAtMost (decideLit s l) k, d = l ∨ d ∈ decisionsAtMost s s.level := by
  intro d hd
  rw [mem_decisionsAtMost_iff] at hd
  have hmem : d ∈ s.trail.toList ∨ d = l := by
    have h := hd.1
    simp only [decideLit, trail_assignLit, Array.toList_push, List.mem_append,
      List.mem_singleton] at h
    exact h
  rcases hmem with htrl | rfl
  · right
    have hnv : litVar d ≠ litVar l := litStatus_none_no_var hun d htrl
    have hdl : stateLevel (decideLit s l) d = stateLevel s d := by
      simp [decideLit, hnv]; rfl
    have hdr : stateReason (decideLit s l) d = stateReason s d := by
      simp [decideLit, hnv]; rfl
    obtain ⟨i, hi, rfl⟩ := trail_mem_iff_exists.mp htrl
    exact mem_decisionsAtMost_iff.mpr ⟨htrl, hdr ▸ hd.2.1, hinv.levels_le i hi⟩
  · exact Or.inl rfl

private theorem entails_trail_of_decisions {s : CdclState} (hinv : TrailInv s) {f_rest : CNF Nat}
    {kept : List Nat} (hf0 : s.f0 = f_rest)
    (hdec : ∀ d ∈ decisionsAtMost s s.level, d ∈ kept.map litNeg) :
    ∀ x ∈ s.trail.toList,
      (f_rest ++ unitsCnf (kept.map litNeg)).EntailsClause (cnfClause [x]) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := trail_mem_iff_exists.mp hx
  have htr := trailEntailment_le hinv hi (hinv.levels_le i hi)
  rw [hf0] at htr
  refine CNF.entails_clause_def.mpr fun α hα => ?_
  rw [CNF.sat_append] at hα
  have hdec_sat : (unitsCnf (decisionsAtMost s s.level)).Sat α :=
    (sat_unitsCnf_iff α _).mpr fun d hd =>
      (sat_unitsCnf_iff α _).mp hα.2 d (hdec d hd)
  exact CNF.entails_clause_def.mp htr α (CNF.sat_append.mpr ⟨hα.1, hdec_sat⟩)

private theorem mem_vivifyAux {fuel : Nat} {orig : List Nat} :
    ∀ (todo kept : List Nat) (s : CdclState),
      (∀ l ∈ kept, l ∈ orig) → (∀ l ∈ todo, l ∈ orig) →
      ∀ l ∈ vivifyAux fuel orig kept s todo, l ∈ orig
  | [], kept, _, hk, _, l, hl => by
    simp only [vivifyAux, List.mem_reverse] at hl; exact hk l hl
  | x :: rest, kept, s, hk, ht, l, hl => by
    have hx_mem : x ∈ orig := ht x (List.mem_cons_self)
    have hrest_mem : ∀ y ∈ rest, y ∈ orig := fun y hy => ht y (List.mem_cons_of_mem x hy)
    unfold vivifyAux at hl
    cases hst : litStatus s.trail x with
    | some b =>
      rw [hst] at hl
      cases b
      · exact mem_vivifyAux rest kept s hk hrest_mem l hl
      · simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hl
        exact hl.elim (hk l) (· ▸ hx_mem)
    | none =>
      rw [hst] at hl; dsimp only at hl
      cases hprop : propagateAll fuel (decideLit s (litNeg x)) with
      | conflict _ _ =>
        rw [hprop] at hl
        simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hl
        exact hl.elim (hk l) (· ▸ hx_mem)
      | ok s2 =>
        rw [hprop] at hl
        exact mem_vivifyAux rest (x :: kept) s2
          (fun y hy => (List.mem_cons.mp hy).elim (· ▸ hx_mem) (hk y)) hrest_mem l hl
      | outOfFuel _ =>
        rw [hprop] at hl; exact hl

private theorem vivifyAux_sound {fuel : Nat} {f_rest : CNF Nat} {orig : List Nat} :
    ∀ (todo kept : List Nat) (s : CdclState),
      TrailInv s → s.f0 = f_rest →
      (∀ d ∈ decisionsAtMost s s.level, d ∈ kept.map litNeg) →
      (∀ l ∈ kept, l ∈ orig) → (∀ l ∈ todo, l ∈ orig) →
      (∀ α : Nat → Bool, f_rest.Sat α →
        ((cnfClause (kept.reverse ++ todo)).Sat α ↔ (cnfClause orig).Sat α)) →
      ∀ α : Nat → Bool, f_rest.Sat α →
        ((cnfClause (vivifyAux fuel orig kept s todo)).Sat α ↔ (cnfClause orig).Sat α)
  | [], kept, _, _, _, _, _, _, heqv, α, hf => by
    simpa [vivifyAux] using heqv α hf
  | x :: rest, kept, s, hinv, hf0, hdec, hk, ht, heqv, α, hf => by
    have hent_trail := entails_trail_of_decisions hinv hf0 hdec
    have hk_rev_iff : ∀ u, u ∈ kept.reverse.map litNeg ↔ u ∈ kept.map litNeg := fun u => by
      simp [List.mem_map]
    have hx_mem : x ∈ orig := ht x List.mem_cons_self
    have hrest_mem : ∀ y ∈ rest, y ∈ orig := fun y hy => ht y (List.mem_cons_of_mem x hy)
    unfold vivifyAux
    cases hst : litStatus s.trail x with
    | some b =>
      cases b
      · have hneg_x : (f_rest ++ unitsCnf (kept.reverse.map litNeg)).EntailsClause
            (cnfClause [litNeg x]) := by
          have h0 := hent_trail (litNeg x) ((litStatus_eq_some_false hinv.vars_nodup).mp hst)
          refine CNF.entails_clause_def.mpr fun β hβ =>
            CNF.entails_clause_def.mp h0 β ?_
          rw [CNF.sat_append, sat_unitsCnf_iff] at hβ ⊢
          exact ⟨hβ.1, fun u hu => hβ.2 u ((hk_rev_iff u).mpr hu)⟩
        have heqv' : ∀ β : Nat → Bool, f_rest.Sat β →
            ((cnfClause (kept.reverse ++ rest)).Sat β ↔ (cnfClause orig).Sat β) := fun β hβ =>
          (vivify_dropFalse_equiv hneg_x hβ).trans (heqv β hβ)
        exact vivifyAux_sound rest kept s hinv hf0 hdec hk hrest_mem heqv' α hf
      · have hx_ent : (f_rest ++ unitsCnf (kept.reverse.map litNeg)).EntailsClause
            (cnfClause [x]) := by
          have h0 := hent_trail x (litStatus_eq_some_true.mp hst)
          refine CNF.entails_clause_def.mpr fun β hβ =>
            CNF.entails_clause_def.mp h0 β ?_
          rw [CNF.sat_append, sat_unitsCnf_iff] at hβ ⊢
          exact ⟨hβ.1, fun u hu => hβ.2 u ((hk_rev_iff u).mpr hu)⟩
        have hkr_sub : ∀ l ∈ kept.reverse, l ∈ orig := fun l hl =>
          hk l (List.mem_reverse.mp hl)
        have hpl_ent := (entails_unit_append_iff f_rest kept.reverse x).mp hx_ent
        have hsat_pl : (cnfClause (kept.reverse ++ [x])).Sat α :=
          CNF.entails_clause_def.mp hpl_ent α hf
        have horig_sat : (cnfClause orig).Sat α :=
          sat_clause_of_subset (fun l hl => (List.mem_append.mp hl).elim (hkr_sub l)
            (fun hm => by simp only [List.mem_singleton] at hm; exact hm ▸ hx_mem)) hsat_pl
        exact ⟨fun _ => horig_sat, fun _ => hsat_pl⟩
    | none =>
      dsimp only
      have hun_neg : litStatus s.trail (litNeg x) = none := by
        rw [litStatus_eq_none] at hst ⊢; simpa [litNeg_litNeg] using hst.symm
      have hdecLit := decideLit_inv hinv hun_neg
      have hpi := propagateAll_inv (fuel := fuel) hdecLit.1
      cases hprop : propagateAll fuel (decideLit s (litNeg x)) with
      | outOfFuel _ =>
        exact ⟨id, id⟩
      | conflict confl s2 =>
        rw [hprop] at hpi
        obtain ⟨hinv2, hf02, hl2, hconfl2, hfals2, hdam2⟩ := hpi
        have hf02' : s2.f0 = f_rest := hf02.trans (hdecLit.2.trans hf0)
        have hdec2 : ∀ d ∈ decisionsAtMost s2 s2.level, d ∈ (x :: kept).map litNeg := by
          intro d hd
          rw [hl2, hdam2] at hd
          rcases decisionsAtMost_decideLit_subset hinv hun_neg _ d hd with rfl | hds
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hdec d hds)
        have hent2 := entails_trail_of_decisions hinv2 hf02' hdec2
        have hunsat : (f_rest ++ unitsCnf (kept.reverse.map litNeg ++ [litNeg x])).Unsat := by
          rw [CNF.unsat_iff_not_sat]
          intro β hβ
          have hβ' : (f_rest ++ unitsCnf ((x :: kept).map litNeg)).Sat β := by
            rw [CNF.sat_append, sat_unitsCnf_iff] at hβ ⊢
            refine ⟨hβ.1, fun u hu => hβ.2 u ?_⟩
            rcases List.mem_map.mp hu with ⟨y, hy, rfl⟩
            rcases List.mem_cons.mp hy with rfl | hyk
            · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
            · exact List.mem_append_left _ (List.mem_map.mpr ⟨y, List.mem_reverse.mpr hyk, rfl⟩)
          rw [CNF.sat_append] at hβ'
          have hconfl_f : f_rest.EntailsClause (cnfClause confl) := hf02' ▸ hconfl2
          obtain ⟨y, hy, hys⟩ :=
            (clause_sat_cnfClause_iff β confl).mp (CNF.entails_clause_def.mp hconfl_f β hβ'.1)
          have hny := CNF.entails_clause_def.mp (hent2 (litNeg y) (hfals2 y hy)) β
            (CNF.sat_append.mpr hβ')
          exact (sat_cnfClause_litNeg_iff β y).mp hny ((sat_cnfClause_singleton β y).mpr hys)
        have hunsat' : (f_rest ++ unitsCnf ((kept.reverse ++ [x]).map litNeg)).Unsat := by
          simpa [List.map_append] using hunsat
        have hpl_ent := (unsat_append_units_iff f_rest (kept.reverse ++ [x])).mp hunsat'
        have hsat_pl : (cnfClause (kept.reverse ++ [x])).Sat α :=
          CNF.entails_clause_def.mp hpl_ent α hf
        have hkr_sub : ∀ l ∈ kept.reverse, l ∈ orig := fun l hl =>
          hk l (List.mem_reverse.mp hl)
        have horig_sat : (cnfClause orig).Sat α :=
          sat_clause_of_subset (fun l hl => (List.mem_append.mp hl).elim (hkr_sub l)
            (fun hm => by simp only [List.mem_singleton] at hm; exact hm ▸ hx_mem)) hsat_pl
        exact ⟨fun _ => horig_sat, fun _ => hsat_pl⟩
      | ok s2 =>
        rw [hprop] at hpi
        obtain ⟨hinv2, hf02, hl2, hdam2⟩ := hpi
        have hf02' : s2.f0 = f_rest := hf02.trans (hdecLit.2.trans hf0)
        have hdec2 : ∀ d ∈ decisionsAtMost s2 s2.level, d ∈ (x :: kept).map litNeg := by
          intro d hd
          rw [hl2, hdam2] at hd
          rcases decisionsAtMost_decideLit_subset hinv hun_neg _ d hd with rfl | hds
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hdec d hds)
        have hk2 : ∀ l ∈ x :: kept, l ∈ orig := fun l hl =>
          (List.mem_cons.mp hl).elim (· ▸ hx_mem) (hk l)
        have heqv' : ∀ β : Nat → Bool, f_rest.Sat β →
            ((cnfClause ((x :: kept).reverse ++ rest)).Sat β ↔ (cnfClause orig).Sat β) := by
          intro β hβ
          have hsub1 : (cnfClause ((x :: kept).reverse ++ rest)).Sat β ↔
              (cnfClause (kept.reverse ++ x :: rest)).Sat β := by
            simp only [clause_sat_cnfClause_iff, List.mem_append, List.mem_reverse,
              List.mem_cons]
            constructor <;> rintro ⟨y, hy, hys⟩ <;> refine ⟨y, ?_, hys⟩
            · rcases hy with (rfl | hyk) | hyr
              · exact Or.inr (Or.inl rfl)
              · exact Or.inl hyk
              · exact Or.inr (Or.inr hyr)
            · rcases hy with hyk | rfl | hyr
              · exact Or.inl (Or.inr hyk)
              · exact Or.inl (Or.inl rfl)
              · exact Or.inr hyr
          exact hsub1.trans (heqv β hβ)
        exact vivifyAux_sound rest (x :: kept) s2 hinv2 hf02' hdec2 hk2 hrest_mem heqv' α hf

/-- Combined semantic soundness and subset property of `vivifyClause`. -/
theorem vivifyClause_sound (fuel : Nat) (rest : List (List Nat)) (c : List Nat) :
    (∀ α : Nat → Bool, (cnfOfClauses rest).Sat α →
      ((cnfClause (vivifyClause fuel rest c)).Sat α ↔ (cnfClause c).Sat α)) ∧
      (∀ l ∈ vivifyClause fuel rest c, l ∈ c) := by
  have h0 := initState_inv (cnfOfClauses rest)
  have hpi := propagateAll_inv (fuel := fuel) h0.1
  unfold vivifyClause
  cases hprop : propagateAll fuel (initState (cnfOfClauses rest)) with
  | outOfFuel s0 => exact ⟨fun _ _ => ⟨id, id⟩, fun _ hl => hl⟩
  | conflict confl s0 =>
    rw [hprop] at hpi
    obtain ⟨hinv0, hf0, hl0, hconfl, hfals, _⟩ := hpi
    have hunsat : (cnfOfClauses rest).Unsat := by
      have := unsat_of_conflict hinv0 (by simp [hl0, initState]) hconfl hfals
      rwa [hf0, h0.2] at this
    exact ⟨fun α hα => absurd hα (CNF.unsat_iff_not_sat.mp hunsat α), fun _ hl => by cases hl⟩
  | ok s0 =>
    rw [hprop] at hpi
    obtain ⟨hinv0, hf0, hl0, hdam0⟩ := hpi
    have hf0' : s0.f0 = cnfOfClauses rest := hf0.trans h0.2
    have hdec0 : ∀ d ∈ decisionsAtMost s0 s0.level, d ∈ ([] : List Nat).map litNeg := by
      intro d hd
      rw [hl0, hdam0, decisionsAtMost_initState] at hd
      cases hd
    have heqv := vivifyAux_sound (fuel := fuel) c [] s0 hinv0 hf0' hdec0
      (fun _ h => by cases h) (fun _ h => h) (fun _ _ => ⟨id, id⟩)
    have hsub := mem_vivifyAux (fuel := fuel) c [] s0 (fun _ h => by cases h) (fun _ h => h)
    exact ⟨heqv, hsub⟩

/-- **Executable vivification of clause `cs[i]`**: replaces `cs[i]` by `vivifyClause` run
against `deleteIdx cs i` and preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem vivify_clause_equiv (fuel : Nat) (cs : List (List Nat)) {i : Nat} (hi : i < cs.length) :
    let cs' := replaceIdx cs i (vivifyClause fuel (deleteIdx cs i) cs[i])
    (∀ α : Nat → Bool, (cnfOfClauses cs').Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses cs').Unsat ↔ (cnfOfClauses cs).Unsat) :=
  sat_cnfOfClauses_replaceIdx_equiv hi
    (fun α hdel hc' => ((vivifyClause_sound fuel (deleteIdx cs i) cs[i]).1 α hdel).mp hc')
    (fun α hall =>
      let hget := (sat_cnfOfClauses_iff_getElem α cs).mp hall
      let hdel : (cnfOfClauses (deleteIdx cs i)).Sat α :=
        (sat_cnfOfClauses_deleteIdx_iff α cs i).mpr fun j hj _ => hget j hj
      ((vivifyClause_sound fuel (deleteIdx cs i) cs[i]).1 α hdel).mpr (hget i hi))

/-- **Executable vivification pass soundness**: `vivifyPass` preserves both `Sat α` (`↔`) and
`Unsat` (`↔`). -/
theorem vivify_pass_equiv (fuel : Nat) (cs : List (List Nat)) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (vivifyPass fuel cs)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (vivifyPass fuel cs)).Unsat ↔ (cnfOfClauses cs).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (vivifyPass fuel cs)).Sat α ↔ (cnfOfClauses cs).Sat α := fun α => by
    have hstep : ∀ β c others, (cnfOfClauses others).Sat β →
        ((cnfClause (vivifyClause fuel others c)).Sat β ↔ (cnfClause c).Sat β) :=
      fun β c others ho => (vivifyClause_sound fuel others c).1 β ho
    simpa [vivifyPass, vivifyPassAux] using
      clauseTransformPassAux_sat_iff (vivifyClause fuel) hstep α cs []
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

end LeanQbe.T.Examples.Kissat.Ref
