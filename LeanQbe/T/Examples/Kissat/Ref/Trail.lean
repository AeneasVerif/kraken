/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Sat

/-!
# Soundness Proofs for the Kissat Abstract CDCL Core (Layer A, Part 1)

Proves foundational semantic soundness for `LeanQbe.T.Examples.Kissat.Ref.Sat` over
`Std.Sat.CNF Nat` (pure Lean, zero `Kraken.Mem`):

1. Signed DIMACS literal round-trip lemmas (`litToDimacs`, `dimacsToLit`).
2. Root-unit stripping/pruning (`pruneClause_sound`) and binary strengthening
   (`strengthenWithBinary_sound`).
3. `ReasonDagInv`, `LazyTrailInv`, `TrailInv`, and `lazyTrailEntailment` / `trailEntailment`.
4. Transition invariant preservation (`reasonDagInv_assignLit`, `initState`, `decideLit`,
   `assignProp`, `addRootUnit`, `backtrackTo`, `addLearnedClause`, `unitPropStep`,
   `propagateAll`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Signed DIMACS `Int` literal bridges -/

theorem litToDimacs_litNeg (l : Nat) : litToDimacs (litNeg l) = -litToDimacs l := by
  simp only [litToDimacs, litVar_litNeg, litSign_litNeg]; cases litSign l <;> simp

theorem dimacsToLit_litToDimacs (l : Nat) : dimacsToLit (litToDimacs l) = some l := by
  unfold litToDimacs dimacsToLit litVar litSign
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · have hs : ((l % 2 == 1) = false) := by simp [h]
    rw [hs]; simp only [Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]
    rw [beq_false_of_ne (by omega : (↑(l / 2 + 1) : Int) ≠ 0), ite_eq_right (by simp),
      ite_eq_left (by omega : (0 : Int) < ↑(l / 2 + 1))]
    simp only [Int.natAbs_natCast, Option.some.injEq]; omega
  · have hs : ((l % 2 == 1) = true) := by simp [h]
    rw [hs]; simp only [↓reduceIte, Int.ofNat_eq_natCast]
    rw [beq_false_of_ne (by omega : -(↑(l / 2 + 1) : Int) ≠ 0), ite_eq_right (by simp),
      ite_eq_right (by omega : ¬((0 : Int) < -(↑(l / 2 + 1) : Int)))]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, Option.some.injEq]; omega

theorem litToDimacs_dimacsToLit {e : Int} {l : Nat} (h : dimacsToLit e = some l) :
    litToDimacs l = e := by
  unfold dimacsToLit at h
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · cases n with
    | zero => simp at h
    | succ k =>
      rw [beq_false_of_ne (by omega : (↑(k + 1) : Int) ≠ 0), ite_eq_right (by simp),
        ite_eq_left (by omega : (0 : Int) < ↑(k + 1))] at h
      simp only [Int.natAbs_natCast, Nat.add_sub_cancel, Option.some.injEq] at h; subst h
      have hs : ((2 * k) % 2 == 1) = false := beq_false_of_ne (by omega)
      rw [litToDimacs, litSign, litVar, hs]
      simp [show (2 * k) / 2 = k by omega, Int.ofNat_eq_natCast]
  · cases n with
    | zero => simp at h
    | succ k =>
      rw [beq_false_of_ne (by omega : -(↑(k + 1) : Int) ≠ 0), ite_eq_right (by simp),
        ite_eq_right (by omega : ¬((0 : Int) < -(↑(k + 1) : Int)))] at h
      simp only [Int.natAbs_neg, Int.natAbs_natCast, Nat.add_sub_cancel, Option.some.injEq] at h
      subst h
      have hs : ((2 * k + 1) % 2 == 1) = true := beq_iff_eq.mpr (by omega)
      rw [litToDimacs, litSign, litVar, hs]
      simp [show (2 * k + 1) / 2 = k by omega, Int.ofNat_eq_natCast]

/-! ## 2. Root-unit stripping, pruning, and binary strengthening soundness -/

theorem entails_stripRootUnits {f : CNF Nat} {units c : List Nat}
    (hc : f.EntailsClause (cnfClause c))
    (hunits : ∀ u ∈ units, f.EntailsClause (cnfClause [u])) :
    f.EntailsClause (cnfClause (stripRootUnits units c)) :=
  entails_stripFalsified hc fun l _ hl =>
    hunits (litNeg l) (by simp only [List.contains_iff_mem] at hl; exact hl)

/-- Root-unit clause pruning soundness. -/
theorem pruneClause_sound {f : CNF Nat} {units c : List Nat}
    (hc : f.EntailsClause (cnfClause c))
    (hunits : ∀ u ∈ units, f.EntailsClause (cnfClause [u])) :
    match pruneClause units c with
    | none => ∃ u ∈ units, u ∈ c ∧ f.EntailsClause (cnfClause [u])
    | some c' => f.EntailsClause (cnfClause c') := by
  unfold pruneClause
  cases hany : c.any (fun l => units.contains l)
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact entails_stripRootUnits hc hunits
  · simp only [↓reduceIte]; simp only [List.any_eq_true, List.contains_iff_mem] at hany
    obtain ⟨l, hl, hu⟩ := hany; exact ⟨l, hu, hl, hunits l hu⟩

/-- Self-subsuming binary strengthening soundness. -/
theorem strengthenWithBinary_sound {f : CNF Nat} {c : List Nat} {pivot binOther : Nat}
    (hc : f.EntailsClause (cnfClause c))
    (hbin : f.EntailsClause (cnfClause [pivot, binOther])) :
    f.EntailsClause (cnfClause (strengthenWithBinary c pivot binOther)) := by
  unfold strengthenWithBinary
  by_cases hcond : (binOther != litNeg pivot && c.contains binOther) = true
  · simp only [hcond, ↓reduceIte]
    simp only [Bool.and_eq_true, bne_iff_ne, List.contains_iff_mem] at hcond
    obtain ⟨hne, hmem⟩ := hcond
    rw [CNF.entails_clause_def] at hc hbin ⊢
    intro α hα; rw [clause_sat_cnfClause_iff]
    by_cases hp : (cnfClause [litNeg pivot]).Sat α
    · obtain ⟨y, hy, hsat⟩ := (clause_sat_cnfClause_iff α [pivot, binOther]).mp (hbin α hα)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy_eq | hy_eq <;> rw [hy_eq] at hsat
      · exact absurd ((sat_cnfClause_singleton α pivot).mpr hsat)
          ((sat_cnfClause_litNeg_iff α pivot).mp hp)
      · exact ⟨binOther, List.mem_filter.mpr ⟨hmem, by simp [hne]⟩, hsat⟩
    · obtain ⟨x, hx, hsat⟩ := (clause_sat_cnfClause_iff α c).mp (hc α hα)
      have hxne : x ≠ litNeg pivot := by
        rintro rfl; exact hp ((sat_cnfClause_singleton α (litNeg pivot)).mpr hsat)
      exact ⟨x, List.mem_filter.mpr ⟨hx, by simp [hxne]⟩, hsat⟩
  · have hcond' : (binOther != litNeg pivot && c.contains binOther) = false :=
      Bool.eq_false_iff.mpr hcond
    simp only [hcond', Bool.false_eq_true, ↓reduceIte]; exact hc

theorem binaryStrengthen_sound {f : CNF Nat} {units c : List Nat} {a b : Nat}
    (hc : f.EntailsClause (cnfClause c))
    (hunits : ∀ u ∈ units, f.EntailsClause (cnfClause [u]))
    (hpr : pruneClause units c = some [a, b]) :
    f.EntailsClause (cnfClause [a, b]) := by
  have h := pruneClause_sound hc hunits; simpa [hpr] using h

/-! ## 3. `ReasonDagInv`, `LazyTrailInv`, `TrailInv`, and trail entailment -/

/-- Strict lexicographic `(level, trailIdx)` precedence relation. -/
@[expose] def lexLt (lvl1 idx1 lvl2 idx2 : Nat) : Prop :=
  lvl1 < lvl2 ∨ (lvl1 = lvl2 ∧ idx1 < idx2)

/-- List of decision literals on `s.trail` at level `≤ k`. -/
@[expose] def decisionsAtMost (s : CdclState) (k : Nat) : List Nat :=
  s.trail.toList.filter fun l =>
    decide (stateReason s l = .decision) && decide (stateLevel s l ≤ k)

theorem mem_decisionsAtMost_iff {s : CdclState} {k l : Nat} :
    l ∈ decisionsAtMost s k ↔
      l ∈ s.trail.toList ∧ stateReason s l = .decision ∧ stateLevel s l ≤ k := by
  simp [decisionsAtMost]

theorem unitsCnf_decisionsAtMost_mono {s : CdclState} {k1 k2 : Nat} (hle : k1 ≤ k2) :
    (s.f0 ++ unitsCnf (decisionsAtMost s k2)).Entails
      (s.f0 ++ unitsCnf (decisionsAtMost s k1)) := by
  rw [CNF.entails_def]
  intro α hα; rw [CNF.sat_append, sat_unitsCnf_iff] at hα ⊢
  refine ⟨hα.1, fun l hl => hα.2 l ?_⟩
  rw [mem_decisionsAtMost_iff] at hl ⊢; exact ⟨hl.1, hl.2.1, Nat.le_trans hl.2.2 hle⟩

/-- Reason-DAG invariant: every trail literal at index `i` is justified by strictly earlier
trail predecessors with non-greater decision level (strictly smaller `(level, idx)`). -/
@[expose] def ReasonDagInv (s : CdclState) : Prop :=
  ∀ (i : Nat) (hi : i < s.trail.size),
    let l := s.trail[i]
    let d := stateLevel s l
    match stateReason s l with
    | .decision => 0 < d
    | .unit => d = 0 ∧ s.f0.EntailsClause (cnfClause [l])
    | .binary other =>
      s.f0.EntailsClause (cnfClause [l, other]) ∧
      ∃ (j : Nat) (hj : j < s.trail.size), j < i ∧
        s.trail[j] = litNeg other ∧ stateLevel s other ≤ d ∧
        lexLt (stateLevel s other) j d i
    | .large cid =>
      ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ !c.garbage = true ∧
        l ∈ c.lits ∧
        ∀ x ∈ c.lits, x ≠ l →
          ∃ (j : Nat) (hj : j < s.trail.size), j < i ∧
            s.trail[j] = litNeg x ∧ stateLevel s x ≤ d ∧
            lexLt (stateLevel s x) j d i

/-- Kissat-faithful trail invariant supporting lazy assignment levels (`levels_mono` omitted). -/
structure LazyTrailInv (s : CdclState) : Prop where
  vars_nodup : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    litVar s.trail[i] = litVar s.trail[j] → i = j
  levels_le : ∀ i, (hi : i < s.trail.size) → stateLevel s s.trail[i] ≤ s.level
  dec_earliest : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    stateLevel s s.trail[i] = stateLevel s s.trail[j] →
    stateReason s s.trail[j] = .decision → j ≤ i
  db_sound : ∀ (cid : Nat) (c : Clause),
    s.clauses[cid]? = some (some c) → s.f0.EntailsClause (cnfClause c.lits)
  units_sound : ∀ u ∈ s.units, s.f0.EntailsClause (cnfClause [u])
  reason_dag : ReasonDagInv s
  inconsistent_sound : s.inconsistent = true → s.f0.Unsat

/-- Complete Layer-A CDCL trail & database soundness invariant. -/
structure TrailInv (s : CdclState) : Prop where
  vars_nodup : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    litVar s.trail[i] = litVar s.trail[j] → i = j
  levels_le : ∀ i, (hi : i < s.trail.size) → stateLevel s s.trail[i] ≤ s.level
  levels_mono : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    i ≤ j → stateLevel s s.trail[i] ≤ stateLevel s s.trail[j]
  dec_earliest : ∀ i j, (hi : i < s.trail.size) → (hj : j < s.trail.size) →
    stateLevel s s.trail[i] = stateLevel s s.trail[j] →
    stateReason s s.trail[j] = .decision → j ≤ i
  db_sound : ∀ (cid : Nat) (c : Clause),
    s.clauses[cid]? = some (some c) → s.f0.EntailsClause (cnfClause c.lits)
  units_sound : ∀ u ∈ s.units, s.f0.EntailsClause (cnfClause [u])
  reason_dag : ReasonDagInv s
  inconsistent_sound : s.inconsistent = true → s.f0.Unsat

theorem trail_mem_iff_exists {trail : Array Nat} {l : Nat} :
    l ∈ trail.toList ↔ ∃ (i : Nat) (hi : i < trail.size), trail[i] = l := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]

theorem trailHasLit_iff {trail : Array Nat} {l : Nat} :
    trailHasLit trail l = true ↔ l ∈ trail.toList := by
  simp [trailHasLit, Array.mem_toList_iff]

theorem litStatus_eq_some_true {trail : Array Nat} {l : Nat} :
    litStatus trail l = some true ↔ l ∈ trail.toList := by
  simp only [litStatus, Array.contains_iff_mem, ← Array.mem_toList_iff]
  by_cases h1 : l ∈ trail.toList <;> by_cases h2 : litNeg l ∈ trail.toList <;> simp [h1, h2]

theorem litStatus_eq_some_false {trail : Array Nat} {l : Nat}
    (hnodup : ∀ i j, (hi : i < trail.size) → (hj : j < trail.size) →
      litVar trail[i] = litVar trail[j] → i = j) :
    litStatus trail l = some false ↔ litNeg l ∈ trail.toList := by
  simp only [litStatus, Array.contains_iff_mem, ← Array.mem_toList_iff]
  by_cases h1 : l ∈ trail.toList
  · refine ⟨fun h => by simp [h1] at h, fun hneg => ?_⟩
    obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp h1
    obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp hneg
    have hij := hnodup i j hi hj (by simp [hieq, hjeq]); subst hij
    rw [hieq] at hjeq; exact absurd hjeq.symm (litNeg_ne_self l)
  · by_cases h2 : litNeg l ∈ trail.toList <;> simp [h1, h2]

theorem litStatus_eq_none {trail : Array Nat} {l : Nat} :
    litStatus trail l = none ↔ l ∉ trail.toList ∧ litNeg l ∉ trail.toList := by
  simp only [litStatus, Array.contains_iff_mem, ← Array.mem_toList_iff]
  by_cases h1 : l ∈ trail.toList <;> by_cases h2 : litNeg l ∈ trail.toList <;> simp [h1, h2]

theorem litStatus_none_no_var {trail : Array Nat} {l : Nat}
    (h : litStatus trail l = none) : ∀ x ∈ trail.toList, litVar x ≠ litVar l := by
  rw [litStatus_eq_none] at h
  intro x hx hvar
  rcases (litVar_eq_iff x l).mp hvar with rfl | rfl
  · exact h.1 hx
  · exact h.2 hx

@[simp] theorem trail_assignLit (s : CdclState) (l lvl : Nat) (rsn : Reason) :
    (assignLit s l lvl rsn).trail = s.trail.push l := rfl
@[simp] theorem level_assignLit (s : CdclState) (l lvl : Nat) (rsn : Reason) :
    (assignLit s l lvl rsn).level = s.level := rfl
@[simp] theorem f0_assignLit (s : CdclState) (l lvl : Nat) (rsn : Reason) :
    (assignLit s l lvl rsn).f0 = s.f0 := rfl
@[simp] theorem clauses_assignLit (s : CdclState) (l lvl : Nat) (rsn : Reason) :
    (assignLit s l lvl rsn).clauses = s.clauses := rfl
@[simp] theorem units_assignLit (s : CdclState) (l lvl : Nat) (rsn : Reason) :
    (assignLit s l lvl rsn).units = s.units := rfl
@[simp] theorem inconsistent_assignLit (s : CdclState) (l lvl : Nat) (rsn : Reason) :
    (assignLit s l lvl rsn).inconsistent = s.inconsistent := rfl

@[simp] theorem stateLevel_assignLit (s : CdclState) (l lvl : Nat) (rsn : Reason) (x : Nat) :
    stateLevel (assignLit s l lvl rsn) x =
      if litVar x = litVar l then lvl else stateLevel s x :=
  arraySetPad_getD s.levels (litVar l) lvl 0 (litVar x)

@[simp] theorem stateReason_assignLit (s : CdclState) (l lvl : Nat) (rsn : Reason) (x : Nat) :
    stateReason (assignLit s l lvl rsn) x =
      if litVar x = litVar l then rsn else stateReason s x :=
  arraySetPad_getD s.reasons (litVar l) rsn .unit (litVar x)

@[simp] theorem f0_addLearnedClause (s : CdclState) (lits : List Nat) (glue : Nat) :
    (addLearnedClause s lits glue).f0 = s.f0 := rfl
@[simp] theorem trail_addLearnedClause (s : CdclState) (lits : List Nat) (glue : Nat) :
    (addLearnedClause s lits glue).trail = s.trail := rfl
@[simp] theorem level_addLearnedClause (s : CdclState) (lits : List Nat) (glue : Nat) :
    (addLearnedClause s lits glue).level = s.level := rfl
@[simp] theorem stateLevel_addLearnedClause (s : CdclState) (lits : List Nat) (glue x : Nat) :
    stateLevel (addLearnedClause s lits glue) x = stateLevel s x := rfl
@[simp] theorem stateReason_addLearnedClause (s : CdclState) (lits : List Nat) (glue x : Nat) :
    stateReason (addLearnedClause s lits glue) x = stateReason s x := rfl

/-- Every `TrailInv` state satisfies `LazyTrailInv`. -/
theorem TrailInv.toLazy {s : CdclState} (h : TrailInv s) : LazyTrailInv s :=
  ⟨h.vars_nodup, h.levels_le, h.dec_earliest, h.db_sound, h.units_sound,
    h.reason_dag, h.inconsistent_sound⟩

/-- Trail entailment under lazy levels (`levels_mono` omitted): `F₀ ∧ decisions ≤_k ⊨ literal`. -/
theorem lazyTrailEntailment {s : CdclState} (hinv : LazyTrailInv s) :
    ∀ (i : Nat) (hi : i < s.trail.size),
      (s.f0 ++ unitsCnf (decisionsAtMost s (stateLevel s s.trail[i]))).EntailsClause
        (cnfClause [s.trail[i]]) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    have hrd := hinv.reason_dag i hi
    dsimp only at hrd
    generalize hrsn : stateReason s s.trail[i] = rsn; rw [hrsn] at hrd
    cases rsn with
    | decision =>
      refine CNF.entails_clause_def.mpr fun α hα => ?_
      rw [CNF.sat_append, sat_unitsCnf_iff] at hα
      exact hα.2 s.trail[i] (mem_decisionsAtMost_iff.mpr
        ⟨trail_mem_iff_exists.mpr ⟨i, hi, rfl⟩, hrsn, Nat.le_refl _⟩)
    | unit => exact CNF.entails_clause_trans CNF.append_entails_left hrd.2
    | binary other =>
      obtain ⟨hbin, j, hj, hjlt, hjeq, hle, _⟩ := hrd
      have hneg : (s.f0 ++ unitsCnf (decisionsAtMost s (stateLevel s s.trail[i]))).EntailsClause
          (cnfClause [litNeg other]) := by
        rw [← hjeq]
        exact CNF.entails_clause_trans
          (unitsCnf_decisionsAtMost_mono (by simpa [hjeq, stateLevel] using hle)) (ih j hjlt hj)
      refine CNF.entails_clause_def.mpr fun α hα => ?_
      have hα_neg := CNF.entails_clause_def.mp hneg α hα
      obtain ⟨y, hy, hsat⟩ := (clause_sat_cnfClause_iff α [s.trail[i], other]).mp
        (CNF.entails_clause_def.mp hbin α (CNF.sat_append.mp hα).1)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with heq | heq <;> rw [heq] at hsat
      · exact (sat_cnfClause_singleton α s.trail[i]).mpr hsat
      · exact absurd ((sat_cnfClause_singleton α other).mpr hsat)
          ((sat_cnfClause_litNeg_iff α other).mp hα_neg)
    | large cid =>
      obtain ⟨c, hget, _, _, hall⟩ := hrd
      refine CNF.entails_clause_def.mpr fun α hα => ?_
      obtain ⟨x, hx, hsat⟩ := (clause_sat_cnfClause_iff α c.lits).mp
        (CNF.entails_clause_def.mp (hinv.db_sound cid c hget) α (CNF.sat_append.mp hα).1)
      by_cases hxeq : x = s.trail[i]
      · rw [hxeq] at hsat; exact (sat_cnfClause_singleton α s.trail[i]).mpr hsat
      · obtain ⟨j, hj, hjlt, hjeq, hle, _⟩ := hall x hx hxeq
        have hneg : (s.f0 ++ unitsCnf (decisionsAtMost s (stateLevel s s.trail[i]))).EntailsClause
            (cnfClause [litNeg x]) := by
          rw [← hjeq]
          exact CNF.entails_clause_trans
            (unitsCnf_decisionsAtMost_mono (by simpa [hjeq, stateLevel] using hle)) (ih j hjlt hj)
        exact absurd ((sat_cnfClause_singleton α x).mpr hsat)
          ((sat_cnfClause_litNeg_iff α x).mp (CNF.entails_clause_def.mp hneg α hα))

theorem lazyDecisionsAtMost_zero_empty {s : CdclState} (hinv : LazyTrailInv s) :
    decisionsAtMost s 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro l hl; rw [mem_decisionsAtMost_iff] at hl
  obtain ⟨i, hi, rfl⟩ := trail_mem_iff_exists.mp hl.1
  have hrd := hinv.reason_dag i hi; dsimp only at hrd; rw [hl.2.1] at hrd; omega

theorem lazyTrailEntailment_level0 {s : CdclState} (hinv : LazyTrailInv s) {i : Nat}
    (hi : i < s.trail.size) (hlvl : stateLevel s s.trail[i] = 0) :
    s.f0.EntailsClause (cnfClause [s.trail[i]]) := by
  have h := lazyTrailEntailment hinv i hi
  rw [hlvl, lazyDecisionsAtMost_zero_empty hinv] at h
  exact CNF.entails_clause_def.mpr fun α hα =>
    CNF.entails_clause_def.mp h α (by simpa [unitsCnf] using hα)

theorem lazyUnsat_of_conflict {s : CdclState} (hinv : LazyTrailInv s) {confl : List Nat}
    (hlvl : s.level = 0) (hconfl : s.f0.EntailsClause (cnfClause confl))
    (hfals : ∀ l ∈ confl, litNeg l ∈ s.trail.toList) : s.f0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  obtain ⟨l, hl, hsat⟩ :=
    (clause_sat_cnfClause_iff α confl).mp (CNF.entails_clause_def.mp hconfl α hα)
  obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp (hfals l hl)
  have hli : stateLevel s s.trail[i] = 0 := by have := hinv.levels_le i hi; omega
  have hent := lazyTrailEntailment_level0 hinv hi hli; rw [hieq] at hent
  exact (sat_cnfClause_litNeg_iff α l).mp (CNF.entails_clause_def.mp hent α hα)
    ((sat_cnfClause_singleton α l).mpr hsat)

/-- Trail entailment: every literal `s.trail[i]` at level `d` is entailed by `s.f0` plus decisions
at level `≤ d`. -/
theorem trailEntailment {s : CdclState} (hinv : TrailInv s) :
    ∀ (i : Nat) (hi : i < s.trail.size),
      (s.f0 ++ unitsCnf (decisionsAtMost s (stateLevel s s.trail[i]))).EntailsClause
        (cnfClause [s.trail[i]]) :=
  lazyTrailEntailment hinv.toLazy

theorem trailEntailment_le {s : CdclState} (hinv : TrailInv s) {i k : Nat}
    (hi : i < s.trail.size) (hle : stateLevel s s.trail[i] ≤ k) :
    (s.f0 ++ unitsCnf (decisionsAtMost s k)).EntailsClause (cnfClause [s.trail[i]]) :=
  CNF.entails_clause_trans (unitsCnf_decisionsAtMost_mono hle) (trailEntailment hinv i hi)

theorem decisionsAtMost_zero_empty {s : CdclState} (hinv : TrailInv s) :
    decisionsAtMost s 0 = [] :=
  lazyDecisionsAtMost_zero_empty hinv.toLazy

theorem trailEntailment_level0 {s : CdclState} (hinv : TrailInv s) {i : Nat}
    (hi : i < s.trail.size) (hlvl : stateLevel s s.trail[i] = 0) :
    s.f0.EntailsClause (cnfClause [s.trail[i]]) :=
  lazyTrailEntailment_level0 hinv.toLazy hi hlvl

theorem unsat_of_conflict {s : CdclState} (hinv : TrailInv s) {confl : List Nat}
    (hlvl : s.level = 0) (hconfl : s.f0.EntailsClause (cnfClause confl))
    (hfals : ∀ l ∈ confl, litNeg l ∈ s.trail.toList) : s.f0.Unsat :=
  lazyUnsat_of_conflict hinv.toLazy hlvl hconfl hfals

/-! ## 4. Transition invariant preservation -/

theorem initState_inv (cnf : CNF Nat) :
    TrailInv (initState cnf) ∧ (initState cnf).f0 = cnf := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro i _ hi; simp [initState] at hi
  · intro i hi; simp [initState] at hi
  · intro i _ hi; simp [initState] at hi
  · intro i _ hi; simp [initState] at hi
  · intro cid c hget
    simp only [initState, Array.getElem?_map] at hget
    cases h : cnf.clauses[cid]? with
    | none => simp [h] at hget
    | some cl =>
      simp only [h, Option.map_some, Option.some.injEq] at hget; subst hget
      have hmem : cl ∈ cnf := by
        rw [CNF.Internal.mem_iff, Array.mem_iff_getElem]
        exact ⟨cid, (Array.getElem?_eq_some_iff.mp h).1, (Array.getElem?_eq_some_iff.mp h).2⟩
      change CNF.EntailsClause cnf (cnfClause (clauseOfCnf cl))
      simpa [cnfClause_clauseOfCnf] using CNF.entails_clause_of_mem hmem
  · intro u hu; simp [initState] at hu
  · intro i hi; simp [initState] at hi
  · intro h; simp [initState] at h

/-- Shared trail-push invariant for decisions, propagations, and level-0 unit additions. -/
@[expose] def ReasonOk (s : CdclState) (l lvl : Nat) : Reason → Prop
  | .decision => 0 < lvl
  | .unit => lvl = 0 ∧ s.f0.EntailsClause (cnfClause [l])
  | .binary other =>
    s.f0.EntailsClause (cnfClause [l, other]) ∧
    ∃ (j : Nat) (hj : j < s.trail.size),
      s.trail[j] = litNeg other ∧ stateLevel s other ≤ lvl ∧
      lexLt (stateLevel s other) j lvl s.trail.size
  | .large cid =>
    ∃ c : Clause, s.clauses[cid]? = some (some c) ∧ !c.garbage = true ∧ l ∈ c.lits ∧
      ∀ x ∈ c.lits, x ≠ l →
        ∃ (j : Nat) (hj : j < s.trail.size),
          s.trail[j] = litNeg x ∧ stateLevel s x ≤ lvl ∧
          lexLt (stateLevel s x) j lvl s.trail.size

private def withLvlUnits (s : CdclState) (nl : Nat) (us : List Nat) : CdclState :=
  { s with level := nl, units := us }
@[simp] private theorem f0_wlu (s : CdclState) (nl : Nat) (us : List Nat) :
    (withLvlUnits s nl us).f0 = s.f0 := rfl
@[simp] private theorem clauses_wlu (s : CdclState) (nl : Nat) (us : List Nat) :
    (withLvlUnits s nl us).clauses = s.clauses := rfl
@[simp] private theorem trail_wlu (s : CdclState) (nl : Nat) (us : List Nat) :
    (withLvlUnits s nl us).trail = s.trail := rfl
@[simp] private theorem level_wlu (s : CdclState) (nl : Nat) (us : List Nat) :
    (withLvlUnits s nl us).level = nl := rfl
@[simp] private theorem inconsistent_wlu (s : CdclState) (nl : Nat) (us : List Nat) :
    (withLvlUnits s nl us).inconsistent = s.inconsistent := rfl
@[simp] private theorem stateLevel_wlu (s : CdclState) (nl : Nat) (us : List Nat) (x : Nat) :
    stateLevel (withLvlUnits s nl us) x = stateLevel s x := rfl
@[simp] private theorem stateReason_wlu (s : CdclState) (nl : Nat) (us : List Nat) (x : Nat) :
    stateReason (withLvlUnits s nl us) x = stateReason s x := rfl

/-- `ReasonDagInv` preservation across `assignLit s l lvl rsn` (shared by standard & chrono). -/
theorem reasonDagInv_assignLit {s : CdclState} (hrd_old : ReasonDagInv s) {l lvl : Nat}
    {rsn : Reason} (hun : litStatus s.trail l = none) (hrsn : ReasonOk s l lvl rsn) :
    ReasonDagInv (assignLit s l lvl rsn) := by
  have hold_lt : ∀ {i : Nat} (hi : i < s.trail.size), litVar s.trail[i] ≠ litVar l :=
    fun hi => litStatus_none_no_var hun _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
  intro i hi
  simp only [trail_assignLit, Array.size_push] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
  · have hrd := hrd_old i hi'; dsimp only at hrd
    simp only [trail_assignLit, Array.getElem_push_lt hi', stateLevel_assignLit,
      stateReason_assignLit, hold_lt hi', ↓reduceIte, f0_assignLit, clauses_assignLit]
    generalize hrs : stateReason s s.trail[i] = r0; rw [hrs] at hrd
    cases r0 with
    | decision | unit => exact hrd
    | binary other =>
      obtain ⟨hbin, j, hj, hjlt, hjeq, hle, hlex⟩ := hrd
      have hnv : litVar other ≠ litVar l := by simpa [hjeq] using hold_lt hj
      refine ⟨hbin, j, by rw [Array.size_push]; exact Nat.lt_succ_of_lt hj, hjlt,
        by simp [Array.getElem_push_lt hj, hjeq],
        by simpa [hnv] using hle, by simpa [hnv] using hlex⟩
    | large cid =>
      obtain ⟨c, hget, hng, hlmem, hall⟩ := hrd
      refine ⟨c, hget, hng, hlmem, fun x hx hne => ?_⟩
      obtain ⟨j, hj, hjlt, hjeq, hle, hlex⟩ := hall x hx hne
      have hnv : litVar x ≠ litVar l := by simpa [hjeq] using hold_lt hj
      refine ⟨j, by rw [Array.size_push]; exact Nat.lt_succ_of_lt hj, hjlt,
        by simp [Array.getElem_push_lt hj, hjeq],
        by simpa [hnv] using hle, by simpa [hnv] using hlex⟩
  · simp only [trail_assignLit, Array.getElem_push_eq, stateLevel_assignLit,
      stateReason_assignLit, ↓reduceIte, f0_assignLit, clauses_assignLit]
    cases rsn with
    | decision | unit => exact hrsn
    | binary other =>
      obtain ⟨hbin, j, hj, hjeq, hle, hlex⟩ := hrsn
      have hnv : litVar other ≠ litVar l := by simpa [hjeq] using hold_lt hj
      refine ⟨hbin, j, by rw [Array.size_push]; exact Nat.lt_succ_of_lt hj, hj,
        by simp [Array.getElem_push_lt hj, hjeq],
        by simpa [hnv] using hle, by simpa [hnv] using hlex⟩
    | large cid =>
      obtain ⟨c, hget, hng, hlmem, hall⟩ := hrsn
      refine ⟨c, hget, hng, hlmem, fun x hx hne => ?_⟩
      obtain ⟨j, hj, hjeq, hle, hlex⟩ := hall x hx hne
      have hnv : litVar x ≠ litVar l := by simpa [hjeq] using hold_lt hj
      refine ⟨j, by rw [Array.size_push]; exact Nat.lt_succ_of_lt hj, hj,
        by simp [Array.getElem_push_lt hj, hjeq],
        by simpa [hnv] using hle, by simpa [hnv] using hlex⟩

private theorem pushLit_inv {s : CdclState} (hinv : TrailInv s) {l lvl newLvl : Nat}
    {rsn : Reason} {us : List Nat}
    (hun : litStatus s.trail l = none)
    (hs_lvl : s.level ≤ newLvl) (hlvl_le : lvl ≤ newLvl)
    (hmono_old : ∀ i (hi : i < s.trail.size), stateLevel s s.trail[i] ≤ lvl)
    (hdec_old : rsn = .decision → ∀ i (hi : i < s.trail.size), stateLevel s s.trail[i] < lvl)
    (hrsn : ReasonOk s l lvl rsn)
    (hunits : ∀ u ∈ us, s.f0.EntailsClause (cnfClause [u])) :
    let s' := assignLit (withLvlUnits s newLvl us) l lvl rsn
    TrailInv s' ∧ s'.f0 = s.f0 := by
  have hold_lt : ∀ {i : Nat} (hi : i < s.trail.size), litVar s.trail[i] ≠ litVar l :=
    fun hi => litStatus_none_no_var hun _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
  refine ⟨⟨?_, ?_, ?_, ?_, hinv.db_sound, hunits, ?_, hinv.inconsistent_sound⟩, rfl⟩
  · intro i j hi hj hvar
    simp only [trail_assignLit, trail_wlu, Array.size_push] at hi hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · simp only [trail_assignLit, trail_wlu, Array.getElem_push_lt hi',
        Array.getElem_push_lt hj'] at hvar
      exact hinv.vars_nodup i j hi' hj' hvar
    · simp only [trail_assignLit, trail_wlu, Array.getElem_push_lt hi',
        Array.getElem_push_eq] at hvar
      exact absurd hvar (hold_lt hi')
    · simp only [trail_assignLit, trail_wlu, Array.getElem_push_eq,
        Array.getElem_push_lt hj'] at hvar
      exact absurd hvar.symm (hold_lt hj')
    · rfl
  · intro i hi
    simp only [trail_assignLit, trail_wlu, Array.size_push] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · simp only [trail_assignLit, trail_wlu, Array.getElem_push_lt hi', stateLevel_assignLit,
        stateLevel_wlu, hold_lt hi', ↓reduceIte, level_assignLit, level_wlu]
      exact Nat.le_trans (hinv.levels_le i hi') hs_lvl
    · simp [hlvl_le]
  · intro i j hi hj hij
    simp only [trail_assignLit, trail_wlu, Array.size_push] at hi hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · have hi' : i < s.trail.size := Nat.lt_of_le_of_lt hij hj'
      simp only [trail_assignLit, trail_wlu, Array.getElem_push_lt hi', Array.getElem_push_lt hj',
        stateLevel_assignLit, stateLevel_wlu, hold_lt hi', hold_lt hj', ↓reduceIte]
      exact hinv.levels_mono i j hi' hj' hij
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · simp only [trail_assignLit, trail_wlu, Array.getElem_push_lt hi', Array.getElem_push_eq,
          stateLevel_assignLit, stateLevel_wlu, hold_lt hi', ↓reduceIte]
        exact hmono_old i hi'
      · exact Nat.le_refl _
  · intro i j hi hj hleq hrsn_j
    simp only [trail_assignLit, trail_wlu, Array.size_push] at hi hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · simp only [trail_assignLit, trail_wlu, Array.getElem_push_lt hi', Array.getElem_push_lt hj',
          stateLevel_assignLit, stateReason_assignLit, stateLevel_wlu, stateReason_wlu,
          hold_lt hi', hold_lt hj', ↓reduceIte] at hleq hrsn_j
        exact hinv.dec_earliest i j hi' hj' hleq hrsn_j
      · omega
    · simp only [trail_assignLit, trail_wlu, Array.getElem_push_eq, stateReason_assignLit,
        ↓reduceIte] at hrsn_j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · simp only [trail_assignLit, trail_wlu, Array.getElem_push_lt hi', Array.getElem_push_eq,
          stateLevel_assignLit, stateLevel_wlu, hold_lt hi', ↓reduceIte] at hleq
        exact absurd hleq (Nat.ne_of_lt (hdec_old hrsn_j i hi'))
      · exact Nat.le_refl _
  · exact reasonDagInv_assignLit hinv.reason_dag hun hrsn

theorem decideLit_inv {s : CdclState} (hinv : TrailInv s) {l : Nat}
    (hun : litStatus s.trail l = none) :
    TrailInv (decideLit s l) ∧ (decideLit s l).f0 = s.f0 :=
  pushLit_inv hinv hun (Nat.le_succ s.level) (Nat.le_refl _)
    (fun i hi => Nat.le_trans (hinv.levels_le i hi) (Nat.le_succ _))
    (fun _ i hi => Nat.lt_succ_of_le (hinv.levels_le i hi))
    (Nat.zero_lt_succ s.level) hinv.units_sound

theorem assignProp_inv {s : CdclState} (hinv : TrailInv s) {l : Nat} {rsn : Reason}
    (hun : litStatus s.trail l = none) (hrsn_ne : rsn ≠ .decision)
    (hrsn : ReasonOk s l s.level rsn) :
    TrailInv (assignLit s l s.level rsn) ∧ (assignLit s l s.level rsn).f0 = s.f0 :=
  pushLit_inv hinv hun (Nat.le_refl _) (Nat.le_refl _)
    hinv.levels_le (fun h => absurd h hrsn_ne) hrsn hinv.units_sound

theorem addRootUnit_inv {s : CdclState} (hinv : TrailInv s) (hl0 : s.level = 0) {l : Nat}
    (hun : litStatus s.trail l = none) (hent : s.f0.EntailsClause (cnfClause [l])) :
    let s' := assignLit { s with units := l :: s.units } l 0 .unit
    TrailInv s' ∧ s'.f0 = s.f0 := by
  have hwlu : ({ s with units := l :: s.units } : CdclState) =
      withLvlUnits s 0 (l :: s.units) := by cases s; simp_all [withLvlUnits]
  rw [hwlu]
  exact pushLit_inv hinv hun (by omega) (Nat.le_refl _)
    (fun i hi => by have := hinv.levels_le i hi; omega)
    (fun h => by cases h) ⟨rfl, hent⟩
    (fun u hu => (List.mem_cons.mp hu).elim (· ▸ hent) (hinv.units_sound u))

@[simp] theorem f0_backtrackTo (s : CdclState) (t : Nat) : (backtrackTo s t).f0 = s.f0 := rfl
@[simp] theorem clauses_backtrackTo (s : CdclState) (t : Nat) :
    (backtrackTo s t).clauses = s.clauses := rfl
@[simp] theorem level_backtrackTo (s : CdclState) (t : Nat) :
    (backtrackTo s t).level = Nat.min s.level t := rfl
@[simp] theorem stateLevel_backtrackTo (s : CdclState) (t x : Nat) :
    stateLevel (backtrackTo s t) x = stateLevel s x := rfl
@[simp] theorem stateReason_backtrackTo (s : CdclState) (t x : Nat) :
    stateReason (backtrackTo s t) x = stateReason s x := rfl

theorem trail_backtrackTo_size_le (s : CdclState) (t : Nat) :
    (backtrackTo s t).trail.size ≤ s.trail.size := by
  simp only [backtrackTo, Array.size_extract, Nat.sub_zero]; exact Nat.min_le_right _ _

theorem trail_backtrackTo_getElem (s : CdclState) (t i : Nat)
    (hi : i < (backtrackTo s t).trail.size) :
    (backtrackTo s t).trail[i] =
      s.trail[i]'(Nat.lt_of_lt_of_le hi (trail_backtrackTo_size_le s t)) := by
  simp only [backtrackTo, Array.getElem_extract, Nat.zero_add]

theorem backtrackTo_inv {s : CdclState} (hinv : TrailInv s) (targetLevel : Nat) :
    TrailInv (backtrackTo s targetLevel) ∧ (backtrackTo s targetLevel).f0 = s.f0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, hinv.db_sound, hinv.units_sound, ?_, hinv.inconsistent_sound⟩, rfl⟩
  · intro i j hi hj hvar
    rw [trail_backtrackTo_getElem, trail_backtrackTo_getElem] at hvar
    exact hinv.vars_nodup i j _ _ hvar
  · intro i hi
    simp only [stateLevel_backtrackTo, level_backtrackTo]
    have h1 : stateLevel s (backtrackTo s targetLevel).trail[i] ≤ s.level := by
      rw [trail_backtrackTo_getElem]; exact hinv.levels_le i _
    have hi_tw : i < (s.trail.toList.takeWhile
        (fun l => decide (s.levels.getD (litVar l) 0 ≤ targetLevel))).length := by
      simp only [backtrackTo, Array.size_extract] at hi; omega
    have h2 : stateLevel s (backtrackTo s targetLevel).trail[i] ≤ targetLevel := by
      rw [trail_backtrackTo_getElem]
      have hp := (takeWhile_props (fun l => decide (s.levels.getD (litVar l) 0 ≤ targetLevel))
        s.trail.toList).2 i hi_tw |>.2.2
      simpa [stateLevel] using hp
    exact Nat.le_min.mpr ⟨h1, h2⟩
  · intro i j hi hj hij
    rw [stateLevel_backtrackTo, stateLevel_backtrackTo,
      trail_backtrackTo_getElem, trail_backtrackTo_getElem]
    exact hinv.levels_mono i j _ _ hij
  · intro i j hi hj hleq hrsn
    rw [stateLevel_backtrackTo, stateLevel_backtrackTo,
      trail_backtrackTo_getElem, trail_backtrackTo_getElem] at hleq
    rw [stateReason_backtrackTo, trail_backtrackTo_getElem] at hrsn
    exact hinv.dec_earliest i j _ _ hleq hrsn
  · intro i hi
    have hi' := Nat.lt_of_lt_of_le hi (trail_backtrackTo_size_le s targetLevel)
    have hrd := hinv.reason_dag i hi'; dsimp only at hrd
    simp only [clauses_backtrackTo, f0_backtrackTo, stateLevel_backtrackTo, stateReason_backtrackTo]
    rw [trail_backtrackTo_getElem]
    generalize hrs : stateReason s s.trail[i] = rsn; rw [hrs] at hrd
    cases rsn with
    | decision | unit => exact hrd
    | binary other =>
      obtain ⟨hbin, j, hj, hjlt, hjeq, hle, hlex⟩ := hrd
      exact ⟨hbin, j, Nat.lt_trans hjlt hi, hjlt,
        by rw [trail_backtrackTo_getElem]; exact hjeq, hle, hlex⟩
    | large cid =>
      obtain ⟨c, hget, hng, hlmem, hall⟩ := hrd
      refine ⟨c, hget, hng, hlmem, fun x hx hne => ?_⟩
      obtain ⟨j, hj, hjlt, hjeq, hle, hlex⟩ := hall x hx hne
      exact ⟨j, Nat.lt_trans hjlt hi, hjlt,
        by rw [trail_backtrackTo_getElem]; exact hjeq, hle, hlex⟩

/-- Replacing `s.clauses` while keeping all active trail-referenced clauses intact preserves
`ReasonDagInv`. -/
theorem reasonDagInv_withClauses {s : CdclState} (hrd_old : ReasonDagInv s)
    (clauses' : Array (Option Clause))
    (hact : ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat) (c : Clause),
      stateReason s s.trail[i] = .large cid → s.clauses[cid]? = some (some c) →
      !c.garbage = true → clauses'[cid]? = some (some c)) :
    ReasonDagInv { s with clauses := clauses' } := by
  intro i hi
  have hrd := hrd_old i hi
  have hrs_eq : ∀ x, stateReason { s with clauses := clauses' } x = stateReason s x := fun _ => rfl
  have hlv_eq : ∀ x, stateLevel { s with clauses := clauses' } x = stateLevel s x := fun _ => rfl
  dsimp only [ReasonDagInv] at hrd ⊢
  simp only [hrs_eq, hlv_eq]
  cases hrsn : stateReason s s.trail[i] <;> simp only [hrsn] at hrd ⊢
  · exact hrd
  · exact hrd
  · exact hrd
  · obtain ⟨c, hget, hng, hm, hall⟩ := hrd
    exact ⟨c, hact i hi _ c hrsn hget hng, hng, hm, hall⟩

/-- Replacing `s.clauses` while keeping all active trail-referenced clauses intact preserves
`LazyTrailInv`. -/
theorem lazyTrailInv_withClauses {s : CdclState} (hinv : LazyTrailInv s)
    (clauses' : Array (Option Clause))
    (hdb : ∀ (cid : Nat) (c : Clause),
      clauses'[cid]? = some (some c) → s.f0.EntailsClause (cnfClause c.lits))
    (hact : ∀ (i : Nat) (_hi : i < s.trail.size) (cid : Nat) (c : Clause),
      stateReason s s.trail[i] = .large cid → s.clauses[cid]? = some (some c) →
      !c.garbage = true → clauses'[cid]? = some (some c)) :
    LazyTrailInv { s with clauses := clauses' } :=
  ⟨hinv.vars_nodup, hinv.levels_le, hinv.dec_earliest, hdb, hinv.units_sound,
    reasonDagInv_withClauses hinv.reason_dag clauses' hact, hinv.inconsistent_sound⟩

theorem addLearnedClause_inv {s : CdclState} (hinv : TrailInv s) {lits : List Nat} {glue : Nat}
    (hent : s.f0.EntailsClause (cnfClause lits)) :
    TrailInv (addLearnedClause s lits glue) ∧ (addLearnedClause s lits glue).f0 = s.f0 := by
  have hlazy := lazyTrailInv_withClauses hinv.toLazy (addLearnedClause s lits glue).clauses
    (fun cid c hget => by
      simp only [addLearnedClause, Array.getElem?_push] at hget
      split at hget
      · simp only [Option.some.injEq] at hget; subst hget; exact hent
      · exact hinv.db_sound cid c hget)
    (fun i hi cid c _ hget _ => by
      have hne : cid ≠ s.clauses.size := Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp hget).1
      simp only [addLearnedClause, Array.getElem?_push, hne, ↓reduceIte]; exact hget)
  exact ⟨⟨hlazy.vars_nodup, hlazy.levels_le, hinv.levels_mono, hlazy.dec_earliest,
    hlazy.db_sound, hlazy.units_sound, hlazy.reason_dag, hlazy.inconsistent_sound⟩, rfl⟩

private theorem classifyClauseAux_sound {trail : Array Nat}
    (hnodup : ∀ i j, (hi : i < trail.size) → (hj : j < trail.size) →
      litVar trail[i] = litVar trail[j] → i = j) :
    ∀ (lits : List Nat) (cand : Option Nat),
      (∀ u, cand = some u → litStatus trail u = none) →
      match classifyClauseAux trail lits cand with
      | .falsified => cand = none ∧ ∀ x ∈ lits, litNeg x ∈ trail.toList
      | .unit u =>
        litStatus trail u = none ∧ (∀ w, cand = some w → u = w) ∧
        (cand = none → u ∈ lits) ∧ ∀ x ∈ lits, x ≠ u → litNeg x ∈ trail.toList
      | _ => True := by
  intro lits
  induction lits with
  | nil =>
    intro cand hcand
    cases cand with
    | none => simp [classifyClauseAux]
    | some u => simp [classifyClauseAux, hcand u rfl]
  | cons l ls ih =>
    intro cand hcand
    simp only [classifyClauseAux]
    cases hl : litStatus trail l with
    | some b =>
      cases b
      · have hih := ih cand hcand
        have hlneg := (litStatus_eq_some_false hnodup).mp hl
        cases hres : classifyClauseAux trail ls cand <;> rw [hres] at hih
        · trivial
        · exact ⟨hih.1, fun x hx =>
            (List.mem_cons.mp hx).elim (fun h => h ▸ hlneg) (hih.2 x)⟩
        · exact ⟨hih.1, hih.2.1, fun hc => List.mem_cons_of_mem _ (hih.2.2.1 hc), fun x hx hne =>
            (List.mem_cons.mp hx).elim (fun h => h ▸ hlneg) (fun hx' => hih.2.2.2 x hx' hne)⟩
        · trivial
      · trivial
    | none =>
      cases cand with
      | none =>
        have hih := ih (some l) fun u hu => by
          simp only [Option.some.injEq] at hu; subst hu; exact hl
        cases hres : classifyClauseAux trail ls (some l) with
        | falsified => rw [hres] at hih; exact absurd hih.1 (by simp)
        | unit u =>
          rw [hres] at hih; have hu_eq := hih.2.1 l rfl
          refine ⟨hih.1, fun _ hc => (by cases hc), fun _ => by simp [hu_eq], fun x hx hne => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hls
          · exact absurd hu_eq hne.symm
          · exact hih.2.2.2 x hls hne
        | _ => trivial
      | some w =>
        by_cases hwl : w = l
        · subst hwl; simp only [beq_self_eq_true, ↓reduceIte]
          have hih := ih (some w) hcand
          cases hres : classifyClauseAux trail ls (some w) with
          | falsified => rw [hres] at hih; exact absurd hih.1 (by simp)
          | unit u =>
            rw [hres] at hih; have hu_eq := hih.2.1 w rfl
            refine ⟨hih.1, hih.2.1, fun hc => (by cases hc), fun x hx hne => ?_⟩
            rcases List.mem_cons.mp hx with rfl | hls
            · exact absurd hu_eq hne.symm
            · exact hih.2.2.2 x hls hne
          | _ => trivial
        · simp [beq_false_of_ne hwl]

theorem decisionsAtMost_assignProp {s : CdclState} {l lvl : Nat} {rsn : Reason} {k : Nat}
    (hun : litStatus s.trail l = none) (hrsn : rsn ≠ .decision) :
    decisionsAtMost (assignLit s l lvl rsn) k = decisionsAtMost s k := by
  have hnovar := litStatus_none_no_var hun
  simp only [decisionsAtMost, trail_assignLit, Array.toList_push, List.filter_append,
    List.filter_cons, List.filter_nil, stateReason_assignLit, ↓reduceIte, hrsn, decide_false,
    Bool.false_and, Bool.false_eq_true]
  rw [List.append_nil]
  apply List.filter_congr
  intro x hx
  have hne : litVar x ≠ litVar l := hnovar x hx
  simp [hne]

private theorem unitPropUnitsAux_inv {s : CdclState} (hinv : TrailInv s) :
    ∀ us, (∀ u ∈ us, s.f0.EntailsClause (cnfClause [u])) →
    match unitPropUnitsAux s us with
    | none => True
    | some (.unchanged s') => s' = s
    | some (.propagated s') =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.level = s.level ∧
      ∀ k, decisionsAtMost s' k = decisionsAtMost s k
    | some (.conflict clits s') =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.level = s.level ∧
      s'.f0.EntailsClause (cnfClause clits) ∧ (∀ l ∈ clits, litNeg l ∈ s'.trail.toList) ∧
      ∀ k, decisionsAtMost s' k = decisionsAtMost s k := by
  intro us hus
  induction us with
  | nil => simp [unitPropUnitsAux]
  | cons u us ih =>
    simp only [unitPropUnitsAux]
    have hu_ent : s.f0.EntailsClause (cnfClause [u]) := hus u (by simp)
    cases hst : litStatus s.trail u with
    | some b =>
      cases b
      · have hlneg := (litStatus_eq_some_false hinv.vars_nodup).mp hst
        have hinc : (s.level == 0) = true → s.f0.Unsat := fun hl0 =>
          unsat_of_conflict hinv (by simpa using hl0) hu_ent
            (fun l hl => (List.mem_singleton.mp hl) ▸ hlneg)
        refine ⟨⟨hinv.vars_nodup, hinv.levels_le, hinv.levels_mono, hinv.dec_earliest,
          hinv.db_sound, hinv.units_sound, hinv.reason_dag, fun h => hinc h⟩,
          rfl, rfl, hu_ent, fun l hl => (List.mem_singleton.mp hl) ▸ hlneg, fun _ => rfl⟩
      · exact ih fun v hv => hus v (List.mem_cons_of_mem _ hv)
    | none =>
      by_cases hl0 : s.level = 0
      · have hl0b : (s.level == 0) = true := by simp [hl0]
        simp only [hl0b, ↓reduceIte]
        have hpush := assignProp_inv (s := s) (rsn := .unit) hinv hst (by simp)
          (by simpa [ReasonOk, hl0] using hu_ent)
        rw [hl0] at hpush
        exact ⟨hpush.1, hpush.2, rfl, fun k => decisionsAtMost_assignProp hst (by simp)⟩
      · have hl0b : (s.level == 0) = false := beq_false_of_ne hl0
        simp only [hl0b, Bool.false_eq_true, ↓reduceIte]
        exact ih fun v hv => hus v (List.mem_cons_of_mem _ hv)

private theorem pred_of_falsified {s : CdclState} (hinv : TrailInv s) {x : Nat}
    (hx : litNeg x ∈ s.trail.toList) :
    ∃ (j : Nat) (hj : j < s.trail.size),
      s.trail[j] = litNeg x ∧ stateLevel s x ≤ s.level ∧
      lexLt (stateLevel s x) j s.level s.trail.size := by
  obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp hx
  have hle : stateLevel s x ≤ s.level := by
    have := hinv.levels_le j hj
    simpa [hjeq, stateLevel] using this
  refine ⟨j, hj, hjeq, hle, ?_⟩
  by_cases hlt : stateLevel s x < s.level
  · exact Or.inl hlt
  · exact Or.inr ⟨by omega, hj⟩

private theorem unitReasonFor_ok {s : CdclState} (hinv : TrailInv s) {cid u : Nat} {c : Clause}
    (hget : s.clauses[cid]? = some (some c)) (hng : !c.garbage = true)
    (humem : u ∈ c.lits)
    (hall : ∀ x ∈ c.lits, x ≠ u → litNeg x ∈ s.trail.toList) :
    unitReasonFor cid c.lits u ≠ .decision ∧
    ReasonOk s u s.level (unitReasonFor cid c.lits u) := by
  unfold unitReasonFor
  split
  · rename_i a b heq
    rw [heq] at humem hall
    by_cases h1 : (a == u && b != u) = true
    · simp only [h1, ↓reduceIte, ReasonOk, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h1
      have hc_ent := hinv.db_sound cid c hget
      rw [heq, h1.1] at hc_ent
      exact ⟨hc_ent, pred_of_falsified hinv (hall b (by simp) h1.2)⟩
    · have h1f : (a == u && b != u) = false := Bool.eq_false_iff.mpr h1
      simp only [h1f, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (b == u && a != u) = true
      · simp only [h2, ↓reduceIte, ReasonOk, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h2
        have hc_ent := hinv.db_sound cid c hget
        rw [heq, h2.1] at hc_ent
        exact ⟨entails_swap2 hc_ent, pred_of_falsified hinv (hall a (by simp) h2.2)⟩
      · have h2f : (b == u && a != u) = false := Bool.eq_false_iff.mpr h2
        simp only [h2f, Bool.false_eq_true, ↓reduceIte, ReasonOk, ne_eq, reduceCtorEq,
          not_false_eq_true, true_and]
        exact ⟨c, hget, hng, by simpa [← heq] using humem,
          fun x hx hne => pred_of_falsified hinv (hall x (heq ▸ hx) hne)⟩
  · refine ⟨by simp, c, hget, hng, humem, fun x hx hne => pred_of_falsified hinv (hall x hx hne)⟩

private theorem classifyClause_falsified {trail : Array Nat}
    (hnodup : ∀ i j, (hi : i < trail.size) → (hj : j < trail.size) →
      litVar trail[i] = litVar trail[j] → i = j)
    {lits : List Nat} (h : classifyClause trail lits = .falsified) :
    ∀ x ∈ lits, litNeg x ∈ trail.toList := by
  have hcs := classifyClauseAux_sound hnodup lits none (fun _ h => by cases h)
  dsimp only [classifyClause] at h; rw [h] at hcs; exact hcs.2

private theorem classifyClause_unit {trail : Array Nat}
    (hnodup : ∀ i j, (hi : i < trail.size) → (hj : j < trail.size) →
      litVar trail[i] = litVar trail[j] → i = j)
    {lits : List Nat} {u : Nat} (h : classifyClause trail lits = .unit u) :
    litStatus trail u = none ∧ u ∈ lits ∧ ∀ x ∈ lits, x ≠ u → litNeg x ∈ trail.toList := by
  have hcs := classifyClauseAux_sound hnodup lits none (fun _ h => by cases h)
  dsimp only [classifyClause] at h; rw [h] at hcs; exact ⟨hcs.1, hcs.2.2.1 rfl, hcs.2.2.2⟩

private theorem unitPropClausesAux_inv {s : CdclState} (hinv : TrailInv s) (idx : Nat) :
    match unitPropClausesAux s idx with
    | .unchanged s' => s' = s
    | .propagated s' =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.level = s.level ∧
      ∀ k, decisionsAtMost s' k = decisionsAtMost s k
    | .conflict clits s' =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.level = s.level ∧
      s'.f0.EntailsClause (cnfClause clits) ∧ (∀ l ∈ clits, litNeg l ∈ s'.trail.toList) ∧
      ∀ k, decisionsAtMost s' k = decisionsAtMost s k := by
  fun_induction unitPropClausesAux s idx with
  | case1 idx hlt c hget hc_garb ih => exact ih
  | case2 idx hlt c hget hc_ng hcls =>
    have hfals := classifyClause_falsified hinv.vars_nodup hcls
    have hc_ent := hinv.db_sound idx c (by simp [Array.getElem?_eq_getElem hlt, hget])
    have hinc : (s.level == 0) = true → s.f0.Unsat := fun hl0 =>
      unsat_of_conflict hinv (by simpa using hl0) hc_ent hfals
    refine ⟨⟨hinv.vars_nodup, hinv.levels_le, hinv.levels_mono, hinv.dec_earliest,
      hinv.db_sound, hinv.units_sound, hinv.reason_dag, fun h => hinc h⟩,
      rfl, rfl, hc_ent, hfals, fun _ => rfl⟩
  | case3 idx hlt c hget hc_ng u hcls =>
    have hgarb : !c.garbage = true := by cases hcb : c.garbage <;> simp_all
    obtain ⟨hun, humem, hall⟩ := classifyClause_unit hinv.vars_nodup hcls
    obtain ⟨hrsn_ne, hrsn_ok⟩ := unitReasonFor_ok hinv (cid := idx) (c := c)
      (by rw [Array.getElem?_eq_getElem hlt, hget]) hgarb humem hall
    have hpush := assignProp_inv hinv hun hrsn_ne hrsn_ok
    exact ⟨hpush.1, hpush.2, rfl, fun k => decisionsAtMost_assignProp hun hrsn_ne⟩
  | case4 idx hlt c hget hc_ng hcls ih => exact ih
  | case5 idx hlt c hget hc_ng hcls ih => exact ih
  | case6 idx hlt hget ih => exact ih
  | case7 idx hlt => rfl

theorem unitPropStep_inv {s : CdclState} (hinv : TrailInv s) :
    match unitPropStep s with
    | .unchanged s' => s' = s
    | .propagated s' =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.level = s.level ∧
      ∀ k, decisionsAtMost s' k = decisionsAtMost s k
    | .conflict clits s' =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.level = s.level ∧
      s'.f0.EntailsClause (cnfClause clits) ∧ (∀ l ∈ clits, litNeg l ∈ s'.trail.toList) ∧
      ∀ k, decisionsAtMost s' k = decisionsAtMost s k := by
  unfold unitPropStep
  have hu := unitPropUnitsAux_inv hinv s.units hinv.units_sound
  cases h : unitPropUnitsAux s s.units with
  | none => exact unitPropClausesAux_inv hinv 0
  | some res => rw [h] at hu; cases res <;> exact hu

theorem propagateAll_inv {fuel : Nat} {s : CdclState} (hinv : TrailInv s) :
    match propagateAll fuel s with
    | .ok s' | .outOfFuel s' =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.level = s.level ∧
      ∀ k, decisionsAtMost s' k = decisionsAtMost s k
    | .conflict clits s' =>
      TrailInv s' ∧ s'.f0 = s.f0 ∧ s'.level = s.level ∧
      s'.f0.EntailsClause (cnfClause clits) ∧ (∀ l ∈ clits, litNeg l ∈ s'.trail.toList) ∧
      ∀ k, decisionsAtMost s' k = decisionsAtMost s k := by
  induction fuel generalizing s with
  | zero => exact ⟨hinv, rfl, rfl, fun _ => rfl⟩
  | succ fuel ih =>
    simp only [propagateAll]
    have hstep := unitPropStep_inv hinv
    cases hs : unitPropStep s with
    | unchanged s' =>
      rw [hs] at hstep; subst hstep
      exact ⟨hinv, rfl, rfl, fun _ => rfl⟩
    | propagated s' =>
      rw [hs] at hstep
      obtain ⟨hinv', hf0', hlvl', hdec'⟩ := hstep
      have hih := ih hinv'
      dsimp only
      cases hp : propagateAll fuel s' with
      | ok s'' =>
        rw [hp] at hih
        exact ⟨hih.1, hih.2.1.trans hf0', hih.2.2.1.trans hlvl',
          fun k => (hih.2.2.2 k).trans (hdec' k)⟩
      | outOfFuel s'' =>
        rw [hp] at hih
        exact ⟨hih.1, hih.2.1.trans hf0', hih.2.2.1.trans hlvl',
          fun k => (hih.2.2.2 k).trans (hdec' k)⟩
      | conflict clits s'' =>
        rw [hp] at hih
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hih
        exact ⟨h1, h2.trans hf0', h3.trans hlvl', h4, h5, fun k => (h6 k).trans (hdec' k)⟩
    | conflict clits s' =>
      rw [hs] at hstep
      exact hstep

end LeanQbe.T.Examples.Kissat.Ref
