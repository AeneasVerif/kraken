/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Substitute
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Trail

/-!
# Soundness Proofs for `Substitute`

Extracted pure-Lean proofs for `Substitute` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Single-step equivalence substitution and model reconstruction -/

theorem equivEntailed_eval {f : CNF Nat} {v l : Nat} {α : Nat → Bool}
    (heq : EquivEntailed f v l) (hα : f.Sat α) :
    α v = evalLitVal α l := by
  have h1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp heq.1 α hα)
  have h2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp heq.2 α hα)
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    evalLitVal_mkLit, evalLitVal_litNeg] at h1 h2
  cases hv : α v <;> cases hl : evalLitVal α l <;> simp_all

private theorem clause_sat_map_iff (f : Nat → Nat) (α' α : Nat → Bool)
    (hdual : ∀ x, evalLitVal α' x = evalLitVal α (f x)) (c : List Nat) :
    (cnfClause (c.map f)).Sat α ↔ (cnfClause c).Sat α' := by
  simp only [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hsat⟩; exact ⟨x, hx, by rwa [hdual]⟩
  · rintro ⟨x, hx, hsat⟩; exact ⟨f x, ⟨x, hx, rfl⟩, by rwa [← hdual]⟩

private theorem mapClauses_sat_fwd {f : Nat → Nat} {fα : (Nat → Bool) → (Nat → Bool)}
    {cnf : CNF Nat} {α : Nat → Bool}
    (hdual : ∀ β x, evalLitVal (fα β) x = evalLitVal β (f x))
    (hid : fα α = α) (hα : cnf.Sat α) :
    (cnfOfClauses ((clausesOfCnf cnf).filterMap (mapClauseTaut f))).Sat α := by
  rw [cnf_sat_cnfOfClauses_iff]
  intro c' hc'
  rw [List.mem_filterMap] at hc'
  obtain ⟨c, hc, hsub⟩ := hc'
  unfold mapClauseTaut at hsub; dsimp only at hsub
  split at hsub
  · cases hsub
  · injection hsub with hce
    rw [← hce, clause_sat_dedup_iff, clause_sat_map_iff f (fα α) α (hdual α), hid]
    exact (sat_iff_clausesOfCnf α cnf).mp hα c hc

private theorem mapClauses_sat_recon {f : Nat → Nat} {fα : (Nat → Bool) → (Nat → Bool)}
    {cnf : CNF Nat} {α : Nat → Bool}
    (hdual : ∀ β x, evalLitVal (fα β) x = evalLitVal β (f x))
    (hα : (cnfOfClauses ((clausesOfCnf cnf).filterMap (mapClauseTaut f))).Sat α) :
    cnf.Sat (fα α) := by
  rw [sat_iff_clausesOfCnf]
  intro c hc
  rw [← clause_sat_map_iff f (fα α) α (hdual α), ← clause_sat_dedup_iff]
  by_cases ht : clauseIsTaut (dedupLits (c.map f)) = true
  · exact clauseIsTaut_sat ht α
  · have hmem : dedupLits (c.map f) ∈ (clausesOfCnf cnf).filterMap (mapClauseTaut f) :=
      List.mem_filterMap.mpr ⟨c, hc, by simp [mapClauseTaut, ht]⟩
    exact (cnf_sat_cnfOfClauses_iff α _).mp hα _ hmem

theorem substLit_litNeg (v l x : Nat) :
    substLit v l (litNeg x) = litNeg (substLit v l x) := by
  simp only [substLit, litVar_litNeg, litSign_litNeg]
  split
  · cases litSign x <;> simp
  · rfl

theorem litVar_substLit_ne {v l : Nat} (hne : litVar l ≠ v) (x : Nat) :
    litVar (substLit v l x) ≠ v := by
  unfold substLit
  split
  · cases litSign x <;> simpa
  · rename_i h; simpa using h

/-- Fundamental substitution-extension duality on literals: evaluating `x` under `α[v ↦ α.eval l]`
equals evaluating `substLit v l x` under `α`. -/
theorem evalLitVal_substExtend (v l : Nat) (α : Nat → Bool) (x : Nat) :
    evalLitVal (substExtend v l α) x = evalLitVal α (substLit v l x) := by
  unfold substExtend substLit
  by_cases hx : litVar x = v
  · simp only [hx, beq_self_eq_true, ↓reduceIte, evalLitVal, substUpdate_self]
    cases hs : litSign x <;> simp
  · simp only [beq_false_of_ne hx, Bool.false_eq_true, ↓reduceIte]
    exact evalLitVal_substUpdate_ne α (evalLitVal α l) hx

theorem evalLitVal_substLit_of_eq {v l : Nat} {α : Nat → Bool}
    (heq : α v = evalLitVal α l) (x : Nat) :
    evalLitVal α (substLit v l x) = evalLitVal α x := by
  rw [← evalLitVal_substExtend]
  have hfn : substExtend v l α = α := by
    funext w; unfold substExtend substUpdate
    by_cases hw : w = v <;> simp [hw, heq]
  rw [hfn]

theorem clause_sat_subst_map_iff (v l : Nat) (α : Nat → Bool) (c : List Nat) :
    (cnfClause (c.map (substLit v l))).Sat α ↔ (cnfClause c).Sat (substExtend v l α) :=
  clause_sat_map_iff (substLit v l) (substExtend v l α) α (evalLitVal_substExtend v l α) c

theorem substExtend_agrees_ne (v l : Nat) (α : Nat → Bool) {w : Nat} (hne : w ≠ v) :
    substExtend v l α w = α w :=
  substUpdate_ne α (evalLitVal α l) hne

/-- When `litVar l ≠ v`, the reconstructed assignment `substExtend v l α` satisfies both
implication clauses of `v ↔ l`. -/
theorem substExtend_equiv_sat {v l : Nat} (hne : litVar l ≠ v) (α : Nat → Bool) :
    (cnfClause [mkLit v false, l]).Sat (substExtend v l α) ∧
    (cnfClause [mkLit v true, litNeg l]).Sat (substExtend v l α) := by
  have hl : evalLitVal (substExtend v l α) l = evalLitVal α l :=
    evalLitVal_substUpdate_ne α (evalLitVal α l) hne
  simp only [← clauseEvalVal_iff, clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    evalLitVal_mkLit, evalLitVal_litNeg, hl]
  simp only [substExtend, substUpdate_self]
  cases evalLitVal α l <;> decide

/-- Forward satisfiability preservation for single-step equivalence substitution. -/
theorem subst_sat_fwd {f : CNF Nat} {v l : Nat} {α : Nat → Bool}
    (heq : EquivEntailed f v l) (hα : f.Sat α) :
    (substCnf v l f).Sat α := by
  have hval := equivEntailed_eval heq hα
  have hfn : substExtend v l α = α := by
    funext w; unfold substExtend substUpdate
    by_cases hw : w = v <;> simp [hw, hval]
  exact mapClauses_sat_fwd (evalLitVal_substExtend v l) hfn hα

/-- UNSAT soundness of single-step equivalence substitution (`F'.Unsat → F.Unsat`). -/
theorem subst_unsat_sound {f : CNF Nat} {v l : Nat}
    (heq : EquivEntailed f v l) (hu : (substCnf v l f).Unsat) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  exact fun α hα => hu α (subst_sat_fwd heq hα)

/-- Explicit SAT model reconstruction for single-step substitution: any model `α` of
`substCnf v l f` reconstructs to `α' = substExtend v l α` satisfying `f`. -/
theorem subst_sat_reconstruct {f : CNF Nat} {v l : Nat} {α : Nat → Bool}
    (hα : (substCnf v l f).Sat α) :
    f.Sat (substExtend v l α) :=
  mapClauses_sat_recon (evalLitVal_substExtend v l) hα

/-- Equisatisfiability of single-step equivalence substitution. -/
theorem subst_equisat {f : CNF Nat} {v l : Nat} (heq : EquivEntailed f v l) :
    (∃ α, f.Sat α) ↔ (∃ α, (substCnf v l f).Sat α) :=
  ⟨fun ⟨α, hα⟩ => ⟨α, subst_sat_fwd heq hα⟩,
    fun ⟨α, hα⟩ => ⟨substExtend v l α, subst_sat_reconstruct hα⟩⟩

/-- UNSAT equivalence for single-step equivalence substitution. -/
theorem subst_unsat_iff {f : CNF Nat} {v l : Nat} (heq : EquivEntailed f v l) :
    f.Unsat ↔ (substCnf v l f).Unsat := by
  simp only [CNF.unsat_iff_not_sat]
  exact ⟨fun hu α hα => hu (substExtend v l α) (subst_sat_reconstruct hα),
    fun hu α hα => hu α (subst_sat_fwd heq hα)⟩

/-- Variable elimination guarantee: when `litVar l ≠ v`, variable `v` no longer occurs anywhere
in `substCnf v l f`. -/
theorem subst_var_elim {f : CNF Nat} {v l : Nat} (hne : litVar l ≠ v) :
    VarFreshCnf (substCnf v l f) v := by
  intro c' hc' x hx
  rw [substCnf, clausesOfCnf_cnfOfClauses, substClauses, List.mem_filterMap] at hc'
  obtain ⟨c, _, hsub⟩ := hc'
  unfold substClause mapClauseTaut at hsub
  dsimp only at hsub
  split at hsub
  · cases hsub
  · injection hsub with hce
    rw [← hce] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp (mem_dedupLits_iff.mp hx)
    exact litVar_substLit_ne hne y

/-! ## 2. Multi-step substitution trace and witness stack composition -/

theorem substTraceApply_cnfOfClauses (tr : SubstTrace) (cs : List (List Nat)) :
    substTraceApply tr (cnfOfClauses cs) = cnfOfClauses (substTraceApplyClauses tr cs) := by
  induction tr generalizing cs with
  | nil => rfl
  | cons e rest ih =>
    simp only [substTraceApply, substTraceApplyClauses, substCnf, clausesOfCnf_cnfOfClauses]
    exact ih (substClauses e.var e.repr cs)

theorem substTraceApply_append (tr1 tr2 : SubstTrace) (f : CNF Nat) :
    substTraceApply (tr1 ++ tr2) f = substTraceApply tr2 (substTraceApply tr1 f) := by
  induction tr1 generalizing f with
  | nil => rfl
  | cons e rest ih => exact ih (substCnf e.var e.repr f)

theorem substExtendTrace_append (tr1 tr2 : SubstTrace) (α : Nat → Bool) :
    substExtendTrace (tr1 ++ tr2) α = substExtendTrace tr1 (substExtendTrace tr2 α) := by
  simp [substExtendTrace, List.foldr_append]

theorem substTraceValid_append {f : CNF Nat} {tr1 tr2 : SubstTrace}
    (h1 : SubstTraceValid f tr1) (h2 : SubstTraceValid (substTraceApply tr1 f) tr2) :
    SubstTraceValid f (tr1 ++ tr2) := by
  induction tr1 generalizing f with
  | nil => exact h2
  | cons e rest ih =>
    obtain ⟨hne, heq, hrest⟩ := h1
    exact ⟨hne, heq, ih hrest h2⟩

/-- Forward satisfiability preservation across a valid multi-step substitution trace. -/
theorem substTrace_sat_fwd {f : CNF Nat} {tr : SubstTrace} {α : Nat → Bool}
    (hval : SubstTraceValid f tr) (hα : f.Sat α) :
    (substTraceApply tr f).Sat α := by
  induction tr generalizing f with
  | nil => exact hα
  | cons e rest ih =>
    obtain ⟨_, heq, hrest⟩ := hval
    exact ih hrest (subst_sat_fwd heq hα)

/-- UNSAT soundness across a valid multi-step substitution trace. -/
theorem substTrace_unsat {f : CNF Nat} {tr : SubstTrace}
    (hval : SubstTraceValid f tr) (hu : (substTraceApply tr f).Unsat) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu α (substTrace_sat_fwd hval hα)

/-- Explicit SAT model reconstruction across a multi-step substitution trace. -/
theorem substTrace_sat {f : CNF Nat} {tr : SubstTrace} {α : Nat → Bool}
    (hα : (substTraceApply tr f).Sat α) :
    f.Sat (substExtendTrace tr α) := by
  induction tr generalizing f with
  | nil => exact hα
  | cons e rest ih =>
    exact subst_sat_reconstruct (ih hα)

/-- Equisatisfiability across a valid multi-step substitution trace. -/
theorem substTrace_equisat {f : CNF Nat} {tr : SubstTrace} (hval : SubstTraceValid f tr) :
    (∃ α, f.Sat α) ↔ (∃ α, (substTraceApply tr f).Sat α) :=
  ⟨fun ⟨α, hα⟩ => ⟨α, substTrace_sat_fwd hval hα⟩,
    fun ⟨α, hα⟩ => ⟨substExtendTrace tr α, substTrace_sat hα⟩⟩

/-! ## 4. Binary implication graph, SCC reachability, and simultaneous representative maps -/

theorem binEdge_of_mem_left {f : CNF Nat} {a b : Nat}
    (h : [litNeg a, b] ∈ clausesOfCnf f) : BinEdge f a b :=
  entails_mem_clausesOfCnf h

theorem binEdge_of_mem_right {f : CNF Nat} {a b : Nat}
    (h : [b, litNeg a] ∈ clausesOfCnf f) : BinEdge f a b :=
  entails_swap2 (entails_mem_clausesOfCnf h)

theorem binEdge_of_bin {f : CNF Nat} {x y : Nat}
    (h : [x, y] ∈ clausesOfCnf f) : BinEdge f (litNeg x) y ∧ BinEdge f (litNeg y) x := by
  have hx := entails_mem_clausesOfCnf h
  refine ⟨?_, ?_⟩
  · simpa [BinEdge, litNeg_litNeg] using hx
  · simpa [BinEdge, litNeg_litNeg] using entails_swap2 hx

theorem binReach_trans {f : CNF Nat} {a b c : Nat}
    (h1 : BinReach f a b) (h2 : BinReach f b c) : BinReach f a c := by
  induction h1 with
  | refl _ => exact h2
  | step hab _ ih => exact .step hab (ih h2)

/-- Every binary implication path `a →* b` entails the binary clause `[¬a, b]`. -/
theorem binReach_sound {f : CNF Nat} {a b : Nat} (hr : BinReach f a b) :
    f.EntailsClause (cnfClause [litNeg a, b]) := by
  induction hr with
  | refl x =>
    rw [CNF.entails_clause_def]
    intro α _
    exact clauseIsTaut_sat (by simp [clauseIsTaut, litNeg_litNeg]) α
  | @step x y z hxy _ ih =>
    rw [CNF.entails_clause_def]
    intro α hα
    have h1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hxy α hα)
    have h2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp ih α hα)
    rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      evalLitVal_litNeg] at h1 h2 ⊢
    cases hx : evalLitVal α x <;> cases hy : evalLitVal α y <;> simp_all

/-- Kissat `substitute.c` failed-literal implication check: `a →* ¬a` entails the unit `[¬a]`. -/
theorem binReach_failed_unit {f : CNF Nat} {a : Nat} (hr : BinReach f a (litNeg a)) :
    f.EntailsClause (cnfClause [litNeg a]) := by
  have h := binReach_sound hr
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  have hs := (clauseEvalVal_iff α _).mpr (h α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at hs ⊢
  simpa using hs

/-- Kissat `substitute.c` SCC contradiction check: if `a` and `¬a` lie in the same SCC
(`a →* ¬a` and `¬a →* a`), then `f` is unsatisfiable. -/
theorem binReach_contra_unsat {f : CNF Nat} {a : Nat}
    (h1 : BinReach f a (litNeg a)) (h2 : BinReach f (litNeg a) a) : f.Unsat := by
  have hu1 := binReach_failed_unit h1
  have hu2 : f.EntailsClause (cnfClause [a]) := by
    simpa [litNeg_litNeg] using binReach_failed_unit (a := litNeg a) (by simpa using h2)
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have s1 := (sat_cnfClause_litNeg_iff α a).mp (CNF.entails_clause_def.mp hu1 α hα)
  exact s1 (CNF.entails_clause_def.mp hu2 α hα)

/-- Kissat `substitute.c` SCC equivalence check: if `mkLit v true` and `l` are mutually reachable
in the binary implication graph, then `EquivEntailed f v l`. -/
theorem binReach_scc_equiv {f : CNF Nat} {v l : Nat}
    (h1 : BinReach f (mkLit v true) l) (h2 : BinReach f l (mkLit v true)) :
    EquivEntailed f v l := by
  refine ⟨?_, ?_⟩
  · simpa [litNeg_mkLit] using binReach_sound h1
  · exact entails_swap2 (binReach_sound h2)

theorem evalLitVal_substMapExtend (m : Nat → Nat) (α : Nat → Bool) (x : Nat) :
    evalLitVal (substMapExtend m α) x = evalLitVal α (substMapLit m x) := by
  unfold substMapExtend substMapLit
  cases hs : litSign x <;> simp [evalLitVal, hs]

theorem clause_sat_substMap_iff (m : Nat → Nat) (α : Nat → Bool) (c : List Nat) :
    (cnfClause (c.map (substMapLit m))).Sat α ↔ (cnfClause c).Sat (substMapExtend m α) :=
  clause_sat_map_iff (substMapLit m) (substMapExtend m α) α (evalLitVal_substMapExtend m α) c

/-- Forward satisfiability preservation for simultaneous SCC representative substitution. -/
theorem substMap_sat_fwd {f : CNF Nat} {m : Nat → Nat} {α : Nat → Bool}
    (hm : ∀ v, EquivEntailed f v (m v)) (hα : f.Sat α) :
    (substMapCnf m f).Sat α := by
  have hfn : substMapExtend m α = α := funext fun v => (equivEntailed_eval (hm v) hα).symm
  exact mapClauses_sat_fwd (evalLitVal_substMapExtend m) hfn hα

/-- UNSAT soundness for simultaneous SCC representative substitution. -/
theorem substMap_unsat_sound {f : CNF Nat} {m : Nat → Nat}
    (hm : ∀ v, EquivEntailed f v (m v)) (hu : (substMapCnf m f).Unsat) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  exact fun α hα => hu α (substMap_sat_fwd hm hα)

/-- Explicit SAT model reconstruction for simultaneous SCC representative substitution. -/
theorem substMap_sat_recon {f : CNF Nat} {m : Nat → Nat} {α : Nat → Bool}
    (hα : (substMapCnf m f).Sat α) :
    f.Sat (substMapExtend m α) :=
  mapClauses_sat_recon (evalLitVal_substMapExtend m) hα

/-- Equisatisfiability for simultaneous SCC representative substitution. -/
theorem substMap_equisat {f : CNF Nat} {m : Nat → Nat}
    (hm : ∀ v, EquivEntailed f v (m v)) :
    (∃ α, f.Sat α) ↔ (∃ α, (substMapCnf m f).Sat α) :=
  ⟨fun ⟨α, hα⟩ => ⟨α, substMap_sat_fwd hm hα⟩,
    fun ⟨α, hα⟩ => ⟨substMapExtend m α, substMap_sat_recon hα⟩⟩

/-! ## 5. Executable `Array Bool` model reconstruction bridge -/

theorem hasBinEdge_sound {cs : List (List Nat)} {a b : Nat}
    (h : hasBinEdge cs a b = true) : BinEdge (cnfOfClauses cs) a b := by
  unfold hasBinEdge at h
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with h1 | h2
  · exact binEdge_of_mem_left (by simpa using h1)
  · exact binEdge_of_mem_right (by simpa using h2)

theorem checkBinPath_sound {cs : List (List Nat)} :
    ∀ {a : Nat} {path : List Nat} {b : Nat},
      checkBinPath cs a path b = true → BinReach (cnfOfClauses cs) a b
  | a, [], b, h => by
    simp only [checkBinPath, beq_iff_eq] at h; subst h; exact .refl a
  | a, next :: rest, b, h => by
    simp only [checkBinPath, Bool.and_eq_true] at h
    exact .step (hasBinEdge_sound h.1) (checkBinPath_sound h.2)

theorem evalVar_substExtendArr (v l : Nat) (σ : Array Bool) :
    evalVar (substExtendArr v l σ) = substExtend v l (evalVar σ) :=
  evalVar_arraySetPad σ v (evalLit σ l)

theorem evalVar_substTraceExtendArr (tr : SubstTrace) (σ : Array Bool) :
    evalVar (substTraceExtendArr tr σ) = substExtendTrace tr (evalVar σ) := by
  induction tr with
  | nil => rfl
  | cons e rest ih =>
    unfold substTraceExtendArr substExtendTrace
    simp only [List.foldr_cons]
    rw [evalVar_substExtendArr]
    exact congrArg (substExtend e.var e.repr) ih

/-- Executable `checkModel` soundness bridge across a multi-step substitution trace. -/
theorem substTraceExtendArr_sound {f : CNF Nat} {tr : SubstTrace} {σ : Array Bool}
    (h : checkModel (substTraceApply tr f) σ = true) :
    checkModel f (substTraceExtendArr tr σ) = true := by
  rw [checkModel_iff_sat] at h ⊢
  rw [evalVar_substTraceExtendArr]
  exact substTrace_sat h

theorem evalVar_substTableExtendArr (tbl : Array Nat) (σ : Array Bool) :
    evalVar (substTableExtendArr tbl σ) = substMapExtend (reprOfTable tbl) (evalVar σ) := by
  funext v
  unfold substTableExtendArr substMapExtend evalVar
  by_cases hv : v < Nat.max σ.size tbl.size
  · simp [hv, evalLit, evalLitVal, evalVar]
  · have hge : Nat.max σ.size tbl.size ≤ v := Nat.le_of_not_lt hv
    have hv1 : σ.size ≤ v := Nat.le_trans (Nat.le_max_left _ _) hge
    have hv2 : tbl.size ≤ v := Nat.le_trans (Nat.le_max_right _ _) hge
    have hnone1 : σ[v]? = none := Array.getElem?_eq_none hv1
    have hnone2 : tbl[v]? = none := Array.getElem?_eq_none hv2
    have hnone3 : (Array.ofFn (n := Nat.max σ.size tbl.size)
        fun i => evalLit σ (reprOfTable tbl i.val))[v]? = none :=
      Array.getElem?_eq_none (by simp [hge])
    rw [hnone3]
    simp [reprOfTable, hnone2, evalLitVal_mkLit, hnone1]

/-- Executable `checkModel` soundness bridge for simultaneous SCC representative table. -/
theorem substTableExtendArr_sound {f : CNF Nat} {tbl : Array Nat} {σ : Array Bool}
    (h : checkModel (substMapCnf (reprOfTable tbl) f) σ = true) :
    checkModel f (substTableExtendArr tbl σ) = true := by
  rw [checkModel_iff_sat] at h ⊢
  rw [evalVar_substTableExtendArr]
  exact substMap_sat_recon h

end LeanQbe.T.Examples.Kissat.Ref
