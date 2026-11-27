/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Cdcl
public import LeanQbe.T.Examples.Kissat.Ref.Substitute

/-!
# Pure Lean Layer-A Inprocessing Theory: Bounded Variable Elimination

Pure Lean formalization (zero `Kraken.Mem` or `Kraken.Separation` imports) of single- and
multi-pivot bounded variable elimination (`BVE`, `bveElim`, `bveElimCnf`, `bveBoundedElim`) and
LIFO SAT witness reconstruction (`BveWitness`, `BveStack`, `extendBve`, `extendBveArray`)
modeling `kissat_extend`, plus end-to-end integration with `cdclSolve`:

1. **Tautology & literal helpers**: `litVar_eq_iff_mkLit`, `clauseIsTaut_congr`,
   `sat_cnfClause_congr`, `setModelVar`, `resolveOn_comm_mem` (reusing `Substitute`'s
   `clauseIsTaut`, `substUpdate`, and `clauseEvalVal`).
2. **Single-step pivot partition, UNSAT soundness & witness reconstruction**: `bvePartition`,
   `bveClauses`, `bve_unsat_sound`, `extendBveStep_sound`, `extendBveStep_sat`,
   `extendBveStepArr_sound`.
3. **Iterated elimination & LIFO witness stack**: `BveStack`, `bveStep`, `bveElim`,
   `bveElimCnf`, `bveBoundedElim`, `bveElim_unsat_sound`, `extendBve_sound`,
   `extendBveArray_cnf`, `bveElim_equisat`, and `cdclSolveAfterBve_sound`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Model variable update helper -/

/-- Pointwise variable update on executable `Array Bool` model. -/
@[expose] def setModelVar (σ : Array Bool) (v : Nat) (b : Bool) : Array Bool :=
  arraySetPad σ v b false

@[simp] theorem evalVar_setModelVar (σ : Array Bool) (v : Nat) (b : Bool) (x : Nat) :
    evalVar (setModelVar σ v b) x = substUpdate (evalVar σ) v b x :=
  congrFun (evalVar_arraySetPad σ v b) x

/-! ## 2. Pivot partition, BVE resolvents, and `bve` formula transformation -/

/-- Partition clauses on pivot variable `v` into `(P, N, R)`:
`P` (`pos ∈ C ∧ neg ∉ C`), `N` (`neg ∈ D ∧ pos ∉ D`), `R` (`pos ∉ C ∧ neg ∉ C`),
dropping tautological clauses that contain both `pos` and `neg`. -/
@[expose] def bvePartition (cs : List (List Nat)) (v : Nat) :
    List (List Nat) × List (List Nat) × List (List Nat) :=
  let pos := mkLit v true
  let neg := mkLit v false
  cs.foldr (fun c acc =>
    let (p, n, r) := acc
    if c.contains pos then
      if c.contains neg then (p, n, r) else (c :: p, n, r)
    else if c.contains neg then (p, c :: n, r)
    else (p, n, c :: r)) ([], [], [])

theorem bvePartition_props (cs : List (List Nat)) (v : Nat) :
    let (p, n, r) := bvePartition cs v
    let pos := mkLit v true
    let neg := mkLit v false
    (∀ c ∈ p, c ∈ cs ∧ pos ∈ c ∧ neg ∉ c) ∧
    (∀ d ∈ n, d ∈ cs ∧ neg ∈ d ∧ pos ∉ d) ∧
    (∀ r0 ∈ r, r0 ∈ cs ∧ pos ∉ r0 ∧ neg ∉ r0) ∧
    (∀ c ∈ cs, (pos ∈ c ∧ neg ∈ c) ∨ c ∈ p ∨ c ∈ n ∨ c ∈ r) := by
  unfold bvePartition
  induction cs with
  | nil => simp
  | cons c rest ih =>
    dsimp only at ih ⊢
    obtain ⟨hp, hn, hr, hall⟩ := ih
    simp only [List.foldr_cons]
    by_cases hpos : c.contains (mkLit v true) = true
    · have hpm : mkLit v true ∈ c := List.contains_iff_mem.mp hpos
      by_cases hneg : c.contains (mkLit v false) = true
      · have hnm : mkLit v false ∈ c := List.contains_iff_mem.mp hneg
        simp only [hpos, hneg, ↓reduceIte]
        refine ⟨fun x hx => ⟨List.mem_cons_of_mem _ (hp x hx).1, (hp x hx).2⟩,
          fun x hx => ⟨List.mem_cons_of_mem _ (hn x hx).1, (hn x hx).2⟩,
          fun x hx => ⟨List.mem_cons_of_mem _ (hr x hx).1, (hr x hx).2⟩, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hrest
        · exact Or.inl ⟨hpm, hnm⟩
        · rcases hall x hrest with ht | h1 | h2 | h3
          · exact Or.inl ht
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl h2))
          · exact Or.inr (Or.inr (Or.inr h3))
      · have hnm : mkLit v false ∉ c := fun h => hneg (List.contains_iff_mem.mpr h)
        simp only [hpos, hneg, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun x hx => (List.mem_cons.mp hx).elim
            (fun h => by subst h; exact ⟨List.mem_cons_self, hpm, hnm⟩)
            (fun h => ⟨List.mem_cons_of_mem _ (hp x h).1, (hp x h).2⟩),
          fun x hx => ⟨List.mem_cons_of_mem _ (hn x hx).1, (hn x hx).2⟩,
          fun x hx => ⟨List.mem_cons_of_mem _ (hr x hx).1, (hr x hx).2⟩, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hrest
        · exact Or.inr (Or.inl List.mem_cons_self)
        · rcases hall x hrest with ht | h1 | h2 | h3
          · exact Or.inl ht
          · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
          · exact Or.inr (Or.inr (Or.inl h2))
          · exact Or.inr (Or.inr (Or.inr h3))
    · have hpm : mkLit v true ∉ c := fun h => hpos (List.contains_iff_mem.mpr h)
      by_cases hneg : c.contains (mkLit v false) = true
      · have hnm : mkLit v false ∈ c := List.contains_iff_mem.mp hneg
        simp only [hpos, Bool.false_eq_true, ↓reduceIte, hneg]
        refine ⟨fun x hx => ⟨List.mem_cons_of_mem _ (hp x hx).1, (hp x hx).2⟩,
          fun x hx => (List.mem_cons.mp hx).elim
            (fun h => by subst h; exact ⟨List.mem_cons_self, hnm, hpm⟩)
            (fun h => ⟨List.mem_cons_of_mem _ (hn x h).1, (hn x h).2⟩),
          fun x hx => ⟨List.mem_cons_of_mem _ (hr x hx).1, (hr x hx).2⟩, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hrest
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · rcases hall x hrest with ht | h1 | h2 | h3
          · exact Or.inl ht
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ h2)))
          · exact Or.inr (Or.inr (Or.inr h3))
      · have hnm : mkLit v false ∉ c := fun h => hneg (List.contains_iff_mem.mpr h)
        simp only [hpos, hneg, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun x hx => ⟨List.mem_cons_of_mem _ (hp x hx).1, (hp x hx).2⟩,
          fun x hx => ⟨List.mem_cons_of_mem _ (hn x hx).1, (hn x hx).2⟩,
          fun x hx => (List.mem_cons.mp hx).elim
            (fun h => by subst h; exact ⟨List.mem_cons_self, hpm, hnm⟩)
            (fun h => ⟨List.mem_cons_of_mem _ (hr x h).1, (hr x h).2⟩), fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hrest
        · exact Or.inr (Or.inr (Or.inr List.mem_cons_self))
        · rcases hall x hrest with ht | h1 | h2 | h3
          · exact Or.inl ht
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl h2))
          · exact Or.inr (Or.inr (Or.inr (List.mem_cons_of_mem _ h3)))

/-- All non-tautological resolvents `(C \ {pos}) ++ (D \ {¬pos})` for `C ∈ P`, `D ∈ N`. -/
@[expose] def bveResolvents (pos : Nat) (p n : List (List Nat)) : List (List Nat) :=
  (p.flatMap fun c => n.map fun d => resolveOn pos c d).filter fun r => !clauseIsTaut r

theorem mem_bveResolvents_iff (pos : Nat) (p n : List (List Nat)) (r : List Nat) :
    r ∈ bveResolvents pos p n ↔
      (∃ c ∈ p, ∃ d ∈ n, r = resolveOn pos c d) ∧ clauseIsTaut r = false := by
  simp only [bveResolvents, List.mem_filter, List.mem_flatMap, List.mem_map, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨c, hc, d, hd, heq⟩, hnt⟩
    exact ⟨⟨c, hc, d, hd, heq.symm⟩, hnt⟩
  · rintro ⟨⟨c, hc, d, hd, rfl⟩, hnt⟩
    exact ⟨⟨c, hc, d, hd, rfl⟩, hnt⟩

/-- Clauses after bounded variable elimination on variable `v`. -/
@[expose] def bveClauses (cs : List (List Nat)) (v : Nat) : List (List Nat) :=
  let (p, n, r) := bvePartition cs v
  bveResolvents (mkLit v true) p n ++ r

/-- Bounded variable elimination on `cnf : CNF Nat` for pivot variable `v`. -/
@[expose] def bve (cnf : CNF Nat) (v : Nat) : CNF Nat :=
  cnfOfClauses (bveClauses (clausesOfCnf cnf) v)

/-! ## 3. UNSAT soundness and pivot elimination -/

/-- Variable `v` does not appear anywhere in `bveClauses cs v`. -/
theorem bve_var_absent (cs : List (List Nat)) (v : Nat) :
    ∀ cl ∈ bveClauses cs v, ∀ l ∈ cl, litVar l ≠ v := by
  have hp := bvePartition_props cs v
  dsimp only at hp
  obtain ⟨hpp, hpn, hpr, _⟩ := hp
  intro cl hcl l hl hv
  unfold bveClauses at hcl
  rcases List.mem_append.mp hcl with hr | hrem
  · obtain ⟨⟨c, hc, d, hd, rfl⟩, _⟩ := (mem_bveResolvents_iff _ _ _ _).mp hr
    have h1 := hpp c hc
    have h2 := hpn d hd
    rw [litVar_eq_iff_mkLit] at hv
    simp only [resolveOn, List.mem_append, List.mem_filter, bne_iff_ne] at hl
    rcases hl with ⟨hlc, hnec⟩ | ⟨hld, hned⟩
    · rcases hv with rfl | rfl
      · exact hnec rfl
      · exact h1.2.2 hlc
    · rw [litNeg_mkLit] at hned
      rcases hv with rfl | rfl
      · exact h2.2.2 hld
      · exact hned rfl
  · have h3 := hpr cl hrem
    rw [litVar_eq_iff_mkLit] at hv
    rcases hv with rfl | rfl
    · exact h3.2.1 hl
    · exact h3.2.2 hl

/-- Forward satisfaction: every model of `cs` satisfies `bveClauses cs v`. -/
theorem bveClauses_sat_of_sat {α : Nat → Bool} {cs : List (List Nat)} {v : Nat}
    (h : (cnfOfClauses cs).Sat α) :
    (cnfOfClauses (bveClauses cs v)).Sat α := by
  have hp := bvePartition_props cs v
  dsimp only at hp
  obtain ⟨hpp, hpn, hpr, _⟩ := hp
  rw [cnf_sat_cnfOfClauses_iff] at h ⊢
  intro cl hcl
  unfold bveClauses at hcl
  rcases List.mem_append.mp hcl with hr | hrem
  · obtain ⟨⟨c, hc, d, hd, rfl⟩, _⟩ := (mem_bveResolvents_iff _ _ _ _).mp hr
    have hcs := h c (hpp c hc).1
    have hds := h d (hpn d hd).1
    have hent := entails_resolve (f := cnfOfClauses cs) (p := mkLit v true)
      (CNF.entails_clause_def.mpr fun β hβ => (cnf_sat_cnfOfClauses_iff β cs).mp hβ c (hpp c hc).1)
      (CNF.entails_clause_def.mpr fun β hβ => (cnf_sat_cnfOfClauses_iff β cs).mp hβ d (hpn d hd).1)
    exact CNF.entails_clause_def.mp hent α ((cnf_sat_cnfOfClauses_iff α cs).mpr h)
  · exact h cl (hpr cl hrem).1

/-- **BVE UNSAT soundness (clause list)**:
`(cnfOfClauses (bveClauses cs v)).Unsat → (cnfOfClauses cs).Unsat`. -/
theorem bveClauses_unsat {cs : List (List Nat)} {v : Nat}
    (hu : (cnfOfClauses (bveClauses cs v)).Unsat) : (cnfOfClauses cs).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα; exact hu α (bveClauses_sat_of_sat hα)

/-- **BVE UNSAT soundness (`CNF Nat`)**: `(bve cnf v).Unsat → cnf.Unsat`. -/
theorem bve_unsat_sound {cnf : CNF Nat} {v : Nat}
    (hu : (bve cnf v).Unsat) : cnf.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu α (bveClauses_sat_of_sat (by simpa using hα))

/-! ## 4. SAT witness reconstruction (`BveWitness`, `extendBveStep`, `extendBveStepArray`) -/

/-- Witness entry recorded when eliminating pivot variable `litVar lit` via side `lit`:
stores all clauses containing `lit` (`clauses`) for reconstruction (`kissat_extend`). -/
structure BveWitness where
  lit : Nat
  clauses : List (List Nat)
  deriving Repr, DecidableEq

/-- Choose smaller polarity side (`P` vs `N`) as the saved witness entry. -/
@[expose] def mkBveWitness (v : Nat) (p n : List (List Nat)) : BveWitness :=
  if p.length ≤ n.length then { lit := mkLit v true, clauses := p }
  else { lit := mkLit v false, clauses := n }

/-- Single-step SAT witness extension on assignment `α : Nat → Bool`: sets `w.lit` false
(`litVar w.lit := litSign w.lit`) if that satisfies all `w.clauses`, else flips `w.lit` true. -/
@[expose] def extendBveStep (w : BveWitness) (α : Nat → Bool) : Nat → Bool :=
  let αFalse := substUpdate α (litVar w.lit) (litSign w.lit)
  if w.clauses.all fun c => clauseEvalVal αFalse c then αFalse
  else substUpdate α (litVar w.lit) (!(litSign w.lit))

/-- Single-step SAT witness extension on executable `Array Bool`. -/
@[expose] def extendBveStepArray (w : BveWitness) (σ : Array Bool) : Array Bool :=
  let σFalse := setModelVar σ (litVar w.lit) (litSign w.lit)
  if w.clauses.all fun c => evalClause σFalse c then σFalse
  else setModelVar σ (litVar w.lit) (!(litSign w.lit))

theorem evalVar_extendBveStepArray (w : BveWitness) (σ : Array Bool) :
    evalVar (extendBveStepArray w σ) = extendBveStep w (evalVar σ) := by
  unfold extendBveStepArray extendBveStep
  dsimp only
  have hcond :
      (w.clauses.all fun c => evalClause (setModelVar σ (litVar w.lit) (litSign w.lit)) c) =
      (w.clauses.all fun c =>
        clauseEvalVal (substUpdate (evalVar σ) (litVar w.lit) (litSign w.lit)) c) := by
    apply congrArg (List.all w.clauses)
    funext c
    rw [Bool.eq_iff_iff, evalClause_iff, clauseEvalVal_iff,
      clause_sat_cnfClause_iff, clause_sat_cnfClause_iff]
    simp only [evalVar_setModelVar]
  rw [hcond]
  split
  · funext x; exact evalVar_setModelVar σ (litVar w.lit) (litSign w.lit) x
  · funext x; exact evalVar_setModelVar σ (litVar w.lit) (!(litSign w.lit)) x

private theorem substUpdate_preserves_absent (α : Nat → Bool) (v : Nat) (b : Bool)
    {r0 : List Nat} (hm1 : mkLit v true ∉ r0) (hm2 : mkLit v false ∉ r0)
    (hsat : (cnfClause r0).Sat α) :
    (cnfClause r0).Sat (substUpdate α v b) := by
  refine (clause_sat_substUpdate_fresh b ?_).mpr hsat
  intro x hx hveq
  rcases (litVar_eq_iff_mkLit x v).mp hveq with rfl | rfl
  · exact hm1 hx
  · exact hm2 hx

private theorem extendBveCore_sound {w : BveWitness} {opp : List (List Nat)} {α : Nat → Bool}
    (hw_mem : ∀ c ∈ w.clauses, w.lit ∈ c ∧ litNeg w.lit ∉ c)
    (hopp_mem : ∀ d ∈ opp, litNeg w.lit ∈ d ∧ w.lit ∉ d)
    (hres : ∀ c ∈ w.clauses, ∀ d ∈ opp,
      clauseIsTaut (resolveOn w.lit c d) = false → (cnfClause (resolveOn w.lit c d)).Sat α) :
    (∀ c ∈ w.clauses, (cnfClause c).Sat (extendBveStep w α)) ∧
    (∀ d ∈ opp, (cnfClause d).Sat (extendBveStep w α)) := by
  let αFalse := substUpdate α (litVar w.lit) (litSign w.lit)
  let αTrue := substUpdate α (litVar w.lit) (!(litSign w.lit))
  unfold extendBveStep
  dsimp only
  by_cases hall : (w.clauses.all fun c => clauseEvalVal αFalse c) = true
  · simp only [show (w.clauses.all fun c => clauseEvalVal
        (substUpdate α (litVar w.lit) (litSign w.lit)) c) = true from hall, ↓reduceIte]
    constructor
    · intro c hc
      simp only [List.all_eq_true, clauseEvalVal_iff] at hall
      exact hall c hc
    · intro d hd
      exact (clause_sat_cnfClause_iff αFalse d).mpr
        ⟨litNeg w.lit, (hopp_mem d hd).1, by simp [αFalse]⟩
  · have hallf : (w.clauses.all fun c => clauseEvalVal
        (substUpdate α (litVar w.lit) (litSign w.lit)) c) = false :=
      Bool.eq_false_iff.mpr hall
    simp only [hallf, Bool.false_eq_true, ↓reduceIte]
    have hfa : ∃ c0 ∈ w.clauses, ¬ (cnfClause c0).Sat αFalse := by
      exact Classical.byContradiction fun hnone => by
        apply hall
        rw [List.all_eq_true]
        intro c hc
        rw [clauseEvalVal_iff]
        exact Classical.byContradiction fun hn => hnone ⟨c, hc, hn⟩
    obtain ⟨c0, hc0_mem, hc0_nsat⟩ := hfa
    have hc0_p := hw_mem c0 hc0_mem
    have hc0_rest_false_α : ∀ x ∈ c0, x ≠ w.lit → α (litVar x) ≠ !(litSign x) := by
      intro x hx hne hxs
      apply hc0_nsat
      have hvar_ne : litVar x ≠ litVar w.lit := by
        intro hv
        rcases (litVar_eq_iff x w.lit).mp hv with rfl | rfl
        · exact hne rfl
        · exact hc0_p.2 hx
      exact (clause_sat_cnfClause_iff αFalse c0).mpr
        ⟨x, hx, by simpa [αFalse, substUpdate_ne α _ hvar_ne] using hxs⟩
    have hc0_rest_false_αTrue : ∀ x ∈ c0, x ≠ w.lit → αTrue (litVar x) ≠ !(litSign x) := by
      intro x hx hne hxs
      have hvar_ne : litVar x ≠ litVar w.lit := by
        intro hv
        rcases (litVar_eq_iff x w.lit).mp hv with rfl | rfl
        · exact hne rfl
        · exact hc0_p.2 hx
      dsimp only [αTrue] at hxs
      rw [substUpdate_ne α _ hvar_ne] at hxs
      exact hc0_rest_false_α x hx hne hxs
    constructor
    · intro c hc
      exact (clause_sat_cnfClause_iff αTrue c).mpr
        ⟨w.lit, (hw_mem c hc).1, by simp [αTrue]⟩
    · intro d hd
      have hd_p := hopp_mem d hd
      cases htau : clauseIsTaut (resolveOn w.lit c0 d) with
      | false =>
        have hres_sat := hres c0 hc0_mem d hd htau
        obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp hres_sat
        simp only [resolveOn, List.mem_append, List.mem_filter, bne_iff_ne] at hy
        rcases hy with ⟨hyc0, hynw⟩ | ⟨hyd, hynneg⟩
        · exact absurd hys (hc0_rest_false_α y hyc0 hynw)
        · have hvar_ne : litVar y ≠ litVar w.lit := by
            intro hv
            rcases (litVar_eq_iff y w.lit).mp hv with rfl | rfl
            · exact hd_p.2 hyd
            · exact hynneg rfl
          exact (clause_sat_cnfClause_iff αTrue d).mpr
            ⟨y, hyd, by simpa [αTrue, substUpdate_ne α _ hvar_ne] using hys⟩
      | true =>
        obtain ⟨u, hu, hneg⟩ := (clauseIsTaut_iff _).mp htau
        simp only [resolveOn, List.mem_append, List.mem_filter, bne_iff_ne] at hu hneg
        rcases hu with ⟨huc0, hunw⟩ | ⟨hud, hunneg⟩
        · rcases hneg with ⟨hnc0, hnnw⟩ | ⟨hnd, hnnneg⟩
          · have hfalse : ¬ (cnfClause c0).Sat αFalse := hc0_nsat
            exfalso; apply hfalse
            by_cases hsat_u : αFalse (litVar u) = !(litSign u)
            · exact (clause_sat_cnfClause_iff αFalse c0).mpr ⟨u, huc0, hsat_u⟩
            · have hns := (sat_cnfClause_litNeg_iff αFalse u).mpr
                (by simpa [sat_cnfClause_singleton] using hsat_u)
              exact (clause_sat_cnfClause_iff αFalse c0).mpr
                ⟨litNeg u, hnc0, (sat_cnfClause_singleton αFalse _).mp hns⟩
          · have huf : αTrue (litVar u) ≠ !(litSign u) := hc0_rest_false_αTrue u huc0 hunw
            have hns := (sat_cnfClause_litNeg_iff αTrue u).mpr
              (by simpa [sat_cnfClause_singleton] using huf)
            exact (clause_sat_cnfClause_iff αTrue d).mpr
              ⟨litNeg u, hnd, (sat_cnfClause_singleton αTrue _).mp hns⟩
        · rcases hneg with ⟨hnc0, hnnw⟩ | ⟨hnd, hnnneg⟩
          · have hnf : αTrue (litVar (litNeg u)) ≠ !(litSign (litNeg u)) :=
              hc0_rest_false_αTrue (litNeg u) hnc0 hnnw
            have hus : (cnfClause [u]).Sat αTrue := Classical.byContradiction fun hnu =>
              hnf ((sat_cnfClause_singleton αTrue (litNeg u)).mp
                ((sat_cnfClause_litNeg_iff αTrue u).mpr hnu))
            exact (clause_sat_cnfClause_iff αTrue d).mpr
              ⟨u, hud, (sat_cnfClause_singleton αTrue u).mp hus⟩
          · by_cases hsat_u : αTrue (litVar u) = !(litSign u)
            · exact (clause_sat_cnfClause_iff αTrue d).mpr ⟨u, hud, hsat_u⟩
            · have hns := (sat_cnfClause_litNeg_iff αTrue u).mpr
                (by simpa [sat_cnfClause_singleton] using hsat_u)
              exact (clause_sat_cnfClause_iff αTrue d).mpr
                ⟨litNeg u, hnd, (sat_cnfClause_singleton αTrue _).mp hns⟩

/-- **Single-step SAT witness reconstruction (`List (List Nat)`)**: extending any model `α` of
`bveClauses cs v` with `extendBveStep (mkBveWitness v p n) α` yields a model of `cs`. -/
theorem extendBveStep_sound {α : Nat → Bool} {cs : List (List Nat)} {v : Nat}
    (h : (cnfOfClauses (bveClauses cs v)).Sat α) :
    let (p, n, _) := bvePartition cs v
    (cnfOfClauses cs).Sat (extendBveStep (mkBveWitness v p n) α) := by
  have hp := bvePartition_props cs v
  dsimp only at hp ⊢
  obtain ⟨hpp, hpn, hpr, hall⟩ := hp
  have hres_mem : ∀ c ∈ (bvePartition cs v).1, ∀ d ∈ (bvePartition cs v).2.1,
      clauseIsTaut (resolveOn (mkLit v true) c d) = false →
      (cnfClause (resolveOn (mkLit v true) c d)).Sat α := by
    intro c hc d hd hnt
    exact (cnf_sat_cnfOfClauses_iff α _).mp h (resolveOn (mkLit v true) c d)
      (List.mem_append_left _ ((mem_bveResolvents_iff _ _ _ _).mpr ⟨⟨c, hc, d, hd, rfl⟩, hnt⟩))
  have hlit_var : ∀ w : BveWitness,
      w = mkBveWitness v (bvePartition cs v).1 (bvePartition cs v).2.1 →
      litVar w.lit = v := by
    intro w hw; subst hw; unfold mkBveWitness; split <;> simp
  have hr_sat : ∀ r0 ∈ (bvePartition cs v).2.2,
      (cnfClause r0).Sat (extendBveStep (mkBveWitness v (bvePartition cs v).1
        (bvePartition cs v).2.1) α) := by
    intro r0 hr0
    have hα_r0 := (cnf_sat_cnfOfClauses_iff α _).mp h r0 (List.mem_append_right _ hr0)
    have hr_p := hpr r0 hr0
    unfold extendBveStep
    dsimp only
    rw [hlit_var _ rfl]
    split
    · exact substUpdate_preserves_absent α _ _ hr_p.2.1 hr_p.2.2 hα_r0
    · exact substUpdate_preserves_absent α _ _ hr_p.2.1 hr_p.2.2 hα_r0
  have hpn_sat : (∀ c ∈ (bvePartition cs v).1,
        (cnfClause c).Sat (extendBveStep (mkBveWitness v (bvePartition cs v).1
          (bvePartition cs v).2.1) α)) ∧
      (∀ d ∈ (bvePartition cs v).2.1,
        (cnfClause d).Sat (extendBveStep (mkBveWitness v (bvePartition cs v).1
          (bvePartition cs v).2.1) α)) := by
    unfold mkBveWitness
    by_cases hle : (bvePartition cs v).1.length ≤ (bvePartition cs v).2.1.length
    · simp only [hle, ↓reduceIte]
      exact extendBveCore_sound
        (w := { lit := mkLit v true, clauses := (bvePartition cs v).1 })
        (opp := (bvePartition cs v).2.1)
        (fun c hc => ⟨(hpp c hc).2.1, by simpa [litNeg_mkLit] using (hpp c hc).2.2⟩)
        (fun d hd => ⟨by simpa [litNeg_mkLit] using (hpn d hd).2.1, (hpn d hd).2.2⟩)
        hres_mem
    · simp only [hle, ↓reduceIte]
      have hcore := extendBveCore_sound
        (w := { lit := mkLit v false, clauses := (bvePartition cs v).2.1 })
        (opp := (bvePartition cs v).1)
        (fun d hd => ⟨(hpn d hd).2.1, by simpa [litNeg_mkLit] using (hpn d hd).2.2⟩)
        (fun c hc => ⟨by simpa [litNeg_mkLit] using (hpp c hc).2.1, (hpp c hc).2.2⟩)
        fun d hd c hc hnt => by
          have hmem : ∀ x, x ∈ resolveOn (mkLit v false) d c ↔
              x ∈ resolveOn (mkLit v true) c d := fun x => by
            simpa [litNeg_mkLit] using resolveOn_comm_mem (mkLit v true) c d x
          rw [sat_cnfClause_congr hmem]
          apply hres_mem c hc d hd
          rw [← clauseIsTaut_congr hmem]
          exact hnt
      exact ⟨hcore.2, hcore.1⟩
  rw [cnf_sat_cnfOfClauses_iff]
  intro cl hcl
  rcases hall cl hcl with ⟨hp_cl, hn_cl⟩ | hc_p | hc_n | hc_r
  · by_cases hsat_pos : (cnfClause [mkLit v true]).Sat
        (extendBveStep (mkBveWitness v (bvePartition cs v).1 (bvePartition cs v).2.1) α)
    · exact (clause_sat_cnfClause_iff _ cl).mpr
        ⟨mkLit v true, hp_cl, (sat_cnfClause_singleton _ _).mp hsat_pos⟩
    · have hns := (sat_cnfClause_litNeg_iff _ _).mpr hsat_pos
      rw [litNeg_mkLit] at hns
      exact (clause_sat_cnfClause_iff _ cl).mpr
        ⟨mkLit v false, hn_cl, (sat_cnfClause_singleton _ _).mp hns⟩
  · exact hpn_sat.1 cl hc_p
  · exact hpn_sat.2 cl hc_n
  · exact hr_sat cl hc_r

/-- **Single-step SAT witness reconstruction (`CNF Nat`)**: extending any model `α` of `bve cnf v`
yields a model of `cnf`. -/
theorem extendBveStep_sat {α : Nat → Bool} {cnf : CNF Nat} {v : Nat}
    (h : (bve cnf v).Sat α) :
    let (p, n, _) := bvePartition (clausesOfCnf cnf) v
    cnf.Sat (extendBveStep (mkBveWitness v p n) α) := by
  have hs := extendBveStep_sound h
  dsimp only at hs ⊢
  simpa using hs

/-- **Executable Array single-step witness reconstruction**: extends a verified `Array Bool` model
of `bve cnf v` to a verified `Array Bool` model of `cnf`. -/
theorem extendBveStepArr_sound {σ : Array Bool} {cnf : CNF Nat} {v : Nat}
    (h : checkModel (bve cnf v) σ = true) :
    let (p, n, _) := bvePartition (clausesOfCnf cnf) v
    checkModel cnf (extendBveStepArray (mkBveWitness v p n) σ) = true := by
  dsimp only
  rw [checkModel_iff_sat, evalVar_extendBveStepArray]
  exact extendBveStep_sat ((checkModel_iff_sat _ σ).mp h)

/-! ## 5. Iterated BVE and LIFO reconstruction stack -/


/-- LIFO stack of elimination witness entries (`kissat_extend`). -/
abbrev BveStack := List BveWitness

/-- Single elimination step returning `(bveClauses cs v, witness)`. -/
@[expose] def bveStep (cs : List (List Nat)) (v : Nat) : List (List Nat) × BveWitness :=
  let (p, n, r) := bvePartition cs v
  (bveResolvents (mkLit v true) p n ++ r, mkBveWitness v p n)

theorem bveStep_fst (cs : List (List Nat)) (v : Nat) :
    (bveStep cs v).1 = bveClauses cs v := rfl

/-- Auxiliary fold eliminating `pivots` in order while pushing witness entries onto `stack`. -/
@[expose] def bveElimAux : List Nat → List (List Nat) → BveStack → List (List Nat) × BveStack
  | [], cs, st => (cs, st)
  | v :: vs, cs, st =>
    let res := bveStep cs v
    bveElimAux vs res.1 (res.2 :: st)

/-- Eliminate a list of pivot variables `pivots`, returning `(reducedClauses, witnessStack)`. -/
@[expose] def bveElim (cs : List (List Nat)) (pivots : List Nat) : List (List Nat) × BveStack :=
  bveElimAux pivots cs []

/-- Eliminates `pivots` from `cnf : CNF Nat`, returning `(reducedCnf, witnessStack)`. -/
@[expose] def bveElimCnf (cnf : CNF Nat) (pivots : List Nat) : CNF Nat × BveStack :=
  let res := bveElim (clausesOfCnf cnf) pivots
  (cnfOfClauses res.1, res.2)

/-- Cost-bounded single step: eliminates `v` only if resolvent count does not exceed
`p.length + n.length + bound`. -/
@[expose] def bveBoundedStep (bound : Nat) (cs : List (List Nat)) (v : Nat) :
    List (List Nat) × Option BveWitness :=
  let (p, n, r) := bvePartition cs v
  let res := bveResolvents (mkLit v true) p n
  if res.length ≤ p.length + n.length + bound then (res ++ r, some (mkBveWitness v p n))
  else (cs, none)

@[expose] def bveBoundedElimAux (bound : Nat) :
    List Nat → List (List Nat) → BveStack → List (List Nat) × BveStack
  | [], cs, st => (cs, st)
  | v :: vs, cs, st =>
    match bveBoundedStep bound cs v with
    | (cs', some w) => bveBoundedElimAux bound vs cs' (w :: st)
    | (cs', none) => bveBoundedElimAux bound vs cs' st

/-- Cost-bounded iterated BVE pass over candidate variables `pivots`. -/
@[expose] def bveBoundedElim (bound : Nat) (cs : List (List Nat)) (pivots : List Nat) :
    List (List Nat) × BveStack :=
  bveBoundedElimAux bound pivots cs []

/-- LIFO SAT witness reconstruction on `α : Nat → Bool` (`kissat_extend`). -/
@[expose] def extendBve (stack : BveStack) (α : Nat → Bool) : Nat → Bool :=
  stack.foldl (fun acc w => extendBveStep w acc) α

/-- LIFO SAT witness reconstruction on executable `Array Bool` models. -/
@[expose] def extendBveArray (stack : BveStack) (σ : Array Bool) : Array Bool :=
  stack.foldl (fun acc w => extendBveStepArray w acc) σ

@[simp] theorem extendBve_nil (α : Nat → Bool) : extendBve [] α = α := rfl

@[simp] theorem extendBve_cons (w : BveWitness) (st : BveStack) (α : Nat → Bool) :
    extendBve (w :: st) α = extendBve st (extendBveStep w α) := rfl

theorem evalVar_extendBveArray (stack : BveStack) (σ : Array Bool) :
    evalVar (extendBveArray stack σ) = extendBve stack (evalVar σ) := by
  unfold extendBveArray extendBve
  induction stack generalizing σ with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons, ih, evalVar_extendBveStepArray]

/-! ## 2. Compositional UNSAT soundness and SAT witness reconstruction -/

private theorem bveElimAux_sat_of_sat :
    ∀ (pivots : List Nat) (cs : List (List Nat)) (st : BveStack) (α : Nat → Bool),
      (cnfOfClauses cs).Sat α → (cnfOfClauses (bveElimAux pivots cs st).1).Sat α
  | [], _, _, _, h => h
  | v :: vs, cs, st, α, h => by
    unfold bveElimAux
    exact bveElimAux_sat_of_sat vs (bveStep cs v).1 _ α
      (by simpa [bveStep_fst] using bveClauses_sat_of_sat (v := v) h)

/-- Forward satisfaction under `bveElim`. -/
theorem bveElim_sat_of_sat {α : Nat → Bool} {cs : List (List Nat)} {pivots : List Nat}
    (h : (cnfOfClauses cs).Sat α) :
    (cnfOfClauses (bveElim cs pivots).1).Sat α :=
  bveElimAux_sat_of_sat pivots cs [] α h

/-- **Iterated BVE UNSAT soundness (`List (List Nat)`)**:
`(cnfOfClauses (bveElim cs pivots).1).Unsat → (cnfOfClauses cs).Unsat`. -/
theorem bveElim_unsat_sound {cs : List (List Nat)} {pivots : List Nat}
    (hu : (cnfOfClauses (bveElim cs pivots).1).Unsat) : (cnfOfClauses cs).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα; exact hu α (bveElim_sat_of_sat hα)

/-- **Iterated BVE UNSAT soundness (`CNF Nat`)**:
`(bveElimCnf cnf pivots).1.Unsat → cnf.Unsat`. -/
theorem bveElimCnf_unsat_sound {cnf : CNF Nat} {pivots : List Nat}
    (hu : (bveElimCnf cnf pivots).1.Unsat) : cnf.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu α (bveElim_sat_of_sat (by simpa using hα))

private theorem bveElimAux_extend_rel (csOrig : List (List Nat)) :
    ∀ (pivots : List Nat) (cs : List (List Nat)) (st : BveStack),
      (∀ α : Nat → Bool, (cnfOfClauses cs).Sat α → (cnfOfClauses csOrig).Sat (extendBve st α)) →
      ∀ α : Nat → Bool, (cnfOfClauses (bveElimAux pivots cs st).1).Sat α →
        (cnfOfClauses csOrig).Sat (extendBve (bveElimAux pivots cs st).2 α)
  | [], _, _, hrel, _, hsat => hrel _ hsat
  | v :: vs, cs, st, hrel, α, hsat => by
    unfold bveElimAux at hsat ⊢
    refine bveElimAux_extend_rel csOrig vs (bveStep cs v).1 ((bveStep cs v).2 :: st) ?_ α hsat
    intro β hβ
    have hstep : (cnfOfClauses cs).Sat (extendBveStep (bveStep cs v).2 β) := by
      have hs := extendBveStep_sound (cs := cs) (v := v) (by simpa [bveStep_fst] using hβ)
      simpa [bveStep] using hs
    simpa [extendBve_cons] using hrel _ hstep

/-- **Iterated SAT witness reconstruction (`List (List Nat)`)**: `extendBve` converts any model
of `(bveElim cs pivots).1` into a model of `cs`. -/
theorem extendBve_sound {cs : List (List Nat)} {pivots : List Nat} {α : Nat → Bool}
    (h : (cnfOfClauses (bveElim cs pivots).1).Sat α) :
    (cnfOfClauses cs).Sat (extendBve (bveElim cs pivots).2 α) :=
  bveElimAux_extend_rel cs pivots cs [] (fun _ h0 => h0) α h

/-- **Iterated SAT witness reconstruction (`CNF Nat`)**: `extendBve` converts any model of
`(bveElimCnf cnf pivots).1` into a model of `cnf`. -/
theorem extendBve_cnf_sound {cnf : CNF Nat} {pivots : List Nat} {α : Nat → Bool}
    (h : (bveElimCnf cnf pivots).1.Sat α) :
    cnf.Sat (extendBve (bveElimCnf cnf pivots).2 α) := by
  have hs := extendBve_sound h
  rw [cnfOfClauses_clausesOfCnf] at hs
  exact hs

/-- **Executable Array iterated witness reconstruction (`evalCnf`)**. -/
theorem extendBveArray_sound {cs : List (List Nat)} {pivots : List Nat} {σ : Array Bool}
    (h : evalCnf σ (bveElim cs pivots).1 = true) :
    evalCnf (extendBveArray (bveElim cs pivots).2 σ) cs = true := by
  rw [evalCnf_iff, evalVar_extendBveArray]
  exact extendBve_sound ((evalCnf_iff σ _).mp h)

/-- **Executable Array iterated witness reconstruction (`checkModel` on `CNF Nat`)**. -/
theorem extendBveArray_cnf {cnf : CNF Nat} {pivots : List Nat} {σ : Array Bool}
    (h : checkModel (bveElimCnf cnf pivots).1 σ = true) :
    checkModel cnf (extendBveArray (bveElimCnf cnf pivots).2 σ) = true := by
  rw [checkModel_iff_sat, evalVar_extendBveArray]
  exact extendBve_cnf_sound ((checkModel_iff_sat _ σ).mp h)

/-- **Iterated BVE equisatisfiability**: preserves both `Unsat` (`↔`) and satisfiability
(`(∃ α, Sat α) ↔`). -/
theorem bveElim_equisat (cs : List (List Nat)) (pivots : List Nat) :
    ((cnfOfClauses (bveElim cs pivots).1).Unsat ↔ (cnfOfClauses cs).Unsat) ∧
    ((∃ α : Nat → Bool, (cnfOfClauses (bveElim cs pivots).1).Sat α) ↔
      (∃ α : Nat → Bool, (cnfOfClauses cs).Sat α)) :=
  ⟨⟨bveElim_unsat_sound, fun hu => by
      rw [CNF.unsat_iff_not_sat] at hu ⊢
      intro α hα; exact hu _ (extendBve_sound hα)⟩,
   ⟨fun ⟨α, hα⟩ => ⟨extendBve (bveElim cs pivots).2 α, extendBve_sound hα⟩,
    fun ⟨α, hα⟩ => ⟨α, bveElim_sat_of_sat hα⟩⟩⟩

private theorem bveBoundedElimAux_sound (bound : Nat) (csOrig : List (List Nat)) :
    ∀ (pivots : List Nat) (cs : List (List Nat)) (st : BveStack),
      (∀ α, (cnfOfClauses csOrig).Sat α → (cnfOfClauses cs).Sat α) →
      (∀ α, (cnfOfClauses cs).Sat α → (cnfOfClauses csOrig).Sat (extendBve st α)) →
      let res := bveBoundedElimAux bound pivots cs st
      (∀ α, (cnfOfClauses csOrig).Sat α → (cnfOfClauses res.1).Sat α) ∧
      (∀ α, (cnfOfClauses res.1).Sat α → (cnfOfClauses csOrig).Sat (extendBve res.2 α))
  | [], cs, st, hfwd, hrev => ⟨hfwd, hrev⟩
  | v :: vs, cs, st, hfwd, hrev => by
    unfold bveBoundedElimAux bveBoundedStep
    dsimp only
    by_cases hlen : (bveResolvents (mkLit v true) (bvePartition cs v).1
        (bvePartition cs v).2.1).length ≤
        (bvePartition cs v).1.length + (bvePartition cs v).2.1.length + bound
    · simp only [hlen, ↓reduceIte]
      apply bveBoundedElimAux_sound bound csOrig vs _ _
      · intro α hα; exact bveClauses_sat_of_sat (hfwd α hα)
      · intro α hα
        rw [extendBve_cons]
        exact hrev _ (extendBveStep_sound (cs := cs) (v := v) hα)
    · simp only [hlen, ↓reduceIte]
      exact bveBoundedElimAux_sound bound csOrig vs cs st hfwd hrev

/-- **Cost-bounded iterated BVE equisatisfiability & reconstruction**. -/
theorem bveBounded_sound (bound : Nat) (cs : List (List Nat)) (pivots : List Nat) :
    let res := bveBoundedElim bound cs pivots
    ((cnfOfClauses res.1).Unsat → (cnfOfClauses cs).Unsat) ∧
    (∀ α : Nat → Bool, (cnfOfClauses res.1).Sat α →
      (cnfOfClauses cs).Sat (extendBve res.2 α)) ∧
    (∀ σ : Array Bool, evalCnf σ res.1 = true →
      evalCnf (extendBveArray res.2 σ) cs = true) := by
  have h := bveBoundedElimAux_sound bound cs pivots cs [] (fun _ h0 => h0) (fun _ h0 => h0)
  refine ⟨fun hu => ?_, h.2, fun σ hσ => ?_⟩
  · rw [CNF.unsat_iff_not_sat] at hu ⊢
    intro α hα; exact hu α (h.1 α hα)
  · rw [evalCnf_iff, evalVar_extendBveArray]
    exact h.2 (evalVar σ) ((evalCnf_iff σ _).mp hσ)

/-! ## 3. Integration with `cdclSolve` -/

/-- **End-to-end BVE + CDCL solver soundness**: running `cdclSolve fuel (bveElimCnf cnf pivots).1`
certifies `cnf.Unsat` on `.unsat` and produces a verified extended `Array Bool` model
`extendBveArray stack σ` satisfying `checkModel cnf _ = true` and `cnf.Sat` on `.sat σ`. -/
theorem cdclSolveAfterBve_sound (fuel : Nat) (cnf : CNF Nat) (pivots : List Nat) :
    let (cnf', stack) := bveElimCnf cnf pivots
    match cdclSolve fuel cnf' with
    | .unsat => cnf.Unsat
    | .sat σ =>
      let σFull := extendBveArray stack σ
      checkModel cnf σFull = true ∧ ¬ cnf.Unsat ∧ cnf.Sat (evalVar σFull)
    | .unknown => True := by
  dsimp only
  cases h : cdclSolve fuel (bveElimCnf cnf pivots).1 with
  | unknown => trivial
  | unsat => exact bveElimCnf_unsat_sound (cdclSolve_unsat_sound h)
  | sat σ =>
    have hchk : checkModel cnf (extendBveArray (bveElimCnf cnf pivots).2 σ) = true :=
      extendBveArray_cnf (cdclSolve_sat_model h)
    have hs := checkModel_sound hchk
    exact ⟨hchk, hs.1, (checkModel_iff_sat cnf _).mp hchk⟩

end LeanQbe.T.Examples.Kissat.Ref
