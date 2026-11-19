module

public import LeanQbe.T.Examples.Kissat.LayerABve1

/-!
# Pure Lean Layer-A Inprocessing Theory: Iterated BVE & Model Reconstruction

Pure Lean formalization (zero `Kraken.Mem` or `Kraken.Separation` imports) of multi-pivot
bounded variable elimination (`bveElim`, `bveElimCnf`, `bveBoundedElim`) and iterated LIFO
SAT witness reconstruction (`extendBve`, `extendBveArray`) modeling `kissat_extend`, plus
end-to-end integration with `cdclSolve`:

1. **Iterated elimination & LIFO witness stack**: `BveStack`, `bveStep`, `bveElim`,
   `bveElimCnf`, `bveBoundedElim`, `extendBve`, `extendBveArray`.
2. **Compositional UNSAT & SAT reconstruction theorems**:
   - `bveElim_unsat_sound` & `bveElimCnf_unsat_sound`: refutation of the reduced formula
     certifies unsatisfiability of the original formula.
   - `extendBve_sound`, `extendBve_cnf_sound`, `extendBveArray_sound`, `extendBveArray_cnf`:
     iterated witness extension converts any satisfying assignment / `Array Bool` model of the
     reduced formula into a verified model of the original formula.
   - `bveElim_equisat`: full equisatisfiability (`Unsat ↔` and `(∃ α, Sat α) ↔`).
3. **Solver integration (`cdclSolveAfterBve_sound`)**: solving `bveElimCnf cnf pivots` via
   `cdclSolve` certifies either `cnf.Unsat` or a concrete verified model array
   `extendBveArray stack σ` satisfying `checkModel cnf _ = true`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std.Sat

/-! ## 1. Iterated BVE and LIFO reconstruction stack -/

/-- LIFO stack of elimination witness entries (`kissat_extend`). -/
abbrev BveStack := List BveWitness

/-- Single elimination step returning `(bveClauses cs v, witness)`. -/
def bveStep (cs : List (List Nat)) (v : Nat) : List (List Nat) × BveWitness :=
  let (p, n, r) := bvePartition cs v
  (bveResolvents (mkLit v true) p n ++ r, mkBveWitness v p n)

theorem bveStep_fst (cs : List (List Nat)) (v : Nat) :
    (bveStep cs v).1 = bveClauses cs v := rfl

/-- Auxiliary fold eliminating `pivots` in order while pushing witness entries onto `stack`. -/
def bveElimAux : List Nat → List (List Nat) → BveStack → List (List Nat) × BveStack
  | [], cs, st => (cs, st)
  | v :: vs, cs, st =>
    let res := bveStep cs v
    bveElimAux vs res.1 (res.2 :: st)

/-- Eliminate a list of pivot variables `pivots`, returning `(reducedClauses, witnessStack)`. -/
def bveElim (cs : List (List Nat)) (pivots : List Nat) : List (List Nat) × BveStack :=
  bveElimAux pivots cs []

/-- Eliminates `pivots` from `cnf : CNF Nat`, returning `(reducedCnf, witnessStack)`. -/
def bveElimCnf (cnf : CNF Nat) (pivots : List Nat) : CNF Nat × BveStack :=
  let res := bveElim (clausesOfCnf cnf) pivots
  (cnfOfClauses res.1, res.2)

/-- Cost-bounded single step: eliminates `v` only if resolvent count does not exceed
`p.length + n.length + bound`. -/
def bveBoundedStep (bound : Nat) (cs : List (List Nat)) (v : Nat) :
    List (List Nat) × Option BveWitness :=
  let (p, n, r) := bvePartition cs v
  let res := bveResolvents (mkLit v true) p n
  if res.length ≤ p.length + n.length + bound then (res ++ r, some (mkBveWitness v p n))
  else (cs, none)

def bveBoundedElimAux (bound : Nat) :
    List Nat → List (List Nat) → BveStack → List (List Nat) × BveStack
  | [], cs, st => (cs, st)
  | v :: vs, cs, st =>
    match bveBoundedStep bound cs v with
    | (cs', some w) => bveBoundedElimAux bound vs cs' (w :: st)
    | (cs', none) => bveBoundedElimAux bound vs cs' st

/-- Cost-bounded iterated BVE pass over candidate variables `pivots`. -/
def bveBoundedElim (bound : Nat) (cs : List (List Nat)) (pivots : List Nat) :
    List (List Nat) × BveStack :=
  bveBoundedElimAux bound pivots cs []

/-- LIFO SAT witness reconstruction on `α : Nat → Bool` (`kissat_extend`). -/
def extendBve (stack : BveStack) (α : Nat → Bool) : Nat → Bool :=
  stack.foldl (fun acc w => extendBveStep w acc) α

/-- LIFO SAT witness reconstruction on executable `Array Bool` models. -/
def extendBveArray (stack : BveStack) (σ : Array Bool) : Array Bool :=
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

private theorem cdclLoop_sat_model {fuel : Nat} {s : CdclState} (hinv : TrailInv s) :
    match cdclLoop fuel s with
    | .sat σ => checkModel s.f0 σ = true
    | _ => True := by
  induction fuel generalizing s with
  | zero => simp [cdclLoop]
  | succ fuel ih =>
    simp only [cdclLoop]
    by_cases hinc : s.inconsistent = true
    · simp [hinc]
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
        · simp [hl0]
        · have hl0f : (s1.level == 0) = false := beq_false_of_ne hl0
          simp only [hl0f, Bool.false_eq_true, ↓reduceIte]
          by_cases he : (minimizeClause s1 (analyze1UIP s1 confl)).isEmpty = true
          · simp [he]
          · have hef : (minimizeClause s1 (analyze1UIP s1 confl)).isEmpty = false :=
              Bool.eq_false_iff.mpr he
            simp only [hef, Bool.false_eq_true, ↓reduceIte]
            have h1uip := analyze1UIP_sound hinv1 hconfl1 hfals1
            have hmin := minimizeCut_sound hinv1 h1uip.1
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
          · simp only [hchk, ↓reduceIte]; rwa [← hf01]
          · have hchkf : checkModel s1.f0 (modelFromTrail s1.numVars s1.trail) = false :=
              Bool.eq_false_iff.mpr hchk
            simp [hchkf]

theorem cdclSolve_sat_model {fuel : Nat} {cnf : CNF Nat} {σ : Array Bool}
    (h : cdclSolve fuel cnf = .sat σ) : checkModel cnf σ = true := by
  have hm := cdclLoop_sat_model (fuel := fuel) (initState_inv cnf).1
  unfold cdclSolve at h; rw [h, (initState_inv cnf).2] at hm; exact hm

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

end LeanQbe.T.Examples.Kissat
