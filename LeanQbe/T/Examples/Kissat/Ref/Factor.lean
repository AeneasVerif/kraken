/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Gates

/-!
# Pure Lean Layer-A Soundness Theory for BCA, BVA / Factorization & Tier-B Traces

Builds on `Kissat.Ref.Gates` (`factor.c`):

1. **Blocked Clause Addition (`BCA`) & Bounded Variable Addition / Factorization (`factor.c`)**:
   proves general and fresh-variable BCA (`bca_unsat_sound`, `fresh_bca_batch_unsat`) and
   Kissat's fresh-variable divider/quotient factorization (`bvaFactor_unsat_sound`,
   `bvaFactor_sat_recon`, `bvaFactor_equisat`).
2. **Unified Tier-B Pipeline (`TierBStep`, `TierBTrace`)**:
   composes `Subst`, `BCE`, `Gate-BVE`, and `BVA/Factor` into a single witness-reconstructing
   trace (`tierBTrace_unsat`, `tierBTrace_sat_recon`, `tierBTrace_equisat`) with an executable
   `Array Bool` reconstruction bridge (`tierBTraceExtendArr_sound`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 3. Blocked Clause Addition (`BCA`) and Bounded Variable Addition (`factor.c`) -/

/-- Forward satisfiability preservation of Blocked Clause Addition (`BCA`). -/
theorem bca_sat_fwd {cs : List (List Nat)} {c : List Nat} {l : Nat} {α : Nat → Bool}
    (hblk : IsBlockedOn cs c l) (hsat : (cnfOfClauses cs).Sat α) :
    (cnfOfClauses (c :: cs)).Sat (extendBce l c α) :=
  bce_extend_sat hblk hsat

/-- UNSAT soundness of Blocked Clause Addition (`(c :: cs).Unsat → cs.Unsat`). -/
theorem bca_unsat_sound {cs : List (List Nat)} {c : List Nat} {l : Nat}
    (hblk : IsBlockedOn cs c l) (hu : (cnfOfClauses (c :: cs)).Unsat) :
    (cnfOfClauses cs).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu (extendBce l c α) (bce_extend_sat hblk hα)

/-- SAT model reconstruction for Blocked Clause Addition (`α ⊨ c :: cs → α ⊨ cs`). -/
theorem bca_sat_recon {cs : List (List Nat)} {c : List Nat} {α : Nat → Bool}
    (hsat : (cnfOfClauses (c :: cs)).Sat α) :
    (cnfOfClauses cs).Sat α := by
  rw [cnf_sat_cnfOfClauses_iff] at hsat ⊢
  intro d hd; exact hsat d (List.mem_cons_of_mem c hd)

/-- Equisatisfiability of Blocked Clause Addition. -/
theorem bca_equisat {cs : List (List Nat)} {c : List Nat} {l : Nat}
    (hblk : IsBlockedOn cs c l) :
    (∃ α, (cnfOfClauses cs).Sat α) ↔ (∃ α, (cnfOfClauses (c :: cs)).Sat α) :=
  ⟨fun ⟨α, hα⟩ => ⟨extendBce l c α, bca_sat_fwd hblk hα⟩,
    fun ⟨α, hα⟩ => ⟨α, bca_sat_recon hα⟩⟩

/-- Any clause containing a literal `l` on a variable fresh in `cs` is blocked on `l`. -/
theorem isBlockedOn_of_fresh_var {cs : List (List Nat)} {c : List Nat} {l : Nat}
    (hfresh : VarFreshIn cs (litVar l)) (hl : l ∈ c) : IsBlockedOn cs c l := by
  refine ⟨hl, fun d hd hnl => ?_⟩
  exact absurd (litVar_litNeg l) (hfresh d hd (litNeg l) hnl)

/-- Batch fresh-variable Blocked Clause Addition: adding any set of clauses `newCs` all
containing `mkLit z pol` for fresh `z ∉ vars cs` preserves `Unsat` and reconstructs models. -/
theorem fresh_bca_batch_unsat {cs newCs : List (List Nat)} {z : Nat} {pol : Bool}
    (hfresh : VarFreshIn cs z) (hpol : ∀ c ∈ newCs, mkLit z pol ∈ c)
    (hu : (cnfOfClauses (newCs ++ cs)).Unsat) :
    (cnfOfClauses cs).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  refine hu (substUpdate α z pol) ?_
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  intro c hc
  rcases List.mem_append.mp hc with hnew | hold
  · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
    exact ⟨mkLit z pol, hpol c hnew, by simp⟩
  · exact (clause_sat_substUpdate_fresh pol (hfresh c hold)).mpr (hα c hold)

/-- Kissat `factor.c` divider clauses `[z, fᵢ]` for each factor literal `fᵢ ∈ L`. -/
@[expose] def bvaDivClauses (z : Nat) (L : List Nat) : List (List Nat) :=
  L.map fun f => [mkLit z true, f]

/-- Kissat `factor.c` quotient clauses `[¬z] ++ qⱼ` for each quotient subclause `qⱼ ∈ Q`. -/
@[expose] def bvaQuotClauses (z : Nat) (Q : List (List Nat)) : List (List Nat) :=
  Q.map fun q => mkLit z false :: q

/-- Order-independent membership test: `true` iff `c` is subsumed by some product clause
`f :: q` with `f ∈ L` and `q ∈ Q`. -/
@[expose] def bvaIsFactored (L : List Nat) (Q : List (List Nat)) (c : List Nat) : Bool :=
  L.any fun f => c.contains f && Q.any fun q => q.all fun x => c.contains x

/-- Kissat `factor.c` Bounded Variable Addition / Factorization transform: introduces fresh `z`,
adds divider clauses `{[z, f] | f ∈ L}` and quotient clauses `{¬z :: q | q ∈ Q}`, and deletes
every clause subsumed by a factored product clause `f :: q`. -/
@[expose] def bvaFactorClauses (z : Nat) (L : List Nat) (Q : List (List Nat))
    (cs : List (List Nat)) : List (List Nat) :=
  bvaDivClauses z L ++ bvaQuotClauses z Q ++ cs.filter (fun c => !bvaIsFactored L Q c)

/-- Forward witness assignment for fresh variable `z` introduced by `bvaFactorClauses`:
`z := false` if every divider literal `f ∈ L` is already true under `α`, else `z := true`. -/
@[expose] def bvaExtend (z : Nat) (L : List Nat) (α : Nat → Bool) : Nat → Bool :=
  substUpdate α z (!(L.all (evalLitVal α)))

/-- Validity side-condition for Bounded Variable Addition / Factorization (`factor.c`). -/
@[expose]
def BvaValid (z : Nat) (L : List Nat) (Q : List (List Nat)) (cs : List (List Nat)) : Prop :=
  VarFreshIn cs z ∧
  (∀ f ∈ L, litVar f ≠ z) ∧
  (∀ q ∈ Q, ∀ x ∈ q, litVar x ≠ z) ∧
  (∀ f ∈ L, ∀ q ∈ Q, (cnfOfClauses cs).EntailsClause (cnfClause (f :: q)))

/-- Convenience constructor for `BvaValid` when every product clause `f :: q` appears in `cs`. -/
theorem bvaValid_of_mem {z : Nat} {L : List Nat} {Q : List (List Nat)} {cs : List (List Nat)}
    (hfresh : VarFreshIn cs z)
    (hL : L ≠ []) (hQ : Q ≠ [])
    (hprod : ∀ f ∈ L, ∀ q ∈ Q, (f :: q) ∈ cs) :
    BvaValid z L Q cs := by
  obtain ⟨f0, hf0⟩ := List.exists_mem_of_ne_nil L hL
  obtain ⟨q0, hq0⟩ := List.exists_mem_of_ne_nil Q hQ
  refine ⟨hfresh, ?_, ?_, ?_⟩
  · intro f hf
    exact hfresh (f :: q0) (hprod f hf q0 hq0) f (List.mem_cons_self ..)
  · intro q hq x hx
    exact hfresh (f0 :: q) (hprod f0 hf0 q hq) x (List.mem_cons_of_mem f0 hx)
  · intro f hf q hq
    exact entails_mem_clausesOfCnf (by simpa using hprod f hf q hq)

/-- Forward satisfiability preservation of Kissat Bounded Factorization (`factor.c`). -/
theorem bvaFactor_sat_fwd {z : Nat} {L : List Nat} {Q : List (List Nat)} {cs : List (List Nat)}
    {α : Nat → Bool} (hval : BvaValid z L Q cs) (hα : (cnfOfClauses cs).Sat α) :
    (cnfOfClauses (bvaFactorClauses z L Q cs)).Sat (bvaExtend z L α) := by
  obtain ⟨hfresh, hfL, hfQ, hent⟩ := hval
  rw [cnf_sat_cnfOfClauses_iff]
  intro c hc
  unfold bvaFactorClauses at hc
  simp only [List.mem_append, List.mem_filter] at hc
  rcases hc with (hdiv | hquot) | ⟨hmem, _⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hdiv
    unfold bvaExtend
    rw [← clauseEvalVal_iff, clauseEvalVal, List.any_cons, List.any_cons, List.any_nil,
      Bool.or_false, evalLitVal_mkLit, substUpdate_self,
      evalLitVal_substUpdate_ne α _ (hfL f hf)]
    cases hall : L.all (evalLitVal α)
    · simp
    · simp [List.all_eq_true.mp hall f hf]
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hquot
    unfold bvaExtend
    by_cases hall : L.all (evalLitVal α) = true
    · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_cons, evalLitVal_mkLit,
        substUpdate_self, hall]
      simp
    · have hex : ∃ f0 ∈ L, evalLitVal α f0 = false :=
        Classical.byContradiction fun hno => hall <| List.all_eq_true.mpr fun f hf => by
          cases hv : evalLitVal α f
          · exact absurd ⟨f, hf, hv⟩ hno
          · rfl
      obtain ⟨f0, hf0, hf0_false⟩ := hex
      have hfq := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp (hent f0 hf0 q hq) α hα)
      simp only [clauseEvalVal, List.any_cons, hf0_false, Bool.false_or, List.any_eq_true] at hfq
      obtain ⟨x, hx, hxt⟩ := hfq
      rw [← clauseEvalVal_iff, clauseEvalVal, List.any_cons, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨x, hx, by rw [evalLitVal_substUpdate_ne α _ (hfQ q hq x hx)]; exact hxt⟩
  · exact (clause_sat_substUpdate_fresh _ (hfresh c hmem)).mpr
      ((cnf_sat_cnfOfClauses_iff α cs).mp hα c hmem)

/-- UNSAT soundness of Kissat Bounded Factorization (`factor.c`). -/
theorem bvaFactor_unsat_sound {z : Nat} {L : List Nat} {Q : List (List Nat)}
    {cs : List (List Nat)} (hval : BvaValid z L Q cs)
    (hu : (cnfOfClauses (bvaFactorClauses z L Q cs)).Unsat) :
    (cnfOfClauses cs).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu (bvaExtend z L α) (bvaFactor_sat_fwd hval hα)

/-- SAT model reconstruction for Kissat Bounded Factorization (`factor.c`): any model `α` of
the factored formula already satisfies the original formula `cs` directly. -/
theorem bvaFactor_sat_recon {z : Nat} {L : List Nat} {Q : List (List Nat)}
    {cs : List (List Nat)} {α : Nat → Bool}
    (hα : (cnfOfClauses (bvaFactorClauses z L Q cs)).Sat α) :
    (cnfOfClauses cs).Sat α := by
  have hα' := (cnf_sat_cnfOfClauses_iff α _).mp hα
  rw [cnf_sat_cnfOfClauses_iff]
  intro c hc
  by_cases hfac : bvaIsFactored L Q c = true
  · unfold bvaIsFactored at hfac
    simp only [List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at hfac
    obtain ⟨f, hf, hfc, q, hq, hqc⟩ := hfac
    have hdiv := (clauseEvalVal_iff α _).mpr
      (hα' [mkLit z true, f] (by
        unfold bvaFactorClauses bvaDivClauses
        simp only [List.mem_append, List.mem_map]
        exact Or.inl (Or.inl ⟨f, hf, rfl⟩)))
    have hquot := (clauseEvalVal_iff α _).mpr
      (hα' (mkLit z false :: q) (by
        unfold bvaFactorClauses bvaQuotClauses
        simp only [List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨q, hq, rfl⟩)))
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      evalLitVal_mkLit] at hdiv hquot
    rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
    cases hz : α z
    · simp only [hz] at hdiv
      exact ⟨f, hfc, by simpa using hdiv⟩
    · simp only [hz] at hquot
      have hq' : q.any (evalLitVal α) = true := by simpa using hquot
      obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp hq'
      exact ⟨x, hqc x hx, hxt⟩
  · have hfacf : bvaIsFactored L Q c = false := Bool.eq_false_iff.mpr hfac
    exact hα' c (by
      unfold bvaFactorClauses
      simp [hc, hfacf])

/-- Equisatisfiability of Kissat Bounded Factorization (`factor.c`). -/
theorem bvaFactor_equisat {z : Nat} {L : List Nat} {Q : List (List Nat)}
    {cs : List (List Nat)} (hval : BvaValid z L Q cs) :
    (∃ α, (cnfOfClauses cs).Sat α) ↔
    (∃ α, (cnfOfClauses (bvaFactorClauses z L Q cs)).Sat α) :=
  ⟨fun ⟨α, hα⟩ => ⟨bvaExtend z L α, bvaFactor_sat_fwd hval hα⟩,
    fun ⟨α, hα⟩ => ⟨α, bvaFactor_sat_recon hα⟩⟩

/-! ## 4. Unified Tier-B Inprocessing Trace and Executable `Array Bool` Reconstruction -/

/-- One Tier-B inprocessing step (`substitute.c`, `BCE`, `gates.c` BVE, or `factor.c` BVA). -/
inductive TierBStep where
  | subst (v l : Nat)
  | bce (l : Nat) (clause : List Nat)
  | gateBve (v : Nat) (gp : GatePartition)
  | bvaFactor (z : Nat) (dividers : List Nat) (quotients : List (List Nat))
  deriving Repr, DecidableEq

/-- Multi-step Tier-B inprocessing trace. -/
abbrev TierBTrace := List TierBStep

/-- Execute a single Tier-B transformation step on a clause list. -/
@[expose] def tierBStepApply (step : TierBStep) (cs : List (List Nat)) : List (List Nat) :=
  match step with
  | .subst v l => substClauses v l cs
  | .bce _ c => cs.erase c
  | .gateBve v gp => gateBveClauses v gp
  | .bvaFactor z L Q => bvaFactorClauses z L Q cs

/-- Reconstruct a model across a single Tier-B step. -/
@[expose] def tierBStepExtend (step : TierBStep) (α : Nat → Bool) : Nat → Bool :=
  match step with
  | .subst v l => substExtend v l α
  | .bce l c => extendBce l c α
  | .gateBve v gp => extendGateBve v gp.posClauses α
  | .bvaFactor _ _ _ => α

/-- Semantic validity of one Tier-B step on clause list `cs`. -/
@[expose] def TierBStepValid (cs : List (List Nat)) : TierBStep → Prop
  | .subst v l => litVar l ≠ v ∧ EquivEntailed (cnfOfClauses cs) v l
  | .bce l c => c ∈ cs ∧ IsBlockedOn (cs.erase c) c l
  | .gateBve v gp =>
    (∀ α, (cnfOfClauses gp.allClauses).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
    GatePartValid v gp ∧
    GateNonGateEntailed v gp
  | .bvaFactor z L Q => BvaValid z L Q cs

/-- Apply a multi-step Tier-B trace left-to-right. -/
@[expose] def tierBTraceApply : TierBTrace → List (List Nat) → List (List Nat)
  | [], cs => cs
  | s :: rest, cs => tierBTraceApply rest (tierBStepApply s cs)

/-- Reconstruct a model across a multi-step Tier-B trace right-to-left (`foldr`). -/
@[expose] def tierBTraceExtend (tr : TierBTrace) (α : Nat → Bool) : Nat → Bool :=
  tr.foldr tierBStepExtend α

/-- Inductive validity of a multi-step Tier-B trace on `cs`. -/
@[expose] def TierBTraceValid : List (List Nat) → TierBTrace → Prop
  | _, [] => True
  | cs, s :: rest => TierBStepValid cs s ∧ TierBTraceValid (tierBStepApply s cs) rest

theorem tierBStep_unsat {cs : List (List Nat)} {s : TierBStep}
    (hval : TierBStepValid cs s)
    (hu : (cnfOfClauses (tierBStepApply s cs)).Unsat) :
    (cnfOfClauses cs).Unsat := by
  cases s with
  | subst v l =>
    have hsub : substCnf v l (cnfOfClauses cs) = cnfOfClauses (substClauses v l cs) := by
      simp [substCnf]
    exact subst_unsat_sound hval.2 (by simpa [tierBStepApply, hsub] using hu)
  | bce l c =>
    exact bce_erase_unsat hu
  | gateBve v gp =>
    have hugp := gateBve_unsat_sound hu
    rw [CNF.unsat_iff_not_sat] at hugp ⊢
    intro α hα
    exact hugp α ((hval.1 α).mpr hα)
  | bvaFactor z L Q =>
    exact bvaFactor_unsat_sound hval hu

theorem tierBStep_sat_recon {cs : List (List Nat)} {s : TierBStep} {α : Nat → Bool}
    (hval : TierBStepValid cs s)
    (hsat : (cnfOfClauses (tierBStepApply s cs)).Sat α) :
    (cnfOfClauses cs).Sat (tierBStepExtend s α) := by
  cases s with
  | subst v l =>
    have hsub : substCnf v l (cnfOfClauses cs) = cnfOfClauses (substClauses v l cs) := by
      simp [substCnf]
    exact subst_sat_reconstruct (by simpa [tierBStepApply, hsub] using hsat)
  | bce l c =>
    exact bce_erase_sat hval.2 hsat
  | gateBve v gp =>
    exact (hval.1 _).mp (gateBve_sat_recon hval.2.1 hval.2.2 hsat)
  | bvaFactor z L Q =>
    exact bvaFactor_sat_recon hsat

/-- UNSAT soundness across a multi-step Tier-B inprocessing trace. -/
theorem tierBTrace_unsat {cs : List (List Nat)} {tr : TierBTrace}
    (hval : TierBTraceValid cs tr)
    (hu : (cnfOfClauses (tierBTraceApply tr cs)).Unsat) :
    (cnfOfClauses cs).Unsat := by
  induction tr generalizing cs with
  | nil => exact hu
  | cons s rest ih => exact tierBStep_unsat hval.1 (ih hval.2 hu)

/-- Explicit SAT model reconstruction across a multi-step Tier-B inprocessing trace. -/
theorem tierBTrace_sat_recon {cs : List (List Nat)} {tr : TierBTrace} {α : Nat → Bool}
    (hval : TierBTraceValid cs tr)
    (hsat : (cnfOfClauses (tierBTraceApply tr cs)).Sat α) :
    (cnfOfClauses cs).Sat (tierBTraceExtend tr α) := by
  induction tr generalizing cs with
  | nil => exact hsat
  | cons s rest ih => exact tierBStep_sat_recon hval.1 (ih hval.2 hsat)

/-- Equisatisfiability across a multi-step Tier-B inprocessing trace. -/
theorem tierBTrace_equisat {cs : List (List Nat)} {tr : TierBTrace}
    (hval : TierBTraceValid cs tr) :
    (∃ α, (cnfOfClauses cs).Sat α) ↔ (∃ α, (cnfOfClauses (tierBTraceApply tr cs)).Sat α) := by
  constructor
  · rintro ⟨α, hα⟩
    exact Classical.byContradiction fun hno =>
      CNF.unsat_iff_not_sat.mp
        (tierBTrace_unsat hval (CNF.unsat_iff_not_sat.mpr fun β hβ => hno ⟨β, hβ⟩)) α hα
  · rintro ⟨α, hα⟩
    exact ⟨tierBTraceExtend tr α, tierBTrace_sat_recon hval hα⟩

/-! ### Executable `Array Bool` Reconstruction Bridges -/

/-- Executable BCE witness reconstruction on `Array Bool`. -/
@[expose] def extendBceArr (l : Nat) (c : List Nat) (σ : Array Bool) : Array Bool :=
  if evalClause σ c then σ else arraySetPad σ (litVar l) (!(litSign l)) false

/-- Executable BCE stack reconstruction on `Array Bool`. -/
@[expose] def extendBceStackArr (st : BceReconStack) (σ : Array Bool) : Array Bool :=
  st.foldr (fun e acc => extendBceArr e.lit e.clause acc) σ

/-- Executable Gate-BVE witness reconstruction on `Array Bool`. -/
@[expose]
def extendGateBveArr (v : Nat) (posClauses : List (List Nat)) (σ : Array Bool) : Array Bool :=
  let σF := arraySetPad σ v false false
  if posClauses.all (evalClause σF) then σF else arraySetPad σ v true false

/-- Executable single-step Tier-B reconstruction on `Array Bool`. -/
@[expose] def tierBStepExtendArr (step : TierBStep) (σ : Array Bool) : Array Bool :=
  match step with
  | .subst v l => substExtendArr v l σ
  | .bce l c => extendBceArr l c σ
  | .gateBve v gp => extendGateBveArr v gp.posClauses σ
  | .bvaFactor _ _ _ => σ

/-- Executable multi-step Tier-B reconstruction on `Array Bool`. -/
@[expose] def tierBTraceExtendArr (tr : TierBTrace) (σ : Array Bool) : Array Bool :=
  tr.foldr tierBStepExtendArr σ

private theorem evalVar_arraySetPad (σ : Array Bool) (v : Nat) (val : Bool) :
    evalVar (arraySetPad σ v val false) = substUpdate (evalVar σ) v val := by
  funext w
  unfold evalVar substUpdate
  have hiff : ∀ (arr : Array Bool) (k : Nat), arr[k]?.getD false = arr.getD k false := by
    intro arr k
    by_cases hk : k < arr.size <;> simp [Array.getD, hk]
  rw [hiff, arraySetPad_getD, ← hiff]
  by_cases hw : w = v
  · subst hw; simp
  · simp [hw]

theorem evalVar_extendBceArr (l : Nat) (c : List Nat) (σ : Array Bool) :
    evalVar (extendBceArr l c σ) = extendBce l c (evalVar σ) := by
  unfold extendBceArr extendBce setLitTrue
  have hce : evalClause σ c = clauseEvalVal (evalVar σ) c := rfl
  rw [hce]
  split
  · rfl
  · exact evalVar_arraySetPad σ (litVar l) (!(litSign l))

theorem evalVar_extendBceStackArr (st : BceReconStack) (σ : Array Bool) :
    evalVar (extendBceStackArr st σ) = extendBceStack st (evalVar σ) := by
  induction st with
  | nil => rfl
  | cons e rest ih =>
    unfold extendBceStackArr extendBceStack
    simp only [List.foldr_cons]
    rw [evalVar_extendBceArr]
    exact congrArg (extendBce e.lit e.clause) ih

theorem evalVar_extendGateBveArr (v : Nat) (posClauses : List (List Nat)) (σ : Array Bool) :
    evalVar (extendGateBveArr v posClauses σ) = extendGateBve v posClauses (evalVar σ) := by
  unfold extendGateBveArr extendGateBve
  dsimp only
  have hcond : posClauses.all (evalClause (arraySetPad σ v false false)) =
      posClauses.all (clauseEvalVal (substUpdate (evalVar σ) v false)) := by
    have hfn : evalClause (arraySetPad σ v false false) =
        clauseEvalVal (substUpdate (evalVar σ) v false) := by
      funext c
      change clauseEvalVal (evalVar (arraySetPad σ v false false)) c = _
      rw [evalVar_arraySetPad]
    rw [hfn]
  rw [hcond]
  split
  · exact evalVar_arraySetPad σ v false
  · exact evalVar_arraySetPad σ v true

theorem evalVar_tierBStepExtendArr (s : TierBStep) (σ : Array Bool) :
    evalVar (tierBStepExtendArr s σ) = tierBStepExtend s (evalVar σ) := by
  cases s with
  | subst v l => exact evalVar_substExtendArr v l σ
  | bce l c => exact evalVar_extendBceArr l c σ
  | gateBve v gp => exact evalVar_extendGateBveArr v gp.posClauses σ
  | bvaFactor z L Q => rfl

theorem evalVar_tierBTraceExtendArr (tr : TierBTrace) (σ : Array Bool) :
    evalVar (tierBTraceExtendArr tr σ) = tierBTraceExtend tr (evalVar σ) := by
  induction tr with
  | nil => rfl
  | cons s rest ih =>
    unfold tierBTraceExtendArr tierBTraceExtend
    simp only [List.foldr_cons]
    rw [evalVar_tierBStepExtendArr]
    exact congrArg (tierBStepExtend s) ih

/-- Executable `checkModel` soundness bridge across a valid `BceReconStack`. -/
theorem extendBceStackArr_sound {cs : List (List Nat)} {st : BceReconStack} {σ : Array Bool}
    (hval : BceStackValid cs st)
    (h : checkModel (cnfOfClauses (bceApplyStack st cs)) σ = true) :
    checkModel (cnfOfClauses cs) (extendBceStackArr st σ) = true := by
  rw [checkModel_iff_sat] at h ⊢
  rw [evalVar_extendBceStackArr]
  exact bceStack_sat_recon hval h

/-- Executable `checkModel` soundness bridge across a valid multi-step Tier-B trace. -/
theorem tierBTraceExtendArr_sound {cs : List (List Nat)} {tr : TierBTrace} {σ : Array Bool}
    (hval : TierBTraceValid cs tr)
    (h : checkModel (cnfOfClauses (tierBTraceApply tr cs)) σ = true) :
    checkModel (cnfOfClauses cs) (tierBTraceExtendArr tr σ) = true := by
  rw [checkModel_iff_sat] at h ⊢
  rw [evalVar_tierBTraceExtendArr]
  exact tierBTrace_sat_recon hval h

end LeanQbe.T.Examples.Kissat.Ref
