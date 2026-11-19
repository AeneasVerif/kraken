module

public import LeanQbe.T.Examples.Kissat.CoreLemmas1

/-!
# Pure Lean Layer-A Soundness Theory for Equivalence / SCC Literal Substitution

Pure Lean (`CNF Nat`, zero `Kraken.Mem` or C0 imports) soundness theory for Kissat's
`substitute.c` (binary implication graph SCC equivalence detection, representative literal
substitution, tautology elimination, and model reconstruction):

1. **Assignment evaluation & tautology helpers**: `evalLitVal`, `clauseEvalVal`, `cnfEvalVal`,
   `substUpdate`, `clauseIsTaut`, `VarFreshIn`, `VarFreshCnf`, and `CNF Nat ↔ List (List Nat)`
   round-trip lemmas.
2. **Single-step representative substitution (`EquivEntailed`, `substCnf`, `substExtend`)**:
   if `F ⊨ (v ↔ l)`, substituting `l` for positive `v` and `¬l` for negative `v` across `F`
   (dropping tautologies) preserves `Unsat` (`subst_unsat_sound`), reconstructs SAT models
   explicitly via `α[v ↦ α.eval l]` (`subst_sat_reconstruct`), preserves equisatisfiability
   (`subst_equisat`), and eliminates `v` when `litVar l ≠ v` (`subst_var_elim`).
3. **Multi-step substitution trace / witness stack (`SubstTrace`, `substTraceApply`,
   `substExtendTrace`)**: compositional UNSAT preservation (`substTrace_unsat`), explicit SAT
   model reconstruction (`substTrace_sat`), and equisatisfiability (`substTrace_equisat`).
4. **Binary implication graph & simultaneous SCC substitution (`BinReach`, `substMapCnf`,
   `substMapExtend`)**: SCC equivalence (`binReach_scc_equiv`), same-SCC contradiction
   (`binReach_contra_unsat`), failed-literal unit detection (`binReach_failed_unit`),
   simultaneous representative substitution (`substMap_unsat_sound`, `substMap_sat_recon`),
   and executable `Array Bool` model reconstruction bridges (`substTraceExtendArr_sound`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std.Sat

/-! ## 1. Assignment evaluation, point updates, tautologies, and CNF bijection -/

@[simp] theorem litNeg_mkLit (v : Nat) (pol : Bool) :
    litNeg (mkLit v pol) = mkLit v (!pol) := by
  cases pol <;> simp [mkLit, litNeg_eq] <;> omega

theorem mkLit_litVar_litPol (l : Nat) : mkLit (litVar l) (litPol l) = l := by
  simp only [mkLit, litVar, litPol]
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h] <;> omega

theorem mkLit_ne_neg (v : Nat) (pol : Bool) : mkLit v pol ≠ mkLit v (!pol) := by
  cases pol <;> simp [mkLit] <;> omega

/-- Evaluate a Kissat-encoded literal `l` under a total Boolean assignment `α : Nat → Bool`. -/
@[inline] def evalLitVal (α : Nat → Bool) (l : Nat) : Bool :=
  α (litVar l) != litSign l

/-- Evaluate a clause (disjunction of Kissat literals) under `α : Nat → Bool`. -/
def clauseEvalVal (α : Nat → Bool) (c : List Nat) : Bool :=
  c.any (evalLitVal α)

/-- Evaluate a clause list (conjunction of clauses) under `α : Nat → Bool`. -/
def cnfEvalVal (α : Nat → Bool) (cs : List (List Nat)) : Bool :=
  cs.all (clauseEvalVal α)

/-- Point update `α[v ↦ val]` on a total Boolean assignment `α : Nat → Bool`. -/
@[inline] def substUpdate (α : Nat → Bool) (v : Nat) (val : Bool) : Nat → Bool :=
  fun x => if x == v then val else α x

/-- Tautology detector: `true` iff `c` contains a complementary pair `x` and `litNeg x`. -/
def clauseIsTaut (c : List Nat) : Bool :=
  c.any (fun x => c.contains (litNeg x))

/-- Variable `v` does not occur in any clause of `cs`. -/
def VarFreshIn (cs : List (List Nat)) (v : Nat) : Prop :=
  ∀ c ∈ cs, ∀ x ∈ c, litVar x ≠ v

/-- Executable Boolean checker for `VarFreshIn`. -/
def varFreshInBool (cs : List (List Nat)) (v : Nat) : Bool :=
  cs.all fun c => c.all fun x => litVar x != v

theorem varFreshInBool_iff (cs : List (List Nat)) (v : Nat) :
    varFreshInBool cs v = true ↔ VarFreshIn cs v := by
  simp [varFreshInBool, VarFreshIn, List.all_eq_true, bne_iff_ne]

/-- Variable `v` does not occur in any clause of `f : CNF Nat`. -/
def VarFreshCnf (f : CNF Nat) (v : Nat) : Prop :=
  VarFreshIn (clausesOfCnf f) v

theorem evalLitVal_iff (α : Nat → Bool) (l : Nat) :
    evalLitVal α l = true ↔ (cnfClause [l]).Sat α := by
  simp only [evalLitVal, sat_cnfClause_singleton]
  cases α (litVar l) <;> cases litSign l <;> decide

@[simp] theorem evalLitVal_litNeg (α : Nat → Bool) (l : Nat) :
    evalLitVal α (litNeg l) = !(evalLitVal α l) := by
  simp only [evalLitVal, litVar_litNeg, litSign_litNeg]
  cases α (litVar l) <;> cases litSign l <;> decide

@[simp] theorem evalLitVal_mkLit (α : Nat → Bool) (v : Nat) (pol : Bool) :
    evalLitVal α (mkLit v pol) = (α v == pol) := by
  simp only [evalLitVal, litVar_mkLit, litSign_mkLit]
  cases α v <;> cases pol <;> decide

theorem evalLitVal_evalVar (σ : Array Bool) (l : Nat) :
    evalLitVal (evalVar σ) l = evalLit σ l := rfl

theorem clauseEvalVal_iff (α : Nat → Bool) (c : List Nat) :
    clauseEvalVal α c = true ↔ (cnfClause c).Sat α := by
  rw [clauseEvalVal, List.any_eq_true, clause_sat_cnfClause_iff]
  constructor
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, (sat_cnfClause_singleton α l).mp ((evalLitVal_iff α l).mp h)⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, (evalLitVal_iff α l).mpr ((sat_cnfClause_singleton α l).mpr h)⟩

theorem cnfEvalVal_iff (α : Nat → Bool) (cs : List (List Nat)) :
    cnfEvalVal α cs = true ↔ (cnfOfClauses cs).Sat α := by
  simp only [cnfEvalVal, List.all_eq_true, clauseEvalVal_iff, cnf_sat_cnfOfClauses_iff]

@[simp] theorem substUpdate_self (α : Nat → Bool) (v : Nat) (val : Bool) :
    substUpdate α v val v = val := by
  simp [substUpdate]

@[simp] theorem substUpdate_ne (α : Nat → Bool) {v w : Nat} (val : Bool) (hne : w ≠ v) :
    substUpdate α v val w = α w := by
  simp [substUpdate, hne]

theorem evalLitVal_substUpdate_ne (α : Nat → Bool) {v l : Nat} (val : Bool)
    (hne : litVar l ≠ v) :
    evalLitVal (substUpdate α v val) l = evalLitVal α l := by
  simp [evalLitVal, substUpdate_ne α val hne]

theorem clause_sat_of_agree {α β : Nat → Bool} {c : List Nat}
    (h : ∀ x ∈ c, evalLitVal α x = evalLitVal β x) :
    (cnfClause c).Sat α ↔ (cnfClause c).Sat β := by
  simp only [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hs⟩ => ⟨x, hx, h x hx ▸ hs⟩, fun ⟨x, hx, hs⟩ => ⟨x, hx, (h x hx).symm ▸ hs⟩⟩

theorem clause_sat_substUpdate_fresh {α : Nat → Bool} {c : List Nat} {v : Nat} (val : Bool)
    (hf : ∀ x ∈ c, litVar x ≠ v) :
    (cnfClause c).Sat (substUpdate α v val) ↔ (cnfClause c).Sat α :=
  clause_sat_of_agree fun x hx => evalLitVal_substUpdate_ne α val (hf x hx)

theorem clause_sat_dedup_iff (α : Nat → Bool) (c : List Nat) :
    (cnfClause (dedupLits c)).Sat α ↔ (cnfClause c).Sat α := by
  simp only [clause_sat_cnfClause_iff]
  exact ⟨fun ⟨l, hl, hs⟩ => ⟨l, mem_dedupLits_iff.mp hl, hs⟩,
    fun ⟨l, hl, hs⟩ => ⟨l, mem_dedupLits_iff.mpr hl, hs⟩⟩

theorem clauseIsTaut_iff (c : List Nat) :
    clauseIsTaut c = true ↔ ∃ x ∈ c, litNeg x ∈ c := by
  simp [clauseIsTaut, List.any_eq_true]

/-- Any clause flagged by `clauseIsTaut` is satisfied under every assignment `α`. -/
theorem clauseIsTaut_sat {c : List Nat} (ht : clauseIsTaut c = true) (α : Nat → Bool) :
    (cnfClause c).Sat α := by
  obtain ⟨x, hx, hnx⟩ := (clauseIsTaut_iff c).mp ht
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
  cases h : evalLitVal α x
  · exact ⟨litNeg x, hnx, by simp [evalLitVal_litNeg, h]⟩
  · exact ⟨x, hx, h⟩

@[simp] theorem cnfOfClauses_clausesOfCnf (f : CNF Nat) :
    cnfOfClauses (clausesOfCnf f) = f := by
  cases f with
  | mk arr =>
    simp [cnfOfClauses, clausesOfCnf, Function.comp_def]

@[simp] theorem clausesOfCnf_cnfOfClauses (cs : List (List Nat)) :
    clausesOfCnf (cnfOfClauses cs) = cs := by
  simp [clausesOfCnf, cnfOfClauses, Function.comp_def]

theorem sat_iff_clausesOfCnf (α : Nat → Bool) (f : CNF Nat) :
    f.Sat α ↔ ∀ c ∈ clausesOfCnf f, (cnfClause c).Sat α := by
  have h := cnf_sat_cnfOfClauses_iff α (clausesOfCnf f)
  rwa [cnfOfClauses_clausesOfCnf] at h

theorem entails_mem_clausesOfCnf {f : CNF Nat} {c : List Nat} (hc : c ∈ clausesOfCnf f) :
    f.EntailsClause (cnfClause c) := by
  rw [CNF.entails_clause_def]
  intro α hα
  exact (sat_iff_clausesOfCnf α f).mp hα c hc

theorem entails_mem_cnfOfClauses {cs : List (List Nat)} {c : List Nat} (hc : c ∈ cs) :
    (cnfOfClauses cs).EntailsClause (cnfClause c) :=
  entails_mem_clausesOfCnf (by simpa using hc)

theorem checkModel_cnfOfClauses_eq_evalCnf (cs : List (List Nat)) (σ : Array Bool) :
    checkModel (cnfOfClauses cs) σ = evalCnf σ cs := by
  rw [← checkModel_iff_evalCnf, clausesOfCnf_cnfOfClauses]

/-! ## 2. Single-step equivalence substitution and model reconstruction -/

/-- Formula `f` entails the literal equivalence `v ↔ l`, represented by the two binary
implication clauses `[¬v, l]` (`v → l`) and `[v, ¬l]` (`l → v`). -/
def EquivEntailed (f : CNF Nat) (v l : Nat) : Prop :=
  f.EntailsClause (cnfClause [mkLit v false, l]) ∧
  f.EntailsClause (cnfClause [mkLit v true, litNeg l])

theorem equivEntailed_eval {f : CNF Nat} {v l : Nat} {α : Nat → Bool}
    (heq : EquivEntailed f v l) (hα : f.Sat α) :
    α v = evalLitVal α l := by
  have h1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp heq.1 α hα)
  have h2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp heq.2 α hα)
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    evalLitVal_mkLit, evalLitVal_litNeg] at h1 h2
  cases hv : α v <;> cases hl : evalLitVal α l <;> simp_all

/-- Substitute `l` for positive occurrences of `v` and `¬l` for negative occurrences of `v`. -/
@[inline] def substLit (v l x : Nat) : Nat :=
  if litVar x == v then
    if litSign x then litNeg l else l
  else
    x

/-- Substitute `(v ↦ l)` into clause `c`, deduplicating and dropping tautologies (`none`). -/
def substClause (v l : Nat) (c : List Nat) : Option (List Nat) :=
  let c' := dedupLits (c.map (substLit v l))
  if clauseIsTaut c' then none else some c'

/-- Apply single-variable substitution `(v ↦ l)` across a list of clauses, dropping tautologies. -/
def substClauses (v l : Nat) (cs : List (List Nat)) : List (List Nat) :=
  cs.filterMap (substClause v l)

/-- Apply single-variable substitution `(v ↦ l)` across a `CNF Nat`, dropping tautologies. -/
def substCnf (v l : Nat) (f : CNF Nat) : CNF Nat :=
  cnfOfClauses (substClauses v l (clausesOfCnf f))

/-- Explicit SAT model reconstruction for substitution `(v ↦ l)`: `α' = α[v ↦ α.eval l]`. -/
@[inline] def substExtend (v l : Nat) (α : Nat → Bool) : Nat → Bool :=
  substUpdate α v (evalLitVal α l)

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
  · have hxf : (litVar x == v) = false := beq_false_of_ne hx
    simp only [hxf, Bool.false_eq_true, ↓reduceIte]
    exact evalLitVal_substUpdate_ne α (evalLitVal α l) hx

theorem evalLitVal_substLit_of_eq {v l : Nat} {α : Nat → Bool}
    (heq : α v = evalLitVal α l) (x : Nat) :
    evalLitVal α (substLit v l x) = evalLitVal α x := by
  rw [← evalLitVal_substExtend]
  have hfn : substExtend v l α = α := by
    funext w
    unfold substExtend substUpdate
    by_cases hw : w = v
    · subst hw; simp [heq]
    · simp [hw]
  rw [hfn]

theorem clause_sat_subst_map_iff (v l : Nat) (α : Nat → Bool) (c : List Nat) :
    (cnfClause (c.map (substLit v l))).Sat α ↔ (cnfClause c).Sat (substExtend v l α) := by
  simp only [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hsat⟩
    exact ⟨x, hx, by rwa [evalLitVal_substExtend]⟩
  · rintro ⟨x, hx, hsat⟩
    exact ⟨substLit v l x, ⟨x, hx, rfl⟩, by rwa [← evalLitVal_substExtend]⟩

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
  rw [substCnf, cnf_sat_cnfOfClauses_iff]
  intro c' hc'
  rw [substClauses, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hsub⟩ := hc'
  unfold substClause at hsub
  dsimp only at hsub
  split at hsub
  · cases hsub
  · injection hsub with hce
    rw [← hce, clause_sat_dedup_iff, clause_sat_subst_map_iff]
    have hfn : substExtend v l α = α := by
      funext w
      unfold substExtend substUpdate
      by_cases hw : w = v
      · subst hw; simp [hval]
      · simp [hw]
    rw [hfn]
    exact (sat_iff_clausesOfCnf α f).mp hα c hc

/-- UNSAT soundness of single-step equivalence substitution (`F'.Unsat → F.Unsat`). -/
theorem subst_unsat_sound {f : CNF Nat} {v l : Nat}
    (heq : EquivEntailed f v l) (hu : (substCnf v l f).Unsat) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu α (subst_sat_fwd heq hα)

/-- Explicit SAT model reconstruction for single-step substitution: any model `α` of
`substCnf v l f` reconstructs to `α' = substExtend v l α` satisfying `f`. -/
theorem subst_sat_reconstruct {f : CNF Nat} {v l : Nat} {α : Nat → Bool}
    (hα : (substCnf v l f).Sat α) :
    f.Sat (substExtend v l α) := by
  rw [sat_iff_clausesOfCnf]
  intro c hc
  rw [← clause_sat_subst_map_iff, ← clause_sat_dedup_iff]
  by_cases ht : clauseIsTaut (dedupLits (c.map (substLit v l))) = true
  · exact clauseIsTaut_sat ht α
  · have hmem : dedupLits (c.map (substLit v l)) ∈ substClauses v l (clausesOfCnf f) := by
      rw [substClauses, List.mem_filterMap]
      exact ⟨c, hc, by simp [substClause, ht]⟩
    exact (cnf_sat_cnfOfClauses_iff α _).mp hα _ hmem

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
  unfold substClause at hsub
  dsimp only at hsub
  split at hsub
  · cases hsub
  · injection hsub with hce
    rw [← hce] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp (mem_dedupLits_iff.mp hx)
    exact litVar_substLit_ne hne y

/-! ## 3. Multi-step substitution trace and witness stack composition -/

/-- One recorded literal substitution `(var ↦ repr)` on the substitution witness stack. -/
structure SubstEntry where
  var : Nat
  repr : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Ordered sequence of substitution steps `[e₁, e₂, ..., eₖ]` applied left-to-right. -/
abbrev SubstTrace := List SubstEntry

/-- Apply a substitution trace left-to-right to a clause list. -/
def substTraceApplyClauses : SubstTrace → List (List Nat) → List (List Nat)
  | [], cs => cs
  | e :: rest, cs => substTraceApplyClauses rest (substClauses e.var e.repr cs)

/-- Apply a substitution trace left-to-right to a formula `f`. -/
def substTraceApply : SubstTrace → CNF Nat → CNF Nat
  | [], f => f
  | e :: rest, f => substTraceApply rest (substCnf e.var e.repr f)

theorem substTraceApply_cnfOfClauses (tr : SubstTrace) (cs : List (List Nat)) :
    substTraceApply tr (cnfOfClauses cs) = cnfOfClauses (substTraceApplyClauses tr cs) := by
  induction tr generalizing cs with
  | nil => rfl
  | cons e rest ih =>
    simp only [substTraceApply, substTraceApplyClauses, substCnf, clausesOfCnf_cnfOfClauses]
    exact ih (substClauses e.var e.repr cs)

/-- Validity of a substitution trace against `f`: each step `(v ↦ l)` is entailed by the
current transformed formula (with `litVar l ≠ v`). -/
def SubstTraceValid : CNF Nat → SubstTrace → Prop
  | _, [] => True
  | f, e :: rest =>
    litVar e.repr ≠ e.var ∧
    EquivEntailed f e.var e.repr ∧
    SubstTraceValid (substCnf e.var e.repr f) rest

/-- Reconstruct a model of `f` from a model `α` of `substTraceApply tr f` by unwinding the
substitution stack right-to-left (`foldr`). -/
def substExtendTrace (tr : SubstTrace) (α : Nat → Bool) : Nat → Bool :=
  tr.foldr (fun e acc => substExtend e.var e.repr acc) α

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

/-- Binary implication edge `a → b` entailed by `f` (equivalently `f ⊨ [¬a, b]`). -/
def BinEdge (f : CNF Nat) (a b : Nat) : Prop :=
  f.EntailsClause (cnfClause [litNeg a, b])

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

/-- Reflexive-transitive reachability `a →* b` in the binary implication graph of `f`. -/
inductive BinReach (f : CNF Nat) : Nat → Nat → Prop where
  | refl (a : Nat) : BinReach f a a
  | step {a b c : Nat} : BinEdge f a b → BinReach f b c → BinReach f a c

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

/-- Simultaneous polarity-respecting representative map lifted from variables (`Nat → Nat`)
to literals (`Nat → Nat`). -/
@[inline] def substMapLit (m : Nat → Nat) (x : Nat) : Nat :=
  if litSign x then litNeg (m (litVar x)) else m (litVar x)

/-- Apply simultaneous representative map `m` to clause `c`, dropping tautologies. -/
def substMapClause (m : Nat → Nat) (c : List Nat) : Option (List Nat) :=
  let c' := dedupLits (c.map (substMapLit m))
  if clauseIsTaut c' then none else some c'

/-- Apply simultaneous representative map `m` across a clause list, dropping tautologies. -/
def substMapClauses (m : Nat → Nat) (cs : List (List Nat)) : List (List Nat) :=
  cs.filterMap (substMapClause m)

/-- Apply simultaneous representative map `m` across a `CNF Nat`, dropping tautologies. -/
def substMapCnf (m : Nat → Nat) (f : CNF Nat) : CNF Nat :=
  cnfOfClauses (substMapClauses m (clausesOfCnf f))

/-- Simultaneous SAT model reconstruction for a representative map `m`:
`α'(v) = α.eval (m v)`. -/
@[inline] def substMapExtend (m : Nat → Nat) (α : Nat → Bool) : Nat → Bool :=
  fun v => evalLitVal α (m v)

theorem evalLitVal_substMapExtend (m : Nat → Nat) (α : Nat → Bool) (x : Nat) :
    evalLitVal (substMapExtend m α) x = evalLitVal α (substMapLit m x) := by
  unfold substMapExtend substMapLit
  cases hs : litSign x <;> simp [evalLitVal, hs]

theorem clause_sat_substMap_iff (m : Nat → Nat) (α : Nat → Bool) (c : List Nat) :
    (cnfClause (c.map (substMapLit m))).Sat α ↔ (cnfClause c).Sat (substMapExtend m α) := by
  simp only [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hsat⟩
    exact ⟨x, hx, by rwa [evalLitVal_substMapExtend]⟩
  · rintro ⟨x, hx, hsat⟩
    exact ⟨substMapLit m x, ⟨x, hx, rfl⟩, by rwa [← evalLitVal_substMapExtend]⟩

/-- Forward satisfiability preservation for simultaneous SCC representative substitution. -/
theorem substMap_sat_fwd {f : CNF Nat} {m : Nat → Nat} {α : Nat → Bool}
    (hm : ∀ v, EquivEntailed f v (m v)) (hα : f.Sat α) :
    (substMapCnf m f).Sat α := by
  have hfn : substMapExtend m α = α := by
    funext v
    exact (equivEntailed_eval (hm v) hα).symm
  rw [substMapCnf, cnf_sat_cnfOfClauses_iff]
  intro c' hc'
  rw [substMapClauses, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hsub⟩ := hc'
  unfold substMapClause at hsub
  dsimp only at hsub
  split at hsub
  · cases hsub
  · injection hsub with hce
    rw [← hce, clause_sat_dedup_iff, clause_sat_substMap_iff, hfn]
    exact (sat_iff_clausesOfCnf α f).mp hα c hc

/-- UNSAT soundness for simultaneous SCC representative substitution. -/
theorem substMap_unsat_sound {f : CNF Nat} {m : Nat → Nat}
    (hm : ∀ v, EquivEntailed f v (m v)) (hu : (substMapCnf m f).Unsat) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu α (substMap_sat_fwd hm hα)

/-- Explicit SAT model reconstruction for simultaneous SCC representative substitution. -/
theorem substMap_sat_recon {f : CNF Nat} {m : Nat → Nat} {α : Nat → Bool}
    (hα : (substMapCnf m f).Sat α) :
    f.Sat (substMapExtend m α) := by
  rw [sat_iff_clausesOfCnf]
  intro c hc
  rw [← clause_sat_substMap_iff, ← clause_sat_dedup_iff]
  by_cases ht : clauseIsTaut (dedupLits (c.map (substMapLit m))) = true
  · exact clauseIsTaut_sat ht α
  · have hmem : dedupLits (c.map (substMapLit m)) ∈ substMapClauses m (clausesOfCnf f) := by
      rw [substMapClauses, List.mem_filterMap]
      exact ⟨c, hc, by simp [substMapClause, ht]⟩
    exact (cnf_sat_cnfOfClauses_iff α _).mp hα _ hmem

/-- Equisatisfiability for simultaneous SCC representative substitution. -/
theorem substMap_equisat {f : CNF Nat} {m : Nat → Nat}
    (hm : ∀ v, EquivEntailed f v (m v)) :
    (∃ α, f.Sat α) ↔ (∃ α, (substMapCnf m f).Sat α) :=
  ⟨fun ⟨α, hα⟩ => ⟨α, substMap_sat_fwd hm hα⟩,
    fun ⟨α, hα⟩ => ⟨substMapExtend m α, substMap_sat_recon hα⟩⟩

/-! ## 5. Executable `Array Bool` model reconstruction bridge -/

/-- Executable single-step model update on `Array Bool` (`σ[v ↦ evalLit σ l]`). -/
def substExtendArr (v l : Nat) (σ : Array Bool) : Array Bool :=
  arraySetPad σ v (evalLit σ l) false

/-- Executable trace model reconstruction on `Array Bool`. -/
def substTraceExtendArr (tr : SubstTrace) (σ : Array Bool) : Array Bool :=
  tr.foldr (fun e acc => substExtendArr e.var e.repr acc) σ

/-- Executable representative table lookup (`tbl[v]?.getD (mkLit v true)`). -/
def reprOfTable (tbl : Array Nat) (v : Nat) : Nat :=
  tbl[v]?.getD (mkLit v true)

/-- Executable simultaneous SCC model reconstruction on `Array Bool`. -/
def substTableExtendArr (tbl : Array Nat) (σ : Array Bool) : Array Bool :=
  Array.ofFn (n := Nat.max σ.size tbl.size) fun i => evalLit σ (reprOfTable tbl i.val)

/-- Executable check that a binary implication edge `a → b` appears directly in `cs`. -/
def hasBinEdge (cs : List (List Nat)) (a b : Nat) : Bool :=
  cs.contains [litNeg a, b] || cs.contains [b, litNeg a]

/-- Executable check that `a :: rest` is a valid binary implication chain ending at `b`. -/
def checkBinPath (cs : List (List Nat)) : Nat → List Nat → Nat → Bool
  | a, [], b => a == b
  | a, next :: rest, b => hasBinEdge cs a next && checkBinPath cs next rest b

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
    simp only [checkBinPath, beq_iff_eq] at h
    subst h
    exact .refl a
  | a, next :: rest, b, h => by
    simp only [checkBinPath, Bool.and_eq_true] at h
    exact .step (hasBinEdge_sound h.1) (checkBinPath_sound h.2)

theorem evalVar_substExtendArr (v l : Nat) (σ : Array Bool) :
    evalVar (substExtendArr v l σ) = substExtend v l (evalVar σ) := by
  funext w
  unfold substExtendArr substExtend substUpdate evalVar
  have hiff : ∀ (arr : Array Bool) (k : Nat), arr[k]?.getD false = arr.getD k false := by
    intro arr k
    by_cases hk : k < arr.size <;> simp [Array.getD, hk]
  rw [hiff, arraySetPad_getD, ← hiff]
  by_cases hw : w = v
  · subst hw; simp [evalLit, evalLitVal, evalVar]
  · simp [hw]

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

end LeanQbe.T.Examples.Kissat
