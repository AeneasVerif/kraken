module

public import LeanQbe.T.Examples.Kissat.LayerASubstitute

/-!
# Pure Lean Layer-A Soundness Theory for BCE, Gate-Restricted BVE, and BVA / Factorization

Pure Lean (`CNF Nat`, zero `Kraken.Mem` or C0 imports) soundness theory for Kissat's Tier-B
equisatisfiable inprocessing passes (`eliminate.c`, `gates.c`, `definition.c`, `extend.c`,
`factor.c`):

1. **Blocked Clause Elimination (`BCE`) & `BceReconStack`**:
   if `l ∈ C` and every clause `D ∈ F` containing `¬l` has tautological resolvent
   `(C \ {l}) ∪ (D \ {¬l})`, removing `C` preserves equisatisfiability with explicit
   flip-if-falsified witness reconstruction (`extendBce`), composing over `BceReconStack`
   (`bceStack_unsat_sound`, `bceStack_sat_recon`, `bceStack_equisat`).
2. **Gate-Restricted BVE (`gates.c`, `eliminate.c`, `definition.c`)**:
   partitioning `P` / `N` around pivot `v` into gate clauses (`P_g`, `N_g`) and non-gate clauses
   (`P_ng`, `N_ng`), skipping `P_ng × N_ng` and resolving only `P_g × N` and `P × N_g` preserves
   `Unsat` (`gateBve_unsat_sound`) unconditionally and reconstructs SAT models (`extendGateBve`)
   under non-gate resolvent entailment (`gateBve_sat_recon`), semantic/functional gates
   (`gateFunc_bve_sat`, `gateFunc_bve_equisat`), or blocked non-gate resolvents
   (`gateBlocked_bve_sat`). Includes `GateFunctional` proofs for Kissat's `Equiv`, `AND`, `ITE`,
   `XOR`, and core-UNSAT `definition.c` gates.
3. **Blocked Clause Addition (`BCA`) & Bounded Variable Addition / Factorization (`factor.c`)**:
   proves general and fresh-variable BCA (`bca_unsat_sound`, `fresh_bca_batch_unsat`) and
   Kissat's fresh-variable divider/quotient factorization (`bvaFactor_unsat_sound`,
   `bvaFactor_sat_recon`, `bvaFactor_equisat`).
4. **Unified Tier-B Pipeline (`TierBStep`, `TierBTrace`)**:
   composes `Subst`, `BCE`, `Gate-BVE`, and `BVA/Factor` into a single witness-reconstructing
   trace (`tierBTrace_unsat`, `tierBTrace_sat_recon`, `tierBTrace_equisat`) with an executable
   `Array Bool` reconstruction bridge (`tierBTraceExtendArr_sound`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std.Sat

/-! ## 1. Blocked Clause Elimination (`BCE`) and `BceReconStack` -/

/-- Set literal `l` to `true` in assignment `α` by updating `litVar l ↦ !(litSign l)`. -/
@[inline] def setLitTrue (l : Nat) (α : Nat → Bool) : Nat → Bool :=
  substUpdate α (litVar l) (!(litSign l))

/-- Explicit flip-if-falsified BCE witness reconstruction: if `α` already satisfies `c`, return
`α` unchanged; otherwise flip `litVar l` so that `l` becomes `true`. -/
def extendBce (l : Nat) (c : List Nat) (α : Nat → Bool) : Nat → Bool :=
  if clauseEvalVal α c then α else setLitTrue l α

/-- Clause `c` is blocked on literal `l` with respect to clause set `cs`: `l ∈ c`, and every
clause `d ∈ cs` containing `¬l` produces a tautological resolvent `resolveOn l c d`. -/
def IsBlockedOn (cs : List (List Nat)) (c : List Nat) (l : Nat) : Prop :=
  l ∈ c ∧ ∀ d ∈ cs, litNeg l ∈ d → clauseIsTaut (resolveOn l c d) = true

/-- Executable Boolean checker for `IsBlockedOn`. -/
def isBlockedOnBool (cs : List (List Nat)) (c : List Nat) (l : Nat) : Bool :=
  c.contains l && cs.all (fun d => !d.contains (litNeg l) || clauseIsTaut (resolveOn l c d))

theorem isBlockedOnBool_iff (cs : List (List Nat)) (c : List Nat) (l : Nat) :
    isBlockedOnBool cs c l = true ↔ IsBlockedOn cs c l := by
  unfold isBlockedOnBool IsBlockedOn
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · rintro ⟨hl, hall⟩
    refine ⟨hl, fun d hd hnd => ?_⟩
    rcases hall d hd with hno | ht
    · exfalso
      have hne : d.contains (litNeg l) = true := List.contains_iff_mem.mpr hnd
      rw [hne] at hno; cases hno
    · exact ht
  · rintro ⟨hl, hall⟩
    refine ⟨hl, fun d hd => ?_⟩
    by_cases hnd : litNeg l ∈ d
    · exact Or.inr (hall d hd hnd)
    · exact Or.inl (Bool.eq_false_iff.mpr fun hc => hnd (List.contains_iff_mem.mp hc))

theorem isBlockedOn_mono {cs1 cs2 : List (List Nat)} {c : List Nat} {l : Nat}
    (hsub : ∀ d ∈ cs1, d ∈ cs2) (hblk : IsBlockedOn cs2 c l) : IsBlockedOn cs1 c l :=
  ⟨hblk.1, fun d hd => hblk.2 d (hsub d hd)⟩

@[simp] theorem evalLitVal_setLitTrue_self (l : Nat) (α : Nat → Bool) :
    evalLitVal (setLitTrue l α) l = true := by
  simp only [evalLitVal, setLitTrue, substUpdate_self]
  cases litSign l <;> decide

theorem evalLitVal_setLitTrue_ne {l x : Nat} (α : Nat → Bool) (hne : litVar x ≠ litVar l) :
    evalLitVal (setLitTrue l α) x = evalLitVal α x :=
  evalLitVal_substUpdate_ne α (!(litSign l)) hne

private theorem bce_flip_sat_other {c d : List Nat} {l : Nat} {α : Nat → Bool}
    (hl : l ∈ c) (hc_false : clauseEvalVal α c = false)
    (htaut : clauseIsTaut (resolveOn l c d) = true) :
    (cnfClause d).Sat (setLitTrue l α) := by
  have hcf : ∀ x ∈ c, evalLitVal α x = false := by
    intro x hx
    apply Bool.eq_false_iff.mpr
    intro ht
    have hany : clauseEvalVal α c = true :=
      List.any_eq_true.mpr ⟨x, hx, ht⟩
    rw [hc_false] at hany; cases hany
  obtain ⟨u, hu, hnu⟩ := (clauseIsTaut_iff _).mp htaut
  unfold resolveOn at hu hnu
  rw [List.mem_append] at hu hnu
  have hcase : ∀ a b, a ∈ c.filter (· != l) → b ∈ d.filter (· != litNeg l) →
      b = litNeg a → (cnfClause d).Sat (setLitTrue l α) := by
    intro a b ha hb hba
    rw [List.mem_filter, bne_iff_ne] at ha hb
    rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
    by_cases hvar : litVar a = litVar l
    · rcases (litVar_eq_iff a l).mp hvar with rfl | rfl
      · exact absurd rfl ha.2
      · rw [litNeg_litNeg] at hba
        exact ⟨b, hb.1, by rw [hba]; exact evalLitVal_setLitTrue_self l α⟩
    · have hvb : litVar b ≠ litVar l := by rw [hba, litVar_litNeg]; exact hvar
      have ha_f : evalLitVal α a = false := hcf a ha.1
      refine ⟨b, hb.1, ?_⟩
      rw [evalLitVal_setLitTrue_ne α hvb, hba, evalLitVal_litNeg, ha_f]
      rfl
  rcases hu with hu1 | hu2 <;> rcases hnu with hnu1 | hnu2
  · rw [List.mem_filter] at hu1 hnu1
    have h1 := hcf u hu1.1
    have h2 := hcf (litNeg u) hnu1.1
    rw [evalLitVal_litNeg, h1] at h2; cases h2
  · exact hcase u (litNeg u) hu1 hnu2 rfl
  · exact hcase (litNeg u) u hnu1 hu2 (litNeg_litNeg u).symm
  · rw [List.mem_filter] at hu2 hnu2
    exact clauseIsTaut_sat ((clauseIsTaut_iff d).mpr ⟨u, hu2.1, hnu2.1⟩) (setLitTrue l α)

/-- Fundamental Blocked Clause Witness Theorem: if `c` is blocked on `l` against `cs` and `α`
satisfies `cs`, then `extendBce l c α` satisfies `c :: cs`. -/
theorem bce_extend_sat {cs : List (List Nat)} {c : List Nat} {l : Nat} {α : Nat → Bool}
    (hblk : IsBlockedOn cs c l) (hsat : (cnfOfClauses cs).Sat α) :
    (cnfOfClauses (c :: cs)).Sat (extendBce l c α) := by
  rw [cnf_sat_cnfOfClauses_iff] at hsat ⊢
  unfold extendBce
  by_cases hc : clauseEvalVal α c = true
  · simp only [hc, ↓reduceIte]
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hmem
    · exact (clauseEvalVal_iff α d).mp hc
    · exact hsat d hmem
  · have hcf : clauseEvalVal α c = false := Bool.eq_false_iff.mpr hc
    simp only [hcf, Bool.false_eq_true, ↓reduceIte]
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hmem
    · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
      exact ⟨l, hblk.1, evalLitVal_setLitTrue_self l α⟩
    · by_cases hnl : litNeg l ∈ d
      · exact bce_flip_sat_other hblk.1 hcf (hblk.2 d hmem hnl)
      · obtain ⟨y, hy, hysat⟩ := List.any_eq_true.mp ((clauseEvalVal_iff α d).mpr (hsat d hmem))
        have hvy : litVar y ≠ litVar l := by
          intro heq
          rcases (litVar_eq_iff y l).mp heq with rfl | rfl
          · have hct : clauseEvalVal α c = true := List.any_eq_true.mpr ⟨y, hblk.1, hysat⟩
            rw [hcf] at hct; cases hct
          · exact hnl hy
        rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
        exact ⟨y, hy, by rw [evalLitVal_setLitTrue_ne α hvy]; exact hysat⟩

private theorem mem_of_mem_erase {cs : List (List Nat)} {c d : List Nat}
    (hd : d ∈ cs.erase c) : d ∈ cs :=
  List.mem_of_mem_erase hd

private theorem mem_or_eq_of_mem {cs : List (List Nat)} {c d : List Nat}
    (hd : d ∈ cs) : d = c ∨ d ∈ cs.erase c := by
  by_cases hdc : d = c
  · exact Or.inl hdc
  · exact Or.inr ((List.mem_erase_of_ne hdc).mpr hd)

/-- UNSAT soundness of single-step BCE (`(cs.erase c).Unsat → cs.Unsat`). -/
theorem bce_erase_unsat {cs : List (List Nat)} {c : List Nat}
    (hu : (cnfOfClauses (cs.erase c)).Unsat) : (cnfOfClauses cs).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα
  exact hu α ((cnf_sat_cnfOfClauses_iff α _).mpr fun d hd => hα d (mem_of_mem_erase hd))

/-- Explicit SAT model reconstruction for single-step BCE removing a blocked clause `c ∈ cs`. -/
theorem bce_erase_sat {cs : List (List Nat)} {c : List Nat} {l : Nat} {α : Nat → Bool}
    (hblk : IsBlockedOn (cs.erase c) c l)
    (hsat : (cnfOfClauses (cs.erase c)).Sat α) :
    (cnfOfClauses cs).Sat (extendBce l c α) := by
  have hext := (cnf_sat_cnfOfClauses_iff _ _).mp (bce_extend_sat hblk hsat)
  rw [cnf_sat_cnfOfClauses_iff]
  intro d hd
  rcases mem_or_eq_of_mem (c := c) hd with rfl | hmem
  · exact hext d (List.mem_cons_self ..)
  · exact hext d (List.mem_cons_of_mem c hmem)

/-- Equisatisfiability of single-step BCE (`F` and `F \ {C}` are equisatisfiable). -/
theorem bce_erase_equisat {cs : List (List Nat)} {c : List Nat} {l : Nat}
    (hblk : IsBlockedOn (cs.erase c) c l) :
    (∃ α, (cnfOfClauses cs).Sat α) ↔ (∃ α, (cnfOfClauses (cs.erase c)).Sat α) := by
  constructor
  · rintro ⟨α, hα⟩
    rw [cnf_sat_cnfOfClauses_iff] at hα
    exact ⟨α, (cnf_sat_cnfOfClauses_iff α _).mpr fun d hd => hα d (mem_of_mem_erase hd)⟩
  · rintro ⟨α, hα⟩
    exact ⟨extendBce l c α, bce_erase_sat hblk hα⟩

/-- Witness entry for one eliminated blocked clause on the reconstruction stack. -/
structure BceReconEntry where
  lit : Nat
  clause : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Composable reconstruction stack for iterated Blocked Clause Elimination. -/
abbrev BceReconStack := List BceReconEntry

/-- Apply a BCE elimination stack left-to-right to a clause list. -/
def bceApplyStack : BceReconStack → List (List Nat) → List (List Nat)
  | [], cs => cs
  | e :: rest, cs => bceApplyStack rest (cs.erase e.clause)

/-- Validity of a BCE elimination stack: every popped clause is blocked on its witness literal
with respect to the remaining clauses. -/
def BceStackValid : List (List Nat) → BceReconStack → Prop
  | _, [] => True
  | cs, e :: rest =>
    e.clause ∈ cs ∧
    IsBlockedOn (cs.erase e.clause) e.clause e.lit ∧
    BceStackValid (cs.erase e.clause) rest

/-- Unwind a `BceReconStack` right-to-left (`foldr`) to reconstruct a model of the original CNF. -/
def extendBceStack (st : BceReconStack) (α : Nat → Bool) : Nat → Bool :=
  st.foldr (fun e acc => extendBce e.lit e.clause acc) α

theorem bceApplyStack_append (st1 st2 : BceReconStack) (cs : List (List Nat)) :
    bceApplyStack (st1 ++ st2) cs = bceApplyStack st2 (bceApplyStack st1 cs) := by
  induction st1 generalizing cs with
  | nil => rfl
  | cons e rest ih => exact ih (cs.erase e.clause)

theorem extendBceStack_append (st1 st2 : BceReconStack) (α : Nat → Bool) :
    extendBceStack (st1 ++ st2) α = extendBceStack st1 (extendBceStack st2 α) := by
  simp [extendBceStack, List.foldr_append]

theorem bceStackValid_append {cs : List (List Nat)} {st1 st2 : BceReconStack}
    (h1 : BceStackValid cs st1) (h2 : BceStackValid (bceApplyStack st1 cs) st2) :
    BceStackValid cs (st1 ++ st2) := by
  induction st1 generalizing cs with
  | nil => exact h2
  | cons e rest ih =>
    obtain ⟨hmem, hblk, hrest⟩ := h1
    exact ⟨hmem, hblk, ih hrest h2⟩

/-- UNSAT soundness over an arbitrary `BceReconStack`. -/
theorem bceStack_unsat_sound {cs : List (List Nat)} {st : BceReconStack}
    (hu : (cnfOfClauses (bceApplyStack st cs)).Unsat) : (cnfOfClauses cs).Unsat := by
  induction st generalizing cs with
  | nil => exact hu
  | cons e rest ih => exact bce_erase_unsat (ih hu)

/-- Explicit SAT model reconstruction over a valid `BceReconStack`. -/
theorem bceStack_sat_recon {cs : List (List Nat)} {st : BceReconStack} {α : Nat → Bool}
    (hval : BceStackValid cs st)
    (hsat : (cnfOfClauses (bceApplyStack st cs)).Sat α) :
    (cnfOfClauses cs).Sat (extendBceStack st α) := by
  induction st generalizing cs with
  | nil => exact hsat
  | cons e rest ih =>
    obtain ⟨_, hblk, hrest⟩ := hval
    exact bce_erase_sat hblk (ih hrest hsat)

/-- Equisatisfiability over a valid `BceReconStack`. -/
theorem bceStack_equisat {cs : List (List Nat)} {st : BceReconStack}
    (hval : BceStackValid cs st) :
    (∃ α, (cnfOfClauses cs).Sat α) ↔ (∃ α, (cnfOfClauses (bceApplyStack st cs)).Sat α) := by
  constructor
  · rintro ⟨α, hα⟩
    exact Classical.byContradiction fun hno =>
      CNF.unsat_iff_not_sat.mp
        (bceStack_unsat_sound (st := st) (CNF.unsat_iff_not_sat.mpr fun β hβ => hno ⟨β, hβ⟩))
        α hα
  · rintro ⟨α, hα⟩
    exact ⟨extendBceStack st α, bceStack_sat_recon hval hα⟩

/-! ## 2. Gate-Restricted BVE (`gates.c`, `eliminate.c`, `definition.c`) -/

/-- Partition of a clause database around pivot variable `v` into positive/negative gate clauses
(`posGate`, `negGate`), positive/negative non-gate clauses (`posNonGate`, `negNonGate`), and
pivot-free remainder clauses (`rest`). -/
structure GatePartition where
  posGate : List (List Nat)
  posNonGate : List (List Nat)
  negGate : List (List Nat)
  negNonGate : List (List Nat)
  rest : List (List Nat)
  deriving Repr, DecidableEq, Inhabited

def GatePartition.posClauses (gp : GatePartition) : List (List Nat) :=
  gp.posGate ++ gp.posNonGate

def GatePartition.negClauses (gp : GatePartition) : List (List Nat) :=
  gp.negGate ++ gp.negNonGate

def GatePartition.gateClauses (gp : GatePartition) : List (List Nat) :=
  gp.posGate ++ gp.negGate

def GatePartition.allClauses (gp : GatePartition) : List (List Nat) :=
  gp.posGate ++ gp.posNonGate ++ gp.negGate ++ gp.negNonGate ++ gp.rest

/-- Partition validity around pivot variable `v`. -/
def GatePartValid (v : Nat) (gp : GatePartition) : Prop :=
  (∀ c ∈ gp.posClauses, mkLit v true ∈ c) ∧
  (∀ d ∈ gp.negClauses, mkLit v false ∈ d) ∧
  (∀ r ∈ gp.rest, ∀ x ∈ r, litVar x ≠ v)

/-- Executable partitioning of `cs` around variable `v` using gate classifier `isGate`. -/
def partitionOnVar (v : Nat) (isGate : List Nat → Bool) (cs : List (List Nat)) : GatePartition :=
  let p := mkLit v true
  let np := mkLit v false
  let pos := cs.filter (fun c => c.contains p)
  let neg := cs.filter (fun c => !c.contains p && c.contains np)
  let rest := cs.filter (fun c => !c.contains p && !c.contains np)
  { posGate := pos.filter isGate
    posNonGate := pos.filter (fun c => !isGate c)
    negGate := neg.filter isGate
    negNonGate := neg.filter (fun c => !isGate c)
    rest := rest }

theorem partitionOnVar_valid (v : Nat) (isGate : List Nat → Bool) (cs : List (List Nat)) :
    GatePartValid v (partitionOnVar v isGate cs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    unfold GatePartition.posClauses partitionOnVar at hc
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hc
    rcases hc with ⟨⟨_, hp⟩, _⟩ | ⟨⟨_, hp⟩, _⟩ <;> exact hp
  · intro d hd
    unfold GatePartition.negClauses partitionOnVar at hd
    simp only [List.mem_append, List.mem_filter, Bool.and_eq_true, List.contains_iff_mem] at hd
    rcases hd with ⟨⟨_, _, hnp⟩, _⟩ | ⟨⟨_, _, hnp⟩, _⟩ <;> exact hnp
  · intro r hr x hx hvx
    unfold partitionOnVar at hr
    simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hr
    have hp : mkLit v true ∉ r := fun hm => by
      have := List.contains_iff_mem.mpr hm; rw [this] at hr; cases hr.2.1
    have hnp : mkLit v false ∉ r := fun hm => by
      have := List.contains_iff_mem.mpr hm; rw [this] at hr; cases hr.2.2
    have hveq : litVar x = litVar (mkLit v true) := by simpa using hvx
    rcases (litVar_eq_iff x (mkLit v true)).mp hveq with rfl | hne
    · exact hp hx
    · rw [litNeg_mkLit] at hne; exact hnp (hne ▸ hx)

theorem partitionOnVar_sat_iff (v : Nat) (isGate : List Nat → Bool) (cs : List (List Nat))
    (α : Nat → Bool) :
    (cnfOfClauses (partitionOnVar v isGate cs).allClauses).Sat α ↔ (cnfOfClauses cs).Sat α := by
  simp only [cnf_sat_cnfOfClauses_iff, GatePartition.allClauses, partitionOnVar, List.mem_append,
    List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · intro h c hc
    by_cases hp : c.contains (mkLit v true) = true
    · by_cases hg : isGate c = true
      · exact h c (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨hc, hp⟩, hg⟩))))
      · have hgf : isGate c = false := Bool.eq_false_iff.mpr hg
        exact h c (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hc, hp⟩, by simp [hgf]⟩))))
    · have hpf : c.contains (mkLit v true) = false := Bool.eq_false_iff.mpr hp
      by_cases hnp : c.contains (mkLit v false) = true
      · by_cases hg : isGate c = true
        · exact h c (Or.inl (Or.inl (Or.inr ⟨⟨hc, hpf, hnp⟩, hg⟩)))
        · have hgf : isGate c = false := Bool.eq_false_iff.mpr hg
          exact h c (Or.inl (Or.inr ⟨⟨hc, hpf, hnp⟩, by simp [hgf]⟩))
      · have hnpf : c.contains (mkLit v false) = false := Bool.eq_false_iff.mpr hnp
        exact h c (Or.inr ⟨hc, hpf, hnpf⟩)
  · intro h c hc
    rcases hc with ((((⟨⟨hmem, _⟩, _⟩ | ⟨⟨hmem, _⟩, _⟩) | ⟨⟨hmem, _⟩, _⟩) | ⟨⟨hmem, _⟩, _⟩) |
      ⟨hmem, _⟩) <;> exact h c hmem

/-- All non-tautological deduplicated resolvents on pivot literal `p` across `as × bs`. -/
def nonTautResolvents (p : Nat) (as bs : List (List Nat)) : List (List Nat) :=
  as.flatMap fun c => bs.filterMap fun d =>
    let r := dedupLits (resolveOn p c d)
    if clauseIsTaut r then none else some r

theorem mem_nonTautResolvents_iff {p : Nat} {as bs : List (List Nat)} {r : List Nat} :
    r ∈ nonTautResolvents p as bs ↔
      ∃ c ∈ as, ∃ d ∈ bs,
        clauseIsTaut (dedupLits (resolveOn p c d)) = false ∧
        r = dedupLits (resolveOn p c d) := by
  unfold nonTautResolvents
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, d, hd, hite⟩
    split at hite
    · cases hite
    · rename_i hnt
      injection hite with hr
      exact ⟨c, hc, d, hd, Bool.eq_false_iff.mpr hnt, hr.symm⟩
  · rintro ⟨c, hc, d, hd, hnt, rfl⟩
    exact ⟨c, hc, d, hd, by simp [hnt]⟩

/-- Gate-restricted BVE output clauses: retains `rest` and resolves ONLY `posGate × negClauses`
and `posNonGate × negGate` (skipping `posNonGate × negNonGate`). -/
def gateBveClauses (v : Nat) (gp : GatePartition) : List (List Nat) :=
  let p := mkLit v true
  gp.rest ++
    nonTautResolvents p gp.posGate gp.negClauses ++
    nonTautResolvents p gp.posNonGate gp.negGate

/-- Full BVE output clauses (for comparison and blocked-resolvent composition). -/
def fullBveClauses (v : Nat) (gp : GatePartition) : List (List Nat) :=
  gateBveClauses v gp ++ nonTautResolvents (mkLit v true) gp.posNonGate gp.negNonGate

/-- Explicit SAT model reconstruction for gate-restricted (and full) BVE: assign `v := false`
if `α[v ↦ false]` satisfies all positive clauses `posClauses`, otherwise assign `v := true`. -/
def extendGateBve (v : Nat) (posClauses : List (List Nat)) (α : Nat → Bool) : Nat → Bool :=
  if posClauses.all (clauseEvalVal (substUpdate α v false)) then
    substUpdate α v false
  else
    substUpdate α v true

/-- Non-gate resolvent entailment condition: every non-tautological resolvent of `posNonGate`
with `negNonGate` is already entailed by `gateBveClauses v gp`. -/
def GateNonGateEntailed (v : Nat) (gp : GatePartition) : Prop :=
  ∀ c ∈ gp.posNonGate, ∀ d ∈ gp.negNonGate,
    let r := dedupLits (resolveOn (mkLit v true) c d)
    clauseIsTaut r = false →
    (cnfOfClauses (gateBveClauses v gp)).EntailsClause (cnfClause r)

/-- Semantic / functional gate definition (`gates.c`, `definition.c`): no assignment to variables
other than `v` can simultaneously satisfy `posGate` with `v = false` and `negGate` with
`v = true`. -/
def GateFunctional (v : Nat) (posGate negGate : List (List Nat)) : Prop :=
  ∀ α : Nat → Bool,
    ¬ ((cnfOfClauses posGate).Sat (substUpdate α v false) ∧
       (cnfOfClauses negGate).Sat (substUpdate α v true))

private theorem sat_resolveOn_of_sat {p : Nat} {c d : List Nat} {α : Nat → Bool}
    (hc : (cnfClause c).Sat α) (hd : (cnfClause d).Sat α) :
    (cnfClause (resolveOn p c d)).Sat α := by
  have hf : (cnfOfClauses [c, d]).Sat α := by
    rw [cnf_sat_cnfOfClauses_iff]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  have h1 : (cnfOfClauses [c, d]).EntailsClause (cnfClause c) :=
    entails_mem_clausesOfCnf (by simp)
  have h2 : (cnfOfClauses [c, d]).EntailsClause (cnfClause d) :=
    entails_mem_clausesOfCnf (by simp)
  exact CNF.entails_clause_def.mp (entails_resolve (p := p) h1 h2) α hf

/-- Forward satisfiability preservation of gate-restricted BVE (unconditional: every emitted
clause is either in `rest` or a valid resolvent of `allClauses`). -/
theorem gateBve_sat_fwd {v : Nat} {gp : GatePartition} {α : Nat → Bool}
    (hα : (cnfOfClauses gp.allClauses).Sat α) :
    (cnfOfClauses (gateBveClauses v gp)).Sat α := by
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  have hmem_all : ∀ x, x ∈ gp.rest ∨ x ∈ gp.posGate ∨ x ∈ gp.posNonGate ∨
      x ∈ gp.negGate ∨ x ∈ gp.negNonGate → (cnfClause x).Sat α := by
    intro x hx
    apply hα x
    unfold GatePartition.allClauses
    simp only [List.mem_append]
    rcases hx with h | h | h | h | h <;> simp [h]
  intro r hr
  unfold gateBveClauses at hr
  simp only [List.mem_append] at hr
  rcases hr with (hr1 | hr2) | hr3
  · exact hmem_all r (Or.inl hr1)
  · obtain ⟨c, hc, d, hd, _, rfl⟩ := mem_nonTautResolvents_iff.mp hr2
    rw [clause_sat_dedup_iff]
    have hdsat : (cnfClause d).Sat α := by
      rcases List.mem_append.mp hd with hd1 | hd2
      · exact hmem_all d (Or.inr (Or.inr (Or.inr (Or.inl hd1))))
      · exact hmem_all d (Or.inr (Or.inr (Or.inr (Or.inr hd2))))
    exact sat_resolveOn_of_sat (hmem_all c (Or.inr (Or.inl hc))) hdsat
  · obtain ⟨c, hc, d, hd, _, rfl⟩ := mem_nonTautResolvents_iff.mp hr3
    rw [clause_sat_dedup_iff]
    exact sat_resolveOn_of_sat
      (hmem_all c (Or.inr (Or.inr (Or.inl hc))))
      (hmem_all d (Or.inr (Or.inr (Or.inr (Or.inl hd)))))

/-- UNSAT soundness of gate-restricted BVE (`(gateBveClauses v gp).Unsat → gp.allClauses.Unsat`). -/
theorem gateBve_unsat_sound {v : Nat} {gp : GatePartition}
    (hu : (cnfOfClauses (gateBveClauses v gp)).Unsat) :
    (cnfOfClauses gp.allClauses).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu α (gateBve_sat_fwd hα)

private theorem false_filter_of_false_update_false {v : Nat} {c : List Nat} {α : Nat → Bool}
    (hcf : clauseEvalVal (substUpdate α v false) c = false) :
    ∀ x ∈ c.filter (· != mkLit v true), evalLitVal α x = false := by
  intro x hx
  rw [List.mem_filter, bne_iff_ne] at hx
  have hxf : evalLitVal (substUpdate α v false) x = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hany : clauseEvalVal (substUpdate α v false) c = true :=
      List.any_eq_true.mpr ⟨x, hx.1, ht⟩
    rw [hcf] at hany; cases hany
  have hvar : litVar x ≠ v := by
    intro hv
    have hveq : litVar x = litVar (mkLit v true) := by simpa using hv
    rcases (litVar_eq_iff x (mkLit v true)).mp hveq with h1 | h2
    · exact hx.2 h1
    · rw [litNeg_mkLit] at h2
      rw [h2, evalLitVal_mkLit, substUpdate_self] at hxf
      cases hxf
  rwa [evalLitVal_substUpdate_ne α false hvar] at hxf

private theorem false_filter_of_false_update_true {v : Nat} {d : List Nat} {α : Nat → Bool}
    (hdf : clauseEvalVal (substUpdate α v true) d = false) :
    ∀ y ∈ d.filter (· != mkLit v false), evalLitVal α y = false := by
  intro y hy
  rw [List.mem_filter, bne_iff_ne] at hy
  have hyf : evalLitVal (substUpdate α v true) y = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hany : clauseEvalVal (substUpdate α v true) d = true :=
      List.any_eq_true.mpr ⟨y, hy.1, ht⟩
    rw [hdf] at hany; cases hany
  have hvar : litVar y ≠ v := by
    intro hv
    have hveq : litVar y = litVar (mkLit v false) := by simpa using hv
    rcases (litVar_eq_iff y (mkLit v false)).mp hveq with h1 | h2
    · exact hy.2 h1
    · rw [litNeg_mkLit] at h2
      rw [h2, evalLitVal_mkLit, substUpdate_self] at hyf
      cases hyf
  rwa [evalLitVal_substUpdate_ne α true hvar] at hyf

private theorem sat_neg_of_resolve_sat {v : Nat} {c d : List Nat} {α : Nat → Bool}
    (hcf : clauseEvalVal (substUpdate α v false) c = false)
    (hres : (cnfClause (resolveOn (mkLit v true) c d)).Sat α) :
    (cnfClause d).Sat (substUpdate α v true) := by
  have hleft := false_filter_of_false_update_false hcf
  obtain ⟨y, hy, hysat⟩ := List.any_eq_true.mp ((clauseEvalVal_iff α _).mpr hres)
  unfold resolveOn at hy
  rw [List.mem_append] at hy
  rcases hy with hy1 | hy2
  · rw [hleft y hy1] at hysat; cases hysat
  · rw [List.mem_filter, bne_iff_ne, litNeg_mkLit] at hy2
    rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
    by_cases hv : litVar y = v
    · have hveq : litVar y = litVar (mkLit v true) := by simpa using hv
      rcases (litVar_eq_iff y (mkLit v true)).mp hveq with rfl | h2
      · exact ⟨mkLit v true, hy2.1, by simp⟩
      · rw [litNeg_mkLit] at h2; exact absurd h2 hy2.2
    · exact ⟨y, hy2.1, by rw [evalLitVal_substUpdate_ne α true hv]; exact hysat⟩

private theorem sat_nonTaut_or_taut {p : Nat} {as bs : List (List Nat)} {c d : List Nat}
    {α : Nat → Bool} (hc : c ∈ as) (hd : d ∈ bs)
    (hsat : ∀ r ∈ nonTautResolvents p as bs, (cnfClause r).Sat α) :
    (cnfClause (resolveOn p c d)).Sat α := by
  rw [← clause_sat_dedup_iff]
  by_cases ht : clauseIsTaut (dedupLits (resolveOn p c d)) = true
  · exact clauseIsTaut_sat ht α
  · exact hsat _ (mem_nonTautResolvents_iff.mpr
      ⟨c, hc, d, hd, Bool.eq_false_iff.mpr ht, rfl⟩)

/-- Core full-resolvent SAT model reconstruction: if `α` satisfies `rest` and every resolvent
of `posClauses × negClauses`, then `extendGateBve v gp.posClauses α` satisfies `gp.allClauses`. -/
theorem fullBve_sat_recon {v : Nat} {gp : GatePartition} {α : Nat → Bool}
    (hpart : GatePartValid v gp)
    (hrest : ∀ r ∈ gp.rest, (cnfClause r).Sat α)
    (hres : ∀ c ∈ gp.posClauses, ∀ d ∈ gp.negClauses,
      (cnfClause (resolveOn (mkLit v true) c d)).Sat α) :
    (cnfOfClauses gp.allClauses).Sat (extendGateBve v gp.posClauses α) := by
  obtain ⟨hpos, hneg, hrfresh⟩ := hpart
  have hsat_all : ∀ β,
      (∀ c ∈ gp.posClauses, (cnfClause c).Sat β) →
      (∀ d ∈ gp.negClauses, (cnfClause d).Sat β) →
      (∀ r ∈ gp.rest, (cnfClause r).Sat β) →
      (cnfOfClauses gp.allClauses).Sat β := by
    intro β hp hn hr
    rw [cnf_sat_cnfOfClauses_iff]
    intro x hx
    unfold GatePartition.allClauses at hx
    unfold GatePartition.posClauses at hp
    unfold GatePartition.negClauses at hn
    simp only [List.mem_append] at hx hp hn
    rcases hx with ((((h | h) | h) | h) | h)
    · exact hp x (Or.inl h)
    · exact hp x (Or.inr h)
    · exact hn x (Or.inl h)
    · exact hn x (Or.inr h)
    · exact hr x h
  unfold extendGateBve
  by_cases hall : gp.posClauses.all (clauseEvalVal (substUpdate α v false)) = true
  · simp only [hall, ↓reduceIte]
    apply hsat_all
    · intro c hc
      exact (clauseEvalVal_iff _ c).mp (List.all_eq_true.mp hall c hc)
    · intro d hd
      rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
      exact ⟨mkLit v false, hneg d hd, by simp⟩
    · intro r hr
      exact (clause_sat_substUpdate_fresh false (hrfresh r hr)).mpr (hrest r hr)
  · have hallf : gp.posClauses.all (clauseEvalVal (substUpdate α v false)) = false :=
      Bool.eq_false_iff.mpr hall
    simp only [hallf, Bool.false_eq_true, ↓reduceIte]
    have hex : ∃ c ∈ gp.posClauses, clauseEvalVal (substUpdate α v false) c = false :=
      Classical.byContradiction fun hno => hall <| List.all_eq_true.mpr fun c hc => by
        cases hv : clauseEvalVal (substUpdate α v false) c
        · exact absurd ⟨c, hc, hv⟩ hno
        · rfl
    obtain ⟨c0, hc0, hc0f⟩ := hex
    apply hsat_all
    · intro c hc
      rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
      exact ⟨mkLit v true, hpos c hc, by simp⟩
    · intro d hd
      exact sat_neg_of_resolve_sat hc0f (hres c0 hc0 d hd)
    · intro r hr
      exact (clause_sat_substUpdate_fresh true (hrfresh r hr)).mpr (hrest r hr)

/-- Explicit SAT model reconstruction for gate-restricted BVE when non-tautological
`posNonGate × negNonGate` resolvents are entailed by `gateBveClauses v gp`. -/
theorem gateBve_sat_recon {v : Nat} {gp : GatePartition} {α : Nat → Bool}
    (hpart : GatePartValid v gp)
    (hent : GateNonGateEntailed v gp)
    (hα : (cnfOfClauses (gateBveClauses v gp)).Sat α) :
    (cnfOfClauses gp.allClauses).Sat (extendGateBve v gp.posClauses α) := by
  have hα' := (cnf_sat_cnfOfClauses_iff α _).mp hα
  have hrest : ∀ r ∈ gp.rest, (cnfClause r).Sat α := fun r hr =>
    hα' r (by unfold gateBveClauses; simp [hr])
  have hpgn : ∀ r ∈ nonTautResolvents (mkLit v true) gp.posGate gp.negClauses,
      (cnfClause r).Sat α := fun r hr =>
    hα' r (by unfold gateBveClauses; simp [hr])
  have hpngng : ∀ r ∈ nonTautResolvents (mkLit v true) gp.posNonGate gp.negGate,
      (cnfClause r).Sat α := fun r hr =>
    hα' r (by unfold gateBveClauses; simp [hr])
  apply fullBve_sat_recon hpart hrest
  intro c hc d hd
  rcases List.mem_append.mp hc with hcg | hcng
  · exact sat_nonTaut_or_taut hcg hd hpgn
  · rcases List.mem_append.mp hd with hdg | hdng
    · exact sat_nonTaut_or_taut hcng hdg hpngng
    · rw [← clause_sat_dedup_iff]
      by_cases ht : clauseIsTaut (dedupLits (resolveOn (mkLit v true) c d)) = true
      · exact clauseIsTaut_sat ht α
      · exact CNF.entails_clause_def.mp
          (hent c hcng d hdng (Bool.eq_false_iff.mpr ht)) α hα

/-- Semantic/functional gate theorem: `GateFunctional v gp.posGate gp.negGate` implies every
non-tautological `posNonGate × negNonGate` resolvent is entailed by `gateBveClauses v gp`. -/
theorem gateFunctional_entails {v : Nat} {gp : GatePartition}
    (hfunc : GateFunctional v gp.posGate gp.negGate) :
    GateNonGateEntailed v gp := by
  intro c hc d hd
  dsimp only
  intro _
  rw [CNF.entails_clause_def]
  intro α hα
  rw [clause_sat_dedup_iff]
  have hα' := (cnf_sat_cnfOfClauses_iff α _).mp hα
  have hpgn : ∀ r ∈ nonTautResolvents (mkLit v true) gp.posGate gp.negClauses,
      (cnfClause r).Sat α := fun r hr =>
    hα' r (by unfold gateBveClauses; simp [hr])
  have hpngng : ∀ r ∈ nonTautResolvents (mkLit v true) gp.posNonGate gp.negGate,
      (cnfClause r).Sat α := fun r hr =>
    hα' r (by unfold gateBveClauses; simp [hr])
  by_cases hpf : (cnfOfClauses gp.posGate).Sat (substUpdate α v false)
  · have hnt : ¬ (cnfOfClauses gp.negGate).Sat (substUpdate α v true) :=
      fun ht => hfunc α ⟨hpf, ht⟩
    have hex : ∃ dg ∈ gp.negGate, clauseEvalVal (substUpdate α v true) dg = false :=
      Classical.byContradiction fun hno => hnt <| (cnf_sat_cnfOfClauses_iff _ _).mpr fun dg hdg =>
        (clauseEvalVal_iff _ _).mp <| by
          cases hv : clauseEvalVal (substUpdate α v true) dg
          · exact absurd ⟨dg, hdg, hv⟩ hno
          · rfl
    obtain ⟨dg, hdg, hdgf⟩ := hex
    have hres := sat_nonTaut_or_taut hc hdg hpngng
    have hright := false_filter_of_false_update_true hdgf
    obtain ⟨x, hx, hxsat⟩ := List.any_eq_true.mp ((clauseEvalVal_iff α _).mpr hres)
    unfold resolveOn at hx
    rw [List.mem_append, litNeg_mkLit] at hx
    rcases hx with hx1 | hx2
    · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
      exact ⟨x, List.mem_append_left _ hx1, hxsat⟩
    · rw [hright x hx2] at hxsat; cases hxsat
  · have hex : ∃ cg ∈ gp.posGate, clauseEvalVal (substUpdate α v false) cg = false :=
      Classical.byContradiction fun hno => hpf <| (cnf_sat_cnfOfClauses_iff _ _).mpr fun cg hcg =>
        (clauseEvalVal_iff _ _).mp <| by
          cases hv : clauseEvalVal (substUpdate α v false) cg
          · exact absurd ⟨cg, hcg, hv⟩ hno
          · rfl
    obtain ⟨cg, hcg, hcgf⟩ := hex
    have hres := sat_nonTaut_or_taut hcg (List.mem_append_right _ hd) hpgn
    have hleft := false_filter_of_false_update_false hcgf
    obtain ⟨y, hy, hysat⟩ := List.any_eq_true.mp ((clauseEvalVal_iff α _).mpr hres)
    unfold resolveOn at hy
    rw [List.mem_append] at hy
    rcases hy with hy1 | hy2
    · rw [hleft y hy1] at hysat; cases hysat
    · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
      exact ⟨y, List.mem_append_right _ hy2, hysat⟩

/-- Explicit SAT model reconstruction for gate-restricted BVE under a functional gate. -/
theorem gateFunc_bve_sat {v : Nat} {gp : GatePartition} {α : Nat → Bool}
    (hpart : GatePartValid v gp)
    (hfunc : GateFunctional v gp.posGate gp.negGate)
    (hα : (cnfOfClauses (gateBveClauses v gp)).Sat α) :
    (cnfOfClauses gp.allClauses).Sat (extendGateBve v gp.posClauses α) :=
  gateBve_sat_recon hpart (gateFunctional_entails hfunc) hα

/-- Equisatisfiability of gate-restricted BVE under a functional gate. -/
theorem gateFunc_bve_equisat {v : Nat} {gp : GatePartition}
    (hpart : GatePartValid v gp)
    (hfunc : GateFunctional v gp.posGate gp.negGate) :
    (∃ α, (cnfOfClauses gp.allClauses).Sat α) ↔
    (∃ α, (cnfOfClauses (gateBveClauses v gp)).Sat α) :=
  ⟨fun ⟨α, hα⟩ => ⟨α, gateBve_sat_fwd hα⟩,
    fun ⟨α, hα⟩ => ⟨extendGateBve v gp.posClauses α, gateFunc_bve_sat hpart hfunc hα⟩⟩

/-- Blocked-resolvent gate-restricted BVE: if the skipped `posNonGate × negNonGate` resolvents
are eliminated from `fullBveClauses v gp` by a valid `BceReconStack` down to `gateBveClauses v gp`,
composing `extendBceStack` with `extendGateBve` reconstructs a model of `gp.allClauses`. -/
theorem gateBlocked_bve_sat {v : Nat} {gp : GatePartition} {st : BceReconStack} {α : Nat → Bool}
    (hpart : GatePartValid v gp)
    (hval : BceStackValid (fullBveClauses v gp) st)
    (hsub : ∀ c ∈ bceApplyStack st (fullBveClauses v gp), c ∈ gateBveClauses v gp)
    (hα : (cnfOfClauses (gateBveClauses v gp)).Sat α) :
    (cnfOfClauses gp.allClauses).Sat (extendGateBve v gp.posClauses (extendBceStack st α)) := by
  have hsat_sub : (cnfOfClauses (bceApplyStack st (fullBveClauses v gp))).Sat α := by
    rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
    intro c hc; exact hα c (hsub c hc)
  have hfull := (cnf_sat_cnfOfClauses_iff _ _).mp (bceStack_sat_recon hval hsat_sub)
  have hrest : ∀ r ∈ gp.rest, (cnfClause r).Sat (extendBceStack st α) := fun r hr =>
    hfull r (by unfold fullBveClauses gateBveClauses; simp [hr])
  have hpgn : ∀ r ∈ nonTautResolvents (mkLit v true) gp.posGate gp.negClauses,
      (cnfClause r).Sat (extendBceStack st α) := fun r hr =>
    hfull r (by unfold fullBveClauses gateBveClauses; simp [hr])
  have hpngng : ∀ r ∈ nonTautResolvents (mkLit v true) gp.posNonGate gp.negGate,
      (cnfClause r).Sat (extendBceStack st α) := fun r hr =>
    hfull r (by unfold fullBveClauses gateBveClauses; simp [hr])
  have hng : ∀ r ∈ nonTautResolvents (mkLit v true) gp.posNonGate gp.negNonGate,
      (cnfClause r).Sat (extendBceStack st α) := fun r hr =>
    hfull r (by unfold fullBveClauses; simp [hr])
  apply fullBve_sat_recon hpart hrest
  intro c hc d hd
  rcases List.mem_append.mp hc with hcg | hcng
  · exact sat_nonTaut_or_taut hcg hd hpgn
  · rcases List.mem_append.mp hd with hdg | hdng
    · exact sat_nonTaut_or_taut hcng hdg hpngng
    · exact sat_nonTaut_or_taut hcng hdng hng

/-- Pivot elimination guarantee for gate-restricted BVE when positive/negative clauses are
non-tautological on `v`. -/
theorem gateBve_var_elim {v : Nat} {gp : GatePartition}
    (hpart : GatePartValid v gp)
    (hpno : ∀ c ∈ gp.posClauses, mkLit v false ∉ c)
    (hnno : ∀ d ∈ gp.negClauses, mkLit v true ∉ d) :
    VarFreshIn (gateBveClauses v gp) v := by
  have hres_fresh : ∀ c ∈ gp.posClauses, ∀ d ∈ gp.negClauses,
      ∀ x ∈ dedupLits (resolveOn (mkLit v true) c d), litVar x ≠ v := by
    intro c hc d hd x hx hvx
    have hmem := mem_dedupLits_iff.mp hx
    unfold resolveOn at hmem
    rw [List.mem_append] at hmem
    have hveq : litVar x = litVar (mkLit v true) := by simpa using hvx
    rcases hmem with h1 | h2
    · rw [List.mem_filter, bne_iff_ne] at h1
      rcases (litVar_eq_iff x (mkLit v true)).mp hveq with heq | hne
      · exact h1.2 heq
      · rw [litNeg_mkLit] at hne; exact hpno c hc (hne ▸ h1.1)
    · rw [List.mem_filter, bne_iff_ne, litNeg_mkLit] at h2
      rcases (litVar_eq_iff x (mkLit v true)).mp hveq with heq | hne
      · exact hnno d hd (heq ▸ h2.1)
      · rw [litNeg_mkLit] at hne; exact h2.2 hne
  intro r hr x hx
  unfold gateBveClauses at hr
  simp only [List.mem_append] at hr
  rcases hr with (hr1 | hr2) | hr3
  · exact hpart.2.2 r hr1 x hx
  · obtain ⟨c, hc, d, hd, _, rfl⟩ := mem_nonTautResolvents_iff.mp hr2
    exact hres_fresh c (List.mem_append_left _ hc) d hd x hx
  · obtain ⟨c, hc, d, hd, _, rfl⟩ := mem_nonTautResolvents_iff.mp hr3
    exact hres_fresh c (List.mem_append_right _ hc) d (List.mem_append_left _ hd) x hx

/-! ### Concrete Kissat `gates.c` / `definition.c` Gate Instances -/

/-- Kissat equivalence gate `v ↔ l`: `P_g = [[v, ¬l]]`, `N_g = [[¬v, l]]`. -/
theorem equivGate_functional {v l : Nat} (hne : litVar l ≠ v) :
    GateFunctional v [[mkLit v true, litNeg l]] [[mkLit v false, l]] := by
  intro α ⟨hp, hn⟩
  have h1 := (clauseEvalVal_iff _ _).mpr
    ((cnf_sat_cnfOfClauses_iff _ _).mp hp [mkLit v true, litNeg l] (by simp))
  have h2 := (clauseEvalVal_iff _ _).mpr
    ((cnf_sat_cnfOfClauses_iff _ _).mp hn [mkLit v false, l] (by simp))
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    evalLitVal_mkLit, substUpdate_self, evalLitVal_litNeg,
    evalLitVal_substUpdate_ne α _ hne] at h1 h2
  cases hl : evalLitVal α l <;> simp [hl] at h1 h2

/-- Kissat AND gate `v ↔ (x₁ ∧ ... ∧ xₖ)`:
`P_g = [v :: xs.map litNeg]`, `N_g = xs.map (fun x => [¬v, x])`. -/
theorem andGate_functional {v : Nat} {xs : List Nat} (hne : ∀ x ∈ xs, litVar x ≠ v) :
    GateFunctional v [mkLit v true :: xs.map litNeg] (xs.map fun x => [mkLit v false, x]) := by
  intro α ⟨hp, hn⟩
  have h1 := (clauseEvalVal_iff _ _).mpr
    ((cnf_sat_cnfOfClauses_iff _ _).mp hp (mkLit v true :: xs.map litNeg) (by simp))
  simp only [clauseEvalVal, List.any_cons, evalLitVal_mkLit, substUpdate_self] at h1
  have h1' : (xs.map litNeg).any (evalLitVal (substUpdate α v false)) = true := by simpa using h1
  obtain ⟨y, hy, hxf⟩ := List.any_eq_true.mp h1'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have h2 := (clauseEvalVal_iff _ _).mpr
    ((cnf_sat_cnfOfClauses_iff _ _).mp hn [mkLit v false, x] (List.mem_map_of_mem hx))
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    evalLitVal_mkLit, substUpdate_self, evalLitVal_substUpdate_ne α true (hne x hx)] at h2
  rw [evalLitVal_litNeg, evalLitVal_substUpdate_ne α false (hne x hx)] at hxf
  cases h : evalLitVal α x <;> simp [h] at hxf h2

/-- Kissat ITE gate `v ↔ (if c then t else e)`. -/
theorem iteGate_functional {v c t e : Nat}
    (hc : litVar c ≠ v) (ht : litVar t ≠ v) (he : litVar e ≠ v) :
    GateFunctional v
      [[mkLit v true, litNeg c, litNeg t], [mkLit v true, c, litNeg e]]
      [[mkLit v false, litNeg c, t], [mkLit v false, c, e]] := by
  intro α ⟨hp, hn⟩
  have hp' := (cnf_sat_cnfOfClauses_iff _ _).mp hp
  have hn' := (cnf_sat_cnfOfClauses_iff _ _).mp hn
  have h1 := (clauseEvalVal_iff _ _).mpr (hp' [mkLit v true, litNeg c, litNeg t] (by simp))
  have h2 := (clauseEvalVal_iff _ _).mpr (hp' [mkLit v true, c, litNeg e] (by simp))
  have h3 := (clauseEvalVal_iff _ _).mpr (hn' [mkLit v false, litNeg c, t] (by simp))
  have h4 := (clauseEvalVal_iff _ _).mpr (hn' [mkLit v false, c, e] (by simp))
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    evalLitVal_mkLit, substUpdate_self, evalLitVal_litNeg,
    evalLitVal_substUpdate_ne α _ hc, evalLitVal_substUpdate_ne α _ ht,
    evalLitVal_substUpdate_ne α _ he] at h1 h2 h3 h4
  cases hc' : evalLitVal α c <;> cases ht' : evalLitVal α t <;> cases he' : evalLitVal α e <;>
    simp_all

/-- Kissat binary XOR gate `v ↔ (a ⊕ b)`. -/
theorem xorGate_functional {v a b : Nat} (ha : litVar a ≠ v) (hb : litVar b ≠ v) :
    GateFunctional v
      [[mkLit v true, litNeg a, b], [mkLit v true, a, litNeg b]]
      [[mkLit v false, a, b], [mkLit v false, litNeg a, litNeg b]] := by
  intro α ⟨hp, hn⟩
  have hp' := (cnf_sat_cnfOfClauses_iff _ _).mp hp
  have hn' := (cnf_sat_cnfOfClauses_iff _ _).mp hn
  have h1 := (clauseEvalVal_iff _ _).mpr (hp' [mkLit v true, litNeg a, b] (by simp))
  have h2 := (clauseEvalVal_iff _ _).mpr (hp' [mkLit v true, a, litNeg b] (by simp))
  have h3 := (clauseEvalVal_iff _ _).mpr (hn' [mkLit v false, a, b] (by simp))
  have h4 := (clauseEvalVal_iff _ _).mpr (hn' [mkLit v false, litNeg a, litNeg b] (by simp))
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    evalLitVal_mkLit, substUpdate_self, evalLitVal_litNeg,
    evalLitVal_substUpdate_ne α _ ha, evalLitVal_substUpdate_ne α _ hb] at h1 h2 h3 h4
  cases ha' : evalLitVal α a <;> cases hb' : evalLitVal α b <;> simp_all

/-- Kissat `definition.c` semantic gate check: if stripping `v` from `posGate` and `¬v` from
`negGate` yields an UNSAT core, then `(posGate, negGate)` is a functional gate for `v`. -/
theorem defGate_functional {v : Nat} {posGate negGate : List (List Nat)}
    (hpno : ∀ c ∈ posGate, mkLit v false ∉ c)
    (hnno : ∀ d ∈ negGate, mkLit v true ∉ d)
    (hcore : (cnfOfClauses (posGate.map (·.filter (· != mkLit v true)) ++
        negGate.map (·.filter (· != mkLit v false)))).Unsat) :
    GateFunctional v posGate negGate := by
  intro α ⟨hp, hn⟩
  refine CNF.unsat_iff_not_sat.mp hcore α ?_
  rw [cnf_sat_cnfOfClauses_iff]
  intro c hc
  rw [List.mem_append, List.mem_map, List.mem_map] at hc
  rcases hc with ⟨c0, hc0, rfl⟩ | ⟨d0, hd0, rfl⟩
  · have hsat := (clauseEvalVal_iff _ _).mpr ((cnf_sat_cnfOfClauses_iff _ _).mp hp c0 hc0)
    obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp hsat
    have hxne : x ≠ mkLit v true := by
      rintro rfl; simp at hxt
    have hvar : litVar x ≠ v := by
      intro hv
      have hveq : litVar x = litVar (mkLit v true) := by simpa using hv
      rcases (litVar_eq_iff x (mkLit v true)).mp hveq with h1 | h2
      · exact hxne h1
      · rw [litNeg_mkLit] at h2; exact hpno c0 hc0 (h2 ▸ hx)
    rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
    exact ⟨x, List.mem_filter.mpr ⟨hx, bne_iff_ne.mpr hxne⟩,
      by rwa [evalLitVal_substUpdate_ne α false hvar] at hxt⟩
  · have hsat := (clauseEvalVal_iff _ _).mpr ((cnf_sat_cnfOfClauses_iff _ _).mp hn d0 hd0)
    obtain ⟨y, hy, hyt⟩ := List.any_eq_true.mp hsat
    have hyne : y ≠ mkLit v false := by
      rintro rfl; simp at hyt
    have hvar : litVar y ≠ v := by
      intro hv
      have hveq : litVar y = litVar (mkLit v false) := by simpa using hv
      rcases (litVar_eq_iff y (mkLit v false)).mp hveq with h1 | h2
      · exact hyne h1
      · rw [litNeg_mkLit] at h2; exact hnno d0 hd0 (h2 ▸ hy)
    rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
    exact ⟨y, List.mem_filter.mpr ⟨hy, bne_iff_ne.mpr hyne⟩,
      by rwa [evalLitVal_substUpdate_ne α true hvar] at hyt⟩

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
def bvaDivClauses (z : Nat) (L : List Nat) : List (List Nat) :=
  L.map fun f => [mkLit z true, f]

/-- Kissat `factor.c` quotient clauses `[¬z] ++ qⱼ` for each quotient subclause `qⱼ ∈ Q`. -/
def bvaQuotClauses (z : Nat) (Q : List (List Nat)) : List (List Nat) :=
  Q.map fun q => mkLit z false :: q

/-- Order-independent membership test: `true` iff `c` is subsumed by some product clause
`f :: q` with `f ∈ L` and `q ∈ Q`. -/
def bvaIsFactored (L : List Nat) (Q : List (List Nat)) (c : List Nat) : Bool :=
  L.any fun f => c.contains f && Q.any fun q => q.all fun x => c.contains x

/-- Kissat `factor.c` Bounded Variable Addition / Factorization transform: introduces fresh `z`,
adds divider clauses `{[z, f] | f ∈ L}` and quotient clauses `{¬z :: q | q ∈ Q}`, and deletes
every clause subsumed by a factored product clause `f :: q`. -/
def bvaFactorClauses (z : Nat) (L : List Nat) (Q : List (List Nat))
    (cs : List (List Nat)) : List (List Nat) :=
  bvaDivClauses z L ++ bvaQuotClauses z Q ++ cs.filter (fun c => !bvaIsFactored L Q c)

/-- Forward witness assignment for fresh variable `z` introduced by `bvaFactorClauses`:
`z := false` if every divider literal `f ∈ L` is already true under `α`, else `z := true`. -/
def bvaExtend (z : Nat) (L : List Nat) (α : Nat → Bool) : Nat → Bool :=
  substUpdate α z (!(L.all (evalLitVal α)))

/-- Validity side-condition for Bounded Variable Addition / Factorization (`factor.c`). -/
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
def tierBStepApply (step : TierBStep) (cs : List (List Nat)) : List (List Nat) :=
  match step with
  | .subst v l => substClauses v l cs
  | .bce _ c => cs.erase c
  | .gateBve v gp => gateBveClauses v gp
  | .bvaFactor z L Q => bvaFactorClauses z L Q cs

/-- Reconstruct a model across a single Tier-B step. -/
def tierBStepExtend (step : TierBStep) (α : Nat → Bool) : Nat → Bool :=
  match step with
  | .subst v l => substExtend v l α
  | .bce l c => extendBce l c α
  | .gateBve v gp => extendGateBve v gp.posClauses α
  | .bvaFactor _ _ _ => α

/-- Semantic validity of one Tier-B step on clause list `cs`. -/
def TierBStepValid (cs : List (List Nat)) : TierBStep → Prop
  | .subst v l => litVar l ≠ v ∧ EquivEntailed (cnfOfClauses cs) v l
  | .bce l c => c ∈ cs ∧ IsBlockedOn (cs.erase c) c l
  | .gateBve v gp =>
    (∀ α, (cnfOfClauses gp.allClauses).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
    GatePartValid v gp ∧
    GateNonGateEntailed v gp
  | .bvaFactor z L Q => BvaValid z L Q cs

/-- Apply a multi-step Tier-B trace left-to-right. -/
def tierBTraceApply : TierBTrace → List (List Nat) → List (List Nat)
  | [], cs => cs
  | s :: rest, cs => tierBTraceApply rest (tierBStepApply s cs)

/-- Reconstruct a model across a multi-step Tier-B trace right-to-left (`foldr`). -/
def tierBTraceExtend (tr : TierBTrace) (α : Nat → Bool) : Nat → Bool :=
  tr.foldr tierBStepExtend α

/-- Inductive validity of a multi-step Tier-B trace on `cs`. -/
def TierBTraceValid : List (List Nat) → TierBTrace → Prop
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
def extendBceArr (l : Nat) (c : List Nat) (σ : Array Bool) : Array Bool :=
  if evalClause σ c then σ else arraySetPad σ (litVar l) (!(litSign l)) false

/-- Executable BCE stack reconstruction on `Array Bool`. -/
def extendBceStackArr (st : BceReconStack) (σ : Array Bool) : Array Bool :=
  st.foldr (fun e acc => extendBceArr e.lit e.clause acc) σ

/-- Executable Gate-BVE witness reconstruction on `Array Bool`. -/
def extendGateBveArr (v : Nat) (posClauses : List (List Nat)) (σ : Array Bool) : Array Bool :=
  let σF := arraySetPad σ v false false
  if posClauses.all (evalClause σF) then σF else arraySetPad σ v true false

/-- Executable single-step Tier-B reconstruction on `Array Bool`. -/
def tierBStepExtendArr (step : TierBStep) (σ : Array Bool) : Array Bool :=
  match step with
  | .subst v l => substExtendArr v l σ
  | .bce l c => extendBceArr l c σ
  | .gateBve v gp => extendGateBveArr v gp.posClauses σ
  | .bvaFactor _ _ _ => σ

/-- Executable multi-step Tier-B reconstruction on `Array Bool`. -/
def tierBTraceExtendArr (tr : TierBTrace) (σ : Array Bool) : Array Bool :=
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

end LeanQbe.T.Examples.Kissat
