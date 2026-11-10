module

public import Kraken.Bedrock2.Test.LratTrimSpec
public import Kraken.Bedrock2.Test.LratTrimRupProof
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
import all Std.Sat.CNF.Entails
import all Std.Tactic.BVDecide.LRAT.Internal.Basic
import all Std.Tactic.BVDecide.LRAT.Internal.Rup
import all Std.Tactic.BVDecide.LRAT.Internal.Add

@[expose] public section

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace Kraken.Bedrock2.Test

/-! ## 1. `kernelState` Field Accessor & Store Lemmas -/

@[simp] theorem length_kernelFields_toList (k : KernelFields) :
    k.toList.length = 20 := rfl

theorem kernelState_load_field {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R)
    (i : Nat) (hi : i < 20) :
    load? .eight m (st + BitVec.ofNat 64 (8 * i)) = some (k.toList[i]'(by simpa using hi)) := by
  unfold kernelState at hsep
  exact load_word8Array_elem (by simpa using hi) hsep

theorem kernelState_load_used_begin {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m st = some k.used_begin := by
  have h := kernelState_load_field hsep 0 (by decide)
  simpa [KernelFields.toList] using h

theorem kernelState_load_antecedents_begin {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 8#64) = some k.antecedents_begin :=
  kernelState_load_field hsep 1 (by decide)

theorem kernelState_load_literals_begin {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 16#64) = some k.literals_begin :=
  kernelState_load_field hsep 2 (by decide)

theorem kernelState_load_empty_clause {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 64#64) = some k.empty_clause :=
  kernelState_load_field hsep 8 (by decide)

theorem kernelState_load_first_proof_id {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 72#64) = some k.first_proof_id :=
  kernelState_load_field hsep 9 (by decide)

theorem kernelState_load_strict {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 80#64) = some k.strict :=
  kernelState_load_field hsep 10 (by decide)

theorem kernelState_load_trimming {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 88#64) = some k.trimming :=
  kernelState_load_field hsep 11 (by decide)

theorem kernelState_load_checking {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 96#64) = some k.checking :=
  kernelState_load_field hsep 12 (by decide)

theorem kernelState_load_forward {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 104#64) = some k.forward :=
  kernelState_load_field hsep 13 (by decide)

theorem kernelState_load_stat_chk_total {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 128#64) = some k.stat_chk_total :=
  kernelState_load_field hsep 16 (by decide)

theorem kernelState_load_stat_chk_empty {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m (st + 136#64) = some k.stat_chk_empty :=
  kernelState_load_field hsep 17 (by decide)

theorem kernelState_store_stat_chk_total {e : Env} {B : Nat} {ea ev : Expr}
    {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {st v : BitVec 64} {k : KernelFields} {R : Mem 64 → Prop}
    (ha : ea.eval m l = some (st + 128#64)) (hv : ev.eval m l = some v)
    (hsep : m =⋆ kernelState st k ⋆ R)
    (hpost : ∀ m', (m' =⋆ kernelState st { k with stat_chk_total := v } ⋆ R) → post t m' l) :
    Exec lratFailExt e B (.store .eight ea ev) t m l post :=
  store_word8Array_elem (i := 16) (by simp) ha hv hsep hpost

theorem kernelState_store_stat_chk_empty {e : Env} {B : Nat} {ea ev : Expr}
    {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {st v : BitVec 64} {k : KernelFields} {R : Mem 64 → Prop}
    (ha : ea.eval m l = some (st + 136#64)) (hv : ev.eval m l = some v)
    (hsep : m =⋆ kernelState st k ⋆ R)
    (hpost : ∀ m', (m' =⋆ kernelState st { k with stat_chk_empty := v } ⋆ R) → post t m' l) :
    Exec lratFailExt e B (.store .eight ea ev) t m l post :=
  store_word8Array_elem (i := 17) (by simp) ha hv hsep hpost

/-! ## 2. Semantic State (`stateSkip`, `stepState`, `stateAt`) & Entailment Lemmas -/

/-- Skip a proof step (when `trimming != 0` and `used[id] == 0`) by pushing `none` onto `s.formula`,
keeping 1-based clause indices aligned while leaving `s.toCNF` unchanged. -/
def stateSkip (s : State) : State :=
  { s with formula := s.formula.push none }

@[simp] theorem toCNF_stateSkip (s : State) :
    (stateSkip s).toCNF = s.toCNF := by
  simp [stateSkip, State.toCNF]

@[simp] theorem formula_size_stateSkip (s : State) :
    (stateSkip s).formula.size = s.formula.size + 1 := by
  simp [stateSkip]

@[simp] theorem formula_size_add (s : State) (c : CNF.Clause Nat) :
    (s.add c).formula.size = s.formula.size + 1 := by
  simp [State.add]

@[simp] theorem formula_size_ofCNF (f : CNF Nat) :
    (State.ofCNF f).formula.size = f.clauses.size := by
  simp [State.ofCNF]

@[simp] theorem toCNF_ofCNF (f : CNF Nat) :
    (State.ofCNF f).toCNF = f := by
  cases f
  simp only [State.ofCNF, State.toCNF, CNF.mk.injEq, ← Array.toList_inj,
    Array.toList_filterMap, Array.toList_map, List.filterMap_map]
  exact List.filterMap_some

/-- One step of `br_check_proof` at proof clause `c`: either add `c` (when checked) or skip it. -/
def stepState (s : State) (used : Bool) (c : CNF.Clause Nat) : State :=
  if used then s.add c else stateSkip s

@[simp] theorem formula_size_stepState (s : State) (used : Bool) (c : CNF.Clause Nat) :
    (stepState s used c).formula.size = s.formula.size + 1 := by
  cases used <;> simp [stepState]

theorem entails_stepState_of_used {cnf₀ : CNF Nat} {s : State} {c : CNF.Clause Nat}
    (hent : CNF.Entails cnf₀ s.toCNF) (hc : CNF.EntailsClause s.toCNF c) :
    CNF.Entails cnf₀ (stepState s true c).toCNF :=
  CNF.entails_trans hent (State.entails_add_of_entails_clause hc)

theorem entails_stepState_of_unused {cnf₀ : CNF Nat} {s : State} (c : CNF.Clause Nat)
    (hent : CNF.Entails cnf₀ s.toCNF) :
    CNF.Entails cnf₀ (stepState s false c).toCNF := by
  simpa [stepState] using hent

/-- Whether step `id` is checked by `br_check_proof`: either `trimming = 0` (`used_where = -1`)
or `usedWords[id] ≠ 0`. -/
def isStepUsed (trimming : BitVec 64) (usedWords : List (BitVec 64)) (id : Nat) : Bool :=
  (trimming == 0) || (usedWords.getD id 0 != 0)

theorem isStepUsed_eq_true_iff {trimming : BitVec 64} {usedWords : List (BitVec 64)} {id : Nat}
    (hid : id < usedWords.length) :
    isStepUsed trimming usedWords id = true ↔ (trimming = 0 ∨ usedWords[id] ≠ 0) := by
  simp [isStepUsed, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hid]

/-- Clause at 1-based clause ID `id` in `clauses` (defaulting to `.empty`). -/
def clauseAt (clauses : List (CNF.Clause Nat)) (id : Nat) : CNF.Clause Nat :=
  clauses.getD id .empty

/-- The `Internal.State` after processing `n` proof clauses (`first_proof_id .. first_proof_id + n - 1`). -/
def stateAt (cnf₀ : CNF Nat) (first_proof_id : Nat) (trimming : BitVec 64)
    (usedWords : List (BitVec 64)) (clauses : List (CNF.Clause Nat)) : Nat → State
  | 0 => State.ofCNF cnf₀
  | n + 1 =>
    let id := first_proof_id + n
    stepState (stateAt cnf₀ first_proof_id trimming usedWords clauses n)
      (isStepUsed trimming usedWords id) (clauseAt clauses id)

@[simp] theorem stateAt_zero (cnf₀ : CNF Nat) (first_proof_id : Nat) (trimming : BitVec 64)
    (usedWords : List (BitVec 64)) (clauses : List (CNF.Clause Nat)) :
    stateAt cnf₀ first_proof_id trimming usedWords clauses 0 = State.ofCNF cnf₀ := rfl

@[simp] theorem stateAt_succ (cnf₀ : CNF Nat) (first_proof_id : Nat) (trimming : BitVec 64)
    (usedWords : List (BitVec 64)) (clauses : List (CNF.Clause Nat)) (n : Nat) :
    stateAt cnf₀ first_proof_id trimming usedWords clauses (n + 1) =
      stepState (stateAt cnf₀ first_proof_id trimming usedWords clauses n)
        (isStepUsed trimming usedWords (first_proof_id + n))
        (clauseAt clauses (first_proof_id + n)) := rfl

theorem entails_stateAt_zero (cnf₀ : CNF Nat) (first_proof_id : Nat) (trimming : BitVec 64)
    (usedWords : List (BitVec 64)) (clauses : List (CNF.Clause Nat)) :
    CNF.Entails cnf₀ (stateAt cnf₀ first_proof_id trimming usedWords clauses 0).toCNF := by
  rw [stateAt_zero, toCNF_ofCNF]

@[simp] theorem formula_size_stateAt (cnf₀ : CNF Nat) (first_proof_id : Nat) (trimming : BitVec 64)
    (usedWords : List (BitVec 64)) (clauses : List (CNF.Clause Nat)) (n : Nat) :
    (stateAt cnf₀ first_proof_id trimming usedWords clauses n).formula.size =
      cnf₀.clauses.size + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [stateAt_succ, ih, Nat.add_assoc]

theorem formula_stepState (s : State) (used : Bool) (c : CNF.Clause Nat) :
    (stepState s used c).formula = s.formula.push (if used then some c else none) := by
  cases used <;> rfl

theorem getElem?_formula_stateAt_of_lt (cnf₀ : CNF Nat) (first_proof_id : Nat) (trimming : BitVec 64)
    (usedWords : List (BitVec 64)) (clauses : List (CNF.Clause Nat)) (n : Nat)
    {j : Nat} (hj : j < cnf₀.clauses.size) :
    (stateAt cnf₀ first_proof_id trimming usedWords clauses n).formula[j]? =
      some (some cnf₀.clauses[j]) := by
  induction n with
  | zero =>
    simp [stateAt_zero, State.ofCNF, hj]
  | succ n ih =>
    rw [stateAt_succ, formula_stepState, Array.getElem?_push]
    rw [ite_eq_right_iff.mpr (by rw [formula_size_stateAt]; omega), ih]

theorem getElem?_formula_stateAt_of_ge (cnf₀ : CNF Nat) (first_proof_id : Nat) (trimming : BitVec 64)
    (usedWords : List (BitVec 64)) (clauses : List (CNF.Clause Nat)) (n : Nat)
    {k : Nat} (hk : k < n) :
    (stateAt cnf₀ first_proof_id trimming usedWords clauses n).formula[cnf₀.clauses.size + k]? =
      some (if isStepUsed trimming usedWords (first_proof_id + k) then
        some (clauseAt clauses (first_proof_id + k))
      else none) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [stateAt_succ, formula_stepState, Array.getElem?_push, formula_size_stateAt]
    by_cases hkn : k = n
    · subst hkn
      simp
    · rw [ite_eq_right_iff.mpr (by omega), ih (by omega)]

theorem mem_toCNF_of_getElem?_formula {s : State} {j : Nat} {c : CNF.Clause Nat}
    (h : s.formula[j]? = some (some c)) :
    c ∈ s.toCNF.clauses := by
  simp only [State.toCNF]
  rw [← Array.mem_toList_iff, Array.toList_filterMap, List.mem_filterMap]
  refine ⟨some c, ?_, rfl⟩
  rw [Array.mem_toList_iff]
  exact Array.mem_of_getElem? h

theorem entailsClause_toCNF_of_getElem?_formula {s : State} {j : Nat} {c : CNF.Clause Nat}
    (h : s.formula[j]? = some (some c)) :
    CNF.EntailsClause s.toCNF c := by
  rw [CNF.entails_clause_def]
  intro a hsat
  exact CNF.sat_of_mem hsat (CNF.Internal.mem_iff.mpr (mem_toCNF_of_getElem?_formula h))

theorem unsat_of_entails_and_entails_empty {cnf₀ f : CNF Nat} {c : CNF.Clause Nat}
    (hent : CNF.Entails cnf₀ f) (hc : CNF.EntailsClause f c) (hempty : c = .empty) :
    cnf₀.Unsat := by
  subst hempty
  have hf_unsat : f.Unsat := CNF.unsat_of_entails_clause_unsat CNF.Clause.unsat_empty hc
  exact CNF.unsat_of_entails_unsat hf_unsat hent

/-! ## 3. Bedrock2 `call` Specification for `br_check_clause` -/

/-- Effect of `br_check_clause`'s header on `KernelFields` statistics (`stat_chk_total` and `stat_chk_empty`). -/
def KernelFields.bumpCheckStats (k : KernelFields) (firstLitWord : BitVec 64) : KernelFields :=
  { k with
    stat_chk_total := k.stat_chk_total + 1
    stat_chk_empty :=
      if (firstLitWord &&& 0xffffffff#64) == 0 then k.stat_chk_empty + 1 else k.stat_chk_empty }

/-- Two `KernelFields` records share the same configuration and pointer fields (differing only in `stat_*` or `trail_end`). -/
structure KernelFields.SameConfig (k k₀ : KernelFields) : Prop where
  used_begin : k.used_begin = k₀.used_begin
  antecedents_begin : k.antecedents_begin = k₀.antecedents_begin
  literals_begin : k.literals_begin = k₀.literals_begin
  values_begin : k.values_begin = k₀.values_begin
  marks_begin : k.marks_begin = k₀.marks_begin
  trail_begin : k.trail_begin = k₀.trail_begin
  work_begin : k.work_begin = k₀.work_begin
  empty_clause : k.empty_clause = k₀.empty_clause
  first_proof_id : k.first_proof_id = k₀.first_proof_id
  strict : k.strict = k₀.strict
  trimming : k.trimming = k₀.trimming
  checking : k.checking = k₀.checking
  forward : k.forward = k₀.forward

theorem KernelFields.SameConfig.refl (k : KernelFields) : k.SameConfig k where
  used_begin := rfl
  antecedents_begin := rfl
  literals_begin := rfl
  values_begin := rfl
  marks_begin := rfl
  trail_begin := rfl
  work_begin := rfl
  empty_clause := rfl
  first_proof_id := rfl
  strict := rfl
  trimming := rfl
  checking := rfl
  forward := rfl

theorem KernelFields.SameConfig.bumpCheckStats {k k₀ : KernelFields} (h : k.SameConfig k₀)
    (w₀ : BitVec 64) : (k.bumpCheckStats w₀).SameConfig k₀ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13⟩

/-- Specification of `br_check_clause`: increments `stat_chk_total` (and `stat_chk_empty` if
`load4(literals) == 0`), reads `k.strict`, and dispatches to `br_check_clause_non_strictly_by_propagation`
when `k.strict = 0` or `br_check_clause_strictly_by_resolution` when `k.strict ≠ 0`. -/
theorem call_br_check_clause {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64}
    {st id literals antecedents w₀ : BitVec 64} {k : KernelFields} {R : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hfn : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hsep : m =⋆ kernelState st k ⋆ (int4 literals w₀ ⋆ R))
    (hcall : ∀ m', (m' =⋆ kernelState st (k.bumpCheckStats w₀) ⋆ (int4 literals w₀ ⋆ R)) →
      if k.strict = 0 then
        call lratFailExt e B br_check_clause_non_strictly_by_propagation.1 t m'
          [st, id, literals, antecedents] (fun t' m'' rets => rets = [] ∧ post t' m'' [])
      else
        call lratFailExt e B br_check_clause_strictly_by_resolution.1 t m'
          [st, id, literals, antecedents] (fun t' m'' rets => rets = [] ∧ post t' m'' [])) :
    call lratFailExt e B br_check_clause.1 t m [st, id, literals, antecedents] post := by
  let l₀ : Locals 64 :=
    insertMany ∅ (br_check_clause.2.params.zip [st, id, literals, antecedents])
  refine call.of_body hfn rfl ?_
  change Exec lratFailExt e B br_check_clause.2.body t m l₀ (fun t' m' l' =>
    ∃ rets, getMany l' [] = some rets ∧ post t' m' rets)
  dsimp only [br_check_clause, Func.body]
  have hst : l₀["st"]? = some st := by
    simp [l₀, br_check_clause, insertMany_cons, insertMany_nil]
  have hlits : l₀["literals"]? = some literals := by
    simp [l₀, br_check_clause, insertMany_cons, insertMany_nil]
  -- Step 1: store8(st + 128, load8(st + 128) + 1)
  refine Exec.seq_cps ?_
  refine kernelState_store_stat_chk_total (v := k.stat_chk_total + 1) ?_ ?_ hsep (fun m1 hm1 => ?_)
  · simp [Expr.eval, hst, interpBinop]
  · simp [Expr.eval, hst, interpBinop]
    rw [kernelState_load_stat_chk_total hsep]
    rfl
  let k1 : KernelFields := { k with stat_chk_total := k.stat_chk_total + 1 }
  -- Step 2: if load4(literals) == 0 { store8(st + 136, load8(st + 136) + 1) }
  refine Exec.seq_cps (c2 := .seq _ _) ?_
  refine Exec.weaken (post1 := fun t2 m2 l2 => t2 = t ∧ l2 = l₀ ∧
    (m2 =⋆ kernelState st (k.bumpCheckStats w₀) ⋆ (int4 literals w₀ ⋆ R))) ?_ (fun t2 m2 l2 h2 => ?_)
  · have hm1_int4 : m1 =⋆ int4 literals w₀ ⋆ (kernelState st k1 ⋆ R) := by
      have h := hm1
      rw [← sep_assoc, sep_comm (kernelState st k1), sep_assoc] at h
      exact h
    have hload4 := load_int4_raw hm1_int4
    refine Exec.cond_cps (v := if (w₀ &&& 0xffffffff#64) = 0 then 1 else 0) ?_ (fun hnz => ?_) (fun hz => ?_)
    · simp [Expr.eval, hlits, interpBinop]
      rw [hload4]
      rfl
    · have h0 : (w₀ &&& 0xffffffff#64) = 0#64 := by
        split at hnz
        · assumption
        · contradiction
      refine kernelState_store_stat_chk_empty (v := k1.stat_chk_empty + 1) ?_ ?_ hm1 (fun m2 hm2 => ⟨rfl, rfl, ?_⟩)
      · simp [Expr.eval, hst, interpBinop]
      · simp [Expr.eval, hst, interpBinop]
        rw [kernelState_load_stat_chk_empty hm1]
        rfl
      · simpa [KernelFields.bumpCheckStats, k1, h0] using hm2
    · have h0 : (w₀ &&& 0xffffffff#64) ≠ 0#64 := by
        split at hz
        · contradiction
        · assumption
      refine .skip _ _ _ _ _ ⟨rfl, rfl, ?_⟩
      simpa [KernelFields.bumpCheckStats, k1, h0] using hm1
  · rcases h2 with ⟨rfl, rfl, hm2⟩
    let k2 := k.bumpCheckStats w₀
    -- Step 3: strict = load8(st + 80)
    refine Exec.seq_cps ?_
    refine Exec.set_cps (v := k2.strict) ?_ ?_
    · simp [Expr.eval, hst, interpBinop]
      exact kernelState_load_strict hm2
    let l₃ := l₀.insert "strict" k2.strict
    have hargs : evalArgs m2 l₃ [.var "st", .var "id", .var "literals", .var "antecedents"] =
        some [st, id, literals, antecedents] := by
      simp [evalArgs, l₃, l₀, Expr.eval, br_check_clause, insertMany_cons, insertMany_nil]
    have hk2_strict : k2.strict = k.strict := rfl
    have hl3_strict : (Expr.var "strict").eval m2 l₃ = some k.strict := by
      simp [l₃, Expr.eval, hk2_strict]
    -- Step 4: if strict { br_check_clause_strictly_by_resolution(...) } else { br_check_clause_non_strictly_by_propagation(...) }
    have hcall2 := hcall m2 hm2
    refine Exec.cond_cps hl3_strict (fun hnz => ?_) (fun hz => ?_)
    · rw [ite_eq_right_iff.mpr fun h => False.elim (hnz h)] at hcall2
      refine Exec.call_cps hargs (call.weaken hcall2 ?_)
      rintro t' m' rets ⟨rfl, hpost⟩
      exact ⟨l₃, putManyZip_nil l₃, [], rfl, hpost⟩
    · rw [ite_eq_left_iff.mpr fun h => False.elim (h hz)] at hcall2
      refine Exec.call_cps hargs (call.weaken hcall2 ?_)
      rintro t' m' rets ⟨rfl, hpost⟩
      exact ⟨l₃, putManyZip_nil l₃, [], rfl, hpost⟩

theorem zeroTermInts_split_head (p : BitVec 64) (xs : List (BitVec 64)) :
    ZeroTermInts p xs =
      (int4 p ((xs ++ [0])[0]'(by simp)) ⋆ int4Array (p + 4) (xs ++ [0]).tail) := by
  cases xs with
  | nil => simp [ZeroTermInts]
  | cons x xs => rfl

/-- Variant of `call_br_check_clause` framed directly with `ZeroTermInts literals clits`. -/
theorem call_br_check_clause_zeroTerm {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64}
    {st id literals antecedents : BitVec 64} {clits : List (BitVec 64)}
    {k : KernelFields} {R : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hfn : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hsep : m =⋆ kernelState st k ⋆ (ZeroTermInts literals clits ⋆ R))
    (hcall : ∀ m', (m' =⋆ kernelState st (k.bumpCheckStats ((clits ++ [0])[0]'(by simp))) ⋆
        (ZeroTermInts literals clits ⋆ R)) →
      if k.strict = 0 then
        call lratFailExt e B br_check_clause_non_strictly_by_propagation.1 t m'
          [st, id, literals, antecedents] (fun t' m'' rets => rets = [] ∧ post t' m'' [])
      else
        call lratFailExt e B br_check_clause_strictly_by_resolution.1 t m'
          [st, id, literals, antecedents] (fun t' m'' rets => rets = [] ∧ post t' m'' [])) :
    call lratFailExt e B br_check_clause.1 t m [st, id, literals, antecedents] post := by
  rw [zeroTermInts_split_head literals clits, sep_assoc (int4 literals _)] at hsep
  refine call_br_check_clause hfn hsep (fun m' hm' => ?_)
  rw [← sep_assoc (int4 literals _), ← zeroTermInts_split_head literals clits] at hm'
  exact hcall m' hm'

/-! ## 4. BitVec Arithmetic Helpers for `br_check_proof` -/

theorem sext32_of_isInt32 {v : BitVec 64} (hv : IsInt32 v) :
    (v <<< shamt 32#64).sshiftRight (shamt 32#64) = v := by
  have hs : shamt 32#64 = 32 := by decide
  rw [hs]
  exact hv

theorem isInt32_of_toNat_lt {v : BitVec 64} (hv : v.toNat < 2 ^ 31) : IsInt32 v := by
  unfold IsInt32
  have hlt : v < 0x80000000#64 := by simpa [BitVec.lt_def] using hv
  revert hlt
  bv_decide

theorem slt_iff_toNat_lt {x y : BitVec 64} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    x.slt y = decide (x.toNat < y.toNat) := by
  have hx' : x < 0x80000000#64 := by simpa [BitVec.lt_def] using hx
  have hy' : y < 0x80000000#64 := by simpa [BitVec.lt_def] using hy
  have hiff : x.slt y = true ↔ x < y := by
    revert hx' hy'
    bv_decide
  rw [BitVec.lt_def] at hiff
  cases h : x.slt y <;> simp_all

theorem toNat_add_one_of_lt {id : BitVec 64} (hid : id.toNat + 1 < 2 ^ 31) :
    (id + 1#64).toNat = id.toNat + 1 := by
  rw [BitVec.toNat_add]
  change (id.toNat + 1) % 2 ^ 64 = id.toNat + 1
  exact Nat.mod_eq_of_lt (by omega)

theorem slu_two_eq_ofNat {id : BitVec 64} (hid : id.toNat < 2 ^ 31) :
    id <<< shamt 2#64 = BitVec.ofNat 64 (4 * id.toNat) := by
  change interpBinop .slu id 2#64 = BitVec.ofNat 64 (4 * id.toNat)
  apply BitVec.eq_of_toNat_eq
  rw [unsigned_slu_shamtZ (Or.inr rfl) id (n := 2) (by decide), BitVec.toNat_ofNat]
  have : id.toNat <<< 2 = 4 * id.toNat := by omega
  rw [this, Nat.mod_eq_of_lt (by omega)]

theorem slu_three_eq_ofNat {id : BitVec 64} (hid : id.toNat < 2 ^ 31) :
    id <<< shamt 3#64 = BitVec.ofNat 64 (8 * id.toNat) := by
  change interpBinop .slu id 3#64 = BitVec.ofNat 64 (8 * id.toNat)
  apply BitVec.eq_of_toNat_eq
  rw [unsigned_slu_shamtZ (Or.inr rfl) id (n := 3) (by decide), BitVec.toNat_ofNat]
  have : id.toNat <<< 3 = 8 * id.toNat := by omega
  rw [this, Nat.mod_eq_of_lt (by omega)]

/-! ## 5. Outer Loop & Top-Level Soundness of `br_check_proof` -/

/-- The outer `while (empty_clause .< id) == 0` command in `br_check_proof`. -/
def checkProofLoopCmd : Cmd :=
  Cmd.while (Expr.op .eq (Expr.op .lts (Expr.var "empty_clause") (Expr.var "id")) (Expr.literal 0))
    ((Cmd.cond (Expr.var "trimming")
        (Cmd.set "used_where"
          (Expr.op .srs
            (Expr.op .slu
              (Expr.load .four
                (Expr.op .add (Expr.var "used_begin") (Expr.op .slu (Expr.var "id") (Expr.literal 2))))
              (Expr.literal 32))
            (Expr.literal 32)))
        (Cmd.set "used_where" (Expr.op1 .opp (Expr.literal 1)))).seq
      ((Cmd.cond (Expr.var "used_where")
          ((Cmd.set "l"
              (Expr.load .eight
                (Expr.op .add (Expr.var "literals_begin")
                  (Expr.op .slu (Expr.var "id") (Expr.literal 3))))).seq
            ((Cmd.set "a"
                (Expr.load .eight
                  (Expr.op .add (Expr.var "antecedents_begin")
                    (Expr.op .slu (Expr.var "id") (Expr.literal 3))))).seq
              (Cmd.call [] "br_check_clause" [Expr.var "st", Expr.var "id", Expr.var "l", Expr.var "a"])))
          Cmd.skip).seq
        (Cmd.set "id" (Expr.op .add (Expr.var "id") (Expr.literal 1)))))

/-- Loop invariant for `checkProofLoopCmd` at measure `v = empty_clause.toNat + 1 - id.toNat`. -/
def CheckProofLoopInv (st : BitVec 64) (k₀ : KernelFields)
    (usedWords : List (BitVec 64))
    (cnf₀ : CNF Nat) (clauses : List (CNF.Clause Nat))
    (InvMem : KernelFields → Mem 64 → Prop)
    (t₀ : Trace 64) (v : Nat) (t : Trace 64) (m : Mem 64) (l : Locals 64) : Prop :=
  ∃ (id : BitVec 64) (k : KernelFields),
    v = k₀.empty_clause.toNat + 1 - id.toNat ∧
    k₀.first_proof_id.toNat ≤ id.toNat ∧
    id.toNat ≤ k₀.empty_clause.toNat + 1 ∧
    t₀ = t ∧
    l["st"]? = some st ∧
    l["empty_clause"]? = some k₀.empty_clause ∧
    l["first_proof_id"]? = some k₀.first_proof_id ∧
    l["trimming"]? = some k₀.trimming ∧
    l["used_begin"]? = some k₀.used_begin ∧
    l["literals_begin"]? = some k₀.literals_begin ∧
    l["antecedents_begin"]? = some k₀.antecedents_begin ∧
    l["id"]? = some id ∧
    InvMem k m ∧
    CNF.Entails cnf₀
      (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)).toCNF ∧
    (k₀.empty_clause.toNat < id.toNat → cnf₀.Unsat)

private theorem sep_focus_2 {m : Mem 64} {A B R : Mem 64 → Prop}
    (h : m =⋆ A ⋆ (B ⋆ R)) : ∃ R', m =⋆ B ⋆ R' := by
  rw [← sep_assoc A B, sep_comm A B, sep_assoc] at h
  exact ⟨A ⋆ R, h⟩

private theorem sep_focus_3 {m : Mem 64} {A B C R : Mem 64 → Prop}
    (h : m =⋆ A ⋆ (B ⋆ (C ⋆ R))) : ∃ R', m =⋆ C ⋆ R' := by
  rw [← sep_assoc B C, sep_comm B C, sep_assoc] at h
  exact sep_focus_2 h

private theorem sep_focus_4 {m : Mem 64} {A B C D R : Mem 64 → Prop}
    (h : m =⋆ A ⋆ (B ⋆ (C ⋆ (D ⋆ R)))) : ∃ R', m =⋆ D ⋆ R' := by
  rw [← sep_assoc C D, sep_comm C D, sep_assoc] at h
  exact sep_focus_3 h

theorem br_check_proof_loop_ok {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64} {l₀ : Locals 64}
    {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {InvMem : KernelFields → Mem 64 → Prop}
    (_hfst_le : k₀.first_proof_id.toNat ≤ k₀.empty_clause.toNat)
    (hemp_lt : k₀.empty_clause.toNat + 1 < 2 ^ 31)
    (hused_len : k₀.empty_clause.toNat < usedWords.length)
    (hused_int32 : ∀ i (hi : i < usedWords.length), IsInt32 usedWords[i])
    (hlits_len : k₀.empty_clause.toNat < litsPtrs.length)
    (hante_len : k₀.empty_clause.toNat < antePtrs.length)
    (hempty_used : isStepUsed k₀.trimming usedWords k₀.empty_clause.toNat = true)
    (hempty_clause : clauseAt clauses k₀.empty_clause.toNat = .empty)
    (hInvSep : ∀ k m, InvMem k m →
      k.SameConfig k₀ ∧
      ∃ R, m =⋆ kernelState st k ⋆ (int4Array k₀.used_begin usedWords ⋆
        (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R))))
    (hstep : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      ∀ k m, InvMem k m →
        CNF.Entails cnf₀
          (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
            (id.toNat - k₀.first_proof_id.toNat)).toCNF →
        call lratFailExt e B br_check_clause.1 t₀ m
          [st, id, litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len),
            antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)]
          (fun t' m' rets =>
            t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧
            CNF.EntailsClause
              (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
                (id.toNat - k₀.first_proof_id.toNat)).toCNF
              (clauseAt clauses id.toNat)))
    (hinit : CheckProofLoopInv st k₀ usedWords cnf₀ clauses InvMem t₀
      (k₀.empty_clause.toNat + 1 - k₀.first_proof_id.toNat) t₀ m₀ l₀) :
    Exec lratFailExt e B checkProofLoopCmd t₀ m₀ l₀
      (fun t' m' _ => t' = t₀ ∧ (∃ k', InvMem k' m') ∧ cnf₀.Unsat) := by
  refine Exec.while_wf (lt := (· < ·)) Nat.lt_wfRel.wf
    (CheckProofLoopInv st k₀ usedWords cnf₀ clauses InvMem t₀)
    (k₀.empty_clause.toNat + 1 - k₀.first_proof_id.toNat) hinit ?_
  rintro v t m l ⟨id, k, rfl, hid_lo, hid_hi, rfl, hst, hemp, hfst, htrim, husedb, hlitsb, hanteb, hid, hinv, hent, hunsat⟩
  have hemp_lt31 : k₀.empty_clause.toNat < 2 ^ 31 := by omega
  have hid_lt31 : id.toNat < 2 ^ 31 := by omega
  have hslt : k₀.empty_clause.slt id = decide (k₀.empty_clause.toNat < id.toNat) :=
    slt_iff_toNat_lt hemp_lt31 hid_lt31
  let condVal : BitVec 64 := if (if k₀.empty_clause.slt id then (1 : BitVec 64) else 0) = 0 then 1 else 0
  refine ⟨condVal, ?_, ?_, ?_⟩
  · simp [Expr.eval, hemp, hid, interpBinop, condVal]
  · intro hnz
    have hid_le : id.toNat ≤ k₀.empty_clause.toNat := by
      by_cases hlt : k₀.empty_clause.toNat < id.toNat
      · simp [condVal, hslt, hlt] at hnz
      · omega
    have hid_used : id.toNat < usedWords.length := Nat.lt_of_le_of_lt hid_le hused_len
    have hid_lits : id.toNat < litsPtrs.length := Nat.lt_of_le_of_lt hid_le hlits_len
    have hid_ante : id.toNat < antePtrs.length := Nat.lt_of_le_of_lt hid_le hante_len
    obtain ⟨_, R, hm_sep⟩ := hInvSep k m hinv
    let uw : BitVec 64 := if k₀.trimming = 0#64 then -1#64 else usedWords[id.toNat]
    -- Step 1: if trimming { used_where = ... } else { used_where = -1 }
    refine Exec.seq_cps ?_
    refine Exec.weaken (post1 := fun t1 m1 l1 =>
      t₀ = t1 ∧ m = m1 ∧ l1 = l.insert "used_where" uw) ?_ (fun t1 m1 l1 h1 => ?_)
    · refine Exec.cond_cps (v := k₀.trimming) (by simp [Expr.eval, htrim]) (fun htnz => ?_) (fun htz => ?_)
      · have huw : uw = usedWords[id.toNat] := ite_eq_right_iff.mpr fun h => False.elim (htnz h)
        refine Exec.set_cps (v := uw) ?_ ⟨rfl, rfl, rfl⟩
        rw [huw]
        obtain ⟨R_used, hm_used⟩ := sep_focus_2 hm_sep
        refine eval_load4_int4Array_elem hid_used ?_ hm_used (hused_int32 id.toNat hid_used)
        simp [Expr.eval, husedb, hid, slu_two_eq_ofNat hid_lt31, interpBinop]
      · have huw : uw = -1#64 := ite_eq_left_iff.mpr fun h => False.elim (h htz)
        refine Exec.set_cps (v := uw) ?_ ⟨rfl, rfl, rfl⟩
        rw [huw]
        rfl
    · rcases h1 with ⟨rfl, rfl, rfl⟩
      let l1 := l.insert "used_where" uw
      -- Step 2: if used_where { l = ...; a = ...; br_check_clause(st, id, l, a) }
      refine Exec.seq_cps ?_
      refine Exec.weaken (post1 := fun t2 m2 l2 =>
        t₀ = t2 ∧
        l2["st"]? = some st ∧
        l2["empty_clause"]? = some k₀.empty_clause ∧
        l2["first_proof_id"]? = some k₀.first_proof_id ∧
        l2["trimming"]? = some k₀.trimming ∧
        l2["used_begin"]? = some k₀.used_begin ∧
        l2["literals_begin"]? = some k₀.literals_begin ∧
        l2["antecedents_begin"]? = some k₀.antecedents_begin ∧
        l2["id"]? = some id ∧
        (∃ k', InvMem k' m2) ∧
        CNF.Entails cnf₀
          (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
            (id.toNat - k₀.first_proof_id.toNat + 1)).toCNF ∧
        (k₀.empty_clause.toNat < id.toNat + 1 → cnf₀.Unsat)) ?_ (fun t2 m2 l2 h2 => ?_)
      · refine Exec.cond_cps (v := uw) (by simp [Expr.eval]) (fun huw_nz => ?_) (fun huw_z => ?_)
        · have hused_true : isStepUsed k₀.trimming usedWords id.toNat = true := by
            rw [isStepUsed_eq_true_iff hid_used]
            by_cases ht0 : k₀.trimming = 0#64
            · exact Or.inl ht0
            · right
              have huw_eq : uw = usedWords[id.toNat] := ite_eq_right_iff.mpr fun h => False.elim (ht0 h)
              rwa [← huw_eq]
          -- l = load8(literals_begin + (id << 3))
          obtain ⟨R_lits, hm_lits⟩ := sep_focus_3 hm_sep
          refine Exec.seq_cps ?_
          refine Exec.set_cps (v := litsPtrs[id.toNat]) ?_ ?_
          · refine eval_load_word8Array_elem hid_lits ?_ hm_lits
            simp [Expr.eval, hlitsb, hid, interpBinop]
          let l_l := l1.insert "l" litsPtrs[id.toNat]
          -- a = load8(antecedents_begin + (id << 3))
          obtain ⟨R_ante, hm_ante⟩ := sep_focus_4 hm_sep
          refine Exec.seq_cps ?_
          refine Exec.set_cps (v := antePtrs[id.toNat]) ?_ ?_
          · refine eval_load_word8Array_elem hid_ante ?_ hm_ante
            simp [Expr.eval, hanteb, hid, interpBinop]
          let l_a := l_l.insert "a" antePtrs[id.toNat]
          -- br_check_clause(st, id, l, a)
          have hargs : evalArgs m l_a [.var "st", .var "id", .var "l", .var "a"] =
              some [st, id, litsPtrs[id.toNat], antePtrs[id.toNat]] := by
            simp [evalArgs, l_a, l_l, l1, Expr.eval, hst, hid]
          refine Exec.call_cps hargs (call.weaken (hstep id hid_lo hid_le hused_true k m hinv hent) ?_)
          rintro t' m' rets ⟨rfl, rfl, hk', hc⟩
          refine ⟨l_a, putManyZip_nil l_a, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk', ?_, ?_⟩
          · simp [l_a, l_l, l1, hst]
          · simp [l_a, l_l, l1, hemp]
          · simp [l_a, l_l, l1, hfst]
          · simp [l_a, l_l, l1, htrim]
          · simp [l_a, l_l, l1, husedb]
          · simp [l_a, l_l, l1, hlitsb]
          · simp [l_a, l_l, l1, hanteb]
          · simp [l_a, l_l, l1, hid]
          · have hidx : k₀.first_proof_id.toNat + (id.toNat - k₀.first_proof_id.toNat) = id.toNat := by omega
            rw [stateAt_succ, hidx, hused_true]
            exact entails_stepState_of_used hent hc
          · intro hlt_succ
            have heq_emp : id.toNat = k₀.empty_clause.toNat := by omega
            have hc_emp : clauseAt clauses id.toNat = .empty := by rw [heq_emp, hempty_clause]
            exact unsat_of_entails_and_entails_empty hent hc hc_emp
        · have hused_false : isStepUsed k₀.trimming usedWords id.toNat = false := by
            rw [Bool.eq_false_iff]
            intro htrue
            rw [isStepUsed_eq_true_iff hid_used] at htrue
            by_cases ht0 : k₀.trimming = 0#64
            · have : uw = -1#64 := ite_eq_left_iff.mpr fun h => False.elim (h ht0)
              rw [this] at huw_z
              contradiction
            · have huw_eq : uw = usedWords[id.toNat] := ite_eq_right_iff.mpr fun h => False.elim (ht0 h)
              rcases htrue with h1 | h2
              · exact ht0 h1
              · exact h2 (huw_eq.symm.trans huw_z)
          refine .skip _ _ _ _ _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨k, hinv⟩, ?_, ?_⟩
          · simp [hst]
          · simp [hemp]
          · simp [hfst]
          · simp [htrim]
          · simp [husedb]
          · simp [hlitsb]
          · simp [hanteb]
          · simp [hid]
          · have hidx : k₀.first_proof_id.toNat + (id.toNat - k₀.first_proof_id.toNat) = id.toNat := by omega
            rw [stateAt_succ, hidx, hused_false]
            exact entails_stepState_of_unused _ hent
          · intro hlt_succ
            have heq_emp : id.toNat = k₀.empty_clause.toNat := by omega
            rw [heq_emp, hempty_used] at hused_false
            contradiction
      · rcases h2 with ⟨rfl, hst2, hemp2, hfst2, htrim2, husedb2, hlitsb2, hanteb2, hid2, ⟨k', hinv2⟩, hent2, hunsat2⟩
        -- Step 3: id = id + 1
        refine Exec.set_cps (v := id + 1#64) (by simp [Expr.eval, hid2, interpBinop]) ?_
        have hid1_toNat : (id + 1#64).toNat = id.toNat + 1 := toNat_add_one_of_lt (by omega)
        have hsub : (id + 1#64).toNat - k₀.first_proof_id.toNat = id.toNat - k₀.first_proof_id.toNat + 1 := by
          rw [hid1_toNat]; omega
        refine ⟨k₀.empty_clause.toNat + 1 - (id + 1#64).toNat,
          ⟨id + 1#64, k', rfl, by omega, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv2,
            by rwa [hsub], by rw [hid1_toNat]; exact hunsat2⟩,
          by omega⟩
        · simp [hst2]
        · simp [hemp2]
        · simp [hfst2]
        · simp [htrim2]
        · simp [husedb2]
        · simp [hlitsb2]
        · simp [hanteb2]
        · simp
  · intro hz
    have hlt : k₀.empty_clause.toNat < id.toNat := by
      by_cases h : k₀.empty_clause.toNat < id.toNat
      · exact h
      · simp [condVal, hslt, h] at hz
    exact ⟨rfl, ⟨k, hinv⟩, hunsat hlt⟩

/-- Top-level `call` specification for `br_check_proof`: when `checking ≠ 0`, `forward = 0`,
`0 < first_proof_id ≤ empty_clause`, `empty_clause` is marked used (or `trimming = 0`), and
`clauses[empty_clause] = .empty`, `br_check_proof` establishes `cnf₀.Unsat`. -/
theorem call_br_check_proof {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {InvMem : KernelFields → Mem 64 → Prop}
    (hfn : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hchecking : k₀.checking ≠ 0)
    (hforward : k₀.forward = 0)
    (hfst_pos : 0 < k₀.first_proof_id.toNat)
    (hfst_le : k₀.first_proof_id.toNat ≤ k₀.empty_clause.toNat)
    (hemp_lt : k₀.empty_clause.toNat + 1 < 2 ^ 31)
    (hused_len : k₀.empty_clause.toNat < usedWords.length)
    (hused_int32 : ∀ i (hi : i < usedWords.length), IsInt32 usedWords[i])
    (hlits_len : k₀.empty_clause.toNat < litsPtrs.length)
    (hante_len : k₀.empty_clause.toNat < antePtrs.length)
    (hempty_used : isStepUsed k₀.trimming usedWords k₀.empty_clause.toNat = true)
    (hempty_clause : clauseAt clauses k₀.empty_clause.toNat = .empty)
    (hInvInit : InvMem k₀ m₀)
    (hInvSep : ∀ k m, InvMem k m →
      k.SameConfig k₀ ∧
      ∃ R, m =⋆ kernelState st k ⋆ (int4Array k₀.used_begin usedWords ⋆
        (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R))))
    (hstep : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      ∀ k m, InvMem k m →
        CNF.Entails cnf₀
          (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
            (id.toNat - k₀.first_proof_id.toNat)).toCNF →
        call lratFailExt e B br_check_clause.1 t₀ m
          [st, id, litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len),
            antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)]
          (fun t' m' rets =>
            t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧
            CNF.EntailsClause
              (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
                (id.toNat - k₀.first_proof_id.toNat)).toCNF
              (clauseAt clauses id.toNat))) :
    call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t' m' rets => t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧ cnf₀.Unsat) := by
  let l₀ : Locals 64 := insertMany ∅ (br_check_proof.2.params.zip [st])
  refine call.of_body hfn rfl ?_
  change Exec lratFailExt e B br_check_proof.2.body t₀ m₀ l₀ (fun t' m' l' =>
    ∃ rets, getMany l' [] = some rets ∧ t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧ cnf₀.Unsat)
  dsimp only [br_check_proof, Func.body]
  obtain ⟨_, R₀, hm₀⟩ := hInvSep k₀ m₀ hInvInit
  have hst₀ : l₀["st"]? = some st := by
    simp [l₀, br_check_proof, insertMany_cons, insertMany_nil]
  have hemp32 : IsInt32 k₀.empty_clause := isInt32_of_toNat_lt (by omega)
  have hfst32 : IsInt32 k₀.first_proof_id := isInt32_of_toNat_lt (by omega)
  have hemp_ne : k₀.empty_clause ≠ 0 :=
    fun h0 => Nat.ne_of_gt (Nat.lt_of_lt_of_le hfst_pos hfst_le) (by rw [h0]; rfl)
  have hfst_ne : k₀.first_proof_id ≠ 0 :=
    fun h0 => Nat.ne_of_gt hfst_pos (by rw [h0]; rfl)
  -- checking = load8(st + 96)
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.checking) ?_ ?_
  · simp [Expr.eval, hst₀, interpBinop]
    exact kernelState_load_checking hm₀
  let l1 := l₀.insert "checking" k₀.checking
  -- forward = load8(st + 104)
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.forward) ?_ ?_
  · simp [Expr.eval, hst₀, interpBinop]
    exact kernelState_load_forward hm₀
  let l2 := l1.insert "forward" k₀.forward
  -- empty_clause = (load8(st + 64) << 32) .>> 32
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.empty_clause) ?_ ?_
  · simp [Expr.eval, hst₀, interpBinop, kernelState_load_empty_clause hm₀, sext32_of_isInt32 hemp32]
  let l3 := l2.insert "empty_clause" k₀.empty_clause
  -- first_proof_id = (load8(st + 72) << 32) .>> 32
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.first_proof_id) ?_ ?_
  · simp [Expr.eval, hst₀, interpBinop, kernelState_load_first_proof_id hm₀, sext32_of_isInt32 hfst32]
  let l4 := l3.insert "first_proof_id" k₀.first_proof_id
  -- if checking
  refine .if_true _ _ _ _ _ _ _ _ k₀.checking (by simp [Expr.eval]) hchecking ?_
  -- if forward == 0
  refine .if_true _ _ _ _ _ _ _ _ 1#64 (by simp [Expr.eval, interpBinop, hforward]) (by decide) ?_
  -- if empty_clause
  refine .if_true _ _ _ _ _ _ _ _ k₀.empty_clause (by simp [Expr.eval]) hemp_ne ?_
  -- if first_proof_id
  refine .if_true _ _ _ _ _ _ _ _ k₀.first_proof_id (by simp [Expr.eval]) hfst_ne ?_
  -- trimming = load8(st + 88)
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.trimming) ?_ ?_
  · simp [Expr.eval, hst₀, interpBinop]
    exact kernelState_load_trimming hm₀
  let l5 := l4.insert "trimming" k₀.trimming
  -- used_begin = load8(st)
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.used_begin) ?_ ?_
  · simp [Expr.eval, hst₀]
    exact kernelState_load_used_begin hm₀
  let l6 := l5.insert "used_begin" k₀.used_begin
  -- literals_begin = load8(st + 16)
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.literals_begin) ?_ ?_
  · simp [Expr.eval, hst₀, interpBinop]
    exact kernelState_load_literals_begin hm₀
  let l7 := l6.insert "literals_begin" k₀.literals_begin
  -- antecedents_begin = load8(st + 8)
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.antecedents_begin) ?_ ?_
  · simp [Expr.eval, hst₀, interpBinop]
    exact kernelState_load_antecedents_begin hm₀
  let l8 := l7.insert "antecedents_begin" k₀.antecedents_begin
  -- id = first_proof_id
  refine Exec.seq_cps ?_
  refine Exec.set_cps (v := k₀.first_proof_id) (by simp [Expr.eval]) ?_
  let l9 := l8.insert "id" k₀.first_proof_id
  -- while (empty_clause .< id) == 0 { ... }
  refine (br_check_proof_loop_ok hfst_le hemp_lt hused_len hused_int32 hlits_len hante_len
    hempty_used hempty_clause hInvSep hstep ?_).weaken ?_
  · refine ⟨k₀.first_proof_id, k₀, rfl, Nat.le_refl _, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hInvInit, ?_, fun hlt => by omega⟩
    · simp [hst₀]
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · rw [Nat.sub_self]
      exact entails_stateAt_zero cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
  · rintro t' m' _ ⟨rfl, hk', hunsat⟩
    exact ⟨[], rfl, rfl, rfl, hk', hunsat⟩

/-- Combined specification for `br_check_proof` and `br_check_clause`: reduces `br_check_proof`
directly to the specifications of `br_check_clause_strictly_by_resolution` (when `k₀.strict ≠ 0`)
and `br_check_clause_non_strictly_by_propagation` (when `k₀.strict = 0`). -/
theorem call_br_check_proof_of_subcheckers {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable : List (List (BitVec 64))}
    {InvMem : KernelFields → Mem 64 → Prop}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hchecking : k₀.checking ≠ 0)
    (hforward : k₀.forward = 0)
    (hfst_pos : 0 < k₀.first_proof_id.toNat)
    (hfst_le : k₀.first_proof_id.toNat ≤ k₀.empty_clause.toNat)
    (hemp_lt : k₀.empty_clause.toNat + 1 < 2 ^ 31)
    (hused_len : k₀.empty_clause.toNat < usedWords.length)
    (hused_int32 : ∀ i (hi : i < usedWords.length), IsInt32 usedWords[i])
    (hlits_len : k₀.empty_clause.toNat < litsPtrs.length)
    (hante_len : k₀.empty_clause.toNat < antePtrs.length)
    (hempty_used : isStepUsed k₀.trimming usedWords k₀.empty_clause.toNat = true)
    (hempty_clause : clauseAt clauses k₀.empty_clause.toNat = .empty)
    (hInvInit : InvMem k₀ m₀)
    (hInvSep : ∀ k m, InvMem k m →
      k.SameConfig k₀ ∧
      ∃ R, m =⋆ kernelState st k ⋆ (int4Array k₀.used_begin usedWords ⋆
        (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R))))
    (hInvClause : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      clauseAt clauses id.toNat = toClause (litsTable.getD id.toNat []) ∧
      ∀ k m, InvMem k m →
        ∃ R_cl,
          (m =⋆ kernelState st k ⋆
            (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len))
              (litsTable.getD id.toNat []) ⋆ R_cl)) ∧
          (k₀.strict ≠ 0 →
            ∀ m₁,
              (m₁ =⋆ kernelState st (k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))) ⋆
                (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len))
                  (litsTable.getD id.toNat []) ⋆ R_cl)) →
              call lratFailExt e B br_check_clause_strictly_by_resolution.1 t₀ m₁
                [st, id, litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len),
                  antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)]
                (fun t' m' rets =>
                  t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧
                  CNF.EntailsClause
                    (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
                      (id.toNat - k₀.first_proof_id.toNat)).toCNF
                    (toClause (litsTable.getD id.toNat [])))) ∧
          (k₀.strict = 0 →
            ∀ m₁,
              (m₁ =⋆ kernelState st (k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))) ⋆
                (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len))
                  (litsTable.getD id.toNat []) ⋆ R_cl)) →
              call lratFailExt e B br_check_clause_non_strictly_by_propagation.1 t₀ m₁
                [st, id, litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len),
                  antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)]
                (fun t' m' rets =>
                  t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧
                  CNF.EntailsClause
                    (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
                      (id.toNat - k₀.first_proof_id.toNat)).toCNF
                    (toClause (litsTable.getD id.toNat []))))) :
    call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t' m' rets => t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧ cnf₀.Unsat) := by
  refine call_br_check_proof hfn_proof hchecking hforward hfst_pos hfst_le hemp_lt
    hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause hInvInit hInvSep ?_
  intro id hid_lo hid_hi hused k m hinv _hent
  obtain ⟨hc_eq, hcl_mem⟩ := hInvClause id hid_lo hid_hi hused
  obtain ⟨R_cl, hm_cl, hstrict, hrup⟩ := hcl_mem k m hinv
  have hcfg := (hInvSep k m hinv).1
  rw [hc_eq]
  refine call_br_check_clause_zeroTerm hfn_clause hm_cl (fun m₁ hm₁ => ?_)
  by_cases hkz : k.strict = 0
  · rw [ite_eq_left_iff.mpr fun h => False.elim (h hkz)]
    refine call.weaken (hrup (hcfg.strict ▸ hkz) m₁ hm₁) ?_
    rintro t' m' rets ⟨rfl, rfl, hk', hc⟩
    exact ⟨rfl, rfl, rfl, hk', hc⟩
  · rw [ite_eq_right_iff.mpr fun h => False.elim (hkz h)]
    refine call.weaken (hstrict (hcfg.strict ▸ hkz) m₁ hm₁) ?_
    rintro t' m' rets ⟨rfl, rfl, hk', hc⟩
    exact ⟨rfl, rfl, rfl, hk', hc⟩

/-- Option A (`k₀.strict = 0`) specialization of `call_br_check_proof_of_subcheckers`:
only requires `br_check_clause_non_strictly_by_propagation`. -/
theorem call_br_check_proof_non_strict {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable : List (List (BitVec 64))}
    {InvMem : KernelFields → Mem 64 → Prop}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hstrict0 : k₀.strict = 0)
    (hchecking : k₀.checking ≠ 0)
    (hforward : k₀.forward = 0)
    (hfst_pos : 0 < k₀.first_proof_id.toNat)
    (hfst_le : k₀.first_proof_id.toNat ≤ k₀.empty_clause.toNat)
    (hemp_lt : k₀.empty_clause.toNat + 1 < 2 ^ 31)
    (hused_len : k₀.empty_clause.toNat < usedWords.length)
    (hused_int32 : ∀ i (hi : i < usedWords.length), IsInt32 usedWords[i])
    (hlits_len : k₀.empty_clause.toNat < litsPtrs.length)
    (hante_len : k₀.empty_clause.toNat < antePtrs.length)
    (hempty_used : isStepUsed k₀.trimming usedWords k₀.empty_clause.toNat = true)
    (hempty_clause : clauseAt clauses k₀.empty_clause.toNat = .empty)
    (hInvInit : InvMem k₀ m₀)
    (hInvSep : ∀ k m, InvMem k m →
      k.SameConfig k₀ ∧
      ∃ R, m =⋆ kernelState st k ⋆ (int4Array k₀.used_begin usedWords ⋆
        (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R))))
    (hInvClause : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      clauseAt clauses id.toNat = toClause (litsTable.getD id.toNat []) ∧
      ∀ k m, InvMem k m →
        ∃ R_cl,
          (m =⋆ kernelState st k ⋆
            (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len))
              (litsTable.getD id.toNat []) ⋆ R_cl)) ∧
          (∀ m₁,
            (m₁ =⋆ kernelState st (k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))) ⋆
              (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len))
                (litsTable.getD id.toNat []) ⋆ R_cl)) →
            call lratFailExt e B br_check_clause_non_strictly_by_propagation.1 t₀ m₁
              [st, id, litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len),
                antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)]
              (fun t' m' rets =>
                t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧
                CNF.EntailsClause
                  (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
                    (id.toNat - k₀.first_proof_id.toNat)).toCNF
                  (toClause (litsTable.getD id.toNat []))))) :
    call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t' m' rets => t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧ cnf₀.Unsat) := by
  refine call_br_check_proof_of_subcheckers (litsTable := litsTable) hfn_proof hfn_clause
    hchecking hforward hfst_pos hfst_le
    hemp_lt hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause hInvInit hInvSep ?_
  intro id hid_lo hid_hi hused
  obtain ⟨hc_eq, hcl⟩ := hInvClause id hid_lo hid_hi hused
  refine ⟨hc_eq, fun k m hinv => ?_⟩
  obtain ⟨R_cl, hm_cl, hrup⟩ := hcl k m hinv
  exact ⟨R_cl, hm_cl, fun hne => False.elim (hne hstrict0), fun _ => hrup⟩

/-- Option B (`k₀.strict ≠ 0`) specialization of `call_br_check_proof_of_subcheckers`:
only requires `br_check_clause_strictly_by_resolution`. -/
theorem call_br_check_proof_strict {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable : List (List (BitVec 64))}
    {InvMem : KernelFields → Mem 64 → Prop}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hstrict_ne : k₀.strict ≠ 0)
    (hchecking : k₀.checking ≠ 0)
    (hforward : k₀.forward = 0)
    (hfst_pos : 0 < k₀.first_proof_id.toNat)
    (hfst_le : k₀.first_proof_id.toNat ≤ k₀.empty_clause.toNat)
    (hemp_lt : k₀.empty_clause.toNat + 1 < 2 ^ 31)
    (hused_len : k₀.empty_clause.toNat < usedWords.length)
    (hused_int32 : ∀ i (hi : i < usedWords.length), IsInt32 usedWords[i])
    (hlits_len : k₀.empty_clause.toNat < litsPtrs.length)
    (hante_len : k₀.empty_clause.toNat < antePtrs.length)
    (hempty_used : isStepUsed k₀.trimming usedWords k₀.empty_clause.toNat = true)
    (hempty_clause : clauseAt clauses k₀.empty_clause.toNat = .empty)
    (hInvInit : InvMem k₀ m₀)
    (hInvSep : ∀ k m, InvMem k m →
      k.SameConfig k₀ ∧
      ∃ R, m =⋆ kernelState st k ⋆ (int4Array k₀.used_begin usedWords ⋆
        (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R))))
    (hInvClause : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      clauseAt clauses id.toNat = toClause (litsTable.getD id.toNat []) ∧
      ∀ k m, InvMem k m →
        ∃ R_cl,
          (m =⋆ kernelState st k ⋆
            (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len))
              (litsTable.getD id.toNat []) ⋆ R_cl)) ∧
          (∀ m₁,
            (m₁ =⋆ kernelState st (k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))) ⋆
              (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len))
                (litsTable.getD id.toNat []) ⋆ R_cl)) →
            call lratFailExt e B br_check_clause_strictly_by_resolution.1 t₀ m₁
              [st, id, litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len),
                antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)]
              (fun t' m' rets =>
                t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧
                CNF.EntailsClause
                  (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
                    (id.toNat - k₀.first_proof_id.toNat)).toCNF
                  (toClause (litsTable.getD id.toNat []))))) :
    call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t' m' rets => t' = t₀ ∧ rets = [] ∧ (∃ k', InvMem k' m') ∧ cnf₀.Unsat) := by
  refine call_br_check_proof_of_subcheckers (litsTable := litsTable) hfn_proof hfn_clause
    hchecking hforward hfst_pos hfst_le
    hemp_lt hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause hInvInit hInvSep ?_
  intro id hid_lo hid_hi hused
  obtain ⟨hc_eq, hcl⟩ := hInvClause id hid_lo hid_hi hused
  refine ⟨hc_eq, fun k m hinv => ?_⟩
  obtain ⟨R_cl, hm_cl, hstrict⟩ := hcl k m hinv
  exact ⟨R_cl, hm_cl, fun _ => hstrict, fun h0 => False.elim (hstrict_ne h0)⟩

/-- Corollary via `run_body_of_call (Handler.ok_none lratFailExt)`: any terminating `Interp.run`
execution of `br_check_proof` (under the standard handler that rejects `lrat_fail`) guarantees
that the original CNF formula `cnf₀` is unsatisfiable (`cnf₀.Unsat`). -/
theorem br_check_proof_run_unsat {e : Env} {B : Nat} {t₀ t' : Trace 64} {m₀ m' : Mem 64}
    {st : BitVec 64} {lf l' : Locals 64} {fill : UInt8} {fuel : Nat} {o o' : List (BitVec 64)}
    {cnf₀ : CNF Nat} {P : Trace 64 → Mem 64 → Prop}
    (hcall : call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t₁ m₁ rets => P t₁ m₁ ∧ rets = [] ∧ cnf₀.Unsat))
    (hfn : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hlf : putManyZip br_check_proof.2.params [st] ∅ = some lf)
    (hrun : run e fill fuel br_check_proof.2.body t₀ m₀ lf o (fun _ _ _ _ => none) =
      some (t', m', l', o')) :
    P t' m' ∧ cnf₀.Unsat := by
  obtain ⟨rets, _, hp, _, hunsat⟩ :=
    run_body_of_call (Handler.ok_none lratFailExt) hcall hfn hlf hrun
  exact ⟨hp, hunsat⟩

/-! ## 6. Option A Integration: End-to-End Non-Strict (RUP) Soundness (`strict = 0`) -/

theorem sep_rearrange_clause (RW KS Z RL : Mem 64 → Prop) :
    (RW ⋆ (KS ⋆ (Z ⋆ RL))) = (KS ⋆ (Z ⋆ (RW ⋆ RL))) := by
  rw [sep_comm_l RW KS (Z ⋆ RL), sep_comm_l RW Z RL]

theorem sep_rearrange_arrays (RW KS U L A R : Mem 64 → Prop) :
    (RW ⋆ (KS ⋆ (U ⋆ (L ⋆ (A ⋆ R))))) = (KS ⋆ (U ⋆ (L ⋆ (A ⋆ (RW ⋆ R))))) := by
  rw [sep_comm_l RW KS, sep_comm_l RW U, sep_comm_l RW L, sep_comm_l RW A]

/-- Concrete `call` specification for `br_check_clause` in non-strict mode (`k.strict = 0`),
combining `call_br_check_clause_zeroTerm` and `br_check_clause_non_strictly_by_propagation_ok`. -/
theorem call_br_check_clause_rup {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64}
    {post : Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    {max_var : Nat} {st id literals antecedents : BitVec 64}
    {k : KernelFields} {lits aids lit_ptrs trail_free0 : List (BitVec 64)}
    {s : State} {P_ro : Mem 64 → Prop}
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hfn_rup : e.lookup br_check_clause_non_strictly_by_propagation.1 =
      some br_check_clause_non_strictly_by_propagation.2)
    (hstrict0 : k.strict = 0)
    (hk_trail : k.trail_end = k.trail_begin)
    (hct : ClauseTable max_var k.literals_begin lit_ptrs s.formula P_ro)
    (hlits_ro : ∃ R_lits, P_ro = (ZeroTermInts literals lits ⋆ R_lits))
    (haids_ro : ∃ R_aids, P_ro = (ZeroTermInts antecedents aids ⋆ R_aids))
    (hlits_valid : ∀ x ∈ lits, IsValidLit max_var x)
    (haids_valid : ∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
      (aid.slt 0 = false → ∃ h : aid.toNat < lit_ptrs.length, lit_ptrs[aid.toNat] ≠ 0))
    (hcap : lits.length + aids.length ≤ trail_free0.length)
    (htrail_len : 4 * trail_free0.length < 2 ^ 64)
    (hsep : m =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k.trail_begin trail_free0) ⋆
      (kernelState st k ⋆ P_ro))
    (hpost : ∀ m' (stat_resolved stat_lit_assigned : BitVec 64)
        (trail_all : List (BitVec 64)),
      trail_all.length = trail_free0.length →
      (m' =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k.trail_begin trail_all) ⋆
        (kernelState st
          { (k.bumpCheckStats ((lits ++ [0])[0]'(by simp))) with
            trail_end := k.trail_begin
            stat_resolved := stat_resolved
            stat_lit_assigned := stat_lit_assigned } ⋆ P_ro)) →
      CNF.EntailsClause s.toCNF (toClause lits) →
      post t m' []) :
    call lratFailExt e B br_check_clause.1 t m [st, id, literals, antecedents] post := by
  obtain ⟨R_lits, hP_lits⟩ := hlits_ro
  have hsep_z : m =⋆ kernelState st k ⋆
      (ZeroTermInts literals lits ⋆
        ((byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k.trail_begin trail_free0) ⋆ R_lits)) := by
    have h := hsep
    rw [hP_lits, sep_rearrange_clause] at h
    exact h
  refine call_br_check_clause_zeroTerm hfn_clause hsep_z (fun m₁ hm₁ => ?_)
  rw [ite_eq_left hstrict0]
  let k1 := k.bumpCheckStats ((lits ++ [0])[0]'(by simp))
  have hm₁_rup : m₁ =⋆ (byte1Array k1.values_begin (assignBytes max_var Assignment.empty) ⋆
      int4Array k1.trail_begin trail_free0) ⋆
    (kernelState st k1 ⋆ P_ro) := by
    have h := hm₁
    rw [← sep_rearrange_clause, ← hP_lits] at h
    exact h
  exact br_check_clause_non_strictly_by_propagation_ok (k := k1) hfn_rup hk_trail hct
    ⟨R_lits, hP_lits⟩ haids_ro hlits_valid haids_valid hcap htrail_len hm₁_rup
    (fun m' sr sla trail_all hlen hm' hent => ⟨rfl, hpost m' sr sla trail_all hlen hm' hent⟩)

/-- Memory invariant maintained across iterations of `br_check_proof` in RUP mode (`strict = 0`). -/
def RupMemInv (max_var trail_cap : Nat) (st : BitVec 64) (k₀ : KernelFields)
    (P_ro : Mem 64 → Prop) (k : KernelFields) (m : Mem 64) : Prop :=
  k.SameConfig k₀ ∧
  k.trail_end = k₀.trail_begin ∧
  ∃ trail_free : List (BitVec 64),
    trail_free.length = trail_cap ∧
    (m =⋆ (byte1Array k₀.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k₀.trail_begin trail_free) ⋆
      (kernelState st k ⋆ P_ro))

/-- End-to-end `call` soundness theorem for `br_check_proof` in Option A (`k₀.strict = 0`),
connecting `br_check_proof`, `br_check_clause`, and `br_check_clause_non_strictly_by_propagation_ok`
to `Std.Sat.CNF.Unsat cnf₀`. -/
theorem call_br_check_proof_rup {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {max_var : Nat} {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable anteTable : List (List (BitVec 64))}
    {P_ro : Mem 64 → Prop}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hfn_rup : e.lookup br_check_clause_non_strictly_by_propagation.1 =
      some br_check_clause_non_strictly_by_propagation.2)
    (hstrict0 : k₀.strict = 0)
    (hchecking : k₀.checking ≠ 0)
    (hforward : k₀.forward = 0)
    (hk_trail : k₀.trail_end = k₀.trail_begin)
    (hfst_pos : 0 < k₀.first_proof_id.toNat)
    (hfst_le : k₀.first_proof_id.toNat ≤ k₀.empty_clause.toNat)
    (hemp_lt : k₀.empty_clause.toNat + 1 < 2 ^ 31)
    (hused_len : k₀.empty_clause.toNat < usedWords.length)
    (hused_int32 : ∀ i (hi : i < usedWords.length), IsInt32 usedWords[i])
    (hlits_len : k₀.empty_clause.toNat < litsPtrs.length)
    (hante_len : k₀.empty_clause.toNat < antePtrs.length)
    (hempty_used : isStepUsed k₀.trimming usedWords k₀.empty_clause.toNat = true)
    (hempty_clause : clauseAt clauses k₀.empty_clause.toNat = .empty)
    (htrail_len : 4 * trail_free0.length < 2 ^ 64)
    (hP_arrays : ∃ R_arr, P_ro = (int4Array k₀.used_begin usedWords ⋆
      (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R_arr))))
    (hsep0 : m₀ =⋆ (byte1Array k₀.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k₀.trail_begin trail_free0) ⋆
      (kernelState st k₀ ⋆ P_ro))
    (hsteps : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      let lits := litsTable.getD id.toNat []
      let aids := anteTable.getD id.toNat []
      let s := stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)
      clauseAt clauses id.toNat = toClause lits ∧
      ClauseTable max_var k₀.literals_begin (litsPtrs.take id.toNat) s.formula P_ro ∧
      (∃ R_lits, P_ro = (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len)) lits ⋆ R_lits)) ∧
      (∃ R_aids, P_ro = (ZeroTermInts (antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)) aids ⋆ R_aids)) ∧
      (∀ x ∈ lits, IsValidLit max_var x) ∧
      (∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
        (aid.slt 0 = false →
          ∃ h : aid.toNat < (litsPtrs.take id.toNat).length, (litsPtrs.take id.toNat)[aid.toNat] ≠ 0)) ∧
      lits.length + aids.length ≤ trail_free0.length) :
    call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t' m' rets =>
        t' = t₀ ∧ rets = [] ∧
        (∃ k', RupMemInv max_var trail_free0.length st k₀ P_ro k' m') ∧
        cnf₀.Unsat) := by
  refine call_br_check_proof_non_strict (litsTable := litsTable)
    (InvMem := RupMemInv max_var trail_free0.length st k₀ P_ro)
    hfn_proof hfn_clause hstrict0 hchecking hforward hfst_pos hfst_le hemp_lt
    hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause
    ⟨KernelFields.SameConfig.refl k₀, hk_trail, trail_free0, rfl, hsep0⟩ ?_ ?_
  · rintro k m ⟨hcfg, _, trail_free, _, hm⟩
    refine ⟨hcfg, ?_⟩
    obtain ⟨R_arr, hP⟩ := hP_arrays
    refine ⟨(byte1Array k₀.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k₀.trail_begin trail_free) ⋆ R_arr, ?_⟩
    have h := hm
    rw [hP, sep_rearrange_arrays] at h
    exact h
  · intro id hid_lo hid_hi hused
    obtain ⟨hc_eq, hct, ⟨R_lits, hP_lits⟩, haids_ro, hlits_valid, haids_valid, hcap⟩ :=
      hsteps id hid_lo hid_hi hused
    refine ⟨hc_eq, ?_⟩
    rintro k m ⟨hcfg, hk_te, trail_free, htf_len, hm⟩
    refine ⟨(byte1Array k₀.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k₀.trail_begin trail_free) ⋆ R_lits, ?_, ?_⟩
    · have h := hm
      rw [hP_lits, sep_rearrange_clause] at h
      exact h
    · intro m₁ hm₁
      let k1 := k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))
      have hk1_cfg : k1.SameConfig k₀ := hcfg.bumpCheckStats _
      have hk1_te : k1.trail_end = k1.trail_begin := by
        show k.trail_end = k.trail_begin
        rw [hk_te, hcfg.trail_begin]
      have hm₁_rup : m₁ =⋆ (byte1Array k1.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k1.trail_begin trail_free) ⋆
        (kernelState st k1 ⋆ P_ro) := by
        have h := hm₁
        rw [← sep_rearrange_clause, ← hP_lits, ← hk1_cfg.values_begin, ← hk1_cfg.trail_begin] at h
        exact h
      have hct1 : ClauseTable max_var k1.literals_begin (litsPtrs.take id.toNat)
          (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
            (id.toNat - k₀.first_proof_id.toNat)).formula P_ro := by
        rwa [hk1_cfg.literals_begin]
      refine br_check_clause_non_strictly_by_propagation_ok hfn_rup hk1_te hct1
        ⟨R_lits, hP_lits⟩ haids_ro hlits_valid haids_valid
        (htf_len ▸ hcap) (htf_len ▸ htrail_len) hm₁_rup ?_
      intro m' sr sla trail_all hlen_all hm' hent_cl
      let k' : KernelFields :=
        { k1 with
          trail_end := k1.trail_begin
          stat_resolved := sr
          stat_lit_assigned := sla }
      have hk'_cfg : k'.SameConfig k₀ :=
        ⟨hk1_cfg.1, hk1_cfg.2, hk1_cfg.3, hk1_cfg.4, hk1_cfg.5, hk1_cfg.6, hk1_cfg.7,
         hk1_cfg.8, hk1_cfg.9, hk1_cfg.10, hk1_cfg.11, hk1_cfg.12, hk1_cfg.13⟩
      change m' =⋆ (byte1Array k1.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k1.trail_begin trail_all) ⋆
        (kernelState st k' ⋆ P_ro) at hm'
      rw [hk1_cfg.values_begin, hk1_cfg.trail_begin] at hm'
      exact ⟨rfl, rfl, ⟨k', hk'_cfg, hk1_cfg.trail_begin, trail_all, hlen_all.trans htf_len, hm'⟩, hent_cl⟩

/-- End-to-end `Interp.run` soundness corollary for Option A (`k₀.strict = 0`):
any terminating execution of `br_check_proof` (under the standard handler that rejects `lrat_fail`)
guarantees `cnf₀.Unsat` (`Std.Sat.CNF.Unsat cnf₀`). -/
theorem br_check_proof_rup_run_unsat {e : Env} {t₀ t' : Trace 64} {m₀ m' : Mem 64}
    {max_var : Nat} {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable anteTable : List (List (BitVec 64))}
    {P_ro : Mem 64 → Prop}
    {lf l' : Locals 64} {fill : UInt8} {fuel : Nat} {o o' : List (BitVec 64)}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hfn_rup : e.lookup br_check_clause_non_strictly_by_propagation.1 =
      some br_check_clause_non_strictly_by_propagation.2)
    (hstrict0 : k₀.strict = 0)
    (hchecking : k₀.checking ≠ 0)
    (hforward : k₀.forward = 0)
    (hk_trail : k₀.trail_end = k₀.trail_begin)
    (hfst_pos : 0 < k₀.first_proof_id.toNat)
    (hfst_le : k₀.first_proof_id.toNat ≤ k₀.empty_clause.toNat)
    (hemp_lt : k₀.empty_clause.toNat + 1 < 2 ^ 31)
    (hused_len : k₀.empty_clause.toNat < usedWords.length)
    (hused_int32 : ∀ i (hi : i < usedWords.length), IsInt32 usedWords[i])
    (hlits_len : k₀.empty_clause.toNat < litsPtrs.length)
    (hante_len : k₀.empty_clause.toNat < antePtrs.length)
    (hempty_used : isStepUsed k₀.trimming usedWords k₀.empty_clause.toNat = true)
    (hempty_clause : clauseAt clauses k₀.empty_clause.toNat = .empty)
    (htrail_len : 4 * trail_free0.length < 2 ^ 64)
    (hP_arrays : ∃ R_arr, P_ro = (int4Array k₀.used_begin usedWords ⋆
      (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R_arr))))
    (hsep0 : m₀ =⋆ (byte1Array k₀.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k₀.trail_begin trail_free0) ⋆
      (kernelState st k₀ ⋆ P_ro))
    (hsteps : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      let lits := litsTable.getD id.toNat []
      let aids := anteTable.getD id.toNat []
      let s := stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)
      clauseAt clauses id.toNat = toClause lits ∧
      ClauseTable max_var k₀.literals_begin (litsPtrs.take id.toNat) s.formula P_ro ∧
      (∃ R_lits, P_ro = (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len)) lits ⋆ R_lits)) ∧
      (∃ R_aids, P_ro = (ZeroTermInts (antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)) aids ⋆ R_aids)) ∧
      (∀ x ∈ lits, IsValidLit max_var x) ∧
      (∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
        (aid.slt 0 = false →
          ∃ h : aid.toNat < (litsPtrs.take id.toNat).length, (litsPtrs.take id.toNat)[aid.toNat] ≠ 0)) ∧
      lits.length + aids.length ≤ trail_free0.length)
    (hlf : putManyZip br_check_proof.2.params [st] ∅ = some lf)
    (hrun : run e fill fuel br_check_proof.2.body t₀ m₀ lf o (fun _ _ _ _ => none) =
      some (t', m', l', o')) :
    cnf₀.Unsat := by
  have hcall := call_br_check_proof_rup (B := 0) (t₀ := t₀) (litsTable := litsTable) (anteTable := anteTable)
    hfn_proof hfn_clause hfn_rup hstrict0 hchecking hforward hk_trail hfst_pos hfst_le hemp_lt
    hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause htrail_len hP_arrays hsep0 hsteps
  obtain ⟨_, _, _, _, _, hunsat⟩ :=
    run_body_of_call (Handler.ok_none lratFailExt) hcall hfn_proof hlf hrun
  exact hunsat

end Kraken.Bedrock2.Test
