module

public import Kraken.Bedrock2.Test.LratTrimSpec
public import Kraken.Bedrock2.Test.LratTrimRupProof
public import Kraken.Bedrock2.Test.LratTrimStrictProof
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
    load? .eight m (st + BitVec.ofNat 64 (8 * i)) = some (k.toList[i]'(by simpa using hi)) :=
  load_word8Array_elem (by simpa using hi) (show m =⋆ word8Array st k.toList ⋆ R from hsep)

theorem kernelState_load_used_begin {m : Mem 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (hsep : m =⋆ kernelState st k ⋆ R) :
    load? .eight m st = some k.used_begin := by
  simpa [KernelFields.toList] using kernelState_load_field hsep 0 (by decide)

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
  simp [State.ofCNF, State.toCNF, ← Array.toList_inj, List.filterMap_map]

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
  induction n <;> simp [*, Nat.add_assoc]

theorem formula_stepState (s : State) (used : Bool) (c : CNF.Clause Nat) :
    (stepState s used c).formula = s.formula.push (if used then some c else none) := by
  cases used <;> rfl

theorem getElem?_formula_stateAt_of_lt (cnf₀ : CNF Nat) (first_proof_id : Nat) (trimming : BitVec 64)
    (usedWords : List (BitVec 64)) (clauses : List (CNF.Clause Nat)) (n : Nat)
    {j : Nat} (hj : j < cnf₀.clauses.size) :
    (stateAt cnf₀ first_proof_id trimming usedWords clauses n).formula[j]? =
      some (some cnf₀.clauses[j]) := by
  induction n with
  | zero => simp [State.ofCNF, hj]
  | succ n ih =>
    rw [stateAt_succ, formula_stepState, Array.getElem?_push, ite_eq_right (by simp; omega), ih]

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
    split <;> grind

theorem mem_toCNF_of_getElem?_formula {s : State} {j : Nat} {c : CNF.Clause Nat}
    (h : s.formula[j]? = some (some c)) :
    c ∈ s.toCNF.clauses := by
  simp only [State.toCNF, ← Array.mem_toList_iff, Array.toList_filterMap, List.mem_filterMap]
  exact ⟨some c, Array.mem_toList_iff.mpr (Array.mem_of_getElem? h), rfl⟩

theorem entailsClause_toCNF_of_getElem?_formula {s : State} {j : Nat} {c : CNF.Clause Nat}
    (h : s.formula[j]? = some (some c)) :
    CNF.EntailsClause s.toCNF c :=
  fun _ hsat => CNF.sat_of_mem hsat (CNF.Internal.mem_iff.mpr (mem_toCNF_of_getElem?_formula h))

theorem unsat_of_entails_and_entails_empty {cnf₀ f : CNF Nat} {c : CNF.Clause Nat}
    (hent : CNF.Entails cnf₀ f) (hc : CNF.EntailsClause f c) (hempty : c = .empty) :
    cnf₀.Unsat := by
  subst hempty
  exact CNF.unsat_of_entails_unsat (CNF.unsat_of_entails_clause_unsat CNF.Clause.unsat_empty hc) hent

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

theorem KernelFields.SameConfig.refl (k : KernelFields) : k.SameConfig k := by
  constructor <;> rfl

theorem KernelFields.SameConfig.bumpCheckStats {k k₀ : KernelFields} (h : k.SameConfig k₀)
    (w₀ : BitVec 64) : (k.bumpCheckStats w₀).SameConfig k₀ := by
  cases h; constructor <;> assumption

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
  change Exec lratFailExt e B br_check_clause.2.body t m l₀ _
  dsimp only [br_check_clause, Func.body]
  have hst : l₀["st"]? = some st := by simp [l₀, br_check_clause, insertMany_cons, insertMany_nil]
  have hlits : l₀["literals"]? = some literals := by simp [l₀, br_check_clause, insertMany_cons, insertMany_nil]
  refine Exec.seq_cps ?_
  refine kernelState_store_stat_chk_total (v := k.stat_chk_total + 1)
    (by simp [Expr.eval, hst, interpBinop])
    (by simp [Expr.eval, hst, interpBinop, kernelState_load_stat_chk_total hsep])
    hsep fun m1 hm1 => ?_
  let k1 : KernelFields := { k with stat_chk_total := k.stat_chk_total + 1 }
  refine Exec.seq_cps (c2 := .seq _ _) ?_
  refine Exec.weaken (post1 := fun t2 m2 l2 => t2 = t ∧ l2 = l₀ ∧
    (m2 =⋆ kernelState st (k.bumpCheckStats w₀) ⋆ (int4 literals w₀ ⋆ R))) ?_ ?_
  · have hload4 : load? .four m1 literals = some (w₀ &&& 0xffffffff#64) :=
      load_int4_raw (by rwa [sep_comm_l] at hm1)
    by_cases h0 : (w₀ &&& 0xffffffff#64) = 0#64
    · refine .if_true _ _ _ _ _ _ _ _ 1#64
        (by simp [Expr.eval, hlits, interpBinop, hload4, h0]) (by decide) ?_
      refine kernelState_store_stat_chk_empty (v := k1.stat_chk_empty + 1)
        (by simp [Expr.eval, hst, interpBinop])
        (by simp [Expr.eval, hst, interpBinop, kernelState_load_stat_chk_empty hm1]; rfl)
        hm1 fun m2 hm2 => ⟨rfl, rfl, by simpa [KernelFields.bumpCheckStats, k1, h0] using hm2⟩
    · refine .if_false _ _ _ _ _ _ _ _ 0#64
        (by simp [Expr.eval, hlits, interpBinop, hload4, h0]) rfl ?_
      exact .skip _ _ _ _ _ ⟨rfl, rfl, by simpa [KernelFields.bumpCheckStats, k1, h0] using hm1⟩
  · rintro _ m2 _ ⟨rfl, rfl, hm2⟩
    refine Exec.seq_cps (Exec.set_cps (v := k.strict)
      (by simp [Expr.eval, hst, interpBinop, kernelState_load_strict hm2]; rfl) ?_)
    have hcall2 := hcall m2 hm2
    have hargs : evalArgs m2 (l₀.insert "strict" k.strict)
        [.var "st", .var "id", .var "literals", .var "antecedents"] =
        some [st, id, literals, antecedents] := by
      simp [evalArgs, l₀, Expr.eval, br_check_clause, insertMany_cons, insertMany_nil]
    refine Exec.cond_cps (v := k.strict) (by simp [Expr.eval]) (fun hnz => ?_) (fun hz => ?_)
    · simp only [hnz, ↓reduceIte] at hcall2
      exact Exec.call_cps hargs (hcall2.weaken (by rintro _ _ _ ⟨rfl, hp⟩; exact ⟨_, putManyZip_nil _, _, rfl, hp⟩))
    · simp only [hz, ↓reduceIte] at hcall2
      exact Exec.call_cps hargs (hcall2.weaken (by rintro _ _ _ ⟨rfl, hp⟩; exact ⟨_, putManyZip_nil _, _, rfl, hp⟩))

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
  simpa [shamt] using hv

theorem isInt32_of_toNat_lt {v : BitVec 64} (hv : v.toNat < 2 ^ 31) : IsInt32 v := by
  unfold IsInt32; grind

theorem slt_iff_toNat_lt {x y : BitVec 64} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    x.slt y = decide (x.toNat < y.toNat) := by
  grind

theorem toNat_add_one_of_lt {id : BitVec 64} (hid : id.toNat + 1 < 2 ^ 31) :
    (id + 1#64).toNat = id.toNat + 1 := by
  rw [BitVec.toNat_add]; simp; omega

theorem slu_two_eq_ofNat {id : BitVec 64} (hid : id.toNat < 2 ^ 31) :
    id <<< shamt 2#64 = BitVec.ofNat 64 (4 * id.toNat) := by
  have _ := hid
  apply BitVec.eq_of_toNat_eq; simp [shamt, Nat.shiftLeft_eq]; omega

theorem slu_three_eq_ofNat {id : BitVec 64} (hid : id.toNat < 2 ^ 31) :
    id <<< shamt 3#64 = BitVec.ofNat 64 (8 * id.toNat) := by
  have _ := hid
  apply BitVec.eq_of_toNat_eq; simp [shamt, Nat.shiftLeft_eq]; omega

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
    (h : m =⋆ A ⋆ (B ⋆ R)) : ∃ R', m =⋆ B ⋆ R' :=
  ⟨_, by rwa [sep_comm_l] at h⟩

private theorem sep_focus_3 {m : Mem 64} {A B C R : Mem 64 → Prop}
    (h : m =⋆ A ⋆ (B ⋆ (C ⋆ R))) : ∃ R', m =⋆ C ⋆ R' :=
  ⟨_, by rwa [show A ⋆ (B ⋆ (C ⋆ R)) = C ⋆ (A ⋆ (B ⋆ R)) by ac_rfl] at h⟩

private theorem sep_focus_4 {m : Mem 64} {A B C D R : Mem 64 → Prop}
    (h : m =⋆ A ⋆ (B ⋆ (C ⋆ (D ⋆ R)))) : ∃ R', m =⋆ D ⋆ R' :=
  ⟨_, by rwa [show A ⋆ (B ⋆ (C ⋆ (D ⋆ R))) = D ⋆ (A ⋆ (B ⋆ (C ⋆ R))) by ac_rfl] at h⟩

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
  have hslt : k₀.empty_clause.slt id = decide (k₀.empty_clause.toNat < id.toNat) :=
    slt_iff_toNat_lt (by omega) (by omega)
  refine ⟨_, by simp [Expr.eval, hemp, hid, interpBinop]; rfl, fun hnz => ?_, fun hz => ?_⟩
  · have hid_le : id.toNat ≤ k₀.empty_clause.toNat := by simp [hslt] at hnz; omega
    have hid_used : id.toNat < usedWords.length := Nat.lt_of_le_of_lt hid_le hused_len
    have hid_lits : id.toNat < litsPtrs.length := Nat.lt_of_le_of_lt hid_le hlits_len
    have hid_ante : id.toNat < antePtrs.length := Nat.lt_of_le_of_lt hid_le hante_len
    obtain ⟨_, R, hm_sep⟩ := hInvSep k m hinv
    let uw : BitVec 64 := if k₀.trimming = 0#64 then -1#64 else usedWords[id.toNat]
    refine Exec.seq_cps (Exec.weaken (post1 := fun t1 m1 l1 =>
      t₀ = t1 ∧ m = m1 ∧ l1 = l.insert "used_where" uw) ?_ ?_)
    · refine Exec.cond_cps (v := k₀.trimming) (by simp [Expr.eval, htrim]) (fun htnz => ?_) (fun htz => ?_)
      · obtain ⟨R_used, hm_used⟩ := sep_focus_2 hm_sep
        refine Exec.set_cps (v := uw) ?_ ⟨rfl, rfl, rfl⟩
        dsimp only [uw]; rw [ite_eq_right (show k₀.trimming ≠ 0#64 from htnz)]
        exact eval_load4_int4Array_elem hid_used
          (by simp [Expr.eval, husedb, hid, interpBinop, slu_two_eq_ofNat (id := id) (by omega)])
          hm_used (hused_int32 id.toNat hid_used)
      · exact Exec.set_cps (v := uw) (by simp [Expr.eval, uw, htz]; rfl) ⟨rfl, rfl, rfl⟩
    · rintro _ _ _ ⟨rfl, rfl, rfl⟩
      let l1 := l.insert "used_where" uw
      refine Exec.seq_cps (Exec.weaken (post1 := fun t2 m2 l2 =>
        t₀ = t2 ∧
        (l2["st"]? = some st ∧ l2["empty_clause"]? = some k₀.empty_clause ∧
         l2["first_proof_id"]? = some k₀.first_proof_id ∧ l2["trimming"]? = some k₀.trimming ∧
         l2["used_begin"]? = some k₀.used_begin ∧ l2["literals_begin"]? = some k₀.literals_begin ∧
         l2["antecedents_begin"]? = some k₀.antecedents_begin ∧ l2["id"]? = some id) ∧
        (∃ k', InvMem k' m2) ∧
        CNF.Entails cnf₀
          (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
            (id.toNat - k₀.first_proof_id.toNat + 1)).toCNF ∧
        (k₀.empty_clause.toNat < id.toNat + 1 → cnf₀.Unsat)) ?_ ?_)
      · refine Exec.cond_cps (v := uw) (by simp [Expr.eval]) (fun huw_nz => ?_) (fun huw_z => ?_)
        · have hused_true : isStepUsed k₀.trimming usedWords id.toNat = true := by
            rw [isStepUsed_eq_true_iff hid_used]
            by_cases ht0 : k₀.trimming = 0#64 <;> simp_all [uw]
          obtain ⟨R_lits, hm_lits⟩ := sep_focus_3 hm_sep
          refine Exec.seq_cps (Exec.set_cps (v := litsPtrs[id.toNat])
            (eval_load_word8Array_elem hid_lits
              (by simp [Expr.eval, hlitsb, hid, ← bitVec_ofNat_eight_mul_toNat, interpBinop])
              hm_lits) ?_)
          let l_l := l1.insert "l" litsPtrs[id.toNat]
          obtain ⟨R_ante, hm_ante⟩ := sep_focus_4 hm_sep
          refine Exec.seq_cps (Exec.set_cps (v := antePtrs[id.toNat])
            (eval_load_word8Array_elem hid_ante
              (by simp [Expr.eval, hanteb, hid, ← bitVec_ofNat_eight_mul_toNat, interpBinop])
              hm_ante) ?_)
          let l_a := l_l.insert "a" antePtrs[id.toNat]
          refine Exec.call_cps
            (by simp [evalArgs, Expr.eval, hst, hid])
            ((hstep id hid_lo hid_le hused_true k m hinv hent).weaken ?_)
          rintro t' m' rets ⟨rfl, rfl, hk', hc⟩
          refine ⟨l_a, putManyZip_nil l_a, rfl, ?_, hk', ?_, ?_⟩
          · simp [l_a, l_l, l1, hst, hemp, hfst, htrim, husedb, hlitsb, hanteb, hid]
          · rw [stateAt_succ, show k₀.first_proof_id.toNat + (id.toNat - k₀.first_proof_id.toNat) = id.toNat by omega, hused_true]
            exact entails_stepState_of_used hent hc
          · exact fun _ => unsat_of_entails_and_entails_empty hent hc
              (by rwa [show id.toNat = k₀.empty_clause.toNat by omega])
        · have hused_false : isStepUsed k₀.trimming usedWords id.toNat = false := by
            rw [Bool.eq_false_iff, ne_eq, isStepUsed_eq_true_iff hid_used]
            by_cases ht0 : k₀.trimming = 0#64
            · simp [uw, ht0] at huw_z
            · have : k₀.trimming ≠ 0 := by simpa using ht0
              simp_all [uw]
          refine .skip _ _ _ _ _ ⟨rfl, ?_, ⟨k, hinv⟩, ?_, ?_⟩
          · simp [hst, hemp, hfst, htrim, husedb, hlitsb, hanteb, hid]
          · rw [stateAt_succ, show k₀.first_proof_id.toNat + (id.toNat - k₀.first_proof_id.toNat) = id.toNat by omega, hused_false]
            exact entails_stepState_of_unused _ hent
          · exact fun _ => by
              rw [show id.toNat = k₀.empty_clause.toNat by omega] at hused_false
              simp [hempty_used] at hused_false
      · rintro _ m2 l2 ⟨rfl, hloc, ⟨k', hinv2⟩, hent2, hunsat2⟩
        refine Exec.set_cps (v := id + 1#64) (by simp [Expr.eval, hloc, interpBinop]) ?_
        have hid1_toNat : (id + 1#64).toNat = id.toNat + 1 := toNat_add_one_of_lt (by omega)
        refine ⟨k₀.empty_clause.toNat + 1 - (id + 1#64).toNat,
          ⟨id + 1#64, k', rfl, by omega, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv2,
            by rwa [show (id + 1#64).toNat - k₀.first_proof_id.toNat = id.toNat - k₀.first_proof_id.toNat + 1 by rw [hid1_toNat]; omega],
            by rwa [hid1_toNat]⟩,
          by omega⟩ <;> simp [hloc]
  · exact ⟨rfl, ⟨k, hinv⟩, hunsat (by simp [hslt] at hz; exact hz)⟩

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
  change Exec lratFailExt e B br_check_proof.2.body t₀ m₀ l₀ _
  dsimp only [br_check_proof, Func.body]
  obtain ⟨_, R₀, hm₀⟩ := hInvSep k₀ m₀ hInvInit
  have hst₀ : l₀["st"]? = some st := by simp [l₀, br_check_proof, insertMany_cons, insertMany_nil]
  have hemp_ne : k₀.empty_clause ≠ 0 := fun h0 => by simp [h0] at hfst_le; omega
  have hfst_ne : k₀.first_proof_id ≠ 0 := fun h0 => by simp [h0] at hfst_pos
  refine Exec.seq_cps (Exec.set_cps (v := k₀.checking)
    (by simp [Expr.eval, hst₀, interpBinop]; exact kernelState_load_checking hm₀) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := k₀.forward)
    (by simp [Expr.eval, hst₀, interpBinop]; exact kernelState_load_forward hm₀) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := k₀.empty_clause)
    (by simp [Expr.eval, hst₀, interpBinop, kernelState_load_empty_clause hm₀,
      sext32_of_isInt32 (isInt32_of_toNat_lt (v := k₀.empty_clause) (by omega))]) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := k₀.first_proof_id)
    (by simp [Expr.eval, hst₀, interpBinop, kernelState_load_first_proof_id hm₀,
      sext32_of_isInt32 (isInt32_of_toNat_lt (v := k₀.first_proof_id) (by omega))]) ?_)
  refine .if_true _ _ _ _ _ _ _ _ k₀.checking (by simp [Expr.eval]) hchecking ?_
  refine .if_true _ _ _ _ _ _ _ _ 1#64 (by simp [Expr.eval, interpBinop, hforward]) (by decide) ?_
  refine .if_true _ _ _ _ _ _ _ _ k₀.empty_clause (by simp [Expr.eval]) hemp_ne ?_
  refine .if_true _ _ _ _ _ _ _ _ k₀.first_proof_id (by simp [Expr.eval]) hfst_ne ?_
  refine Exec.seq_cps (Exec.set_cps (v := k₀.trimming)
    (by simp [Expr.eval, hst₀, interpBinop]; exact kernelState_load_trimming hm₀) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := k₀.used_begin)
    (by simp [Expr.eval, hst₀]; exact kernelState_load_used_begin hm₀) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := k₀.literals_begin)
    (by simp [Expr.eval, hst₀, interpBinop]; exact kernelState_load_literals_begin hm₀) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := k₀.antecedents_begin)
    (by simp [Expr.eval, hst₀, interpBinop]; exact kernelState_load_antecedents_begin hm₀) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := k₀.first_proof_id) (by simp [Expr.eval]) ?_)
  refine (br_check_proof_loop_ok hfst_le hemp_lt hused_len hused_int32 hlits_len hante_len
    hempty_used hempty_clause hInvSep hstep ?_).weaken ?_
  · refine ⟨k₀.first_proof_id, k₀, rfl, Nat.le_refl _, by omega, rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hInvInit, by rw [Nat.sub_self]; exact entails_stateAt_zero _ _ _ _ _,
      fun _ => by omega⟩ <;> (simp; try exact hst₀)
  · exact fun _ _ _ ⟨rfl, hk', hunsat⟩ => ⟨[], rfl, rfl, rfl, hk', hunsat⟩

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
  · rw [ite_eq_left hkz]
    exact (hrup (hcfg.strict ▸ hkz) m₁ hm₁).weaken fun _ _ _ ⟨rfl, rfl, hk', hc⟩ => ⟨rfl, rfl, rfl, hk', hc⟩
  · rw [ite_eq_right hkz]
    exact (hstrict (hcfg.strict ▸ hkz) m₁ hm₁).weaken fun _ _ _ ⟨rfl, rfl, hk', hc⟩ => ⟨rfl, rfl, rfl, hk', hc⟩

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
  exact ⟨hc_eq, fun k m hinv =>
    let ⟨R_cl, hm_cl, hrup⟩ := hcl k m hinv
    ⟨R_cl, hm_cl, fun hne => absurd hstrict0 hne, fun _ => hrup⟩⟩

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
  exact ⟨hc_eq, fun k m hinv =>
    let ⟨R_cl, hm_cl, hstrict⟩ := hcl k m hinv
    ⟨R_cl, hm_cl, fun _ => hstrict, fun h0 => absurd h0 hstrict_ne⟩⟩

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
  ac_rfl

theorem sep_rearrange_arrays (RW KS U L A R : Mem 64 → Prop) :
    (RW ⋆ (KS ⋆ (U ⋆ (L ⋆ (A ⋆ R))))) = (KS ⋆ (U ⋆ (L ⋆ (A ⋆ (RW ⋆ R))))) := by
  ac_rfl

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
  refine call_br_check_clause_zeroTerm hfn_clause
    (by rwa [hP_lits, sep_rearrange_clause] at hsep) fun m₁ hm₁ => ?_
  rw [ite_eq_left hstrict0]
  rw [← sep_rearrange_clause, ← hP_lits] at hm₁
  let k1 := k.bumpCheckStats ((lits ++ [0])[0]'(by simp))
  exact br_check_clause_non_strictly_by_propagation_ok (k := k1) hfn_rup hk_trail hct
    ⟨R_lits, hP_lits⟩ haids_ro hlits_valid haids_valid hcap htrail_len hm₁
    fun m' sr sla trail_all hlen hm' hent => ⟨rfl, hpost m' sr sla trail_all hlen hm' hent⟩

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
    obtain ⟨R_arr, hP⟩ := hP_arrays
    exact ⟨hcfg, _, by rwa [hP, sep_rearrange_arrays] at hm⟩
  · intro id hid_lo hid_hi hused
    obtain ⟨hc_eq, hct, ⟨R_lits, hP_lits⟩, haids_ro, hlits_valid, haids_valid, hcap⟩ :=
      hsteps id hid_lo hid_hi hused
    refine ⟨hc_eq, fun k m ⟨hcfg, hk_te, trail_free, htf_len, hm⟩ =>
      ⟨_, by rwa [hP_lits, sep_rearrange_clause] at hm, fun m₁ hm₁ => ?_⟩⟩
    let k1 := k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))
    have hk1_cfg : k1.SameConfig k₀ := hcfg.bumpCheckStats _
    rw [← sep_rearrange_clause, ← hP_lits, ← hk1_cfg.values_begin, ← hk1_cfg.trail_begin] at hm₁
    refine br_check_clause_non_strictly_by_propagation_ok (k := k1) hfn_rup
      (by simp [k1, KernelFields.bumpCheckStats, hk_te, hcfg.trail_begin])
      (by rwa [hk1_cfg.literals_begin]) ⟨R_lits, hP_lits⟩ haids_ro hlits_valid haids_valid
      (htf_len ▸ hcap) (htf_len ▸ htrail_len) hm₁
      fun m' sr sla trail_all hlen_all hm' hent_cl =>
        ⟨rfl, rfl, ⟨{ k1 with trail_end := k1.trail_begin, stat_resolved := sr, stat_lit_assigned := sla },
          by cases hk1_cfg; constructor <;> assumption, hk1_cfg.trail_begin,
          trail_all, hlen_all.trans htf_len, by rwa [← hk1_cfg.values_begin, ← hk1_cfg.trail_begin]⟩, hent_cl⟩

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

/-! ## 7. Option B & Unified Integration: Strict Resolution (`strict ≠ 0`) and Full Soundness -/

/-- Bridge lemma connecting `ClauseTable` on `s.formula` and `entailsClause_toCNF_of_getElem?_formula`
directly to `ValidAntecedent max_var s.toCNF literals_begin P_ro aid`. -/
theorem validAntecedent_of_clauseTable {max_var : Nat} {s : State} {literals_begin : BitVec 64}
    {lit_ptrs : List (BitVec 64)} {P_ro : Mem 64 → Prop} {aid : BitVec 64}
    (hct : ClauseTable max_var literals_begin lit_ptrs s.formula P_ro)
    (hnontaut : ∀ (j : Nat) (c : CNF.Clause Nat), s.formula[j]? = some (some c) → ClauseNonTautological c)
    (hne0 : aid ≠ 0)
    (haid : aid.toNat < lit_ptrs.length)
    (hptr : lit_ptrs[aid.toNat] ≠ 0) :
    ValidAntecedent max_var s.toCNF literals_begin P_ro aid := by
  have hpos : 0 < aid.toNat :=
    Nat.pos_of_ne_zero fun h0 => hne0 (BitVec.eq_of_toNat_eq h0)
  exact hct.validAntecedent ⟨emp, (sep_emp P_ro).symm⟩ haid hpos hptr
    (fun c hc => ⟨hnontaut (aid.toNat - 1) c hc, entailsClause_toCNF_of_getElem?_formula hc⟩)

/-- Concrete `call` specification for `br_check_clause` in strict resolution mode (`k.strict ≠ 0`),
combining `call_br_check_clause_zeroTerm` and `call_br_check_clause_strictly_by_resolution`. -/
theorem call_br_check_clause_strict {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64}
    {post : Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    {max_var n : Nat} {f : CNF Nat}
    {st id literals antecedents : BitVec 64} {k : KernelFields}
    {clause_lits ants : List (BitVec 64)} {P_ro : Mem 64 → Prop}
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hfn_strict : e.lookup br_check_clause_strictly_by_resolution.1 =
      some br_check_clause_strictly_by_resolution.2)
    (hstrict_ne : k.strict ≠ 0)
    (hlen : max_var < n)
    (hn_bound : n < 2 ^ 64)
    (hants_bound : 4 * ants.length < 2 ^ 64)
    (hants_int : ∀ x ∈ ants, IsInt32 x ∧ x ≠ 0)
    (hants_valid : ∀ aid ∈ ants, aid.slt 0 = false →
      ValidAntecedent max_var f k.literals_begin P_ro aid)
    (hclause_valid : ∀ x ∈ clause_lits, IsValidLit max_var x)
    (hmem : m =⋆ byte1Array k.marks_begin (List.replicate n 0) ⋆ (kernelState st k ⋆ P_ro))
    (hsub_ants : ∃ R', P_ro = (ZeroTermInts antecedents ants ⋆ R'))
    (hsub_lits : ∃ R', P_ro = (ZeroTermInts literals clause_lits ⋆ R'))
    (hpost : CNF.EntailsClause f (toClause clause_lits) →
      ∀ m',
        (m' =⋆ byte1Array k.marks_begin (List.replicate n 0) ⋆
          (kernelState st
            { (k.bumpCheckStats ((clause_lits ++ [0])[0]'(by simp))) with
              stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆ P_ro)) →
        post t m' []) :
    call lratFailExt e B br_check_clause.1 t m [st, id, literals, antecedents] post := by
  obtain ⟨R_lits, hP_lits⟩ := hsub_lits
  refine call_br_check_clause_zeroTerm hfn_clause
    (by rwa [hP_lits, sep_rearrange_clause] at hmem) fun m₁ hm₁ => ?_
  rw [ite_eq_right hstrict_ne]
  rw [← sep_rearrange_clause, ← hP_lits] at hm₁
  let k1 := k.bumpCheckStats ((clause_lits ++ [0])[0]'(by simp))
  exact call_br_check_clause_strictly_by_resolution (k := k1) hfn_strict hlen hn_bound
    hants_bound hants_int hants_valid hclause_valid hm₁ hsub_ants ⟨R_lits, hP_lits⟩
    fun hent m' hm' => ⟨rfl, hpost hent m' hm'⟩

/-- Memory invariant maintained across iterations of `br_check_proof` in strict resolution mode (`strict ≠ 0`). -/
def StrictMemInv (n : Nat) (st : BitVec 64) (k₀ : KernelFields)
    (P_ro : Mem 64 → Prop) (k : KernelFields) (m : Mem 64) : Prop :=
  k.SameConfig k₀ ∧
  (m =⋆ byte1Array k₀.marks_begin (List.replicate n 0) ⋆ (kernelState st k ⋆ P_ro))

/-- End-to-end `call` soundness theorem for `br_check_proof` in Option B (`k₀.strict ≠ 0`),
connecting `br_check_proof`, `br_check_clause`, and `call_br_check_clause_strictly_by_resolution`
to `Std.Sat.CNF.Unsat cnf₀`. -/
theorem call_br_check_proof_resolution {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {max_var n : Nat} {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable anteTable : List (List (BitVec 64))}
    {P_ro : Mem 64 → Prop}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hfn_strict : e.lookup br_check_clause_strictly_by_resolution.1 =
      some br_check_clause_strictly_by_resolution.2)
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
    (hlen : max_var < n)
    (hn_bound : n < 2 ^ 64)
    (hP_arrays : ∃ R_arr, P_ro = (int4Array k₀.used_begin usedWords ⋆
      (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R_arr))))
    (hsep0 : m₀ =⋆ byte1Array k₀.marks_begin (List.replicate n 0) ⋆ (kernelState st k₀ ⋆ P_ro))
    (hsteps : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      let lits := litsTable.getD id.toNat []
      let ants := anteTable.getD id.toNat []
      let s := stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)
      clauseAt clauses id.toNat = toClause lits ∧
      4 * ants.length < 2 ^ 64 ∧
      (∀ x ∈ ants, IsInt32 x ∧ x ≠ 0) ∧
      (∀ aid ∈ ants, aid.slt 0 = false →
        ValidAntecedent max_var s.toCNF k₀.literals_begin P_ro aid) ∧
      (∀ x ∈ lits, IsValidLit max_var x) ∧
      (∃ R_lits, P_ro = (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len)) lits ⋆ R_lits)) ∧
      (∃ R_ants, P_ro = (ZeroTermInts (antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)) ants ⋆ R_ants))) :
    call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t' m' rets =>
        t' = t₀ ∧ rets = [] ∧
        (∃ k', StrictMemInv n st k₀ P_ro k' m') ∧
        cnf₀.Unsat) := by
  refine call_br_check_proof_strict (litsTable := litsTable)
    (InvMem := StrictMemInv n st k₀ P_ro)
    hfn_proof hfn_clause hstrict_ne hchecking hforward hfst_pos hfst_le hemp_lt
    hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause
    ⟨KernelFields.SameConfig.refl k₀, hsep0⟩ ?_ ?_
  · rintro k m ⟨hcfg, hm⟩
    obtain ⟨R_arr, hP⟩ := hP_arrays
    exact ⟨hcfg, _, by rwa [hP, sep_rearrange_arrays] at hm⟩
  · intro id hid_lo hid_hi hused
    obtain ⟨hc_eq, hants_bound, hants_int, hants_valid, hlits_valid, ⟨R_lits, hP_lits⟩, hsub_ants⟩ :=
      hsteps id hid_lo hid_hi hused
    refine ⟨hc_eq, fun k m ⟨hcfg, hm⟩ =>
      ⟨_, by rwa [hP_lits, sep_rearrange_clause] at hm, fun m₁ hm₁ => ?_⟩⟩
    let k1 := k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))
    have hk1_cfg : k1.SameConfig k₀ := hcfg.bumpCheckStats _
    rw [← sep_rearrange_clause, ← hP_lits, ← hk1_cfg.marks_begin] at hm₁
    refine call_br_check_clause_strictly_by_resolution (k := k1) hfn_strict hlen hn_bound
      hants_bound hants_int (by rwa [hk1_cfg.literals_begin]) hlits_valid hm₁ hsub_ants ⟨R_lits, hP_lits⟩
      fun hent_cl m' hm' =>
        ⟨rfl, rfl, ⟨{ k1 with stat_resolved := k1.stat_resolved + BitVec.ofNat 64 (anteTable.getD id.toNat []).length },
          by cases hk1_cfg; constructor <;> assumption, by rwa [← hk1_cfg.marks_begin]⟩, hent_cl⟩

/-- End-to-end `Interp.run` soundness corollary for Option B (`k₀.strict ≠ 0`):
any terminating execution of `br_check_proof` in strict resolution mode
guarantees `cnf₀.Unsat` (`Std.Sat.CNF.Unsat cnf₀`). -/
theorem br_check_proof_strict_run_unsat {e : Env} {t₀ t' : Trace 64} {m₀ m' : Mem 64}
    {max_var n : Nat} {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable anteTable : List (List (BitVec 64))}
    {P_ro : Mem 64 → Prop}
    {lf l' : Locals 64} {fill : UInt8} {fuel : Nat} {o o' : List (BitVec 64)}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hfn_strict : e.lookup br_check_clause_strictly_by_resolution.1 =
      some br_check_clause_strictly_by_resolution.2)
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
    (hlen : max_var < n)
    (hn_bound : n < 2 ^ 64)
    (hP_arrays : ∃ R_arr, P_ro = (int4Array k₀.used_begin usedWords ⋆
      (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R_arr))))
    (hsep0 : m₀ =⋆ byte1Array k₀.marks_begin (List.replicate n 0) ⋆ (kernelState st k₀ ⋆ P_ro))
    (hsteps : ∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      let lits := litsTable.getD id.toNat []
      let ants := anteTable.getD id.toNat []
      let s := stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)
      clauseAt clauses id.toNat = toClause lits ∧
      4 * ants.length < 2 ^ 64 ∧
      (∀ x ∈ ants, IsInt32 x ∧ x ≠ 0) ∧
      (∀ aid ∈ ants, aid.slt 0 = false →
        ValidAntecedent max_var s.toCNF k₀.literals_begin P_ro aid) ∧
      (∀ x ∈ lits, IsValidLit max_var x) ∧
      (∃ R_lits, P_ro = (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len)) lits ⋆ R_lits)) ∧
      (∃ R_ants, P_ro = (ZeroTermInts (antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)) ants ⋆ R_ants)))
    (hlf : putManyZip br_check_proof.2.params [st] ∅ = some lf)
    (hrun : run e fill fuel br_check_proof.2.body t₀ m₀ lf o (fun _ _ _ _ => none) =
      some (t', m', l', o')) :
    cnf₀.Unsat := by
  have hcall := call_br_check_proof_resolution (B := 0) (t₀ := t₀)
    (litsTable := litsTable) (anteTable := anteTable)
    hfn_proof hfn_clause hfn_strict hstrict_ne hchecking hforward hfst_pos hfst_le hemp_lt
    hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause hlen hn_bound
    hP_arrays hsep0 hsteps
  obtain ⟨_, _, _, _, _, hunsat⟩ :=
    run_body_of_call (Handler.ok_none lratFailExt) hcall hfn_proof hlf hrun
  exact hunsat

/-- Unified memory invariant for `br_check_proof` supporting both `k₀.strict = 0` (Option A: RUP)
and `k₀.strict ≠ 0` (Option B: strict resolution). -/
def FullMemInv (max_var n trail_cap : Nat) (st : BitVec 64) (k₀ : KernelFields)
    (P_ro : Mem 64 → Prop) (k : KernelFields) (m : Mem 64) : Prop :=
  if k₀.strict = 0 then
    RupMemInv max_var trail_cap st k₀ P_ro k m
  else
    StrictMemInv n st k₀ P_ro k m

/-- Unified end-to-end `call` soundness theorem for `br_check_proof` covering both
`k₀.strict = 0` (Option A: RUP propagation) and `k₀.strict ≠ 0` (Option B: strict resolution). -/
theorem call_br_check_proof_full {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {max_var n : Nat} {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable anteTable : List (List (BitVec 64))}
    {P_ro : Mem 64 → Prop}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hfn_rup : e.lookup br_check_clause_non_strictly_by_propagation.1 =
      some br_check_clause_non_strictly_by_propagation.2)
    (hfn_strict : e.lookup br_check_clause_strictly_by_resolution.1 =
      some br_check_clause_strictly_by_resolution.2)
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
    (hP_arrays : ∃ R_arr, P_ro = (int4Array k₀.used_begin usedWords ⋆
      (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R_arr))))
    (hrup_case : k₀.strict = 0 →
      k₀.trail_end = k₀.trail_begin ∧
      4 * trail_free0.length < 2 ^ 64 ∧
      (m₀ =⋆ (byte1Array k₀.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k₀.trail_begin trail_free0) ⋆
        (kernelState st k₀ ⋆ P_ro)) ∧
      (∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
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
        lits.length + aids.length ≤ trail_free0.length))
    (hstrict_case : k₀.strict ≠ 0 →
      max_var < n ∧
      n < 2 ^ 64 ∧
      (m₀ =⋆ byte1Array k₀.marks_begin (List.replicate n 0) ⋆ (kernelState st k₀ ⋆ P_ro)) ∧
      (∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
          (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
        isStepUsed k₀.trimming usedWords id.toNat = true →
        let lits := litsTable.getD id.toNat []
        let ants := anteTable.getD id.toNat []
        let s := stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
          (id.toNat - k₀.first_proof_id.toNat)
        clauseAt clauses id.toNat = toClause lits ∧
        4 * ants.length < 2 ^ 64 ∧
        (∀ x ∈ ants, IsInt32 x ∧ x ≠ 0) ∧
        (∀ aid ∈ ants, aid.slt 0 = false →
          ValidAntecedent max_var s.toCNF k₀.literals_begin P_ro aid) ∧
        (∀ x ∈ lits, IsValidLit max_var x) ∧
        (∃ R_lits, P_ro = (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len)) lits ⋆ R_lits)) ∧
        (∃ R_ants, P_ro = (ZeroTermInts (antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)) ants ⋆ R_ants)))) :
    call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t' m' rets =>
        t' = t₀ ∧ rets = [] ∧
        (∃ k', FullMemInv max_var n trail_free0.length st k₀ P_ro k' m') ∧
        cnf₀.Unsat) := by
  by_cases hstrict0 : k₀.strict = 0
  · obtain ⟨hk_trail, htrail_len, hsep0, hsteps⟩ := hrup_case hstrict0
    refine (call_br_check_proof_rup (litsTable := litsTable) (anteTable := anteTable)
      hfn_proof hfn_clause hfn_rup hstrict0 hchecking hforward hk_trail hfst_pos hfst_le hemp_lt
      hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause htrail_len hP_arrays hsep0 hsteps).weaken ?_
    rintro _ _ _ ⟨rfl, rfl, ⟨k', hk'⟩, hunsat⟩
    exact ⟨rfl, rfl, ⟨k', by simpa [FullMemInv, ite_eq_left (by simpa using hstrict0)] using hk'⟩, hunsat⟩
  · obtain ⟨hlen, hn_bound, hsep0, hsteps⟩ := hstrict_case hstrict0
    refine (call_br_check_proof_resolution (litsTable := litsTable) (anteTable := anteTable)
      hfn_proof hfn_clause hfn_strict hstrict0 hchecking hforward hfst_pos hfst_le hemp_lt
      hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause hlen hn_bound hP_arrays hsep0 hsteps).weaken ?_
    rintro _ _ _ ⟨rfl, rfl, ⟨k', hk'⟩, hunsat⟩
    exact ⟨rfl, rfl, ⟨k', by simpa [FullMemInv, ite_eq_right (by simpa using hstrict0)] using hk'⟩, hunsat⟩

/-- Unified end-to-end `Interp.run` soundness corollary for `br_check_proof` covering both
`k₀.strict = 0` (Option A) and `k₀.strict ≠ 0` (Option B). -/
theorem br_check_proof_full_run_unsat {e : Env} {t₀ t' : Trace 64} {m₀ m' : Mem 64}
    {max_var n : Nat} {st : BitVec 64} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List (BitVec 64)}
    {cnf₀ : CNF Nat} {clauses : List (CNF.Clause Nat)}
    {litsTable anteTable : List (List (BitVec 64))}
    {P_ro : Mem 64 → Prop}
    {lf l' : Locals 64} {fill : UInt8} {fuel : Nat} {o o' : List (BitVec 64)}
    (hfn_proof : e.lookup br_check_proof.1 = some br_check_proof.2)
    (hfn_clause : e.lookup br_check_clause.1 = some br_check_clause.2)
    (hfn_rup : e.lookup br_check_clause_non_strictly_by_propagation.1 =
      some br_check_clause_non_strictly_by_propagation.2)
    (hfn_strict : e.lookup br_check_clause_strictly_by_resolution.1 =
      some br_check_clause_strictly_by_resolution.2)
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
    (hP_arrays : ∃ R_arr, P_ro = (int4Array k₀.used_begin usedWords ⋆
      (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R_arr))))
    (hrup_case : k₀.strict = 0 →
      k₀.trail_end = k₀.trail_begin ∧
      4 * trail_free0.length < 2 ^ 64 ∧
      (m₀ =⋆ (byte1Array k₀.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k₀.trail_begin trail_free0) ⋆
        (kernelState st k₀ ⋆ P_ro)) ∧
      (∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
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
        lits.length + aids.length ≤ trail_free0.length))
    (hstrict_case : k₀.strict ≠ 0 →
      max_var < n ∧
      n < 2 ^ 64 ∧
      (m₀ =⋆ byte1Array k₀.marks_begin (List.replicate n 0) ⋆ (kernelState st k₀ ⋆ P_ro)) ∧
      (∀ (id : BitVec 64) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
          (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
        isStepUsed k₀.trimming usedWords id.toNat = true →
        let lits := litsTable.getD id.toNat []
        let ants := anteTable.getD id.toNat []
        let s := stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
          (id.toNat - k₀.first_proof_id.toNat)
        clauseAt clauses id.toNat = toClause lits ∧
        4 * ants.length < 2 ^ 64 ∧
        (∀ x ∈ ants, IsInt32 x ∧ x ≠ 0) ∧
        (∀ aid ∈ ants, aid.slt 0 = false →
          ValidAntecedent max_var s.toCNF k₀.literals_begin P_ro aid) ∧
        (∀ x ∈ lits, IsValidLit max_var x) ∧
        (∃ R_lits, P_ro = (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len)) lits ⋆ R_lits)) ∧
        (∃ R_ants, P_ro = (ZeroTermInts (antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)) ants ⋆ R_ants))))
    (hlf : putManyZip br_check_proof.2.params [st] ∅ = some lf)
    (hrun : run e fill fuel br_check_proof.2.body t₀ m₀ lf o (fun _ _ _ _ => none) =
      some (t', m', l', o')) :
    cnf₀.Unsat := by
  have hcall := call_br_check_proof_full (B := 0) (t₀ := t₀) (max_var := max_var) (n := n)
    (trail_free0 := trail_free0) (litsTable := litsTable) (anteTable := anteTable)
    hfn_proof hfn_clause hfn_rup hfn_strict hchecking hforward hfst_pos hfst_le hemp_lt
    hused_len hused_int32 hlits_len hante_len hempty_used hempty_clause hP_arrays hrup_case hstrict_case
  obtain ⟨_, _, _, _, _, hunsat⟩ :=
    run_body_of_call (Handler.ok_none lratFailExt) hcall hfn_proof hlf hrun
  exact hunsat

end Kraken.Bedrock2.Test
