module

public import Kraken.Bedrock2.Test.LratTrimCheckProof
import all Kraken.Mem
import all Kraken.Separation

@[expose] public section

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace Kraken.Bedrock2.Test

/-! ## 1. Concrete Checker Environment -/

/-- Concrete Bedrock2 function environment containing all LRAT trimming and checking functions. -/
def lratEnv : Env :=
  lratTrimEntry ++ lratTrimInternal

private theorem lookup_lratEnv_proof :
    lratEnv.lookup br_check_proof.1 = some br_check_proof.2 := rfl

private theorem lookup_lratEnv_clause :
    lratEnv.lookup br_check_clause.1 = some br_check_clause.2 := rfl

private theorem lookup_lratEnv_rup :
    lratEnv.lookup br_check_clause_non_strictly_by_propagation.1 =
      some br_check_clause_non_strictly_by_propagation.2 := rfl

private theorem lookup_lratEnv_strict :
    lratEnv.lookup br_check_clause_strictly_by_resolution.1 =
      some br_check_clause_strictly_by_resolution.2 := rfl

/-! ## 2. Bundled Representation Predicate (`LratRepr` & `ValidLratMemory`) -/

/-- Structured description of the C LRAT checker's initial memory layout for formula `cnf₀`. -/
structure LratRepr (cnf₀ : CNF Nat) where
  max_var : Nat
  n : Nat
  k₀ : KernelFields
  usedWords : List (BitVec 64)
  litsPtrs : List (BitVec 64)
  antePtrs : List (BitVec 64)
  trail_free0 : List (BitVec 64)
  litsTable : List (List (BitVec 64))
  anteTable : List (List (BitVec 64))
  R_clauses : Mem 64 → Prop

/-- Read-only memory region for `usedWords`, `litsPtrs`, `antePtrs`, and clause/antecedent arrays. -/
def LratRepr.roMem {cnf₀ : CNF Nat} (r : LratRepr cnf₀) : Mem 64 → Prop :=
  int4Array r.k₀.used_begin r.usedWords ⋆
    (word8Array r.k₀.literals_begin r.litsPtrs ⋆
      (word8Array r.k₀.antecedents_begin r.antePtrs ⋆ r.R_clauses))

/-- Well-formedness of an `LratRepr cnf₀` at kernel-state pointer `st` in memory `m₀`.
Captures only the syntactic/memory representation of `cnf₀`, proof steps, and scratch buffers,
supporting both strict (`strict ≠ 0`) and non-strict (`strict = 0`) and both trimmed
(`trimming ≠ 0`) and untrimmed (`trimming = 0`) modes. -/
structure LratRepr.Valid {cnf₀ : CNF Nat} (r : LratRepr cnf₀) (st : BitVec 64) (m₀ : Mem 64) : Prop where
  checking : r.k₀.checking ≠ 0
  forward : r.k₀.forward = 0
  fst_pos : 0 < r.k₀.first_proof_id.toNat
  fst_le : r.k₀.first_proof_id.toNat ≤ r.k₀.empty_clause.toNat
  emp_lt : r.k₀.empty_clause.toNat + 1 < 2 ^ 31
  cnf_size : cnf₀.clauses.size + 1 = r.k₀.first_proof_id.toNat
  used_len : r.k₀.empty_clause.toNat < r.usedWords.length
  used_int32 : ∀ i (hi : i < r.usedWords.length), IsInt32 r.usedWords[i]
  lits_len : r.k₀.empty_clause.toNat < r.litsPtrs.length
  ante_len : r.k₀.empty_clause.toNat < r.antePtrs.length
  empty_used : isStepUsed r.k₀.trimming r.usedWords r.k₀.empty_clause.toNat = true
  empty_lits : r.litsTable.getD r.k₀.empty_clause.toNat [] = []
  orig_clauses : ∀ i, 0 < i → i < r.k₀.first_proof_id.toNat →
    r.litsPtrs.getD i 0 ≠ 0 →
      let lits := r.litsTable.getD i []
      cnf₀.clauses[i - 1]? = some (toClause lits) ∧
      (∀ x ∈ lits, IsValidLit r.max_var x) ∧
      (∃ R, r.R_clauses = (ZeroTermInts (r.litsPtrs.getD i 0) lits ⋆ R))
  proof_steps : ∀ i, r.k₀.first_proof_id.toNat ≤ i → i ≤ r.k₀.empty_clause.toNat →
    if isStepUsed r.k₀.trimming r.usedWords i then
      let lits := r.litsTable.getD i []
      let ants := r.anteTable.getD i []
      (∀ x ∈ lits, IsValidLit r.max_var x) ∧
      (r.k₀.strict ≠ 0 → ClauseNonTautological (toClause lits)) ∧
      (∃ R, r.R_clauses = (ZeroTermInts (r.litsPtrs.getD i 0) lits ⋆ R)) ∧
      (∃ R, r.R_clauses = (ZeroTermInts (r.antePtrs.getD i 0) ants ⋆ R)) ∧
      (∀ aid ∈ ants, IsInt32 aid ∧ aid ≠ 0 ∧
        (aid.slt 0 = false → aid.toNat < i ∧ r.litsPtrs.getD aid.toNat 0 ≠ 0))
    else
      r.litsPtrs.getD i 0 = 0
  mode_mem :
    if r.k₀.strict = 0 then
      r.k₀.trail_end = r.k₀.trail_begin ∧
      4 * r.trail_free0.length < 2 ^ 64 ∧
      (m₀ =⋆ (byte1Array r.k₀.values_begin (assignBytes r.max_var Assignment.empty) ⋆
          int4Array r.k₀.trail_begin r.trail_free0) ⋆
        (kernelState st r.k₀ ⋆ r.roMem)) ∧
      (∀ i, r.k₀.first_proof_id.toNat ≤ i → i ≤ r.k₀.empty_clause.toNat →
        isStepUsed r.k₀.trimming r.usedWords i = true →
        (r.litsTable.getD i []).length + (r.anteTable.getD i []).length ≤ r.trail_free0.length)
    else
      r.max_var < r.n ∧
      r.n < 2 ^ 64 ∧
      (∀ c ∈ cnf₀.clauses, ClauseNonTautological c) ∧
      (m₀ =⋆ byte1Array r.k₀.marks_begin (List.replicate r.n 0) ⋆
        (kernelState st r.k₀ ⋆ r.roMem)) ∧
      (∀ i, r.k₀.first_proof_id.toNat ≤ i → i ≤ r.k₀.empty_clause.toNat →
        isStepUsed r.k₀.trimming r.usedWords i = true →
        4 * (r.anteTable.getD i []).length < 2 ^ 64)

/-- A memory state `m₀` at kernel-state pointer `st` validly represents an LRAT check instance
for the input formula `cnf₀`. -/
def ValidLratMemory (cnf₀ : CNF Nat) (st : BitVec 64) (m₀ : Mem 64) : Prop :=
  ∃ r : LratRepr cnf₀, r.Valid st m₀

/-! ## 3. Clause Table and Antecedent Bridge Lemmas -/

private theorem toClause_nil : toClause [] = .empty :=
  CNF.Clause.ext (by simp)

private theorem clauseAt_map_toClause (xs : List (List (BitVec 64))) (i : Nat) :
    clauseAt (xs.map toClause) i = toClause (xs.getD i []) := by
  unfold clauseAt
  by_cases hi : i < xs.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using (by omega : xs.length ≤ i)),
      toClause_nil]

private theorem roMem_sub_zeroTerm {cnf₀ : CNF Nat} (r : LratRepr cnf₀)
    {p : BitVec 64} {xs : List (BitVec 64)}
    (h : ∃ R, r.R_clauses = (ZeroTermInts p xs ⋆ R)) :
    ∃ R, r.roMem = (ZeroTermInts p xs ⋆ R) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨int4Array r.k₀.used_begin r.usedWords ⋆
      (word8Array r.k₀.literals_begin r.litsPtrs ⋆
        (word8Array r.k₀.antecedents_begin r.antePtrs ⋆ R)), ?_⟩
  rw [LratRepr.roMem, hR,
    sep_comm_l (word8Array r.k₀.antecedents_begin r.antePtrs),
    sep_comm_l (word8Array r.k₀.literals_begin r.litsPtrs),
    sep_comm_l (int4Array r.k₀.used_begin r.usedWords)]

private theorem roMem_sub_litsTake {cnf₀ : CNF Nat} (r : LratRepr cnf₀) (k : Nat) :
    ∃ R, r.roMem = (word8Array r.k₀.literals_begin (r.litsPtrs.take k) ⋆ R) := by
  refine ⟨int4Array r.k₀.used_begin r.usedWords ⋆
      (word8Array (r.k₀.literals_begin + BitVec.ofNat 64 (8 * (r.litsPtrs.take k).length))
        (r.litsPtrs.drop k) ⋆
        (word8Array r.k₀.antecedents_begin r.antePtrs ⋆ r.R_clauses)), ?_⟩
  unfold LratRepr.roMem
  conv => lhs; rw [← List.take_append_drop k r.litsPtrs, word8Array_append]
  rw [sep_assoc (word8Array r.k₀.literals_begin (r.litsPtrs.take k)),
    sep_comm_l (int4Array r.k₀.used_begin r.usedWords)]

private theorem getD_eq_getElem {α : Type _} {xs : List α} {i : Nat} {d : α}
    (hi : i < xs.length) : xs.getD i d = xs[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem LratRepr.Valid.clauseTable {cnf₀ : CNF Nat} {r : LratRepr cnf₀}
    {st : BitVec 64} {m₀ : Mem 64} (hr : r.Valid st m₀)
    {id : BitVec 64} (hid_hi : id.toNat ≤ r.k₀.empty_clause.toNat) :
    ClauseTable r.max_var r.k₀.literals_begin (r.litsPtrs.take id.toNat)
      (stateAt cnf₀ r.k₀.first_proof_id.toNat r.k₀.trimming r.usedWords
        (r.litsTable.map toClause) (id.toNat - r.k₀.first_proof_id.toNat)).formula
      r.roMem := by
  refine ⟨roMem_sub_litsTake r id.toNat, fun aid haid hpos hne => ?_⟩
  have haid_id : aid < id.toNat := by
    simp only [List.length_take] at haid
    omega
  have haid_len : aid < r.litsPtrs.length := by
    have := hr.lits_len
    omega
  have hptr_eq : (r.litsPtrs.take id.toNat)[aid] = r.litsPtrs[aid] := List.getElem_take
  have hgetD : r.litsPtrs.getD aid 0 = r.litsPtrs[aid] := getD_eq_getElem haid_len
  rw [hptr_eq] at hne ⊢
  by_cases hlt : aid < r.k₀.first_proof_id.toNat
  · obtain ⟨hcnf, hvalid, hsub⟩ := hr.orig_clauses aid hpos hlt (by rwa [hgetD])
    obtain ⟨R, hR⟩ := roMem_sub_zeroTerm r hsub
    refine ⟨r.litsTable.getD aid [], R, ?_, hvalid, ?_⟩
    · rwa [← hgetD]
    · have hj : aid - 1 < cnf₀.clauses.size := by have := hr.cnf_size; omega
      rw [getElem?_formula_stateAt_of_lt _ _ _ _ _ _ hj]
      rw [Array.getElem?_eq_getElem hj] at hcnf
      exact congrArg some (congrArg some (Option.some.inj hcnf))
  · have hid_lo_aid : r.k₀.first_proof_id.toNat ≤ aid := by omega
    have hle_emp : aid ≤ r.k₀.empty_clause.toNat := by omega
    have hstep := hr.proof_steps aid hid_lo_aid hle_emp
    cases hused : isStepUsed r.k₀.trimming r.usedWords aid
    · simp only [hused, Bool.false_eq_true, ↓reduceIte, hgetD] at hstep
      exact absurd hstep hne
    · simp only [hused, ↓reduceIte] at hstep
      obtain ⟨hvalid, _, hsub, _⟩ := hstep
      obtain ⟨R, hR⟩ := roMem_sub_zeroTerm r hsub
      refine ⟨r.litsTable.getD aid [], R, ?_, hvalid, ?_⟩
      · rwa [← hgetD]
      · have hidx : aid - 1 = cnf₀.clauses.size + (aid - r.k₀.first_proof_id.toNat) := by
          have := hr.cnf_size
          omega
        have hk : aid - r.k₀.first_proof_id.toNat < id.toNat - r.k₀.first_proof_id.toNat := by omega
        rw [hidx, getElem?_formula_stateAt_of_ge _ _ _ _ _ _ hk]
        have hsum : r.k₀.first_proof_id.toNat + (aid - r.k₀.first_proof_id.toNat) = aid := by omega
        rw [hsum, hused, clauseAt_map_toClause]
        rfl

private theorem LratRepr.Valid.formula_nonTautological {cnf₀ : CNF Nat} {r : LratRepr cnf₀}
    {st : BitVec 64} {m₀ : Mem 64} (hr : r.Valid st m₀) (hstrict : r.k₀.strict ≠ 0)
    {id : BitVec 64} (hid_hi : id.toNat ≤ r.k₀.empty_clause.toNat) :
    ∀ (j : Nat) (c : CNF.Clause Nat),
      (stateAt cnf₀ r.k₀.first_proof_id.toNat r.k₀.trimming r.usedWords
        (r.litsTable.map toClause) (id.toNat - r.k₀.first_proof_id.toNat)).formula[j]? =
        some (some c) →
      ClauseNonTautological c := by
  intro j c hj
  have hmode := hr.mode_mem
  rw [ite_eq_right hstrict] at hmode
  obtain ⟨_, _, hcnf_nt, _⟩ := hmode
  by_cases hj_lt : j < cnf₀.clauses.size
  · rw [getElem?_formula_stateAt_of_lt _ _ _ _ _ _ hj_lt] at hj
    cases Option.some.inj (Option.some.inj hj)
    exact hcnf_nt cnf₀.clauses[j] (Array.getElem_mem hj_lt)
  · have hj_size : j < (stateAt cnf₀ r.k₀.first_proof_id.toNat r.k₀.trimming r.usedWords
        (r.litsTable.map toClause) (id.toNat - r.k₀.first_proof_id.toNat)).formula.size := by
      by_cases hlt : j < (stateAt cnf₀ r.k₀.first_proof_id.toNat r.k₀.trimming r.usedWords
          (r.litsTable.map toClause) (id.toNat - r.k₀.first_proof_id.toNat)).formula.size
      · exact hlt
      · rw [Array.getElem?_eq_none (by omega)] at hj
        cases hj
    rw [formula_size_stateAt] at hj_size
    let k := j - cnf₀.clauses.size
    have hj_eq : j = cnf₀.clauses.size + k := by omega
    have hk_lt : k < id.toNat - r.k₀.first_proof_id.toNat := by omega
    rw [hj_eq, getElem?_formula_stateAt_of_ge _ _ _ _ _ _ hk_lt] at hj
    have hstep_idx : r.k₀.first_proof_id.toNat + k ≤ r.k₀.empty_clause.toNat := by omega
    have hstep := hr.proof_steps (r.k₀.first_proof_id.toNat + k) (by omega) hstep_idx
    cases hused : isStepUsed r.k₀.trimming r.usedWords (r.k₀.first_proof_id.toNat + k)
    · simp [hused] at hj
    · simp only [hused, ↓reduceIte] at hj hstep
      have hc : c = toClause (r.litsTable.getD (r.k₀.first_proof_id.toNat + k) []) := by
        simpa [clauseAt_map_toClause] using (Option.some.inj (Option.some.inj hj)).symm
      exact hc ▸ hstep.2.1 hstrict

/-! ## 4. Top-Level Minimalistic Soundness Theorems -/

/-- Minimalistic `call`-level soundness theorem for `br_check_proof` against `lratEnv`:
under `e.Extends lratEnv` and `ValidLratMemory cnf₀ st m₀`, any return from `br_check_proof(st)`
guarantees `cnf₀.Unsat`. -/
theorem br_check_proof_sound_call {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {cnf₀ : CNF Nat} {st : BitVec 64}
    (he : e.Extends lratEnv)
    (hm : ValidLratMemory cnf₀ st m₀) :
    call lratFailExt e B br_check_proof.1 t₀ m₀ [st]
      (fun t' _ rets => t' = t₀ ∧ rets = [] ∧ cnf₀.Unsat) := by
  obtain ⟨r, hr⟩ := hm
  refine call.weaken (call_br_check_proof_full (max_var := r.max_var) (n := r.n)
      (trail_free0 := r.trail_free0) (cnf₀ := cnf₀) (clauses := r.litsTable.map toClause)
      (litsTable := r.litsTable) (anteTable := r.anteTable) (P_ro := r.roMem)
      (he _ _ lookup_lratEnv_proof) (he _ _ lookup_lratEnv_clause)
      (he _ _ lookup_lratEnv_rup) (he _ _ lookup_lratEnv_strict)
      hr.checking hr.forward hr.fst_pos hr.fst_le hr.emp_lt
      hr.used_len hr.used_int32 hr.lits_len hr.ante_len hr.empty_used
      (by rw [clauseAt_map_toClause, hr.empty_lits, toClause_nil])
      ⟨r.R_clauses, rfl⟩ ?_ ?_) ?_
  · intro hstrict0
    have hmode := hr.mode_mem
    rw [ite_eq_left hstrict0] at hmode
    obtain ⟨hk_trail, htrail_len, hsep0, hcap⟩ := hmode
    refine ⟨hk_trail, htrail_len, hsep0, fun id hid_lo hid_hi hused => ?_⟩
    have hstep := hr.proof_steps id.toNat hid_lo hid_hi
    rw [ite_eq_left hused] at hstep
    obtain ⟨hlits_valid, _, hsub_lits, hsub_ants, haids_valid⟩ := hstep
    have hid_lits : id.toNat < r.litsPtrs.length := Nat.lt_of_le_of_lt hid_hi hr.lits_len
    have hid_ante : id.toNat < r.antePtrs.length := Nat.lt_of_le_of_lt hid_hi hr.ante_len
    refine ⟨clauseAt_map_toClause _ _, hr.clauseTable hid_hi,
      ?_, ?_, hlits_valid, ?_, hcap id.toNat hid_lo hid_hi hused⟩
    · rw [← getD_eq_getElem hid_lits]
      exact roMem_sub_zeroTerm r hsub_lits
    · rw [← getD_eq_getElem hid_ante]
      exact roMem_sub_zeroTerm r hsub_ants
    · intro aid haid
      obtain ⟨h32, hne0, hpos_aid⟩ := haids_valid aid haid
      refine ⟨h32, hne0, fun hslt => ?_⟩
      obtain ⟨hlt_id, hnz⟩ := hpos_aid hslt
      have hlen_take : (r.litsPtrs.take id.toNat).length = id.toNat :=
        List.length_take_of_le (Nat.le_of_lt hid_lits)
      refine ⟨hlen_take.symm ▸ hlt_id, ?_⟩
      rw [List.getElem_take, ← getD_eq_getElem (Nat.lt_trans hlt_id hid_lits)]
      exact hnz
  · intro hstrict_ne
    have hmode := hr.mode_mem
    rw [ite_eq_right hstrict_ne] at hmode
    obtain ⟨hlen, hn_bound, _, hsep0, hants_bound⟩ := hmode
    refine ⟨hlen, hn_bound, hsep0, fun id hid_lo hid_hi hused => ?_⟩
    have hstep := hr.proof_steps id.toNat hid_lo hid_hi
    rw [ite_eq_left hused] at hstep
    obtain ⟨hlits_valid, _, hsub_lits, hsub_ants, haids_valid⟩ := hstep
    have hid_lits : id.toNat < r.litsPtrs.length := Nat.lt_of_le_of_lt hid_hi hr.lits_len
    have hid_ante : id.toNat < r.antePtrs.length := Nat.lt_of_le_of_lt hid_hi hr.ante_len
    have hct := hr.clauseTable hid_hi
    have hnt := hr.formula_nonTautological hstrict_ne hid_hi
    refine ⟨clauseAt_map_toClause _ _, hants_bound id.toNat hid_lo hid_hi hused,
      fun aid haid => ⟨(haids_valid aid haid).1, (haids_valid aid haid).2.1⟩,
      fun aid haid hslt => ?_, hlits_valid, ?_, ?_⟩
    · obtain ⟨_, hne0, hpos_aid⟩ := haids_valid aid haid
      obtain ⟨hlt_id, hnz⟩ := hpos_aid hslt
      have hlen_take : (r.litsPtrs.take id.toNat).length = id.toNat :=
        List.length_take_of_le (Nat.le_of_lt hid_lits)
      refine validAntecedent_of_clauseTable hct hnt hne0 (hlen_take.symm ▸ hlt_id) ?_
      rw [List.getElem_take, ← getD_eq_getElem (Nat.lt_trans hlt_id hid_lits)]
      exact hnz
    · rw [← getD_eq_getElem hid_lits]
      exact roMem_sub_zeroTerm r hsub_lits
    · rw [← getD_eq_getElem hid_ante]
      exact roMem_sub_zeroTerm r hsub_ants
  · rintro t' m' rets ⟨rfl, rfl, _, hunsat⟩
    exact ⟨rfl, rfl, hunsat⟩

/-- Top-level `Exec` soundness theorem for `br_check_proof.2.body`. -/
theorem br_check_proof_sound_exec {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {lf : Locals 64} {cnf₀ : CNF Nat} {st : BitVec 64}
    (he : e.Extends lratEnv)
    (hm : ValidLratMemory cnf₀ st m₀)
    (hlf : putManyZip br_check_proof.2.params [st] ∅ = some lf) :
    Exec lratFailExt e B br_check_proof.2.body t₀ m₀ lf (fun t' _ _ => t' = t₀ ∧ cnf₀.Unsat) := by
  obtain ⟨f, hf, l₀, hl₀, hexec⟩ := br_check_proof_sound_call (B := B) (t₀ := t₀) he hm
  cases hf.symm.trans (he _ _ lookup_lratEnv_proof)
  cases hl₀.symm.trans hlf
  exact hexec.weaken fun _ _ _ ⟨_, _, ht, _, hunsat⟩ => ⟨ht, hunsat⟩

/-- Top-level `Exec` soundness theorem for calling `br_check_proof` via `.call [] br_check_proof.1 [est]`. -/
theorem br_check_proof_call_exec {e : Env} {B : Nat} {t₀ : Trace 64} {m₀ : Mem 64}
    {l : Locals 64} {est : Expr} {cnf₀ : CNF Nat} {st : BitVec 64}
    (he : e.Extends lratEnv)
    (hm : ValidLratMemory cnf₀ st m₀)
    (hest : est.eval m₀ l = some st) :
    Exec lratFailExt e B (.call [] br_check_proof.1 [est]) t₀ m₀ l
      (fun t' _ l' => t' = t₀ ∧ l' = l ∧ cnf₀.Unsat) :=
  Exec.call_cps (by simp [evalArgs, hest])
    ((br_check_proof_sound_call he hm).weaken fun _ _ _ ⟨ht, hrets, hunsat⟩ =>
      ⟨l, by subst hrets; exact putManyZip_nil l, ht, rfl, hunsat⟩)

/-- Top-level `Interp.run` soundness theorem for `br_check_proof.2.body`:
any terminating run (under the standard handler rejecting `lrat_fail`) proves `cnf₀.Unsat`. -/
theorem br_check_proof_sound_run {e : Env} {t₀ t' : Trace 64} {m₀ m' : Mem 64}
    {lf l' : Locals 64} {fill : UInt8} {fuel : Nat} {o o' : List (BitVec 64)}
    {cnf₀ : CNF Nat} {st : BitVec 64}
    (he : e.Extends lratEnv)
    (hm : ValidLratMemory cnf₀ st m₀)
    (hlf : putManyZip br_check_proof.2.params [st] ∅ = some lf)
    (hrun : run e fill fuel br_check_proof.2.body t₀ m₀ lf o (fun _ _ _ _ => none) =
      some (t', m', l', o')) :
    cnf₀.Unsat :=
  (run_of_exec (Handler.ok_none lratFailExt) (br_check_proof_sound_exec (B := 0) he hm hlf) hrun).2

/-! ## 5. Non-Vacuity Witnesses (`ValidLratMemory` on Concrete Unsatisfiable CNF) -/

private def word8Bytes : List (BitVec 64) → List UInt8
  | [] => []
  | x :: xs => Int.toBytes 8 x.toNat ++ word8Bytes xs

private def int4Bytes : List (BitVec 64) → List UInt8
  | [] => []
  | x :: xs => Int.toBytes 4 x.toNat ++ int4Bytes xs

private def byte1Bytes : List (BitVec 64) → List UInt8
  | [] => []
  | x :: xs => Int.toBytes 1 x.toNat ++ byte1Bytes xs

private theorem length_word8Bytes (xs : List (BitVec 64)) :
    (word8Bytes xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [word8Bytes, Int.toBytes_length, ih]; omega

private theorem length_int4Bytes (xs : List (BitVec 64)) :
    (int4Bytes xs).length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [int4Bytes, Int.toBytes_length, ih]; omega

private theorem length_byte1Bytes (xs : List (BitVec 64)) :
    (byte1Bytes xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [byte1Bytes, Int.toBytes_length, ih]; omega

private theorem eq_empty_At (a : BitVec 64) : Eq (([] : List UInt8).At a) = emp := by
  funext m
  simp [emp, List.At, ExtHashMap.ofList_nil]

private theorem eq_word8Bytes_At (a : BitVec 64) (xs : List (BitVec 64))
    (h : 8 * xs.length ≤ 2 ^ 64) :
    Eq ((word8Bytes xs).At a) = word8Array a xs := by
  induction xs generalizing a with
  | nil => exact eq_empty_At a
  | cons x xs ih =>
    simp only [word8Bytes, word8Array_cons]
    rw [Mem.At_append_sep _ _ _ (by rw [Int.toBytes_length, length_word8Bytes]; simp at h; omega)]
    rw [Int.toBytes_length]
    change word8 a x ⋆ Eq ((word8Bytes xs).At (a + 8)) = word8 a x ⋆ word8Array (a + 8) xs
    rw [ih (a + 8) (by simp at h; omega)]

private theorem eq_int4Bytes_At (a : BitVec 64) (xs : List (BitVec 64))
    (h : 4 * xs.length ≤ 2 ^ 64) :
    Eq ((int4Bytes xs).At a) = int4Array a xs := by
  induction xs generalizing a with
  | nil => exact eq_empty_At a
  | cons x xs ih =>
    simp only [int4Bytes, int4Array_cons]
    rw [Mem.At_append_sep _ _ _ (by rw [Int.toBytes_length, length_int4Bytes]; simp at h; omega)]
    rw [Int.toBytes_length]
    change int4 a x ⋆ Eq ((int4Bytes xs).At (a + 4)) = int4 a x ⋆ int4Array (a + 4) xs
    rw [ih (a + 4) (by simp at h; omega)]

private theorem eq_byte1Bytes_At (a : BitVec 64) (xs : List (BitVec 64))
    (h : xs.length ≤ 2 ^ 64) :
    Eq ((byte1Bytes xs).At a) = byte1Array a xs := by
  induction xs generalizing a with
  | nil => exact eq_empty_At a
  | cons x xs ih =>
    simp only [byte1Bytes, byte1Array_cons]
    rw [Mem.At_append_sep _ _ _ (by rw [Int.toBytes_length, length_byte1Bytes]; simp at h; omega)]
    rw [Int.toBytes_length]
    change byte1 a x ⋆ Eq ((byte1Bytes xs).At (a + 1)) = byte1 a x ⋆ byte1Array (a + 1) xs
    rw [ih (a + 1) (by simp at h; omega)]

private def exampleCNF : CNF Nat :=
  ⟨#[CNF.Clause.ofLiterals [(1, true)], CNF.Clause.ofLiterals [(1, false)]]⟩

private def exampleSt : BitVec 64 := 0x1000#64

private def exampleRupK : KernelFields where
  used_begin := 0x10aa#64
  antecedents_begin := 0x10da#64
  literals_begin := 0x10ba#64
  values_begin := 0x10a0#64
  marks_begin := 0
  trail_begin := 0x10a2#64
  trail_end := 0x10a2#64
  work_begin := 0
  empty_clause := 3
  first_proof_id := 3
  strict := 0
  trimming := 0
  checking := 1
  forward := 0
  stat_trimmed_cnf := 0
  stat_trimmed_prf := 0
  stat_chk_total := 0
  stat_chk_empty := 0
  stat_resolved := 0
  stat_lit_assigned := 0

private def exampleRupUsed : List (BitVec 64) := [0, 0, 0, 0]
private def exampleRupLitsPtrs : List (BitVec 64) := [0, 0x10fa#64, 0x1102#64, 0x110a#64]
private def exampleRupAntePtrs : List (BitVec 64) := [0, 0, 0, 0x110e#64]
private def exampleRupLitsTable : List (List (BitVec 64)) := [[], [1], [-1], []]
private def exampleRupAnteTable : List (List (BitVec 64)) := [[], [], [], [1, 2]]

private def exampleRupClausesBytes : List UInt8 :=
  int4Bytes [1, 0] ++ int4Bytes [-1, 0] ++ int4Bytes [0] ++ int4Bytes [1, 2, 0]

private def exampleRupBytes : List UInt8 :=
  word8Bytes exampleRupK.toList ++
  byte1Bytes [0, 0] ++
  int4Bytes [0, 0] ++
  int4Bytes exampleRupUsed ++
  word8Bytes exampleRupLitsPtrs ++
  word8Bytes exampleRupAntePtrs ++
  exampleRupClausesBytes

private def exampleRupMem : Mem 64 :=
  exampleRupBytes.At exampleSt

private def exampleRupRCl : Mem 64 → Prop :=
  ZeroTermInts 0x10fa#64 [1] ⋆
    (ZeroTermInts 0x1102#64 [-1] ⋆
      (ZeroTermInts 0x110a#64 [] ⋆ ZeroTermInts 0x110e#64 [1, 2]))

private theorem exampleRupMem_valid :
    ValidLratMemory exampleCNF exampleSt exampleRupMem := by
  refine ⟨{
    max_var := 1
    n := 0
    k₀ := exampleRupK
    usedWords := exampleRupUsed
    litsPtrs := exampleRupLitsPtrs
    antePtrs := exampleRupAntePtrs
    trail_free0 := [0, 0]
    litsTable := exampleRupLitsTable
    anteTable := exampleRupAnteTable
    R_clauses := exampleRupRCl
  }, ?_⟩
  have hcl : Eq (exampleRupClausesBytes.At 0x10fa#64) = exampleRupRCl := by
    simp only [exampleRupClausesBytes, exampleRupRCl, ZeroTermInts]
    rw [Mem.At_append_sep _ _ _ (by simp [length_int4Bytes]),
      Mem.At_append_sep _ _ _ (by simp [length_int4Bytes]),
      Mem.At_append_sep _ _ _ (by simp [length_int4Bytes])]
    simp [length_int4Bytes, eq_int4Bytes_At, sep_assoc]
  refine {
    checking := by decide
    forward := rfl
    fst_pos := by decide
    fst_le := by decide
    emp_lt := by decide
    cnf_size := by decide
    used_len := by decide
    used_int32 := fun i hi => by
      dsimp only at hi ⊢
      simp only [exampleRupUsed, List.length_cons, List.length_nil] at hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
        simp [IsInt32, exampleRupUsed]
    lits_len := by decide
    ante_len := by decide
    empty_used := by decide
    empty_lits := rfl
    orig_clauses := fun i h0 hlt _ => by
      dsimp only [exampleRupK] at hlt ⊢
      change i < 3 at hlt
      rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl <;>
        simp only [exampleRupLitsPtrs, exampleRupLitsTable, List.getD_eq_getElem?_getD,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      · refine ⟨?_, fun x hx => ?_, ⟨_, rfl⟩⟩
        · apply congrArg some (CNF.Clause.ext _)
          simp [exampleCNF, toClause, toLiteral, bvAbs]
        · simp at hx; subst hx; exact ⟨by decide, by decide, by decide, by decide⟩
      · refine ⟨?_, fun x hx => ?_,
          ⟨ZeroTermInts 0x10fa#64 [1] ⋆
            (ZeroTermInts 0x110a#64 [] ⋆ ZeroTermInts 0x110e#64 [1, 2]), ?_⟩⟩
        · apply congrArg some (CNF.Clause.ext _)
          simp [exampleCNF, toClause, toLiteral, bvAbs]
        · simp at hx; subst hx; exact ⟨by decide, by decide, by decide, by decide⟩
        · simp [exampleRupRCl, sep_comm_l]
    proof_steps := fun i hlo hhi => by
      dsimp only [exampleRupK] at hlo hhi ⊢
      change 3 ≤ i at hlo; change i ≤ 3 at hhi
      have hi : i = 3 := by omega
      subst hi
      simp [isStepUsed, exampleRupLitsTable, exampleRupAnteTable,
        exampleRupLitsPtrs, exampleRupAntePtrs]
      refine ⟨⟨ZeroTermInts 0x10fa#64 [1] ⋆
          (ZeroTermInts 0x1102#64 [-1] ⋆ ZeroTermInts 0x110e#64 [1, 2]),
          by rw [exampleRupRCl, sep_comm_l (ZeroTermInts 0x1102#64 [-1]),
            sep_comm_l (ZeroTermInts 0x10fa#64 [1])]; simp⟩,
        ⟨ZeroTermInts 0x10fa#64 [1] ⋆
          (ZeroTermInts 0x1102#64 [-1] ⋆ ZeroTermInts 0x110a#64 []),
          by rw [exampleRupRCl, ← sep_assoc, ← sep_assoc, sep_comm]; simp [ZeroTermInts, sep_assoc, emp_sep]⟩,
        by simp [IsInt32]⟩
    mode_mem := by
      simp only [exampleRupK, ↓reduceIte]
      refine ⟨trivial, by decide, ?_, fun i hlo hhi _ => ?_⟩
      · have hm : Eq (exampleRupBytes.At exampleSt) exampleRupMem := rfl
        simp only [exampleRupBytes] at hm
        have hlen : (word8Bytes exampleRupK.toList ++ byte1Bytes [0, 0] ++ int4Bytes [0, 0] ++
            int4Bytes exampleRupUsed ++ word8Bytes exampleRupLitsPtrs ++
            word8Bytes exampleRupAntePtrs ++ exampleRupClausesBytes).length ≤ 2 ^ 64 := by
          simp [exampleRupClausesBytes, length_word8Bytes, length_byte1Bytes, length_int4Bytes,
            KernelFields.toList, exampleRupUsed, exampleRupLitsPtrs, exampleRupAntePtrs]
        rw [Mem.At_append_sep _ _ _ (by simp only [List.length_append] at hlen ⊢; omega),
          Mem.At_append_sep _ _ _ (by simp only [List.length_append] at hlen ⊢; omega),
          Mem.At_append_sep _ _ _ (by simp only [List.length_append] at hlen ⊢; omega),
          Mem.At_append_sep _ _ _ (by simp only [List.length_append] at hlen ⊢; omega),
          Mem.At_append_sep _ _ _ (by simp only [List.length_append] at hlen ⊢; omega),
          Mem.At_append_sep _ _ _ (by simp only [List.length_append] at hlen ⊢; omega)] at hm
        simp only [List.length_append, length_word8Bytes, length_byte1Bytes, length_int4Bytes,
          KernelFields.toList, exampleRupUsed, exampleRupLitsPtrs, exampleRupAntePtrs,
          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at hm
        have haddrs : exampleSt + 160#64 = 0x10a0#64 ∧
            exampleSt + 162#64 = 0x10a2#64 ∧
            exampleSt + 170#64 = 0x10aa#64 ∧
            exampleSt + 186#64 = 0x10ba#64 ∧
            exampleSt + 218#64 = 0x10da#64 ∧
            exampleSt + 250#64 = 0x10fa#64 := by decide
        rw [haddrs.1, haddrs.2.1, haddrs.2.2.1, haddrs.2.2.2.1, haddrs.2.2.2.2.1, haddrs.2.2.2.2.2, hcl,
          eq_word8Bytes_At _ _ (by simp),
          eq_byte1Bytes_At _ _ (by simp),
          eq_int4Bytes_At _ _ (by simp),
          eq_int4Bytes_At _ _ (by simp),
          eq_word8Bytes_At _ _ (by simp),
          eq_word8Bytes_At _ _ (by simp)] at hm
        change (_ ⋆ _) exampleRupMem at hm
        have hab : assignBytes 1 Assignment.empty = [0, 0] := by simp
        rw [hab]
        change (byte1Array 0x10a0#64 [0, 0] ⋆ int4Array 0x10a2#64 [0, 0] ⋆
          (kernelState exampleSt exampleRupK ⋆
            (int4Array 0x10aa#64 exampleRupUsed ⋆
              (word8Array 0x10ba#64 exampleRupLitsPtrs ⋆
                (word8Array 0x10da#64 exampleRupAntePtrs ⋆ exampleRupRCl))))) exampleRupMem
        change ((((((kernelState exampleSt exampleRupK ⋆ byte1Array 0x10a0#64 [0, 0]) ⋆
            int4Array 0x10a2#64 [0, 0]) ⋆ int4Array 0x10aa#64 exampleRupUsed) ⋆
            word8Array 0x10ba#64 exampleRupLitsPtrs) ⋆ word8Array 0x10da#64 exampleRupAntePtrs) ⋆
            exampleRupRCl) exampleRupMem at hm
        rw [sep_assoc ((kernelState exampleSt exampleRupK ⋆ _) ⋆ _),
          sep_assoc ((kernelState exampleSt exampleRupK ⋆ _) ⋆ _),
          sep_assoc ((kernelState exampleSt exampleRupK ⋆ _) ⋆ _),
          sep_comm ((kernelState exampleSt exampleRupK ⋆ _) ⋆ _),
          sep_assoc (kernelState exampleSt exampleRupK),
          sep_comm (kernelState exampleSt exampleRupK)] at hm
        rw [sep_assoc (int4Array 0x10aa#64 exampleRupUsed),
          sep_assoc (int4Array 0x10aa#64 exampleRupUsed) _ exampleRupRCl,
          sep_assoc (word8Array 0x10ba#64 exampleRupLitsPtrs)] at hm
        rw [sep_comm _ (kernelState exampleSt exampleRupK ⋆ _),
          sep_comm (kernelState exampleSt exampleRupK),
          sep_assoc _ (kernelState exampleSt exampleRupK),
          sep_comm (kernelState exampleSt exampleRupK)]
        exact hm
      · change 3 ≤ i at hlo; change i ≤ 3 at hhi
        have hi : i = 3 := by omega
        subst hi
        simp [exampleRupLitsTable, exampleRupAnteTable]
  }

end Kraken.Bedrock2.Test
