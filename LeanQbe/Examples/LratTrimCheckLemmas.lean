module

public import LeanQbe.Examples.LratTrim
public import LeanQbe.Examples.LratRupLemmas
public import Kraken.SeparationTactics
import all Kraken.Mem
import all Kraken.Separation
import all Std.Sat.CNF.Basic

/-!
# Clause and proof checking (`checkClause`, `checkProof`): correctness

Ports of `call_br_check_clause_rup`, `call_br_check_clause_strict`, and `call_br_check_proof_full`
from `Kraken/Bedrock2/Test/LratTrimCheckProof.lean`. All semantic state definitions (`stateAt`,
`stepState`, `isStepUsed`, `KernelFields.bumpCheckStats`, `SameConfig`, `RupMemInv`, `StrictMemInv`,
`FullMemInv`) and entailment lemmas are reused from `LratTrimCheckProof.lean` unchanged.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratTrim

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.LratRup

/-! ## Memory and bit-vector helpers -/

theorem loaduw_int4 {a v : Val} {R : Mem 64 → Prop} {m : Mem 64} (h : (int4 a v ⋆ R) m) :
    loadVal m .l .w false a = some (v &&& 0xffffffff#64) := by
  rw [loadVal_toBytes (s := .w) h]
  have : BitVec.ofInt 64 ((v.toNat : Int).take 32) = (v.setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq; simp [Int.take]; omega
  simp only [Cls.trunc, Sz.extend, Sz.bytes]; rw [this]; congr 1; grind

theorem loaduw_zeroTerm_head {p : Val} {xs : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (ZeroTermInts p xs ⋆ R) m) :
    loadVal m .l .w false p = some (((xs ++ [0])[0]'(by simp)) &&& 0xffffffff#64) := by
  rw [zeroTermInts_split_head p xs, sep_assoc] at h
  exact loaduw_int4 h

theorem word8_eq_int4_sep (a v : Val) :
    word8 a v = (int4 a v ⋆ Eq (((Int.toBytes 8 v.toNat).drop 4).At (a + 4))) := by
  unfold word8 int4
  conv => lhs; rw [← List.take_append_drop 4 (Int.toBytes 8 v.toNat)]
  exact Mem.At_append_sep (Int.toBytes 4 v.toNat) ((Int.toBytes 8 v.toNat).drop 4) a
    (by simp [Int.toBytes_length])

theorem loadsw_word8 {a v : Val} {R : Mem 64 → Prop} {m : Mem 64} (h : (word8 a v ⋆ R) m)
    (hv : IsInt32 v) : loadVal m .l .w true a = some v := by
  rw [word8_eq_int4_sep, sep_assoc] at h
  exact loadsw_int4 h hv

theorem loadsw_kfield {st : Val} {k : KernelFields} {R : Mem 64 → Prop} {m : Mem 64} (i : Nat)
    (hi : i < 20) (h : (kernelState st k ⋆ R) m) {a : Val} (ha : a = st + BitVec.ofNat 64 (8 * i))
    (hv : IsInt32 (k.toList[i]'(by simpa [KernelFields.toList] using hi))) :
    loadVal m .l .w true a = some (k.toList[i]'(by simpa [KernelFields.toList] using hi)) := by
  subst ha
  unfold kernelState at h
  rw [word8Array_focus st k.toList (by simpa [KernelFields.toList] using hi), sep_assoc] at h
  exact loadsw_word8 h hv

theorem shl_two (x : Val) : x <<< 2 = BitVec.ofNat 64 (4 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft]; omega

theorem storel_stat_chk_total {st : Val} {k : KernelFields} {R : Mem 64 → Prop} {m : Mem 64} :
    (kernelState st k ⋆ R) m →
    storeOk m .l (st + 128) ∧
      (kernelState st { k with stat_chk_total := k.stat_chk_total + 1 } ⋆ R)
        (storeMem m .l (st + 128) (k.stat_chk_total + 1)) :=
  storel_word8Array (i := 16) (k.stat_chk_total + 1) (by simp)

theorem storel_stat_chk_empty {st : Val} {k : KernelFields} {R : Mem 64 → Prop} {m : Mem 64} :
    (kernelState st k ⋆ R) m →
    storeOk m .l (st + 136) ∧
      (kernelState st { k with stat_chk_empty := k.stat_chk_empty + 1 } ⋆ R)
        (storeMem m .l (st + 136) (k.stat_chk_empty + 1)) :=
  storel_word8Array (i := 17) (k.stat_chk_empty + 1) (by simp)

theorem bumpCheckStats_of_eq (k : KernelFields) {w₀ : Val} (h : w₀ &&& 0xffffffff#64 = 0) :
    k.bumpCheckStats w₀ =
      { k with stat_chk_total := k.stat_chk_total + 1, stat_chk_empty := k.stat_chk_empty + 1 } := by
  simp [KernelFields.bumpCheckStats, h]

theorem bumpCheckStats_of_ne (k : KernelFields) {w₀ : Val} (h : w₀ &&& 0xffffffff#64 ≠ 0) :
    k.bumpCheckStats w₀ = { k with stat_chk_total := k.stat_chk_total + 1 } := by
  unfold KernelFields.bumpCheckStats
  rw [ite_eq_right (by simp; exact h)]

/-! ## `checkClause` -/

theorem checkClause_step {Γ : Env} {Q : Post} {X : XPost} {st id literals antecedents : Val}
    {clits : List Val} {k : KernelFields} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (kernelState st k ⋆ (ZeroTermInts literals clits ⋆ R)) m)
    (hcall : ∀ m', (kernelState st (k.bumpCheckStats ((clits ++ [0])[0]'(by simp))) ⋆
        (ZeroTermInts literals clits ⋆ R)) m' →
      (k.strict ≠ 0 → Γ "br_check_clause_strictly_by_resolution" [st, id, literals, antecedents] m'
        (fun rs m'' => wp Γ Q X (.ret []) rs [] m'') X) ∧
      (k.strict = 0 → Γ "br_check_clause_non_strictly_by_propagation" [st, id, literals, antecedents] m'
        (fun rs m'' => wp Γ Q X (.ret []) rs [] m'') X)) :
    Func.spec Γ checkClause [st, id, literals, antecedents] m Q X := by
  unfold checkClause Func.spec
  wp_unfold
  refine ⟨_, loadl_kfield 16 (by decide) hm rfl, ?_⟩
  simp only [KernelFields.toList, List.getElem_cons_succ, List.getElem_cons_zero]
  have ⟨ok1, hm1⟩ := storel_stat_chk_total hm
  have hm1_z : (ZeroTermInts literals clits ⋆
      (kernelState st { k with stat_chk_total := k.stat_chk_total + 1 } ⋆ R))
      (storeMem m .l (st + 128) (k.stat_chk_total + 1)) := by
    rw [sep_comm_l] at hm1; exact hm1
  let w₀ : Val := (clits ++ [0])[0]'(by simp)
  refine ⟨ok1, _, loaduw_zeroTerm_head hm1_z, ?_⟩
  apply wp_join (fun as m2 => as = [] ∧
    (kernelState st (k.bumpCheckStats w₀) ⋆ (ZeroTermInts literals clits ⋆ R)) m2)
  · rintro _ m2 ⟨rfl, hm2⟩
    wp_unfold
    refine ⟨_, loadl_kfield 10 (by decide) hm2 rfl, ?_⟩
    simp only [KernelFields.toList, KernelFields.bumpCheckStats,
      List.getElem_cons_succ, List.getElem_cons_zero]
    refine ⟨fun hne => wp_call_of_spec ((hcall m2 hm2).1 hne),
      fun hz => wp_call_of_spec ((hcall m2 hm2).2 (Classical.not_not.1 hz))⟩
  · intro J hJ
    wp_unfold
    refine ⟨fun heq => ?_, fun hne => ?_⟩
    · refine ⟨_, loadl_kfield 17 (by decide) hm1 rfl, ?_⟩
      simp only [KernelFields.toList, List.getElem_cons_succ, List.getElem_cons_zero]
      have ⟨ok2, hm2⟩ := storel_stat_chk_empty hm1
      refine ⟨ok2, hJ [] _ ⟨rfl, ?_⟩⟩
      rw [bumpCheckStats_of_eq k heq]
      exact hm2
    · refine hJ [] _ ⟨rfl, ?_⟩
      rw [bumpCheckStats_of_ne k hne]
      exact hm1

theorem checkClause_rup_correct (Γ : Env)
    (hrup : ∀ args m Q X, LratRup.checkRupSpec args m Q X →
      Γ "br_check_clause_non_strictly_by_propagation" args m Q X) :
    ∀ args m Q X, checkClauseRupSpec args m Q X → Func.spec Γ checkClause args m Q X := by
  rintro _ m Q X ⟨st, id, literals, antecedents, mv, k, lits, aids, lit_ptrs, tf0, s, P_ro, rfl,
    hstrict0, hk_trail, hct, ⟨R_lits, hP_lits⟩, haids_ro, hlits_valid, haids_valid, hcap, htf_len,
    hsep, hQ, hX⟩
  have hm : (kernelState st k ⋆ (ZeroTermInts literals lits ⋆
      ((byte1Array k.values_begin (assignBytes mv Assignment.empty) ⋆
        int4Array k.trail_begin tf0) ⋆ R_lits))) m := by
    rw [hP_lits] at hsep; exact sep_cast hsep (by ac_rfl)
  refine checkClause_step hm fun m1 hm1 => ⟨fun hne => absurd hstrict0 hne, fun _ => ?_⟩
  refine hrup _ _ _ _ ⟨st, id, literals, antecedents, mv,
    k.bumpCheckStats ((lits ++ [0])[0]'(by simp)), lits, aids, lit_ptrs, tf0, s, P_ro,
    rfl, hk_trail, hct, ⟨R_lits, hP_lits⟩, haids_ro, hlits_valid, haids_valid, hcap, htf_len,
    by rw [hP_lits]; exact sep_cast hm1 (by ac_rfl),
    fun m' sr sla trail_all hlen hm' hent => by
      wp_unfold; exact hQ m' sr sla trail_all hlen hm' hent,
    hX⟩

theorem checkClause_strict_correct (Γ : Env)
    (hstrict : ∀ args m Q X, strictSpec args m Q X →
      Γ "br_check_clause_strictly_by_resolution" args m Q X) :
    ∀ args m Q X, checkClauseStrictSpec args m Q X → Func.spec Γ checkClause args m Q X := by
  rintro _ m Q X ⟨st, id, literals, antecedents, mv, n, f, k, clause_lits, ants, P_ro, rfl,
    hstrict_ne, hlen, hn_bound, hants_bound, hants_int, hants_valid, hclause_valid,
    hmem, hsub_ants, ⟨R_lits, hP_lits⟩, hQ, hX⟩
  have hm : (kernelState st k ⋆ (ZeroTermInts literals clause_lits ⋆
      (byte1Array k.marks_begin (List.replicate n 0) ⋆ R_lits))) m := by
    rw [hP_lits] at hmem; exact sep_cast hmem (by ac_rfl)
  refine checkClause_step hm fun m1 hm1 => ⟨fun _ => ?_, fun h0 => absurd h0 hstrict_ne⟩
  refine hstrict _ _ _ _ ⟨st, id, literals, antecedents, mv, n, f,
    k.bumpCheckStats ((clause_lits ++ [0])[0]'(by simp)), clause_lits, ants, P_ro,
    rfl, hlen, hn_bound, hants_bound, hants_int, hants_valid, hclause_valid,
    by rw [hP_lits]; exact sep_cast hm1 (by ac_rfl),
    hsub_ants, ⟨R_lits, hP_lits⟩,
    fun hent m' hm' => by wp_unfold; exact hQ hent m' hm',
    hX⟩

/-! ## `checkProof` -/

theorem fullMemInv_init {max_var n : Nat} {st : Val} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List Val} {cnf₀ : CNF Nat}
    {clauses : List (CNF.Clause Nat)} {litsTable anteTable : List (List Val)}
    {P_ro : Mem 64 → Prop} {m₀ : Mem 64}
    (pre : CheckProofPre max_var n st k₀ usedWords litsPtrs antePtrs trail_free0 cnf₀ clauses
      litsTable anteTable P_ro m₀) :
    FullMemInv max_var n trail_free0.length st k₀ P_ro k₀ m₀ := by
  unfold FullMemInv
  split
  · rename_i h0
    obtain ⟨hk_te, _, hsep0, _⟩ := pre.hrup_case h0
    exact ⟨KernelFields.SameConfig.refl k₀, hk_te, trail_free0, rfl, hsep0⟩
  · rename_i hne
    obtain ⟨_, _, hsep0, _⟩ := pre.hstrict_case hne
    exact ⟨KernelFields.SameConfig.refl k₀, hsep0⟩

theorem fullMemInv_sep {max_var n : Nat} {st : Val} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List Val} {cnf₀ : CNF Nat}
    {clauses : List (CNF.Clause Nat)} {litsTable anteTable : List (List Val)}
    {P_ro : Mem 64 → Prop} {m₀ : Mem 64}
    (pre : CheckProofPre max_var n st k₀ usedWords litsPtrs antePtrs trail_free0 cnf₀ clauses
      litsTable anteTable P_ro m₀)
    {k : KernelFields} {m : Mem 64}
    (hinv : FullMemInv max_var n trail_free0.length st k₀ P_ro k m) :
    k.SameConfig k₀ ∧
    ∃ R, (kernelState st k ⋆ (int4Array k₀.used_begin usedWords ⋆
      (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R)))) m := by
  obtain ⟨R_arr, hP⟩ := pre.hP_arrays
  unfold FullMemInv at hinv
  split at hinv
  · obtain ⟨hcfg, _, trail_free, _, hm⟩ := hinv
    exact ⟨hcfg, _, by rwa [hP, sep_rearrange_arrays] at hm⟩
  · obtain ⟨hcfg, hm⟩ := hinv
    exact ⟨hcfg, _, by rwa [hP, sep_rearrange_arrays] at hm⟩

theorem fullMemInv_checkClause {max_var n : Nat} {st : Val} {k₀ : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List Val} {cnf₀ : CNF Nat}
    {clauses : List (CNF.Clause Nat)} {litsTable anteTable : List (List Val)}
    {P_ro : Mem 64 → Prop} {m₀ : Mem 64}
    (pre : CheckProofPre max_var n st k₀ usedWords litsPtrs antePtrs trail_free0 cnf₀ clauses
      litsTable anteTable P_ro m₀)
    {id : Val} (hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
    (hid_hi : id.toNat ≤ k₀.empty_clause.toNat)
    (hused : isStepUsed k₀.trimming usedWords id.toNat = true)
    {k : KernelFields} {m : Mem 64}
    (hinv : FullMemInv max_var n trail_free0.length st k₀ P_ro k m)
    {Q : Post} {X : XPost}
    (hQ : ∀ m', (∃ k', FullMemInv max_var n trail_free0.length st k₀ P_ro k' m') →
      CNF.EntailsClause
        (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
          (id.toNat - k₀.first_proof_id.toNat)).toCNF
        (clauseAt clauses id.toNat) → Q [] m')
    (hX : ∀ as m', X "lrat_fail" as m') :
    checkClauseRupSpec
      [st, id, litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi pre.hlits_len),
        antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi pre.hante_len)] m Q X ∨
    checkClauseStrictSpec
      [st, id, litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi pre.hlits_len),
        antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi pre.hante_len)] m Q X := by
  by_cases h0 : k₀.strict = 0
  · obtain ⟨_, htrail_len, _, hsteps⟩ := pre.hrup_case h0
    obtain ⟨hc_eq, hct, hsub_lits, hsub_aids, hlits_v, haids_v, hcap⟩ :=
      hsteps id hid_lo hid_hi hused
    have hinv' : RupMemInv max_var trail_free0.length st k₀ P_ro k m := by
      unfold FullMemInv at hinv; rwa [ite_eq_left h0] at hinv
    obtain ⟨hcfg, hk_te, trail_free, htf_len, hm⟩ := hinv'
    refine Or.inl ⟨st, id, _, _, max_var, k, litsTable.getD id.toNat [],
      anteTable.getD id.toNat [], litsPtrs.take id.toNat, trail_free,
      stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat),
      P_ro, rfl, hcfg.strict.trans h0, hk_te.trans hcfg.trail_begin.symm,
      by rwa [hcfg.literals_begin], hsub_lits, hsub_aids, hlits_v, haids_v,
      htf_len ▸ hcap, htf_len ▸ htrail_len,
      by rwa [hcfg.values_begin, hcfg.trail_begin],
      fun m' sr sla trail_all hlen hm' hent => ?_, hX⟩
    let k1 := k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))
    refine hQ m' ⟨{ k1 with trail_end := k.trail_begin, stat_resolved := sr, stat_lit_assigned := sla }, ?_⟩
      (hc_eq ▸ hent)
    unfold FullMemInv; rw [ite_eq_left h0]
    have hk1 : k1.SameConfig k₀ := hcfg.bumpCheckStats _
    exact ⟨by cases hk1; constructor <;> assumption, hcfg.trail_begin, trail_all,
      hlen.trans htf_len, by rwa [← hcfg.values_begin, ← hcfg.trail_begin]⟩
  · obtain ⟨hlen, hn_bound, _, hsteps⟩ := pre.hstrict_case h0
    obtain ⟨hc_eq, hants_b, hants_i, hants_v, hlits_v, hsub_lits, hsub_ants⟩ :=
      hsteps id hid_lo hid_hi hused
    have hinv' : StrictMemInv n st k₀ P_ro k m := by
      unfold FullMemInv at hinv; rwa [ite_eq_right h0] at hinv
    obtain ⟨hcfg, hm⟩ := hinv'
    refine Or.inr ⟨st, id, _, _, max_var, n,
      (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)).toCNF,
      k, litsTable.getD id.toNat [], anteTable.getD id.toNat [], P_ro,
      rfl, hcfg.strict ▸ h0, hlen, hn_bound, hants_b, hants_i,
      by rwa [hcfg.literals_begin], hlits_v,
      by rwa [hcfg.marks_begin], hsub_ants, hsub_lits,
      fun hent m' hm' => ?_, hX⟩
    let k1 := k.bumpCheckStats (((litsTable.getD id.toNat []) ++ [0])[0]'(by simp))
    refine hQ m' ⟨{ k1 with stat_resolved := k.stat_resolved + BitVec.ofNat 64 (anteTable.getD id.toNat []).length }, ?_⟩
      (hc_eq ▸ hent)
    unfold FullMemInv; rw [ite_eq_right h0]
    have hk1 : k1.SameConfig k₀ := hcfg.bumpCheckStats _
    exact ⟨by cases hk1; constructor <;> assumption, by rwa [← hcfg.marks_begin]⟩

theorem checkProof_correct (Γ : Env)
    (hclause : ∀ args m Q X, checkClauseRupSpec args m Q X ∨ checkClauseStrictSpec args m Q X →
      Γ "br_check_clause" args m Q X) :
    ∀ args m Q X, checkProofSpec args m Q X → Func.spec Γ checkProof args m Q X := by
  rintro _ m₀ Q X ⟨max_var, n, st, k₀, usedWords, litsPtrs, antePtrs, trail_free0, cnf₀,
    clauses, litsTable, anteTable, P_ro, rfl, pre, hQ, hX⟩
  have hfst_pos := pre.hfst_pos
  have hfst_le := pre.hfst_le
  have hemp_lt := pre.hemp_lt
  unfold checkProof Func.spec
  wp_unfold
  have hinv₀ := fullMemInv_init pre
  obtain ⟨_, R₀, hm₀⟩ := fullMemInv_sep pre hinv₀
  have hemp_lt31 : k₀.empty_clause.toNat < 2 ^ 31 := by omega
  have hfst_lt31 : k₀.first_proof_id.toNat < 2 ^ 31 := by omega
  have hemp32 : IsInt32 k₀.empty_clause := isInt32_of_toNat_lt hemp_lt31
  have hfst32 : IsInt32 k₀.first_proof_id := isInt32_of_toNat_lt hfst_lt31
  refine ⟨_, loadl_kfield 12 (by decide) hm₀ rfl, _, loadl_kfield 13 (by decide) hm₀ rfl,
    _, loadsw_kfield 8 (by decide) hm₀ rfl (by simpa [KernelFields.toList] using hemp32),
    _, loadsw_kfield 9 (by decide) hm₀ rfl (by simpa [KernelFields.toList] using hfst32), ?_⟩
  simp only [KernelFields.toList, List.getElem_cons_succ, List.getElem_cons_zero]
  refine ⟨fun _ => ⟨fun _ => ?_, fun h => absurd pre.hforward h⟩,
    fun h => absurd pre.hchecking h⟩
  rw [truthy_iff _ hemp32, truthy_iff _ hfst32]
  have hemp_ne : k₀.empty_clause ≠ 0 := fun h0 => by simp [h0] at hfst_le; omega
  have hfst_ne : k₀.first_proof_id ≠ 0 := fun h0 => by simp [h0] at hfst_pos
  refine ⟨fun _ => ⟨fun _ => ?_, fun h => absurd hfst_ne h⟩, fun h => absurd hemp_ne h⟩
  refine ⟨_, loadl_kfield 11 (by decide) hm₀ rfl,
    _, loadl_kfield 0 (by decide) hm₀ (by simp),
    _, loadl_kfield 2 (by decide) hm₀ rfl,
    _, loadl_kfield 1 (by decide) hm₀ rfl, ?_⟩
  simp only [KernelFields.toList, List.getElem_cons_succ, List.getElem_cons_zero]
  apply wp_loop (fun r as m => ∃ (id : Val) (k : KernelFields),
    as = [id] ∧
    r = k₀.empty_clause.toNat + 1 - id.toNat ∧
    k₀.first_proof_id.toNat ≤ id.toNat ∧
    id.toNat ≤ k₀.empty_clause.toNat + 1 ∧
    FullMemInv max_var n trail_free0.length st k₀ P_ro k m ∧
    CNF.Entails cnf₀
      (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)).toCNF ∧
    (k₀.empty_clause.toNat < id.toNat → cnf₀.Unsat))
  · rintro Jloop r as m ⟨id, k, rfl, rfl, hid_lo, hid_hi, hinv, hent, hunsat⟩ ih
    wp_unfold
    have hslt : k₀.empty_clause.slt id = decide (k₀.empty_clause.toNat < id.toNat) :=
      slt_iff_toNat_lt hemp_lt31 (by omega)
    rw [hslt, decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hgt => hQ m ⟨k, hinv⟩ (hunsat hgt), fun hle => ?_⟩
    have hid_le : id.toNat ≤ k₀.empty_clause.toNat := by omega
    have hid_used : id.toNat < usedWords.length := Nat.lt_of_le_of_lt hid_le pre.hused_len
    have hid_lits : id.toNat < litsPtrs.length := Nat.lt_of_le_of_lt hid_le pre.hlits_len
    have hid_ante : id.toNat < antePtrs.length := Nat.lt_of_le_of_lt hid_le pre.hante_len
    obtain ⟨_, R, hm_sep⟩ := fullMemInv_sep pre hinv
    apply wp_join (fun as m' => as = [] ∧
      (∃ k', FullMemInv max_var n trail_free0.length st k₀ P_ro k' m') ∧
      CNF.Entails cnf₀
        (stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
          (id.toNat - k₀.first_proof_id.toNat + 1)).toCNF ∧
      (k₀.empty_clause.toNat < id.toNat + 1 → cnf₀.Unsat))
    · rintro _ m' ⟨rfl, ⟨k', hinv'⟩, hent', hunsat'⟩
      wp_unfold
      have hid1 : (id + 1).toNat = id.toNat + 1 := toNat_add_one_of_lt (by omega)
      refine ih _ _ _ (by omega) ⟨id + 1, k', rfl, rfl, by omega, by omega, hinv', ?_, ?_⟩
      · rwa [show (id + 1).toNat - k₀.first_proof_id.toNat =
          id.toNat - k₀.first_proof_id.toNat + 1 by omega]
      · rwa [hid1]
    intro Jnext hJnext
    let uw : Val := if k₀.trimming = 0 then -1 else usedWords[id.toNat]
    apply wp_join (fun as m' => as = [uw] ∧ m' = m)
    · rintro _ m1 ⟨rfl, hm1⟩
      subst m1
      wp_unfold
      have huw32 : IsInt32 uw := by
        dsimp only [uw]; split
        · decide
        · exact pre.hused_int32 id.toNat hid_used
      rw [truthy_iff _ huw32]
      refine ⟨fun huw_nz => ?_, fun huw_z => ?_⟩
      · have hused_true : isStepUsed k₀.trimming usedWords id.toNat = true := by
          rw [isStepUsed_eq_true_iff hid_used]
          by_cases ht0 : k₀.trimming = 0 <;> simp_all [uw]
        have hm_lits : (word8Array k₀.literals_begin litsPtrs ⋆
            (kernelState st k ⋆ (int4Array k₀.used_begin usedWords ⋆
              (word8Array k₀.antecedents_begin antePtrs ⋆ R)))) m :=
          sep_cast hm_sep (by ac_rfl)
        have hm_ante : (word8Array k₀.antecedents_begin antePtrs ⋆
            (kernelState st k ⋆ (int4Array k₀.used_begin usedWords ⋆
              (word8Array k₀.literals_begin litsPtrs ⋆ R)))) m :=
          sep_cast hm_sep (by ac_rfl)
        refine ⟨_, loadl_word8Array hid_lits hm_lits, _, loadl_word8Array hid_ante hm_ante, ?_⟩
        refine wp_call_of_spec (hclause _ _ _ _
          (fullMemInv_checkClause pre hid_lo hid_le hused_true hinv (fun m' hk' hc => ?_) hX))
        wp_unfold
        refine hJnext [] m' ⟨rfl, hk', ?_, ?_⟩
        · rw [stateAt_succ, show k₀.first_proof_id.toNat + (id.toNat - k₀.first_proof_id.toNat) =
            id.toNat by omega, hused_true]
          exact entails_stepState_of_used hent hc
        · intro hlt
          exact unsat_of_entails_and_entails_empty hent hc
            (by rw [show id.toNat = k₀.empty_clause.toNat by omega]; exact pre.hempty_clause)
      · have hused_false : isStepUsed k₀.trimming usedWords id.toNat = false := by
          rw [Bool.eq_false_iff, ne_eq, isStepUsed_eq_true_iff hid_used]
          by_cases ht0 : k₀.trimming = 0 <;> simp_all [uw]
        refine hJnext [] m ⟨rfl, ⟨k, hinv⟩, ?_, ?_⟩
        · rw [stateAt_succ, show k₀.first_proof_id.toNat + (id.toNat - k₀.first_proof_id.toNat) =
            id.toNat by omega, hused_false]
          exact entails_stepState_of_unused _ hent
        · intro hlt
          have := pre.hempty_used
          rw [show id.toNat = k₀.empty_clause.toNat by omega] at hused_false
          simp [this] at hused_false
    · intro Jcheck hJcheck
      wp_unfold
      refine ⟨fun htnz => ?_, fun htz => ?_⟩
      · rw [shl_two]
        have hm_used : (int4Array k₀.used_begin usedWords ⋆
            (kernelState st k ⋆ (word8Array k₀.literals_begin litsPtrs ⋆
              (word8Array k₀.antecedents_begin antePtrs ⋆ R)))) m :=
          sep_cast hm_sep (by ac_rfl)
        refine ⟨_, loadsw_int4Array hid_used (pre.hused_int32 id.toNat hid_used) hm_used, ?_⟩
        exact hJcheck _ _ ⟨congrArg (· :: []) (ite_eq_right htnz).symm, rfl⟩
      · have ht0 : k₀.trimming = 0 := Classical.not_not.1 htz
        exact hJcheck _ _ ⟨congrArg (· :: []) (ite_eq_left ht0).symm, rfl⟩
  · intro Jloop hJloop
    wp_unfold
    exact hJloop _ _ _ ⟨k₀.first_proof_id, k₀, rfl, rfl, Nat.le_refl _,
      by omega, hinv₀,
      by rw [Nat.sub_self]; exact entails_stateAt_zero _ _ _ _ _, fun _ => by omega⟩

/-! ## Well-formedness -/

theorem checkClause_wf : Func.Wf checkClause := by wf_tac
theorem checkProof_wf : Func.Wf checkProof := by wf_tac

/-! ## Non-vacuity -/

theorem checkClause_rup_nonvacuous :
    checkClauseRupSpec [0x1000, 7, 0x10aa, 0x10b6] (nvBytes.At 0x1000)
      (fun rs _ => rs = []) (fun f _ _ => f = "lrat_fail") :=
  ⟨0x1000, 7, 0x10aa, 0x10b6, 1, nvK, [1, -1], [], [], [0, 0], ⟨#[]⟩,
    ZeroTermInts 0x10aa [1, -1] ⋆ ZeroTermInts 0x10b6 [], rfl, rfl, rfl,
    ⟨⟨_, by rw [word8Array_nil, emp_sep]⟩, fun _ h => absurd h (by simp)⟩,
    ⟨_, rfl⟩, ⟨_, sep_comm _ _⟩,
    by intro x hx; simp at hx; rcases hx with rfl | rfl <;> (unfold IsValidLit bvAbs; decide),
    by simp, by decide, by decide, nv_mem, fun _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩

def nvCheckK : KernelFields :=
  { nvK with
    used_begin := 0x10a2
    antecedents_begin := 0x10ba
    literals_begin := 0x10aa
    marks_begin := 0x10a0
    empty_clause := 1
    first_proof_id := 1
    strict := 1
    trimming := 0
    checking := 1
    forward := 0 }

def nvCheckBytes : List UInt8 :=
  bytesN 8 nvCheckK.toList ++
    (bytesN 1 [0, 0] ++
      (bytesN 4 [1, 1] ++
        (bytesN 8 [0, 0x10ca] ++
          (bytesN 8 [0, 0x10ce] ++
            (bytesN 4 [0] ++ bytesN 4 [0])))))

def nvCheckPro : Mem 64 → Prop :=
  int4Array 0x10a2 [1, 1] ⋆
    (word8Array 0x10aa [0, 0x10ca] ⋆
      (word8Array 0x10ba [0, 0x10ce] ⋆
        (ZeroTermInts 0x10ca [] ⋆ ZeroTermInts 0x10ce [])))

theorem nvCheck_pre :
    CheckProofPre 1 2 0x1000 nvCheckK [1, 1] [0, 0x10ca] [0, 0x10ce] [] .empty
      [.empty, .empty] [[], []] [[], []] nvCheckPro (nvCheckBytes.At 0x1000) := by
  refine {
    hchecking := by decide
    hforward := by decide
    hfst_pos := by decide
    hfst_le := by decide
    hemp_lt := by decide
    hused_len := by decide
    hused_int32 := by decide
    hlits_len := by decide
    hante_len := by decide
    hempty_used := rfl
    hempty_clause := rfl
    hP_arrays := ⟨ZeroTermInts 0x10ca [] ⋆ ZeroTermInts 0x10ce [], rfl⟩
    hrup_case := fun h => absurd h (by decide)
    hstrict_case := fun _ => ⟨by decide, by decide, ?_, ?_⟩
  }
  · unfold kernelState nvCheckPro ZeroTermInts
    rw [show List.replicate 2 (0 : Val) = [0, 0] from rfl,
      byte1Array_eq _ _ (by simp), word8Array_eq _ _ (by simp [KernelFields.toList]),
      int4Array_eq _ _ (by simp), word8Array_eq _ _ (by simp), word8Array_eq _ _ (by simp),
      int4Array_eq _ _ (by simp), int4Array_eq _ _ (by simp)]
    have e : Eq (nvCheckBytes.At (0x1000 : Val)) =
        (Eq ((bytesN 8 nvCheckK.toList).At (0x1000 : Val)) ⋆
          (Eq ((bytesN 1 [0, 0]).At (0x10a0 : Val)) ⋆
            (Eq ((bytesN 4 [1, 1]).At (0x10a2 : Val)) ⋆
              (Eq ((bytesN 8 [0, 0x10ca]).At (0x10aa : Val)) ⋆
                (Eq ((bytesN 8 [0, 0x10ce]).At (0x10ba : Val)) ⋆
                  (Eq ((bytesN 4 [0]).At (0x10ca : Val)) ⋆
                    Eq ((bytesN 4 [0]).At (0x10ce : Val)))))))) := by
      unfold nvCheckBytes
      rw [eq_append_At _ _ _ (by simp [bytesN_length, KernelFields.toList]),
        eq_append_At _ _ _ (by simp [bytesN_length]),
        eq_append_At _ _ _ (by simp [bytesN_length]),
        eq_append_At _ _ _ (by simp [bytesN_length]),
        eq_append_At _ _ _ (by simp [bytesN_length]),
        eq_append_At _ _ _ (by simp [bytesN_length])]
      simp only [bytesN_length, KernelFields.toList, List.length_cons, List.length_nil]
      rfl
    exact sep_cast (show Eq (nvCheckBytes.At (0x1000 : Val)) _ from rfl) (e.trans (by ac_rfl))
  · intro id hlo hhi _
    have hid : id.toNat = 1 := by change 1 ≤ id.toNat at hlo; change id.toNat ≤ 1 at hhi; omega
    simp only [hid, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      List.getElem_cons_succ, List.getElem_cons_zero]
    refine ⟨rfl, by decide, by simp, by simp, by simp,
      ⟨int4Array 0x10a2 [1, 1] ⋆ (word8Array 0x10aa [0, 0x10ca] ⋆
        (word8Array 0x10ba [0, 0x10ce] ⋆ ZeroTermInts 0x10ce [])), by dsimp [nvCheckPro]; ac_rfl⟩,
      ⟨int4Array 0x10a2 [1, 1] ⋆ (word8Array 0x10aa [0, 0x10ca] ⋆
        (word8Array 0x10ba [0, 0x10ce] ⋆ ZeroTermInts 0x10ca [])), by dsimp [nvCheckPro]; ac_rfl⟩⟩

theorem checkClause_strict_nonvacuous :
    checkClauseStrictSpec [0x1000, 1, 0x10ca, 0x10ce] (nvCheckBytes.At 0x1000)
      (fun rs _ => rs = []) (fun f _ _ => f = "lrat_fail") := by
  obtain ⟨hlen, hn_bound, hmem, hsteps⟩ := nvCheck_pre.hstrict_case (by decide)
  obtain ⟨_, hants_b, hants_i, hants_v, hlits_v, hsub_lits, hsub_ants⟩ :=
    hsteps 1 (by decide) (by decide) rfl
  exact ⟨0x1000, 1, 0x10ca, 0x10ce, 1, 2, _, nvCheckK, [], [], nvCheckPro, rfl, by decide,
    hlen, hn_bound, hants_b, hants_i, hants_v, hlits_v, hmem, hsub_ants, hsub_lits,
    fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem checkProof_nonvacuous :
    checkProofSpec [0x1000] (nvCheckBytes.At 0x1000)
      (fun rs _ => rs = []) (fun f _ _ => f = "lrat_fail") :=
  ⟨1, 2, 0x1000, nvCheckK, [1, 1], [0, 0x10ca], [0, 0x10ce], [], .empty,
    [.empty, .empty], [[], []], [[], []], nvCheckPro, rfl, nvCheck_pre,
    fun _ _ _ => rfl, fun _ _ => rfl⟩

end LeanQbe.LratTrim
