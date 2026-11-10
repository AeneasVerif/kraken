module

public import LeanQbe.Examples.LratTrim
public import LeanQbe.Examples.LratRupLemmas
public import LeanQbe.Examples.LratTrimStrictLemmas
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

/-! ## Well-formedness and module-linking glue -/

theorem checkClause_wf : Func.Wf checkClause := by wf_tac
theorem checkProof_wf : Func.Wf checkProof := by wf_tac
theorem trimProof_wf : Func.Wf trimProof := by
  unfold trimProof markUsed trimInner; wf_tac

/-- Combined contract of `br_check_clause` (`strict = 0` or `strict ≠ 0`). -/
def checkClauseSpec : Spec := fun args m Q X =>
  checkClauseRupSpec args m Q X ∨ checkClauseStrictSpec args m Q X

theorem checkClause_correct (Γ : Env)
    (hrup : ∀ args m Q X, LratRup.checkRupSpec args m Q X →
      Γ "br_check_clause_non_strictly_by_propagation" args m Q X)
    (hstrict : ∀ args m Q X, strictSpec args m Q X →
      Γ "br_check_clause_strictly_by_resolution" args m Q X) :
    ∀ args m Q X, checkClauseSpec args m Q X → Func.spec Γ checkClause args m Q X :=
  fun args m Q X h => h.elim (checkClause_rup_correct Γ hrup args m Q X)
    (checkClause_strict_correct Γ hstrict args m Q X)

/-- The 4 verified checker functions in callee-first order for `compile_correct`. -/
def lratCheckFns : List Fn :=
  [⟨"br_check_clause_non_strictly_by_propagation", LratRup.checkRup⟩,
   ⟨"br_check_clause_strictly_by_resolution", strictCheck⟩,
   ⟨"br_check_clause", checkClause⟩,
   ⟨"br_check_proof", checkProof⟩]

/-- Environment mapping each of the 4 LRAT checker functions to its contract. -/
def lratEnv : Env := fun g =>
  if g = "br_check_clause_non_strictly_by_propagation" then LratRup.checkRupSpec
  else if g = "br_check_clause_strictly_by_resolution" then strictSpec
  else if g = "br_check_clause" then checkClauseSpec
  else checkProofSpec

/-- One-step linking glue for `compile_correct` over `lratCheckFns` and `lratEnv`. -/
theorem lratEnv_step :
    (∀ args m Q X, lratEnv "br_check_clause_non_strictly_by_propagation" args m Q X →
      Func.spec lratEnv LratRup.checkRup args m Q X) ∧
    (∀ args m Q X, lratEnv "br_check_clause_strictly_by_resolution" args m Q X →
      Func.spec lratEnv strictCheck args m Q X) ∧
    (∀ args m Q X, lratEnv "br_check_clause" args m Q X →
      Func.spec lratEnv checkClause args m Q X) ∧
    (∀ args m Q X, lratEnv "br_check_proof" args m Q X →
      Func.spec lratEnv checkProof args m Q X) :=
  ⟨LratRup.checkRup_correct lratEnv,
   strictCheck_correct lratEnv,
   checkClause_correct lratEnv (fun _ _ _ _ h => h) (fun _ _ _ _ h => h),
   checkProof_correct lratEnv (fun _ _ _ _ h => h)⟩

theorem lratCheckFns_wf : ∀ f ∈ lratCheckFns, Func.Wf f.body := by
  intro f hf
  simp only [lratCheckFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact LratRup.checkRup_wf
  · exact strictCheck_wf
  · exact checkClause_wf
  · exact checkProof_wf

theorem lratEnv_sound :
    ∀ f ∈ lratCheckFns, ∀ args m Q X, lratEnv f.name args m Q X → Func.spec lratEnv f.body args m Q X := by
  intro f hf
  simp only [lratCheckFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact lratEnv_step.1
  · exact lratEnv_step.2.1
  · exact lratEnv_step.2.2.1
  · exact lratEnv_step.2.2.2

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

/-! ## Accepting UNSAT instance (`[[1], [-1]]`, exit postcondition `False`) -/

theorem wp_unroll {Γ : Env} {Q : Post} {X : XPost} {b rest : Cont → Expr Val Cont} {m : Mem 64}
    (h : ∀ J : Cont, (∀ as m', wp Γ Q X (b J) as [] m' → J as m') → wp Γ Q X (rest J) [] [] m) :
    wp Γ Q X (.label fun J => .block (b J) (rest J)) [] [] m := by
  simp only [wp, List.nil_append, true_and]; exact h

theorem loadsw_at {a p : Val} {xs : List Val} (i : Nat) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (hv : IsInt32 xs[i]) (h : (int4Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (4 * i) := by rfl) :
    loadVal m .l .w true p = some xs[i] := heq ▸ loadsw_int4Array hi hv h

theorem loadl_at {a p : Val} {xs : List Val} (i : Nat) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (8 * i) := by rfl) :
    loadVal m .l .l true p = some xs[i] := heq ▸ loadl_word8Array hi h

theorem loadsb_at {a p : Val} {xs : List Val} (i : Nat) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (hv : IsInt8 xs[i]) (h : (byte1Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 i := by rfl) :
    loadVal m .l .b true p = some xs[i] := heq ▸ loadsb_byte1Array hi hv h

theorem storeb_at {a : Val} {xs : List Val} (i : Nat) (p v : Val) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 i := by rfl) :
    storeOk m .b p ∧ (byte1Array a (xs.set i v) ⋆ R) (storeMem m .b p v) :=
  heq ▸ storeb_byte1Array v hi h

/-- The unsatisfiable 2-clause formula `(x₁) ∧ (¬x₁)`. -/
def nvAcceptCnf : CNF Nat :=
  (CNF.empty.add (toClause [1])).add (toClause [-1])

theorem nvAcceptCnf_unsat : nvAcceptCnf.Unsat := by
  intro a
  rw [Bool.eq_false_iff, ne_eq]
  intro h
  simp only [nvAcceptCnf, CNF.eval_add, Bool.and_eq_true] at h
  obtain ⟨h1, h2, _⟩ := h
  rw [← CNF.Clause.sat_def] at h1 h2
  cases ha : a 1
  · refine CNF.Clause.not_sat_iff_forall_mem_ne.2 (fun l hl => ?_) h2
    rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hl
    obtain rfl : l = (1, true) := (List.mem_singleton.1 hl).trans (by decide)
    simp [ha]
  · refine CNF.Clause.not_sat_iff_forall_mem_ne.2 (fun l hl => ?_) h1
    rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hl
    obtain rfl : l = (1, false) := (List.mem_singleton.1 hl).trans (by decide)
    simp [ha]

def nvAcceptK : KernelFields :=
  { nvK with
    used_begin := 0x10a2
    antecedents_begin := 0x10d2
    literals_begin := 0x10b2
    marks_begin := 0x10a0
    empty_clause := 3
    first_proof_id := 3
    strict := 1
    trimming := 0
    checking := 1
    forward := 0 }

def nvAcceptK1 : KernelFields :=
  { nvAcceptK with stat_chk_total := 1, stat_chk_empty := 1 }

def nvAcceptK2 : KernelFields :=
  { nvAcceptK1 with stat_resolved := 2 }

def nvAcceptRo : Mem 64 → Prop :=
  int4Array 0x10a2 [0, 0, 0, 1] ⋆
    (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
      (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆
        (int4Array 0x10f2 [1, 0] ⋆
          (int4Array 0x10fa [-1, 0] ⋆
            (ZeroTermInts 0x1102 [] ⋆ int4Array 0x1106 [1, 2, 0])))))

def nvAcceptMem (k : KernelFields) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  byte1Array 0x10a0 [0, 0] ⋆ (kernelState 0x1000 k ⋆ (nvAcceptRo ⋆ R))

def nvAcceptBytes : List UInt8 :=
  bytesN 8 nvAcceptK.toList ++
    (bytesN 1 [0, 0] ++
      (bytesN 4 [0, 0, 0, 1] ++
        (bytesN 8 [0, 0x10f2, 0x10fa, 0x1102] ++
          (bytesN 8 [0, 0, 0, 0x1106] ++
            (bytesN 4 [1, 0] ++
              (bytesN 4 [-1, 0] ++
                (bytesN 4 [0] ++ bytesN 4 [1, 2, 0])))))))

theorem nvAcceptBytes_length : nvAcceptBytes.length = 274 := by
  simp [nvAcceptBytes, bytesN_length, KernelFields.toList]

theorem nvAccept_mem : nvAcceptMem nvAcceptK emp (nvAcceptBytes.At 0x1000) := by
  unfold nvAcceptMem kernelState nvAcceptRo ZeroTermInts
  rw [sep_emp, byte1Array_eq _ _ (by simp), word8Array_eq _ _ (by simp [KernelFields.toList]),
    int4Array_eq _ _ (by simp), word8Array_eq _ _ (by simp), word8Array_eq _ _ (by simp),
    int4Array_eq _ _ (by simp), int4Array_eq _ _ (by simp), int4Array_eq _ _ (by simp),
    int4Array_eq _ _ (by simp)]
  have e : Eq (nvAcceptBytes.At (0x1000 : Val)) =
      (Eq ((bytesN 8 nvAcceptK.toList).At (0x1000 : Val)) ⋆
        (Eq ((bytesN 1 [0, 0]).At (0x10a0 : Val)) ⋆
          (Eq ((bytesN 4 [0, 0, 0, 1]).At (0x10a2 : Val)) ⋆
            (Eq ((bytesN 8 [0, 0x10f2, 0x10fa, 0x1102]).At (0x10b2 : Val)) ⋆
              (Eq ((bytesN 8 [0, 0, 0, 0x1106]).At (0x10d2 : Val)) ⋆
                (Eq ((bytesN 4 [1, 0]).At (0x10f2 : Val)) ⋆
                  (Eq ((bytesN 4 [-1, 0]).At (0x10fa : Val)) ⋆
                    (Eq ((bytesN 4 [0]).At (0x1102 : Val)) ⋆
                      Eq ((bytesN 4 [1, 2, 0]).At (0x1106 : Val)))))))))) := by
    unfold nvAcceptBytes
    rw [eq_append_At _ _ _ (by simp [bytesN_length, KernelFields.toList]),
      eq_append_At _ _ _ (by simp [bytesN_length]),
      eq_append_At _ _ _ (by simp [bytesN_length]),
      eq_append_At _ _ _ (by simp [bytesN_length]),
      eq_append_At _ _ _ (by simp [bytesN_length]),
      eq_append_At _ _ _ (by simp [bytesN_length]),
      eq_append_At _ _ _ (by simp [bytesN_length]),
      eq_append_At _ _ _ (by simp [bytesN_length])]
    simp only [bytesN_length, KernelFields.toList, List.length_cons, List.length_nil]
    rfl
  exact sep_cast (show Eq (nvAcceptBytes.At (0x1000 : Val)) _ from rfl) (e.trans (by ac_rfl))

theorem strictScan_accepts {Γ : Env} {Q : Post} {X : XPost} {scanned : Cont}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (int4Array 0x1106 [1, 2, 0] ⋆ R) m)
    (h : scanned [0x110e] m) :
    wp Γ Q X (strictScan 3 scanned 0x1106) [] [] m := by
  unfold strictScan
  apply wp_unroll; intro Jscan hscan; wp_unfold
  refine hscan _ _ ?_; dsimp only [wp_param]; wp_unfold
  refine ⟨_, loadsw_at 0 (by decide) (by decide) hm, fun _ => ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩, fun hc => absurd (by decide : Truthy 1) hc⟩
  refine hscan _ _ ?_; dsimp only [wp_param]; wp_unfold
  refine ⟨_, loadsw_at 1 (by decide) (by decide) hm, fun _ => ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩, fun hc => absurd (by decide : Truthy 2) hc⟩
  refine hscan _ _ ?_; dsimp only [wp_param]; wp_unfold
  exact ⟨_, loadsw_at 2 (by decide) (by decide) hm, fun hc => absurd hc (by decide), fun _ => h⟩

theorem strictInner_ant2 {Γ : Env} {Q : Post} {X : XPost} {done : Cont}
    {st sr : Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (byte1Array 0x10a0 [0, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ R)) m)
    (h : ∀ m', (byte1Array 0x10a0 [0, -1] ⋆ (int4Array 0x10fa [-1, 0] ⋆ R)) m' → done [0, 1] m') :
    wp Γ Q X (strictInner st 3 2 0x10a0 sr done 0x10fa 0) [] [] m := by
  unfold strictInner
  apply wp_unroll; intro Jlp hlp; wp_unfold
  refine hlp _ _ ?_; dsimp only [wp_param]; wp_unfold
  have hm_c : (int4Array 0x10fa [-1, 0] ⋆ (byte1Array 0x10a0 [0, 0] ⋆ R)) m := sep_cast hm (by ac_rfl)
  refine ⟨_, loadsw_at 0 (by decide) (by decide) hm_c, fun _ => ?_, fun hc => absurd (by decide : Truthy (-1)) hc⟩
  refine ⟨_, loadsb_at 1 (by decide) (by decide) hm, fun _ => ?_, fun hc => absurd rfl hc⟩
  have ⟨ok, hm'⟩ := storeb_at 1 0x10a1 (-1) (by decide) hm
  refine ⟨ok, hlp _ _ ?_⟩; dsimp only [wp_param]; wp_unfold
  have hm'_c : (int4Array 0x10fa [-1, 0] ⋆ (byte1Array 0x10a0 [0, -1] ⋆ R)) _ := sep_cast hm' (by ac_rfl)
  exact ⟨_, loadsw_at 1 (by decide) (by decide) hm'_c, fun hc => absurd hc (by decide), fun _ => h _ hm'⟩

theorem strictInner_ant1 {Γ : Env} {Q : Post} {X : XPost} {done : Cont}
    {st sr : Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (byte1Array 0x10a0 [0, -1] ⋆ (int4Array 0x10f2 [1, 0] ⋆ R)) m)
    (h : done [1, 1] m) :
    wp Γ Q X (strictInner st 3 1 0x10a0 sr done 0x10f2 1) [] [] m := by
  unfold strictInner
  apply wp_unroll; intro Jlp hlp; wp_unfold
  refine hlp _ _ ?_; dsimp only [wp_param]; wp_unfold
  have hm_c : (int4Array 0x10f2 [1, 0] ⋆ (byte1Array 0x10a0 [0, -1] ⋆ R)) m := sep_cast hm (by ac_rfl)
  refine ⟨_, loadsw_at 0 (by decide) (by decide) hm_c, fun _ => ?_, fun hc => absurd (by decide : Truthy 1) hc⟩
  refine ⟨_, loadsb_at 1 (by decide) (by decide) hm, fun hc => absurd hc (by decide), fun _ => ?_⟩
  refine ⟨fun hc => absurd hc (by decide), fun _ => ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩⟩
  refine hlp _ _ ?_; dsimp only [wp_param]; wp_unfold
  exact ⟨_, loadsw_at 1 (by decide) (by decide) hm_c, fun hc => absurd hc (by decide), fun _ => h⟩

theorem strictOuter_accepts {Γ : Env} {Q : Post} {X : XPost} {resolved : Cont}
    {st sr0 : Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (byte1Array 0x10a0 [0, 0] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
      (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))) m)
    (h : ∀ m', (byte1Array 0x10a0 [0, 0] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
      (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))) m' →
      resolved [sr0 + 1 + 1, 0, 0] m') :
    wp Γ Q X (strictOuter st 3 0x10b2 0x10a0 0x1106 resolved 0x110e sr0) [] [] m := by
  unfold strictOuter
  apply wp_unroll; intro Jout hout; wp_unfold
  refine hout _ _ ?_; dsimp only [wp_param]; wp_unfold
  refine ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩
  have hm_ants : (int4Array 0x1106 [1, 2, 0] ⋆ (byte1Array 0x10a0 [0, 0] ⋆
      (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ R))))) m :=
    sep_cast hm (by ac_rfl)
  have hm_lb : (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (byte1Array 0x10a0 [0, 0] ⋆
      (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))) m :=
    sep_cast hm (by ac_rfl)
  refine ⟨_, loadsw_at 1 (by decide) (by decide) hm_ants, _, loadl_at 2 (by decide) hm_lb, ?_⟩
  apply wp_unroll; intro Jdone2 hdone2
  have hm_in2 : (byte1Array 0x10a0 [0, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆
      (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))) m :=
    sep_cast hm (by ac_rfl)
  refine strictInner_ant2 hm_in2 fun m1 hm1 => hdone2 _ _ ?_
  dsimp only [wp_param]; wp_unfold
  refine ⟨fun _ => ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩, fun hc => absurd (by decide : Truthy 1) hc⟩
  refine hout _ _ ?_; dsimp only [wp_param]; wp_unfold
  refine ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩
  have hm1_ants : (int4Array 0x1106 [1, 2, 0] ⋆ (byte1Array 0x10a0 [0, -1] ⋆
      (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ R))))) m1 :=
    sep_cast hm1 (by ac_rfl)
  have hm1_lb : (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (byte1Array 0x10a0 [0, -1] ⋆
      (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))) m1 :=
    sep_cast hm1 (by ac_rfl)
  refine ⟨_, loadsw_at 0 (by decide) (by decide) hm1_ants, _, loadl_at 1 (by decide) hm1_lb, ?_⟩
  apply wp_unroll; intro Jdone1 hdone1
  have hm_in1 : (byte1Array 0x10a0 [0, -1] ⋆ (int4Array 0x10f2 [1, 0] ⋆
      (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (int4Array 0x10fa [-1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))) m1 :=
    sep_cast hm1 (by ac_rfl)
  refine strictInner_ant1 hm_in1 (hdone1 _ _ ?_)
  dsimp only [wp_param]; wp_unfold
  refine ⟨fun hc => absurd hc (by decide), fun _ => ⟨fun _ => ?_, fun hc => absurd (by decide : Truthy 1) hc⟩⟩
  have ⟨ok, hm2⟩ := storeb_at 1 0x10a1 0 (by decide) hm_in1
  refine ⟨ok, hout _ _ ?_⟩; dsimp only [wp_param]; wp_unfold
  exact ⟨fun _ => h _ (sep_cast hm2 (by ac_rfl)), fun hc => absurd rfl hc⟩

theorem strictFinal_accepts {Γ : Env} {Q : Post} {X : XPost} {checked : Cont}
    {id mb rsize0 : Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ZeroTermInts 0x1102 [] ⋆ R) m) (hchk : checked [rsize0] m) :
    wp Γ Q X (strictFinal id mb checked 0x1102 rsize0) [] [] m := by
  unfold strictFinal
  apply wp_unroll; intro J hJ; wp_unfold
  refine hJ _ _ ?_; dsimp only [wp_param]; wp_unfold
  exact ⟨0, loadsw_at 0 (by decide) (by decide) hm, fun h => absurd h (by decide), fun _ => hchk⟩

def strictAcceptSpec : Spec := fun args m Q _ =>
  ∃ R, args = [0x1000, 3, 0x1102, 0x1106] ∧ nvAcceptMem nvAcceptK1 R m ∧
    ∀ m', nvAcceptMem nvAcceptK2 R m' → Q [] m'

theorem strictCheck_accepts (Γ : Env) :
    ∀ args m Q X, strictAcceptSpec args m Q X → Func.spec Γ strictCheck args m Q X := by
  rintro _ m Q X ⟨R, rfl, hm, hQ⟩
  unfold strictCheck Func.spec
  wp_unfold
  apply wp_unroll; intro Jscan hscan
  have hm_scan : (int4Array 0x1106 [1, 2, 0] ⋆ (byte1Array 0x10a0 [0, 0] ⋆ (kernelState 0x1000 nvAcceptK1 ⋆
      (int4Array 0x10a2 [0, 0, 0, 1] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
        (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (int4Array 0x10f2 [1, 0] ⋆
          (int4Array 0x10fa [-1, 0] ⋆ (ZeroTermInts 0x1102 [] ⋆ R))))))))) m := by
    unfold nvAcceptMem nvAcceptRo at hm; exact sep_cast hm (by ac_rfl)
  refine strictScan_accepts hm_scan (hscan _ _ ?_)
  dsimp only [wp_param]; wp_unfold
  have hks : (kernelState 0x1000 nvAcceptK1 ⋆ (byte1Array 0x10a0 [0, 0] ⋆ (nvAcceptRo ⋆ R))) m := by
    unfold nvAcceptMem at hm; exact sep_cast hm (by ac_rfl)
  refine ⟨_, loadl_kfield 2 (by decide) hks rfl, _, loadl_kfield 4 (by decide) hks rfl,
    _, loadl_kfield 18 (by decide) hks rfl, ?_⟩
  simp only [KernelFields.toList, nvAcceptK1, nvAcceptK, nvK, List.getElem_cons_succ, List.getElem_cons_zero]
  apply wp_unroll; intro Jres hres
  have hm_out : (byte1Array 0x10a0 [0, 0] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
      (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆
        (kernelState 0x1000 nvAcceptK1 ⋆ (int4Array 0x10a2 [0, 0, 0, 1] ⋆
          (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (ZeroTermInts 0x1102 [] ⋆ R))))))))) m := by
    unfold nvAcceptMem nvAcceptRo at hm; exact sep_cast hm (by ac_rfl)
  refine strictOuter_accepts hm_out fun m1 hm1 => hres _ _ ?_
  dsimp only [wp_param]; wp_unfold
  have hm1_ks : (word8Array 0x1000 nvAcceptK1.toList ⋆ (byte1Array 0x10a0 [0, 0] ⋆ (nvAcceptRo ⋆ R))) m1 := by
    unfold kernelState at hm1; unfold nvAcceptRo; exact sep_cast hm1 (by ac_rfl)
  have ⟨ok, hm2_ks⟩ := storel_word8Array (i := 18) (0 + 1 + 1) (by simp [KernelFields.toList]) hm1_ks
  refine ⟨ok, fun hc => absurd hc (by decide), fun _ => ?_⟩
  apply wp_unroll; intro Jchk hchk
  have hm2_fin : (ZeroTermInts 0x1102 [] ⋆ (byte1Array 0x10a0 [0, 0] ⋆ (kernelState 0x1000 nvAcceptK2 ⋆
      (int4Array 0x10a2 [0, 0, 0, 1] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
        (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (int4Array 0x10f2 [1, 0] ⋆
          (int4Array 0x10fa [-1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R)))))))))
      (storeMem m1 .l (0x1000 + 144) (0 + 1 + 1)) := by
    unfold nvAcceptRo at hm2_ks; unfold kernelState
    change (word8Array 0x1000 nvAcceptK2.toList ⋆ _) _ at hm2_ks
    exact sep_cast hm2_ks (by ac_rfl)
  refine strictFinal_accepts hm2_fin (hchk _ _ ?_)
  dsimp only [wp_param]; wp_unfold
  refine ⟨fun hc => absurd hc (by decide), fun _ => hQ _ ?_⟩
  unfold nvAcceptMem nvAcceptRo; exact sep_cast hm2_fin (by ac_rfl)

def checkClauseAcceptSpec : Spec := fun args m Q _ =>
  ∃ R, args = [0x1000, 3, 0x1102, 0x1106] ∧ nvAcceptMem nvAcceptK R m ∧
    ∀ m', nvAcceptMem nvAcceptK2 R m' → Q [] m'

theorem checkClause_accepts (Γ : Env)
    (hstrict : ∀ args m Q X, strictAcceptSpec args m Q X →
      Γ "br_check_clause_strictly_by_resolution" args m Q X) :
    ∀ args m Q X, checkClauseAcceptSpec args m Q X → Func.spec Γ checkClause args m Q X := by
  rintro _ m Q X ⟨R, rfl, hm, hQ⟩
  have hm_z : (kernelState 0x1000 nvAcceptK ⋆ (ZeroTermInts 0x1102 [] ⋆
      (byte1Array 0x10a0 [0, 0] ⋆ (int4Array 0x10a2 [0, 0, 0, 1] ⋆
        (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆
          (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))))))) m := by
    unfold nvAcceptMem nvAcceptRo at hm; exact sep_cast hm (by ac_rfl)
  refine checkClause_step hm_z fun m1 hm1 => ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
  refine hstrict _ _ _ _ ⟨R, rfl, ?_, fun m2 hm2 => by wp_unfold; exact hQ m2 hm2⟩
  unfold nvAcceptMem nvAcceptRo
  change (kernelState 0x1000 nvAcceptK1 ⋆ _) m1 at hm1
  exact sep_cast hm1 (by ac_rfl)

def checkProofAcceptSpec : Spec := fun args m Q _ =>
  ∃ R, args = [0x1000] ∧ nvAcceptMem nvAcceptK R m ∧
    ∀ m', nvAcceptMem nvAcceptK2 R m' → nvAcceptCnf.Unsat → Q [] m'

theorem checkProof_accepts (Γ : Env)
    (hclause : ∀ args m Q X, checkClauseAcceptSpec args m Q X →
      Γ "br_check_clause" args m Q X) :
    ∀ args m Q X, checkProofAcceptSpec args m Q X → Func.spec Γ checkProof args m Q X := by
  rintro _ m Q X ⟨R, rfl, hm, hQ⟩
  unfold checkProof Func.spec
  wp_unfold
  have hks : (kernelState 0x1000 nvAcceptK ⋆ (byte1Array 0x10a0 [0, 0] ⋆ (nvAcceptRo ⋆ R))) m := by
    unfold nvAcceptMem at hm; exact sep_cast hm (by ac_rfl)
  refine ⟨_, loadl_kfield 12 (by decide) hks rfl, _, loadl_kfield 13 (by decide) hks rfl,
    _, loadsw_kfield 8 (by decide) hks rfl (by decide),
    _, loadsw_kfield 9 (by decide) hks rfl (by decide), ?_⟩
  simp only [KernelFields.toList, nvAcceptK, nvK, List.getElem_cons_succ, List.getElem_cons_zero]
  refine ⟨fun _ => ⟨fun _ => ⟨fun _ => ⟨fun _ => ?_, fun hc => absurd (by decide : Truthy 3) hc⟩,
    fun hc => absurd (by decide : Truthy 3) hc⟩, fun hc => absurd trivial hc⟩, fun hc => absurd (by decide : (1 : Val) ≠ 0) hc⟩
  refine ⟨_, loadl_kfield 11 (by decide) hks rfl, _, loadl_kfield 0 (by decide) hks (by simp),
    _, loadl_kfield 2 (by decide) hks rfl, _, loadl_kfield 1 (by decide) hks rfl, ?_⟩
  simp only [KernelFields.toList, nvAcceptK, nvK, List.getElem_cons_succ, List.getElem_cons_zero]
  apply wp_unroll; intro Jloop hloop; wp_unfold
  refine hloop _ _ ?_; dsimp only [wp_param]; wp_unfold
  refine ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩
  apply wp_unroll; intro Jnext hnext
  apply wp_unroll; intro Jchk hchk; wp_unfold
  refine ⟨fun hc => absurd trivial hc, fun _ => ?_⟩
  refine hchk _ _ ?_; dsimp only [wp_param]; wp_unfold
  refine ⟨fun _ => ?_, fun hc => absurd (by decide : Truthy (-1)) hc⟩
  have hm_lb : (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (byte1Array 0x10a0 [0, 0] ⋆
      (kernelState 0x1000 nvAcceptK ⋆ (int4Array 0x10a2 [0, 0, 0, 1] ⋆
        (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (int4Array 0x10f2 [1, 0] ⋆
          (int4Array 0x10fa [-1, 0] ⋆ (ZeroTermInts 0x1102 [] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))))))) m := by
    unfold nvAcceptMem nvAcceptRo at hm; exact sep_cast hm (by ac_rfl)
  have hm_ab : (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (byte1Array 0x10a0 [0, 0] ⋆
      (kernelState 0x1000 nvAcceptK ⋆ (int4Array 0x10a2 [0, 0, 0, 1] ⋆
        (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆ (int4Array 0x10f2 [1, 0] ⋆
          (int4Array 0x10fa [-1, 0] ⋆ (ZeroTermInts 0x1102 [] ⋆ (int4Array 0x1106 [1, 2, 0] ⋆ R))))))))) m := by
    unfold nvAcceptMem nvAcceptRo at hm; exact sep_cast hm (by ac_rfl)
  refine ⟨_, loadl_at 3 (by decide) hm_lb, _, loadl_at 3 (by decide) hm_ab, ?_⟩
  refine wp_call_of_spec (hclause _ _ _ _ ⟨R, rfl, hm, fun m2 hm2 => ?_⟩)
  wp_unfold; refine hnext _ _ ?_; wp_unfold
  refine hloop _ _ ?_; dsimp only [wp_param]; wp_unfold
  exact ⟨fun _ => hQ m2 hm2 nvAcceptCnf_unsat, fun hc => absurd hc (by decide)⟩

/-- Environment mapping the 4 LRAT checker functions to their concrete-accepting contracts. -/
def lratAcceptEnv : Env := fun g =>
  if g = "br_check_clause_non_strictly_by_propagation" then LratRup.checkRupSpec
  else if g = "br_check_clause_strictly_by_resolution" then strictAcceptSpec
  else if g = "br_check_clause" then checkClauseAcceptSpec
  else checkProofAcceptSpec

theorem lratAcceptEnv_sound :
    ∀ f ∈ lratCheckFns, ∀ args m Q X, lratAcceptEnv f.name args m Q X → Func.spec lratAcceptEnv f.body args m Q X := by
  intro f hf
  simp only [lratCheckFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact LratRup.checkRup_correct lratAcceptEnv
  · exact strictCheck_accepts lratAcceptEnv
  · exact checkClause_accepts lratAcceptEnv (fun _ _ _ _ h => h)
  · exact checkProof_accepts lratAcceptEnv (fun _ _ _ _ h => h)

theorem nvAccept_pre :
    CheckProofPre 1 2 0x1000 nvAcceptK [0, 0, 0, 1] [0, 0x10f2, 0x10fa, 0x1102]
      [0, 0, 0, 0x1106] [] nvAcceptCnf [.empty, toClause [1], toClause [-1], .empty]
      [[], [1], [-1], []] [[], [], [], [1, 2]] nvAcceptRo (nvAcceptBytes.At 0x1000) := by
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
    hP_arrays := ⟨ZeroTermInts 0x10f2 [1] ⋆ (ZeroTermInts 0x10fa [-1] ⋆
      (ZeroTermInts 0x1102 [] ⋆ ZeroTermInts 0x1106 [1, 2])), by
      unfold nvAcceptRo ZeroTermInts; rfl⟩
    hrup_case := fun h => absurd h (by decide)
    hstrict_case := fun _ => ⟨by decide, by decide, ?_, ?_⟩
  }
  · have hm := nvAccept_mem
    unfold nvAcceptMem at hm
    rwa [sep_emp] at hm
  · intro id hlo hhi _
    have hid : id.toNat = 3 := by change 3 ≤ id.toNat at hlo; change id.toNat ≤ 3 at hhi; omega
    simp only [hid, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, List.getElem_cons_succ, List.getElem_cons_zero]
    refine ⟨rfl, by decide, by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide, ?_, by simp,
      ⟨int4Array 0x10a2 [0, 0, 0, 1] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
        (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (int4Array 0x10f2 [1, 0] ⋆
          (int4Array 0x10fa [-1, 0] ⋆ int4Array 0x1106 [1, 2, 0])))), by
        dsimp [nvAcceptRo, ZeroTermInts]; ac_rfl⟩,
      ⟨int4Array 0x10a2 [0, 0, 0, 1] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
        (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (int4Array 0x10f2 [1, 0] ⋆
          (int4Array 0x10fa [-1, 0] ⋆ ZeroTermInts 0x1102 [])))), by
        dsimp [nvAcceptRo, ZeroTermInts]; ac_rfl⟩⟩
    intro aid haid _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at haid
    have hw : word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] =
        (word8 0x10b2 0 ⋆ (word8 0x10ba 0x10f2 ⋆ (word8 0x10c2 0x10fa ⋆ word8 0x10ca 0x1102))) := by
      simp [word8Array_cons, word8Array_nil, sep_emp]
    change ValidAntecedent 1 (stateAt nvAcceptCnf 3 0 [0, 0, 0, 1]
      [.empty, toClause [1], toClause [-1], .empty] 0).toCNF 0x10b2 nvAcceptRo aid
    let roRest := int4Array 0x10a2 [0, 0, 0, 1] ⋆ (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆
      (int4Array 0x10f2 [1, 0] ⋆ (int4Array 0x10fa [-1, 0] ⋆
        (ZeroTermInts 0x1102 [] ⋆ int4Array 0x1106 [1, 2, 0]))))
    rcases haid with rfl | rfl
    · refine ⟨0x10f2, [1], ⟨word8 0x10b2 0 ⋆ (word8 0x10c2 0x10fa ⋆ (word8 0x10ca 0x1102 ⋆ roRest)), ?_⟩,
        ⟨int4Array 0x10a2 [0, 0, 0, 1] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
          (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (int4Array 0x10fa [-1, 0] ⋆
            (ZeroTermInts 0x1102 [] ⋆ int4Array 0x1106 [1, 2, 0])))),
          by dsimp [nvAcceptRo, ZeroTermInts]; ac_rfl⟩, ?_, ?_, ?_⟩
      · change nvAcceptRo = word8 0x10ba 0x10f2 ⋆ _
        unfold nvAcceptRo; dsimp only [roRest]; rw [hw]; ac_rfl
      · intro x hx; rw [List.mem_singleton.1 hx]; unfold IsValidLit bvAbs; decide
      · rintro atom ⟨h1, h2⟩; rw [literals_toClause] at h1 h2; simp [toLiteral] at h1 h2
      · exact entailsClause_toCNF_of_getElem?_formula (getElem?_formula_stateAt_of_lt
          nvAcceptCnf 3 0 [0, 0, 0, 1] [.empty, toClause [1], toClause [-1], .empty] 0 (j := 0) (by decide))
    · refine ⟨0x10fa, [-1], ⟨word8 0x10b2 0 ⋆ (word8 0x10ba 0x10f2 ⋆ (word8 0x10ca 0x1102 ⋆ roRest)), ?_⟩,
        ⟨int4Array 0x10a2 [0, 0, 0, 1] ⋆ (word8Array 0x10b2 [0, 0x10f2, 0x10fa, 0x1102] ⋆
          (word8Array 0x10d2 [0, 0, 0, 0x1106] ⋆ (int4Array 0x10f2 [1, 0] ⋆
            (ZeroTermInts 0x1102 [] ⋆ int4Array 0x1106 [1, 2, 0])))),
          by dsimp [nvAcceptRo, ZeroTermInts]; ac_rfl⟩, ?_, ?_, ?_⟩
      · change nvAcceptRo = word8 0x10c2 0x10fa ⋆ _
        unfold nvAcceptRo; dsimp only [roRest]; rw [hw]; ac_rfl
      · intro x hx; rw [List.mem_singleton.1 hx]; unfold IsValidLit bvAbs; decide
      · rintro atom ⟨h1, h2⟩; rw [literals_toClause] at h1 h2; simp [toLiteral] at h1 h2
      · exact entailsClause_toCNF_of_getElem?_formula (getElem?_formula_stateAt_of_lt
          nvAcceptCnf 3 0 [0, 0, 0, 1] [.empty, toClause [1], toClause [-1], .empty] 0 (j := 1) (by decide))

theorem checkProof_accepts_nonvacuous :
    checkProofAcceptSpec [0x1000] (nvAcceptBytes.At 0x1000)
      (fun rs m' => rs = [] ∧ nvAcceptMem nvAcceptK2 emp m' ∧ nvAcceptCnf.Unsat)
      (fun _ _ _ => False) :=
  ⟨emp, rfl, nvAccept_mem, fun _ hm hu => ⟨rfl, hm, hu⟩⟩

end LeanQbe.LratTrim
