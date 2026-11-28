/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpDeduce0
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
public import LeanQbe.T.Examples.Kissat.Src.Vivify

/-!
# Vivify Deduce Top-Level WP Proof (`Proof.Vivify.WpDeduce`)

Parametric `(Γ : Env)` `Func.wp` certification (`0` legacy imports, `0` SAT model proofs) for
`full_viv_deduce_m6` (`Spec.vivDeduceM6Spec`), reusing `Proof.Vivify.WpDeduce0` and closing
`VivDeduceSubWitness F_cur s sz.toNat` on all `4` subsumption exits (`confl_type = 1`,
`confl_type = 2`, BFS binary reason, BFS large reason).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Vivify
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. Reason Witness & Subsumption Helpers -/

private theorem bv32_setWidth64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  have := x.isLt; simp [BitVec.toNat_setWidth]; omega

private theorem deduce_bin_subWitness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {lm1 : List (BitVec 8)} {sz : Nat} {idx0 : Nat} {v_bv ot_bv lit0 : Val i32}
    (hw : FullWitnessInv c F0 F_cur s.core) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hidx0 : idx0 < s.core.trail_end) (hlit0 : lit0 = s.core.trl[idx0]?.getD 0#32)
    (htrl0 : lit0.toNat / 2 = v_bv.toNat)
    (hrsn_ne : s.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hot_eq : ot_bv = s.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 &&& 0x7FFFFFFF#32)
    (hbin : s.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32 ≠ 0#32)
    (hok : ∀ l ∈ [lit0.toNat, ot_bv.toNat], l < 2 * s.core.cur_vars ∧
      (lm1[l]?.getD 0#8 ≠ 0#8 ∨
        (s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0))) :
    VivDeduceSubWitness F_cur s sz := by
  have hrs := hw.reason_inv idx0 hidx0
  have htr_div : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat := by
    rw [← hlit0]; exact htrl0
  dsimp only at hrs
  rw [htr_div] at hrs
  have hrs' := hrs hrsn_ne
  rw [ite_eq_left hbin] at hrs'
  obtain ⟨_, hent, m1, hm1_lt, hm1_eq, _⟩ := hrs'
  have hent' : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit0.toNat, ot_bv.toNat]) := by
    simpa only [hlit0, hot_eq] using hent
  refine ⟨[lit0.toNat, ot_bv.toNat], hent', fun l hl => ?_⟩
  obtain ⟨hl_lt, hcase⟩ := hok l hl
  refine ⟨hl_lt, ?_⟩
  rcases hcase with hmk | hlv0
  · refine Or.inl ⟨hlm1_dom l (by omega) hmk, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · right; rwa [htrl0]
    · left
      have hvf := (hw.vals_false_iff ot_bv.toNat hl_lt).mpr ⟨m1, by omega, by rwa [hot_eq]⟩
      rw [hvf]; decide
  · exact Or.inr hlv0

private theorem deduce_large_rsn_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {idx0 : Nat} {v_bv rsn_bv : Val i32}
    (hw : FullWitnessInv c F0 F_cur s.core) (hidx0 : idx0 < s.core.trail_end)
    (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat)
    (hrsn_eq : s.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 = rsn_bv)
    (hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32) (hnbin : rsn_bv &&& 0x80000000#32 = 0#32) :
    rsn_bv.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s rsn_bv.toNat = false ∧
    ∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat,
      q = (s.core.trl[idx0]?.getD 0#32).toNat ∨
      ∃ m < idx0, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
  have hrs := hw.reason_inv idx0 hidx0
  dsimp only at hrs
  rw [htrl0, hrsn_eq] at hrs
  have hnb : ¬ (rsn_bv &&& 0x80000000#32 ≠ 0#32) := fun h => h hnbin
  have hrs' := hrs hrsn_ne
  rw [ite_eq_right hnb] at hrs'
  refine ⟨hrs'.1, hrs'.2.1, fun q hq => ?_⟩
  rcases hrs'.2.2 q hq with rfl | ⟨m, hm1, hm2, hm3⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨m, hm1, hm2, by rw [htrl0]; exact hm3⟩

private theorem deduce_bin_other_trl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {idx0 : Nat} {v_bv rsn_bv : Val i32}
    (hw : FullWitnessInv c F0 F_cur s.core) (hidx0 : idx0 < s.core.trail_end)
    (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat)
    (hrsn_eq : s.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 = rsn_bv)
    (hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32) (hbin : rsn_bv &&& 0x80000000#32 ≠ 0#32) :
    let ot_bv := rsn_bv &&& 0x7FFFFFFF#32
    let ov_bv := ot_bv >>> 1#32
    ov_bv.toNat < s.core.cur_vars ∧
    ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat / 2 = ov_bv.toNat := by
  intro ot_bv ov_bv
  have hrs := hw.reason_inv idx0 hidx0
  dsimp only at hrs
  rw [htrl0, hrsn_eq] at hrs
  have hrs' := hrs hrsn_ne
  rw [ite_eq_left hbin] at hrs'
  obtain ⟨hot_lt, _, m1, hm1_lt, hm1_eq, _⟩ := hrs'
  have hov_val : ov_bv.toNat = ot_bv.toNat / 2 := bv32_lshr1_toNat _
  have := Nat.lt_trans hm1_lt hidx0
  refine ⟨by dsimp only [ot_bv] at hov_val ⊢; rw [hov_val]; omega, m1, this, ?_⟩
  rw [hm1_eq, fullInv_var_xor1, hov_val]

private theorem s13_confl_ar_pres {F_cur : List (List Nat)} {s s1 s2 : FullState}
    {cref implied : Val i32}
    (h1 : S13ArPres s s1) (h2 : S13ArPres s s2)
    (hct : s2.core.confl_type = s1.core.confl_type) (hcr : s2.core.confl_ref = s1.core.confl_ref)
    (hc0 : s2.core.confl_lit0 = s1.core.confl_lit0)
    (hc1 : s2.core.confl_lit1 = s1.core.confl_lit1)
    (hcv : s2.core.cur_vars = s1.core.cur_vars) (hvs : s2.core.vals = s1.core.vals)
    (hcr_s : cref.toNat ∈ fullArenaClauseRefs s)
    (hconfl : implied = 0xFFFFFFFF#32 → FullVivConflictOk F_cur s1 ∨
      (s1.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s1 cref.toNat, s1.core.vals[l]?.getD 0#8 = 0xFF#8)) :
    implied = 0xFFFFFFFF#32 → FullVivConflictOk F_cur s2 ∨
      (s2.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s2 cref.toNat, s2.core.vals[l]?.getD 0#8 = 0xFF#8) := by
  intro himp
  rcases hconfl himp with hcw | ⟨hct0, hcls⟩
  · refine Or.inl ?_
    rcases hcw with hbin | ⟨hct2, href_c, hng_c, hlits_c⟩
    · exact Or.inl (by rw [hct, hc0, hc1, hcv, hvs]; exact hbin)
    · have href_s : s1.core.confl_ref.toNat ∈ fullArenaClauseRefs s := by rw [← h1.1]; exact href_c
      refine Or.inr ⟨by rw [hct]; exact hct2, by rw [hcr, h2.1]; exact href_s, ?_, fun l hl => ?_⟩
      · rw [hcr, (h2.2 _ href_s).1, ← (h1.2 _ href_s).1]; exact hng_c
      · rw [hcr, (h2.2 _ href_s).2.2, ← (h1.2 _ href_s).2.2] at hl; rw [hvs]; exact hlits_c l hl
  · refine Or.inr ⟨by rw [hct]; exact hct0, fun l hl => ?_⟩
    rw [(h2.2 _ hcr_s).2.2, ← (h1.2 _ hcr_s).2.2] at hl; rw [hvs]; exact hcls l hl

private theorem deduce_clear_exact_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_b lm1 : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {asz_b rsz_b : BitVec 64}
    {sz olen_c : Val i32} {qlen_c : Val i64} {taut_c : Val .bool} {m : Mem 64} {Q : Post [i32]}
    {X : XPost} (hspN : S13SparseInvNoMark c F0 F_cur s) (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hqb : VivQueueOk c s mrk_b ws1_b qlen_c.toNat) (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_b : ws2_b.length = 2 * c.max_vars) (hsub_b : S13SubRefOk s asz_b)
    (hsub_w : asz_b ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_b, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) m)
    (hQ : ∀ (ret : Val i32) (mrk' lm' : List (BitVec 8)) (asz' : BitVec 64) (mf : Mem 64),
      let s' := { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz', res_sz := rsz_b } }
      FullSparseInvW c F0 F_cur s' → S13SubRefOk s asz' →
      (asz' ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat) →
      (taut_c = true → ret = 0xFFFFFFFF#32) → (taut_c = false → ret = olen_c ∧ asz' = asz_b) →
      (FullMem c s' ⋆ R) mf → Q (ret, ()) mf) :
    wp Γ Q X (s13DeduceClearExpr c.hdr c.pMark c.pLitMark c.pTmp c.pWorkStk1 sz qlen_c olen_c
      taut_c) m := by
  have hcl := hspN.1.core_ok; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hq_le := hqb.2.2.1; have hcv_le := hcl.cur_vars_le
  dsimp only [s13DeduceClearExpr, fvOp]
  let inv1 : Val i64 × PUnit → Mem 64 → Prop := fun (i, ()) mi => ∃ mrk : List (BitVec 8),
    i.toNat ≤ qlen_c.toNat ∧ mrk.length = c.max_vars ∧
    (∀ v < c.max_vars, mrk[v]?.getD 0#8 ≠ 0#8 →
      ∃ j, i.toNat ≤ j ∧ j < qlen_c.toNat ∧ (ws1_b[j]?.getD 0#32).toNat = v) ∧
    (FullMem c { s with
      core := { s.core with mrk := mrk, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) mi
  refine wp_loop_inv (ts := [i64]) inv1 (fun (i, ()) _ => qlen_c.toNat - i.toNat)
    (fun Js hJs => by
      rw [wp_jump]; refine hJs (0#64, ()) m ⟨mrk_b, Nat.zero_le _, hqb.1, fun v hv hne => ?_, hm⟩
      have hv_cv : v < s.core.cur_vars :=
        if h : v < s.core.cur_vars then h else absurd (hqb.2.2.2.2.2.2.2.2 v (by omega) hv) hne
      have hm1 : mrk_b[v]?.getD 0#8 = 1#8 := (hqb.2.2.2.2.2.2.2.1 v hv_cv).resolve_left hne
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp ((hqb.2.2.2.2.2.2.1 v hv_cv).mp hm1)
      obtain ⟨j, hjq⟩ := List.mem_iff_getElem?.mp hx
      rw [List.getElem?_take] at hjq; split at hjq
      · rename_i hj; exact ⟨j, Nat.zero_le _, hj, by simp [hjq, hxeq]⟩
      · cases hjq)
    (fun Js (i, ()) mi ⟨mrk, hi_le, hmrk_len, hmrk_dom, hmi⟩ hrec => ?_)
  rw [Blocks.get_here]; dsimp only; viv_hsteps_nogrp
  · have hi_lt : i.toNat < qlen_c.toNat := by c0_bound
    have hi_ws1 : i.toNat < ws1_b.length := by have := hqb.2.1; omega
    have hv_lt : ((ws1_b[i.toNat]'hi_ws1).setWidth 64).toNat < mrk.length := by
      rw [bv32_setWidth64_toNat, hmrk_len]; have h := hqb.2.2.2.1 i.toNat hi_lt
      rw [List.getElem?_eq_getElem hi_ws1, Option.getD_some] at h; omega
    viv_hsteps_nogrp
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    let v0 := ws1_b[i.toNat]'hi_ws1; let mrk' := mrk.set (v0.setWidth 64).toNat 0#8
    have hdom' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ j, (i + 1#64).toNat ≤ j ∧ j < qlen_c.toNat ∧ (ws1_b[j]?.getD 0#32).toNat = v := by
      intro v hv hne
      have hv_ne : v ≠ (v0.setWidth 64).toNat := by
        intro heq; subst heq; dsimp only [mrk'] at hne
        rw [List.getElem?_set_self hv_lt, Option.getD_some] at hne; exact hne rfl
      have hne0 : mrk[v]?.getD 0#8 ≠ 0#8 := by
        dsimp only [mrk'] at hne; rwa [List.getElem?_set_ne (Ne.symm hv_ne)] at hne
      obtain ⟨j, hj1, hj2, hjv⟩ := hmrk_dom v hv hne0
      have hjne : j ≠ i.toNat := by
        intro heq; subst heq; rw [List.getElem?_eq_getElem hi_ws1, Option.getD_some] at hjv
        rw [bv32_setWidth64_toNat] at hv_ne; exact hv_ne hjv.symm
      exact ⟨j, by rw [hi1]; omega, hj2, hjv⟩
    exact hrec (i + 1#64, ()) _ (by dsimp only; rw [hi1]; omega)
      ⟨mrk', by rw [hi1]; omega, by simp [mrk', hmrk_len], hdom', by dsimp only [mrk']; assumption⟩
  · have hi_ge : ¬ (i.toNat < qlen_c.toNat) := fun h => by
      have : i < qlen_c := BitVec.lt_def.mpr h; c0_bound
    have hmrk_clr : ∀ v < c.max_vars, mrk[v]?.getD 0#8 = 0#8 := fun v hv =>
      if h0 : mrk[v]?.getD 0#8 = 0#8 then h0 else by
        obtain ⟨j, hj1, hj2, _⟩ := hmrk_dom v hv h0; omega
    let inv2 : Val i32 × PUnit → Mem 64 → Prop := fun (k, ()) mk => ∃ lm : List (BitVec 8),
      k.toNat ≤ sz.toNat ∧ lm.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars, lm[l]?.getD 0#8 ≠ 0#8 →
        ∃ t, k.toNat ≤ t ∧ t < sz.toNat ∧ (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
      (FullMem c { s with
        core := { s.core with mrk := mrk, lit_mark := lm }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) mk
    refine wp_loop_inv (ts := [i32]) inv2 (fun (k, ()) _ => sz.toNat - k.toNat)
      (fun Js2 hJs2 => by
        rw [wp_jump]; exact hJs2 (0#32, ()) _ ⟨lm1, Nat.zero_le _, hlm1_len, fun l hl hne =>
          let ⟨t, ht, hteq⟩ := hlm1_dom l hl hne; ⟨t, Nat.zero_le _, ht, hteq⟩, hmi⟩)
      (fun Js2 (k, ()) mk ⟨lm, hk_le, hlm_len, hlm_dom, hmk⟩ hrec2 => ?_)
    rw [Blocks.get_here]; dsimp only; c0_hstep; c0_hstep
    · have hk_lt : k.toNat < sz.toNat := by c0_bound
      have hk_lt_tmp : k.toNat < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
      have hk_tmp : (k.setWidth 64).toNat < s.core.tmp.length := by
        rw [bv32_setWidth64_toNat, hcl.tmp_len_arr]; omega
      have hlt_eq : s.core.tmp[(k.setWidth 64).toNat]'hk_tmp = s.core.tmp[k.toNat]?.getD 0#32 :=
        Option.some.inj (by rw [← List.getElem?_eq_getElem hk_tmp, bv32_setWidth64_toNat,
          List.getElem?_eq_getElem hk_lt_tmp, Option.getD_some])
      have hl_lm : ((s.core.tmp[(k.setWidth 64).toNat]'hk_tmp).setWidth 64).toNat < lm.length := by
        rw [bv32_setWidth64_toNat, hlt_eq, hlm_len]; have := htmp_lt k.toNat hk_lt; omega
      viv_hsteps_nogrp
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
      let l0 := s.core.tmp[(k.setWidth 64).toNat]'hk_tmp
      let lm' := lm.set (l0.setWidth 64).toNat 0#8
      have hdom' : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 ≠ 0#8 →
          ∃ t, (k + 1#32).toNat ≤ t ∧ t < sz.toNat ∧ (s.core.tmp[t]?.getD 0#32).toNat = l := by
        intro l hl hne
        have hl_ne : l ≠ (l0.setWidth 64).toNat := by
          intro heq; subst heq; dsimp only [lm'] at hne
          rw [List.getElem?_set_self hl_lm, Option.getD_some] at hne; exact hne rfl
        have hne0 : lm[l]?.getD 0#8 ≠ 0#8 := by
          dsimp only [lm'] at hne; rwa [List.getElem?_set_ne (Ne.symm hl_ne)] at hne
        obtain ⟨t, ht1, ht2, htv⟩ := hlm_dom l hl hne0
        have htne : t ≠ k.toNat := by
          intro heq; subst heq; rw [bv32_setWidth64_toNat] at hl_ne
          dsimp only [l0] at hl_ne; rw [hlt_eq] at hl_ne; exact hl_ne htv.symm
        exact ⟨t, by rw [hk1]; omega, ht2, htv⟩
      exact hrec2 (k + 1#32, ()) _ (by dsimp only; rw [hk1]; omega)
        ⟨lm', by rw [hk1]; omega, by simp [lm', hlm_len], hdom', by dsimp only [lm']; assumption⟩
    · have hk_ge : ¬ (k.toNat < sz.toNat) := fun h => by
        have : k < sz := BitVec.lt_def.mpr h; c0_bound
      have hlm_clr : ∀ l < 2 * c.max_vars, lm[l]?.getD 0#8 = 0#8 := fun l hl =>
        if h0 : lm[l]?.getD 0#8 = 0#8 then h0 else by
          obtain ⟨t, ht1, ht2, _⟩ := hlm_dom l hl h0; omega
      viv_hsteps_nogrp
      · have ht : taut_c = true := by c0_bound
        exact hQ 0xFFFFFFFF#32 mrk lm 0xFFFFFFFFFFFFFFFF#64 _
          (s13_deduce_finish_sparse hspN (asz' := 0xFFFFFFFFFFFFFFFF#64) (rsz' := rsz_b)
            hmrk_len hlm_len hqb.2.1 hws2_b hmrk_clr hlm_clr)
          ⟨Or.inl rfl, fun h _ => absurd rfl h⟩ (fun h => absurd rfl h) (fun _ => rfl)
          (fun hf => absurd (ht.symm.trans hf) (by decide)) (by assumption)
      · have hf : taut_c = false := by c0_bound
        exact hQ olen_c mrk lm asz_b _
          (s13_deduce_finish_sparse hspN (asz' := asz_b) (rsz' := rsz_b)
            hmrk_len hlm_len hqb.2.1 hws2_b hmrk_clr hlm_clr)
          hsub_b hsub_w (fun ht => absurd (hf.symm.trans ht) (by decide))
          (fun _ => ⟨rfl, rfl⟩) hmk

/-! ## 2. Phase-2 Loop & Step WPs -/

private abbrev deducePhase2BinExpr
    (h pMark pLevel pWs1 pTrl pTpos pVars : Val i64)
    (v_bv rsn_bv olen_c : Val i32) (qlen_c qi1 : Val i64) (taut_c : Val .bool)
    (J30 : Cont [i64, i64, i32, .bool]) (J50 : Cont [i64]) : Expr Val Cont [i32] :=
  fvOp (OpCode.and i32) (Arg.var rsn_bv, Arg.imm 2147483647, ()) fun p53 =>
  fvOp (OpCode.zext 32 64) (Arg.var v_bv, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pTpos, Arg.var p.fst, ()) fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld_pos =>
  fvOp (OpCode.zext 32 64) (Arg.var ld_pos, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pTrl, Arg.var p.fst, ()) fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld_lit0 =>
  Expr.call "full_viv_subsumes_bin_m6" (as := [i64, i32, i32]) (bs := [.bool])
    (Arg.var h, Arg.var ld_lit0, Arg.var p53.fst, ()) fun ok =>
  Expr.jnz (Arg.var ok.fst)
    (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
     Expr.store (Arg.imm (t := i64) 18446744073709551614) (Arg.var p.fst)
       (Expr.jump J30 (Arg.var qlen_c, Arg.var qi1, Arg.var olen_c, Arg.var taut_c, ())))
    (fvOp (OpCode.lshr i32) (Arg.var p53.fst, Arg.imm 1, ()) fun p63 =>
     Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p65 =>
       Expr.jump J50 (Arg.var p65.fst, ())) Blocks.nil) fun J64 =>
     deducePushExpr pVars pMark pLevel pWs1 p63.fst qlen_c J64.fst)

private theorem deduce_phase2_bin_branch_wp (Γ : Env)
    (hSubBin : Γ.Has "full_viv_subsumes_bin_m6" fullVivSubsumesBinM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sp : FullState} {R : Mem 64 → Prop}
    {mrk_c lm1 : List (BitVec 8)} {ws1_c ws2_c : List (BitVec 32)} {rsz_c : BitVec 64}
    {qlen_c qi_c qi1 : Val i64} {olen_c sz cref implied v_bv rsn_bv : Val i32}
    {taut_c : Val .bool} {idx0 : Nat} {mc : Mem 64} {Q : Post [i32]} {X : XPost}
    {J30 : Cont [i64, i64, i32, .bool]} {J50 : Cont [i64]}
    (hspN : S13SparseInvNoMark c F0 F_cur sp)
    (hq_ok : VivQueueOk c sp mrk_c ws1_c qlen_c.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_len : ws2_c.length = 2 * c.max_vars)
    (hcv_eq : sp.core.cur_vars = s.core.cur_vars) (htmp_eq : sp.core.tmp = s.core.tmp)
    (hvals_eq : sp.core.vals = s.core.vals) (hrsns_eq_s : sp.core.rsns = s.core.rsns)
    (hlvl_eq : sp.core.lvl = s.core.lvl)
    (hqi_lt : qi_c.toNat < qlen_c.toNat) (hv_eq : ws1_c[qi_c.toNat]?.getD 0#32 = v_bv)
    (hclo : VivClosedOk sp implied ws1_c ws2_c qi_c.toNat qlen_c.toNat olen_c.toNat taut_c)
    (ho_ok : VivOutOk sp implied ws1_c ws2_c qi_c.toNat olen_c.toNat taut_c)
    (hsd_ok : VivSeedOk sp cref implied ws1_c ws2_c qlen_c.toNat olen_c.toNat taut_c)
    (hidx0 : idx0 < sp.core.trail_end)
    (htrl0 : (sp.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat)
    (hrsn_eq : sp.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 = rsn_bv)
    (hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32) (hbin : rsn_bv &&& 0x80000000#32 ≠ 0#32)
    (hmc : (FullMem c { sp with
      core := { sp.core with mrk := mrk_c, lit_mark := lm1 }
      scratch := { sp.scratch with
        work_stk1 := ws1_c, work_stk2 := ws2_c,
        ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_c } } ⋆ R) mc)
    (hJ30 : ∀ qlen_n qi_n mrk_n (ws1_n : List (BitVec 32)) asz_n mn,
      VivQueueOk c sp mrk_n ws1_n qlen_n.toNat →
      (FullMem c { sp with
        core := { sp.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { sp.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_c, ant_sz := asz_n, res_sz := rsz_c } } ⋆ R) mn →
      asz_n ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat →
      S13SubRefOk sp asz_n → J30 (qlen_n, qi_n, olen_c, taut_c, ()) mn)
    (hJ50 : ∀ (qlen' : Val i64) mrk_n ws1_n mn,
      qlen_c.toNat ≤ qlen'.toNat → qlen'.toNat ≤ sp.core.cur_vars →
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_c[j]?) →
      VivQueueOk c sp mrk_n ws1_n qlen'.toNat →
      VivOutOk sp implied ws1_n ws2_c (qi_c.toNat + 1) olen_c.toNat taut_c →
      VivClosedOk sp implied ws1_n ws2_c (qi_c.toNat + 1) qlen'.toNat olen_c.toNat taut_c →
      VivSeedOk sp cref implied ws1_n ws2_c qlen'.toNat olen_c.toNat taut_c →
      (FullMem c { sp with
        core := { sp.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { sp.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_c,
          ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_c } } ⋆ R) mn →
      J50 (qlen', ()) mn) :
    wp Γ Q X (deducePhase2BinExpr c.hdr c.pMark c.pLevel c.pWorkStk1 c.pTrail c.pTrailPos
      (BitVec.ofNat 64 sp.core.cur_vars) v_bv rsn_bv olen_c qlen_c qi1 taut_c J30 J50) mc := by
  dsimp only [deducePhase2BinExpr]
  have hw := hspN.2.1; have hcl := hspN.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hv_cv : v_bv.toNat < sp.core.cur_vars := by rw [← hv_eq]; exact hq_ok.2.2.2.1 _ hqi_lt
  have hv_tp : (v_bv.setWidth 64).toNat < sp.core.trail_pos.length := by
    rw [bv32_setWidth64_toNat, hcl.trail_pos_len]; omega
  have hpos_eq : (sp.core.trail_pos[(v_bv.setWidth 64).toNat]'hv_tp).toNat = idx0 := by
    have hinv := hw.trail_pos_inv idx0 hidx0
    rw [htrl0] at hinv
    have htp_get : sp.core.trail_pos[v_bv.toNat]?.getD 0#32 =
        sp.core.trail_pos[(v_bv.setWidth 64).toNat]'hv_tp := by
      rw [← bv32_setWidth64_toNat v_bv, List.getElem?_eq_getElem hv_tp, Option.getD_some]
    rwa [← htp_get]
  have hpos_trl : ((sp.core.trail_pos[(v_bv.setWidth 64).toNat]'hv_tp).setWidth 64).toNat <
      sp.core.trl.length := by
    rw [bv32_setWidth64_toNat, hpos_eq]; have := hcl.trail_end_le; rw [hcl.trl_len]; omega
  let ot_bv := rsn_bv &&& 0x7FFFFFFF#32
  let lit0 := sp.core.trl[idx0]'(by have := hcl.trail_end_le; rw [hcl.trl_len]; omega)
  have hlit0_raw : sp.core.trl[(sp.core.trail_pos[(v_bv.setWidth 64).toNat]'hv_tp).setWidth
      64 |>.toNat]'hpos_trl = lit0 := Option.some.inj (by
    rw [← List.getElem?_eq_getElem hpos_trl, bv32_setWidth64_toNat, hpos_eq,
      List.getElem?_eq_getElem (by have := hcl.trail_end_le; rw [hcl.trl_len]; omega)])
  have hlit0_eq : lit0 = sp.core.trl[idx0]?.getD 0#32 := Option.some.inj (by
    dsimp only [lit0]
    rw [List.getElem?_eq_getElem (by have := hcl.trail_end_le; rw [hcl.trl_len]; omega),
      Option.getD_some])
  have hlit0_lt : lit0.toNat < 2 * sp.core.cur_vars := by
    rw [hlit0_eq]; exact hw.trail_lits_lt idx0 hidx0
  obtain ⟨hov_cv, hov_trl⟩ := deduce_bin_other_trl hw hidx0 htrl0 hrsn_eq hrsn_ne hbin
  have hot_lt : ot_bv.toNat < 2 * sp.core.cur_vars := by
    have := bv32_lshr1_toNat ot_bv; change (ot_bv >>> 1#32).toNat < sp.core.cur_vars at hov_cv
    omega
  have hl_state := s13_deduce_state_len (asz' := 0xFFFFFFFFFFFFFFFF#64) (rsz' := rsz_c)
    hspN.1 hq_ok.1 hlm1_len hq_ok.2.1 hws2_len
  have hw_state := s13_deduce_state_witness hspN.2.1 (mrk' := mrk_c) (lm' := lm1)
  dsimp only [fvOp]
  viv_hsteps_nogrp
  rw [hlit0_raw]
  viv_call hSubBin
  refine ⟨c, F0, F_cur, _, R, rfl, hl_state, hw_state, hlit0_lt, hot_lt, hmc, fun ok hok => ?_⟩
  viv_hsteps_nogrp
  · have hsub_ok := hok (by assumption)
    have hlm1_sp : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
        ∃ t < sz.toNat, (sp.core.tmp[t]?.getD 0#32).toNat = l := by
      simpa only [htmp_eq] using hlm1_dom
    have hw_sp : VivDeduceSubWitness F_cur sp sz.toNat := by
      refine deduce_bin_subWitness hw hcv_le hlm1_sp hidx0 hlit0_eq
        (by rw [← hlit0_eq] at htrl0; exact htrl0) (hrsn_eq ▸ hrsn_ne) (by rw [hrsn_eq])
        (by rw [hrsn_eq]; exact hbin) fun l hl => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact ⟨hlit0_lt, hsub_ok.1⟩
      · exact ⟨hot_lt, hsub_ok.2⟩
    have hw_s := vivDeduceSubWitness_of_pres hcv_eq htmp_eq hvals_eq hrsns_eq_s hlvl_eq hw_sp
    exact hJ30 qlen_c qi1 mrk_c ws1_c 0xFFFFFFFFFFFFFFFE#64 _ hq_ok (by assumption)
      (by decide) hw_s ⟨Or.inr (Or.inl rfl), fun _ h => absurd rfl h⟩
  · refine wp_join_group (ts := [i64])
      (fun (qlen', ()) mn => ∃ (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)),
        qlen_c.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ sp.core.cur_vars ∧
        (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_c[j]?) ∧
        VivQueueOk c sp mrk_n ws1_n qlen'.toNat ∧
        ((sp.core.lvl[ot_bv.toNat / 2]?.getD 0#32).toNat = 0 ∨
          ot_bv.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) ∧
        (FullMem c { sp with
          core := { sp.core with mrk := mrk_n, lit_mark := lm1 }
          scratch := { sp.scratch with
            work_stk1 := ws1_n, work_stk2 := ws2_c,
            ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_c } } ⋆ R) mn)
      (fun _ (qlen', ()) mn ⟨mrk_n, ws1_n, hq_cn, hqn_le, heq_cn, hqn_ok, hcov_o, hmn⟩ => by
        rw [Blocks.get_here]; dsimp only
        have hclo1 := vivClosed_mono_q hclo (Nat.le_of_lt hqi_lt) hq_cn
          (by have := hq_ok.2.1; omega) (by have := hqn_ok.2.1; omega) heq_cn
        have hcov_r : (sp.core.lvl[(sp.core.rsns[(ws1_n[qi_c.toNat]?.getD 0#32).toNat]?.getD
            0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat / 2]?.getD 0#32).toNat = 0 ∨
            (sp.core.rsns[(ws1_n[qi_c.toNat]?.getD 0#32).toNat]?.getD
              0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat / 2 ∈
            (ws1_n.take qlen'.toNat).map BitVec.toNat := by
          rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq]; exact hcov_o
        have hclo2 := vivClosed_step_bin hclo1 hw.trail_vars_nodup hidx0
          (by rw [heq_cn qi_c.toNat hqi_lt, hv_eq]; exact htrl0)
          (by rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq]; exact hrsn_ne)
          (by rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq]; exact hbin) hcov_r
        have ho_n := vivOut_mono_qi_len (qlen := qlen'.toNat)
          (vivOut_mono_qlen ho_ok (Nat.le_of_lt hqi_lt) (by have := hq_ok.2.1; omega)
            (by have := hqn_ok.2.1; omega) heq_cn)
          (by omega) (by have := hqn_ok.2.1; omega)
          (Or.inr (Or.inr (by rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq]; exact hrsn_ne)))
        have hsd_n := vivSeed_mono_q hsd_ok hq_cn (by have := hqn_ok.2.1; omega)
          (by have := hq_ok.2.1; omega) heq_cn
        exact hJ50 qlen' mrk_n ws1_n mn hq_cn hqn_le heq_cn hqn_ok ho_n hclo2 hsd_n hmn)
      (fun _ hJ64 => by
        refine deduce_push_branch_wp Γ hspN.1 hq_ok hov_cv hov_trl hmc
          fun qlen' mrk_n ws1_n mn hq_cn hqn_le heq_cn hqn_ok hcov_o hmn => ?_
        have hcov_o' : (sp.core.lvl[ot_bv.toNat / 2]?.getD 0#32).toNat = 0 ∨
            ot_bv.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat := by
          have heq : ((rsn_bv &&& 2147483647) >>> (1 : BitVec 32)).toNat = ot_bv.toNat / 2 :=
            bv32_lshr1_toNat ot_bv
          rw [← heq]; exact hcov_o
        exact hJ64 (qlen', ()) mn ⟨mrk_n, ws1_n, hq_cn, hqn_le, heq_cn, hqn_ok, hcov_o', hmn⟩)

private abbrev deducePhase2StepExpr
    (h pMark pLevel pArena pRsns pWs1 pWs2 pTrl pTpos pVars : Val i64)
    (cref sz implied : Val i32) (qlen_c qi_c : Val i64) (olen_c : Val i32) (taut_c : Val .bool)
    (J30 J31 : Cont [i64, i64, i32, .bool]) : Expr Val Cont [i32] :=
  fvOp (OpCode.mul i64) (Arg.var qi_c, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld_v =>
  fvOp (OpCode.add i64) (Arg.var qi_c, Arg.imm 1, ()) fun p_qi1 =>
  fvOp (OpCode.zext 32 64) (Arg.var ld_v, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pRsns, Arg.var p.fst, ()) fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld_r =>
  Expr.group (sig := [[i64, i32, .bool]]) (fun J48 => Blocks.cons (fun p49 =>
    Expr.jump J31 (Arg.var p49.fst, Arg.var p_qi1.fst,
      Arg.var p49.snd.fst, Arg.var p49.snd.snd.fst, ())) Blocks.nil) fun J48 =>
  fvOp (OpCode.cmp .eq i32 .bool (by decide)) (Arg.var ld_r, Arg.imm 4294967295, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (fvOp (OpCode.zext 32 64) (Arg.var ld_v, ()) fun p =>
     fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
     fvOp (OpCode.add i64) (Arg.var pTpos, Arg.var p.fst, ()) fun p =>
     Expr.load i32 (Arg.var p.fst) fun ld_pos =>
     fvOp (OpCode.zext 32 64) (Arg.var ld_pos, ()) fun p =>
     fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
     fvOp (OpCode.add i64) (Arg.var pTrl, Arg.var p.fst, ()) fun p =>
     Expr.load i32 (Arg.var p.fst) fun ld_lit =>
     Expr.group (sig := [[i32, .bool]]) (fun J58 => Blocks.cons (fun p59 =>
       Expr.jump J48.fst (Arg.var qlen_c, Arg.var p59.fst, Arg.var p59.snd.fst, ()))
       Blocks.nil) fun J58 =>
     fvOp (OpCode.cmp .eq i32 .bool (by decide)) (Arg.var ld_lit, Arg.var implied, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (Expr.jump J58.fst (Arg.var olen_c, Arg.imm true, ()))
       (Expr.group (sig := [[i32]]) (fun J60 => Blocks.cons (fun p61 =>
          Expr.jump J58.fst (Arg.var p61.fst, Arg.var taut_c, ())) Blocks.nil) fun J60 =>
        fvOp (OpCode.zext 32 64) (Arg.var olen_c, ()) fun p =>
        fvOp (OpCode.cmp .ult i64 .bool (by decide))
          (Arg.var p.fst, Arg.var pVars, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp (OpCode.zext 32 64) (Arg.var olen_c, ()) fun p =>
           fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
           fvOp (OpCode.add i64) (Arg.var pWs2, Arg.var p.fst, ()) fun p =>
           fvOp (OpCode.xor i32) (Arg.var ld_lit, Arg.imm 1, ()) fun p66 =>
           Expr.store (Arg.var p66.fst) (Arg.var p.fst)
             (fvOp (OpCode.add i32) (Arg.var olen_c, Arg.imm 1, ()) fun p67 =>
              Expr.jump J60.fst (Arg.var p67.fst, ())))
          (Expr.jump J60.fst (Arg.var olen_c, ()))))
    (Expr.group (sig := [[i64]]) (fun J50 => Blocks.cons (fun p51 =>
       Expr.jump J48.fst (Arg.var p51.fst, Arg.var olen_c, Arg.var taut_c, ()))
       Blocks.nil) fun J50 =>
     fvOp (OpCode.and i32) (Arg.var ld_r, Arg.imm 2147483648, ()) fun p =>
     fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (deducePhase2BinExpr h pMark pLevel pWs1 pTrl pTpos pVars ld_v ld_r olen_c qlen_c
         p_qi1.fst taut_c J30 J50.fst)
       (s13DeduceLargeRsnExpr h pVars pMark pLevel pArena pWs1 cref sz ld_r ld_v
         qlen_c p_qi1.fst olen_c taut_c J30 J50.fst))

private theorem deduce_phase2_step_wp (Γ : Env)
    (hPromote : Γ.Has "full_viv_recompute_promote_fid" vivRecomputePromoteSpec)
    (hSubBin : Γ.Has "full_viv_subsumes_bin_m6" fullVivSubsumesBinM6Spec)
    (hSubCl : Γ.Has "full_viv_subsumes_cl_m6" fullVivSubsumesClM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {ar_c mclr_c : List (BitVec 32)} {R : Mem 64 → Prop}
    {mrk_c lm1 : List (BitVec 8)} {ws1_c ws2_c : List (BitVec 32)} {rsz_c : BitVec 64}
    {qlen_c qi_c : Val i64} {olen_c sz cref implied : Val i32} {taut_c : Val .bool}
    {mc : Mem 64} {Q : Post [i32]} {X : XPost}
    {J30 : Cont [i64, i64, i32, .bool]} {J31 : Cont [i64, i64, i32, .bool]}
    (hspN : S13SparseInvNoMark c F0 F_cur
      { s with core := { s.core with arena := ar_c, min_clr := mclr_c } })
    (hpres : S13ArPres s
      { s with core := { s.core with arena := ar_c, min_clr := mclr_c } })
    (hq_ok : VivQueueOk c
      { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
      mrk_c ws1_c qlen_c.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_len : ws2_c.length = 2 * c.max_vars)
    (himp_ok : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefs
      { s with core := { s.core with arena := ar_c, min_clr := mclr_c } })
    (hconfl_sp : implied = 0xFFFFFFFF#32 → FullVivConflictOk F_cur
        { s with core := { s.core with arena := ar_c, min_clr := mclr_c } } ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits
            { s with core := { s.core with arena := ar_c, min_clr := mclr_c } } cref.toNat,
          s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hqi_lt : qi_c.toNat < qlen_c.toNat)
    (hclo : VivClosedOk { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
      implied ws1_c ws2_c qi_c.toNat qlen_c.toNat olen_c.toNat taut_c)
    (ho_ok : VivOutOk { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
      implied ws1_c ws2_c qi_c.toNat olen_c.toNat taut_c)
    (hsd_ok : VivSeedOk { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
      cref implied ws1_c ws2_c qlen_c.toNat olen_c.toNat taut_c)
    (hmc : (FullMem c { s with
      core := { s.core with arena := ar_c, min_clr := mclr_c, mrk := mrk_c, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_c, work_stk2 := ws2_c,
        ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_c } } ⋆ R) mc)
    (hJ30 : ∀ (ar_n mclr_n : List (BitVec 32)) qlen_n qi_n mrk_n
        (ws1_n : List (BitVec 32)) asz_n rsz_n mn,
      let s_n : FullState := { s with core := { s.core with arena := ar_n, min_clr := mclr_n } }
      S13SparseInvNoMark c F0 F_cur s_n → S13ArPres s s_n →
      VivQueueOk c s_n mrk_n ws1_n qlen_n.toNat → S13SubRefOk s_n asz_n →
      asz_n ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat →
      (FullMem c { s_n with
        core := { s_n.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s_n.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_c, ant_sz := asz_n, res_sz := rsz_n } } ⋆ R) mn →
      J30 (qlen_n, qi_n, olen_c, taut_c, ()) mn)
    (hJ31 : ∀ (ar_n mclr_n : List (BitVec 32)) qlen_n mrk_n (ws1_n ws2_n : List (BitVec 32))
        (olen_n : Val i32) (taut_n : Val .bool) (rsz_n : BitVec 64) mn,
      let s_n : FullState := { s with core := { s.core with arena := ar_n, min_clr := mclr_n } }
      S13SparseInvNoMark c F0 F_cur s_n → S13ArPres s s_n →
      qlen_c.toNat ≤ qlen_n.toNat → qlen_n.toNat ≤ s.core.cur_vars →
      (qi_c + 1#64).toNat ≤ qlen_n.toNat →
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_c[j]?) → ws2_n.length = 2 * c.max_vars →
      VivQueueOk c s_n mrk_n ws1_n qlen_n.toNat →
      VivOutOk s_n implied ws1_n ws2_n (qi_c + 1#64).toNat olen_n.toNat taut_n →
      VivClosedOk s_n implied ws1_n ws2_n (qi_c + 1#64).toNat qlen_n.toNat olen_n.toNat taut_n →
      VivSeedOk s_n cref implied ws1_n ws2_n qlen_n.toNat olen_n.toNat taut_n →
      (FullMem c { s_n with
        core := { s_n.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s_n.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_n,
          ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_n } } ⋆ R) mn →
      J31 (qlen_n, qi_c + 1#64, olen_n, taut_n, ()) mn) :
    wp Γ Q X (deducePhase2StepExpr c.hdr c.pMark c.pLevel c.pArena c.pReason c.pWorkStk1
      c.pWorkStk2 c.pTrail c.pTrailPos (BitVec.ofNat 64 s.core.cur_vars)
      cref sz implied qlen_c qi_c olen_c taut_c J30 J31) mc := by
  let sp : FullState := { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
  have hspN' : S13SparseInvNoMark c F0 F_cur sp := hspN
  have hq_ok' : VivQueueOk c sp mrk_c ws1_c qlen_c.toNat := hq_ok
  have hw := hspN'.2.1; have hcl := hspN'.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hqi_ws1 : qi_c.toNat < ws1_c.length := by have := hq_ok'.2.1; have := hq_ok'.2.2.1; omega
  have hqi_64 : qi_c.toNat < 2 ^ 64 := by have := hq_ok'.2.2.1; omega
  have hqi1 : (qi_c + 1#64).toNat = qi_c.toNat + 1 := by have := hq_ok'.2.2.1; bv_omega
  let v_bv := ws1_c[qi_c.toNat]'hqi_ws1
  have hv_eq : ws1_c[qi_c.toNat]?.getD 0#32 = v_bv := by
    rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]
  have hv_cv : v_bv.toNat < sp.core.cur_vars := by rw [← hv_eq]; exact hq_ok'.2.2.2.1 _ hqi_lt
  have hv_rsns : (v_bv.setWidth 64).toNat < sp.core.rsns.length := by
    rw [bv32_setWidth64_toNat, hcl.rsns_len]; omega
  let rsn_bv := sp.core.rsns[(v_bv.setWidth 64).toNat]'hv_rsns
  have hrsn_eq : sp.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 = rsn_bv := Option.some.inj (by
    dsimp only [rsn_bv]
    rw [← bv32_setWidth64_toNat v_bv, List.getElem?_eq_getElem hv_rsns, Option.getD_some])
  obtain ⟨_, idx0, hidx0, htrl0⟩ := hq_ok'.2.2.2.2.2.1 qi_c.toNat hqi_lt
  rw [hv_eq] at htrl0
  dsimp only [deducePhase2StepExpr, fvOp]
  viv_hsteps_nogrp
  refine wp_join_group (ts := [i64, i32, .bool])
    (fun (qlen_n, olen_n, taut_n, ()) mn =>
      ∃ (ar_n : List (BitVec 32)) (mclr_n : List (BitVec 32)) (mrk_n : List (BitVec 8))
        (ws1_n : List (BitVec 32)) (ws2_n : List (BitVec 32)) (rsz_n : BitVec 64),
      let s_n : FullState := { s with core := { s.core with arena := ar_n, min_clr := mclr_n } }
      S13SparseInvNoMark c F0 F_cur s_n ∧ S13ArPres s s_n ∧
      qlen_c.toNat ≤ qlen_n.toNat ∧ qlen_n.toNat ≤ s.core.cur_vars ∧
      (qi_c + 1#64).toNat ≤ qlen_n.toNat ∧
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_c[j]?) ∧ ws2_n.length = 2 * c.max_vars ∧
      VivQueueOk c s_n mrk_n ws1_n qlen_n.toNat ∧
      VivOutOk s_n implied ws1_n ws2_n (qi_c + 1#64).toNat olen_n.toNat taut_n ∧
      VivClosedOk s_n implied ws1_n ws2_n (qi_c + 1#64).toNat qlen_n.toNat olen_n.toNat taut_n ∧
      VivSeedOk s_n cref implied ws1_n ws2_n qlen_n.toNat olen_n.toNat taut_n ∧
      (FullMem c { s_n with
        core := { s_n.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s_n.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_n,
          ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_n } } ⋆ R) mn)
    (fun _ (qlen_n, olen_n, taut_n, ()) mn ⟨ar_n, mclr_n, mrk_n, ws1_n, ws2_n, rsz_n,
        hsp_n, hpres_n, h1, h2, h3, h3b, h4, h5, h6, h7, h8, hmn⟩ => by
      rw [Blocks.get_here]; dsimp only
      exact hJ31 ar_n mclr_n qlen_n mrk_n ws1_n ws2_n olen_n taut_n rsz_n mn
        hsp_n hpres_n h1 h2 h3 h3b h4 h5 h6 h7 h8 hmn)
    (fun _ hJ48 => ?_)
  viv_hsteps_nogrp
  · have hrsn_ff : rsn_bv = 0xFFFFFFFF#32 := by c0_bound
    have hrsn_ff' : sp.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
      hrsn_eq.trans hrsn_ff
    have hv_tp : (v_bv.setWidth 64).toNat < sp.core.trail_pos.length := by
      rw [bv32_setWidth64_toNat, hcl.trail_pos_len]; omega
    have hpos_eq : (sp.core.trail_pos[(v_bv.setWidth 64).toNat]'hv_tp).toNat = idx0 := by
      have hinv := hw.trail_pos_inv idx0 hidx0
      rw [htrl0] at hinv
      have htp_get : sp.core.trail_pos[v_bv.toNat]?.getD 0#32 =
          sp.core.trail_pos[(v_bv.setWidth 64).toNat]'hv_tp := by
        rw [← bv32_setWidth64_toNat v_bv, List.getElem?_eq_getElem hv_tp, Option.getD_some]
      rwa [← htp_get]
    have hpos_trl : ((sp.core.trail_pos[(v_bv.setWidth 64).toNat]'hv_tp).setWidth 64).toNat <
        sp.core.trl.length := by
      rw [bv32_setWidth64_toNat, hpos_eq]; have := hcl.trail_end_le; rw [hcl.trl_len]; omega
    let lit := sp.core.trl[idx0]'(by have := hcl.trail_end_le; rw [hcl.trl_len]; omega)
    have hlit_raw : sp.core.trl[((sp.core.trail_pos[(v_bv.setWidth 64).toNat]'hv_tp).setWidth
        64).toNat]'hpos_trl = lit := Option.some.inj (by
      rw [← List.getElem?_eq_getElem hpos_trl, bv32_setWidth64_toNat, hpos_eq,
        List.getElem?_eq_getElem (by have := hcl.trail_end_le; rw [hcl.trl_len]; omega)])
    have hlit_eq : lit = sp.core.trl[idx0]?.getD 0#32 := Option.some.inj (by
      dsimp only [lit]
      rw [List.getElem?_eq_getElem (by have := hcl.trail_end_le; rw [hcl.trl_len]; omega),
        Option.getD_some])
    viv_hsteps_nogrp
    rw [hlit_raw]
    refine wp_join_group (ts := [i32, .bool])
      (fun (olen_n, taut_n, ()) mn => ∃ ws2_n : List (BitVec 32),
        ws2_n.length = 2 * c.max_vars ∧
        VivOutOk sp implied ws1_c ws2_n (qi_c.toNat + 1) olen_n.toNat taut_n ∧
        VivClosedOk sp implied ws1_c ws2_n (qi_c.toNat + 1) qlen_c.toNat olen_n.toNat taut_n ∧
        VivSeedOk sp cref implied ws1_c ws2_n qlen_c.toNat olen_n.toNat taut_n ∧
        (FullMem c { sp with
          core := { sp.core with mrk := mrk_c, lit_mark := lm1 }
          scratch := { sp.scratch with
            work_stk1 := ws1_c, work_stk2 := ws2_n,
            ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_c } } ⋆ R) mn)
      (fun _ (olen_n, taut_n, ()) mn ⟨ws2_n, hws2_n, ho_n, hclo_n, hsd_n, hmn⟩ => by
        rw [Blocks.get_here]; dsimp only
        exact hJ48 (qlen_c, olen_n, taut_n, ()) mn ⟨ar_c, mclr_c, mrk_c,
          ws1_c, ws2_n, rsz_c, hspN, hpres, Nat.le_refl _, hq_ok'.2.2.1,
          by rw [hqi1]; omega, fun _ _ => rfl, hws2_n, hq_ok, (by rwa [hqi1]),
          (by rwa [hqi1]), hsd_n, hmn⟩)
      (fun _ hJ58 => ?_)
    viv_hsteps_nogrp
    · have hrsn_qi : sp.core.rsns[(ws1_c[qi_c.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
          0xFFFFFFFF#32 := by rw [hv_eq]; exact hrsn_ff'
      exact hJ58 (olen_c, true, ()) _ ⟨ws2_c, hws2_len, fun h => Bool.noConfusion h,
        s13_vivClosed_taut_true hclo hrsn_qi, fun h => Bool.noConfusion h, hmc⟩
    · have hlit_ne : lit ≠ implied := by c0_bound
      have hrsn_qi : sp.core.rsns[(ws1_c[qi_c.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
          0xFFFFFFFF#32 := by rw [hv_eq]; exact hrsn_ff'
      refine wp_join_group (ts := [i32])
        (fun (olen_n, ()) mn => ∃ ws2_n : List (BitVec 32),
          ws2_n.length = 2 * c.max_vars ∧
          VivOutOk sp implied ws1_c ws2_n (qi_c.toNat + 1) olen_n.toNat taut_c ∧
          VivClosedOk sp implied ws1_c ws2_n (qi_c.toNat + 1) qlen_c.toNat olen_n.toNat taut_c ∧
          VivSeedOk sp cref implied ws1_c ws2_n qlen_c.toNat olen_n.toNat taut_c ∧
          (FullMem c { sp with
            core := { sp.core with mrk := mrk_c, lit_mark := lm1 }
            scratch := { sp.scratch with
              work_stk1 := ws1_c, work_stk2 := ws2_n,
              ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_c } } ⋆ R) mn)
        (fun _ (olen_n, ()) mn ⟨ws2_n, hws2_n, ho_n, hclo_n, hsd_n, hmn⟩ => by
          rw [Blocks.get_here]; dsimp only
          exact hJ58 (olen_n, taut_c, ()) mn ⟨ws2_n, hws2_n, ho_n, hclo_n, hsd_n, hmn⟩)
        (fun _ hJ60 => ?_)
      viv_hsteps_nogrp
      · by_cases htaut : taut_c = true
        · subst htaut
          have hole_ws2 : (olen_c.setWidth 64).toNat < ws2_c.length := by
            have hlt : (olen_c.setWidth 64).toNat < (BitVec.ofNat 64 sp.core.cur_vars).toNat := by
              c0_bound
            rw [bv32_setWidth64_toNat] at hlt ⊢
            have hlt2 : (BitVec.ofNat 64 sp.core.cur_vars).toNat = sp.core.cur_vars := by
              rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
            omega
          viv_hsteps_nogrp
          let ws2_t := ws2_c.set (olen_c.setWidth 64).toNat (lit ^^^ 1#32)
          exact hJ60 (olen_c + 1#32, ()) _ ⟨ws2_t, by simp [ws2_t, hws2_len],
            fun h => Bool.noConfusion h, s13_vivClosed_taut_true hclo hrsn_qi,
            fun h => Bool.noConfusion h, by dsimp only [ws2_t]; assumption⟩
        · have ht_f : taut_c = false := Bool.eq_false_iff.mpr htaut
          subst ht_f
          have hne_imp : implied ≠ 0xFFFFFFFF#32 → sp.core.trl[idx0]?.getD 0#32 ≠ implied :=
            fun _ heq => hlit_ne (hlit_eq.trans heq)
          obtain ⟨hole_cv, _, ho_n, hclo_n, _⟩ := vivOut_push_step hw hq_ok' hqi_lt ho_ok hclo
            himp_ok hidx0 (by rw [hv_eq]; exact htrl0) (by rw [hv_eq]; exact hrsn_ff') hne_imp
            hws2_len hcv_le
          have hole1 : (olen_c + 1#32).toNat = olen_c.toNat + 1 := by bv_omega
          have hole_mod : (olen_c.setWidth 64).toNat = olen_c.toNat := bv32_setWidth64_toNat _
          viv_hsteps_nogrp
          let ws2_n := ws2_c.set olen_c.toNat (sp.core.trl[idx0]?.getD 0#32 ^^^ 1#32)
          have hws2_eq : ws2_c.set (olen_c.setWidth 64).toNat (lit ^^^ 1#32) = ws2_n := by
            dsimp only [ws2_n]; rw [hole_mod, hlit_eq]
          have hsd_n : VivSeedOk sp cref implied ws1_c ws2_n qlen_c.toNat (olen_c + 1#32).toNat
              false := s13_vivSeed_mono_ws2 hsd_ok (by rw [hole1]; omega) (by omega)
            (by dsimp only [ws2_n]; rw [hole1, List.length_set, hws2_len]; omega)
            (fun j hj => by dsimp only [ws2_n]; rw [List.getElem?_set_ne (by omega)])
          exact hJ60 (olen_c + 1#32, ()) _ ⟨ws2_n, by simp [ws2_n, hws2_len],
            by rw [hole1]; exact ho_n, by rw [hole1]; exact hclo_n, hsd_n,
            by rw [← hws2_eq]; assumption⟩
      · have hge : ¬ (olen_c.setWidth 64 < BitVec.ofNat 64 sp.core.cur_vars) := by c0_bound
        by_cases htaut : taut_c = true
        · subst htaut
          exact hJ60 (olen_c, ()) _ ⟨ws2_c, hws2_len, fun h => Bool.noConfusion h,
            s13_vivClosed_taut_true hclo hrsn_qi, fun h => Bool.noConfusion h, hmc⟩
        · have ht_f : taut_c = false := Bool.eq_false_iff.mpr htaut
          subst ht_f
          have hne_imp : implied ≠ 0xFFFFFFFF#32 → sp.core.trl[idx0]?.getD 0#32 ≠ implied :=
            fun _ heq => hlit_ne (hlit_eq.trans heq)
          have hpush := vivOut_push_lt hw hq_ok' hcv_le hqi_lt ho_ok himp_ok hidx0
            (by rw [hv_eq]; exact htrl0) hne_imp
            (by have h1 : olen_c.toNat ≤ s.core.cur_vars := (ho_ok rfl).1
                have h2 : s.core.cur_vars ≤ c.max_vars := hcv_le; rw [hws2_len]; omega)
          have hlt64 : olen_c.setWidth 64 < BitVec.ofNat 64 sp.core.cur_vars := by
            rw [BitVec.lt_def, bv32_setWidth64_toNat, BitVec.toNat_ofNat]
            rw [Nat.mod_eq_of_lt (by omega)]
            exact hpush.1
          exact absurd hlt64 hge
  · have hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32 := by c0_bound
    refine wp_join_group (ts := [i64])
      (fun (qlen', ()) mn =>
        ∃ (ar_n : List (BitVec 32)) (mclr_n : List (BitVec 32)) (mrk_n : List (BitVec 8))
          (ws1_n : List (BitVec 32)) (rsz_n : BitVec 64),
        let s_n : FullState := { s with core := { s.core with arena := ar_n, min_clr := mclr_n } }
        S13SparseInvNoMark c F0 F_cur s_n ∧ S13ArPres s s_n ∧
        qlen_c.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
        (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_c[j]?) ∧
        VivQueueOk c s_n mrk_n ws1_n qlen'.toNat ∧
        VivOutOk s_n implied ws1_n ws2_c (qi_c.toNat + 1) olen_c.toNat taut_c ∧
        VivClosedOk s_n implied ws1_n ws2_c (qi_c.toNat + 1) qlen'.toNat olen_c.toNat taut_c ∧
        VivSeedOk s_n cref implied ws1_n ws2_c qlen'.toNat olen_c.toNat taut_c ∧
        (FullMem c { s_n with
          core := { s_n.core with mrk := mrk_n, lit_mark := lm1 }
          scratch := { s_n.scratch with
            work_stk1 := ws1_n, work_stk2 := ws2_c,
            ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_n } } ⋆ R) mn)
      (fun _ (qlen', ()) mn ⟨ar_n, mclr_n, mrk_n, ws1_n, rsz_n, hsnN, hpres_n, hq_cn, hqn_le,
          heq_cn, hqn_ok, ho_n, hclo_n, hsd_n, hmn⟩ => by
        rw [Blocks.get_here]; dsimp only
        exact hJ48 (qlen', olen_c, taut_c, ()) mn ⟨ar_n, mclr_n, mrk_n, ws1_n, ws2_c, rsz_n,
          hsnN, hpres_n, hq_cn, hqn_le, by rw [hqi1]; omega, heq_cn, hws2_len, hqn_ok,
          (by rwa [hqi1]), (by rwa [hqi1]), hsd_n, hmn⟩)
      (fun _ hJ50 => ?_)
    c0_hstep; c0_hstep; c0_hstep
    · have hbin : rsn_bv &&& 0x80000000#32 ≠ 0#32 := by c0_bound
      refine deduce_phase2_bin_branch_wp Γ hSubBin (s := s) (sp := sp) hspN' hq_ok' hlm1_len
        hlm1_dom hws2_len rfl rfl rfl rfl rfl hqi_lt hv_eq hclo ho_ok hsd_ok hidx0 htrl0 hrsn_eq
        hrsn_ne hbin hmc ?_ ?_
      · intro qlen_n qi_n mrk_n ws1_n asz_n mn hqn_ok hmn hasz hwsub hsub_sp
        exact hJ30 ar_c mclr_c qlen_n qi_n mrk_n ws1_n asz_n rsz_c mn hspN hpres hqn_ok hsub_sp
          hasz hwsub hmn
      · intro qlen' mrk_n ws1_n mn hq_cn hqn_le heq_cn hqn_ok ho_n hclo_n hsd_n hmn
        exact hJ50 (qlen', ()) mn ⟨ar_c, mclr_c, mrk_n, ws1_n, rsz_c, hspN, hpres, hq_cn, hqn_le,
          heq_cn, hqn_ok, ho_n, hclo_n, hsd_n, hmn⟩
    · have hnbin : rsn_bv &&& 0x80000000#32 = 0#32 := by c0_bound
      obtain ⟨href_r, hng_r, hlits_r⟩ :=
        deduce_large_rsn_facts hw hidx0 htrl0 hrsn_eq hrsn_ne hnbin
      refine s13_deduce_large_rsn_wp Γ hPromote hSubCl (s := sp) hspN' hq_ok' hlm1_len hlm1_dom
        hws2_len href_r hng_r hrsn_ne hidx0 htrl0 hrsn_eq hlits_r hmc ?_ ?_
      · intro ar' mclr' rsz_n mex _ hs_nN hpres_n hsub_n hwsub_n hmex
        have hpres_t : S13ArPres s
            { s with core := { s.core with arena := ar', min_clr := mclr' } } :=
          s13ArPres_trans hpres hpres_n
        have hqn_ok : VivQueueOk c
            { s with core := { s.core with arena := ar', min_clr := mclr' } }
            mrk_c ws1_c qlen_c.toNat := s13_vivQueue_ar_eq rfl rfl rfl rfl hq_ok'
        have hasz_ne : rsn_bv.setWidth 64 ≠ 0xFFFFFFFFFFFFFFFF#64 := by
          intro heq; have h1 := congrArg BitVec.toNat heq; rw [bv32_setWidth64_toNat] at h1
          have h2 := rsn_bv.isLt; change rsn_bv.toNat = 18446744073709551615 at h1; omega
        have hwsub_s := vivDeduceSubWitness_of_pres rfl rfl rfl rfl rfl hwsub_n
        exact hJ30 ar' mclr' qlen_c (qi_c + 1#64) mrk_c ws1_c (rsn_bv.setWidth 64) rsz_n mex
          hs_nN hpres_t hqn_ok hsub_n hasz_ne hwsub_s hmex
      · intro ar' mclr' qlen' mrk_n ws1_n rsz_n mlg s_n hs_nN hpres_n hq_cn hqn_le heq_cn hqn_ok
          hlits_cov hmlg
        have hpres_t : S13ArPres s
            { s with core := { s.core with arena := ar', min_clr := mclr' } } :=
          s13ArPres_trans hpres hpres_n
        have hclo_sp1 := vivClosed_mono_q hclo (Nat.le_of_lt hqi_lt) hq_cn
          (by have := hq_ok'.2.1; omega) (by have := hqn_ok.2.1; omega) heq_cn
        have hclo_sp2 := vivClosed_step_large hclo_sp1 hw.trail_vars_nodup hidx0
          (by rw [heq_cn qi_c.toNat hqi_lt, hv_eq]; exact htrl0)
          (by rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq]; exact hrsn_ne)
          (by rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq]; exact hnbin)
          (fun q hq hne => by
            rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq] at hq
            rw [heq_cn qi_c.toNat hqi_lt, hv_eq] at hne; exact hlits_cov q hq hne)
          (fun q hq => by
            rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq] at hq
            rcases hlits_r q hq with hq_tr | ⟨m, hm1, hm2, _⟩
            · exact Or.inl hq_tr
            · exact Or.inr ⟨m, hm1, hm2⟩)
        have hclo_n := s13_vivClosed_ar_eq (s := sp) (s' := s_n) hw
          (s13_vivQueue_ar_eq rfl rfl rfl rfl hqn_ok)
          (by rw [hqi1] at *; omega) rfl rfl rfl rfl rfl hpres_n hclo_sp2
        have ho_sp1 := vivOut_mono_qi_len (qlen := qlen'.toNat)
          (vivOut_mono_qlen ho_ok (Nat.le_of_lt hqi_lt) (by have := hq_ok'.2.1; omega)
            (by have := hqn_ok.2.1; omega) heq_cn)
          (by omega) (by have := hqn_ok.2.1; omega)
          (Or.inr (Or.inr (by rw [heq_cn qi_c.toNat hqi_lt, hv_eq, hrsn_eq]; exact hrsn_ne)))
        have ho_n := s13_vivOut_ar_eq rfl rfl ho_sp1
        have hsd_sp1 := vivSeed_mono_q hsd_ok hq_cn (by have := hqn_ok.2.1; omega)
          (by have := hq_ok'.2.1; omega) heq_cn
        have hsd_n := s13_vivSeed_ar_eq (_c := c) (_F0 := F0) (s := sp) (s' := s_n) hconfl_sp
          hcr_ref rfl rfl rfl rfl rfl hpres_n hsd_sp1
        exact hJ50 (qlen', ()) mlg ⟨ar', mclr', mrk_n, ws1_n, rsz_n, hs_nN, hpres_t,
          hq_cn, hqn_le, heq_cn, hqn_ok, ho_n, hclo_n, hsd_n, hmlg⟩

private abbrev DeducePost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (sz : Val i32) (Q : Post [i32]) : Prop :=
  ∀ (olen : Val i32) (ar' mclr' : List (BitVec 32)) (mrk' lm' : List (BitVec 8))
    (ws1' ws2' : List (BitVec 32)) (asz' rsz' : BitVec 64) (m' : Mem 64),
    let s' := { s with
      core := { s.core with arena := ar', min_clr := mclr', mrk := mrk', lit_mark := lm' }
      scratch := { s.scratch with
        work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } }
    FullSparseInvW c F0 F_cur s' → M6SubRefOk s' asz' →
    (asz' ≠ -1#64 → asz' ≠ -2#64 →
      asz'.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' asz'.toNat = false) →
    fullArenaClauseRefs s' = fullArenaClauseRefs s →
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) →
    (asz' = -1#64 → olen ≠ -1#32 → olen.toNat ≤ s.core.cur_vars ∧
      (∀ k < olen.toNat, (ws2'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
    (asz' ≠ -1#64 → olen ≠ -1#32 → olen.toNat ≤ s.core.cur_vars ∧
      (∀ k < olen.toNat, (ws2'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      VivDeduceSubWitness F_cur s sz.toNat) →
    (FullMem c s' ⋆ R) m' → Q (olen, ()) m'

private abbrev deducePhase2BodyExpr
    (h pMark pLitMark pTmp pLevel pArena pRsns pWs1 pWs2 pVars : Val i64)
    (cref sz implied : Val i32) (qlen_init : Arg Val i64) (olen_init : Arg Val i32) :
    Expr Val Cont [i32] :=
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 96, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun pTrl =>
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 360, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun pTpos =>
  Expr.group (sig := [[i64, i64, i32, .bool]]) (fun J30 => Blocks.cons (fun p31 =>
    s13DeduceClearExpr h pMark pLitMark pTmp pWs1 sz p31.fst p31.snd.snd.fst
      p31.snd.snd.snd.fst) Blocks.nil) fun J30 =>
  Expr.group (sig := [[i64, i64, i32, .bool]]) (fun J31 => Blocks.cons (fun p32 =>
    fvOp (OpCode.cmp .ult i64 .bool (by decide))
      (Arg.var p32.snd.fst, Arg.var p32.fst, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
       Expr.load i64 (Arg.var p.fst) fun ld_asz =>
       fvOp (OpCode.cmp .eq i64 .bool (by decide))
         (Arg.var ld_asz, Arg.imm 18446744073709551615, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
         (deducePhase2StepExpr h pMark pLevel pArena pRsns pWs1 pWs2 pTrl pTpos pVars
           cref sz implied p32.fst p32.snd.fst p32.snd.snd.fst p32.snd.snd.snd.fst J30.fst J31.fst)
         (Expr.jump J30.fst (Arg.var p32.fst, Arg.var p32.snd.fst,
           Arg.var p32.snd.snd.fst, Arg.var p32.snd.snd.snd.fst, ())))
      (Expr.jump J30.fst (Arg.var p32.fst, Arg.var p32.snd.fst,
        Arg.var p32.snd.snd.fst, Arg.var p32.snd.snd.snd.fst, ()))) Blocks.nil) fun J31 =>
  Expr.jump J31.fst (qlen_init, Arg.imm 0, olen_init, Arg.imm false, ())

private theorem deduce_phase2_wp (Γ : Env)
    (hPromote : Γ.Has "full_viv_recompute_promote_fid" vivRecomputePromoteSpec)
    (hSubBin : Γ.Has "full_viv_subsumes_bin_m6" fullVivSubsumesBinM6Spec)
    (hSubCl : Γ.Has "full_viv_subsumes_cl_m6" fullVivSubsumesClM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {ar_i mclr_i : List (BitVec 32)} {R : Mem 64 → Prop}
    {mrk_i lm1 : List (BitVec 8)} {ws1_i ws2_i : List (BitVec 32)} {asz_i rsz_i : BitVec 64}
    {qlen_i : Val i64} {olen_i sz cref implied : Val i32}
    {mi : Mem 64} {Q : Post [i32]} {X : XPost}
    (_hspW_s : FullSparseInvW c F0 F_cur s)
    (hpres_i : S13ArPres s { s with core := { s.core with arena := ar_i, min_clr := mclr_i } })
    (hspN_i : S13SparseInvNoMark c F0 F_cur
      { s with core := { s.core with arena := ar_i, min_clr := mclr_i } })
    (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hq_i : VivQueueOk c { s with core := { s.core with arena := ar_i, min_clr := mclr_i } }
      mrk_i ws1_i qlen_i.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_len : ws2_i.length = 2 * c.max_vars)
    (himp_ok : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    (himp_cov : implied ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
        implied.toNat / 2 ∈ ((ws1_i.take qlen_i.toNat).map BitVec.toNat))
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefs
      { s with core := { s.core with arena := ar_i, min_clr := mclr_i } })
    (hcr_ng : fullArenaClauseGarb
      { s with core := { s.core with arena := ar_i, min_clr := mclr_i } } cref.toNat = false)
    (hconfl : implied = 0xFFFFFFFF#32 → FullVivConflictOk F_cur
        { s with core := { s.core with arena := ar_i, min_clr := mclr_i } } ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits
            { s with core := { s.core with arena := ar_i, min_clr := mclr_i } } cref.toNat,
          s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (ho_i : VivOutOk { s with core := { s.core with arena := ar_i, min_clr := mclr_i } }
      implied ws1_i ws2_i 0 olen_i.toNat false)
    (hsub_i : S13SubRefOk
      { s with core := { s.core with arena := ar_i, min_clr := mclr_i } } asz_i)
    (hsub_w_i : asz_i ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat)
    (hsd_i : asz_i = 0xFFFFFFFFFFFFFFFF#64 →
      VivSeedOk { s with core := { s.core with arena := ar_i, min_clr := mclr_i } }
        cref implied ws1_i ws2_i qlen_i.toNat olen_i.toNat false)
    (hmi : (FullMem c { s with
      core := { s.core with arena := ar_i, min_clr := mclr_i, mrk := mrk_i, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_i, work_stk2 := ws2_i, ant_sz := asz_i, res_sz := rsz_i } } ⋆ R) mi)
    (hQ : DeducePost c F0 F_cur s R sz Q) :
    wp Γ Q X (deducePhase2BodyExpr c.hdr c.pMark c.pLitMark c.pTmp c.pLevel c.pArena c.pReason
      c.pWorkStk1 c.pWorkStk2 (BitVec.ofNat 64 s.core.cur_vars) cref sz implied
      (Arg.var qlen_i) (Arg.var olen_i)) mi := by
  let si : FullState := { s with core := { s.core with arena := ar_i, min_clr := mclr_i } }
  have hmi_f : (FullMem c { si with
      core := { si.core with mrk := mrk_i, lit_mark := lm1 }
      scratch := { si.scratch with
        work_stk1 := ws1_i, work_stk2 := ws2_i, ant_sz := asz_i, res_sz := rsz_i } } ⋆ R) mi := hmi
  dsimp only [deducePhase2BodyExpr, fvOp]
  viv_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64, i32, .bool])
    (fun (qlen_c, qi_c, olen_c, taut_c, ()) mn =>
      ∃ (ar_c : List (BitVec 32)) (mclr_c : List (BitVec 32)) (mrk_c : List (BitVec 8))
        (ws1_c : List (BitVec 32)) (ws2_c : List (BitVec 32)) (asz_c : BitVec 64)
        (rsz_c : BitVec 64),
      let sc : FullState := { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
      S13SparseInvNoMark c F0 F_cur sc ∧ S13ArPres s sc ∧
      VivQueueOk c sc mrk_c ws1_c qlen_c.toNat ∧ ws2_c.length = 2 * c.max_vars ∧
      S13SubRefOk sc asz_c ∧
      (taut_c = false → olen_c.toNat ≤ s.core.cur_vars ∧
        ∀ k < olen_c.toNat, (ws2_c[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (asz_c ≠ -1#64 → VivDeduceSubWitness F_cur s sz.toNat) ∧
      (asz_c = -1#64 → taut_c = false →
        qlen_c.toNat ≤ s.core.cur_vars ∧
        VivOutOk sc implied ws1_c ws2_c qlen_c.toNat olen_c.toNat false ∧
        VivClosedOk sc implied ws1_c ws2_c qlen_c.toNat qlen_c.toNat olen_c.toNat false ∧
        VivSeedOk sc cref implied ws1_c ws2_c qlen_c.toNat olen_c.toNat false ∧
        (implied ≠ 0xFFFFFFFF#32 →
          (sc.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
            implied.toNat / 2 ∈ ((ws1_c.take qlen_c.toNat).map BitVec.toNat))) ∧
      (FullMem c { sc with
        core := { sc.core with mrk := mrk_c, lit_mark := lm1 }
        scratch := { sc.scratch with
          work_stk1 := ws1_c, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) mn)
    (fun _ (qlen_c, qi_c, olen_c, taut_c, ()) mn ⟨ar_c, mclr_c, mrk_c, ws1_c, ws2_c, asz_c,
        rsz_c, hspN, hpres, hq_ok, hws2_len, hsub_c, hout_bd, hsub_w, hdone, hmn⟩ => by
      let sc : FullState := { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
      rw [Blocks.get_here]; dsimp only
      refine deduce_clear_exact_wp Γ hspN hsz_le htmp_lt hq_ok hlm1_len hlm1_dom hws2_len
        hsub_c hsub_w hmn fun ret mrk' lm' asz' m' hspW' hsub' hwsub' ht_t ht_f hm' => ?_
      let sf := { s with
        core := { s.core with arena := ar_c, min_clr := mclr_c, mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1_c, work_stk2 := ws2_c, ant_sz := asz', res_sz := rsz_c } }
      have hsub_s' : M6SubRefOk sf asz' := hsub'.1
      have hwsub_s : asz' ≠ -1#64 → ret ≠ -1#32 → ret.toNat ≤ s.core.cur_vars ∧
          (∀ k < ret.toNat, (ws2_c[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          VivDeduceSubWitness F_cur s sz.toNat := fun hasz hret => by
        have ht_bool : taut_c = false := by
          cases htc : taut_c with | false => rfl | true => exact absurd (ht_t htc) hret
        have hb := hout_bd ht_bool; rw [← (ht_f ht_bool).1] at hb
        exact ⟨hb.1, hb.2, vivDeduceSubWitness_of_pres rfl rfl rfl rfl rfl (hwsub' hasz)⟩
      have hrefs_eq : fullArenaClauseRefs sf = fullArenaClauseRefs s := hpres.1
      have hcl_eq : ∀ r ∈ fullArenaClauseRefs s,
          fullArenaClauseGarb sf r = fullArenaClauseGarb s r ∧
          fullArenaClauseSize sf r = fullArenaClauseSize s r ∧
          fullArenaClauseLits sf r = fullArenaClauseLits s r := fun r hr => hpres.2 r hr
      have hasz_ref : asz' ≠ -1#64 → asz' ≠ -2#64 →
          asz'.toNat ∈ fullArenaClauseRefs sf ∧ fullArenaClauseGarb sf asz'.toNat = false := hsub'.2
      have hent_s : asz' = -1#64 → ret ≠ -1#32 →
          ret.toNat ≤ s.core.cur_vars ∧
          (∀ k < ret.toNat, (ws2_c[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          ((ws2_c.take ret.toNat).map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((ws2_c.take ret.toNat).map BitVec.toNat)) := by
        intro hasz hret
        have ht_bool : taut_c = false := by
          cases htc : taut_c
          · rfl
          · exact absurd (ht_t htc) hret
        subst ht_bool
        obtain ⟨hret_eq, hasz_eq⟩ := ht_f rfl
        rw [hret_eq]
        obtain ⟨_, ho_end, hclo_end, hsd_end, hcov_end⟩ := hdone (hasz_eq.symm.trans hasz) rfl
        have hcv_le := hspN.1.core_ok.cur_vars_le
        have hcr_s : cref.toNat ∈ fullArenaClauseRefs s := by
          rw [← hpres_i.1]; exact hcr_ref
        have hsc_ref : cref.toNat ∈ fullArenaClauseRefs sc := by rw [hpres.1]; exact hcr_s
        have hsc_ng : fullArenaClauseGarb sc cref.toNat = false := by
          rw [(hpres.2 cref.toNat hcr_s).1, ← (hpres_i.2 cref.toNat hcr_s).1]; exact hcr_ng
        have hconfl_sc := s13_confl_ar_pres hpres_i hpres rfl rfl rfl rfl rfl rfl hcr_s hconfl
        obtain ⟨ho_cv, ho_lt, ho_nd, _, _, _⟩ := ho_end rfl
        have hent := deduce_phase2_sound hspN.2.1 hq_ok hcv_le hsc_ref hsc_ng hclo_end hsd_end
          himp_ok hconfl_sc hcov_end
        exact ⟨ho_cv, ho_lt, by simpa only [List.map_map, Function.comp_def] using ho_nd, hent⟩
      exact hQ ret ar_c mclr_c mrk' lm' ws1_c ws2_c asz' rsz_c m'
        hspW' hsub_s' hasz_ref hrefs_eq hcl_eq hent_s hwsub_s hm')
    (fun _ hJ30 => ?_)
  let loopInv : Val i64 × Val i64 × Val i32 × Val .bool × PUnit → Mem 64 → Prop :=
    fun (qlen_c, qi_c, olen_c, taut_c, ()) mc =>
      ∃ (ar_c : List (BitVec 32)) (mclr_c : List (BitVec 32)) (mrk_c : List (BitVec 8))
          (ws1_c : List (BitVec 32)) (ws2_c : List (BitVec 32)) (asz_c : BitVec 64)
          (rsz_c : BitVec 64),
        let sc : FullState := { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
        S13SparseInvNoMark c F0 F_cur sc ∧ S13ArPres s sc ∧
        qlen_i.toNat ≤ qlen_c.toNat ∧ qlen_c.toNat ≤ s.core.cur_vars ∧
        qi_c.toNat ≤ qlen_c.toNat ∧
        (∀ j < qlen_i.toNat, ws1_c[j]? = ws1_i[j]?) ∧
        ws2_c.length = 2 * c.max_vars ∧
        VivQueueOk c sc mrk_c ws1_c qlen_c.toNat ∧
        S13SubRefOk sc asz_c ∧
        (asz_c ≠ -1#64 → VivDeduceSubWitness F_cur s sz.toNat) ∧
        VivOutOk sc implied ws1_c ws2_c qi_c.toNat olen_c.toNat taut_c ∧
        (asz_c = -1#64 →
          VivClosedOk sc implied ws1_c ws2_c qi_c.toNat qlen_c.toNat olen_c.toNat taut_c ∧
          VivSeedOk sc cref implied ws1_c ws2_c qlen_c.toNat olen_c.toNat taut_c) ∧
        (FullMem c { sc with
          core := { sc.core with mrk := mrk_c, lit_mark := lm1 }
          scratch := { sc.scratch with
            work_stk1 := ws1_c, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) mc
  refine wp_loop_inv loopInv (fun (_, (qi_c, _)) _ => s.core.cur_vars - qi_c.toNat)
    (fun J31 hJ31 => ?_) (fun J31 a mc hinv hrec => ?_)
  · rw [wp_jump]
    exact hJ31 (qlen_i, 0#64, olen_i, false, ()) mi
      ⟨ar_i, mclr_i, mrk_i, ws1_i, ws2_i, asz_i, rsz_i, hspN_i, hpres_i, Nat.le_refl _,
        hq_i.2.2.1, Nat.zero_le _, fun _ _ => rfl, hws2_len, hq_i, hsub_i, hsub_w_i, ho_i,
        fun hasz => ⟨fun k hk _ _ _ => absurd hk (Nat.not_lt_zero _), hsd_i hasz⟩, hmi_f⟩
  · rcases a with ⟨qlen_c, qi_c, olen_c, taut_c, _⟩
    rcases hinv with ⟨ar_c, mclr_c, mrk_c, ws1_c, ws2_c, asz_c, rsz_c, hspN, hpres, hqi_q,
      hqc_le, hqi_le, heq_init, hws2_len, hq_ok, hsub_c, hsub_w, ho_ok, hcs_fn, hmc⟩
    let sc : FullState := { s with core := { s.core with arena := ar_c, min_clr := mclr_c } }
    have hcov_c : implied ≠ 0xFFFFFFFF#32 →
        (sc.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
          implied.toNat / 2 ∈ ((ws1_c.take qlen_c.toNat).map BitVec.toNat) := by
      intro himp
      rcases himp_cov himp with h0 | hmem
      · exact Or.inl h0
      · refine Or.inr ?_
        obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hmem
        obtain ⟨k, hkq⟩ := List.mem_iff_getElem?.mp hx
        rw [List.getElem?_take] at hkq
        split at hkq
        · rename_i hk
          refine List.mem_map.mpr ⟨x, List.mem_iff_getElem?.mpr ⟨k, ?_⟩, hxeq⟩
          rw [List.getElem?_take_of_lt (by omega), heq_init k hk]; exact hkq
        · cases hkq
    have hcr_s : cref.toNat ∈ fullArenaClauseRefs s := by
      rw [← hpres_i.1]; exact hcr_ref
    have hcr_ref_c : cref.toNat ∈ fullArenaClauseRefs sc := by rw [hpres.1]; exact hcr_s
    have hconfl_c := s13_confl_ar_pres hpres_i hpres rfl rfl rfl rfl rfl rfl hcr_s hconfl
    have hout_bd_c : taut_c = false → olen_c.toNat ≤ s.core.cur_vars ∧
        ∀ k < olen_c.toNat, (ws2_c[k]?.getD 0#32).toNat < 2 * s.core.cur_vars := fun ht =>
      ⟨(ho_ok ht).1, (ho_ok ht).2.1⟩
    rw [Blocks.get_here]; dsimp only [fvOp]
    c0_hstep; c0_hstep
    · have hqi_lt : qi_c.toNat < qlen_c.toNat := by c0_bound
      c0_hstep; c0_hstep; c0_hstep; c0_hstep
      · have hasz_eq : asz_c = 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
        subst hasz_eq
        obtain ⟨hclo, hsd_ok⟩ := hcs_fn rfl
        refine deduce_phase2_step_wp Γ hPromote hSubBin hSubCl hspN hpres hq_ok hlm1_len hlm1_dom
          hws2_len himp_ok hcr_ref_c hconfl_c hqi_lt hclo ho_ok hsd_ok hmc ?_ ?_
        · intro ar_n mclr_n qlen_n qi_n mrk_n ws1_n asz_n rsz_n mn _ hs_nN hpres_n hqn_ok
            hsub_n hasz_ne hwsub hmn
          exact hJ30 (qlen_n, qi_n, olen_c, taut_c, ()) mn
            ⟨ar_n, mclr_n, mrk_n, ws1_n, ws2_c, asz_n, rsz_n, hs_nN, hpres_n, hqn_ok,
              hws2_len, hsub_n, hout_bd_c, fun _ => hwsub, fun h _ => absurd h hasz_ne, hmn⟩
        · intro ar_n mclr_n qlen_n mrk_n ws1_n ws2_n olen_n taut_n rsz_n mn _ hs_nN hpres_n
            hq_cn hqn_le hqi1_le heq_step hws2_n hqn_ok ho_n hclo_n hsd_n hmn
          have hqi1 : (qi_c + 1#64).toNat = qi_c.toNat + 1 := by
            have := hq_ok.2.2.1; bv_omega
          have hlt_meas : s.core.cur_vars - (qi_c + 1#64).toNat < s.core.cur_vars - qi_c.toNat := by
            omega
          have heq_n : ∀ j < qlen_i.toNat, ws1_n[j]? = ws1_i[j]? := fun j hj =>
            (heq_step j (by omega)).trans (heq_init j hj)
          have hsub_n : S13SubRefOk
              { s with core := { s.core with arena := ar_n, min_clr := mclr_n } } (-1#64) :=
            ⟨Or.inl rfl, fun h _ => absurd rfl h⟩
          exact hrec (qlen_n, qi_c + 1#64, olen_n, taut_n, ()) mn hlt_meas
            ⟨ar_n, mclr_n, mrk_n, ws1_n, ws2_n, -1#64, rsz_n, hs_nN, hpres_n, by omega, hqn_le,
              hqi1_le, heq_n, hws2_n, hqn_ok, hsub_n, fun h => absurd rfl h, ho_n,
              fun _ => ⟨hclo_n, hsd_n⟩, hmn⟩
      · have hasz_ne : asz_c ≠ 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
        rw [wp_jump]
        exact hJ30 (qlen_c, qi_c, olen_c, taut_c, ()) mc
          ⟨ar_c, mclr_c, mrk_c, ws1_c, ws2_c, asz_c, rsz_c, hspN, hpres, hq_ok, hws2_len,
            hsub_c, hout_bd_c, hsub_w, fun h _ => absurd h hasz_ne, hmc⟩
    · have hqi_ge : ¬ (qi_c < qlen_c) := by c0_bound
      have hqi_eq : qi_c.toNat = qlen_c.toNat := by
        have : ¬ (qi_c.toNat < qlen_c.toNat) := fun h => hqi_ge (BitVec.lt_def.mpr h)
        omega
      rw [wp_jump]
      exact hJ30 (qlen_c, qi_c, olen_c, taut_c, ()) mc
        ⟨ar_c, mclr_c, mrk_c, ws1_c, ws2_c, asz_c, rsz_c, hspN, hpres, hq_ok, hws2_len,
          hsub_c, hout_bd_c, hsub_w, fun hasz ht => by
            subst ht
            obtain ⟨hclo, hsd⟩ := hcs_fn hasz
            exact ⟨hqc_le, by rw [← hqi_eq]; exact ho_ok, by rwa [hqi_eq] at hclo,
              hsd, hcov_c⟩,
          hmc⟩

private theorem deduce_phase1_wp (Γ : Env)
    (hPromote : Γ.Has "full_viv_recompute_promote_fid" vivRecomputePromoteSpec)
    (hSubBin : Γ.Has "full_viv_subsumes_bin_m6" fullVivSubsumesBinM6Spec)
    (hSubCl : Γ.Has "full_viv_subsumes_cl_m6" fullVivSubsumesClM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {lm1 : List (BitVec 8)} {cref sz implied : Val i32}
    {m0 : Mem 64} {Q : Post [i32]} {X : XPost}
    (hspW : FullSparseInvW c F0 F_cur s) (hcr_ref : cref.toNat ∈ fullArenaClauseRefs s)
    (hcr_ng : fullArenaClauseGarb s cref.toNat = false) (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (himp_ok : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    (hconfl : implied = 0xFFFFFFFF#32 → FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hm0 : (FullMem c { s with
      core := { s.core with lit_mark := lm1 }
      scratch := { s.scratch with ant_sz := -1#64, res_sz := 0#64 } } ⋆ R) m0)
    (hQ : DeducePost c F0 F_cur s R sz Q) :
    let h := c.hdr; let pMark := c.pMark; let pLitMark := c.pLitMark; let pLevel := c.pLevel
    let pTmp := c.pTmp; let pArena := c.pArena; let pRsns := c.pReason; let pWs1 := c.pWorkStk1
    let pWs2 := c.pWorkStk2; let pVars := BitVec.ofNat 64 s.core.cur_vars
    wp Γ Q X
      (Expr.group (sig := [[i64, i32]]) (fun _ => Blocks.cons (fun p28 =>
        deducePhase2BodyExpr h pMark pLitMark pTmp pLevel pArena pRsns pWs1 pWs2 pVars
          cref sz implied (Arg.var p28.fst) (Arg.var p28.snd.fst)) Blocks.nil) fun J27 =>
       fvOp (OpCode.cmp .ne i32 .bool (by decide))
         (Arg.var implied, Arg.imm 4294967295, ()) fun p28 =>
       Expr.jnz (Arg.var p28.fst)
         (fvOp (OpCode.lshr i32) (Arg.var implied, Arg.imm 1, ()) fun p29 =>
          Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p31 =>
            fvOp (OpCode.zext 32 64) (Arg.imm (t := i32) 0, ()) fun p32 =>
            fvOp (OpCode.mul i64) (Arg.var p32.fst, Arg.imm 4, ()) fun p33 =>
            fvOp (OpCode.add i64) (Arg.var pWs2, Arg.var p33.fst, ()) fun p34 =>
            Expr.store (Arg.var implied) (Arg.var p34.fst)
              (fvOp (OpCode.add i32) (Arg.imm (t := i32) 0, Arg.imm 1, ()) fun p35 =>
               Expr.jump J27.fst (Arg.var p31.fst, Arg.var p35.fst, ()))) Blocks.nil) fun J30 =>
          fvOp (OpCode.zext 32 64) (Arg.var p29.fst, ()) fun p31 =>
          fvOp (OpCode.cmp .ult i64 .bool (by decide))
            (Arg.var p31.fst, Arg.var pVars, ()) fun p32 =>
          Expr.jnz (Arg.var p32.fst)
            (fvOp (OpCode.zext 32 64) (Arg.var p29.fst, ()) fun p33 =>
             fvOp (OpCode.mul i64) (Arg.var p33.fst, Arg.imm 4, ()) fun p34 =>
             fvOp (OpCode.add i64) (Arg.var pLevel, Arg.var p34.fst, ()) fun p35 =>
             Expr.load i32 (Arg.var p35.fst) fun ld36 =>
             fvOp (OpCode.cmp .ugt i32 .bool (by decide))
               (Arg.var ld36, Arg.imm 0, ()) fun p37 =>
             Expr.jnz (Arg.var p37.fst)
               (fvOp (OpCode.zext 32 64) (Arg.var p29.fst, ()) fun p38 =>
                fvOp (OpCode.add i64) (Arg.var pMark, Arg.var p38.fst, ()) fun p39 =>
                fvOp (OpCode.trunc 32 8) (Arg.imm (t := i32) 1, ()) fun p40 =>
                Expr.store (Arg.var p40.fst) (Arg.var p39.fst)
                  (fvOp (OpCode.mul i64) (Arg.imm (t := i64) 0, Arg.imm 4, ()) fun p41 =>
                   fvOp (OpCode.add i64) (Arg.var pWs1, Arg.var p41.fst, ()) fun p42 =>
                   Expr.store (Arg.var p29.fst) (Arg.var p42.fst)
                     (fvOp (OpCode.add i64) (Arg.imm (t := i64) 0, Arg.imm 1, ()) fun p43 =>
                      Expr.jump J30.fst (Arg.var p43.fst, ()))))
               (Expr.jump J30.fst (Arg.imm 0, ())))
            (Expr.jump J30.fst (Arg.imm 0, ())))
         (Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p30 =>
            Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p32 =>
              Expr.jump J27.fst (Arg.var p32.fst, Arg.imm 0, ())) Blocks.nil) fun J31 =>
            fvOp (OpCode.add i64) (Arg.var h, Arg.imm 528, ()) fun p32 =>
            Expr.load i64 (Arg.var p32.fst) fun ld33 =>
            fvOp (OpCode.cmp .eq i64 .bool (by decide)) (Arg.var ld33, Arg.imm 1, ()) fun p34 =>
            Expr.jnz (Arg.var p34.fst)
              (s13DeducePhase1bBinExpr h pVars pMark pLevel pWs1 J31.fst)
              (s13DeducePhase1bLargeExpr h pVars pMark pLevel pArena pWs1 cref sz p30.fst J31.fst))
            Blocks.nil) fun J29 =>
          fvOp (OpCode.add i64) (Arg.var h, Arg.imm 528, ()) fun p30 =>
          Expr.load i64 (Arg.var p30.fst) fun ld31 =>
          fvOp (OpCode.cmp .eq i64 .bool (by decide)) (Arg.var ld31, Arg.imm 2, ()) fun p32 =>
          Expr.jnz (Arg.var p32.fst)
            (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 176, ()) fun p33 =>
             Expr.load i64 (Arg.var p33.fst) fun ld34 =>
             fvOp (OpCode.trunc 64 32) (Arg.var ld34, ()) fun p35 =>
             Expr.jump J29.fst (Arg.var p35.fst, ()))
            (Expr.jump J29.fst (Arg.var cref, ())))) m0 := by
  have hcl := hspW.1.core_ok; have hscl := hspW.1.scratch_ok
  have hw := hspW.2.1; have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hspN0 := s13_noMark_of_sparseW hspW
  have hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0 := by
    refine ⟨hcl.mrk_len, hscl.work_stk1_len, Nat.zero_le _,
      fun i hi => absurd hi (Nat.not_lt_zero _), by simp,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun v hv => ?_, fun v hv => ?_,
      fun v _ hv => hspW.2.2.1.1 v hv⟩
    · simp [hspW.2.2.1.1 v (by omega)]
    · exact Or.inl (hspW.2.2.1.1 v (by omega))
  dsimp only [fvOp]
  refine wp_join_group (ts := [i64, i32])
    (fun (qlen_i, olen_i, ()) mi =>
      ∃ (ar_i : List (BitVec 32)) (mclr_i : List (BitVec 32)) (mrk_i : List (BitVec 8))
        (ws1_i : List (BitVec 32)) (ws2_i : List (BitVec 32)) (asz_i : BitVec 64)
        (rsz_i : BitVec 64),
      let si : FullState := { s with core := { s.core with arena := ar_i, min_clr := mclr_i } }
      S13ArPres s si ∧ S13SparseInvNoMark c F0 F_cur si ∧
      VivQueueOk c si mrk_i ws1_i qlen_i.toNat ∧ ws2_i.length = 2 * c.max_vars ∧
      (implied ≠ 0xFFFFFFFF#32 →
        (si.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
          implied.toNat / 2 ∈ ((ws1_i.take qlen_i.toNat).map BitVec.toNat)) ∧
      (cref.toNat ∈ fullArenaClauseRefs si) ∧
      (fullArenaClauseGarb si cref.toNat = false) ∧
      (implied = 0xFFFFFFFF#32 → FullVivConflictOk F_cur si ∨
        (s.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits si cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
      VivOutOk si implied ws1_i ws2_i 0 olen_i.toNat false ∧
      S13SubRefOk si asz_i ∧
      (asz_i ≠ -1#64 → VivDeduceSubWitness F_cur s sz.toNat) ∧
      (asz_i = -1#64 → VivSeedOk si cref implied ws1_i ws2_i qlen_i.toNat olen_i.toNat false) ∧
      (FullMem c { si with
        core := { si.core with mrk := mrk_i, lit_mark := lm1 }
        scratch := { si.scratch with
          work_stk1 := ws1_i, work_stk2 := ws2_i, ant_sz := asz_i, res_sz := rsz_i } } ⋆ R) mi)
    (fun _ (qlen_i, olen_i, ()) mi ⟨ar_i, mclr_i, mrk_i, ws1_i, ws2_i, asz_i, rsz_i, hpres_i,
        hspN_i, hq_i, hws2_i, himp_cov, hcr_ri, hcr_gi, hcon_i, ho_i, hsub_i, hsub_wi, hsd_i,
        hmi⟩ => by
      rw [Blocks.get_here]; dsimp only
      exact deduce_phase2_wp Γ hPromote hSubBin hSubCl hspW hpres_i hspN_i hsz_le htmp_lt hq_i
        hlm1_len hlm1_dom hws2_i himp_ok himp_cov hcr_ri hcr_gi hcon_i ho_i hsub_i hsub_wi
        hsd_i hmi hQ)
    (fun _ hJ27 => ?_)
  viv_hsteps_nogrp
  · have himp_ne : implied ≠ 0xFFFFFFFF#32 := by c0_bound
    obtain ⟨himp_lt, himp_val⟩ := himp_ok himp_ne
    have hv_div : (implied >>> 1#32).toNat = implied.toNat / 2 := bv32_lshr1_toNat _
    have hv_cv : (implied >>> 1#32).toNat < s.core.cur_vars := by rw [hv_div]; omega
    refine wp_join_group (ts := [i64])
      (fun (qlen_i, ()) mj => ∃ (mrk_i : List (BitVec 8)) (ws1_i : List (BitVec 32)),
        VivQueueOk c s mrk_i ws1_i qlen_i.toNat ∧
        ((s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
          implied.toNat / 2 ∈ ((ws1_i.take qlen_i.toNat).map BitVec.toNat)) ∧
        (FullMem c { s with
          core := { s.core with mrk := mrk_i, lit_mark := lm1 }
          scratch := { s.scratch with
            work_stk1 := ws1_i, ant_sz := -1#64, res_sz := 0#64 } } ⋆ R) mj)
      (fun _ (qlen_i, ()) mj ⟨mrk_i, ws1_i, hq_i, hcov_i, hmj⟩ => by
        rw [Blocks.get_here]; dsimp only
        have hws2_pos : 0 < s.scratch.work_stk2.length := by rw [hscl.work_stk2_len]; omega
        viv_hsteps_nogrp
        let ws2_0 := s.scratch.work_stk2.set 0 implied
        have hws2_len : ws2_0.length = 2 * c.max_vars := by simp [ws2_0, hscl.work_stk2_len]
        have hws2_get0 : ws2_0[0]? = some implied := by
          dsimp only [ws2_0]; exact List.getElem?_set_self hws2_pos
        have hws2_0_take : (((ws2_0.take 1).map BitVec.toNat).map (· / 2)).Nodup := by
          rcases List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hws2_pos) with ⟨x, xs, hxs⟩
          simp [ws2_0, hxs]
        have ho_0 : VivOutOk s implied ws1_i ws2_0 0 1 false := by
          intro _
          refine ⟨by omega, fun i hi => ?_, hws2_0_take,
            fun i hi => ?_, fun _ => ⟨Nat.zero_lt_one, hws2_get0⟩,
            fun j hj => absurd hj (Nat.not_lt_zero _)⟩
          · have hi0 : i = 0 := by omega
            subst hi0; simp [hws2_get0]; exact himp_lt
          · have hi0 : i = 0 := by omega
            subst hi0; exact Or.inl ⟨himp_ne, rfl, by simp [hws2_get0]⟩
        have hsd_0 : VivSeedOk s cref implied ws1_i ws2_0 qlen_i.toNat 1 false := by
          intro _; rw [ite_eq_left himp_ne]
          exact List.mem_map.mpr ⟨implied,
            List.mem_iff_getElem?.mpr ⟨0, by rw [List.getElem?_take_of_lt Nat.zero_lt_one,
              hws2_get0]⟩, rfl⟩
        exact hJ27 (qlen_i, 1#32, ()) _ ⟨s.core.arena, s.core.min_clr, mrk_i, ws1_i, ws2_0,
          -1#64, 0#64, s13ArPres_refl _, hspN0, hq_i, hws2_len, fun _ => hcov_i, hcr_ref, hcr_ng,
          fun h => absurd h himp_ne, ho_0, ⟨Or.inl rfl, fun h _ => absurd rfl h⟩,
          fun h => absurd rfl h, fun _ => hsd_0, by
            have hz : (BitVec.setWidth 64 0#32).toNat = 0 := rfl
            dsimp only [ws2_0]; rw [← hz]; assumption⟩)
      (fun _ hJ30 => ?_)
    have himp_lvl : (BitVec.setWidth 64 (implied >>> 1#32)).toNat < s.core.lvl.length := by
      rw [bv32_setWidth64_toNat, hcl.lvl_len]; omega
    have himp_mrk : (BitVec.setWidth 64 (implied >>> 1#32)).toNat < s.core.mrk.length := by
      rw [bv32_setWidth64_toNat, hcl.mrk_len]; omega
    have himp_ws1 : 0 < s.scratch.work_stk1.length := by rw [hscl.work_stk1_len]; omega
    viv_hsteps_nogrp
    · have hpos : 0 < (s.core.lvl[(implied >>> 1#32).toNat]?.getD 0#32).toNat := by
        have hlt : 0#32 < s.core.lvl[((implied >>> 1#32).setWidth 64).toNat]'himp_lvl := by
          c0_bound
        have hget : s.core.lvl[(implied >>> 1#32).toNat]?.getD 0#32 =
            s.core.lvl[((implied >>> 1#32).setWidth 64).toNat]'himp_lvl := by
          rw [← bv32_setWidth64_toNat (implied >>> 1#32), List.getElem?_eq_getElem himp_lvl,
            Option.getD_some]
        rw [hget]; exact BitVec.lt_def.mp hlt
      have hmrk0 : s.core.mrk[(implied >>> 1#32).toNat]?.getD 0#8 = 0#8 :=
        hspW.2.2.1.1 _ (by omega)
      obtain ⟨idx_i, hidx_i, htrl_i⟩ := (hw.vals_true_iff implied.toNat himp_lt).mp himp_val
      have hstep :=
        push_queue_step hq0 hcv_le hv_cv hpos hmrk0 ⟨idx_i, hidx_i, by rw [htrl_i, hv_div]⟩
      have hmem_i : implied.toNat / 2 ∈
          ((s.scratch.work_stk1.set 0 (implied >>> 1#32)).take 1).map BitVec.toNat :=
        List.mem_map.mpr ⟨implied >>> 1#32, List.mem_iff_getElem?.mpr ⟨0, by
          rw [List.getElem?_take_of_lt Nat.zero_lt_one, List.getElem?_set_self himp_ws1]⟩,
          hv_div⟩
      refine hJ30 (1#64, ()) _ ⟨_, _, hstep.2.1, Or.inr hmem_i, by
        simpa only [bv32_setWidth64_toNat] using ‹_›⟩
    · have hlvl0 : (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 := by
        have hle : ¬ (0#32 < s.core.lvl[((implied >>> 1#32).setWidth 64).toNat]'himp_lvl) := by
          c0_bound
        have hget : s.core.lvl[implied.toNat / 2]?.getD 0#32 =
            s.core.lvl[((implied >>> 1#32).setWidth 64).toNat]'himp_lvl := by
          rw [← hv_div, ← bv32_setWidth64_toNat (implied >>> 1#32),
            List.getElem?_eq_getElem himp_lvl, Option.getD_some]
        rw [hget]
        have : (s.core.lvl[((implied >>> 1#32).setWidth 64).toNat]'himp_lvl).toNat ≤ 0 :=
          Nat.le_of_not_lt fun h => hle (BitVec.lt_def.mpr h)
        omega
      exact hJ30 (0#64, ()) _ ⟨s.core.mrk, s.scratch.work_stk1, hq0, Or.inl hlvl0, by assumption⟩
  · have himp_eq : implied = 0xFFFFFFFF#32 := by c0_bound
    refine wp_join_group (ts := [i32])
      (fun (src_cr, ()) mj =>
        src_cr.toNat =
          (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat) ∧
        src_cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s src_cr.toNat = false ∧
        (FullMem c { s with
          core := { s.core with lit_mark := lm1 }
          scratch := { s.scratch with ant_sz := -1#64, res_sz := 0#64 } } ⋆ R) mj)
      (fun _ (src_cr, ()) mj ⟨hsrc_eq, hsrc_ref, hsrc_ng, hmj⟩ => by
        rw [Blocks.get_here]; dsimp only
        refine wp_join_group (ts := [i64])
          (fun (qlen_v, ()) mk =>
            ∃ (ar_i : List (BitVec 32)) (mclr_i : List (BitVec 32)) (mrk1 : List (BitVec 8))
              (ws1_1 : List (BitVec 32)) (asz1 : BitVec 64) (rsz1 : BitVec 64),
            let si : FullState :=
              { s with core := { s.core with arena := ar_i, min_clr := mclr_i } }
            S13ArPres s si ∧ S13SparseInvNoMark c F0 F_cur si ∧
            qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c si mrk1 ws1_1 qlen_v.toNat ∧
            S13SubRefOk si asz1 ∧
            (asz1 ≠ -1#64 → VivDeduceSubWitness F_cur s sz.toNat) ∧
            (asz1 = -1#64 →
              VivSeedOk si cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false) ∧
            (FullMem c { si with
              core := { si.core with mrk := mrk1, lit_mark := lm1 }
              scratch := { si.scratch with
                work_stk1 := ws1_1, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) mk)
          (fun _ (qlen_v, ()) mk ⟨ar_i, mclr_i, mrk1, ws1_1, asz1, rsz1, hpres_i, hspN_i,
              _, hq_i, hsub_i, hsub_wi, hsd_i, hmk⟩ => by
            rw [Blocks.get_here]; dsimp only
            let si : FullState :=
              { s with core := { s.core with arena := ar_i, min_clr := mclr_i } }
            have hcr_ri : cref.toNat ∈ fullArenaClauseRefs si := by
              rw [hpres_i.1]; exact hcr_ref
            have hcr_gi : fullArenaClauseGarb si cref.toNat = false := by
              rw [(hpres_i.2 cref.toNat hcr_ref).1]; exact hcr_ng
            have ho_0 : VivOutOk si implied ws1_1 s.scratch.work_stk2 0 0 false := by
              intro _; refine ⟨Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _), by simp,
                fun i hi => absurd hi (Nat.not_lt_zero _), fun h => absurd himp_eq h,
                fun j hj => absurd hj (Nat.not_lt_zero _)⟩
            have hcon_i := s13_confl_ar_pres (s13ArPres_refl s) hpres_i rfl rfl rfl rfl rfl rfl
              hcr_ref hconfl
            exact hJ27 (qlen_v, 0#32, ()) mk ⟨ar_i, mclr_i, mrk1, ws1_1, s.scratch.work_stk2,
              asz1, rsz1, hpres_i, hspN_i, hq_i, hscl.work_stk2_len, fun h => absurd himp_eq h,
              hcr_ri, hcr_gi, hcon_i, ho_0, hsub_i, hsub_wi, hsd_i, hmk⟩)
          (fun _ hJ31 => ?_)
        viv_hsteps_nogrp
        · have hct1 : s.core.confl_type = 1#64 := by c0_bound
          refine s13_deduce_phase1b_bin_wp Γ hSubBin hspW hlm1_len hlm1_dom himp_eq hct1 hconfl
            hq0 hmj ?_
          intro qlen_v mrk1 ws1_1 asz1 rsz1 mq hq_le hq1 hsd1 hsub1 hwsub1 hmq
          exact hJ31 (qlen_v, ()) mq ⟨s.core.arena, s.core.min_clr, mrk1, ws1_1, asz1, rsz1,
            s13ArPres_refl _, hspN0, hq_le, hq1, hsub1, hwsub1, hsd1, hmq⟩
        · have hct_ne1 : s.core.confl_type ≠ 1#64 := by c0_bound
          refine s13_deduce_phase1b_large_wp Γ hPromote hSubCl hspW hlm1_len hlm1_dom himp_eq
            hct_ne1 hconfl hsrc_eq hsrc_ref hsrc_ng hcr_ref hq0 hmj ?_
          intro ar' mclr' qlen_v mrk1 ws1_1 asz1 rsz1 mq _ hsp_nN hpres_n hq_le hq1 hsd1 hsub1
            hwsub1 hmq
          have hwsub_s := fun h => vivDeduceSubWitness_of_pres rfl rfl rfl rfl rfl (hwsub1 h)
          exact hJ31 (qlen_v, ()) mq ⟨ar', mclr', mrk1, ws1_1, asz1, rsz1, hpres_n, hsp_nN, hq_le,
            hq1, hsub1, hwsub_s, hsd1, hmq⟩)
      (fun _ hJ29 => ?_)
    viv_hsteps_nogrp
    · have hct2 : s.core.confl_type = 2#64 := by c0_bound
      rcases hconfl himp_eq with hcw | ⟨hct0, _⟩
      · rcases hcw with hbin | ⟨_, href_c, hng_c, _⟩
        · exfalso; have : s.core.confl_type = 1#64 := hbin.1; rw [hct2] at this; cases this
        · have hcr64_tr : (s.core.confl_ref.truncate 32).toNat = s.core.confl_ref.toNat := by
            have hca := c.harena; unfold dimacsBound at hca
            have := (hw.arena.refs_wf _ href_c).1; have := hcl.arena_len_le
            simp only [BitVec.truncate, BitVec.toNat_setWidth]; omega
          exact hJ29 (s.core.confl_ref.truncate 32, ()) _ ⟨by simp [hct2, hcr64_tr],
            by rw [hcr64_tr]; exact href_c, by rw [hcr64_tr]; exact hng_c, by assumption⟩
      · exfalso; rw [hct0] at hct2; cases hct2
    · have hct_ne2 : s.core.confl_type ≠ 2#64 := by c0_bound
      exact hJ29 (cref, ()) _ ⟨by simp [hct_ne2], hcr_ref, hcr_ng, by assumption⟩

/-- Certification of `full_viv_deduce_m6` against `Spec.vivDeduceM6Spec`. -/
theorem full_viv_deduce_m6_wp (Γ : Env)
    (hPromote : Γ.Has "full_viv_recompute_promote_fid" vivRecomputePromoteSpec)
    (hSubBin : Γ.Has "full_viv_subsumes_bin_m6" fullVivSubsumesBinM6Spec)
    (hSubCl : Γ.Has "full_viv_subsumes_cl_m6" fullVivSubsumesClM6Spec) :
    ∀ a m Q X, vivDeduceM6Spec a m Q X →
      Func.wp Γ full_viv_deduce_m6_body a m Q X := by
  rintro ⟨h, cref, sz, implied, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hspW, hcr_ref, hcr_ng, hsz_le, htmp_lt, hconfl, himp_ok, hm, hQ⟩
  have hcl := hspW.1.core_ok; have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_viv_deduce_m6_body
  viv_hsteps_nogrp
  let loopInv : Val i32 × PUnit → Mem 64 → Prop := fun (k, ()) mk => ∃ lm : List (BitVec 8),
    k.toNat ≤ sz.toNat ∧ lm.length = 2 * c.max_vars ∧
    (∀ l < 2 * c.max_vars, lm[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < k.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
    (FullMem c { s with core := { s.core with lit_mark := lm } } ⋆ R) mk
  refine wp_loop_inv loopInv (fun (k, ()) _ => sz.toNat - k.toNat)
    (fun Js hJs => by
      rw [wp_jump]
      refine hJs (0#32, ()) m ⟨s.core.lit_mark, Nat.zero_le _, hcl.lit_mark_len,
        fun l hl hne => absurd (hspW.2.2.1.2 l hl) hne, hm⟩)
    (fun Js (k, ()) mk ⟨lm, hk_le, hlm_len, hlm_dom, hmk⟩ hrec => ?_)
  rw [Blocks.get_here]; dsimp only [fvOp]
  viv_hsteps_nogrp
  · have hk_lt : k.toNat < sz.toNat := by c0_bound
    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
    have hlt_k := htmp_lt k.toNat hk_lt
    have hk_lt_tmp : k.toNat < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
    have hk_tmp : (k.setWidth 64).toNat < s.core.tmp.length := by
      rw [bv32_setWidth64_toNat, hcl.tmp_len_arr]; omega
    let lt_k := s.core.tmp[k.toNat]?.getD 0#32
    have hlt_eq : s.core.tmp[(k.setWidth 64).toNat]'hk_tmp = lt_k := Option.some.inj (by
      dsimp only [lt_k]
      rw [← List.getElem?_eq_getElem hk_tmp, bv32_setWidth64_toNat,
        List.getElem?_eq_getElem hk_lt_tmp, Option.getD_some])
    have hlit_lm : ((s.core.tmp[(k.setWidth 64).toNat]'hk_tmp).setWidth 64).toNat < lm.length := by
      rw [bv32_setWidth64_toNat, hlt_eq, hlm_len]; dsimp only [lt_k]; have := hcl.cur_vars_le; omega
    viv_hsteps_nogrp
    let lm' := lm.set lt_k.toNat 1#8
    have hlm'_dom : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 ≠ 0#8 →
        ∃ t < (k + 1#32).toNat, (s.core.tmp[t]?.getD 0#32).toNat = l := by
      intro l hl hne
      by_cases hll : l = lt_k.toNat
      · exact ⟨k.toNat, by rw [hk1]; omega, hll.symm⟩
      · have hne' : lm[l]?.getD 0#8 ≠ 0#8 := by
          dsimp only [lm'] at hne; rwa [List.getElem?_set_ne (Ne.symm hll)] at hne
        obtain ⟨t, ht, hteq⟩ := hlm_dom l hl hne'
        exact ⟨t, by rw [hk1]; omega, hteq⟩
    exact hrec (k + 1#32, ()) _ (by dsimp only; rw [hk1]; omega)
      ⟨lm', by rw [hk1]; omega, by simp [lm', hlm_len], hlm'_dom,
        by simpa only [lm', ← hlt_eq, bv32_setWidth64_toNat] using ‹(FullMem _ _ ⋆ R) _›⟩
  · have hk_ge : ¬ (k.toNat < sz.toNat) := by
      intro h; have : k < sz := BitVec.lt_def.mpr h; c0_bound
    have hk_eq : k.toNat = sz.toNat := by omega
    rw [hk_eq] at hlm_dom
    viv_hsteps_nogrp
    refine deduce_phase1_wp Γ hPromote hSubBin hSubCl hspW hcr_ref hcr_ng hsz_le htmp_lt
      hlm_len hlm_dom himp_ok hconfl (by assumption) fun olen ar' mclr' mrk' lm' ws1' ws2'
      asz' rsz' m' hs' hsub' href_n hrefs_eq hcl_eq hent' hwsub' hm' =>
      hQ olen ar' mclr' mrk' lm' ws1' ws2' asz' rsz' m' hs' hsub' href_n hrefs_eq hcl_eq
        hent' hwsub' hm'

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
