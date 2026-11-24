module

public import LeanQbe.T.Examples.Kissat.FullM8FidV12
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof2a
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M6.0` Orchestrator Adapter Proofs — Part 2 (`full_ana_failed_lit_m6_hdr`)

Proves `m8_ana_failed_lit_m6_hdr_wp` certifying `m6aAnaFailedLitSpec` over `FullM6HdrMem`,
calling `m6aBumpAnalyzedSpec` (`"full_bump_analyzed_m6_hdr"`), `full_clear_ana`,
`full_backtrack`, and `full_assign_lvl`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8FidV12

open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

section Helpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem p2_bv32_lshr1_loc (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem p2_bv32_xor1_loc (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 :=
  fl_bv32_xor1 x

private theorem p2_bv32_setWidth64_loc (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  fl_bv32_setWidth64 x

private theorem p2_sext32_64_1 : BitVec.signExtend 64 (1#32 : BitVec 32) = 1#64 := rfl

private theorem p2_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem p2_bv32_0_add (x : BitVec 32) : 0#32 + x = x := by simp

attribute [local bv_c0] p2_bv32_lshr1_loc p2_bv32_xor1_loc p2_bv32_setWidth64_loc
  p2_sext32_64_1 p2_bv32_lshr_nat1 p2_bv32_0_add

end Helpers

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "c0_hcall " h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev m8PostLoopHdrBlock (c : FullCfg) (cv : BitVec 64) (nf : BitVec 32) :
    Blocks Val Cont [i64] [[i64, i64, .bool, i64, i32, .bool]] :=
  Blocks.cons (fun (p : Tup Val [i64, i64, .bool, i64, i32, .bool]) =>
    Expr.jnz (Arg.var p.snd.snd.snd.snd.snd.fst)
      (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
        Expr.ret (Arg.imm 0, ()))
      (Expr.let_ (Op.mk (.cmp .uge i64 .bool rfl) (Arg.var p.snd.fst, Arg.var cv, ()))
        fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
            Expr.ret (Arg.imm 0, ()))
          (Expr.let_ (Op.mk (.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ())) fun p_2 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.pTmp, Arg.var p_2.fst, ())) fun p_3 =>
            Expr.store (t := i32) (Arg.var nf) (Arg.var p_3.fst) (
            Expr.let_ (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 192, ())) fun p_4 =>
            Expr.store (t := i64) (Arg.var p.fst) (Arg.var p_4.fst) (
            Expr.call (as := [i64]) (bs := []) "full_bump_analyzed_m6_hdr"
              (Arg.var c.hdr, ()) fun _ =>
            Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
            Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
              (Arg.var c.hdr, Arg.imm 0, ()) fun _ =>
            @Expr.group Val Cont [i64] [[i64]] (fun Js_lp =>
              Blocks.cons (fun (p_8 : Tup Val [i64]) =>
                Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                    (Arg.var p_8.fst, Arg.var p.fst, ())) fun p_c =>
                Expr.jnz (Arg.var p_c.fst)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var p_8.fst, Arg.imm 4, ())) fun p_m =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pTmp, Arg.var p_m.fst, ())) fun p_a =>
                  Expr.load i32 (Arg.var p_a.fst) fun ld =>
                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_z =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pVals, Arg.var p_z.fst, ())) fun p_v =>
                  Expr.load i8 (Arg.var p_v.fst) fun ld_1 =>
                  Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_t0 =>
                  Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_1, ())) fun p_9 =>
                  Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_t0.fst, ())) fun p_z0 =>
                  Expr.let_ (Op.mk (.cmp .slt i32 .bool rfl)
                      (Arg.var p_9.fst, Arg.var p_z0.fst, ())) fun p_s =>
                  Expr.jnz (Arg.var p_s.fst)
                    (Expr.ret (Arg.imm 20, ()))
                    (@Expr.group Val Cont [i64] [[]] (fun _ =>
                      Blocks.cons (fun _ =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var p_8.fst, Arg.imm 1, ()))
                          fun p_k1 =>
                        Expr.jump Js_lp.fst (Arg.var p_k1.fst, ()))
                      Blocks.nil) fun Js_nxt =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_z2 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pVals, Arg.var p_z2.fst, ())) fun p_v2 =>
                    Expr.load i8 (Arg.var p_v2.fst) fun ld_2 =>
                    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_t1 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_2, ())) fun p_10 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_t1.fst, ())) fun p_z1 =>
                    Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                        (Arg.var p_10.fst, Arg.var p_z1.fst, ())) fun p_eq =>
                    Expr.jnz (Arg.var p_eq.fst)
                      (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
                        (Arg.var c.hdr, Arg.var ld, Arg.imm 0xFFFFFFFF, Arg.imm 0, ())
                        fun _ => Expr.jump Js_nxt.fst ())
                      (Expr.jump Js_nxt.fst ())))
                  (@Expr.group Val Cont [i64] [[]] (fun _ =>
                    Blocks.cons (fun _ =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_c1 =>
                      Expr.load i64 (Arg.var p_c1.fst) fun ld =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.imm 1, ())) fun p_c2 =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_9 =>
                      Expr.store (t := i64) (Arg.var p_c2.fst) (Arg.var p_9.fst) (
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 344, ())) fun p_l1 =>
                      Expr.load i64 (Arg.var p_l1.fst) fun ld_1 =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var ld_1, Arg.imm 1, ())) fun p_l2 =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 344, ())) fun p_10 =>
                      Expr.store (t := i64) (Arg.var p_l2.fst) (Arg.var p_10.fst) (
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1032, ())) fun p_it =>
                      Expr.store (t := i64) (Arg.imm 1) (Arg.var p_it.fst)
                        (Expr.ret (Arg.imm 1, ())))))
                    Blocks.nil) fun Js_em =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 520, ())) fun p_pr =>
                    Expr.load i64 (Arg.var p_pr.fst) fun ld_pr =>
                    Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                        (Arg.var ld_pr, Arg.imm 0, ())) fun p_peq =>
                    Expr.jnz (Arg.var p_peq.fst)
                      (Expr.call (as := [i64, i64]) (bs := []) "full_ema_update"
                        (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.jump Js_em.fst ())
                      (Expr.jump Js_em.fst ())))
              Blocks.nil) fun Js_lp => Expr.jump Js_lp.fst (Arg.imm 0, ()))))))
    Blocks.nil

private theorem fl_post_loop_hdr_wp {Γ Q X}
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hBumpAna : ∀ a m Q X, m6aBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6_hdr" [i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X → Γ "full_ema_update" [i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {not_failed : BitVec 32}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hcut : FullCutInvW c F0 F_cur cut s) (hcl1 : s.core.cur_level = 1)
    (hnf_lt : not_failed.toNat < 2 * s.core.cur_vars)
    (hnf_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_failed.toNat]))
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    {unres_f ucnt_f : Nat} {done_f : Bool} {t_f : Nat} {unit_f : BitVec 32} {err_f : Bool}
    {s_f : FullState} {m_f : Mem 64}
    (hok_f : FailedStateOk c s s_f cut) (_ht_f_le : t_f ≤ s.core.trail_end)
    (hucnt_le : ucnt_f ≤ s.core.cur_vars)
    (htmp_f : ∀ k < ucnt_f, (s_f.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(s_f.core.tmp[k]?.getD 0#32).toNat]))
    (_hact_f : !err_f → !done_f → unres_f = (flIdxs s.core s_f.core.mrk t_f).length ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits s.core s_f.core.mrk t_f)))
    (hm_f : (FullMem c s_f ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m_f) :
    wp Γ Q X ((m8PostLoopHdrBlock c (BitVec.ofNat 64 s.core.cur_vars) not_failed).get
      Member.here (BitVec.ofNat 64 unres_f, BitVec.ofNat 64 ucnt_f, done_f,
        BitVec.ofNat 64 t_f, unit_f, err_f, ())) m_f := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hcut.1.core_ok.cur_vars_le
  let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext ⋆ R
  dsimp only [m8PostLoopHdrBlock]; rw [Blocks.get_here]; dsimp only
  c0_hsplit
  · c0_hsteps_nogrp; c0_hcall hClear
    refine ⟨c, s_f, R_hdr, rfl, hok_f.len, hm_f, fun mrk' m_c hml' _ _ hcov_c hm_c => ?_⟩
    c0_hsteps
    let s_c : FullState := { s_f with core := { s_f.core with mrk := mrk', min_clr_len := 0 } }
    have hok_c := p2_clear_ok hok_f hml' (hcov_c hok_f.cov)
    exact hQ 0#64 ext s_c m_c hext (fun hi => ⟨hi, rfl⟩) hok_c.len (Or.inl rfl)
      (by rw [hok_c.core]) (by rw [hok_c.core]) (by rw [hok_c.scr])
      (fun h => by cases h) (fun _ => fl_otfsInvW_of_ok hcut hok_c (hcov_c hok_f.cov))
      (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm_c)
  · c0_hsplit
    · c0_hsteps_nogrp; c0_hcall hClear
      refine ⟨c, s_f, R_hdr, rfl, hok_f.len, hm_f, fun mrk' m_c hml' _ _ hcov_c hm_c => ?_⟩
      c0_hsteps
      let s_c : FullState := { s_f with core := { s_f.core with mrk := mrk', min_clr_len := 0 } }
      have hok_c := p2_clear_ok hok_f hml' (hcov_c hok_f.cov)
      exact hQ 0#64 ext s_c m_c hext (fun hi => ⟨hi, rfl⟩) hok_c.len (Or.inl rfl)
        (by rw [hok_c.core]) (by rw [hok_c.core]) (by rw [hok_c.scr])
        (fun h => by cases h) (fun _ => fl_otfsInvW_of_ok hcut hok_c (hcov_c hok_f.cov))
        (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm_c)
    · have hucnt_lt : ucnt_f < s.core.cur_vars := by
        have hcv64 :
                                                              s.core.cur_vars < 2 ^ 64 := by omega
        have huc64 : ucnt_f < 2 ^ 64 := by omega
        have hnge : ¬ s.core.cur_vars % 2 ^ 64 ≤ ucnt_f % 2 ^ 64 := by
          simpa only [hok_f.core] using (by assumption : _)
        rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt huc64] at hnge
        exact Nat.lt_of_not_le hnge
      have hucnt_tmp : (BitVec.ofNat 64 ucnt_f).toNat < s_f.core.tmp.length := by
        rw [bv64_ofNat_toNat (by omega), hok_f.len.core_ok.tmp_len_arr]; omega
      have hucnt1_bv : (BitVec.ofNat 64 ucnt_f + 1).toNat = ucnt_f + 1 := by
        rw [show (1 : BitVec 64) = 1#64 from rfl,
          fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
          bv64_ofNat_toNat (by omega)]
      c0_hsteps_nogrp
      let s_t : FullState :=
        { s_f with
          core := { s_f.core with
            tmp := s_f.core.tmp.set ucnt_f not_failed, tmp_len := ucnt_f + 1 } }
      have hok_t0 := fl_failedStateOk_with_tmp hok_f
        (tmp' := s_f.core.tmp.set ucnt_f not_failed)
        (by simp [hok_f.len.core_ok.tmp_len_arr])
      have hok_t : FailedStateOk c s s_t cut :=
        ⟨⟨{ hok_t0.len.core_ok with tmp_len_le := by dsimp [s_t]; omega }, hok_t0.len.scratch_ok⟩,
         (by
           dsimp only [s_t]
           exact congrArg (fun (k : FullCoreState) =>
             { k with tmp := s_f.core.tmp.set ucnt_f not_failed, tmp_len := ucnt_f + 1 })
             hok_f.core),
         hok_t0.scr, hok_t0.cov, hok_t0.mb⟩
      have hm_t : (FullMem c s_t ⋆ R_hdr) m := by
        simpa only [R_hdr, s_t, bv64_ofNat_toNat (by omega : ucnt_f < 2 ^ 64), hucnt1_bv] using hm
      have htmp_t : ∀ k < ucnt_f + 1,
          (s_t.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [(s_t.core.tmp[k]?.getD 0#32).toNat]) :=
        fun k hk => by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · dsimp [s_t]; rw [List.getElem?_set_ne (by omega)]; exact htmp_f k hlt
        · dsimp [s_t]; rw [List.getElem?_set_self (by rw [hok_f.len.core_ok.tmp_len_arr]; omega),
            Option.getD_some]
          exact ⟨hnf_lt, hnf_ent⟩
      try clear hm_f
      m6h_call hBumpAna
      refine m6aBumpAnalyzedSpec_of hcfg hext hok_t.len hok_t.cov ((fullM6HdrMem_iff ..).mpr hm_t)
        fun mrk_b mcl_b sc_b ext' m_b hlen_b hcov_b hpres_b hws2_b hext' hinit' hm_b => ?_
      rw [fullM6HdrMem_iff] at hm_b
      let s_b : FullState :=
        { s_t with core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b }, scratch := sc_b }
      let R' : Mem 64 → Prop := array64 (c.hdr - 2304) ext' ⋆ R
      c0_hsteps_nogrp; c0_hcall hClear
      refine ⟨c, s_b, R', rfl, hlen_b, hm_b, fun mrk_c m_c hml_c _ _ hclr_c hm_c => ?_⟩
      let s_c : FullState := { s_b with core := { s_b.core with mrk := mrk_c, min_clr_len := 0 } }
      obtain ⟨hlen_c, hsc_otfs, hw_c, hcl_c, hcv_c, hfu_c, hdm_c, hws2_c, htmp_c⟩ :=
        p2_post_otfs hcut hcl1 hok_t rfl hlen_b hcov_b hpres_b hws2_b hml_c hclr_c
      clear hm_t hm_b
      c0_hsteps_nogrp; c0_hcall hBacktrack
      refine ⟨c, s_c, R', rfl, hlen_c, by rw [hcl_c]; omega,
        fun h => by
          have := hcv_le; have := hnf_lt
          rw [hcl_c] at h; omega,
        hw_c.trail_lits_lt, hm_c, ?_⟩
      intro vals_bt lvl_bt rsns_bt trl_bt tp_bt te_bt prop_bt cl_bt unass_bt sc_bt
        m_bt _ hbt_len _ _ hbt_cl hbt_pres _ _ _ _ hbt_wo hm_bt
      let s_bt : FullState :=
        { s_c with
          core := { s_c.core with
            vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
            trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
            cur_level := cl_bt, unassigned := unass_bt }
          scratch := sc_bt }
      obtain ⟨hbt_sp, hbt_cl0, hbt_cv, hbt_fu, hbt_dm, hbt_ws2, hbt_tmp⟩ :=
        p2_bt_sp hsc_otfs hcl_c hcv_c hfu_c hdm_c hws2_c hbt_len hbt_cl hbt_pres hbt_wo
      clear hm_c; c0_hsteps_nogrp
      refine wp_while_state (ts := [i64]) (α := Nat × FullState)
        (proj := fun st => (BitVec.ofNat 64 st.1, ()))
        (μ := fun st => (ucnt_f + 1) - st.1)
        (Inv := fun st m1 =>
          st.1 ≤ ucnt_f + 1 ∧ FullSparseInvW c F0 F_cur st.2 ∧ st.2.core.cur_level = 0 ∧
          st.2.core.cur_vars = s.core.cur_vars ∧ st.2.core.fuel = s.core.fuel ∧
          st.2.core.dense_mode = s.core.dense_mode ∧
          st.2.scratch.work_stk2 = s.scratch.work_stk2 ∧ st.2.core.tmp = s_t.core.tmp ∧
          (FullMem c st.2 ⋆ R') m1) ?_ ?_
      · intro Jk hJk; c0_hsteps
        exact hJk (0, s_bt) m_bt
          ⟨Nat.zero_le _, hbt_sp, hbt_cl0, hbt_cv, hbt_fu, hbt_dm, hbt_ws2, hbt_tmp, hm_bt⟩
      · intro Jk ⟨k, s_k⟩ m_k
          ⟨hk_le, hsp_k, hcl_k, hcv_k, hfu_k, hdm_k, hws2_k, htmp_k, hm_k⟩ ih_k
        dsimp only at hk_le hsp_k hcl_k hcv_k hfu_k hdm_k hws2_k htmp_k hm_k ih_k
        rw [Blocks.get_here]; dsimp only
        have hkl_k := hsp_k.1.core_ok
        have hk_lt_bd : ucnt_f + 1 < 2 ^ 64 := by omega
        c0_hsplit
        · have hk_lt : k < ucnt_f + 1 := by
            have hlt : k % 2 ^ 64 < (ucnt_f + 1) % 2 ^ 64 := by
              simpa only [BitVec.toNat_ofNat] using (by assumption : _)
            rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk_lt_bd] at hlt
          have hk_tmp : (BitVec.ofNat 64 k).toNat < s_k.core.tmp.length := by
            rw [bv64_ofNat_toNat (by omega), hkl_k.tmp_len_arr]; omega
          let u := s_k.core.tmp[(BitVec.ofNat 64 k).toNat]'hk_tmp
          have hu_prop := htmp_t k hk_lt
          have hu_eq : u.toNat = (s_t.core.tmp[k]?.getD 0#32).toNat := by
            have hk_t : k < s_t.core.tmp.length := by rw [← htmp_k, hkl_k.tmp_len_arr]; omega
            rw [List.getElem?_eq_getElem hk_t, Option.getD_some]
            exact congrArg BitVec.toNat (p2_getElem_congr_list htmp_k (bv64_ofNat_toNat (by omega)))
          have hu_lt : u.toNat < 2 * s_k.core.cur_vars := by rw [hu_eq, hcv_k]; exact hu_prop.1
          have hu_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat]) := by
            rw [hu_eq]; exact hu_prop.2
          have hu_val_lt : (u.setWidth 64).toNat < s_k.core.vals.length := by
            rw [fl_bv32_setWidth64, hkl_k.vals_len]; have := hkl_k.cur_vars_le; omega
          c0_hsplit
          · have hu_ff : s_k.core.vals[u.toNat]?.getD 0#8 = 0xFF#8 := by
              have hdom := hsp_k.2.1.vals_domain u.toNat hu_lt
              have hidx : u.toNat < s_k.core.vals.length := by
                rw [hkl_k.vals_len]; have := hkl_k.cur_vars_le; omega
              rw [List.getElem?_eq_getElem hidx, Option.getD_some] at hdom ⊢
              exact fl_i8_slt0_neg_iff hdom (by simpa [u] using (by assumption : _))
            obtain ⟨ti, hti_te, hti_eq⟩ := (hsp_k.2.1.vals_false_iff u.toNat hu_lt).mp hu_ff
            have hti_lvl0 :
                (s_k.core.lvl[(s_k.core.trl[ti]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
              have hle := hsp_k.2.1.lvl_le ti hti_te; omega
            have hnu_ent := hsp_k.2.1.level0_sound ti hti_te hti_lvl0
            rw [hti_eq] at hnu_ent
            have hunsat : F0.Unsat :=
              hsp_k.2.1.ext_sound.2 (fl_unsat_of_unit_pair hu_ent hnu_ent)
            c0_hsteps
            exact hQ 20#64 ext' s_k m_k hext' hinit' hsp_k.1 (Or.inr (Or.inr rfl))
              hcv_k hfu_k hws2_k (fun _ => ⟨hunsat, hsp_k.toOtfs, by omega, hdm_k⟩)
              (fun h => by cases h) (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm_k)
          · refine wp_join_state (ts := []) (α := FullState) (proj := fun _ => ())
              (Inv := fun st m1 =>
                FullSparseInvW c F0 F_cur st ∧ st.core.cur_level = 0 ∧
                st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
                st.core.dense_mode = s.core.dense_mode ∧
                st.scratch.work_stk2 = s.scratch.work_stk2 ∧ st.core.tmp = s_t.core.tmp ∧
                (FullMem c st ⋆ R') m1) ?_ ?_
            · intro _ s_n m_n ⟨hsp_n, hcl_n, hcv_n, hfu_n, hdm_n, hws2_n, htmp_n, hm_n⟩
              rw [Blocks.get_here]; c0_hsteps
              rw [p2_bv64_add1_eq (by omega)]
              exact ih_k (k + 1, s_n) m_n (by omega)
                ⟨by omega, hsp_n, hcl_n, hcv_n, hfu_n, hdm_n, hws2_n, htmp_n, hm_n⟩
            · intro Jk1 hJk1
              c0_hsplit
              · have hu_z : s_k.core.vals[u.toNat]?.getD 0#8 = 0#8 := by
                  have hidx : u.toNat < s_k.core.vals.length := by
                    rw [hkl_k.vals_len]; have := hkl_k.cur_vars_le; omega
                  rw [List.getElem?_eq_getElem hidx, Option.getD_some]
                  exact fl_i8_sext32_eq0_iff.mp (by simpa [u] using (by assumption : _))
                have hte_lt : s_k.core.trail_end < c.max_vars := by
                  have := hsp_k.2.1.trail_end_lt_of_unassigned hu_lt hu_z
                  have := hkl_k.cur_vars_le; omega
                have hng : ¬ (s_k.core.cur_vars ≤ u.toNat / 2 ∨ c.max_vars ≤ s_k.core.trail_end ∨
                    s_k.core.vals[u.toNat]?.getD 0#8 ≠ 0#8) := by
                  simp only [hu_z, ne_eq, not_true_eq_false, or_false]; omega
                c0_hsteps_nogrp; c0_hcall hAssignLvl
                refine ⟨c, s_k, R', rfl, hsp_k.1, hm_k, ?_⟩
                rw [ite_eq_right (by simpa only [u, Arg.val_var] using hng)]; dsimp only
                intro flags' unass' phases' m_n hfll' hphl' hm_n
                let s_n : FullState :=
                  { s_k with
                    core := { s_k.core with
                      vals := (s_k.core.vals.set u.toNat 1#8).set (u.toNat ^^^ 1) 0xFF#8
                      flags := flags', lvl := s_k.core.lvl.set (u.toNat / 2) 0#32
                      rsns := s_k.core.rsns.set (u.toNat / 2) 0xFFFFFFFF#32
                      trl := s_k.core.trl.set s_k.core.trail_end u
                      trail_pos := s_k.core.trail_pos.set (u.toNat / 2)
                        (BitVec.ofNat 32 s_k.core.trail_end)
                      trail_end := s_k.core.trail_end + 1, unassigned := unass'
                      unflushed := s_k.core.unflushed + 1#64 }
                    scratch := { s_k.scratch with phases := phases' } }
                have hsp_n := fl_assign0_preserves_sparseW hsp_k hcl_k hu_lt hu_z hu_ent hfll'
                  hphl' (unass' := unass') (unflushed' := s_k.core.unflushed + 1#64)
                c0_hsteps
                refine hJk1 s_n m_n ⟨hsp_n, hcl_k, hcv_k, hfu_k, hdm_k, hws2_k, htmp_k, ?_⟩
                simpa only [s_n, u, Arg.val_var, Arg.val_imm,
                  show (0 : BitVec 32) = 0#32 from rfl,
                  show ((0#32 : BitVec 32) = 0#32) ↔ True by decide, ↓reduceIte,
                  show (BitVec.ofNat 32 0 = 0#32) from rfl,
                  show (4294967295#32 : BitVec 32) = 0xFFFFFFFF#32 from rfl] using hm_n
              · c0_hsteps
                exact hJk1 s_k m_k ⟨hsp_k, hcl_k, hcv_k, hfu_k, hdm_k, hws2_k, htmp_k, hm_k⟩
        · c0_hsteps_nogrp
          refine wp_join_state0 (α := FullState)
            (fun sE mE => sE.LengthsOk c ∧ FullSparseInvW c F0 F_cur sE ∧
              sE.core.cur_level = s_k.core.cur_level ∧ sE.core.cur_vars = s_k.core.cur_vars ∧
              sE.core.fuel = s_k.core.fuel ∧ sE.core.dense_mode = s_k.core.dense_mode ∧
              sE.scratch.work_stk2 = s_k.scratch.work_stk2 ∧ (FullMem c sE ⋆ R') mE) ?_ ?_
          · rintro _ sE mE ⟨hklE, hspE, hclE, hcvE, hfuE, hdmE, hws2E, hmE⟩
            c0_hsteps
            let s_fin : FullState :=
              { sE with scratch := { sE.scratch with
                conflicts := sE.scratch.conflicts + 1#64,
                learned_lits := sE.scratch.learned_lits + 1#64, iterating := 1#64 } }
            have hsp_fin' : FullSparseInvW c F0 F_cur s_fin :=
              ⟨⟨hklE.core_ok, { hklE.scratch_ok with }⟩, hspE.2.1, hspE.2.2.1,
                hspE.2.2.2.1, FullExtScratchOk.of_pres hspE.2.2.2.2.1 ⟨rfl, rfl⟩
                  (fun _ h => h), hspE.2.2.2.2.2⟩
            exact hQ 1#64 ext' s_fin _ hext' hinit' hsp_fin'.1 (Or.inr (Or.inl rfl))
              (hcvE.trans hcv_k) (hfuE.trans hfu_k) (hws2E.trans hws2_k)
              (fun h => by cases h) (fun h => by cases h)
              (fun _ => ⟨hsp_fin', by dsimp [s_fin]; rw [hclE]; omega⟩)
              ((fullM6HdrMem_iff ..).mpr
                (by simpa only [R', s_fin, show (1 : BitVec 64) = 1#64 from rfl] using
                  (by assumption : (FullMem c s_fin ⋆ R') _)))
          · intro JE hJE
            c0_hsteps_nogrp
            c0_hsplit
            · c0_hsteps_nogrp; c0_hcall hEma
              refine ⟨c, s_k, R', rfl, hsp_k.1, hm_k, ?_⟩
              rintro ⟨⟩ sE mE hcoreE hlenE hpresE hmE
              have heqE : sE.core = s_k.core := fullCoreState_agrees_with_scratch hcoreE
              have hspE : FullSparseInvW c F0 F_cur sE :=
                fullSparseInvW_of_core_eq hsp_k hlenE heqE hpresE.1
              exact hJE sE mE ⟨hlenE, hspE, by rw [heqE], by rw [heqE], by rw [heqE],
                by rw [heqE], hpresE.2.2.1, hmE⟩
            · c0_hsteps
              exact hJE s_k m_k ⟨hsp_k.1, hsp_k, rfl, rfl, rfl, rfl, rfl, hm_k⟩

theorem m8_ana_failed_lit_m6_hdr_wp (Γ : Env)
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hBumpAna : ∀ a m Q X, m6aBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6_hdr" [i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X → Γ "full_ema_update" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6aAnaFailedLitSpec a m Q X →
      Func.wp Γ m8_ana_failed_lit_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hspec
  obtain ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, _, hconfl, hm0, hQ⟩ :=
    m6aAnaFailedLitSpec_elim hspec
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have ⟨hlen0, hw0, hlm0, hnd0, hext0, hdm0⟩ := hcut
  have hcl := hlen0.core_ok; have hcv_le := hcl.cur_vars_le
  have hte_le := hcl.trail_end_le; have hcur_le := hw0.cur_level_le
  let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext ⋆ R
  rw [fullM6HdrMem_iff] at hm0
  have hEarly : ∀ (m : Mem 64), (FullMem c s ⋆ R_hdr) m → Q (0#64, ()) m := fun m hm =>
    hQ 0#64 ext s m hext (fun hi => ⟨hi, rfl⟩) hlen0 (Or.inl rfl) rfl rfl rfl
      (fun h => by cases h) (fun _ => hcut.toOtfs) (fun h => by cases h)
      ((fullM6HdrMem_iff ..).mpr hm)
  unfold Func.wp m8_ana_failed_lit_m6_hdr_body; dsimp only
  c0_hsplit
  · c0_hsteps; exact hEarly m0 hm0
  · have hcl1 : s.core.cur_level = 1 := by bv_omega
    c0_hsplit
    · c0_hsteps; exact hEarly m0 hm0
    · have hcv_pos : 0 < s.core.cur_vars := by bv_omega
      have hfdec1_len : 1 < s.core.frame_dec.length := by rw [hcl.frame_dec_len]; omega
      c0_hsplit
      · c0_hsteps; exact hEarly m0 hm0
      · let failed := s.core.frame_dec[(1#64 : BitVec 64).toNat]'(by simpa using hfdec1_len)
        let fv := failed >>> 1
        let not_failed := failed ^^^ 1#32
        have hfv_lt : fv.toNat < s.core.cur_vars := by
          have hcv64 :
                                                              s.core.cur_vars < 2 ^ 64 := by omega
          have hnge : ¬ s.core.cur_vars % 2 ^ 64 ≤ failed.toNat / 2 := by assumption
          rw [Nat.mod_eq_of_lt hcv64] at hnge
          dsimp only [fv]; rw [bv32_lshr_1]; exact Nat.lt_of_not_le hnge
        have hfl_lt : failed.toNat < 2 * s.core.cur_vars := by
          dsimp only [fv] at hfv_lt; rw [bv32_lshr_1] at hfv_lt; omega
        have hfl_val_lt : (failed.setWidth 64).toNat < s.core.vals.length := by
          rw [fl_bv32_setWidth64, hcl.vals_len]; omega
        have hfv_lvl_lt : (fv.setWidth 64).toNat < s.core.lvl.length := by
          rw [fl_bv32_setWidth64, hcl.lvl_len]; omega
        have hfv_rsn_lt : (fv.setWidth 64).toNat < s.core.rsns.length := by
          rw [fl_bv32_setWidth64, hcl.rsns_len]; omega
        c0_hsplit
        · c0_hsteps; exact hEarly m0 hm0
        · have hfl_val : s.core.vals[failed.toNat]?.getD 0#8 = 1#8 := by
            have hdom := hw0.vals_domain failed.toNat hfl_lt
            have hidx : failed.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
            rw [List.getElem?_eq_getElem hidx, Option.getD_some] at hdom ⊢
            exact fl_i8_pos_of_not_sle hdom
              (by simpa [failed, Bool.not_eq_true] using (by assumption : _))
          c0_hsplit
          · c0_hsteps; exact hEarly m0 hm0
          · have hfl_lvl1 : (s.core.lvl[failed.toNat / 2]?.getD 0#32).toNat = 1 := by
              have hidx : failed.toNat / 2 < s.core.lvl.length := by rw [hcl.lvl_len]; omega
              have heq1 : s.core.lvl[failed.toNat / 2]'hidx = 1#32 := by assumption
              rw [List.getElem?_eq_getElem hidx, Option.getD_some]
              exact congrArg BitVec.toNat heq1
            c0_hsplit
            · c0_hsteps; exact hEarly m0 hm0
            · have hfl_rsn : s.core.rsns[failed.toNat / 2]?.getD 0xFFFFFFFF#32 =
                  0xFFFFFFFF#32 := by
                have hidx : failed.toNat / 2 < s.core.rsns.length := by rw [hcl.rsns_len]; omega
                have heq : s.core.rsns[failed.toNat / 2]'hidx = 0xFFFFFFFF#32 := by assumption
                rw [List.getElem?_eq_getElem hidx, Option.getD_some]; exact heq
              have himp := failedLit_trail_imp hw0 hcl1 hfl_val hfl_lt hfl_lvl1 hfl_rsn
              have hnf_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_failed.toNat]) := by
                have hent := failedLit_not_failed_of_confl hw0 hcl1 hconfl himp
                simpa only [not_failed, fl_bv32_xor1] using hent
              have hnf_lt : not_failed.toNat < 2 * s.core.cur_vars := by
                rw [fl_bv32_xor1]; exact litNeg_lt_two_mul hfl_lt
              c0_hsteps_nogrp
              let s0 : FullState := { s with core := { s.core with min_clr_len := 0 } }
              have hok0 : FailedStateOk c s s0 cut :=
                ⟨⟨{ hcl with min_clr_len_le := Nat.zero_le _ }, hlen0.scratch_ok⟩, rfl, rfl,
                 ⟨Nat.zero_le _, by simp [s0], fun _ hk => absurd hk (Nat.not_lt_zero _),
                  fun v hv hnz => absurd (hlm0.1 v hv) hnz⟩,
                 fl_mb_empty (fun v hv => hlm0.1 v (by omega))⟩
              have hm_s0 : (FullMem c s0 ⋆ R_hdr) m := by simpa [s0]
              refine wp_join_state (ts := [i64, .bool]) (α := Nat × Bool × FullState)
                (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, ()))
                (Inv := fun st m1 =>
                  st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2.2 cut ∧
                  (!st.2.1 → st.1 = (flIdxs s.core st.2.2.core.mrk s.core.trail_end).length ∧
                    (cnfOfClauses F_cur).EntailsClause
                      (cnfClause (flLits s.core st.2.2.core.mrk s.core.trail_end))) ∧
                  (FullMem c st.2.2 ⋆ R_hdr) m1) ?_ ?_
              · intro Jseed ⟨unres0, done0, s_sd⟩ m_sd ⟨hunres0_le, hok_sd, hact_sd, hm_sd⟩
                dsimp only at hunres0_le hok_sd hact_sd hm_sd
                rw [Blocks.get_here]; dsimp only
                c0_hsteps_nogrp
                let LpIn := Nat × Nat × Bool × Nat × BitVec 32 × Bool × FullState
                refine wp_join_state (ts := [i64, i64, .bool, i64, i32, .bool]) (α := LpIn)
                  (proj := fun st =>
                    (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, st.2.2.1,
                     BitVec.ofNat 64 st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2.1, ()))
                  (Inv := fun st m1 =>
                    let unres := st.1; let ucnt := st.2.1; let done := st.2.2.1
                    let t := st.2.2.2.1; let err := st.2.2.2.2.2.1; let s1 := st.2.2.2.2.2.2
                    FailedStateOk c s s1 cut ∧ t ≤ s.core.trail_end ∧ ucnt ≤ s.core.cur_vars ∧
                    (∀ k < ucnt, (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                      (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
                    (!err → !done →
                      unres = (flIdxs s.core s1.core.mrk t).length ∧
                      (cnfOfClauses F_cur).EntailsClause
                        (cnfClause (flLits s.core s1.core.mrk t))) ∧
                    (FullMem c s1 ⋆ R_hdr) m1) ?_ ?_
                · intro Jexit ⟨unres_f, ucnt_f, done_f, t_f, unit_f, err_f, s_f⟩ m_f
                    ⟨hok_f, ht_f_le, hucnt_le, htmp_f, hact_f, hm_f⟩
                  dsimp only
                  exact fl_post_loop_hdr_wp hClear hBumpAna hBacktrack hAssignLvl hEma hcfg hext hcut
                    hcl1 hnf_lt hnf_ent hQ hok_f ht_f_le hucnt_le htmp_f hact_f hm_f
                · intro Jexit hJexit; c0_hsteps_nogrp
                  refine wp_while_state (ts := [i64, i64, .bool, i64, i32, .bool]) (α := LpIn)
                    (proj := fun st =>
                      (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, st.2.2.1,
                       BitVec.ofNat 64 st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2.1, ()))
                    (μ := fun st => 2 * st.2.2.2.1 + if st.2.2.1 || st.2.2.2.2.2.1 then 0 else 1)
                    (Inv := fun st m1 =>
                      let unres := st.1; let ucnt := st.2.1; let done := st.2.2.1
                      let t := st.2.2.2.1; let err := st.2.2.2.2.2.1; let s1 := st.2.2.2.2.2.2
                      FailedStateOk c s s1 cut ∧ t ≤ s.core.trail_end ∧ ucnt ≤ s.core.cur_vars ∧
                      (∀ k < ucnt, (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                        (cnfOfClauses F_cur).EntailsClause
                          (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
                      (!err → !done →
                        unres = (flIdxs s.core s1.core.mrk t).length ∧
                        (cnfOfClauses F_cur).EntailsClause
                          (cnfClause (flLits s.core s1.core.mrk t))) ∧
                      (FullMem c s1 ⋆ R_hdr) m1) ?_ ?_
                  · intro Jlp hJlp; c0_hsteps
                    have hte_sd : s_sd.core.trail_end = s.core.trail_end := by rw [hok_sd.core]
                    simpa only [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
                      show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl, hte_sd] using
                      hJlp (unres0, 0, done0, s.core.trail_end, 0xFFFFFFFF#32, false, s_sd) m_sd
                        ⟨hok_sd, Nat.le_refl _, Nat.zero_le _, (fun _ hk => by cases hk),
                          fun _ hnd => hact_sd hnd, hm_sd⟩
                  · intro Jlp ⟨unres, ucnt, done, t, unit, err, s_lp⟩ m1
                      ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩ ih_lp
                    dsimp only at hok_lp ht_le hucnt_le htmp_ok hact_ok hm1 ih_lp
                    rw [Blocks.get_here]; dsimp only
                    c0_hsplit
                    · c0_hsteps; exact hJexit (unres, ucnt, done, t, unit, err, s_lp) m1
                        ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩
                    · have hdone_f : done = false := by assumption
                      c0_hsplit
                      · c0_hsteps; exact hJexit (unres, ucnt, done, t, unit, err, s_lp) m1
                          ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩
                      · have herr_f : err = false := by assumption
                        obtain ⟨hunres_len, hact_ent⟩ :=
                          hact_ok (by simp [herr_f]) (by simp [hdone_f])
                        have hunres_bd : unres ≤ s.core.cur_vars :=
                          Nat.le_trans (hunres_len ▸ flIdxs_length_le) (by omega)
                        c0_hsteps_nogrp
                        let FindSt := Nat × Bool × BitVec 32
                        refine wp_join_state (ts := [i64, .bool, i32]) (α := FindSt)
                          (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2, ()))
                          (Inv := fun st m_f =>
                            let t' := st.1; let err' := st.2.1; let lit' := st.2.2
                            m_f = m1 ∧ if err' then t' ≤ t
                            else t' < t ∧ (s.core.trl[t']?.getD 0#32).toNat = lit'.toNat ∧
                              lit'.toNat < 2 * s.core.cur_vars ∧
                              s_lp.core.mrk[lit'.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
                              unres = (flIdxs s.core s_lp.core.mrk (t' + 1)).length ∧
                              (cnfOfClauses F_cur).EntailsClause
                                (cnfClause (flLits s.core s_lp.core.mrk (t' + 1)))) ?_ ?_
                        · intro Jfind ⟨t', err', lit'⟩ m_f ⟨hm_eq, hfind⟩
                          dsimp only at hfind; rw [Blocks.get_here]; dsimp only
                          c0_hsplit
                          · have he : err' = true := by assumption
                            rw [ite_eq_left he] at hfind
                            c0_hsteps
                            exact hJexit (unres, ucnt, done, t', unit, true, s_lp) m_f
                              ⟨hok_lp, by dsimp only; omega, hucnt_le, htmp_ok,
                                (fun h => by cases h), hm_eq ▸ hm1⟩
                          · have he_f : err' = false := by assumption
                            rw [ite_eq_right (he_f ▸ Bool.false_ne_true)] at hfind
                            obtain ⟨ht'_lt, htrl_t', hlit'_lt, hmrk_t'_0, hunres_t'_0,
                              hact_t'_0⟩ := hfind
                            have hlit'_ne := p2_bv32_lit_neq_ff (by omega : lit'.toNat < 2 ^ 31 - 1)
                            c0_hsplit
                            · c0_hsteps; exact absurd (by assumption) hlit'_ne
                            · c0_hsteps_nogrp
                              refine wp_join_state (ts := [i64, i32, .bool])
                                (α := Nat × BitVec 32 × Bool × FullState)
                                (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, ()))
                                (Inv := fun st m2 =>
                                  let ucnt' := st.1; let unit' := st.2.1; let s1 := st.2.2.2
                                  st.2.2.1 = false ∧ FailedStateOk c s s1 cut ∧
                                  s1.core.mrk = s_lp.core.mrk ∧
                                  s1.core.min_clr_len = s_lp.core.min_clr_len ∧
                                  s1.scratch.work_stk1 = s_lp.scratch.work_stk1 ∧
                                  ucnt' ≤ s.core.cur_vars ∧
                                  (∀ k < ucnt', (s1.core.tmp[k]?.getD 0#32).toNat <
                                    2 * s.core.cur_vars ∧
                                    (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
                                  (FullMem c s1 ⋆ R_hdr) m2) ?_ ?_
                              · intro Juc ⟨ucnt', unit', _brk', s1⟩ m2
                                  ⟨hbrk', hok1, hmrk1_eq, hmcl1_eq, hws1_eq, hucnt'_le, htmp_ok',
                                    hm2⟩
                                dsimp only at hbrk' hok1 hmrk1_eq hmcl1_eq hws1_eq hucnt'_le
                                dsimp only at htmp_ok' hm2
                                rw [Blocks.get_here]; dsimp only
                                have hl1_cv := hok1.len.core_ok
                                have hcv_s1 : s1.core.cur_vars = s.core.cur_vars := by
                                  rw [hok1.core]
                                have hmrk_t' : s1.core.mrk[lit'.toNat / 2]?.getD 0#8 ≠ 0#8 := by
                                  rw [hmrk1_eq]; exact hmrk_t'_0
                                have hmrk_t'_trl :
                                    s1.core.mrk[(s.core.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠
                                      0#8 := by rw [htrl_t']; exact hmrk_t'
                                have hunres_t' :
                                    unres = (flIdxs s.core s1.core.mrk (t' + 1)).length := by
                                  rw [hmrk1_eq]; exact hunres_t'_0
                                have hact_t' : (cnfOfClauses F_cur).EntailsClause
                                    (cnfClause (flLits s.core s1.core.mrk (t' + 1))) := by
                                  rw [hmrk1_eq]; exact hact_t'_0
                                have hlv_rsn :
                                    ((lit' >>> 1#32).setWidth 64).toNat < s1.core.rsns.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1, hl1_cv.rsns_len]
                                  have := hok1.len.core_ok.cur_vars_le; omega
                                c0_hsplit
                                · c0_hsteps
                                  exact hJexit (unres, ucnt', done, t', unit', true, s1) m2
                                    ⟨hok1, by dsimp only; omega, hucnt'_le, htmp_ok',
                                      (fun h => by cases h), hm2⟩
                                · have hrsn_ne :
                                      s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 ≠
                                        0xFFFFFFFF#32 := by
                                    have hidx : lit'.toNat / 2 < s1.core.rsns.length := by
                                      rw [hl1_cv.rsns_len]; omega
                                    have heq : s1.core.rsns[lit'.toNat / 2]'hidx ≠
                                        0xFFFFFFFF#32 := by assumption
                                    have hlt_eq : s1.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                        s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                                      rw [hok1.core]
                                    rw [← hlt_eq, List.getElem?_eq_getElem hidx, Option.getD_some]
                                    exact heq
                                  have hrsn_ne' :
                                      s.core.rsns[(s.core.trl[t']?.getD 0#32).toNat / 2]?.getD
                                        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                                    rw [htrl_t']; exact hrsn_ne
                                  have ht'_cut : t' < cut := by
                                    obtain ⟨_, m_c, hm_cut, hm_eq⟩ :=
                                      fl_mb_get hok1.mb (Nat.div_lt_of_lt_mul hlit'_lt) hmrk_t'
                                    have htm := hw0.trail_vars_nodup t' m_c (by omega)
                                      (Nat.lt_of_lt_of_le hm_cut hw0.cut_le)
                                      (by rw [htrl_t', hm_eq])
                                    omega
                                  have hri := hw0.reason_inv_cut t' ht'_cut hrsn_ne'
                                  rw [htrl_t'] at hri
                                  c0_hsteps_nogrp
                                  refine wp_join_state (ts := [i64, .bool, .bool])
                                    (α := Nat × Bool × Bool × FullState)
                                    (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, ()))
                                    (Inv := fun st m3 =>
                                      let unres' := st.1; let done' := st.2.1
                                      let err'' := st.2.2.1; let s3 := st.2.2.2
                                      FailedStateOk c s s3 cut ∧ s3.core.tmp = s1.core.tmp ∧
                                      (!err'' → !done' →
                                        unres' = (flIdxs s.core s3.core.mrk t').length + 1 ∧
                                        (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause (flLits s.core s3.core.mrk t'))) ∧
                                      (FullMem c s3 ⋆ R_hdr) m3) ?_ ?_
                                  · intro Jrsn ⟨unres', done', err'', s3⟩ m3
                                      ⟨hok3, htmp3, hrsn_ok, hm3⟩
                                    dsimp only at hok3 htmp3 hrsn_ok hm3
                                    rw [Blocks.get_here]; dsimp only
                                    have htmp3' : ∀ k < ucnt',
                                        (s3.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                                        (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause [(s3.core.tmp[k]?.getD 0#32).toNat]) := by
                                      intro k hk; rw [htmp3]; exact htmp_ok' k hk
                                    c0_hsplit
                                    · have hd'_t : done' = true := by assumption
                                      c0_hsteps
                                      exact hJexit (unres', ucnt', done', t', unit', err'', s3) m3
                                        ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                                          (fun _ hd => by simp [hd'_t] at hd), hm3⟩
                                    · have hd'_f : done' = false := by assumption
                                      c0_hsplit
                                      · have he''_t : err'' = true := by assumption
                                        c0_hsteps
                                        exact hJexit (unres', ucnt', done', t', unit', err'', s3)
                                          m3 ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                                            (fun he => by simp [he''_t] at he), hm3⟩
                                      · have he''_f : err'' = false := by assumption
                                        obtain ⟨hunres'_eq, hent3⟩ :=
                                          hrsn_ok (by simp [he''_f]) (by simp [hd'_f])
                                        have hunres'_bd : unres' ≤ s.core.cur_vars + 1 :=
                                          Nat.le_trans
                                            (by
                                              rw [hunres'_eq]
                                              exact Nat.succ_le_succ flIdxs_length_le)
                                            (by omega)
                                        c0_hsplit
                                        · have hz : BitVec.ofNat 64 unres' = 0#64 := by assumption
                                          have h0 := congrArg BitVec.toNat hz
                                          rw [bv64_ofNat_toNat (by omega),
                                            show (0#64 : BitVec 64).toNat = 0 from rfl] at h0
                                          omega
                                        · c0_hsteps
                                          rw [p2_bv64_sub1_eq (by omega) (by omega)]
                                          exact ih_lp
                                            (unres' - 1, ucnt', done', t', unit', err'', s3)
                                            m3 (by
                                              dsimp only; rw [hdone_f, herr_f, hd'_f, he''_f]
                                              simp; omega)
                                            ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                                              fun _ _ => ⟨by dsimp only; omega, hent3⟩, hm3⟩
                                  · intro Jrsn hJrsn
                                    have hunres_t'_s :
                                        unres = (flIdxs s.core s1.core.mrk t').length + 1 := by
                                      rw [flIdxs_succ_marked hmrk_t'_trl, List.length_append,
                                        List.length_singleton] at hunres_t'
                                      exact hunres_t'
                                    have hlv_rsn_d : lit'.toNat / 2 < s1.core.rsns.length := by
                                      rw [hl1_cv.rsns_len]; omega
                                    have heq_rsn :
                                        s1.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                        s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                                      rw [hok1.core]
                                    c0_hsplit
                                    · have hbin :
                                          (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                                            0x80000000#32) ≠ 0#32 := by
                                        rw [← heq_rsn, List.getElem?_eq_getElem hlv_rsn_d,
                                          Option.getD_some]
                                        exact (by assumption : _)
                                      rw [ite_eq_left hbin] at hri
                                      obtain ⟨hot_lt, hent_bin, m_ot, hm_ot_lt, hm_ot_eq, _⟩ := hri
                                      have h_ot_norm : (s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d &&&
                                          0x7FFFFFFF#32).toNat =
                                          (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                                            0x7FFFFFFF#32).toNat := by
                                        rw [← heq_rsn, List.getElem?_eq_getElem hlv_rsn_d,
                                          Option.getD_some]
                                      let ot32 :=
                                        s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d &&& 0x7FFFFFFF#32
                                      have hot32_lt : ot32.toNat < 2 * s.core.cur_vars := by
                                        dsimp only [ot32]; rw [h_ot_norm]; exact hot_lt
                                      c0_hsplit
                                      · c0_hsteps
                                        exact hJexit (unres, ucnt', true, t', unit', _brk', s1) m2
                                          ⟨hok1, by dsimp only; omega, hucnt'_le, htmp_ok',
                                            (fun _ hd => by simp at hd), hm2⟩
                                      · have hov_lt := Nat.div_lt_of_lt_mul hot32_lt
                                        have hov_lvl_lt : ot32.toNat / 2 < s1.core.lvl.length := by
                                          rw [hl1_cv.lvl_len]; have := hl1_cv.cur_vars_le; omega
                                        have hov_mrk_lt : ot32.toNat / 2 < s1.core.mrk.length := by
                                          rw [hl1_cv.mrk_len]; have := hl1_cv.cur_vars_le; omega
                                        c0_hsplit
                                        · exfalso
                                          have hcv64 :
                                                              s.core.cur_vars < 2 ^ 64 := by omega
                                          have hge : s.core.cur_vars % 2 ^ 64 ≤ ot32.toNat / 2 := by
                                            dsimp only [ot32]; simpa only [show
                                              (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl]
                                              using (by assumption : _)
                                          rw [Nat.mod_eq_of_lt hcv64] at hge; omega
                                        · c0_hsteps_nogrp
                                          refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                                            (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                                            (Inv := fun st m3 =>
                                              FailedStateOk c s st.2 cut ∧
                                              st.2.core.tmp = s1.core.tmp ∧
                                              st.1 = (flIdxs s.core st.2.core.mrk t').length + 1 ∧
                                              (∀ l ∈ flLits s.core s1.core.mrk t',
                                                l ∈ flLits s.core st.2.core.mrk t') ∧
                                              ((cnfOfClauses F_cur).EntailsClause
                                                  (cnfClause [ot32.toNat ^^^ 1]) ∨
                                                ot32.toNat ∈ flLits s.core st.2.core.mrk t') ∧
                                              (FullMem c st.2 ⋆ R_hdr) m3) ?_ ?_
                                          · intro Jbin ⟨unres_b, s_b⟩ m3
                                              ⟨hok_b, htmp_b, hunres_b, hpres_b, hot_in, hm3⟩
                                            dsimp only at hok_b htmp_b hunres_b hpres_b hot_in hm3
                                            rw [Blocks.get_here]; dsimp only
                                            have hent_b : (cnfOfClauses F_cur).EntailsClause
                                                (cnfClause (flLits s.core s_b.core.mrk t')) := by
                                              refine fl_resolve_step hmrk_t'_trl hact_t' hpres_b
                                                (by simpa [h_ot_norm, ot32, htrl_t'] using hent_bin)
                                                fun q hq => ?_
                                              simp only [List.mem_cons, List.not_mem_nil, or_false]
                                                at hq
                                              rcases hq with rfl | rfl
                                              · exact Or.inl htrl_t'.symm
                                              · exact Or.inr (by
                                                  simpa only [ot32, BitVec.toNat_and,
                                                    show (0x7FFFFFFF#32 : BitVec 32).toNat =
                                                      2147483647 from rfl, h_ot_norm] using hot_in)
                                            c0_hsteps
                                            exact hJrsn (unres_b, done, _brk', s_b) m3
                                              ⟨hok_b, htmp_b, fun _ _ => ⟨hunres_b, hent_b⟩, hm3⟩
                                          · intro Jbin hJbin
                                            c0_hsplit
                                            · c0_hsplit
                                              · have hmrk0_ov := fl_mark_zero_eq hok1 hov_lt
                                                  (by dsimp only [ot32]; assumption)
                                                have hlvl_pos := p2_lvl_pos_of_lt hok1 hov_lvl_lt
                                                  (by dsimp only [ot32]; assumption)
                                                obtain ⟨hmcl_lt, hmcl64, hmcl_ws, hmcl1_bv, hok2,
                                                  hfl_len, hfl_pres, hot_in⟩ :=
                                                  p2_push_step hw0 hcl1 hok1 (by omega) hot32_lt
                                                    hmrk0_ov hlvl_pos
                                                    ⟨m_ot, hm_ot_lt, by rw [hm_ot_eq, h_ot_norm]⟩
                                                    ⟨m_ot, by omega, by rw [hm_ot_eq, h_ot_norm]⟩
                                                let s2 : FullState :=
                                                  { core :=
                                                      { s1.core with
                                                        mrk := s1.core.mrk.set (ot32.toNat / 2) 1#8,
                                                        min_clr_len := s1.core.min_clr_len + 1 },
                                                    scratch :=
                                                      { s1.scratch with
                                                        work_stk1 := s1.scratch.work_stk1.set
                                                          s1.core.min_clr_len (ot32 >>> 1) } }
                                                c0_hsplit; c0_hsteps
                                                have hm2' : (FullMem c s2 ⋆ R_hdr) m := by
                                                  simpa only [s2, ot32, fl_bv32_setWidth64,
                                                    bv32_lshr_1, bv64_ofNat_toNat hmcl64, hmcl1_bv,
                                                    show (2147483647 : BitVec 32) = 0x7FFFFFFF#32
                                                      from rfl,
                                                    show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
                                                rw [p2_bv64_add1_eq (by omega)]
                                                exact hJbin (unres + 1, s2) m
                                                  ⟨hok2, rfl, by rw [hunres_t'_s, hfl_len],
                                                    hfl_pres, hot_in, hm2'⟩
                                              · have hmrk_nz := fl_mark_nz_eq hok1 hov_lt
                                                  (by dsimp only [ot32]; assumption)
                                                have hot_in := fl_mark_lit_skip hw0 hcl1 (by omega)
                                                  (fun _ => ⟨m_ot, by omega,
                                                    by rw [hm_ot_eq, h_ot_norm]⟩)
                                                  (fun _ => ⟨hmrk_nz, m_ot, hm_ot_lt,
                                                    by rw [hm_ot_eq, h_ot_norm]⟩)
                                                c0_hsteps
                                                exact hJbin (unres, s1) m2
                                                  ⟨hok1, rfl, hunres_t'_s, fun _ hl => hl, hot_in,
                                                    hm2⟩
                                            · have hlvl0 := p2_lvl0_of_nlt hok1 hov_lvl_lt
                                                (by dsimp only [ot32]; assumption)
                                              have hot_in := fl_mark_lit_skip (s1 := s1) (t := t')
                                                (q := ot32.toNat) hw0 hcl1 (by omega)
                                                (fun _ => ⟨m_ot, by omega,
                                                  by rw [hm_ot_eq, h_ot_norm]⟩)
                                                (fun hp => by omega)
                                              c0_hsteps
                                              exact hJbin (unres, s1) m2
                                                ⟨hok1, rfl, hunres_t'_s, fun _ hl => hl, hot_in,
                                                  hm2⟩
                                    · have hlg :
                                          (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                                            0x80000000#32) = 0#32 := by
                                        rw [← heq_rsn, List.getElem?_eq_getElem hlv_rsn_d,
                                          Option.getD_some]
                                        simpa only [show (2147483648 : BitVec 32) = 0x80000000#32
                                          from rfl, show (0 : BitVec 32) = 0#32 from rfl] using
                                          (by assumption : _)
                                      rw [ite_eq_right (fun h => absurd hlg h)] at hri
                                      obtain ⟨href, hng, hall⟩ := hri
                                      have hwf := hw0.arena.refs_wf _ href
                                      let rsn32 := s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d
                                      have hrsn_eq : rsn32.toNat =
                                          (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32).toNat
                                          := by
                                        dsimp [rsn32]; rw [← heq_rsn,
                                          List.getElem?_eq_getElem hlv_rsn_d, Option.getD_some]
                                      have har_core1 : s1.core.arena = s.core.arena := by
                                        rw [hok1.core]
                                      have hal_eq : s1.core.arena_len = s.core.arena_len := by
                                        rw [hok1.core]
                                      have har_cap := c.harena; unfold dimacsBound at har_cap
                                      obtain ⟨hrsn_add2_lt, hrsz_eq, hrsn_bd, hlits_len⟩ :=
                                        p2_arena_clause_sz hlen0 hok1.len har_core1 hal_eq hrsn_eq
                                          ⟨hwf.1, hwf.2.1, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1,
                                            hlen0.core_ok.arena_len_le,
                                            hlen0.core_ok.arena_len_arr.symm⟩
                                      have hle3 : rsn32.toNat + 3 ≤ s.core.arena_len := by
                                        rw [hrsn_eq]; exact hwf.1
                                      have hal_c : s.core.arena_len ≤ c.arena_cap :=
                                        hlen0.core_ok.arena_len_le
                                      c0_hsplit
                                      · exfalso
                                        have hgt : s1.core.arena_len % 2 ^ 64 <
                                            (rsn32.toNat + 3) % 2 ^ 64 := by
                                          dsimp only [rsn32]; assumption
                                        rw [hal_eq, Nat.mod_eq_of_lt (by omega :
                                            s.core.arena_len < 2 ^ 64),
                                          Nat.mod_eq_of_lt (by omega : rsn32.toNat + 3 < 2 ^ 64)]
                                          at hgt
                                        omega
                                      · let rsz := s1.core.arena[
                                            (rsn32.setWidth 64 + 2#64).toNat]'hrsn_add2_lt
                                        c0_hsplit
                                        · exfalso
                                          have hlt3 : rsz.toNat < 3 := by
                                            dsimp only [rsz, rsn32]; assumption
                                          have hge3 : 3 ≤ rsz.toNat := by
                                            change 3 ≤ (s1.core.arena[(rsn32.setWidth 64 +
                                              2#64).toNat]'hrsn_add2_lt).toNat
                                            rw [hrsz_eq, hrsn_eq]; exact hwf.2.1
                                          omega
                                        · c0_hsplit
                                          · exfalso
                                            have hle_a : rsn32.toNat + 3 + rsz.toNat ≤
                                                s.core.arena_len := by
                                              change rsn32.toNat + 3 + (s1.core.arena[
                                                (rsn32.setWidth 64 + 2#64).toNat]'
                                                hrsn_add2_lt).toNat ≤ s.core.arena_len
                                              rw [hrsz_eq, hrsn_eq]
                                              have := hwf.2.2.1; have := hwf.2.2.2.1; omega
                                            have hgt : s1.core.arena_len % 2 ^ 64 <
                                                (rsn32.toNat + 3 + rsz.toNat) % 2 ^ 64 := by
                                              dsimp only [rsz, rsn32]; assumption
                                            have hbd64 : rsn32.toNat + 3 + rsz.toNat < 2 ^ 64 := by
                                              omega
                                            rw [hal_eq, Nat.mod_eq_of_lt (by omega :
                                                s.core.arena_len < 2 ^ 64),
                                              Nat.mod_eq_of_lt hbd64] at hgt
                                            omega
                                          · have hrsz_bd : rsz.toNat < 2 ^ 32 := rsz.isLt
                                            let BrkJ := Nat × Bool × Bool × BitVec 32 × FullState
                                            let RsnLp := Nat × BitVec 32 × FullState
                                            c0_hsteps_nogrp
                                            refine wp_join_state (ts := [i64, .bool, .bool, i32])
                                              (α := BrkJ)
                                              (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1,
                                                st.2.2.1, st.2.2.2.1, ()))
                                              (Inv := fun st m3 =>
                                                let u' := st.1; let d' := st.2.1
                                                let e' := st.2.2.1; let s3 := st.2.2.2.2
                                                FailedStateOk c s s3 cut ∧
                                                s3.core.tmp = s1.core.tmp ∧
                                                (!e' → !d' →
                                                  u' = (flIdxs s.core s3.core.mrk t').length + 1 ∧
                                                  (cnfOfClauses F_cur).EntailsClause
                                                    (cnfClause (flLits s.core s3.core.mrk t'))) ∧
                                                (FullMem c s3 ⋆ R_hdr) m3) ?_ ?_
                                            · intro Jb ⟨u', d', e', _j, s3⟩ m3
                                                ⟨hok3, htmp3, hok_b, hm3⟩
                                              dsimp only at hok3 htmp3 hok_b hm3
                                              rw [Blocks.get_here]; dsimp only
                                              c0_hsteps
                                              exact hJrsn (u', d', e', s3) m3
                                                ⟨hok3, htmp3, hok_b, hm3⟩
                                            · intro Jb hJb
                                              refine wp_while_state (ts := [i64, i32]) (α := RsnLp)
                                                (proj := fun st =>
                                                  (BitVec.ofNat 64 st.1, st.2.1, ()))
                                                (μ := fun st => rsz.toNat - st.2.1.toNat)
                                                (Inv := fun st m3 =>
                                                  let uj := st.1; let j := st.2.1; let sj := st.2.2
                                                  j.toNat ≤ rsz.toNat ∧ FailedStateOk c s sj cut ∧
                                                  sj.core.tmp = s1.core.tmp ∧
                                                  uj = (flIdxs s.core sj.core.mrk t').length + 1 ∧
                                                  (∀ l ∈ flLits s.core s1.core.mrk t',
                                                    l ∈ flLits s.core sj.core.mrk t') ∧
                                                  (∀ q ∈ (fullArenaClauseLitsCore s.core
                                                    rsn32.toNat).take j.toNat,
                                                    q = lit'.toNat ∨
                                                    (cnfOfClauses F_cur).EntailsClause
                                                      (cnfClause [q ^^^ 1]) ∨
                                                    q ∈ flLits s.core sj.core.mrk t') ∧
                                                  (FullMem c sj ⋆ R_hdr) m3) ?_ ?_
                                              · intro Jl hJl; c0_hsteps
                                                exact hJl (unres, 0#32, s1) m2
                                                  ⟨Nat.zero_le _, hok1, rfl, hunres_t'_s,
                                                    fun _ hl => hl, fun _ hq => by simp at hq, hm2⟩
                                              · intro Jl ⟨uj, j, sj⟩ m3
                                                  ⟨hj_le, hokj, htmpj, huj_eq, hpresj, hcovj, hm3⟩
                                                  ih_j
                                                dsimp only at hj_le hokj htmpj huj_eq hpresj hcovj
                                                dsimp only at hm3 ih_j
                                                rw [Blocks.get_here]; dsimp only
                                                have hj_cv := hokj.len.core_ok
                                                have har_j : sj.core.arena = s.core.arena := by
                                                  rw [hokj.core]
                                                have huj_bd : uj ≤ s.core.cur_vars + 1 := by
                                                  rw [huj_eq]
                                                  exact Nat.le_trans
                                                    (Nat.succ_le_succ flIdxs_length_le)
                                                    (by omega)
                                                c0_hsplit
                                                · have hj_lt : j.toNat < rsz.toNat := by
                                                    dsimp only [rsz, rsn32]; assumption
                                                  have hj_csz :
                                                      j.toNat <
                                                        fullArenaClauseSizeCore s.core rsn32.toNat
                                                      := by
                                                    rw [← hrsz_eq]; exact hj_lt
                                                  obtain ⟨hot_ar_lt, hot_lits_len, hot_get, hot_mem⟩
                                                    := p2_arena_clause_lit hlen0 hokj.len har_j rfl
                                                      (hrsn_eq.symm ▸ hrsn_bd) hj_csz
                                                  let ot32 := sj.core.arena[(rsn32.setWidth 64 +
                                                    3#64 + j.setWidth 64).toNat]'hot_ar_lt
                                                  have hot_ar_lt_c : (s1.core.rsns[lit'.toNat /
                                                      2].toNat + 3 + j.toNat) % 2 ^ 64 <
                                                      sj.core.arena.length := by
                                                    change (rsn32.toNat + 3 + j.toNat) % 2 ^ 64 <
                                                      sj.core.arena.length
                                                    simpa only [BitVec.toNat_add,
                                                      fl_bv32_setWidth64,
                                                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by omega : rsn32.toNat + 3 < 2 ^ 64)] using
                                                      hot_ar_lt
                                                  have hot_hc : sj.core.arena[(s1.core.rsns[
                                                      lit'.toNat / 2].toNat + 3 + j.toNat) %
                                                      2 ^ 64]'hot_ar_lt_c = ot32 := by
                                                    dsimp only [ot32, rsn32]; congr 1
                                                    rw [BitVec.toNat_add, BitVec.toNat_add,
                                                      fl_bv32_setWidth64, fl_bv32_setWidth64,
                                                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by omega : rsn32.toNat + 3 < 2 ^ 64)]
                                                  have hot_mem_c :
                                                      ot32.toNat ∈ fullArenaClauseLitsCore s.core
                                                        (s.core.rsns[lit'.toNat / 2]?.getD
                                                          0xFFFFFFFF#32).toNat :=
                                                    hrsn_eq ▸ (hot_mem : ot32.toNat ∈
                                                      fullArenaClauseLitsCore s.core rsn32.toNat)
                                                  have hot_lt :
                                                      ot32.toNat < 2 * s.core.cur_vars :=
                                                    hw0.arena.lits_lt _ href hng _ hot_mem_c
                                                  have hj1_bv : (j + 1#32).toNat = j.toNat + 1 :=
                                                    fl_bv32_add1_toNat (by omega)
                                                  c0_hsteps_nogrp
                                                  refine wp_join_state (ts := [i64, .bool, .bool])
                                                    (α := Nat × FullState)
                                                    (proj := fun st => (BitVec.ofNat 64 st.1,
                                                      done, _brk', ()))
                                                    (Inv := fun st m4 =>
                                                      let uj' := st.1; let sj' := st.2
                                                      FailedStateOk c s sj' cut ∧
                                                      sj'.core.tmp = s1.core.tmp ∧
                                                      (∀ l ∈ flLits s.core s1.core.mrk t',
                                                        l ∈ flLits s.core sj'.core.mrk t') ∧
                                                      uj' = (flIdxs s.core sj'.core.mrk
                                                        t').length + 1 ∧
                                                      (∀ q ∈ (fullArenaClauseLitsCore s.core
                                                        rsn32.toNat).take (j.toNat + 1),
                                                        q = lit'.toNat ∨
                                                        (cnfOfClauses F_cur).EntailsClause
                                                          (cnfClause [q ^^^ 1]) ∨
                                                        q ∈ flLits s.core sj'.core.mrk t') ∧
                                                      (FullMem c sj' ⋆ R_hdr) m4) ?_ ?_
                                                  · intro Jc ⟨uj', sj'⟩ m4
                                                      ⟨hokj', htmpj', hpresj', huj'_eq, hcov_j1,
                                                        hm4⟩
                                                    dsimp only at hokj' htmpj' hpresj' huj'_eq
                                                    dsimp only at hcov_j1 hm4
                                                    rw [Blocks.get_here]; dsimp only
                                                    c0_hsteps
                                                    exact ih_j (uj', j + 1#32, sj') m4
                                                      (by dsimp only; omega)
                                                      ⟨by dsimp only; omega, hokj', htmpj', huj'_eq,
                                                        hpresj', (by
                                                          dsimp only
                                                          simpa only [hj1_bv] using hcov_j1), hm4⟩
                                                  · intro Jc hJc
                                                    c0_hsplit
                                                    · c0_hsplit
                                                      · c0_hsteps
                                                        exact hJb (uj, true, _brk', j, sj) m3
                                                          ⟨hokj, htmpj, fun _ hd => by simp at hd,
                                                            hm3⟩
                                                      · have hot_rsn := hall ot32.toNat hot_mem_c
                                                        have hot_ne : ot32.toNat ≠ lit'.toNat := by
                                                          intro he
                                                          exact (by rw [← hot_hc]; assumption :
                                                            ot32 ≠ lit') (BitVec.eq_of_toNat_eq he)
                                                        obtain ⟨m_ot, hm_ot_lt, hm_ot_eq, _⟩ :=
                                                          hot_rsn.resolve_left hot_ne
                                                        have hov_lt := Nat.div_lt_of_lt_mul hot_lt
                                                        have hcvj :
                                                            sj.core.cur_vars = s.core.cur_vars := by
                                                          rw [hokj.core]
                                                        have hov_lvl_lt :
                                                            ot32.toNat / 2 <
                                                              sj.core.lvl.length := by
                                                          rw [hj_cv.lvl_len]
                                                          have := hl1_cv.cur_vars_le
                                                          have := hokj.len.core_ok.cur_vars_le
                                                          omega
                                                        have hov_mrk_lt :
                                                            ot32.toNat / 2 <
                                                              sj.core.mrk.length := by
                                                          rw [hj_cv.mrk_len]
                                                          have := hokj.len.core_ok.cur_vars_le
                                                          omega
                                                        c0_hsplit
                                                        · exfalso
                                                          have hcv64 :
                                                              s.core.cur_vars < 2 ^ 64 := by
                                                            omega
                                                          first
                                                          | exact False.elim (by
                                                              have hge : s.core.cur_vars % 2 ^ 64 ≤
                                                                  ot32.toNat / 2 := by
                                                                rw [← hot_hc]; assumption
                                                              rw [Nat.mod_eq_of_lt hcv64] at hge
                                                              omega)
                                                          | exact False.elim (by
                                                              have hge : sj.core.cur_vars % 2 ^ 64
                                                                  ≤ ot32.toNat / 2 := by
                                                                rw [← hot_hc]; assumption
                                                              rw [hcvj,
                                                                Nat.mod_eq_of_lt hcv64] at hge
                                                              omega)
                                                        · refine wp_join_state (ts := [i64])
                                                            (α := Nat × FullState)
                                                            (proj := fun st =>
                                                              (BitVec.ofNat 64 st.1, ()))
                                                            (Inv := fun st m4 =>
                                                              let uj' := st.1; let sj' := st.2
                                                              FailedStateOk c s sj' cut ∧
                                                              sj'.core.tmp = s1.core.tmp ∧
                                                              (∀ l ∈ flLits s.core s1.core.mrk t',
                                                                l ∈ flLits s.core sj'.core.mrk t') ∧
                                                              uj' = (flIdxs s.core sj'.core.mrk
                                                                t').length + 1 ∧
                                                              (∀ q ∈ (fullArenaClauseLitsCore s.core
                                                                rsn32.toNat).take (j.toNat + 1),
                                                                q = lit'.toNat ∨
                                                                (cnfOfClauses F_cur).EntailsClause
                                                                  (cnfClause [q ^^^ 1]) ∨
                                                                q ∈ flLits s.core sj'.core.mrk t') ∧
                                                              (FullMem c sj' ⋆ R_hdr) m4) ?_ ?_
                                                          · intro Jo ⟨uj', sj'⟩ m4
                                                              ⟨hokj', htmpj', hpresj', huj', hcovj1,
                                                                hm4⟩
                                                            dsimp only at hokj' htmpj' hpresj' huj'
                                                            dsimp only at hcovj1 hm4
                                                            rw [Blocks.get_here]; dsimp only
                                                            c0_hsteps
                                                            exact hJc (uj', sj') m4
                                                              ⟨hokj', htmpj', hpresj', huj', hcovj1,
                                                                hm4⟩
                                                          · intro Jo hJo
                                                            c0_hsplit
                                                            · c0_hsplit
                                                              · have hmrk0_ov := fl_mark_zero_eq
                                                                  hokj hov_lt (by
                                                                    simp only [← hot_hc]
                                                                    assumption)
                                                                have hlvl_pos := p2_lvl_pos_of_lt
                                                                  hokj hov_lvl_lt (by
                                                                    simp only [← hot_hc, show
                                                                      (0#32 : BitVec 32).toNat =
                                                                      BitVec.toNat 0 from rfl]
                                                                    assumption)
                                                                obtain ⟨hmcl_lt, hmcl64, hmcl_ws,
                                                                  hmcl1_bv, hok2, hfl_len,
                                                                  hfl_pres, hot_in⟩ :=
                                                                  p2_push_step hw0 hcl1 hokj
                                                                    (by omega) hot_lt hmrk0_ov
                                                                    hlvl_pos
                                                                    ⟨m_ot, hm_ot_lt, hm_ot_eq⟩
                                                                    ⟨m_ot, by omega, hm_ot_eq⟩
                                                                let s2 : FullState :=
                                                                  { core :=
                                                                      { sj.core with
                                                                        mrk := sj.core.mrk.set
                                                                          (ot32.toNat / 2) 1#8,
                                                                        min_clr_len :=
                                                                          sj.core.min_clr_len + 1 },
                                                                    scratch :=
                                                                      { sj.scratch with
                                                                        work_stk1 :=
                                                                          sj.scratch.work_stk1.set
                                                                            sj.core.min_clr_len
                                                                            (ot32 >>> 1) } }
                                                                have hpres2 :
                                                                    ∀ l ∈ flLits s.core s1.core.mrk
                                                                      t',
                                                                    l ∈ flLits s.core s2.core.mrk
                                                                      t' :=
                                                                  fun l hl =>
                                                                    hfl_pres l (hpresj l hl)
                                                                have hcovj2 :
                                                                    ∀ q ∈ (fullArenaClauseLitsCore
                                                                      s.core rsn32.toNat).take
                                                                      j.toNat,
                                                                    q = lit'.toNat ∨
                                                                    (cnfOfClauses
                                                                      F_cur).EntailsClause
                                                                      (cnfClause [q ^^^ 1]) ∨
                                                                    q ∈ flLits s.core
                                                                      s2.core.mrk t' := fun q hq =>
                                                                  (hcovj q hq).elim Or.inl fun h =>
                                                                    Or.inr (h.elim Or.inl fun hm =>
                                                                      Or.inr (hfl_pres q hm))
                                                                have hcov2 := fl_take_succ_forall _
                                                                  hot_lits_len _ hcovj2 (hot_get ▸
                                                                  hot_in.elim (fun h0 => Or.inr
                                                                    (Or.inl h0)) (fun hm => Or.inr
                                                                    (Or.inr hm)))
                                                                c0_hsplit; c0_hsteps
                                                                have hm2' :
                                                                    (FullMem c s2 ⋆ R_hdr) m := by
                                                                  simpa only [s2, ot32, rsn32,
                                                                    show (3 : BitVec 64) = 3#64
                                                                      from rfl,
                                                                    show BitVec.ofNat 8 1 = 1#8
                                                                      from rfl,
                                                                    fl_bv32_setWidth64, bv32_lshr_1,
                                                                    bv64_ofNat_toNat hmcl64,
                                                                    hmcl1_bv] using hm
                                                                rw [p2_bv64_add1_eq (by omega)]
                                                                exact hJo (uj + 1, s2) m
                                                                  ⟨hok2, htmpj, hpres2,
                                                                    by rw [huj_eq, hfl_len], hcov2,
                                                                    hm2'⟩
                                                              · have hmrk_nz := fl_mark_nz_eq hokj
                                                                  hov_lt (by
                                                                    simp only [← hot_hc]
                                                                    assumption)
                                                                have hot_in := fl_mark_lit_skip
                                                                  hw0 hcl1 (by omega)
                                                                  (fun _ => ⟨m_ot, by omega,
                                                                    hm_ot_eq⟩)
                                                                  (fun _ => ⟨hmrk_nz, m_ot,
                                                                    hm_ot_lt, hm_ot_eq⟩)
                                                                have hcov2 := fl_take_succ_forall _
                                                                  hot_lits_len _ hcovj (hot_get ▸
                                                                  hot_in.elim (fun h => Or.inr
                                                                    (Or.inl h)) (fun h => Or.inr
                                                                    (Or.inr h)))
                                                                c0_hsteps
                                                                exact hJo (uj, sj) m3
                                                                  ⟨hokj, htmpj, hpresj, huj_eq,
                                                                    hcov2, hm3⟩
                                                            · have hlvl0 := p2_lvl0_of_nlt hokj
                                                                hov_lvl_lt (by
                                                                  simp only [← hot_hc, show
                                                                    (0#32 : BitVec 32).toNat =
                                                                    BitVec.toNat 0 from rfl]
                                                                  assumption)
                                                              have hot_in := fl_mark_lit_skip
                                                                (s1 := sj) (t := t')
                                                                (q := ot32.toNat)
                                                                hw0 hcl1 (by omega)
                                                                (fun _ => ⟨m_ot, by omega,
                                                                  hm_ot_eq⟩) (fun hp => by omega)
                                                              have hcov2 := fl_take_succ_forall _
                                                                hot_lits_len _ hcovj (hot_get ▸
                                                                hot_in.elim (fun h => Or.inr
                                                                  (Or.inl h)) (fun h => Or.inr
                                                                  (Or.inr h)))
                                                              c0_hsteps
                                                              exact hJo (uj, sj) m3
                                                                ⟨hokj, htmpj, hpresj, huj_eq, hcov2,
                                                                  hm3⟩
                                                    · have hot_eq : ot32.toNat = lit'.toNat := by
                                                        exact congrArg BitVec.toNat (by
                                                          simp only [← hot_hc]; assumption :
                                                          ot32 = lit')
                                                      have hcov2 := fl_take_succ_forall _
                                                        hot_lits_len _ hcovj (hot_get ▸
                                                        Or.inl hot_eq)
                                                      c0_hsteps
                                                      exact hJc (uj, sj) m3
                                                        ⟨hokj, htmpj, hpresj, huj_eq, hcov2, hm3⟩
                                                · have hrsz_lt_c : (s1.core.rsns[lit'.toNat /
                                                      2].toNat + 2) % 2 ^ 64 <
                                                      s1.core.arena.length := by
                                                    change (rsn32.toNat + 2) % 2 ^ 64 <
                                                      s1.core.arena.length
                                                    simpa only [BitVec.toNat_add,
                                                      fl_bv32_setWidth64,
                                                      show (2#64 : BitVec 64).toNat = 2 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by omega : rsn32.toNat + 2 < 2 ^ 64)] using
                                                      hrsn_add2_lt
                                                  have hrsz_hc : s1.core.arena[(s1.core.rsns[
                                                      lit'.toNat / 2].toNat + 2) % 2 ^ 64]'
                                                      hrsz_lt_c = rsz := by
                                                    dsimp only [rsz, rsn32]; congr 1
                                                    try rw [BitVec.toNat_add, fl_bv32_setWidth64,
                                                      show (2#64 : BitVec 64).toNat = 2 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by omega : rsn32.toNat + 2 < 2 ^ 64)]
                                                  have hj_nge : ¬ j.toNat < rsz.toNat := by
                                                    rw [← hrsz_hc]; assumption
                                                  have hj_eq : j.toNat = rsz.toNat := by omega
                                                  have htake_all :
                                                      (fullArenaClauseLitsCore s.core
                                                        rsn32.toNat).take j.toNat =
                                                      fullArenaClauseLitsCore s.core
                                                        rsn32.toNat := by
                                                    rw [hj_eq, hrsn_eq, ← hlits_len]
                                                    exact List.take_length
                                                  rw [htake_all] at hcovj
                                                  have hent_cl := hw0.arena.entails _ href hng
                                                  rw [← hrsn_eq] at hent_cl
                                                  have hent_j := fl_resolve_step hmrk_t'_trl hact_t'
                                                    hpresj hent_cl
                                                    (by simpa only [htrl_t'] using hcovj)
                                                  c0_hsteps
                                                  exact hJb (uj, done, _brk', j, sj) m3
                                                    ⟨hokj, htmpj, fun _ _ => ⟨huj_eq, hent_j⟩, hm3⟩
                              · intro Juc hJuc
                                c0_hsplit
                                · have hu1 : unres = 1 := by
                                    have heq : BitVec.ofNat 64 unres = 1 := by assumption
                                    have h0 := congrArg BitVec.toNat heq
                                    rw [show (1 : BitVec 64) = 1#64 from rfl] at h0
                                    rwa [bv64_ofNat_toNat (by omega)] at h0
                                  let unit1 := lit' ^^^ 1#32
                                  have hlen1_id : (flIdxs s.core s_lp.core.mrk (t' + 1)).length =
                                      1 := by rw [← hunres_t'_0, hu1]
                                  have hunit_ent : (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause [unit1.toNat]) := by
                                    have hsng := flLits_eq_singleton_of_len1
                                      (by rw [htrl_t']; exact hmrk_t'_0) hlen1_id
                                    rw [hsng, htrl_t'] at hact_t'_0
                                    simpa only [unit1, fl_bv32_xor1] using hact_t'_0
                                  have hunit_lt : unit1.toNat < 2 * s.core.cur_vars := by
                                    dsimp [unit1]; try rw [fl_bv32_xor1]
                                    exact litNeg_lt_two_mul hlit'_lt
                                  c0_hsplit
                                  · have huc_lt : ucnt < s.core.cur_vars := by
                                      have hcv64 :
                                                                s.core.cur_vars < 2 ^ 64 := by omega
                                      have huc64 : ucnt < 2 ^ 64 := by omega
                                      have hlt : ucnt % 2 ^ 64 < s.core.cur_vars % 2 ^ 64 := by
                                        simpa only [hok_lp.core] using (by assumption : _)
                                      rwa [Nat.mod_eq_of_lt huc64, Nat.mod_eq_of_lt hcv64] at hlt
                                    have huc_tmp :
                                        (BitVec.ofNat 64 ucnt).toNat < s_lp.core.tmp.length := by
                                      rw [bv64_ofNat_toNat (by omega),
                                        hok_lp.len.core_ok.tmp_len_arr]; omega
                                    let s2 : FullState :=
                                      { s_lp with core :=
                                        { s_lp.core with tmp := s_lp.core.tmp.set ucnt unit1 } }
                                    have hok2 := fl_failedStateOk_with_tmp hok_lp
                                      (tmp' := s_lp.core.tmp.set ucnt unit1)
                                      (by rw [List.length_set, hok_lp.len.core_ok.tmp_len_arr])
                                    have htmp2 : ∀ k < ucnt + 1,
                                        (s2.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                                        (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause [(s2.core.tmp[k]?.getD 0#32).toNat]) :=
                                      fun k hk => by
                                      rcases Nat.lt_or_eq_of_le
                                        (Nat.le_of_lt_succ hk) with hlt | rfl
                                      · dsimp [s2]; rw [List.getElem?_set_ne (by omega)]
                                        exact htmp_ok k hlt
                                      · dsimp [s2]; rw [List.getElem?_set_self
                                          (by rw [hok_lp.len.core_ok.tmp_len_arr]; omega),
                                          Option.getD_some]
                                        exact ⟨hunit_lt, hunit_ent⟩
                                    rw [hm_eq]; c0_hsteps
                                    have hm2' : (FullMem c s2 ⋆ R_hdr) m := by
                                      simpa only [s2, unit1, show (1 : BitVec 32) = 1#32 from rfl,
                                        bv64_ofNat_toNat (by omega : ucnt < 2 ^ 64)] using hm
                                    rw [p2_bv64_add1_eq (by omega)]
                                    exact hJuc (ucnt + 1, unit1, err', s2) m
                                      ⟨he_f, hok2, rfl, rfl, rfl, by omega, htmp2, hm2'⟩
                                  · c0_hsteps
                                    rw [hm_eq, show (lit' ^^^ (1 : BitVec 32)) = unit1 from rfl]
                                    exact hJexit (unres, ucnt, done, t', unit1, true, s_lp) m1
                                      ⟨hok_lp, by dsimp only; omega, hucnt_le, htmp_ok,
                                        (fun h => by cases h), hm1⟩
                                · c0_hsteps; rw [hm_eq]
                                  exact hJuc (ucnt, unit, err', s_lp) m1
                                    ⟨he_f, hok_lp, rfl, rfl, rfl, hucnt_le, htmp_ok, hm1⟩
                        · intro Jfind hJfind; c0_hsteps_nogrp
                          refine wp_while_state (ts := [i64]) (α := Nat)
                            (proj := fun tc => (BitVec.ofNat 64 tc, ())) (μ := fun tc => tc)
                            (Inv := fun tc m_w => tc ≤ t ∧
                              flIdxs s.core s_lp.core.mrk tc = flIdxs s.core s_lp.core.mrk t ∧
                              m_w = m1) ?_ ?_
                          · intro Jw hJw; c0_hsteps; exact hJw t m1 ⟨Nat.le_refl _, rfl, rfl⟩
                          · intro Jw tc m_w ⟨htc_le, hfl_eq, hm_eq⟩ ih_w
                            rw [Blocks.get_here]; dsimp only
                            c0_hsplit
                            · c0_hsplit
                              · have htc0 : tc = 0 := by
                                  have hz : BitVec.ofNat 64 tc = 0#64 := by assumption
                                  have := congrArg BitVec.toNat hz
                                  rwa [bv64_ofNat_toNat (by omega)] at this
                                c0_hsteps
                                refine hJfind (tc, true, 0xFFFFFFFF#32) m_w ⟨hm_eq, ?_⟩
                                simp only [↓reduceIte]; exact htc_le
                              · have htc_pos : 0 < tc := Nat.pos_of_ne_zero fun hz =>
                                  (by assumption : BitVec.ofNat 64 tc ≠ 0#64) (by subst hz; rfl)
                                have hsub_bv := p2_bv64_sub1_eq htc_pos (by omega : tc < 2 ^ 64)
                                have htrl_lp : s_lp.core.trl = s.core.trl := by rw [hok_lp.core]
                                have hcv_lp : s_lp.core.cur_vars = s.core.cur_vars := by
                                  rw [hok_lp.core]
                                have htc1_lt : tc - 1 < s_lp.core.trl.length := by
                                  rw [hok_lp.len.core_ok.trl_len]; omega
                                have htc1_te : tc - 1 < s.core.trail_end := by omega
                                have htl_lt : (s_lp.core.trl[(BitVec.ofNat 64 (tc - 1)).toNat]'
                                    (by rw [bv64_ofNat_toNat (by omega)]; exact htc1_lt)).toNat <
                                    2 * s.core.cur_vars := by
                                  simp only [bv64_ofNat_toNat (by omega : tc - 1 < 2 ^ 64), htrl_lp]
                                  have h1 := hw0.trail_lits_lt (tc - 1) htc1_te
                                  rwa [List.getElem?_eq_getElem (by rw [hcl.trl_len]; omega),
                                    Option.getD_some] at h1
                                have htl_mrk_lt :
                                    (((s_lp.core.trl[(BitVec.ofNat 64 (tc - 1)).toNat]'(by
                                      rw [bv64_ofNat_toNat (by omega)]; exact htc1_lt) >>>
                                      1#32).setWidth 64).toNat) < s_lp.core.mrk.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1, hok_lp.len.core_ok.mrk_len]
                                  omega
                                have hm_w : (FullMem c s_lp ⋆ R_hdr) m_w := hm_eq ▸ hm1
                                have hidx1 : (BitVec.ofNat 64 tc - 1).toNat = tc - 1 := by
                                  rw [hsub_bv, bv64_ofNat_toNat (by omega)]
                                have hbt1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                                have hidx2 :
                                    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tc) % 2 ^ 64 =
                                      tc - 1 := by
                                  simp only [hbt1]; omega
                                have h032 :
                                    BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32 := rfl
                                have hidx3 : (BitVec.ofNat 64 (tc - 1)).toNat = tc - 1 :=
                                  bv64_ofNat_toNat (by omega)
                                have htc1_bv_lt :
                                    (BitVec.ofNat 64 tc - 1).toNat < s_lp.core.trl.length := by
                                  rw [hidx1]; exact htc1_lt
                                have htl_mrk_bv_lt :
                                    (((s_lp.core.trl[(BitVec.ofNat 64 tc - 1).toNat]'htc1_bv_lt >>>
                                      1#32).setWidth 64).toNat) < s_lp.core.mrk.length := by
                                  simpa only [hsub_bv] using htl_mrk_lt
                                c0_hsplit
                                · exfalso
                                  have htrl_d :
                                      ∀ (h1 : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tc) %
                                        2 ^ 64 < s_lp.core.trl.length)
                                        (h2 : tc - 1 < s_lp.core.trl.length),
                                      s_lp.core.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
                                        tc) % 2 ^ 64]'h1 = s_lp.core.trl[tc - 1]'h2 := fun _ _ =>
                                    p2_getElem_congr_list rfl hidx2
                                  have hge := hc
                                  rw [htrl_d _ htc1_lt] at hge
                                  try rw [hcv_lp] at hge
                                  have hlt1 : (s_lp.core.trl[tc - 1]'htc1_lt).toNat <
                                      2 * s.core.cur_vars := by
                                    have h1 := htl_lt; simp only [hidx3] at h1; exact h1
                                  have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
                                  rw [Nat.mod_eq_of_lt hcv64] at hge; omega
                                · have hsub1 : (tc - 1) + 1 = tc := Nat.sub_add_cancel htc_pos
                                  let tl := s_lp.core.trl[(BitVec.ofNat 64 tc - 1).toNat]'htc1_bv_lt
                                  have htl_base : tl = s_lp.core.trl[tc - 1]'htc1_lt :=
                                    p2_getElem_congr_list rfl hidx1
                                  have htl_lt' : tl.toNat < 2 * s.core.cur_vars := by
                                    rw [htl_base]; simpa only [hidx3] using htl_lt
                                  have htl_eq :
                                      (s.core.trl[tc - 1]?.getD 0#32).toNat = tl.toNat := by
                                    rw [htl_base]
                                    have hget := p2_getElem_congr_list (by rw [hok_lp.core]) rfl
                                      (hix := htc1_lt) (hjy := by rw [hcl.trl_len]; omega)
                                    rw [hget, List.getElem?_eq_getElem (by rw [hcl.trl_len]; omega),
                                      Option.getD_some]
                                  c0_hsplit
                                  · have hmrk_nz : s_lp.core.mrk[tl.toNat / 2]?.getD 0#8 ≠ 0#8 := by
                                      have hov_m : tl.toNat / 2 < s_lp.core.mrk.length := by
                                        rw [hok_lp.len.core_ok.mrk_len]; omega
                                      have hne0 : BitVec.setWidth 32
                                          (s_lp.core.mrk[tl.toNat / 2]'hov_m) ≠ 0#32 := by
                                        have hhc := hc
                                        try simp only [hidx2, h032] at hhc
                                        dsimp only [tl]; try simp only [hidx1]
                                        exact hhc
                                      exact fl_mark_nz_eq hok_lp (by omega :
                                        tl.toNat / 2 < s.core.cur_vars) hne0
                                    c0_hsteps
                                    let fJ : BitVec 64 → Bool → Prop :=
                                      fun a b => Jfind (a, b, tl, ()) m_w
                                    change fJ (BitVec.ofNat 64 tc - 1) err
                                    rw [show fJ (BitVec.ofNat 64 tc - 1) err =
                                        fJ (BitVec.ofNat 64 (tc - 1)) false by
                                      dsimp only [fJ]; rw [hsub_bv, herr_f]]
                                    refine hJfind (tc - 1, false, tl) m_w ⟨hm_eq, ?_⟩
                                    simp only [Bool.false_eq_true, ↓reduceIte]
                                    refine ⟨by omega, htl_eq, htl_lt', hmrk_nz, ?_, ?_⟩
                                    · rw [hsub1, hfl_eq]; exact hunres_len
                                    · rw [hsub1, flLits_congr_idxs hfl_eq]; exact hact_ent
                                  · have hmrk0_w : s_lp.core.mrk[
                                        (s.core.trl[tc - 1]?.getD 0#32).toNat / 2]?.getD 0#8 =
                                        0#8 := by
                                      have hov_m : tl.toNat / 2 < s_lp.core.mrk.length := by
                                        rw [hok_lp.len.core_ok.mrk_len]; omega
                                      have he0 : BitVec.setWidth 32
                                          (s_lp.core.mrk[tl.toNat / 2]'hov_m) = 0#32 := by
                                        have hhc := hc
                                        try simp only [hidx2, h032] at hhc
                                        dsimp only [tl]; try simp only [hidx1]
                                        exact hhc
                                      rw [htl_eq]
                                      exact fl_mark_zero_eq hok_lp (by omega) he0
                                    have hfl_next : flIdxs s.core s_lp.core.mrk (tc - 1) =
                                        flIdxs s.core s_lp.core.mrk t := by
                                      have hun : ∀ j, tc - 1 ≤ j → j < tc →
                                          s_lp.core.mrk[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD
                                            0#8 = 0#8 := fun j hj1 hj2 => by
                                        obtain rfl : j = tc - 1 := by omega
                                        exact hmrk0_w
                                      exact (flIdxs_eq_of_unmarked_above (by omega) hun).symm.trans
                                        hfl_eq
                                    c0_hsteps; rw [hsub_bv]
                                    exact ih_w (tc - 1) m_w (by omega) ⟨by omega, hfl_next, hm_eq⟩
                            · c0_hsteps; exact absurd (by assumption : true = false) (by decide)
              · intro Jseed hJseed; c0_hsplit
                · have hct1 : s.core.confl_type = 1#64 := by simpa [s0] using (by assumption : _)
                  rcases hconfl.1 with ⟨_, hc0_lt, hc1_lt, hf0, hf1, hent_bin⟩ | ⟨hne, _⟩
                  · have hconfl2 := hconfl.2; rw [ite_eq_left hct1] at hconfl2
                    let c0 := s.core.confl_lit0.setWidth 32
                    let c1 := s.core.confl_lit1.setWidth 32
                    have hc0_to : c0.toNat = s.core.confl_lit0.toNat := by
                      dsimp [c0]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    have hc1_to : c1.toNat = s.core.confl_lit1.toNat := by
                      dsimp [c1]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    have hm_trail0 := (hw0.vals_false_iff _ hc0_lt).mp hf0
                    have hm_trail1 := (hw0.vals_false_iff _ hc1_lt).mp hf1
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [i64, .bool]) (α := Nat × Bool × FullState)
                      (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, ()))
                      (Inv := fun st m1 =>
                        st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2.2 cut ∧
                        (!st.2.1 → st.1 = (flIdxs s.core st.2.2.core.mrk s.core.trail_end).length ∧
                          (cnfOfClauses F_cur).EntailsClause
                            (cnfClause (flLits s.core st.2.2.core.mrk s.core.trail_end))) ∧
                        (FullMem c st.2.2 ⋆ R_hdr) m1) ?_ ?_
                    · intro _ ⟨un1, dn1, sb1⟩ m1 ⟨hun1, hok1, hact1, hm1⟩
                      dsimp only at hun1 hok1 hact1 hm1
                      rw [Blocks.get_here]; dsimp only
                      c0_hsteps; exact hJseed (un1, dn1, sb1) m1 ⟨hun1, hok1, hact1, hm1⟩
                    · intro J1 hJ1; c0_hsplit
                      · c0_hsteps; refine hJ1 (0, true, s0) m
                          ⟨Nat.zero_le _, hok0, (fun h => by cases h), hm_s0⟩
                      · c0_hsplit
                        · c0_hsteps; refine hJ1 (0, true, s0) m
                            ⟨Nat.zero_le _, hok0, (fun h => by cases h), hm_s0⟩
                        · c0_hsplit
                          · exfalso
                            have hcv64 :
                                                              s.core.cur_vars < 2 ^ 64 := by omega
                            have hge : s.core.cur_vars % 2 ^ 64 ≤ c0.toNat / 2 := by
                              dsimp only [c0, s0]; assumption
                            rw [Nat.mod_eq_of_lt hcv64, hc0_to] at hge; omega
                          · c0_hsplit
                            · exfalso
                              have hcv64 :
                                                              s.core.cur_vars < 2 ^ 64 := by omega
                              have hge : s.core.cur_vars % 2 ^ 64 ≤ c1.toNat / 2 := by
                                dsimp only [c1, s0]; assumption
                              rw [Nat.mod_eq_of_lt hcv64, hc1_to] at hge; omega
                            · c0_hsteps_nogrp
                              refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                                (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                                (Inv := fun st m1 =>
                                  st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2 cut ∧
                                  st.1 = (flIdxs s.core st.2.core.mrk s.core.trail_end).length ∧
                                  ((cnfOfClauses F_cur).EntailsClause (cnfClause [c0.toNat ^^^ 1]) ∨
                                    c0.toNat ∈ flLits s.core st.2.core.mrk s.core.trail_end) ∧
                                  (FullMem c st.2 ⋆ R_hdr) m1) ?_ ?_
                              · intro Jv0 ⟨u1, sa⟩ m1 ⟨hu1_le, hoka, hu1_eq, hc0_in, hm1⟩
                                dsimp only at hu1_le hoka hu1_eq hc0_in hm1
                                rw [Blocks.get_here]; dsimp only
                                have hc1_lvl_lt : ((c1 >>> 1#32).setWidth 64).toNat <
                                    sa.core.lvl.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1, hc1_to,
                                    hoka.len.core_ok.lvl_len]; omega
                                have hc1_mrk_lt : ((c1 >>> 1#32).setWidth 64).toNat <
                                    sa.core.mrk.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1, hc1_to,
                                    hoka.len.core_ok.mrk_len]; omega
                                c0_hsteps_nogrp
                                refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                                  (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                                  (Inv := fun st m2 =>
                                    st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2 cut ∧
                                    st.1 = (flIdxs s.core st.2.core.mrk s.core.trail_end).length ∧
                                    ((cnfOfClauses F_cur).EntailsClause
                                        (cnfClause [c0.toNat ^^^ 1]) ∨
                                      c0.toNat ∈ flLits s.core st.2.core.mrk s.core.trail_end) ∧
                                    ((cnfOfClauses F_cur).EntailsClause
                                        (cnfClause [c1.toNat ^^^ 1]) ∨
                                      c1.toNat ∈ flLits s.core st.2.core.mrk s.core.trail_end) ∧
                                    (FullMem c st.2 ⋆ R_hdr) m2) ?_ ?_
                                · intro Jv1 ⟨u2, sb⟩ m2
                                    ⟨hu2_le, hoka_b, hu2_eq, hc0_b, hc1_b, hm2⟩
                                  dsimp only at hu2_le hoka_b hu2_eq hc0_b hc1_b hm2
                                  rw [Blocks.get_here]; dsimp only
                                  have hent_sb : (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause (flLits s.core sb.core.mrk s.core.trail_end)) := by
                                    refine fl_entails_of_clause
                                      (by simpa only [hc0_to, hc1_to] using hent_bin) fun q hq => ?_
                                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                                    rcases hq with rfl | rfl
                                    · simpa only [hc0_to] using hc0_b
                                    · simpa only [hc1_to] using hc1_b
                                  c0_hsteps
                                  exact hJ1 (u2, false, sb) m2
                                    ⟨hu2_le, hoka_b, fun _ => ⟨hu2_eq, hent_sb⟩, hm2⟩
                                · intro Jv1 hJv1
                                  have hc1_to' : c1.toNat < 2 * s.core.cur_vars := by omega
                                  have hcva_eq : sa.core.cur_vars = s.core.cur_vars := by
                                    rw [hoka.core]
                                  c0_hsplit
                                  · have hhc_lvl := hc
                                    c0_hsplit
                                    · have hmrk0_v1 := fl_mark_zero_eq (ov := c1.toNat / 2) hoka
                                        (by omega) (by
                                          have hhc := hc
                                          try simp only [c1, BitVec.toNat_setWidth] at hhc ⊢
                                          first | exact hhc | (
                                            dsimp only [s0] at hhc ⊢; exact hhc))
                                      have hlvl_pos1 := p2_lvl_pos_of_lt (v := c1.toNat / 2) hoka
                                        (by rw [hoka.len.core_ok.lvl_len]; omega) (by
                                          have hhc := hhc_lvl
                                          try simp only [c1, BitVec.toNat_setWidth,
                                            show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from
                                              rfl] at hhc ⊢
                                          first | exact hhc | (
                                            dsimp only [s0] at hhc ⊢; exact hhc))
                                      have hlv1_cl : (s.core.lvl[c1.toNat / 2]?.getD 0#32).toNat =
                                          s.core.cur_level := by
                                        obtain ⟨m1, hm1_te, hm1_eq⟩ := hm_trail1
                                        have hle := hw0.lvl_le m1 hm1_te
                                        rw [hm1_eq, fl_xor1_div2, ← hc1_to] at hle; omega
                                      obtain ⟨hmcl_lt, hmcl64, hmcl_ws, hmcl1_bv, hokb, hfl_len,
                                        hfl_pres, hc1_in⟩ := p2_push_step hw0 hcl1 hoka
                                        (Nat.le_refl _) hc1_to' hmrk0_v1 hlvl_pos1
                                        (hc1_to ▸ hm_trail1) (hc1_to ▸ hconfl2.2 (hc1_to ▸ hlv1_cl))
                                      let sb : FullState :=
                                        { core :=
                                            { sa.core with
                                              mrk := sa.core.mrk.set (c1.toNat / 2) 1#8,
                                              min_clr_len := sa.core.min_clr_len + 1 },
                                          scratch :=
                                            { sa.scratch with
                                              work_stk1 := sa.scratch.work_stk1.set
                                                sa.core.min_clr_len (c1 >>> 1) } }
                                      c0_hsteps
                                      have hm2' : (FullMem c sb ⋆ R_hdr) m := by
                                        simpa only [sb, fl_bv32_setWidth64, bv32_lshr_1,
                                          bv64_ofNat_toNat hmcl64, hmcl1_bv] using hm
                                      have hc0_b := hc0_in.elim Or.inl fun hmem =>
                                        Or.inr (hfl_pres _ hmem)
                                      have hu1_succ_eq : u1 + 1 =
                                          (flIdxs s.core sb.core.mrk s.core.trail_end).length := by
                                        rw [hfl_len, hu1_eq]
                                      have hu1_succ_le : u1 + 1 ≤ s.core.cur_vars := by
                                        rw [hu1_succ_eq]; exact Nat.le_trans flIdxs_length_le hte_le
                                      rw [p2_bv64_add1_eq (by omega)]
                                      exact hJv1 (u1 + 1, sb) m
                                        ⟨hu1_succ_le, hokb, hu1_succ_eq, hc0_b, hc1_in, hm2'⟩
                                    · have hmrk_nz := fl_mark_nz_eq (ov := c1.toNat / 2) hoka
                                        (by omega) (by
                                          have hhc := hc
                                          try simp only [c1, BitVec.toNat_setWidth] at hhc ⊢
                                          first | exact hhc | (
                                            dsimp only [s0] at hhc ⊢; exact hhc))
                                      have hc1_in := fl_mark_lit_skip (s1 := sa) (q := c1.toNat)
                                        hw0 hcl1 (Nat.le_refl _)
                                        (fun _ => by simpa [hc1_to] using hm_trail1)
                                        (fun _ => ⟨hmrk_nz, by simpa [hc1_to] using hm_trail1⟩)
                                      c0_hsteps
                                      exact hJv1 (u1, sa) m1
                                        ⟨hu1_le, hoka, hu1_eq, hc0_in, hc1_in, hm1⟩
                                  · have hlvl0 := p2_lvl0_of_nlt (v := c1.toNat / 2) hoka
                                      (by rw [hoka.len.core_ok.lvl_len]; omega) (by
                                        have hhc := hc
                                        try simp only [c1, BitVec.toNat_setWidth,
                                          show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from
                                            rfl] at hhc ⊢
                                        first | exact hhc | (
                                          dsimp only [s0] at hhc ⊢; exact hhc))
                                    have hc1_in := fl_mark_lit_skip (s1 := sa) (q := c1.toNat) hw0
                                      hcl1 (Nat.le_refl _)
                                      (fun _ => by simpa [hc1_to] using hm_trail1)
                                      (fun hp => by omega)
                                    c0_hsteps
                                    exact hJv1 (u1, sa) m1
                                      ⟨hu1_le, hoka, hu1_eq, hc0_in, hc1_in, hm1⟩
                              · intro Jv0 hJv0
                                have hc0_to' : c0.toNat < 2 * s.core.cur_vars := by omega
                                have hc0_lvl_lt : ((c0 >>> 1#32).setWidth 64).toNat <
                                    s0.core.lvl.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1 c0,
                                    hok0.len.core_ok.lvl_len]; omega
                                have hc0_mrk_lt : ((c0 >>> 1#32).setWidth 64).toNat <
                                    s0.core.mrk.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1 c0,
                                    hok0.len.core_ok.mrk_len]; omega
                                c0_hsplit
                                · have hhc_lvl := hc
                                  c0_hsplit
                                  · have hmrk0_v0 := fl_mark_zero_eq (ov := c0.toNat / 2) hok0
                                      (by omega) (by
                                        have hhc := hc
                                        try simp only [c0, BitVec.toNat_setWidth] at hhc ⊢
                                        first | exact hhc | (
                                          dsimp only [s0] at hhc ⊢; exact hhc))
                                    have hlvl_pos0 := p2_lvl_pos_of_lt (v := c0.toNat / 2) hok0
                                      (by rw [hok0.len.core_ok.lvl_len]; omega) (by
                                        have hhc := hhc_lvl
                                        try simp only [c0, BitVec.toNat_setWidth,
                                          show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from
                                            rfl] at hhc ⊢
                                        first | exact hhc | (
                                          dsimp only [s0] at hhc ⊢; exact hhc))
                                    have hlv0_cl : (s.core.lvl[c0.toNat / 2]?.getD 0#32).toNat =
                                        s.core.cur_level := by
                                      obtain ⟨m0', hm0_te, hm0_eq⟩ := hm_trail0
                                      have hle := hw0.lvl_le m0' hm0_te
                                      rw [hm0_eq, fl_xor1_div2, ← hc0_to] at hle; omega
                                    obtain ⟨hmcl_lt, hmcl64, hmcl_ws, hmcl1_bv, hoka, hfl_len, _,
                                      hc0_in⟩ := p2_push_step hw0 hcl1 hok0 (Nat.le_refl _) hc0_to'
                                      hmrk0_v0 hlvl_pos0 (hc0_to ▸ hm_trail0)
                                      (hc0_to ▸ hconfl2.1 (hc0_to ▸ hlv0_cl))
                                    let sa : FullState :=
                                      { core :=
                                          { s0.core with
                                            mrk := s0.core.mrk.set (c0.toNat / 2) 1#8,
                                            min_clr_len := s0.core.min_clr_len + 1 },
                                        scratch :=
                                          { s0.scratch with
                                            work_stk1 := s0.scratch.work_stk1.set
                                              s0.core.min_clr_len (c0 >>> 1) } }
                                    c0_hsteps
                                    have hm1' : (FullMem c sa ⋆ R_hdr) m := by
                                      simpa only [sa, c0, fl_bv32_setWidth64, bv32_lshr_1,
                                        bv64_ofNat_toNat hmcl64, hmcl1_bv,
                                        show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
                                    exact hJv0 (1, sa) m ⟨by omega, hoka, by
                                      rw [hfl_len, flIdxs_eq_nil_of_zero (fun j hj =>
                                        hlm0.1 ((s.core.trl[j]?.getD 0#32).toNat / 2)
                                          (Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul
                                            (hw0.trail_lits_lt j hj)) hcv_le))]; rfl, hc0_in, hm1'⟩
                                  · have hmrk_nz := fl_mark_nz_eq (ov := c0.toNat / 2) hok0
                                      (by omega) (by
                                        have hhc := hc
                                        try simp only [c0, BitVec.toNat_setWidth] at hhc ⊢
                                        first | exact hhc | (
                                          dsimp only [s0] at hhc ⊢; exact hhc))
                                    have hc0_in := fl_mark_lit_skip (s1 := s0) (q := c0.toNat)
                                      hw0 hcl1 (Nat.le_refl _)
                                      (fun _ => by simpa [hc0_to] using hm_trail0)
                                      (fun _ => ⟨hmrk_nz, by simpa [hc0_to] using hm_trail0⟩)
                                    c0_hsteps
                                    exact hJv0 (0, s0) m ⟨Nat.zero_le _, hok0, by
                                      rw [flIdxs_eq_nil_of_zero (fun j hj =>
                                        hlm0.1 ((s.core.trl[j]?.getD 0#32).toNat / 2)
                                          (Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul
                                            (hw0.trail_lits_lt j hj)) hcv_le))]; rfl, hc0_in, hm_s0⟩
                                · have hlvl0 := p2_lvl0_of_nlt (v := c0.toNat / 2) hok0
                                    (by rw [hok0.len.core_ok.lvl_len]; omega) (by
                                      have hhc := hc
                                      try simp only [c0, BitVec.toNat_setWidth,
                                        show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from
                                          rfl] at hhc ⊢
                                      first | exact hhc | (
                                        dsimp only [s0] at hhc ⊢; exact hhc))
                                  have hc0_in := fl_mark_lit_skip (s1 := s0) (q := c0.toNat)
                                    hw0 hcl1 (Nat.le_refl _)
                                    (fun _ => by simpa [hc0_to] using hm_trail0)
                                    (fun hp => by omega)
                                  c0_hsteps
                                  exact hJv0 (0, s0) m ⟨Nat.zero_le _, hok0, by
                                    rw [flIdxs_eq_nil_of_zero (fun j hj =>
                                      hlm0.1 ((s.core.trl[j]?.getD 0#32).toNat / 2)
                                        (Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul
                                          (hw0.trail_lits_lt j hj)) hcv_le))]; rfl, hc0_in, hm_s0⟩
                  · exact absurd (hct1.symm.trans hne) (by decide)
                · have hct_ne : s.core.confl_type ≠ 1#64 := by simpa [s0] using (by assumption : _)
                  rcases hconfl.1 with ⟨h1, _⟩ | ⟨hct2, href, hng, hfals⟩
                  · exact absurd h1 hct_ne
                  · have hconfl2 := hconfl.2; rw [ite_eq_right hct_ne] at hconfl2
                    have hwf := hw0.arena.refs_wf _ href
                    have har_cap := c.harena; unfold dimacsBound at har_cap
                    have hal_le := hcl.arena_len_le
                    let cr32 := s0.core.confl_ref.setWidth 32
                    have hcr_to : cr32.toNat = s.core.confl_ref.toNat := by
                      dsimp [cr32, s0]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    obtain ⟨hcr_add2_lt, hcsz_eq, hcsz_bd, hcsz_lits_len⟩ :=
                      p2_arena_clause_sz hlen0 hok0.len (by rfl) (by rfl) hcr_to
                        ⟨hwf.1, hwf.2.1, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1,
                          hcl.arena_len_le, hcl.arena_len_arr.symm⟩
                    c0_hsplit
                    · exfalso
                      have hle3 : cr32.toNat + 3 ≤ s.core.arena_len := by rw [hcr_to]; exact hwf.1
                      have hal64 : s.core.arena_len < 2 ^ 64 := by omega
                      have hgt : s0.core.arena_len % 2 ^ 64 < (cr32.toNat + 3) % 2 ^ 64 := by
                        dsimp only [cr32, s0]; assumption
                      dsimp only [s0] at hgt
                      rw [Nat.mod_eq_of_lt hal64,
                        Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 < 2 ^ 64)] at hgt; omega
                    · let csz := s0.core.arena[(cr32.setWidth 64 + 2#64).toNat]'hcr_add2_lt
                      c0_hsplit
                      · exfalso
                        have hle_a : cr32.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                          change cr32.toNat + 3 + (s0.core.arena[(cr32.setWidth 64 +
                            2#64).toNat]'hcr_add2_lt).toNat ≤ s.core.arena_len
                          rw [hcsz_eq, hcr_to]; have := hwf.2.2.1; have := hwf.2.2.2.1; omega
                        have hcsz_bd32 : csz.toNat < 2 ^ 32 := csz.isLt
                        have hal64 : s.core.arena_len < 2 ^ 64 := by omega
                        have hgt : s0.core.arena_len % 2 ^ 64 <
                            (cr32.toNat + 3 + csz.toNat) % 2 ^ 64 := by
                          dsimp only [csz, cr32, s0]; assumption
                        dsimp only [s0] at hgt
                        rw [Nat.mod_eq_of_lt hal64,
                          Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 + csz.toNat < 2 ^ 64)] at hgt
                        omega
                      · c0_hsteps_nogrp
                        refine wp_join_state (ts := [i64, .bool, i32])
                          (α := Nat × Bool × BitVec 32 × FullState)
                          (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, ()))
                          (Inv := fun st m1 =>
                            st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2.2.2 cut ∧
                            (!st.2.1 → st.1 =
                              (flIdxs s.core st.2.2.2.core.mrk s.core.trail_end).length ∧
                              (cnfOfClauses F_cur).EntailsClause
                                (cnfClause (flLits s.core st.2.2.2.core.mrk s.core.trail_end))) ∧
                            (FullMem c st.2.2.2 ⋆ R_hdr) m1) ?_ ?_
                        · intro _ ⟨un_s, dn_s, _i_s, s_s⟩ m1 ⟨hun_le, hok_s, hact_s, hm1⟩
                          dsimp only at hun_le hok_s hact_s hm1
                          rw [Blocks.get_here]; dsimp only
                          c0_hsteps; exact hJseed (un_s, dn_s, s_s) m1 ⟨hun_le, hok_s, hact_s, hm1⟩
                        · intro J1 hJ1
                          let SdLp := Nat × BitVec 32 × FullState
                          refine wp_while_state (ts := [i64, i32]) (α := SdLp)
                            (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, ()))
                            (μ := fun st => csz.toNat - st.2.1.toNat)
                            (Inv := fun st m1 =>
                              let ui := st.1; let i := st.2.1; let si := st.2.2
                              i.toNat ≤ csz.toNat ∧ FailedStateOk c s si cut ∧
                              ui = (flIdxs s.core si.core.mrk s.core.trail_end).length ∧
                              (∀ q ∈ (fullArenaClauseLitsCore s.core cr32.toNat).take i.toNat,
                                (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
                                q ∈ flLits s.core si.core.mrk s.core.trail_end) ∧
                              (FullMem c si ⋆ R_hdr) m1) ?_ ?_
                          · intro Jl hJl; c0_hsteps
                            exact hJl (0, 0#32, s0) m ⟨Nat.zero_le _, hok0, by
                              rw [flIdxs_eq_nil_of_zero (fun j hj =>
                                hlm0.1 ((s.core.trl[j]?.getD 0#32).toNat / 2)
                                  (Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul
                                    (hw0.trail_lits_lt j hj)) hcv_le))]; rfl,
                              fun _ hq => by simp at hq, hm_s0⟩
                          · intro Jl ⟨ui, i, si⟩ m1 ⟨hi_le, hoki, hui_eq, hcovi, hm1⟩ ih_i
                            dsimp only at hi_le hoki hui_eq hcovi hm1 ih_i
                            rw [Blocks.get_here]; dsimp only
                            have hi_cv := hoki.len.core_ok
                            have har_i : si.core.arena = s.core.arena := by rw [hoki.core]
                            have hui_bd : ui ≤ s.core.cur_vars :=
                              Nat.le_trans (hui_eq ▸ flIdxs_length_le) (by omega)
                            c0_hsplit
                            · have hi_lt : i.toNat < csz.toNat := by
                                dsimp only [csz, cr32, s0]; assumption
                              have hi_csz :
                                  i.toNat < fullArenaClauseSizeCore s.core cr32.toNat := by
                                rw [← hcsz_eq]; exact hi_lt
                              obtain ⟨hlit_ar_lt, hlit_lits_len, hlit_get, hlit_mem0⟩ :=
                                p2_arena_clause_lit hlen0 hoki.len har_i rfl
                                  (hcr_to.symm ▸ hcsz_bd) hi_csz
                              let lit := si.core.arena[(cr32.setWidth 64 + 3#64 +
                                i.setWidth 64).toNat]'hlit_ar_lt
                              have hlit_ar_lt_c :
                                  (s0.core.confl_ref.toNat % 2 ^ 32 + 3 + i.toNat) % 2 ^ 64 <
                                    si.core.arena.length := by
                                change (cr32.toNat + 3 + i.toNat) % 2 ^ 64 < si.core.arena.length
                                simpa only [BitVec.toNat_add, fl_bv32_setWidth64,
                                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                                  Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 < 2 ^ 64)] using
                                  hlit_ar_lt
                              have hlit_hc : si.core.arena[(s0.core.confl_ref.toNat % 2 ^ 32 + 3 +
                                  i.toNat) % 2 ^ 64]'hlit_ar_lt_c = lit := by
                                dsimp only [lit, cr32]; congr 1
                                have hcr_lt64 : s0.core.confl_ref.toNat % 2 ^ 32 + 3 < 2 ^ 64 := by
                                  have := hcr_to; dsimp only [cr32] at this
                                  rw [BitVec.toNat_setWidth] at this; omega
                                try rw [BitVec.toNat_add, BitVec.toNat_add, fl_bv32_setWidth64,
                                  fl_bv32_setWidth64, BitVec.toNat_setWidth,
                                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                                  Nat.mod_eq_of_lt hcr_lt64]
                              have hlit_mem :
                                  lit.toNat ∈ fullArenaClauseLits s s.core.confl_ref.toNat := by
                                unfold fullArenaClauseLits; rw [← hcr_to]; exact hlit_mem0
                              have hlit_lt : lit.toNat < 2 * s.core.cur_vars :=
                                hw0.arena.lits_lt _ href hng _ hlit_mem
                              have hi1_bv : (i + 1#32).toNat = i.toNat + 1 :=
                                fl_bv32_add1_toNat (by omega)
                              c0_hsplit
                              · c0_hsteps
                                exact hJ1 (ui, true, i, si) m1
                                  ⟨hui_bd, hoki, (fun h => by cases h), hm1⟩
                              · have hlv_lt := Nat.div_lt_of_lt_mul hlit_lt
                                have hcv_si : si.core.cur_vars = s.core.cur_vars := by
                                  rw [hoki.core]
                                have hlv_lvl_lt : lit.toNat / 2 < si.core.lvl.length := by
                                  rw [hi_cv.lvl_len]
                                  exact Nat.lt_of_lt_of_le hlv_lt (hcv_si ▸ hcv_le)
                                have hlv_mrk_lt : lit.toNat / 2 < si.core.mrk.length := by
                                  rw [hi_cv.mrk_len]
                                  exact Nat.lt_of_lt_of_le hlv_lt (hcv_si ▸ hcv_le)
                                c0_hsplit
                                · exfalso
                                  have hcv64 :
                                                            s.core.cur_vars < 2 ^ 64 := by omega
                                  have hge : s.core.cur_vars % 2 ^ 64 ≤ lit.toNat / 2 := by
                                    rw [← hlit_hc]; assumption
                                  rw [Nat.mod_eq_of_lt hcv64] at hge; omega
                                · c0_hsteps_nogrp
                                  refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                                    (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                                    (Inv := fun st m2 =>
                                      let ui' := st.1; let si' := st.2
                                      FailedStateOk c s si' cut ∧
                                      ui' = (flIdxs s.core si'.core.mrk s.core.trail_end).length ∧
                                      (∀ q ∈ (fullArenaClauseLitsCore s.core cr32.toNat).take
                                          (i.toNat + 1),
                                        (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
                                        q ∈ flLits s.core si'.core.mrk s.core.trail_end) ∧
                                      (FullMem c si' ⋆ R_hdr) m2) ?_ ?_
                                  · intro Js_s' ⟨ui', si'⟩ m2 ⟨hok', hui', hcov', hm2⟩
                                    dsimp only at hok' hui' hcov' hm2
                                    rw [Blocks.get_here]; dsimp only
                                    c0_hsteps
                                    exact ih_i (ui', i + 1#32, si') m2 (by dsimp only; omega)
                                      ⟨by dsimp only; omega, hok', hui',
                                        by dsimp only; simpa only [hi1_bv] using hcov', hm2⟩
                                  · intro Js_s' hJs_s'
                                    have hlit_trail := (hw0.vals_false_iff _ hlit_lt).mp
                                      (hfals _ hlit_mem)
                                    c0_hsplit
                                    · c0_hsplit
                                      · have hmrk0_lv := fl_mark_zero_eq hoki hlv_lt
                                          (by simp only [← hlit_hc]; assumption)
                                        have hlvl_pos := p2_lvl_pos_of_lt hoki hlv_lvl_lt (by
                                          simp only [← hlit_hc, show (0#32 : BitVec 32).toNat =
                                            BitVec.toNat 0 from rfl]; assumption)
                                        have hlv_cl :
                                            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat =
                                            s.core.cur_level := by
                                          obtain ⟨ml, hml_te, hml_eq⟩ := hlit_trail
                                          have hle := hw0.lvl_le ml hml_te
                                          rw [hml_eq, fl_xor1_div2] at hle; omega
                                        obtain ⟨hmcl_lt, hmcl64, hmcl_ws, hmcl1_bv, hok2, hfl_len,
                                          hfl_pres, hlit_in⟩ := p2_push_step hw0 hcl1 hoki
                                          (Nat.le_refl _) hlit_lt hmrk0_lv hlvl_pos hlit_trail
                                          (hconfl2 _ hlit_mem hlv_cl)
                                        let s2 : FullState :=
                                          { core :=
                                              { si.core with
                                                mrk := si.core.mrk.set (lit.toNat / 2) 1#8,
                                                min_clr_len := si.core.min_clr_len + 1 },
                                            scratch :=
                                              { si.scratch with
                                                work_stk1 := si.scratch.work_stk1.set
                                                  si.core.min_clr_len (lit >>> 1) } }
                                        have hcovi2 :
                                            ∀ q ∈ (fullArenaClauseLitsCore s.core
                                              cr32.toNat).take i.toNat,
                                            (cnfOfClauses F_cur).EntailsClause
                                              (cnfClause [q ^^^ 1]) ∨
                                            q ∈ flLits s.core s2.core.mrk s.core.trail_end :=
                                          fun q hq =>
                                            (hcovi q hq).elim Or.inl fun hm =>
                                              Or.inr (hfl_pres q hm)
                                        have hcov2 := fl_take_succ_forall _ hlit_lits_len _ hcovi2
                                          (hlit_get ▸ hlit_in)
                                        c0_hsteps_nogrp
                                        refine wp_join_state (ts := []) (α := FullState)
                                          (proj := fun _ => ())
                                          (Inv := fun si' m2 => FailedStateOk c s si' cut ∧
                                            ui + 1 = (flIdxs s.core si'.core.mrk
                                              s.core.trail_end).length ∧
                                            (∀ q ∈ (fullArenaClauseLitsCore s.core
                                                cr32.toNat).take (i.toNat + 1),
                                              (cnfOfClauses F_cur).EntailsClause
                                                (cnfClause [q ^^^ 1]) ∨
                                              q ∈ flLits s.core si'.core.mrk s.core.trail_end) ∧
                                            (FullMem c si' ⋆ R_hdr) m2) ?_ ?_
                                        · intro Jinc si' m2 ⟨hok', hui', hcov', hm2⟩
                                          rw [Blocks.get_here]; dsimp only
                                          c0_hsteps; rw [p2_bv64_add1_eq (by omega)]
                                          exact hJs_s' (ui + 1, si') m2 ⟨hok', hui', hcov', hm2⟩
                                        · intro Jinc hJinc
                                          c0_hsplit
                                          · c0_hsteps
                                            have hm2' : (FullMem c s2 ⋆ R_hdr) m := by
                                              simpa only [s2, lit, cr32,
                                                show (3 : BitVec 64) = 3#64 from rfl,
                                                fl_bv32_setWidth64, bv32_lshr_1,
                                                bv64_ofNat_toNat hmcl64, hmcl1_bv,
                                                show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
                                            exact hJinc s2 m
                                              ⟨hok2, by rw [hui_eq, hfl_len], hcov2, hm2'⟩
                                          · exfalso
                                            have hge : ¬ si.core.min_clr_len % 2 ^ 64 <
                                                s.core.cur_vars % 2 ^ 64 := by assumption
                                            rw [Nat.mod_eq_of_lt hmcl64, Nat.mod_eq_of_lt
                                              (by omega : s.core.cur_vars < 2 ^ 64)] at hge
                                            omega
                                      · have hmrk_nz := fl_mark_nz_eq hoki hlv_lt
                                          (by simp only [← hlit_hc]; assumption)
                                        have hlit_in := fl_mark_lit_skip (q := lit.toNat) hw0 hcl1
                                          (Nat.le_refl _) (fun _ => hlit_trail)
                                          (fun _ => ⟨hmrk_nz, hlit_trail⟩)
                                        have hcov2 := fl_take_succ_forall _ hlit_lits_len _ hcovi
                                          (hlit_get ▸ hlit_in)
                                        c0_hsteps
                                        exact hJs_s' (ui, si) m1 ⟨hoki, hui_eq, hcov2, hm1⟩
                                    · have hlvl0 := p2_lvl0_of_nlt hoki hlv_lvl_lt (by
                                        simp only [← hlit_hc, show (0#32 : BitVec 32).toNat =
                                          BitVec.toNat 0 from rfl]; assumption)
                                      have hlit_in := fl_mark_lit_skip (s1 := si) (q := lit.toNat)
                                        hw0 hcl1 (Nat.le_refl _) (fun _ => hlit_trail)
                                        (fun hp => by omega)
                                      have hcov2 := fl_take_succ_forall _ hlit_lits_len _ hcovi
                                        (hlit_get ▸ hlit_in)
                                      c0_hsteps
                                      exact hJs_s' (ui, si) m1 ⟨hoki, hui_eq, hcov2, hm1⟩
                            · have hcsz_lt_c :
                                  (s0.core.confl_ref.toNat % 2 ^ 32 + 2) % 2 ^ 64 <
                                    s0.core.arena.length := by
                                change (cr32.toNat + 2) % 2 ^ 64 < s0.core.arena.length
                                simpa only [BitVec.toNat_add, fl_bv32_setWidth64,
                                  show (2#64 : BitVec 64).toNat = 2 from rfl,
                                  Nat.mod_eq_of_lt (by omega : cr32.toNat + 2 < 2 ^ 64)] using
                                  hcr_add2_lt
                              have hcsz_hc : s0.core.arena[(s0.core.confl_ref.toNat % 2 ^ 32 + 2) %
                                  2 ^ 64]'hcsz_lt_c = csz := by
                                dsimp only [csz, cr32]; congr 1
                              have hi_nge : ¬ i.toNat < csz.toNat := by rw [← hcsz_hc]; assumption
                              have hi_eq : i.toNat = csz.toNat := by omega
                              have htake_all :
                                  (fullArenaClauseLitsCore s.core cr32.toNat).take i.toNat =
                                  fullArenaClauseLitsCore s.core cr32.toNat := by
                                rw [hi_eq, hcr_to, ← hcsz_lits_len]; exact List.take_length
                              rw [htake_all] at hcovi
                              have hent_sd : (cnfOfClauses F_cur).EntailsClause
                                  (cnfClause (flLits s.core si.core.mrk s.core.trail_end)) := by
                                refine fl_entails_of_clause ?_ hcovi
                                rw [hcr_to]; exact hw0.arena.entails _ href hng
                              c0_hsteps
                              exact hJ1 (ui, false, i, si) m1
                                ⟨hui_bd, hoki, fun _ => ⟨hui_eq, hent_sd⟩, hm1⟩

end LeanQbe.T.Examples.Kissat.FullM8FidV12
