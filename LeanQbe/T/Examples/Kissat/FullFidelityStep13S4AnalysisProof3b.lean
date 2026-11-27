/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof3a
import LeanQbe.T.Examples.Kissat.FullMinLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-B Proof 3b (`full_min_shrink_m6` Main Theorem)

UNSAT-only, callee-parametric `Func.wp` proof (`public section`, `0` `@[expose]` on theorems,
`0` `import all`, `XPost`-polymorphic) for Step-13 `fidStep13S4MinShrinkM6Fn`
(`full_min_shrink_m6`) against `step13MinShrinkSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  FullMinMarkInv fullMinMarkCore fullMinMarkState fullMinMarkSpec
  fullMinLitSpec fullShrinkLowerSpec fullShrinkBlkSpec fullMinShrinkSpec
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

private theorem is_wp_let {Γ rs Q X ts} {op : Op Val ts} {k : Tup Val ts → Expr Val Cont rs}
    {m : Mem 64} (h : wp Γ Q X (.let_ op k) m) : wp Γ Q X (.let_ op k) m := h
local macro "s13_lets" : tactic => `(tactic| repeat (apply is_wp_let; c0_hstep))

/-! ## 1. Block-Shrink True (`ana_s[res_sz++] = uip_v`) & DFS-Fallback Phase Helpers -/

private def s13MinShrinkTrueExpr {V : Ty → Type} {C : List Ty → Type}
    (p cv pTmp beg : V i64) (K : Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .let_ (op64 (.add i64) (.var p) (.imm 848)) fun p49 =>
  .load i64 (.var p49.fst) fun ana_s =>
  .let_ (op64 (.mul i64) (.var beg) (.imm 4)) fun o51 =>
  .let_ (op64 (.add i64) (.var pTmp) (.var o51.fst)) fun a52 =>
  .load i32 (.var a52.fst) fun lit53 =>
  .let_ (Op.mk (.lshr i32) (.var lit53, .imm 1, ())) fun uip_v =>
  .group (sig := [[]]) (fun _ => .cons (fun _ => K) .nil) fun J55 =>
  .let_ (Op.mk (.zext 32 64) (.var uip_v.fst, ())) fun zuip =>
  .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var zuip.fst, .var cv, ())) fun b57 =>
  .jnz (.var b57.fst)
    (.let_ (op64 (.add i64) (.var p) (.imm 1144)) fun p58 =>
     .load i64 (.var p58.fst) fun rsz1 =>
     .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var rsz1, .var cv, ())) fun b60 =>
     .jnz (.var b60.fst)
       (.let_ (op64 (.add i64) (.var p) (.imm 1144)) fun p61 =>
        .load i64 (.var p61.fst) fun rsz2 =>
        .let_ (op64 (.mul i64) (.var rsz2) (.imm 4)) fun o63 =>
        .let_ (op64 (.add i64) (.var ana_s) (.var o63.fst)) fun a64 =>
        .store (.var uip_v.fst) (.var a64.fst)
          (.let_ (op64 (.add i64) (.var p) (.imm 1144)) fun p65 =>
           .load i64 (.var p65.fst) fun rsz3 =>
           .let_ (op64 (.add i64) (.var rsz3) (.imm 1)) fun rsz4 =>
           .let_ (op64 (.add i64) (.var p) (.imm 1144)) fun p68 =>
           .store (.var rsz4.fst) (.var p68.fst) (.jump J55.fst ())))
       (.jump J55.fst ()))
    (.jump J55.fst ())

private def s13MinDfsFallbackExpr {V : Ty → Type} {C : List Ty → Type}
    (p pTmp beg end_b : V i64) (K : Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Js_3 => .cons (fun p_55 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_55.fst, .var end_b, ())) fun p_56 =>
    .jnz (.var p_56.fst)
      (.group (sig := [[]]) (fun _ => .cons (fun _ =>
         .let_ (op64 (.add i64) (.var p_55.fst) (.imm 1)) fun p =>
         .jump Js_3.fst (.var p.fst, ())) .nil) fun Js =>
       .let_ (op64 (.mul i64) (.var p_55.fst) (.imm 4)) fun p_57 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p_57.fst)) fun p_58 =>
       .load i32 (.var p_58.fst) fun ld =>
       .call "full_min_lit_dfs_m8" (as := [i64, i32, .bool, .bool]) (bs := [.bool])
         (.var p, .var ld, .imm false, .imm false, ()) fun p =>
       .jnz (.var p.fst)
         (.let_ (op64 (.mul i64) (.var p_55.fst) (.imm 4)) fun p =>
          .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
          .store (t := i32) (.imm 4294967295) (.var p.fst) (.jump Js.fst ()))
         (.jump Js.fst ()))
      K) .nil)
    fun Js => .jump Js.fst (.var beg, ())

private theorem s13_min_shrink_true_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s_c1 st_s : FullState} {tlen : Nat} {beg end_b : Val i64} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {K : Expr Val Cont []} {m_s : Mem 64}
    (hinv : S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat st_s)
    (hbeg_lt : beg.toNat < tlen) (ht_cv : tlen ≤ s.core.cur_vars)
    (hm_s : (FullMem c st_s ⋆ R) m_s)
    (hK : ∀ ws1' resSz' mf,
      let st' : FullState :=
        { st_s with scratch := { st_s.scratch with work_stk1 := ws1', res_sz := resSz' } }
      S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat st' →
      (FullMem c st' ⋆ R) mf → wp Γ Q X K mf) :
    wp Γ Q X (s13MinShrinkTrueExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pTmp beg K) m_s := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hinv.core.1.core_ok.cur_vars_le; rw [hinv.cv_eq] at hcv
  have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    Nat.mod_eq_of_lt (by omega)
  have hbg_arr : beg.toNat < st_s.core.tmp.length := by
    rw [hinv.core.1.core_ok.tmp_len_arr]; omega
  dsimp only [s13MinShrinkTrueExpr]
  ml_ld load_full_work_stk1_ptr (s := st_s) hm_s
  ml_ld c0_load_full_tmp (s := st_s) (i := beg) hbg_arr hm_s
  s13_lets
  refine wp_join_group (ts := []) (fun _ mf =>
      ∃ ws1' resSz',
        let st' : FullState :=
          { st_s with scratch := { st_s.scratch with work_stk1 := ws1', res_sz := resSz' } }
        S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat st' ∧ (FullMem c st' ⋆ R) mf)
    (fun _ ⟨⟩ mf ⟨ws1', resSz', hinv', hmf⟩ => by
      rw [Blocks.get_here]; exact hK ws1' resSz' mf hinv' hmf) ?_
  rintro J55 hJ55; s13_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
  · ml_ld load_full_res_sz (s := st_s) hm_s; s13_lets; ml_jnz; refine ⟨fun hrsz => ?_, fun _ => ?_⟩
    · have hrsz_lt : st_s.scratch.res_sz.toNat < s.core.cur_vars := by
        rw [BitVec.ult, decide_eq_true_eq, hcv_bv] at hrsz; exact hrsz
      have hrsz_arr : st_s.scratch.res_sz.toNat < st_s.scratch.work_stk1.length := by
        rw [hinv.core.1.scratch_ok.work_stk1_len]; omega
      ml_ld load_full_res_sz (s := st_s) hm_s; s13_lets
      ml_st m1, hm1 := c0_store_full_work_stk1 (s := st_s) (i := st_s.scratch.res_sz)
        (st_s.core.tmp[beg.toNat]'hbg_arr >>> 1) hrsz_arr hm_s
      let ws1' := st_s.scratch.work_stk1.set st_s.scratch.res_sz.toNat
        (st_s.core.tmp[beg.toNat]'hbg_arr >>> 1)
      let st1 : FullState := { st_s with scratch := { st_s.scratch with work_stk1 := ws1' } }
      ml_ld load_full_res_sz (s := st1) hm1; s13_lets
      ml_st m2, hm2 := store_full_res_sz (s := st1) (st_s.scratch.res_sz + 1) hm1
      let st2 : FullState :=
        { st_s with scratch := { st_s.scratch with work_stk1 := ws1',
                                                   res_sz := st_s.scratch.res_sz + 1 } }
      have hcore2 : FullOtfsCoreInv c F0 st2 :=
        ⟨⟨hinv.core.1.core_ok, { hinv.core.1.scratch_ok with
            work_stk1_len := by dsimp only [st2, ws1']; rw [List.length_set,
              hinv.core.1.scratch_ok.work_stk1_len] }⟩, hinv.core.2⟩
      have hinv2 : S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat st2 :=
        ⟨hcore2, hinv.min_inv, hinv.entails, hinv.nodup, hinv.mrk_above, hinv.no8, hinv.cv_eq,
         hinv.tl_eq, hinv.lvl_eq, hinv.vals_eq, hinv.clvl_eq, hinv.tpos_eq, hinv.zero_eq,
         hinv.tail_eq, hinv.beg_bnd, hinv.rem_mrk, hinv.post_lvls⟩
      exact hJ55 () m2 ⟨ws1', st_s.scratch.res_sz + 1, hinv2, hm2⟩
    · exact hJ55 () m_s ⟨st_s.scratch.work_stk1, st_s.scratch.res_sz, hinv, hm_s⟩
  · exact hJ55 () m_s ⟨st_s.scratch.work_stk1, st_s.scratch.res_sz, hinv, hm_s⟩

private theorem s13_min_dfs_fallback_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s_c1 : FullState} {tlen : Nat} {beg end_b : Val i64}
    {mrk_s : List (BitVec 8)} {tmp_s mclr_s sstk_s wsort_s ws1_s : List (BitVec 32)}
    {mcl_s : Nat} {mcf_s ticks_s resSz_s : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} {K : Expr Val Cont []} {m_s : Mem 64}
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hbeg_1 : 1 ≤ beg.toNat) (hbeg_end : beg.toNat < end_b.toNat) (hend_tl : end_b.toNat ≤ tlen)
    (ht_cv : tlen ≤ s.core.cur_vars)
    (hc1_ne : ∀ k < tlen, s_c1.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hc1_lvls : ∀ k, 1 ≤ k → k < tlen →
      let lv := (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    (htmp_s_tail : ∀ k, beg.toNat ≤ k → k < tlen → tmp_s[k]? = s_c1.core.tmp[k]?)
    (hinv_s : S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat
      (s13BlkState s_c1 tmp_s mrk_s mclr_s sstk_s wsort_s ws1_s mcl_s mcf_s ticks_s resSz_s))
    (hm_s : (FullMem c
      (s13BlkState s_c1 tmp_s mrk_s mclr_s sstk_s wsort_s ws1_s mcl_s mcf_s ticks_s resSz_s) ⋆ R)
      m_s)
    (hK : ∀ mrk_d tmp_d mclr_d wsort_d mcl_d mcf_d ticks_d md,
      let cur_d :=
        s13BlkState s_c1 tmp_d mrk_d mclr_d sstk_s wsort_d ws1_s mcl_d mcf_d ticks_d resSz_s
      S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_d →
      (FullMem c cur_d ⋆ R) md → wp Γ Q X K md) :
    wp Γ Q X (s13MinDfsFallbackExpr c.hdr c.pTmp beg end_b K) m_s := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hinv_s.core.1.core_ok.cur_vars_le; rw [hinv_s.cv_eq] at hcv
  dsimp only [s13MinDfsFallbackExpr]
  refine wp_loop_group (ts := [i64]) (fun n_d (mk2, ()) md =>
      n_d = end_b.toNat - mk2.toNat ∧ beg.toNat ≤ mk2.toNat ∧ mk2.toNat ≤ end_b.toNat ∧
      ∃ (mrk_d : List (BitVec 8)) (tmp_d mclr_d wsort_d : List (BitVec 32))
        (mcl_d : Nat) (mcf_d ticks_d : BitVec 64),
        let cur_d :=
          s13BlkState s_c1 tmp_d mrk_d mclr_d sstk_s wsort_d ws1_s mcl_d mcf_d ticks_d resSz_s
        S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_d ∧
        (∀ k, beg.toNat ≤ k → k < end_b.toNat → mk2.toNat ≤ k →
          cur_d.core.tmp[k]? = tmp_s[k]?) ∧
        (FullMem c cur_d ⋆ R) md) ?_
    (fun Js_3 hJs_3 => by
      s13_lets; exact hJs_3 (end_b.toNat - beg.toNat) (beg, ()) m_s
        ⟨rfl, le_refl _, le_of_lt hbeg_end, mrk_s, tmp_s, mclr_s, wsort_s,
          mcl_s, mcf_s, ticks_s, hinv_s, fun _ _ _ _ => rfl, hm_s⟩)
  rintro Js_3 n_d ⟨mk2, ⟨⟩⟩ md hJs_3 ⟨rfl, hmk2_lb, hmk2_ub, mrk_d, tmp_d, mclr_d,
    wsort_d, mcl_d, mcf_d, ticks_d, hd, hd_tail, hm_d⟩
  let cur_d :=
    s13BlkState s_c1 tmp_d mrk_d mclr_d sstk_s wsort_d ws1_s mcl_d mcf_d ticks_d resSz_s
  rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hmk2_lt => ?_, fun _ => ?_⟩
  · c0_cond hmk2_lt
    have hmk2_t : mk2.toNat < tlen := Nat.lt_of_lt_of_le hmk2_lt hend_tl
    have hmk2_tl : mk2.toNat < cur_d.core.tmp.length := by
      dsimp only [cur_d]; rw [hd.core.1.core_ok.tmp_len_arr]; omega
    have hmk2_1 : (mk2 + 1).toNat = mk2.toNat + 1 := min_bv64_add1 (by omega)
    refine wp_join_group (ts := []) (fun _ md_n =>
        ∃ (mrk_n : List (BitVec 8)) (tmp_n mclr_n wsort_n : List (BitVec 32))
          (mcl_n : Nat) (mcf_n ticks_n : BitVec 64),
          let cur_n :=
            s13BlkState s_c1 tmp_n mrk_n mclr_n sstk_s wsort_n ws1_s mcl_n mcf_n ticks_n resSz_s
          S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_n ∧
          (∀ k, beg.toNat ≤ k → k < end_b.toNat → mk2.toNat + 1 ≤ k →
            cur_n.core.tmp[k]? = tmp_s[k]?) ∧
          (FullMem c cur_n ⋆ R) md_n)
      (fun _ ⟨⟩ md_n ⟨mrk_n, tmp_n, mclr_n, wsort_n, mcl_n, mcf_n, ticks_n,
          hn, hnt, hm_n⟩ => by
        rw [Blocks.get_here]; s13_lets
        exact hJs_3 (end_b.toNat - (mk2 + 1).toNat) (mk2 + 1, ()) md_n (by omega)
          ⟨rfl, by rw [hmk2_1]; omega, by rw [hmk2_1]; omega,
            mrk_n, tmp_n, mclr_n, wsort_n, mcl_n, mcf_n, ticks_n, hn,
            by simpa only [hmk2_1] using hnt, hm_n⟩) ?_
    rintro Jnext hJnext
    ml_ld c0_load_full_tmp (s := cur_d) (i := mk2) hmk2_tl hm_d
    let root_lit := cur_d.core.tmp[mk2.toNat]'hmk2_tl
    have hrl_eq : cur_d.core.tmp[mk2.toNat]? = some root_lit := List.getElem?_eq_getElem hmk2_tl
    have hrl_orig : cur_d.core.tmp[mk2.toNat]? = s_c1.core.tmp[mk2.toNat]? := by
      rw [hd_tail mk2.toNat hmk2_lb hmk2_lt (le_refl _)]; exact htmp_s_tail mk2.toNat hmk2_lb hmk2_t
    have hrl_ne : root_lit ≠ 0xFFFFFFFF#32 := by
      have := hc1_ne mk2.toNat hmk2_t; rwa [← hrl_orig, hrl_eq, Option.getD_some] at this
    have hrl_rm := hd.rem_mrk mk2.toNat hmk2_t (by rwa [hrl_eq, Option.getD_some])
    rw [hrl_eq, Option.getD_some] at hrl_rm
    have hrl_lvl :
        (cur_d.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < cur_d.core.cur_level := by
      rw [hd.lvl_eq, hd.clvl_eq]
      have hrn : root_lit.toNat = (s_c1.core.tmp[mk2.toNat]?.getD 0#32).toNat := by
        rw [← hrl_orig, hrl_eq, Option.getD_some]
      rw [hrn]; exact (hc1_lvls mk2.toNat (by omega) hmk2_t).2
    s13_lets; apply wp_call_of_spec; apply hDfs; dsimp only [vals, Arg.val]
    refine m8MinLitDfsSpec_of hd.core (m8_toFullMinInv hd.min_inv)
      (by rw [hd.cv_eq]; exact hrl_rm.1) (by rw [hd.vals_eq]; exact hrl_rm.2.1) hrl_lvl
      (fun v hv _ => hd.no8 v (hd.cv_eq ▸ hv)) hm_d ?_
    intro ok_d mrk_n wsort_n mclr_n mcl_n mcf_n ticks_n m_dn _s_dn
      hlen_dn hab_dn hmono2_dn hbit8_dn hmin_df hok_dn hm_dn
    have hmin_dn := m8_toSpecsMinInv hmin_df
    have hok_dn' : ok_d = true →
        (∀ keep', (∀ l ∈ (((cur_d.core.tmp.take tlen).filter
              (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep') →
          FullMinMarkInv (m8MinLitDfsState cur_d mrk_n wsort_n mclr_n
            mcl_n mcf_n ticks_n).core keep') ∧
        FullMinMarkInv (fullMinMarkCore (m8MinLitDfsState cur_d mrk_n wsort_n mclr_n
            mcl_n mcf_n ticks_n).core (root_lit.toNat / 2) 2#8)
          (((cur_d.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) :=
      fun h => let ⟨h1, h2⟩ := hok_dn h
        ⟨fun keep' hs => m8_toSpecsMinInv (h1 keep' hs), m8_toSpecsMinInv h2⟩
    obtain ⟨hcore_n, hmin_n, hent_n, hnd_n, hab_n, hno8_n, hrem_n, _⟩ :=
      s13MinLitStepState hmk2_t (by rw [hd.cv_eq]; exact ht_cv) hd.core
        hd.min_inv hd.entails hd.nodup
        (fun v hv => hd.mrk_above v (hd.cv_eq ▸ hv))
        (fun v hv => hd.no8 v (hd.cv_eq ▸ hv))
        (fun k hk hne => by
          have h := hd.rem_mrk k hk hne; rw [← hd.cv_eq, ← hd.vals_eq] at h; exact h)
        hrl_eq hrl_ne hlen_dn hab_dn hmono2_dn hbit8_dn hmin_dn hok_dn'
    let tmp_n := if ok_d then cur_d.core.tmp.set mk2.toNat 0xFFFFFFFF#32 else cur_d.core.tmp
    let cur_n : FullState :=
      s13BlkState s_c1 tmp_n mrk_n mclr_n sstk_s wsort_n ws1_s mcl_n mcf_n ticks_n resSz_s
    have hcur_n_eq : cur_n = s13BlkState cur_d tmp_n mrk_n mclr_n cur_d.scratch.shrink_stk wsort_n
        cur_d.scratch.work_stk1 mcl_n mcf_n ticks_n cur_d.scratch.res_sz := rfl
    have hzero_n : cur_n.core.tmp[0]? = s_c1.core.tmp[0]? := by
      rw [← hd.zero_eq]; dsimp only [cur_n, s13BlkState, tmp_n]
      cases ok_d <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rfl
      · exact List.getElem?_set_ne (by omega)
    have htail_n : ∀ k, end_b.toNat ≤ k → k < tlen → cur_n.core.tmp[k]? = s_c1.core.tmp[k]? :=
      fun k hk1 hk2 => by
        dsimp only [cur_n, s13BlkState, tmp_n]
        have hdt := hd.tail_eq k hk1 hk2
        cases ok_d <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact hdt
        · rw [List.getElem?_set_ne (by omega)]; exact hdt
    have hinv_n : S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_n :=
      ⟨hcur_n_eq ▸ hcore_n, hcur_n_eq ▸ hmin_n,
        fun F_cur hw hEnt0 => hcur_n_eq ▸ hent_n F_cur hw hEnt0,
        fun hnd0 hne0 => hcur_n_eq ▸ hnd_n hnd0 hne0,
        fun v hv => hcur_n_eq ▸ hab_n v (hd.cv_eq ▸ hv),
        fun v hv => hcur_n_eq ▸ hno8_n v (hd.cv_eq ▸ hv),
        hd.cv_eq, hd.tl_eq, hd.lvl_eq, hd.vals_eq, hd.clvl_eq, hd.tpos_eq,
        hzero_n, htail_n, hd.beg_bnd, fun k hk hne => by
          have hr := hrem_n k hk hne
          have hcv_c : cur_d.core.cur_vars = s.core.cur_vars := hd.cv_eq
          have hvals_c : cur_d.core.vals = s.core.vals := hd.vals_eq
          dsimp only [cur_n, s13BlkState, tmp_n] at hr ⊢
          rw [hcv_c, hvals_c] at hr; exact hr,
        fun k hk1 hk2 hne => by
          dsimp only [cur_n, s13BlkState, tmp_n] at hne ⊢
          cases ok_d <;> simp only [Bool.false_eq_true, ↓reduceIte] at hne ⊢
          · exact hd.post_lvls k hk1 hk2 hne
          · by_cases hkm : k = mk2.toNat
            · subst k; exfalso; apply hne; rw [List.getElem?_set_self hmk2_tl]; rfl
            · rw [List.getElem?_set_ne (Ne.symm hkm)] at hne ⊢; exact hd.post_lvls k hk1 hk2 hne⟩
    have hnt : ∀ k, beg.toNat ≤ k → k < end_b.toNat → mk2.toNat + 1 ≤ k →
        cur_n.core.tmp[k]? = tmp_s[k]? := fun k hk1 hk2 hk3 => by
      have hdt := hd_tail k hk1 hk2 (by omega)
      dsimp only [cur_n, s13BlkState, tmp_n]
      cases ok_d <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact hdt
      · rw [List.getElem?_set_ne (by omega)]; exact hdt
    s13_lets; ml_jnz; refine ⟨fun hok_t => ?_, fun hok_f => ?_⟩
    · have hok_d : ok_d = true := by c0_cond hok_t; exact hok_t
      ml_st md_n, hmd_n := c0_store_full_tmp (s := m8MinLitDfsState cur_d mrk_n wsort_n
        mclr_n mcl_n mcf_n ticks_n) (i := mk2) 0xFFFFFFFF#32 hmk2_tl hm_dn
      have hmd_n' : (FullMem c cur_n ⋆ R) md_n := by
        dsimp only [cur_n, s13BlkState, m8MinLitDfsState, tmp_n] at hmd_n ⊢
        rw [hok_d]; simp only [↓reduceIte] at hmd_n ⊢; exact hmd_n
      exact hJnext () md_n
        ⟨mrk_n, tmp_n, mclr_n, wsort_n, mcl_n, mcf_n, ticks_n, hinv_n, hnt, hmd_n'⟩
    · have hok_d : ok_d = false := by c0_cond hok_f; exact hok_f
      have hmd_n' : (FullMem c cur_n ⋆ R) m_dn := by
        dsimp only [cur_n, s13BlkState, m8MinLitDfsState, tmp_n] at hm_dn ⊢
        rw [hok_d]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hm_dn
      exact hJnext () m_dn
        ⟨mrk_n, tmp_n, mclr_n, wsort_n, mcl_n, mcf_n, ticks_n, hinv_n, hnt, hmd_n'⟩
  · exact hK mrk_d tmp_d mclr_d wsort_d mcl_d mcf_d ticks_d md hd hm_d

/-! ## 2. Block-Loop AST & WP (`s13MinBlkLoopExpr`, `s13_min_shrink_blk_loop_wp`) -/

private def s13MinBlkLoopExpr {V : Ty → Type} {C : List Ty → Type}
    (p cv orig_tlen pTmp pLvl pTpos tlen : V i64) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Js => .cons (fun p_34 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_34.fst, .var tlen, ())) fun p_35 =>
    .jnz (.var p_35.fst)
      (.let_ (op64 (.mul i64) (.var p_34.fst) (.imm 4)) fun p_36 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p_36.fst)) fun p_37 =>
       .load i32 (.var p_37.fst) fun ld =>
       .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun p_38 =>
       .let_ (Op.mk (.zext 32 64) (.var p_38.fst, ())) fun p_39 =>
       .let_ (op64 (.mul i64) (.var p_39.fst) (.imm 4)) fun p_40 =>
       .let_ (op64 (.add i64) (.var pLvl) (.var p_40.fst)) fun p_41 =>
       .load i32 (.var p_41.fst) fun ld =>
       .let_ (op64 (.mul i64) (.var p_34.fst) (.imm 4)) fun p_42 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p_42.fst)) fun p_43 =>
       .load i32 (.var p_43.fst) fun ld_9 =>
       .let_ (Op.mk (.lshr i32) (.var ld_9, .imm 1, ())) fun p_44 =>
       .let_ (Op.mk (.zext 32 64) (.var p_44.fst, ())) fun p_45 =>
       .let_ (op64 (.mul i64) (.var p_45.fst) (.imm 4)) fun p_46 =>
       .let_ (op64 (.add i64) (.var pTpos) (.var p_46.fst)) fun p_47 =>
       .load i32 (.var p_47.fst) fun ld_10 =>
       .let_ (Op.mk (.zext 32 64) (.var ld_10, ())) fun p_48 =>
       .let_ (op64 (.add i64) (.var p_34.fst) (.imm 1)) fun p_49 =>
       .group (sig := [[i64, i64]]) (fun Js_1 => .cons (fun p_50 =>
         .group (sig := [[]]) (fun _ => .cons (fun _ =>
           .group (sig := [[]]) (fun _ => .cons (fun _ =>
             .jump Js.fst (.var p_50.snd.fst, ())) .nil) fun Js =>
           .let_ (op64 (.sub i64) (.var p_50.snd.fst) (.var p_34.fst)) fun p_52 =>
           .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var p_52.fst, .imm 2, ())) fun p_53 =>
           .jnz (.var p_53.fst)
             (.group (sig := [[]]) (fun _ => .cons (fun _ => .jump Js.fst ()) .nil) fun Js =>
              .call "full_shrink_blk_bool_m8" (as := [i64, i64, i64, i32, i64]) (bs := [.bool])
                (.var p, .var p_34.fst, .var p_50.snd.fst, .var ld, .var p_50.fst, ())
                fun p_54 =>
              .jnz (.var p_54.fst)
                (s13MinShrinkTrueExpr p cv pTmp p_34.fst (.jump Js.fst ()))
                (s13MinDfsFallbackExpr p pTmp p_34.fst p_50.snd.fst (.jump Js.fst ())))
             (.jump Js.fst ())) .nil) fun Js =>
         .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_50.snd.fst, .var tlen, ())) fun p =>
         .jnz (.var p.fst)
           (.let_ (op64 (.mul i64) (.var p_50.snd.fst) (.imm 4)) fun p =>
            .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
            .load i32 (.var p.fst) fun ld_11 =>
            .let_ (Op.mk (.lshr i32) (.var ld_11, .imm 1, ())) fun p =>
            .let_ (Op.mk (.zext 32 64) (.var p.fst, ())) fun p =>
            .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
            .let_ (op64 (.add i64) (.var pLvl) (.var p.fst)) fun p =>
            .load i32 (.var p.fst) fun ld_12 =>
            .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld_12, .var ld, ())) fun p =>
            .jnz (.var p.fst)
              (.let_ (op64 (.mul i64) (.var p_50.snd.fst) (.imm 4)) fun p =>
               .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
               .load i32 (.var p.fst) fun ld =>
               .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun p =>
               .let_ (Op.mk (.zext 32 64) (.var p.fst, ())) fun p =>
               .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
               .let_ (op64 (.add i64) (.var pTpos) (.var p.fst)) fun p =>
               .load i32 (.var p.fst) fun ld =>
               .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p =>
               .group (sig := [[i64]]) (fun _ => .cons (fun p =>
                 .let_ (op64 (.add i64) (.var p_50.snd.fst) (.imm 1)) fun p_51 =>
                 .jump Js_1.fst (.var p.fst, .var p_51.fst, ())) .nil) fun Js =>
               .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var p.fst, .var p_50.fst, ())) fun p_51 =>
               .jnz (.var p_51.fst) (.jump Js.fst (.var p.fst, ()))
                 (.jump Js.fst (.var p_50.fst, ())))
              (.jump Js.fst ()))
           (.jump Js.fst ())) .nil)
         fun Js => .jump Js.fst (.var p_48.fst, .var p_49.fst, ()))
      (s13MinCompactLoopExpr tlen pTmp fun keep =>
        .let_ (op64 (.add i64) (.var p) (.imm 72)) fun p_38 =>
        .load i64 (.var p_38.fst) fun ld_9 =>
        s13MinCleanExpr p cv orig_tlen pTmp pLvl ld_9 keep)) .nil)
    fun Js => .jump Js.fst (.imm 1, ())

private theorem s13_min_shrink_blk_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s_c1 : FullState} {tlen : Nat} {tlen_bv : BitVec 64} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost}
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X)
    (htlen_eq : tlen_bv.toNat = tlen) (ht1 : 1 ≤ tlen) (ht_cv : tlen ≤ s.core.cur_vars)
    (ht_tl : tlen ≤ s.core.tmp_len)
    (hc1_inv : S13BlkLoopInv c F0 s s_c1 tlen 1 s_c1)
    (hc1_0eq : s_c1.core.tmp[0]? = s.core.tmp[0]?)
    (hc1_0ne : s_c1.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hc1_0lv : (s.core.lvl[(s_c1.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      s.core.cur_level)
    (hc1_ne : ∀ k < tlen, s_c1.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hc1_lvls : ∀ k, 1 ≤ k → k < tlen →
      let lv := (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    (hc1_sort : ∀ i j, 1 ≤ i → i ≤ j → j < tlen →
      (s.core.lvl[(s_c1.core.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s_c1.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {m : Mem 64} (hm_in : (FullMem c s_c1 ⋆ R) m)
    (hpost : ∀ (tmp' : List (BitVec 32)) (tl' : Nat) (mrk' : List (BitVec 8))
        (mclr' sstk' wsort' ws1' : List (BitVec 32)) (mcl' : Nat)
        (mcf' llits' mrem' ticks' resSz' : BitVec 64) (m' : Mem 64),
      let s' := step13MinShrinkState s_c1 tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf'
        s_c1.scratch.conflicts llits' mrem' ticks' resSz'
      tmp'.length = c.max_vars → mrk'.length = c.max_vars → mclr'.length = c.max_vars →
      mcl' ≤ c.max_vars → sstk'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      ws1'.length = 2 * c.max_vars →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) → FullMarksClear s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      (((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
        (∀ k, 1 ≤ k → k < s.core.tmp_len →
          (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
          (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup) →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
        lv < s.core.cur_level) →
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (s13MinBlkLoopExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      tlen_bv c.pTmp c.pLevel c.pTrailPos tlen_bv) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hc1_inv.core.1.core_ok.cur_vars_le; rw [hc1_inv.cv_eq] at hcv
  have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
  dsimp only [s13MinBlkLoopExpr]
  refine wp_loop_group (ts := [i64]) (fun n (beg, ()) mb =>
      n = tlen - beg.toNat ∧ 1 ≤ beg.toNat ∧ beg.toNat ≤ tlen ∧
      ∃ (mrk_b : List (BitVec 8)) (tmp_b mclr_b sstk_b wsort_b ws1_b : List (BitVec 32))
        (mcl_b : Nat) (mcf_b ticks_b resSz_b : BitVec 64),
      let cur :=
        s13BlkState s_c1 tmp_b mrk_b mclr_b sstk_b wsort_b ws1_b mcl_b mcf_b ticks_b resSz_b
      S13BlkLoopInv c F0 s s_c1 tlen beg.toNat cur ∧ (FullMem c cur ⋆ R) mb) ?_
    (fun Js hJs => by
      s13_lets; exact hJs (tlen - 1) (1#64, ()) m
        ⟨by rw [h1v], by rw [h1v]; exact le_refl _, by rw [h1v]; exact ht1,
         s_c1.core.mrk, s_c1.core.tmp, s_c1.core.min_clr, s_c1.scratch.shrink_stk,
         s_c1.scratch.wsort, s_c1.scratch.work_stk1, s_c1.core.min_clr_len, s_c1.core.min_clr_full,
         s_c1.scratch.search_ticks, s_c1.scratch.res_sz, by rw [h1v]; exact hc1_inv, hm_in⟩)
  rintro Js n ⟨beg, ⟨⟩⟩ mb hJs
    ⟨rfl, hbeg1, hbeg_tl, mrk_b, tmp_b, mclr_b, sstk_b, wsort_b, ws1_b, mcl_b, mcf_b, ticks_b,
      resSz_b, hb, hm_b⟩
  let cur := s13BlkState s_c1 tmp_b mrk_b mclr_b sstk_b wsort_b ws1_b mcl_b mcf_b ticks_b resSz_b
  rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have hbx : beg.toNat < tlen := by
      rw [BitVec.ult, decide_eq_true_eq, htlen_eq] at hlt; exact hlt
    have hbg_tl : beg.toNat < cur.core.tmp.length := by
      dsimp only [cur]; rw [hb.core.1.core_ok.tmp_len_arr]; omega
    ml_ld c0_load_full_tmp (s := cur) (i := beg) hbg_tl hm_b
    let lit_b := cur.core.tmp[beg.toNat]'hbg_tl
    have hbt1 : cur.core.tmp[beg.toNat]? = s_c1.core.tmp[beg.toNat]? :=
      hb.tail_eq beg.toNat (le_refl _) hbx
    have hne_b : cur.core.tmp[beg.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [hbt1]; exact hc1_ne beg.toNat hbx
    have hr_b := hb.rem_mrk beg.toNat hbx hne_b
    rw [List.getElem?_eq_getElem hbg_tl, Option.getD_some] at hr_b
    have hbv_lt : (lit_b >>> 1).toNat < s.core.cur_vars := by
      dsimp only [lit_b]; rw [bv32_lshr_1]; omega
    have hblvl_l : ((lit_b >>> 1).setWidth 64).toNat < cur.core.lvl.length := by
      rw [hb.core.1.core_ok.lvl_len, bv_c0_zext32_64]; omega
    s13_lets; ml_ld c0_load_full_lvl (s := cur) (i := (lit_b >>> 1).setWidth 64) hblvl_l hm_b
    let blvl := cur.core.lvl[((lit_b >>> 1).setWidth 64).toNat]'hblvl_l
    ml_ld c0_load_full_tmp (s := cur) (i := beg) hbg_tl hm_b
    have hbt_len : cur.core.trail_pos.length = c.max_vars := hb.core.1.core_ok.trail_pos_len
    have hbtp_l : ((lit_b >>> 1).setWidth 64).toNat < cur.core.trail_pos.length := by
      rw [hbt_len, bv_c0_zext32_64]; omega
    s13_lets; ml_ld c0_load_full_trail_pos (s := cur) (i := (lit_b >>> 1).setWidth 64) hbtp_l hm_b
    let tp0 := cur.core.trail_pos[((lit_b >>> 1).setWidth 64).toNat]'hbtp_l
    have hlit_b_eq : lit_b.toNat = (s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat := by
      dsimp only [lit_b]; rw [← hbt1, List.getElem?_eq_getElem hbg_tl, Option.getD_some]
    have hblv_nat : blvl.toNat =
        (s.core.lvl[(s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
      dsimp only [blvl]
      rw [show cur.core.lvl[((lit_b >>> 1).setWidth 64).toNat]'hblvl_l =
            (some (cur.core.lvl[((lit_b >>> 1).setWidth 64).toNat]'hblvl_l)).getD 0#32 from rfl,
        ← List.getElem?_eq_getElem hblvl_l, bv_c0_zext32_64, bv32_lshr_1, hb.lvl_eq, hlit_b_eq]
    have hblv_ok : 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level := by
      rw [hblv_nat]; exact hc1_lvls beg.toNat hbeg1 hbx
    have htp0_nat : (tp0.setWidth 64).toNat =
        (s.core.trail_pos[(s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
      rw [bv_c0_zext32_64]; dsimp only [tp0]
      rw [show cur.core.trail_pos[((lit_b >>> 1).setWidth 64).toNat]'hbtp_l =
            (some (cur.core.trail_pos[((lit_b >>> 1).setWidth 64).toNat]'hbtp_l)).getD 0#32
            from rfl,
        ← List.getElem?_eq_getElem hbtp_l, bv_c0_zext32_64, bv32_lshr_1, hb.tpos_eq, hlit_b_eq]
    have hbeg1_nat : (beg + 1).toNat = beg.toNat + 1 := min_bv64_add1 (by omega)
    s13_lets
    refine wp_loop_group (ts := [i64, i64]) (fun n (max_tr, end_b, ()) m_w =>
        n = tlen - end_b.toNat ∧ m_w = mb ∧ beg.toNat < end_b.toNat ∧ end_b.toNat ≤ tlen ∧
        (∀ k, beg.toNat ≤ k → k < end_b.toNat →
          (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
          (s.core.trail_pos[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            max_tr.toNat)) ?_
      (fun Js_1 hJs_1 => by
        s13_lets; exact hJs_1 (tlen - (beg.toNat + 1)) (tp0.setWidth 64, beg + 1, ()) mb
          ⟨by rw [hbeg1_nat], rfl, by rw [hbeg1_nat]; omega, by rw [hbeg1_nat]; omega,
            fun k hk1 hk2 => by
              rw [hbeg1_nat] at hk2; obtain rfl : k = beg.toNat := (by omega)
              exact ⟨hblv_nat.symm, by rw [htp0_nat]; exact le_refl _⟩⟩)
    rintro Js_1 n_w ⟨max_tr, end_b, ⟨⟩⟩ m_w hJs_1 ⟨rfl, hmw_eq, hbeg_end, hend_tl, hblk_in⟩
    subst m_w; rw [Blocks.get_here]
    refine wp_join_group (ts := []) (fun () m_end =>
        m_end = mb ∧ (end_b.toNat < tlen → blvl.toNat <
          (s.core.lvl[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)) ?_ ?_
    · rintro J_ex ⟨⟩ m_end ⟨hm_end_eq, hstep_end⟩; subst m_end; rw [Blocks.get_here]
      refine wp_join_group (ts := []) (fun () m_next =>
          ∃ mrk_n tmp_n mclr_n sstk_n wsort_n ws1_n mcl_n mcf_n ticks_n resSz_n,
            let cur_n := s13BlkState s_c1 tmp_n mrk_n mclr_n sstk_n wsort_n ws1_n
              mcl_n mcf_n ticks_n resSz_n
            S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_n ∧ (FullMem c cur_n ⋆ R) m_next)
        (fun _ ⟨⟩ m_next ⟨mrk_n, tmp_n, mclr_n, sstk_n, wsort_n, ws1_n, mcl_n, mcf_n, ticks_n,
            resSz_n, hn, hm_n⟩ => by
          rw [Blocks.get_here]; s13_lets
          exact hJs (tlen - end_b.toNat) (end_b, ()) m_next (by omega)
            ⟨rfl, by omega, hend_tl, mrk_n, tmp_n, mclr_n, sstk_n, wsort_n, ws1_n, mcl_n, mcf_n,
              ticks_n, resSz_n, hn, hm_n⟩) ?_
      rintro J_nb hJ_nb; s13_lets; ml_jnz; refine ⟨fun hge2 => ?_, fun _ => ?_⟩
      · refine wp_join_group (ts := []) (fun () m_done =>
            ∃ mrk_n tmp_n mclr_n sstk_n wsort_n ws1_n mcl_n mcf_n ticks_n resSz_n,
              let cur_n := s13BlkState s_c1 tmp_n mrk_n mclr_n sstk_n wsort_n ws1_n
                mcl_n mcf_n ticks_n resSz_n
              S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_n ∧ (FullMem c cur_n ⋆ R) m_done)
          (fun _ ⟨⟩ m_done hdone => by rw [Blocks.get_here]; exact hJ_nb () m_done hdone) ?_
        rintro J_bd hJ_bd
        have hblk_cur : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
            let l := (cur.core.tmp[k]?.getD 0#32).toNat
            l < 2 * cur.core.cur_vars ∧ cur.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
            (cur.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
            (cur.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat := fun k hk1 hk2 => by
          have hk_t : k < tlen := Nat.lt_of_lt_of_le hk2 hend_tl
          have htk := hb.tail_eq k (by omega) hk_t
          have hrm := hb.rem_mrk k hk_t (by rw [htk]; exact hc1_ne k hk_t)
          have hbi := hblk_in k hk1 hk2
          dsimp only; rw [hb.cv_eq, hb.vals_eq, hb.lvl_eq, hb.tpos_eq]
          exact ⟨hrm.1, hrm.2.1, by rw [htk]; exact hbi.1, by rw [htk]; exact hbi.2⟩
        have hkeep_cur : ∀ k < tlen, cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
            let l := (cur.core.tmp[k]?.getD 0#32).toNat
            l < 2 * cur.core.cur_vars ∧ cur.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
            (cur.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun k hk hne => by
          have hrm := hb.rem_mrk k hk hne; rw [hb.cv_eq, hb.vals_eq]; exact hrm
        apply wp_call_of_spec; apply hSb; dsimp only [vals, Arg.val]
        refine m8ShrinkBlkBoolSpec_of hb.core (m8_toFullMinInv hb.min_inv)
          (fun v hv => hb.no8 v (hb.cv_eq ▸ hv)) hbeg1 hbeg_end hend_tl
          (by rw [hb.cv_eq]; exact ht_cv) hblv_ok.1 (by rw [hb.clvl_eq]; exact hblv_ok.2)
          hblk_cur hkeep_cur hm_b ?_
        intro ok_s tmp_s mrk_s mclr_s sstk_s wsort_s mcl_s mcf_s ticks_s m_s
          hcore_s hmin_sf hab_s h8_s _ hfl_s hoth_s hlvl_s hnd_s hEnt_s hrem_s hm_s
        have hmin_s := m8_toSpecsMinInv hmin_sf
        let st_s := s13BlkState s_c1 tmp_s mrk_s mclr_s sstk_s wsort_s ws1_b
          mcl_s mcf_s ticks_s resSz_b
        have hst_s_eq : m8ShrinkBlkBoolState cur tmp_s mrk_s mclr_s sstk_s wsort_s mcl_s mcf_s
            ticks_s = st_s := rfl
        have hinv_s : S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat st_s := by
          refine ⟨hst_s_eq ▸ hcore_s, hst_s_eq ▸ hmin_s, fun F_cur hw hEnt0 => ?_,
            fun hnd0 hne0 => ?_, fun v hv => (hab_s v (hb.cv_eq ▸ hv)).trans (hb.mrk_above v hv),
            fun v hv => h8_s v (hb.cv_eq ▸ hv),
            hb.cv_eq, hb.tl_eq, hb.lvl_eq, hb.vals_eq, hb.clvl_eq, hb.tpos_eq,
            ?_, fun k hk1 hk2 => ?_, ?_, fun k hk hne => ?_, fun k hk1 hk2 hne => ?_⟩
          · obtain ⟨hw1, he1⟩ := hb.entails F_cur hw hEnt0
            have ⟨hw2, he2⟩ := hEnt_s F_cur hw1 he1; exact ⟨hst_s_eq ▸ hw2, he2⟩
          · refine hnd_s (hb.nodup hnd0 hne0) fun k hk hkb hne heq => ?_
            have heq_s : (s.core.lvl[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                blvl.toNat :=
              (congrArg (fun lv => (lv[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
                hb.lvl_eq.symm).trans heq
            by_cases hk0 : k = 0
            · subst k; rw [hb.zero_eq] at heq_s
              have heq' : (s.core.lvl[(s_c1.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  blvl.toNat := heq_s
              rw [hc1_0lv] at heq'; exact absurd heq' (Nat.ne_of_gt hblv_ok.2)
            · rw [hb.post_lvls k (Nat.pos_of_ne_zero hk0) hk hne] at heq_s
              rcases hkb with hlt_b | hge_e
              · have := hb.beg_bnd (by omega) hbx
                have := hc1_sort k (beg.toNat - 1) (Nat.pos_of_ne_zero hk0) (by omega) (by omega)
                omega
              · have := hstep_end (by omega)
                have := hc1_sort end_b.toNat k (Nat.le_trans hbeg1 (le_of_lt hbeg_end)) hge_e hk
                omega
          · rw [hoth_s 0 (by omega) (Or.inl (by omega))]; exact hb.zero_eq
          · rw [hoth_s k hk2 (Or.inr hk1)]; exact hb.tail_eq k (by omega) hk2
          · intro _ hend_lt
            have := (hblk_in (end_b.toNat - 1) (by omega) (by omega)).1
            have := hstep_end hend_lt; omega
          · have hr := hrem_s k hk hne; rw [hb.cv_eq, hb.vals_eq] at hr; exact hr
          · by_cases hk_in : beg.toNat ≤ k ∧ k < end_b.toNat
            · have hl1 := hlvl_s k hk_in.1 hk_in.2 hne
              have hl2 := (hblk_in k hk_in.1 hk_in.2).1
              have hl1' : (s.core.lvl[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  blvl.toNat :=
                (congrArg (fun lv => (lv[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
                  hb.lvl_eq.symm).trans hl1
              rw [hl1', hl2]
            · have hkb : k < beg.toNat ∨ end_b.toNat ≤ k := by omega
              have hne' := hne; rw [hoth_s k (by omega) hkb] at hne'
              rw [hoth_s k (by omega) hkb]; exact hb.post_lvls k hk1 hk2 hne'
        s13_lets; ml_jnz; refine ⟨fun _ => ?_, fun hok_f => ?_⟩
        · exact s13_min_shrink_true_wp hinv_s hbx ht_cv hm_s
            fun ws1' resSz' mf hinv' hmf =>
              hJ_bd () mf ⟨mrk_s, tmp_s, mclr_s, sstk_s, wsort_s, ws1', mcl_s, mcf_s, ticks_s,
                resSz', hinv', hmf⟩
        · have hf_s : ok_s = false := by c0_cond hok_f; exact hok_f
          have htmp_s_eq : tmp_s = cur.core.tmp := hfl_s hf_s
          exact s13_min_dfs_fallback_wp hDfs hbeg1 hbeg_end hend_tl ht_cv hc1_ne hc1_lvls
            (fun k hk1 hk2 => htmp_s_eq ▸ hb.tail_eq k hk1 hk2) hinv_s hm_s
            fun mrk_d tmp_d mclr_d wsort_d mcl_d mcf_d ticks_d md hd hm_d =>
              hJ_bd () md ⟨mrk_d, tmp_d, mclr_d, sstk_s, wsort_d, ws1_b, mcl_d, mcf_d, ticks_d,
                resSz_b, hd, hm_d⟩
      · have hinv_next : S13BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur :=
          { hb with
            tail_eq := fun k hk1 hk2 => hb.tail_eq k (by omega) hk2
            beg_bnd := fun _ hend_lt => by
              have := (hblk_in (end_b.toNat - 1) (by omega) (by omega)).1
              have := hstep_end hend_lt; omega }
        exact hJ_nb () mb ⟨mrk_b, tmp_b, mclr_b, sstk_b, wsort_b, ws1_b, mcl_b, mcf_b, ticks_b,
          resSz_b, hinv_next, hm_b⟩
    rintro J_ex hJ_ex; s13_lets; ml_jnz; refine ⟨fun hlt_tl => ?_, fun hge_tl => ?_⟩
    · have hend_x : end_b.toNat < tlen := by
        rw [BitVec.ult, decide_eq_true_eq, htlen_eq] at hlt_tl; exact hlt_tl
      have hend_arr : end_b.toNat < cur.core.tmp.length := by
        dsimp only [cur]; rw [hb.core.1.core_ok.tmp_len_arr]; omega
      ml_ld c0_load_full_tmp (s := cur) (i := end_b) hend_arr hm_b
      let lit_e := cur.core.tmp[end_b.toNat]'hend_arr
      have het1 : cur.core.tmp[end_b.toNat]? = s_c1.core.tmp[end_b.toNat]? :=
        hb.tail_eq end_b.toNat (by omega) hend_x
      have hr_e := hb.rem_mrk end_b.toNat hend_x (by rw [het1]; exact hc1_ne end_b.toNat hend_x)
      rw [List.getElem?_eq_getElem hend_arr, Option.getD_some] at hr_e
      have hev_lt : (lit_e >>> 1).toNat < s.core.cur_vars := by
        rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hr_e.1
      have helvl_l : ((lit_e >>> 1).setWidth 64).toNat < cur.core.lvl.length := by
        rw [hb.core.1.core_ok.lvl_len, bv_c0_zext32_64]; omega
      s13_lets; ml_ld c0_load_full_lvl (s := cur) (i := (lit_e >>> 1).setWidth 64) helvl_l hm_b
      let elvl := cur.core.lvl[((lit_e >>> 1).setWidth 64).toNat]'helvl_l
      have hlit_e_eq : lit_e.toNat = (s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat := by
        dsimp only [lit_e]; rw [← het1, List.getElem?_eq_getElem hend_arr, Option.getD_some]
      have helv_nat : elvl.toNat =
          (s.core.lvl[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        dsimp only [elvl]
        rw [show cur.core.lvl[((lit_e >>> 1).setWidth 64).toNat]'helvl_l =
              (some (cur.core.lvl[((lit_e >>> 1).setWidth 64).toNat]'helvl_l)).getD 0#32 from rfl,
          ← List.getElem?_eq_getElem helvl_l, bv_c0_zext32_64, bv32_lshr_1, hb.lvl_eq, hlit_e_eq]
      s13_lets; ml_jnz; refine ⟨fun heq_lv => ?_, fun hne_lv => ?_⟩
      · have helv_eq : elvl.toNat = blvl.toNat := by
          c0_cond heq_lv; exact congrArg BitVec.toNat heq_lv
        ml_ld c0_load_full_tmp (s := cur) (i := end_b) hend_arr hm_b
        have hetp_l : ((lit_e >>> 1).setWidth 64).toNat < cur.core.trail_pos.length := by
          rw [hbt_len, bv_c0_zext32_64]; omega
        s13_lets
        ml_ld c0_load_full_trail_pos (s := cur) (i := (lit_e >>> 1).setWidth 64) hetp_l hm_b
        let tpe := cur.core.trail_pos[((lit_e >>> 1).setWidth 64).toNat]'hetp_l
        have htpe_nat : (tpe.setWidth 64).toNat =
            (s.core.trail_pos[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD
              0#32).toNat := by
          rw [bv_c0_zext32_64]; dsimp only [tpe]
          rw [show cur.core.trail_pos[((lit_e >>> 1).setWidth 64).toNat]'hetp_l =
                (some (cur.core.trail_pos[((lit_e >>> 1).setWidth 64).toNat]'hetp_l)).getD 0#32
                from rfl,
            ← List.getElem?_eq_getElem hetp_l, bv_c0_zext32_64, bv32_lshr_1, hb.tpos_eq, hlit_e_eq]
        have hend1 : (end_b + 1).toNat = end_b.toNat + 1 := min_bv64_add1 (by omega)
        s13_lets
        refine wp_join_group (ts := [i64]) (fun (m_tr', ()) mw' =>
            mw' = mb ∧ max_tr.toNat ≤ m_tr'.toNat ∧
            (s.core.trail_pos[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              m_tr'.toNat)
          (fun _ ⟨m_tr', ⟨⟩⟩ mw' ⟨hmw_eq, hmt1, hmt2⟩ => by
            subst mw'; rw [Blocks.get_here]; s13_lets
            exact hJs_1 (tlen - (end_b + 1).toNat) (m_tr', end_b + 1, ()) mb (by omega)
              ⟨by rw [hend1], rfl, by rw [hend1]; omega, by rw [hend1]; exact hend_x,
                fun k hk1 hk2 => by
                  rw [hend1] at hk2; by_cases hke : k = end_b.toNat
                  · subst k; exact ⟨helv_nat ▸ helv_eq, hmt2⟩
                  · have hi := hblk_in k hk1 (by omega); exact ⟨hi.1, le_trans hi.2 hmt1⟩⟩) ?_
        rintro Jtp hJtp; s13_lets; ml_jnz; refine ⟨fun hgt => ?_, fun hle => ?_⟩
        · c0_cond hgt
          exact hJtp (tpe.setWidth 64, ()) mb ⟨rfl, le_of_lt hgt, by rw [htpe_nat]; exact le_refl _⟩
        · have hle' : (tpe.setWidth 64).toNat ≤ max_tr.toNat := by
            c0_cond hle; dsimp only [tpe]
            simp only [bv_c0_zext32_64, bv32_lshr_1] at hle ⊢; omega
          exact hJtp (max_tr, ()) mb ⟨rfl, le_refl _, by rw [htpe_nat] at hle'; exact hle'⟩
      · have helv_ne : elvl.toNat ≠ blvl.toNat := by
          c0_cond hne_lv; intro heq; apply hne_lv; exact BitVec.eq_of_toNat_eq heq
        have hlt_b := hc1_sort beg.toNat end_b.toNat hbeg1 (le_of_lt hbeg_end) hend_x
        have hb0 := (hblk_in beg.toNat (le_refl _) hbeg_end).1
        exact hJ_ex () mb ⟨rfl, fun _ => by rw [← helv_nat]; omega⟩
    · exact hJ_ex () mb ⟨rfl, fun h => by
        rw [BitVec.ult, decide_eq_false_iff_not, htlen_eq] at hge_tl; omega⟩
  · c0_cond hge
    have hbeg_e : beg.toNat = tlen := by rw [htlen_eq] at hge; omega
    subst hbeg_e; s13_lets
    refine s13_min_shrink_compact_loop_wp hb.core ht1 (by rw [hb.cv_eq]; exact ht_cv) htlen_eq
      (by rw [hb.zero_eq]; exact hc1_0ne)
      (fun k hk hne => by
        rw [hb.cv_eq, hb.vals_eq]; have hr := hb.rem_mrk k hk hne; exact ⟨hr.1, hr.2.1⟩)
      (fun k hk1 hk2 hne => by
        rw [hb.lvl_eq, hb.clvl_eq, hb.post_lvls k hk1 hk2 hne]; exact hc1_lvls k hk1 hk2) hm_b
      (fun keep_bv tmp_c mc htc_len hkp1 hkp_tl htc0 htake_eq htc_ne htc_ok hm_c => by
        ml_ld load_full_mark_ptr (s := { cur with core := { cur.core with tmp := tmp_c } }) hm_c
        s13_lets
        have hcv_c : ({ cur with core := { cur.core with tmp := tmp_c } } :
            FullState).core.cur_vars = s.core.cur_vars := hb.cv_eq
        have hcore_c : FullOtfsCoreInv c F0 { cur with core := { cur.core with tmp := tmp_c } } :=
          s13CoreInv_blk hb.core htc_len hb.core.1.core_ok.mrk_len
            hb.core.1.core_ok.min_clr_len_arr hb.core.1.core_ok.min_clr_len_le
            hb.core.1.scratch_ok.shrink_stk_len hb.core.1.scratch_ok.wsort_len
            hb.core.1.scratch_ok.work_stk1_len
        have hmin_c : FullMinMarkInv ({ cur with core := { cur.core with tmp := tmp_c } } :
            FullState).core
            (((tmp_c.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
          have hmf := s13ListFilterNeEqSelf (k := keep_bv.toNat)
            (by rw [htc_len]; exact le_trans hkp_tl (le_trans ht_cv hcv)) htc_ne
          have hma : ((tmp_c.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat =
              ((cur.core.tmp.take beg.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
            rw [hmf, htake_eq]
          exact ⟨fun v hv => hb.min_inv.mrk_dom v hv,
            fun hnf w hw h6 => hb.min_inv.clr_cov hnf w hw h6,
            fun idx hi h2 => by rw [hma]; exact hb.min_inv.rem_sound idx hi h2⟩
        rw [show BitVec.ofNat 64 s.core.cur_vars =
            BitVec.ofNat 64
              ({ cur with core := { cur.core with tmp := tmp_c } } : FullState).core.cur_vars
            from congrArg (BitVec.ofNat 64) hcv_c.symm]
        exact s13_min_shrink_clean_wp hcore_c
          (by rw [hcv_c]; exact le_trans hkp_tl ht_cv) (by rw [htlen_eq]; exact hkp_tl)
          (by rw [htlen_eq, hcv_c]; exact ht_cv) hmin_c
          (fun v hv => hb.no8 v (by rw [← hcv_c]; exact hv))
          (fun j hj1 hj2 => (htc_ok j hj1 hj2).1) hm_c
          fun tmp_f mrk_f mf hrev_f hml_f hab_f hmc_f hm_f => by
            have htf0' : tmp_f[0]? = s.core.tmp[0]? :=
              hrev_f.2.1.trans (htc0.trans (hb.zero_eq.trans hc1_0eq))
            exact hpost tmp_f keep_bv.toNat mrk_f mclr_b sstk_b wsort_b ws1_b 0 0#64
              (s_c1.scratch.learned_lits + keep_bv)
              (s_c1.scratch.min_removed + (tlen_bv - keep_bv)) ticks_b resSz_b mf
              (hrev_f.1.trans htc_len) hml_f hb.core.1.core_ok.min_clr_len_arr (Nat.zero_le _)
              hb.core.1.scratch_ok.shrink_stk_len hb.core.1.scratch_ok.wsort_len
              hb.core.1.scratch_ok.work_stk1_len
              (fun v hv => (hab_f v (by rw [hcv_c]; exact hv)).trans (hb.mrk_above v hv))
              hmc_f hkp1 (le_trans hkp_tl ht_tl) htf0'
              (fun hnd0 hne0 => by
                have htake_div : (tmp_c.take keep_bv.toNat).map (fun x => x.toNat / 2) =
                    ((cur.core.tmp.take beg.toNat).filter (· ≠ 0xFFFFFFFF#32)).map
                      (fun x => x.toNat / 2) := by
                  have h1 := congrArg (List.map (· / 2)) htake_eq
                  simpa only [List.map_map, Function.comp_def] using h1
                exact (hrev_f.2.2.1.map (fun x => x.toNat / 2)).nodup_iff.mpr
                  (htake_div ▸ hb.nodup hnd0 hne0))
              (fun j hj1 hj2 => by
                obtain ⟨i, hi1, hi2, heq⟩ := hrev_f.2.2.2 j hj1 hj2
                have ho := htc_ok i hi1 hi2
                rw [hb.cv_eq, hb.vals_eq, hb.lvl_eq, hb.clvl_eq] at ho
                simpa only [heq] using ho)
              (fun F_cur hw hEnt0 => by
                obtain ⟨hwc, hec⟩ := hb.entails F_cur hw hEnt0
                rw [← htake_eq] at hec
                exact ⟨m8Witness_minTmp hwc, s13TmpRevInv_entails hrev_f hec⟩)
              (by dsimp only [step13MinShrinkState]; exact hm_f))

/-! ## 3. Exact Body Equivalence & Top-Level `full_min_shrink_m6_step13_wp` -/

private theorem s13_min_shrink_m6_body_eq :
    full_min_shrink_m6_body = fun V _ p =>
      let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
      .let_ (op64 (.add i64) (.var p.fst) (.imm 776)) fun p_1 =>
      .load i64 (.var p_1.fst) fun ld =>
      .let_ (op64 (.add i64) (.var p.fst) (.imm 192)) fun p_2 =>
      .load i64 (.var p_2.fst) fun ld_1 =>
      .group (sig := [[]]) (fun _Js_p => .cons (fun _ =>
        .group (sig := [[]]) (fun _Js => .cons (fun _ =>
          .let_ (op64 (.add i64) (.var p.fst) (.imm 344)) fun p_7 =>
          .load i64 (.var p_7.fst) fun ld =>
          .let_ (op64 (.add i64) (.var ld) (.var ld_1)) fun p_8 =>
          .let_ (op64 (.add i64) (.var p.fst) (.imm 344)) fun p =>
          .store (.var p_8.fst) (.var p.fst) (.ret ())) .nil) fun Js =>
        .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var ld_1, .imm 1, ())) fun p_6 =>
        .jnz (.var p_6.fst) (.jump Js.fst ())
          (.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var ld_1, .var ld, ())) fun p_7 =>
           .jnz (.var p_7.fst) (.jump Js.fst ())
             (.call "full_sort_tmp" (as := [i64]) (bs := []) (.var p.fst, ()) fun _ =>
              .let_ (op64 (.add i64) (.var p.fst) (.imm 136)) fun p_9 =>
              .load i64 (.var p_9.fst) fun ld_3 =>
              .let_ (op64 (.add i64) (.var p.fst) (.imm 80)) fun p_10 =>
              .load i64 (.var p_10.fst) fun ld_4 =>
              .let_ (op64 (.add i64) (.var p.fst) (.imm 360)) fun p_11 =>
              .load i64 (.var p_11.fst) fun ld_5 =>
              .let_ (op64 (.add i64) (.var p.fst) (.imm 272)) fun p_12 =>
              .store (t := i64) (.imm 0) (.var p_12.fst)
                (.let_ (op64 (.add i64) (.var p.fst) (.imm 280)) fun p_13 =>
                 .store (t := i64) (.imm 0) (.var p_13.fst)
                   (s13MinMarkInitExpr p.fst ld_1 ld_3
                     (s13MinBlkLoopExpr p.fst ld ld_1 ld_3 ld_4 ld_5 ld_1)))))) .nil)
      (fun Js_p =>
        .let_ (op64 (.add i64) (.var p.fst) (.imm 520)) fun p_pr =>
        .load i64 (.var p_pr.fst) fun ld_pr =>
        .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var ld_pr, .imm 0, ())) fun p_peq =>
        .jnz (.var p_peq.fst)
          (.let_ (op64 (.add i64) (.var p.fst) (.imm 336)) fun p_3 =>
           .load i64 (.var p_3.fst) fun ld_2 =>
           .let_ (op64 (.add i64) (.var ld_2) (.imm 1)) fun p_4 =>
           .let_ (op64 (.add i64) (.var p.fst) (.imm 336)) fun p_5 =>
           .store (.var p_4.fst) (.var p_5.fst) (.jump Js_p.fst ()))
          (.jump Js_p.fst ())) := by
  funext V C p; rfl

private theorem full_min_shrink_m6_step13_wp_core (Γ : Env)
    (hStCore : ∀ {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
      {Q : Post []} {X : XPost},
      s.LengthsOk c → s.core.tmp_len ≤ s.core.cur_vars →
      (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat / 2 < c.max_vars) →
      (FullMem c s ⋆ R) m →
      (∀ tmp' wsort' m',
        ({ s with core := { s.core with tmp := tmp' }
                  scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c →
        tmp'.length = c.max_vars →
        (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
        (1 ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
        (∀ k, 1 ≤ k → k < s.core.tmp_len →
          ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[k]? = s.core.tmp[i]?) →
        (∀ i, 1 ≤ i → i < s.core.tmp_len →
          ∃ k, 1 ≤ k ∧ k < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[k]?) →
        (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
          (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
        (FullMem c { s with core := { s.core with tmp := tmp' }
                            scratch := { s.scratch with wsort := wsort' } } ⋆ R) m' → Q () m') →
      Γ "full_sort_tmp" [i64] [] (c.hdr, ()) m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, step13MinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_m6_body args m Q X := by
  rintro ⟨h0, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hlm0, htl1, htl_cv, hnd0, hEnt0, htmp_vals,
    htmp_lvls, h0_lvl, hm, hQ⟩ := step13MinShrinkSpec_elim hspec
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hlen0.core_ok.cur_vars_le
  have hmc0 : FullMarksClear s := fun v hv => hlm0.1 v (lt_of_lt_of_le hv hcv)
  dsimp only [Func.wp]; rw [s13_min_shrink_m6_body_eq]; dsimp only
  ml_ld load_full_cur_vars hm; ml_ld load_full_tmp_len hm
  let cf0 := if s.core.probing = 0#64 then s.scratch.conflicts + 1 else s.scratch.conflicts
  refine wp_join_group (ts := []) (fun () m0 =>
      (FullMem c { s with scratch := { s.scratch with conflicts := cf0 } } ⋆ R) m0) ?_
    (fun J_p hJ_p => by
      ml_ld load_full_probing hm; s13_lets; ml_jnz; refine ⟨fun hpr0 => ?_, fun hpr1 => ?_⟩
      · have hp : s.core.probing = 0#64 := by c0_cond hpr0; exact hpr0
        ml_ld load_full_conflicts hm; s13_lets
        ml_st m0, hm0 := store_full_conflicts (s.scratch.conflicts + 1) hm
        exact hJ_p () m0 (by dsimp only [cf0]; rw [ite_eq_left hp]; exact hm0)
      · have hp : s.core.probing ≠ 0#64 := by c0_cond hpr1; exact hpr1
        exact hJ_p () m (by dsimp only [cf0]; rw [ite_eq_right hp]; exact hm))
  rintro _ ⟨⟩ m0 hm0; rw [Blocks.get_here]
  let s0 : FullState := { s with scratch := { s.scratch with conflicts := cf0 } }
  have hs0_core : FullOtfsCoreInv c F0 s0 :=
    ⟨⟨hlen0.core_ok, s13MinShrinkScratchOk hlen0.scratch_ok hlen0.scratch_ok.shrink_stk_len
      hlen0.scratch_ok.wsort_len hlen0.scratch_ok.work_stk1_len⟩, F_cur, hw0⟩
  refine wp_join_group (ts := []) (fun () mq => s.core.tmp_len = 1 ∧ mq = m0)
    (fun _ ⟨⟩ mq ⟨htl_eq1, rfl⟩ => by
      rw [Blocks.get_here]
      ml_ld load_full_learned_lits (s := s0) hm0; s13_lets
      ml_st m_e, hm_e := store_full_learned_lits (s := s0)
        (s0.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len) hm0
      rw [wp]
      exact hQ s.core.tmp s.core.tmp_len s.core.mrk s.core.min_clr
        s.scratch.shrink_stk s.scratch.wsort s.scratch.work_stk1 s.core.min_clr_len
        s.core.min_clr_full cf0 (s.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len)
        s.scratch.min_removed s.scratch.search_ticks s.scratch.res_sz m_e
        ⟨hlen0.core_ok, s13MinShrinkScratchOk hlen0.scratch_ok hlen0.scratch_ok.shrink_stk_len
          hlen0.scratch_ok.wsort_len hlen0.scratch_ok.work_stk1_len⟩
        hw0 hlm0 htl1 (le_refl _) rfl hnd0 (fun j hj1 hj2 => by omega) hEnt0 hm_e) ?_
  rintro J_early hJ_early; s13_lets; ml_jnz
  refine ⟨fun hle1 => ?_, fun hgt1 => ?_⟩
  · have htl_eq1 : s.core.tmp_len = 1 := by c0_cond hle1; bv_omega
    s13_lets; exact hJ_early () m0 ⟨htl_eq1, rfl⟩
  · c0_cond hgt1; have h2lt : 2 ≤ s.core.tmp_len := by bv_omega
    s13_lets; ml_jnz; refine ⟨fun hoob => by exfalso; c0_cond hoob; bv_omega, fun _ => ?_⟩
    s13_lets; apply wp_call_of_spec; dsimp only [vals, Arg.val]
    refine hStCore hs0_core.1 (by dsimp only [s0]; omega)
      (fun k _ hk2 => by dsimp only [s0] at hk2 ⊢; have := (htmp_vals k (by omega)).1; omega)
      hm0
      (fun tmp1 wsort1 m1 hlen1 ht1_len ht1_perm ht1_0 ht1_r ht1_l ht1_sort hm1 => ?_)
    obtain ⟨hkeep_eq, hEnt1, htmp1_vals, htmp1_lvls⟩ := s13MinShrinkPostSort
      htl1 htl_cv hcv hlen0.core_ok.tmp_len_arr htmp_vals htmp_lvls ht1_len ht1_0 ht1_r ht1_l
    let s1 : FullState :=
      { s0 with core := { s0.core with tmp := tmp1 }
                scratch := { s0.scratch with wsort := wsort1 } }
    ml_ld load_full_tmp_lits_ptr (s := s1) hm1; ml_ld load_full_level_ptr (s := s1) hm1
    ml_ld load_full_trail_pos_ptr (s := s1) hm1
    ml_st m2, hm2 := store_full_min_clr_len (s := s1) 0 (Nat.zero_lt_succ _) hm1
    ml_st m3, hm3 :=
      store_full_min_clr_full (s := { s1 with core := { s1.core with min_clr_len := 0 } }) 0#64 hm2
    let s2 : FullState :=
      { s1 with core := { s1.core with min_clr_len := 0, min_clr_full := 0#64 } }
    have hs2_core : FullOtfsCoreInv c F0 s2 := fullOtfsCoreInv_with_min_tmp hs0_core ht1_len
      hlen0.core_ok.tmp_len_le hlen0.core_ok.mrk_len hlen0.core_ok.min_stk_len
      hlen0.core_ok.min_clr_len_arr (Nat.zero_le _) hlen1.scratch_ok
    let keep0 := ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    have hmin2_init : FullMinMarkInv s2.core keep0 := fullMinMarkInv_init hs2_core hmc0 keep0
    clear hm hm0 hm1 m1 hm2 m2 hs0_core
    have htl_bv : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len :=
      Nat.mod_eq_of_lt (by omega)
    refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) mi =>
        n = s.core.tmp_len - i_bv.toNat ∧ i_bv.toNat ≤ s.core.tmp_len ∧
        ∃ (mrk_i : List (BitVec 8)) (mclr_i : List (BitVec 32)) (mcl_i : Nat) (mcf_i : BitVec 64),
          let st_i := s13BlkState s2 tmp1 mrk_i mclr_i s2.scratch.shrink_stk wsort1
            s2.scratch.work_stk1 mcl_i mcf_i s2.scratch.search_ticks s2.scratch.res_sz
          mrk_i.length = c.max_vars ∧ mclr_i.length = c.max_vars ∧ mcl_i ≤ c.max_vars ∧
          (∀ v, s.core.cur_vars ≤ v → mrk_i[v]? = s.core.mrk[v]?) ∧
          (∀ v < s.core.cur_vars, (mrk_i[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
          FullMinMarkInv st_i.core keep0 ∧
          (∀ k < i_bv.toNat, (mrk_i[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
          (FullMem c st_i ⋆ R) mi) ?_
      (fun Jinit hJinit => by
        have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
        s13_lets; exact hJinit s.core.tmp_len (0#64, ()) m3
          ⟨by rw [h0v]; exact Nat.sub_zero _, by rw [h0v]; exact Nat.zero_le _, s2.core.mrk,
            s2.core.min_clr, s2.core.min_clr_len, s2.core.min_clr_full, hlen0.core_ok.mrk_len,
            hlen0.core_ok.min_clr_len_arr, Nat.zero_le _, fun _ _ => rfl, fun v hv => by
              change (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8; rw [hmc0 v hv]; rfl,
            hmin2_init, fun _ h => by rw [h0v] at h; omega, hm3⟩)
    rintro Jinit n ⟨i_bv, ⟨⟩⟩ mi hJinit
      ⟨rfl, hi_le, mrk_i, mclr_i, mcl_i, mcf_i, hmr_len, hmcl_len, hmcl_le,
        hab_i, hno8_i, hmin_i, hmarked_i, hm_i⟩
    let st_i := s13BlkState s2 tmp1 mrk_i mclr_i s2.scratch.shrink_stk wsort1 s2.scratch.work_stk1
      mcl_i mcf_i s2.scratch.search_ticks s2.scratch.res_sz
    have hcore_i := s13CoreInv_blk hs2_core ht1_len hmr_len hmcl_len hmcl_le
      hlen1.scratch_ok.shrink_stk_len hlen1.scratch_ok.wsort_len hlen1.scratch_ok.work_stk1_len
      (mcf1 := mcf_i) (ticks1 := s2.scratch.search_ticks) (resSz1 := s2.scratch.res_sz)
    rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hlt_i => ?_, fun hge_i => ?_⟩
    · have hi_lt : i_bv.toNat < s.core.tmp_len := by
        rw [BitVec.ult, decide_eq_true_eq, htl_bv] at hlt_i; exact hlt_i
      have hi_arr : i_bv.toNat < st_i.core.tmp.length := by
        dsimp only [st_i, s13BlkState]; rw [ht1_len]; omega
      ml_ld c0_load_full_tmp (s := st_i) (i := i_bv) hi_arr hm_i
      let lit_i := st_i.core.tmp[i_bv.toNat]'hi_arr
      have hl_get : lit_i.toNat = (tmp1[i_bv.toNat]?.getD 0#32).toNat := by
        dsimp only [lit_i]
        rw [show st_i.core.tmp[i_bv.toNat]'hi_arr =
              (some (st_i.core.tmp[i_bv.toNat]'hi_arr)).getD 0#32 from rfl,
          ← List.getElem?_eq_getElem hi_arr]
      have hli_v := htmp1_vals i_bv.toNat hi_lt
      have hli_lit_lt : lit_i.toNat < 2 * st_i.core.cur_vars := by rw [hl_get]; exact hli_v.2.1
      have hli_lt : (lit_i >>> 1).toNat < s.core.cur_vars := by
        rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hli_lit_lt
      s13_lets; apply wp_call_of_spec; apply hMm; refine m8_fullMinMarkSpec_of_specs ?_
      refine fullMinMarkSpec_step hcore_i.1 hm_i (lit_i >>> 1) hli_lt
        ((2 : BitVec 32).setWidth 8) fun mn hmn => ?_
      have h2eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl; rw [h2eq] at hmn
      let st_n := fullMinMarkStepState st_i (lit_i >>> 1).toNat 2#8
      have hlen_n := fullMinMarkStepState_lengths hcore_i.1 (lit_i >>> 1).toNat 2#8
      have hno8_v : (st_i.core.mrk[(lit_i >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8 :=
        hno8_i _ hli_lt
      have hab_n := fullMinMarkStepState_mrk_above (s := st_i) hli_lt 2#8
      obtain ⟨h8_n, hmono_n⟩ := fullMinMarkStepState_bit8_mono2 hcore_i.1 hli_lt (Or.inl rfl) hno8_v
      have hmin_n : FullMinMarkInv st_n.core keep0 := by
        have h1 := fullMinMarkInv_step_keep hcore_i hmin_i hli_lit_lt (hl_get ▸ hli_v.2.2.2)
          (hl_get ▸ hli_v.2.2.1) (by simpa only [bv32_lshr_1] using hno8_v)
        simpa only [st_n, bv32_lshr_1] using h1
      have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := min_bv64_add1 (by omega)
      have hm_n' : (FullMem c (s13BlkState s2 tmp1 st_n.core.mrk st_n.core.min_clr
          s2.scratch.shrink_stk wsort1 s2.scratch.work_stk1 st_n.core.min_clr_len
          st_n.core.min_clr_full s2.scratch.search_ticks s2.scratch.res_sz) ⋆ R) mn := by
        dsimp only [st_n] at hmn ⊢; rw [s13Blk_step]; exact hmn
      have hmin_n' : FullMinMarkInv (s13BlkState s2 tmp1 st_n.core.mrk st_n.core.min_clr
          s2.scratch.shrink_stk wsort1 s2.scratch.work_stk1 st_n.core.min_clr_len
          st_n.core.min_clr_full s2.scratch.search_ticks s2.scratch.res_sz).core keep0 := by
        have hc_f : ¬ s2.core.cur_vars ≤ (lit_i >>> 1).toNat := Nat.not_le.mpr hli_lt
        dsimp only [st_n, fullMinMarkStepState, fullMinMarkStepCore, st_i, s13BlkState] at hmin_n ⊢
        simp only [eq_false hc_f] at hmin_n ⊢
        by_cases hcond : (mrk_i[(lit_i >>> 1).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8
        · simp only [false_or, eq_true hcond, ↓reduceIte] at hmin_n ⊢; exact hmin_n
        · simp only [false_or, eq_false hcond, ↓reduceIte] at hmin_n ⊢
          dsimp only [fullMinMarkCore] at hmin_n ⊢; exact hmin_n
      refine hJinit (s.core.tmp_len - (i_bv + 1).toNat) (i_bv + 1, ()) mn (by omega)
        ⟨by rw [hi1], by rw [hi1]; omega, st_n.core.mrk, st_n.core.min_clr, st_n.core.min_clr_len,
          st_n.core.min_clr_full, hlen_n.core_ok.mrk_len, hlen_n.core_ok.min_clr_len_arr,
          hlen_n.core_ok.min_clr_len_le, fun v hv => (hab_n v hv).trans (hab_i v hv),
          fun v hv => by rw [h8_n v hv]; exact hno8_i v hv, hmin_n', fun k hk => ?_, hm_n'⟩
      rw [hi1] at hk; by_cases hki : k = i_bv.toNat
      · subst k; dsimp only [st_n, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore]
        split
        · rename_i hc
          simpa only [bv32_lshr_1, hl_get] using hc.resolve_left (Nat.not_le.mpr hli_lt)
        · dsimp only [lit_i, st_i, s13BlkState]
          rw [bv32_lshr_1, hl_get,
            List.getElem?_set_self (by rw [hmr_len, ← hl_get, ← bv32_lshr_1]; omega),
            Option.getD_some]
          exact bv8_and2_of_or2 _
      · exact hmono_n _ (Nat.div_lt_of_lt_mul (htmp1_vals k (by omega)).2.1)
          (hmarked_i k (by omega))
    · have hi_eq : i_bv.toNat = s.core.tmp_len := by
        rw [BitVec.ult, decide_eq_false_iff_not, htl_bv] at hge_i; omega
      rw [hi_eq] at hmarked_i
      have hc1_inv : S13BlkLoopInv c F0 s st_i s.core.tmp_len 1 st_i :=
        ⟨hcore_i, hmin_i,
          fun F_cur' hw' hEnt' =>
            ⟨{ hw' with
                arena := { hw'.arena with len_ok := hw'.arena.len_ok }
                watches := hw'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
              hEnt1 F_cur' hEnt'⟩,
          fun hnd _ => by
            have hmf := s13ListFilterNeEqSelf (by rw [ht1_len]; exact le_trans htl_cv hcv)
              (fun j hj => (htmp1_vals j hj).1)
            change (((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map
              fun x => x.toNat / 2).Nodup
            rw [hmf]; exact (ht1_perm.map (fun x => x.toNat / 2)).nodup_iff.mpr hnd,
          hab_i, hno8_i, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl,
          fun h _ => by omega,
          fun k hk _ => ⟨(htmp1_vals k hk).2.1, (htmp1_vals k hk).2.2.1, hmarked_i k hk⟩,
          fun _ _ _ _ => rfl⟩
      refine s13_min_shrink_blk_loop_wp hDfs hSb htl_bv htl1 htl_cv (le_refl _) hc1_inv
        (ht1_0 (Nat.lt_of_lt_of_le Nat.zero_lt_one htl1)) (htmp1_vals 0 htl1).1
        (by change (s.core.lvl[(tmp1[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level
            rw [ht1_0 (Nat.lt_of_lt_of_le Nat.zero_lt_one htl1)]; exact h0_lvl)
        (fun k hk => (htmp1_vals k hk).1) htmp1_lvls ht1_sort hm_i ?_
      intro tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' llits' mrem' ticks' resSz' mf _s'
        htmp'_len hmrk'_len hmclr'_len hmcl'_le hsstk'_len hws'_len hws1'_len hab' hmc'
        htl'_1 htl'_le ht'_0 hnd'_fn hlv'_fn hEnt'_fn hm'
      have hnd_out : ((tmp'.take tl').map fun x => x.toNat / 2).Nodup :=
        hnd'_fn hnd0 fun k hk1 hk2 => by
          have hl := (htmp_lvls k hk1 hk2).2
          change (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ _
          rw [h0_lvl]; omega
      obtain ⟨hw', hEnt'⟩ := hEnt'_fn F_cur hw0 hEnt0
      have hlen' : FullState.LengthsOk c (step13MinShrinkState s tmp' tl' mrk' mclr' sstk' wsort'
          ws1' mcl' mcf' cf0 llits' mrem' ticks' resSz') :=
        ⟨{ hlen0.core_ok with
            tmp_len_arr := htmp'_len, tmp_len_le := le_trans htl'_le hlen0.core_ok.tmp_len_le,
            mrk_len := hmrk'_len, min_clr_len_arr := hmclr'_len, min_clr_len_le := hmcl'_le },
          s13MinShrinkScratchOk hlen0.scratch_ok hsstk'_len hws'_len hws1'_len⟩
      exact hQ tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' cf0 llits' mrem' ticks' resSz' mf
        hlen' hw' (m8_mrk_above_zero hlm0 rfl hmc' hab' rfl)
        htl'_1 htl'_le ht'_0 hnd_out hlv'_fn hEnt' hm'

/-- `Func.wp` soundness theorem for Step-13 `full_min_shrink_m6` (`step7SortTmpSpec`). -/
theorem full_min_shrink_m6_step13_wp (Γ : Env)
    (hSt : ∀ args m Q X, step7SortTmpSpec args m Q X →
      Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, step13MinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_m6_body args m Q X :=
  full_min_shrink_m6_step13_wp_core Γ
    (fun {_c _s _R _m _Q _X} hlen htl hbd hm hcont =>
      hSt _ _ _ _ (step7SortTmpSpec_of hlen (le_trans htl hlen.core_ok.cur_vars_le)
        (fun k hk1 hk2 => by have := hbd k hk1 hk2; omega) hm
        fun tmp' wsort' m' hlen' ht' _ hperm h0 hr hl hlvl _ hm' =>
          hcont tmp' wsort' m' hlen' ht' hperm h0 hr hl hlvl hm'))
    hMm hDfs hSb

/-- `m7SortTmpSpec` variant of `full_min_shrink_m6_step13_wp`. -/
theorem full_min_shrink_m6_step13_wp_m7 (Γ : Env)
    (hSt : ∀ args m Q X, m7SortTmpSpec args m Q X →
      Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, step13MinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_m6_body args m Q X :=
  full_min_shrink_m6_step13_wp_core Γ
    (fun {_c _s _R _m _Q _X} hlen htl hbd hm hcont =>
      hSt _ _ _ _ (m7SortTmpSpec_of hlen (le_trans htl hlen.core_ok.cur_vars_le)
        (fun k hk1 hk2 => by have := hbd k hk1 hk2; omega) hm
        fun tmp' wsort' m' hlen' ht' _ hperm h0 hr hl _ hlvl _ hm' =>
          hcont tmp' wsort' m' hlen' ht' hperm h0 hr hl hlvl hm'))
    hMm hDfs hSb

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

end
