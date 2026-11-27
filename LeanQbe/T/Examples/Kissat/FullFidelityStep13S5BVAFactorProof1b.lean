/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactor
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactorProof0a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactorProof1a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas2
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas3
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullIngestLemmas2
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S5-C — BVA Commit Proofs Part 1b (`Proof1b`)

Subtree navigators (`s13HdrExpr` .. `s13FinalExpr`) and Phase 2 WP proofs (`s13_del_row_wp`,
`s13_final_wp`, `s13_del_wp`, `s13_phase2_wp`) for
`FullFidelityStep13S5BVAFactor.full_bva_commit_body`.
-/

set_option autoImplicit false

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000
local elab "c0_hstep" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 1
local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000
local elab "c0_hfast30" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 30

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a
open LeanQbe.T.Examples.Kissat.FullFidelityStep9
open scoped FullArenaTactics FullBvaHeapTactics

@[local bv_c0] private theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem bv32_one_toNat : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl

/-! ## 1. Step-13 `full_bva_commit_body` Subtree Navigators -/

@[expose, irreducible] def s13HdrExpr (h pAr pScr : Val i64) (best_k sc : Val i32) :
    Expr Val Cont [.bool] :=
  FullFidelityStep13S5BVAFactor.full_bva_commit_body Val Cont (h, best_k, ())
    |> sSteps 3 |> sElse |> sSteps 2 |> sCall32 sc |> sStep |> sElse |> sStep |> sElse |> sStep
    |> sLd64 pAr |> sStep |> sLd64 pScr

@[expose, irreducible] def s13PreMidExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) : Expr Val Cont [.bool] :=
  s13HdrExpr h pAr pScr best_k sc |> sStep |> sLd64 pCnt |> sStep |> sLd64 pFl
    |> sStep |> sLd64 pWv |> sLet32 dm |> sSteps 4 |> sLd32 brow_off
    |> sSteps 5 |> sLd32 mn |> sSteps 6

@[expose, irreducible] def s13PreExitExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) (need_ar need_w : Val i64) :
    Expr Val Cont [.bool] :=
  s13PreMidExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn
    |> sGrp64_32 (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse
    |> sGrp64_64_32v (fun (_ : Tup Val [i64, i64, i32]) (_ : Mem 64) => True) need_ar need_w
    |> sStep |> sElse |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse

@[expose, irreducible] def s13PostDefragExpr (h pAr pScr pCnt pFl pWv : Val i64)
    (best_k sc dm brow_off mn : Val i32) (dd : Val .bool) : Expr Val Cont [.bool] :=
  s13PreMidExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn |> s9MidExpr dd

@[expose, irreducible] def s13Phase1bExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh : Val i32) (dd ok1a : Val .bool) : Expr Val Cont [.bool] :=
  s13PostDefragExpr h pAr pScr pCnt pFl pWv best_k sc dm brow_off mn dd
    |> sSteps 10 |> sLd64 pDeg |> sSteps 22 |> sLet32 fresh |> sStep |> sLd64 pTmp
    |> sGrp32bb (fun (_ : Tup Val [i32, .bool, .bool]) (_ : Mem 64) => True) 0#32 dd ok1a

@[expose, irreducible] def s13Phase2Expr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 : Val i32) (dd1a dd1b : Val .bool)
    (garb_add0 irred_add0 : Val i64) : Expr Val Cont [.bool] :=
  s13Phase1bExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh dd1a true
    |> sGrp32bb6464 (fun (_ : Tup Val [i32, .bool, .bool, i64, i64]) (_ : Mem 64) => True)
      mi0 dd1b true garb_add0 irred_add0
    |> sThen

@[expose, irreducible] def s13DelExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 : Val i32) (dd1a dd1b : Val .bool)
    (garb_add0 irred_add0 : Val i64) : Expr Val Cont [.bool] :=
  s13Phase2Expr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0 dd1a dd1b
    garb_add0 irred_add0
    |> sGrp1 (fun (_ : Tup Val [i32]) (_ : Mem 64) => True) 0#32 |> sStep |> sElse

@[expose, irreducible] def s13DelRowExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 mv : Val i32) (garb_add : Val i64) (qsv : Val i32)
    (dd1a dd1b : Val .bool) (garb_add0 irred_add0 : Val i64) (Jq : Cont [i32, i64, i32]) :
    Expr Val Cont [.bool] :=
  s13DelExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0 dd1a dd1b
    garb_add0 irred_add0
    |> sStep |> sGrp32_64_32 Jq mv garb_add qsv |> sStep |> sThen

@[expose, irreducible] def s13FinalExpr (h pAr pScr pCnt pFl pWv pDeg pTmp : Val i64)
    (best_k sc dm brow_off mn fresh mi0 mv : Val i32) (garb_add : Val i64) (qsv : Val i32)
    (dd1a dd1b : Val .bool) (garb_add0 irred_add0 : Val i64) : Expr Val Cont [.bool] :=
  s13DelExpr h pAr pScr pCnt pFl pWv pDeg pTmp best_k sc dm brow_off mn fresh mi0 dd1a dd1b
    garb_add0 irred_add0
    |> sStep
    |> sGrp32_64_32 (fun (_ : Tup Val [i32, i64, i32]) (_ : Mem 64) => True) mv garb_add qsv
    |> sStep |> sElse

/-! ## 2. Phase 2: Row Compaction, Deletion Sweep & Deferred-Flush Exit -/

private theorem s13_del_row_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : S13DelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {stF std : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv : Val i32}
    {garb_add garb_add0 irred_add0 : Val i64} {dd1a dd1b : Val .bool}
    {Jq : Cont [i32, i64, i32]} {m0 : Mem 64}
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hqs_pos : 0 < qsv.toNat) (hqs_le : qsv.toNat ≤ best_k.toNat + 1)
    (hfs_ok : ∀ q ≤ best_k.toNat, (stF.scratch.scratch_buf[q]?.getD 0#32).toNat < 2 * c.max_vars)
    (hro : ∀ q ≤ best_k.toNat, s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
      mn_bv.toNat ≤ c.scratch_cap)
    (hval : ∀ q ≤ best_k.toNat, ∀ j < mn_bv.toNat, Step7RowRefOk stF
      (stF.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
        j]?.getD 0#32))
    (hstd : S9DelOk c F0 F_next stF std) (hm0 : (FullMem c std ⋆ R) m0)
    (hJq : ∀ (mv : Val i32) (ga' : Val i64) (st' : FullState) (mm : Mem 64),
      S9DelOk c F0 F_next stF st' → (FullMem c st' ⋆ R) mm → Jq (mv, ga', qsv - 1, ()) mm) :
    wp Γ Q X (s13DelRowExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 mv garb_add qsv dd1a dd1b garb_add0 irred_add0 Jq)
      m0 := by
  have hmx := c.hmaxv; have hscr_b : c.scratch_cap < 2 ^ 28 := c.hscr; unfold dimacsBound at hmx
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hsbd : std.scratch.scratch_buf = stF.scratch.scratch_buf := by rw [hstd.2.2.2.1]
  have hsbF_len : stF.scratch.scratch_buf.length = c.scratch_cap := by
    rw [← hsbd]; exact hstd.1.1.scratch_ok.scratch_buf_len
  unfold s13DelRowExpr s13DelExpr s13Phase2Expr s13Phase1bExpr s13PostDefragExpr s9MidExpr
    s13PreMidExpr s13HdrExpr
  delta FullFidelityStep13S5BVAFactor.full_bva_commit_body
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp1, sGrp64_32,
    sGrp64_64_32, sGrp32bb, sGrp32bb6464, sGrp32_64_32, sThen, sElse, sDummyTup, sDummyVal, i64,
    i32]
  have hq1 : (qsv - 1).toNat = qsv.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by simp only [bv_c0]; omega)]; rfl
  have hqsc_n : (BitVec.setWidth 64 (sc + (qsv - 1))).toNat =
      fidStepsCap c.scratch_cap + (qsv.toNat - 1) := by
    rw [bv64_setWidth_32, BitVec.toNat_add, hq1, hsc_eq]; omega
  have hqsc_lt : (BitVec.setWidth 64 (sc + (qsv - 1))).toNat < std.scratch.scratch_buf.length := by
    rw [hqsc_n, hsbd, hsbF_len]; omega
  have hq_n : (BitVec.setWidth 64 (qsv - 1)).toNat = qsv.toNat - 1 := by
    rw [bv64_setWidth_32, hq1]
  have hq_lt : (BitVec.setWidth 64 (qsv - 1)).toNat < std.scratch.scratch_buf.length := by
    rw [hq_n, hsbd, hsbF_len]; omega
  c0_hfast_nogrp
  generalize hrov : std.scratch.scratch_buf[(BitVec.setWidth 64 (sc + (qsv - 1))).toNat]'hqsc_lt =
    rov
  generalize hfsv : std.scratch.scratch_buf[(BitVec.setWidth 64 (qsv - 1)).toNat]'hq_lt = fsv
  have hfsv_lt : fsv.toNat < 2 * c.max_vars := by
    have h1 := hfs_ok (qsv.toNat - 1) (by omega)
    have h2 : stF.scratch.scratch_buf[qsv.toNat - 1]? = some fsv := by
      rw [← hsbd, ← hq_n, List.getElem?_eq_getElem hq_lt, hfsv]
    rwa [h2, Option.getD_some] at h1
  have hrov_n : rov.toNat =
      s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf (qsv.toNat - 1) := by
    have h1 : stF.scratch.scratch_buf[fidStepsCap c.scratch_cap + (qsv.toNat - 1)]? =
        some rov := by
      rw [← hsbd, ← hqsc_n, List.getElem?_eq_getElem hqsc_lt, hrov]
    simp only [s7Ro, h1, Option.getD_some]
  have hrow_b := hro (qsv.toNat - 1) (by omega)
  refine wp_loop_inv
    (fun (mi, _ga, ()) mm => ∃ st' : FullState, mi.toNat ≤ mn_bv.toNat ∧
      S9DelOk c F0 F_next stF st' ∧ (FullMem c st' ⋆ R) mm)
    (fun (mi, _, ()) _ => mn_bv.toNat - mi.toNat)
    (fun Jm hJm => ?_) (fun Jm (mi, gam, ()) mm ⟨st', hmi_le, hst', hmm⟩ ihm => ?_)
  · c0_hstep; exact hJm (0, garb_add, ()) m0 ⟨std, Nat.zero_le _, hstd, hm0⟩
  · c0_hsplit
    · have hmi_lt : mi.toNat < mn_bv.toNat := by assumption
      obtain ⟨hinv', hcv', hfuel', hsc', hal', hmono'⟩ := hst'
      have hsb' : st'.scratch.scratch_buf = stF.scratch.scratch_buf := by rw [hsc']
      have hcs_n : (BitVec.setWidth 64 (rov + mi)).toNat = rov.toNat + mi.toNat := by
        rw [bv64_setWidth_32, BitVec.toNat_add]; omega
      have hcs_lt : (BitVec.setWidth 64 (rov + mi)).toNat < st'.scratch.scratch_buf.length := by
        rw [hcs_n, hsb', hsbF_len, hrov_n]; omega
      c0_hfast_nogrp
      generalize hcsv : st'.scratch.scratch_buf[(BitVec.setWidth 64 (rov + mi)).toNat]'hcs_lt = cs
      have hcs_okF : Step7RowRefOk stF cs := by
        have h1 : stF.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap)
            stF.scratch.scratch_buf (qsv.toNat - 1) + mi.toNat]? = some cs := by
          rw [← hrov_n, ← hcs_n, ← hsb', List.getElem?_eq_getElem hcs_lt, hcsv]
        have h2 := hval (qsv.toNat - 1) (by omega) mi.toNat hmi_lt
        rwa [h1, Option.getD_some] at h2
      refine wp_join_group (ts := [i64])
        (fun (_, ()) mc => ∃ stc : FullState, (FullMem c stc ⋆ R) mc ∧ S9DelOk c F0 F_next stF stc)
        (fun _ (ga1, ()) mc ⟨stc, hmc, hstc⟩ => ?_) (fun Jc hJc => ?_)
      · have hmi1 : (mi + 1).toNat = mi.toNat + 1 := by
          rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
        c0_hfast; exact ihm (mi + 1, ga1, ()) mc (by dsimp only; omega) ⟨stc, by omega, hstc, hmc⟩
      · c0_hsplit
        · have hbin_ct : (cs &&& 0x80000000#32) ≠ 0#32 := by assumption
          have hcs_ok := step7RowRefOk_mono hcs_okF hmono' (by omega) hinv'.2.1.arena
          unfold Step7RowRefOk at hcs_ok; rw [ite_eq_left hbin_ct] at hcs_ok
          have hq_lt : (cs &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars := by
            have := hinv'.1.core_ok.cur_vars_le; omega
          c0_hfast; c0_call hDelBin
          refine ⟨c, st', R, rfl, hinv'.1, hinv'.2.1.watches.layout, hfsv_lt, hq_lt, hmm,
            fun flags' wvec' wstk' wu' nb' md1 hlen_d _ hwat_d hmd1 => ?_⟩
          have hinv_d := s13_fullDenseInvW_of_delBin hinv' hlen_d (hwat_d F_next hinv'.2.1.watches)
          c0_hfast; exact hJc (gam, ()) md1 ⟨_, hmd1, hinv_d, hcv', hfuel', hsc', hal', hmono'⟩
        · have hbin : (cs &&& 0x80000000#32) = 0#32 := by assumption
          have hcs_ok := step7RowRefOk_mono hcs_okF hmono' (by omega) hinv'.2.1.arena
          unfold Step7RowRefOk at hcs_ok; rw [ite_eq_right (fun h' => h' hbin)] at hcs_ok
          obtain ⟨hcs_ref', hcs_end, hcs_ng'⟩ := hcs_ok
          have hcl' := hinv'.1.core_ok
          have har_le : st'.core.arena_len ≤ st'.core.arena.length := by
            have := hcl'.arena_len_le; have := hcl'.arena_len_arr; omega
          have hcs2_n : (BitVec.setWidth 64 cs + 2).toNat = cs.toNat + 2 := by
            change (BitVec.setWidth 64 cs + 2#64).toNat = _; c0_bound
          have hcs2_lt : (BitVec.setWidth 64 cs + 2).toNat < st'.core.arena.length := by
            rw [hcs2_n]; omega
          c0_hfast_nogrp
          generalize hcszv : st'.core.arena[(BitVec.setWidth 64 cs + 2).toNat]'hcs2_lt = csz
          have hcsz : csz.toNat = fullArenaClauseSize st' cs.toNat := by
            show _ = (st'.core.arena[cs.toNat + 2]?.getD 0#32).toNat
            rw [← hcs2_n, List.getElem?_eq_getElem hcs2_lt, hcszv, Option.getD_some]
          refine wp_loop_inv
            (fun (k, ()) mk => ∃ stk : FullState, k.toNat ≤ csz.toNat ∧
              S9DelOk c F0 F_next stF stk ∧ stk.core.arena = st'.core.arena ∧
              (FullMem c stk ⋆ R) mk)
            (fun (k, ()) _ => csz.toNat - k.toNat)
            (fun Jk hJk => ?_) (fun Jk (k, ()) mk ⟨stk, hk_le, hstk, hark, hmk⟩ ihk => ?_)
          · c0_hstep; exact hJk (0, ()) mm ⟨st', Nat.zero_le _, ⟨hinv', hcv', hfuel', hsc', hal',
              hmono'⟩, rfl, hmm⟩
          · obtain ⟨hinvk, hcvk, hfuelk, hsck, halk, hmonok⟩ := hstk
            c0_hsplit
            · have hk_lt : k.toNat < csz.toNat := by assumption
              have hk1 : (k + 1).toNat = k.toNat + 1 := by
                rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
              have hclk := hinvk.1.core_ok
              have hcs_okk := step7RowRefOk_mono hcs_okF hmonok (by omega) hinvk.2.1.arena
              unfold Step7RowRefOk at hcs_okk; rw [ite_eq_right (fun h' => h' hbin)] at hcs_okk
              have hcsk_n : (BitVec.setWidth 64 cs + 3 + BitVec.setWidth 64 k).toNat =
                  cs.toNat + 3 + k.toNat := by
                change (BitVec.setWidth 64 cs + 3#64 + BitVec.setWidth 64 k).toNat = _; c0_bound
              have hcsk_lt : (BitVec.setWidth 64 cs + 3 + BitVec.setWidth 64 k).toNat <
                  stk.core.arena.length := by rw [hcsk_n, hark]; omega
              have hdl_lt : (stk.core.arena[(BitVec.setWidth 64 cs + 3 +
                  BitVec.setWidth 64 k).toNat]'hcsk_lt).toNat < 2 * stk.core.cur_vars := by
                have hk_sz : k.toNat < fullArenaClauseSizeCore stk.core cs.toNat := by
                  show k.toNat < (stk.core.arena[cs.toNat + 2]?.getD 0#32).toNat
                  rw [hark]; show k.toNat < fullArenaClauseSize st' cs.toNat; exact hcsz ▸ hk_lt
                have hmem := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem hk_sz
                  (by rw [← hcsk_n]; exact hcsk_lt)
                have hdl := hcs_okk.2.2 _ (List.mem_of_getElem? hmem)
                simpa only [hcsk_n] using hdl
              have hdl_fl_bv : (BitVec.setWidth 64 ((stk.core.arena[(BitVec.setWidth 64 cs + 3 +
                  BitVec.setWidth 64 k).toNat]'hcsk_lt) >>> (1 : BitVec 32))).toNat <
                  stk.core.flags.length := by
                rw [bv64_setWidth_32, bv32_lshr1_bv, hclk.flags_len]
                have := hclk.cur_vars_le; omega
              have hdl_fl_n : (BitVec.setWidth 64 ((stk.core.arena[(BitVec.setWidth 64 cs + 3 +
                  BitVec.setWidth 64 k).toNat]'hcsk_lt) >>> (1 : Nat))).toNat <
                  stk.core.flags.length := by
                rw [bv64_setWidth_32, bv32_lshr1_nat, hclk.flags_len]
                have := hclk.cur_vars_le; omega
              c0_hfast
              let fl' := stk.core.flags.set (BitVec.setWidth 64
                ((stk.core.arena[(BitVec.setWidth 64 cs + 3 +
                  BitVec.setWidth 64 k).toNat]'hcsk_lt) >>> (1 : BitVec 32))).toNat
                ((stk.core.flags[(BitVec.setWidth 64
                  ((stk.core.arena[(BitVec.setWidth 64 cs + 3 +
                    BitVec.setWidth 64 k).toNat]'hcsk_lt) >>>
                    (1 : BitVec 32))).toNat]'hdl_fl_bv) ||| 16#32)
              have hinv_fl := fullDenseInvW_set_flags hinvk (fl' := fl')
                (by simp [fl', hclk.flags_len])
              c0_call hUnwatch
              refine ⟨c, { stk with core := { stk.core with flags := fl' } }, R, rfl, hinv_fl.1,
                hinv_fl.2.1.watches.layout, hm,
                fun wvec' wstk' wu' mu hlen_u _ hwat_u hmu => ?_⟩
              have hinv_u := s13_fullDenseInvW_of_unwatchLarge hinv_fl hlen_u
                (hwat_u F_next hinv_fl.2.1.watches)
              c0_hfast; exact ihk (k + 1, ()) mu (by dsimp only; omega)
                ⟨_, by omega, ⟨hinv_u, hcvk, hfuelk, hsck, halk, hmonok⟩, hark, hmu⟩
            · have hcs_okk := step7RowRefOk_mono hcs_okF hmonok (by omega) hinvk.2.1.arena
              unfold Step7RowRefOk at hcs_okk; rw [ite_eq_right (fun h' => h' hbin)] at hcs_okk
              have hcs_refk : cs.toNat ∈ fullArenaClauseRefsCore stk.core := hcs_okk.1
              have hcs_lt : (BitVec.setWidth 64 cs).toNat < stk.core.arena.length := by
                rw [bv64_setWidth_32, hark]; omega
              have hgen : S9DelOk c F0 F_next stF { stk with
                  core := { stk.core with
                    arena := stk.core.arena.set cs.toNat
                      (fullArenaHdrCore stk.core cs.toNat ||| 0x00080000#32) } } := by
                obtain ⟨hinv_g, hmono_g⟩ :=
                  FullFidelityBva.fullDenseInvW_of_markGarb hinvk hcs_refk stk.core.arena_garbage
                exact ⟨hinv_g, hcvk, hfuelk, hsck, halk, fidBvaArenaMono_trans hmonok hmono_g⟩
              have harr : stk.core.arena.set (BitVec.setWidth 64 cs).toNat
                  (stk.core.arena[(BitVec.setWidth 64 cs).toNat]'hcs_lt ||| 0x00080000#32) =
                  stk.core.arena.set cs.toNat
                    (fullArenaHdrCore stk.core cs.toNat ||| 0x00080000#32) := by
                have h1 : fullArenaHdrCore stk.core cs.toNat =
                    stk.core.arena[(BitVec.setWidth 64 cs).toNat]'hcs_lt := by
                  unfold fullArenaHdrCore
                  rw [← bv64_setWidth_32 cs, List.getElem?_eq_getElem hcs_lt, Option.getD_some]
                rw [h1]
                exact congrArg (fun i => List.set stk.core.arena i
                  (stk.core.arena[(BitVec.setWidth 64 cs).toNat]'hcs_lt ||| 0x00080000#32))
                  (bv64_setWidth_32 cs)
              c0_hfast
              refine hJc (gam + 3#64 + BitVec.setWidth 64 csz, ()) m ⟨_, ?_, hgen⟩
              rw [← harr]; exact hm
    · c0_hfast; exact hJq mi gam st' mm hst' hmm

private theorem s13_final_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFillU64 : FidFillU64Hyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stF stm : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 mv qsv : Val i32}
    {garb_add garb_add0 irred_add0 : Val i64} {dd1a dd1b : Val .bool} {mm : Mem 64}
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hcvF : stF.core.cur_vars = s.core.cur_vars + 1) (hfuelF : stF.core.fuel = s.core.fuel)
    (htmF : stF.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrF : stF.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hcommF : ∀ st', S9DelOk c F0 F_next stF st' → Step7BvaCommittedOk c st' best_k.toNat)
    (hstm : S9DelOk c F0 F_next stF stm) (hmm : (FullMem c stm ⋆ R) mm)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s13FinalExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 mv garb_add qsv dd1a dd1b garb_add0 irred_add0)
      mm := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcomm := hcommF stm hstm
  obtain ⟨hinvm, hcvm, hfuelm, hscm', halm, hmonom⟩ := hstm
  have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le := hclm.cur_vars_le
  have htmm : stm.scratch.tarjan_mark = s.scratch.tarjan_mark := by rw [hscm']; exact htmF
  have htrm : stm.scratch.tarjan_reach = s.scratch.tarjan_reach := by rw [hscm']; exact htrF
  unfold s13FinalExpr s13DelExpr s13Phase2Expr s13Phase1bExpr s13PostDefragExpr s9MidExpr
    s13PreMidExpr s13HdrExpr
  delta FullFidelityStep13S5BVAFactor.full_bva_commit_body
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp1, sGrp64_32,
    sGrp64_64_32, sGrp32bb, sGrp32bb6464, sGrp32_64_32, sThen, sElse, sDummyTup, sDummyVal, i64,
    i32]
  refine wp_join0
    (fun mg => ∃ stg : FullState, S9DelOk c F0 F_next stF stg ∧ (FullMem c stg ⋆ R) mg)
    (fun _ mg ⟨stg, hstg, hmg⟩ => ?_) (fun Jg hJg => ?_)
  · refine wp_join0
      (fun mi_m => ∃ sti : FullState, S9DelOk c F0 F_next stF sti ∧ (FullMem c sti ⋆ R) mi_m)
      (fun _ mi_m ⟨sti, hsti, hmi_m⟩ => ?_) (fun Ji hJi => ?_)
    · have hcomm_i := hcommF sti hsti
      obtain ⟨hinvi, hcvi, hfueli, hsci, _, _⟩ := hsti
      have hcli := hinvi.1.core_ok; have hsci_ok := hinvi.1.scratch_ok
      refine wp_join_state0 (α := List (BitVec 32))
        (fun wsz mzi => wsz.length = 2 * c.max_vars ∧
          (FullMem c { sti with scratch := { sti.scratch with wsort := wsz } } ⋆ R) mzi)
        (fun _ wsz mzi ⟨hwsz_l, hmzi⟩ => ?_) (fun Jw hJw => ?_)
      · have hfr_rp : (BitVec.setWidth 64 fresh).toNat < sti.core.repr.length := by
          rw [bv64_setWidth_32, hfresh_nat, hcli.repr_len]; omega
        have hfr1_rp :
            (BitVec.setWidth 64 (fresh ^^^ 1#32)).toNat <
              (sti.core.repr.set (BitVec.setWidth 64 fresh).toNat dm_bv).length := by
          rw [List.length_set, bv64_setWidth_32, hfresh1, hcli.repr_len]; omega
        c0_hfast
        have hrp_len :
            ((sti.core.repr.set (BitVec.setWidth 64 fresh).toNat dm_bv).set
              (BitVec.setWidth 64 (fresh ^^^ 1#32)).toNat mn_bv).length = 2 * c.max_vars := by
          simp [hcli.repr_len]
        have hinv_fin := fullDenseInv_with_core_aux (tc' := sti.core.tmp_cnt)
          (tl' := sti.core.tmp_len)
          (sc' := { sti.scratch with wsort := wsz, bva_cnt := sti.scratch.bva_cnt + 1#64 })
          hinvi hrp_len hcli.min_clr_len_arr hcli.tmp_len_arr hcli.flags_len
          hcli.tmp_len_le { hsci_ok with wsort_len := hwsz_l } rfl rfl
        have htm_i : sti.scratch.tarjan_mark = s.scratch.tarjan_mark := by rw [hsci]; exact htmF
        have htr_i : sti.scratch.tarjan_reach = s.scratch.tarjan_reach := by rw [hsci]; exact htrF
        exact hQ true _ m hinv_fin.toDense (by dsimp only; omega)
          (fun _ => by dsimp only; omega) (fun _ => hcomm_i.congr rfl rfl rfl rfl rfl)
          (hfueli.trans hfuelF) htm_i htr_i hm
      · c0_hsplit
        · c0_hfast_nogrp
          refine s9_call_fill_u64_wsort hFillU64 hsci_ok.wsort_len hcli.cur_vars_le
            rfl rfl (by decide) hmi_m fun ws' m' hws'_l hm' => ?_
          c0_hstep; exact hJw ws' m' ⟨hws'_l, hm'⟩
        · c0_hstep; exact hJw sti.scratch.wsort mi_m ⟨hsci_ok.wsort_len, hmi_m⟩
    · obtain ⟨hinvg, hcvg, hfuelg, hscg, halg, hmonog⟩ := hstg
      c0_hsplit
      · c0_hfast
        exact hJi m
          ⟨{ stg with core := { stg.core with num_irred := stg.core.num_irred + irred_add0 } },
           ⟨s9_fullDenseInvW_with_num_irred hinvg _, hcvg, hfuelg, hscg, halg, hmonog⟩, hm⟩
      · c0_hstep; exact hJi mg ⟨stg, ⟨hinvg, hcvg, hfuelg, hscg, halg, hmonog⟩, hmg⟩
  · c0_hsplit
    · c0_hfast
      exact hJg m
        ⟨{ stm with core := { stm.core with arena_garbage := stm.core.arena_garbage + garb_add } },
         ⟨s9_fullDenseInvW_with_garb hinvm _, hcvm, hfuelm, hscm', halm, hmonom⟩, hm⟩
    · c0_hstep; exact hJg mm ⟨stm, ⟨hinvm, hcvm, hfuelm, hscm', halm, hmonom⟩, hmm⟩

private theorem s13_del_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : S13DelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {stF : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 : Val i32}
    {dd1a dd1b : Val .bool} {garb_add0 irred_add0 : Val i64} {m0 : Mem 64}
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hfs_ok : ∀ q ≤ best_k.toNat, (stF.scratch.scratch_buf[q]?.getD 0#32).toNat < 2 * c.max_vars)
    (hro : ∀ q ≤ best_k.toNat, s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
      mn_bv.toNat ≤ c.scratch_cap)
    (hval : ∀ q ≤ best_k.toNat, ∀ j < mn_bv.toNat, Step7RowRefOk stF
      (stF.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap) stF.scratch.scratch_buf q +
        j]?.getD 0#32))
    (hinvF : FullDenseInvW c F0 F_next stF) (hm0 : (FullMem c stF ⋆ R) m0)
    (hfin : ∀ (mv : Val i32) (ga : Val i64) (qsv : Val i32) (st' : FullState) (mm : Mem 64),
      S9DelOk c F0 F_next stF st' → (FullMem c st' ⋆ R) mm →
      wp Γ Q X (s13FinalExpr c.hdr c.pArena c.pScratchBuf c.pWsort
        c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0 mv ga qsv
        dd1a dd1b garb_add0 irred_add0) mm) :
    wp Γ Q X (s13DelExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 dd1a dd1b garb_add0 irred_add0) m0 := by
  have hscr_b : c.scratch_cap < 2 ^ 28 := c.hscr
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbk1 : (best_k + 1).toNat = best_k.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
  have heq : s13DelExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 dd1a dd1b garb_add0 irred_add0 = s13DelExpr c.hdr
      c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv
      fresh mi0 dd1a dd1b garb_add0 irred_add0 := rfl
  conv at heq =>
    rhs
    unfold s13DelExpr s13Phase2Expr s13Phase1bExpr s13PostDefragExpr s9MidExpr s13PreMidExpr
      s13HdrExpr
    delta FullFidelityStep13S5BVAFactor.full_bva_commit_body
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp1, sGrp64_32,
      sGrp64_64_32, sGrp32bb, sGrp32bb6464, sThen, sElse, sDummyTup, sDummyVal, i64, i32]
  rw [heq]; c0_hstep
  refine wp_loop_inv
    (fun (_, _, qsv, ()) mm => ∃ st' : FullState, qsv.toNat ≤ best_k.toNat + 1 ∧
      S9DelOk c F0 F_next stF st' ∧ (FullMem c st' ⋆ R) mm)
    (fun (_, _, qsv, ()) _ => qsv.toNat)
    (fun J hJ => ?_) (fun J (mv, ga, qsv, ()) mm ⟨st', hqs_le, hst', hmm⟩ ih => ?_)
  · c0_hstep; exact hJ (_, garb_add0, best_k + 1, ()) m0 ⟨stF, by omega,
      ⟨hinvF, rfl, rfl, rfl, rfl, fidBvaArenaMono_refl _⟩, hm0⟩
  · c0_hsplit
    · have hqs_pos : 0 < qsv.toNat := by simpa using hc
      have hq1 : (qsv - 1).toNat = qsv.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp only [bv_c0]; omega)]; rfl
      have h := s13_del_row_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch (dm_bv := dm_bv)
        (brow_off := brow_off) (fresh := fresh) (mi0 := mi0) (mv := mv) (garb_add := ga)
        (dd1a := dd1a) (dd1b := dd1b) (garb_add0 := garb_add0) (irred_add0 := irred_add0)
        (Jq := J) hsc_eq hbk_sc hqs_pos hqs_le hfs_ok hro hval hst' hmm
        (fun mv' ga' st'' mm' hst'' hmm' =>
          ih (mv', ga', qsv - 1, ()) mm' (by dsimp only; omega) ⟨st'', by omega, hst'', hmm'⟩)
      unfold s13DelRowExpr at h; rw [heq] at h; exact h
    · have h := hfin mv ga qsv st' mm hst' hmm
      unfold s13FinalExpr at h; rw [heq] at h; exact h

theorem s13_phase2_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFillU64 : FidFillU64Hyp Γ) (hDelBin : S13DelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st0 : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh mi0 : Val i32}
    {dd1a dd1b : Val .bool} {garb_add0 irred_add0 : Val i64} {m0 : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hmn_getD : (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hst0 : S7StOk c F0 F_next s st0) (hm0 : (FullMem c st0 ⋆ R) m0)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s13Phase2Expr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr
      c.pTmp best_k sc dm_bv brow_off mn_bv fresh mi0 dd1a dd1b garb_add0 irred_add0) m0 := by
  obtain ⟨hinv0, hcv0, hfuel0, hsb0s, htm0, htr0, hmono0, hres0⟩ := hst0
  have hmx := c.hmaxv; have hscr_b := c.hscr; unfold dimacsBound at hmx hscr_b
  have hsc0 := hinv0.1.scratch_ok
  have hsb0_len : st0.scratch.scratch_buf.length = c.scratch_cap := hsc0.scratch_buf_len
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hg : S7Geom (fidStepsCap c.scratch_cap) c.scratch_cap best_k.toNat
      st0.scratch.scratch_buf := by rw [hsb0s]; exact s7Geom_of hmat hlay
  have hmn : mn_bv.toNat =
      s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf best_k.toNat := by
    rw [hsb0s, ← hmn_getD, hsc_eq]
  have hrows : ∀ r ≤ best_k.toNat, ∀ j < s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf r,
      Step7RowRefOk st0 (st0.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap)
        st0.scratch.scratch_buf r + j]?.getD 0#32) := by
    rw [hsb0s]; exact s7_rows_ok hinv hmat hmono0 (by omega) hinv0.2.1.arena
  have hpars : ∀ r ≤ best_k.toNat, 0 < r →
      ∀ j < s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf r,
      (st0.scratch.scratch_buf[s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf r +
        j]?.getD 0#32).toNat <
        s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf (r - 1) := by
    rw [hsb0s]; exact s7_pars_ok hmat
  have hqmn : ∀ r ≤ best_k.toNat, mn_bv.toNat ≤
      s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf r := fun r hr =>
    hmn ▸ s7Geom_qn_le hg hr
  have heq2 : s13Phase2Expr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
      best_k sc dm_bv brow_off mn_bv fresh mi0 dd1a dd1b garb_add0 irred_add0 = s13Phase2Expr c.hdr
      c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp best_k sc dm_bv brow_off mn_bv
      fresh mi0 dd1a dd1b garb_add0 irred_add0 := rfl
  conv at heq2 =>
    rhs
    unfold s13Phase2Expr s13Phase1bExpr s13PostDefragExpr s9MidExpr s13PreMidExpr s13HdrExpr
    delta FullFidelityStep13S5BVAFactor.full_bva_commit_body
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp64_32, sGrp64_64_32,
      sGrp32bb, sGrp32bb6464, sThen, sElse, sDummyTup, sDummyVal, i64, i32]
  rw [heq2]
  refine wp_loop_inv
    (fun (fsi, ()) mv => ∃ sbv : List (BitVec 32), fsi.toNat ≤ best_k.toNat ∧
      S7CompInv (fidStepsCap c.scratch_cap) c.scratch_cap best_k.toNat mn_bv.toNat fsi.toNat mn_bv
        st0.scratch.scratch_buf sbv (Step7RowRefOk st0) ∧
      (FullMem c { st0 with scratch := { st0.scratch with scratch_buf := sbv } } ⋆ R) mv)
    (fun (fsi, ()) _ => fsi.toNat)
    (fun J hJ => ?_) (fun J (fsi, ()) mv ⟨sbv, hfsi_le, hcomp, hmv⟩ ih => ?_)
  · c0_hstep; exact hJ (best_k, ()) m0 ⟨st0.scratch.scratch_buf, Nat.le_refl _,
      s7CompInv_base hsb0_len (fun j hj => hrows _ (Nat.le_refl _) j (by omega))
        (fun hb j hj => hpars _ (Nat.le_refl _) hb j (by omega)), hm0⟩
  · c0_hsplit
    · clear heq2
      have hfsi_pos : 0 < fsi.toNat := by simpa using hc
      have hsbv_len := hcomp.1
      have hfm1 : (fsi - 1).toNat = fsi.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp only [bv_c0]; omega)]; rfl
      have hro_n : (BitVec.setWidth 64 (sc + (fsi - 1))).toNat =
          fidStepsCap c.scratch_cap + (fsi.toNat - 1) := by
        rw [bv64_setWidth_32, BitVec.toNat_add, hfm1, hsc_eq]; omega
      have hro_lt : (BitVec.setWidth 64 (sc + (fsi - 1))).toNat < sbv.length := by
        rw [hro_n, hsbv_len]; omega
      have hpo_n : (BitVec.setWidth 64 (3 * sc + fsi)).toNat =
          3 * fidStepsCap c.scratch_cap + fsi.toNat := by
        rw [bv64_setWidth_32, BitVec.toNat_add, BitVec.toNat_mul, hsc_eq]
        simp only [show (3 : BitVec 32).toNat = 3 from rfl]; omega
      have hpo_lt : (BitVec.setWidth 64 (3 * sc + fsi)).toNat < sbv.length := by
        rw [hpo_n, hsbv_len]; omega
      c0_hfast_nogrp
      generalize hrov : sbv[(BitVec.setWidth 64 (sc + (fsi - 1))).toNat]'hro_lt = rov
      generalize hpov : sbv[(BitVec.setWidth 64 (3 * sc + fsi)).toNat]'hpo_lt = pov
      obtain ⟨_, hB, hC, hD, hE, hF, hG⟩ := hcomp
      have hrov_n : rov.toNat = s7Ro (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf
          (fsi.toNat - 1) := by
        have h1 : sbv[fidStepsCap c.scratch_cap + (fsi.toNat - 1)]? = some rov := by
          rw [← hro_n, List.getElem?_eq_getElem hro_lt, hrov]
        have h2 := hB (fidStepsCap c.scratch_cap + (fsi.toNat - 1)) (by omega)
          (fun r h1 h2 => by omega)
        rw [h1] at h2; simp only [s7Ro, ← h2, Option.getD_some]
      have hpov_n : pov.toNat = s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf
          fsi.toNat := by
        have h1 : sbv[3 * fidStepsCap c.scratch_cap + fsi.toNat]? = some pov := by
          rw [← hpo_n, List.getElem?_eq_getElem hpo_lt, hpov]
        have h2 := hB (3 * fidStepsCap c.scratch_cap + fsi.toNat) (by omega)
          (fun r h1 h2 => by omega)
        rw [h1] at h2; simp only [s7Po, ← h2, Option.getD_some]
      have hcomp : S7CompInv (fidStepsCap c.scratch_cap) c.scratch_cap best_k.toNat mn_bv.toNat
          fsi.toNat mn_bv st0.scratch.scratch_buf sbv (Step7RowRefOk st0) :=
        ⟨hsbv_len, hB, hC, hD, hE, hF, hG⟩
      refine wp_join_group (ts := [i32])
        (fun (pp, ()) mm => mm = mv ∧ (1 < fsi.toNat → pp.toNat =
          s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf (fsi.toNat - 1)))
        (fun _ (pp, ()) mm ⟨hmm, hpp⟩ => ?_) (fun Jt hJt => ?_)
      rotate_left
      · have h3m_n : (BitVec.setWidth 64 (3 * sc + (fsi - 1))).toNat =
            3 * fidStepsCap c.scratch_cap + (fsi.toNat - 1) := by
          rw [bv64_setWidth_32, BitVec.toNat_add, BitVec.toNat_mul, hfm1, hsc_eq]
          simp only [show (3 : BitVec 32).toNat = 3 from rfl]; omega
        have h3m_lt : (BitVec.setWidth 64 (3 * sc + (fsi - 1))).toNat < sbv.length := by
          rw [h3m_n, hsbv_len]; omega
        c0_hfast
        · exact hJt (_, ()) mv ⟨rfl, fun _ => by
            have h1 : sbv[3 * fidStepsCap c.scratch_cap + (fsi.toNat - 1)]? =
                some (sbv[(BitVec.setWidth 64 (3 * sc + (fsi - 1))).toNat]'h3m_lt) := by
              rw [← h3m_n, List.getElem?_eq_getElem h3m_lt]
            have h2 := hB (3 * fidStepsCap c.scratch_cap + (fsi.toNat - 1)) (by omega)
              (fun r h1 h2 => by omega)
            rw [h1] at h2; simp only [s7Po, ← h2, Option.getD_some]⟩
        · exact hJt (0, ()) mv ⟨rfl, fun h => absurd h (by assumption)⟩
      · subst hmm
        refine wp_loop_inv
          (fun (fi, ()) mw => ∃ sbw : List (BitVec 32), fi.toNat ≤ mn_bv.toNat ∧
            S7RowInv (fidStepsCap c.scratch_cap) c.scratch_cap (fsi.toNat - 1)
              st0.scratch.scratch_buf sbv sbw (Step7RowRefOk st0) ∧
            (FullMem c { st0 with scratch := { st0.scratch with scratch_buf := sbw } } ⋆ R) mw)
          (fun (fi, ()) _ => mn_bv.toNat - fi.toNat)
          (fun Ji hJi => ?_) (fun Ji (fi, ()) mw ⟨sbw, hfi_le, hrinv, hmw⟩ ihi => ?_)
        · c0_hstep; exact hJi (0, ()) mm ⟨sbv, Nat.zero_le _, s7RowInv_init hcomp (by omega)
            (hrows _ (by omega)) (fun hq => hpars _ (by omega) hq), hmv⟩
        · have hsbw_len := hrinv.1
          c0_hsplit
          · have hfi_lt : fi.toNat < mn_bv.toNat := hc
            obtain ⟨_, hfj_lt⟩ := s7_par_read hg hcomp hrinv (by omega) hfsi_le hmn hfi_lt
            have hqb : fsi.toNat - 1 < best_k.toNat := by omega
            have hqmn' := hqmn (fsi.toNat - 1) (by omega)
            have hgq := hg.2.2.1 (fsi.toNat - 1) (by omega)
            have hgi := hg.2.2.2.1 fsi.toNat hfsi_le (by omega)
            have hqmn_i := hqmn fsi.toNat hfsi_le
            have hpofi_n : (BitVec.setWidth 64 (pov + fi)).toNat = pov.toNat + fi.toNat := by
              rw [bv64_setWidth_32, BitVec.toNat_add]; omega
            have hpofi_lt : (BitVec.setWidth 64 (pov + fi)).toNat < sbw.length := by
              rw [hpofi_n, hsbw_len, hpov_n]; omega
            c0_hfast_nogrp
            generalize hfjv : sbw[(BitVec.setWidth 64 (pov + fi)).toNat]'hpofi_lt = fjv
            have hfjv_lt : fjv.toNat < s7Qn (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf
                (fsi.toNat - 1) := by
              have h1 : sbw[s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf fsi.toNat +
                  fi.toNat]? = some fjv := by
                rw [← hpov_n, ← hpofi_n, List.getElem?_eq_getElem hpofi_lt, hfjv]
              rw [h1] at hfj_lt; simpa using hfj_lt
            have hrofj_n : (BitVec.setWidth 64 (rov + fjv)).toNat = rov.toNat + fjv.toNat := by
              rw [bv64_setWidth_32, BitVec.toNat_add]; omega
            have hrofi_n : (BitVec.setWidth 64 (rov + fi)).toNat = rov.toNat + fi.toNat := by
              rw [bv64_setWidth_32, BitVec.toNat_add]; omega
            refine wp_join_state0 (α := List (BitVec 32))
              (fun sbw1 mf => (FullMem c { st0 with scratch := { st0.scratch with
                  scratch_buf := sbw1 } } ⋆ R) mf ∧
                (1 < fsi.toNat → ∃ v1, sbw[s7Po (fidStepsCap c.scratch_cap)
                  st0.scratch.scratch_buf (fsi.toNat - 1) + fjv.toNat]? = some v1 ∧
                  sbw1 = sbw.set (s7Po (fidStepsCap c.scratch_cap) st0.scratch.scratch_buf
                    (fsi.toNat - 1) + fi.toNat) v1) ∧
                (¬ 1 < fsi.toNat → sbw1 = sbw))
              (fun _ sbw1 mf ⟨hmf, hsbw1a, hsbw1b⟩ => ?_) (fun Jf hJf => ?_)
            rotate_left
            · c0_hsplit
              · have hgt1 : 1 < fsi.toNat := by assumption
                have hpp_n := hpp hgt1
                have hgq' := hg.2.2.2.1 (fsi.toNat - 1) (by omega) (by omega)
                have hppfi_n : (BitVec.setWidth 64 (pp + fi)).toNat = pp.toNat + fi.toNat := by
                  rw [bv64_setWidth_32, BitVec.toNat_add]; omega
                have hppfj_n : (BitVec.setWidth 64 (pp + fjv)).toNat = pp.toNat + fjv.toNat := by
                  rw [bv64_setWidth_32, BitVec.toNat_add]; omega
                have hppfi_lt : (BitVec.setWidth 64 (pp + fi)).toNat < sbw.length := by
                  rw [hppfi_n, hsbw_len, hpp_n]; omega
                have hppfj_lt : (BitVec.setWidth 64 (pp + fjv)).toNat < sbw.length := by
                  rw [hppfj_n, hsbw_len, hpp_n]; omega
                c0_hfast
                refine hJf _ m ⟨hm, fun _ => ⟨sbw[(BitVec.setWidth 64 (pp + fjv)).toNat]'hppfj_lt,
                  ?_, ?_⟩, fun h => absurd hgt1 h⟩
                · rw [← hpp_n, ← hppfj_n, List.getElem?_eq_getElem hppfj_lt]
                · show List.set sbw _ _ = _; rw [hppfi_n, hpp_n]
              · c0_hfast
                exact hJf sbw mw ⟨hmw, fun h => absurd h (by assumption), fun _ => rfl⟩
            · have hsbw1_len : sbw1.length = c.scratch_cap := by
                by_cases hgt : 1 < fsi.toNat
                · obtain ⟨v1, _, hsbw1e⟩ := hsbw1a hgt; rw [hsbw1e]; simp [hsbw_len]
                · rw [hsbw1b hgt]; exact hsbw_len
              have hrofi_lt : (BitVec.setWidth 64 (rov + fi)).toNat < sbw1.length := by
                rw [hrofi_n, hsbw1_len, hrov_n]; omega
              have hrofj_lt : (BitVec.setWidth 64 (rov + fjv)).toNat < sbw1.length := by
                rw [hrofj_n, hsbw1_len, hrov_n]; omega
              have hfi1 : (fi + 1).toNat = fi.toNat + 1 := by
                rw [BitVec.toNat_add]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega
              c0_hfast
              refine ihi (fi + 1, ()) m (by dsimp only; omega) ⟨_, by omega, ?_, hm⟩
              show S7RowInv (fidStepsCap c.scratch_cap) c.scratch_cap (fsi.toNat - 1)
                st0.scratch.scratch_buf sbv (List.set sbw1 _ _) (Step7RowRefOk st0)
              rw [hrofi_n, hrov_n]
              by_cases hgt : 1 < fsi.toNat
              · obtain ⟨v1, hv1, hsbw1e⟩ := hsbw1a hgt; subst hsbw1e
                refine s7RowInv_step_pos hg hrinv (by omega) (by omega) (by omega) hfjv_lt hv1 ?_
                rw [← hrov_n, ← hrofj_n, List.getElem?_eq_getElem hrofj_lt]
              · have hq0 : fsi.toNat - 1 = 0 := by omega
                have hs1 := hsbw1b hgt; subst hs1
                have hrinv0 := hrinv; rw [hq0] at hrinv0 hfjv_lt hrov_n ⊢
                refine s7RowInv_step_zero hg hrinv0 (by have := hqmn 0 (by omega); omega)
                  hfjv_lt ?_
                rw [← hrov_n, ← hrofj_n, List.getElem?_eq_getElem hrofj_lt]
          · have hfi_eq : fi.toNat = mn_bv.toNat := by
              have : ¬ fi.toNat < mn_bv.toNat := hc; omega
            have hh_n : (BitVec.setWidth 64 (2 * sc + (fsi - 1))).toNat =
                2 * fidStepsCap c.scratch_cap + (fsi.toNat - 1) := by
              rw [bv64_setWidth_32, BitVec.toNat_add, BitVec.toNat_mul, hfm1, hsc_eq]
              simp only [show (2 : BitVec 32).toNat = 2 from rfl]; omega
            have hh_lt : (BitVec.setWidth 64 (2 * sc + (fsi - 1))).toNat < sbw.length := by
              rw [hh_n, hsbw_len]; omega
            c0_hfast
            refine ih (fsi - 1, ()) m (by dsimp only; omega) ⟨_, by omega, ?_, hm⟩
            show S7CompInv (fidStepsCap c.scratch_cap) c.scratch_cap best_k.toNat mn_bv.toNat
              (fsi - 1).toNat mn_bv st0.scratch.scratch_buf (List.set sbw _ _) (Step7RowRefOk st0)
            rw [hh_n, hfm1]
            exact s7CompInv_step hg hcomp hrinv (by omega) hfsi_le hmn
    · have hfsi0 : fsi.toNat = 0 := by
        have : ¬ 0 < fsi.toNat := by simpa using hc
        omega
      rw [hfsi0] at hcomp
      have hz := s7CompInv_zero hg hcomp hmn rfl
      have hcommF : ∀ st', S9DelOk c F0 F_next
          { st0 with scratch := { st0.scratch with scratch_buf := sbv } } st' →
          Step7BvaCommittedOk c st' best_k.toNat := fun st' hst' => by
        obtain ⟨hinv', hcv', _, hsc', _, hmono'⟩ := hst'
        have hcv'' : st'.core.cur_vars = s.core.cur_vars + 1 := hcv'.trans hcv0
        have hsb' : st'.scratch.scratch_buf = sbv := by rw [hsc']
        have hres' : st'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat := by
          rw [hsc']; exact hres0.trans hres
        dsimp only [Step7BvaCommittedOk]; rw [hsb']
        refine ⟨hbk_sc, hres', fun q hq => ?_⟩
        obtain ⟨hq0, hro1, hqn1, hrob, hent⟩ := hz q hq
        have hfr := (hmat.2.2.2.2.2 q (by omega)).1
        refine ⟨?_, ?_, fun qi hqi => ?_⟩
        · rw [hq0, hsb0s]; omega
        · show s7Ro _ sbv q + s7Qn _ sbv q ≤ _; rw [hro1, hqn1]; exact hrob
        · have hqi' : qi < mn_bv.toNat := by rw [← hqn1]; exact hqi
          exact step7RowRefOk_mono ((hent qi hqi').congr rfl rfl rfl) hmono'
            (Nat.le_of_eq hcv'.symm) hinv'.2.1.arena
      have hfs_ok : ∀ q ≤ best_k.toNat,
          (sbv[q]?.getD 0#32).toNat < 2 * c.max_vars := fun q hq => by
        have h1 := (hz q hq).1; rw [h1, hsb0s]
        have hcv_le := hinv.1.core_ok.cur_vars_le
        have h2 := (hmat.2.2.2.2.2 q (by omega)).1; omega
      have hd := s13_del_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch
        (stF := { st0 with scratch := { st0.scratch with scratch_buf := sbv } })
        (dm_bv := dm_bv) (brow_off := brow_off) (fresh := fresh) (mi0 := mi0)
        (dd1a := dd1a) (dd1b := dd1b) (garb_add0 := garb_add0) (irred_add0 := irred_add0)
        hsc_eq hbk_sc hfs_ok
        (fun q hq => by
          obtain ⟨_, hro1, _, hrob, _⟩ := hz q hq
          show s7Ro _ sbv q + _ ≤ _; rw [hro1]; exact hrob)
        (fun q hq j hj => ((hz q hq).2.2.2.2 j hj).congr rfl rfl rfl)
        (s9_fullDenseInvW_set_sb hinv0 hcomp.1) hmv
        (fun mv ga qsv st' mm hst' hmm => s13_final_wp hFillU64 (s := s)
          (stF := { st0 with scratch := { st0.scratch with scratch_buf := sbv } })
          (mv := mv) (garb_add := ga) (qsv := qsv) hfresh_nat hfresh1 hcv0 hfuel0 htm0 htr0
          hcommF hst' hmm hQ)
      unfold s13DelExpr at hd
      rw [heq2] at hd
      dsimp only [sGrp1, sStep, sElse, sDummyTup, sDummyVal, i64, i32] at hd
      exact hd

@[expose] def s13BvaBinFlExpr (h pFl : Val i64) (mi fresh q p14v : Val i32)
    (dd2 ok : Val .bool) (ga ia p12v : Val i64)
    (J1b : Cont [i32, .bool, .bool, i64, i64])
    (Jtop : Cont [.bool, .bool, i64, i64]) : Expr Val Cont [.bool] :=
  s9BOp32 (.lshr i32) (Arg.var fresh) (Arg.imm 1) fun p15 =>
  s9BZext (Arg.var p15) fun p16 => s9BPtr32 pFl p16 fun p18 =>
  s9BOp32 (.lshr i32) (Arg.var fresh) (Arg.imm 1) fun p19 =>
  s9BZext (Arg.var p19) fun p20 => s9BLd32 pFl p20 fun ldf =>
  s9BOp32 (.or i32) (Arg.var ldf) (Arg.imm 8) fun p23 =>
  s9BOp32 (.or i32) (Arg.var p23) (Arg.imm 16) fun p24 =>
  s9BOp32 (.or i32) (Arg.var p24) (Arg.imm 64) fun p25 =>
  Expr.store (Arg.var p25) (Arg.var p18)
    (s9BOp32 (.lshr i32) (Arg.var q) (Arg.imm 1) fun p26 =>
     s9BZext (Arg.var p26) fun p27 => s9BPtr32 pFl p27 fun p29 =>
     s9BOp32 (.lshr i32) (Arg.var q) (Arg.imm 1) fun p30 =>
     s9BZext (Arg.var p30) fun p31 => s9BLd32 pFl p31 fun ldq =>
     s9BOp32 (.or i32) (Arg.var ldq) (Arg.imm 8) fun p34 =>
     s9BOp32 (.or i32) (Arg.var p34) (Arg.imm 16) fun p35 =>
     s9BOp32 (.or i32) (Arg.var p35) (Arg.var p14v) fun p36 =>
     Expr.store (Arg.var p36) (Arg.var p29)
       (Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64,
                    args := (Arg.var p12v, Arg.imm 2, ()) } fun p37 =>
        Expr.jnz (Arg.var p37.fst)
          (Expr.jump J1b (Arg.var mi, Arg.var dd2, Arg.imm false, Arg.var ga,
            Arg.var ia, ()))
          (Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64,
                       args := (Arg.var p12v, Arg.imm 20, ()) } fun p38 =>
           Expr.jnz (Arg.var p38.fst)
             (Expr.jump J1b (Arg.var mi, Arg.var dd2, Arg.imm false, Arg.var ga,
               Arg.var ia, ()))
             (s9BOp64 (.add i64) (Arg.var h) (Arg.imm 760) fun p39 =>
              Expr.load i64 (Arg.var p39) fun ldi =>
              Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ne i64,
                           args := (Arg.var ldi, Arg.imm 0, ()) } fun p40 =>
              Expr.jnz (Arg.var p40.fst)
                (Expr.jump J1b (Arg.var mi, Arg.var dd2, Arg.imm false, Arg.var ga,
                  Arg.var ia, ()))
                (Expr.jump Jtop (Arg.var dd2, Arg.var ok, Arg.var ga,
                  Arg.var ia, ()))))))

private theorem s13_phase1b_bin_fl_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s st1 : FullState}
    {R : Mem 64 → Prop} {mi fresh q p14v : Val i32} {dd2 : Val .bool} {ga ia p12v : Val i64}
    {m1 : Mem 64} {J1b : Cont [i32, .bool, .bool, i64, i64]}
    {Jtop : Cont [.bool, .bool, i64, i64]}
    (hcv_s : s.core.cur_vars < c.max_vars)
    (hinv1' : FullDenseInvW c F0 F_next st1)
    (hcvm : st1.core.cur_vars = s.core.cur_vars + 1) (hfuelm : st1.core.fuel = s.core.fuel)
    (hsbm : st1.scratch.scratch_buf = s.scratch.scratch_buf)
    (htmm : st1.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrm : st1.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hmono : FidBvaArenaMono s.core st1.core)
    (hresm : st1.scratch.res_sz = s.scratch.res_sz)
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hq_lt : q.toNat < 2 * s.core.cur_vars)
    (hm1 : (FullMem c st1 ⋆ R) m1)
    (hJ1b : ∀ xs m,
      (match xs with
       | (_mi, _dd, _ok, _ga, _ia, ()) =>
         ∃ st' : FullState, S7StOk c F0 F_next s st' ∧ (FullMem c st' ⋆ R) m) →
      J1b xs m)
    (hJtop : ∀ xs m,
      (match xs with
       | (_dd', _ok', _ga', _ia', ()) =>
         ∃ st' : FullState, (FullMem c st' ⋆ R) m ∧ S7StOk c F0 F_next s st') →
      Jtop xs m) :
    wp Γ Q X (s13BvaBinFlExpr c.hdr c.pFlags mi fresh q p14v dd2 true ga ia p12v J1b Jtop) m1 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hfl1 : st1.core.flags.length = c.max_vars := hinv1'.1.core_ok.flags_len
  have hfr_shr :
      (BitVec.setWidth 64 (fresh >>> (1 : BitVec 32))).toNat < st1.core.flags.length := by
    rw [bv64_setWidth_32, bv32_lshr1_bv, hfl1, hfresh_nat]; omega
  have hfr_shr_n : (BitVec.setWidth 64 (fresh >>> (1 : Nat))).toNat < st1.core.flags.length := by
    rw [bv64_setWidth_32, bv32_lshr1_nat, hfl1, hfresh_nat]; omega
  have hq_shr : (BitVec.setWidth 64 (q >>> (1 : BitVec 32))).toNat < st1.core.flags.length := by
    rw [bv64_setWidth_32, bv32_lshr1_bv, hfl1]; omega
  have hq_shr_n : (BitVec.setWidth 64 (q >>> (1 : Nat))).toNat < st1.core.flags.length := by
    rw [bv64_setWidth_32, bv32_lshr1_nat, hfl1]; omega
  have hlen2 : ∀ (i j : Nat) (v w : BitVec 32),
      ((st1.core.flags.set i v).set j w).length = c.max_vars :=
    fun _ _ _ _ => by simp [hfl1]
  unfold s13BvaBinFlExpr s9BLd32 s9BPtr32 s9BZext s9BOp64 s9BOp32
  c0_hfast
  all_goals first
    | exact hJ1b (mi, dd2, false, ga, ia, ()) _
        ⟨_, ⟨fullDenseInvW_set_flags hinv1' (hlen2 _ _ _ _),
          hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩, by assumption⟩
    | exact hJtop (dd2, true, ga, ia, ()) _
        ⟨_, by assumption, ⟨fullDenseInvW_set_flags hinv1' (hlen2 _ _ _ _),
          hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩⟩

@[expose] def s13BvaBinArmExpr (h pFl : Val i64) (mi fresh q : Val i32) (dd' ok : Val .bool)
    (ga ia : Val i64) (J1b : Cont [i32, .bool, .bool, i64, i64])
    (Jtop : Cont [.bool, .bool, i64, i64]) : Expr Val Cont [.bool] :=
  s9BOp64 (.add i64) (Arg.var h) (Arg.imm 56) fun p10 =>
  Expr.load i64 (Arg.var p10) fun pw =>
  s9BOp32 (.xor i32) (Arg.var fresh) (Arg.imm 1) fun p11 =>
  Expr.call "full_add_bin" (as := [i64, i32, i32]) (bs := [i64])
    (Arg.var h, Arg.var p11, Arg.var q, ()) fun p12 =>
  Expr.group (fun _ => Blocks.cons (fun (p13 : Tup Val [.bool]) =>
    Expr.group (fun _ => Blocks.cons (fun (p14 : Tup Val [i32]) =>
      s13BvaBinFlExpr h pFl mi fresh q p14.fst p13.fst ok ga ia p12.fst J1b Jtop) Blocks.nil)
      fun Js3 =>
    s9BOp32 (.and i32) (Arg.var q) (Arg.imm 1) fun pa =>
    s9BCmp32 .ne (Arg.var pa) (Arg.imm 0) fun pc =>
    Expr.jnz (Arg.var pc) (Expr.jump Js3.fst (Arg.imm 64, ()))
      (Expr.jump Js3.fst (Arg.imm 32, ()))) Blocks.nil) fun Js2 =>
  s9BOp64 (.add i64) (Arg.var h) (Arg.imm 56) fun pw2 =>
  Expr.load i64 (Arg.var pw2) fun ld1 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ult i64,
              args := (Arg.var ld1, Arg.var pw, ()) } fun cw =>
  Expr.jnz (Arg.var cw.fst) (Expr.jump Js2.fst (Arg.imm true, ()))
    (Expr.jump Js2.fst (Arg.var dd', ()))

theorem s13_phase1b_bin_arm_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddBin : FidAddBinHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {mi fresh q : Val i32} {dd' : Val .bool} {ga ia : Val i64}
    {mm : Mem 64} {J1b : Cont [i32, .bool, .bool, i64, i64]}
    {Jtop : Cont [.bool, .bool, i64, i64]}
    (hcv_s : s.core.cur_vars < c.max_vars)
    (hinvm : FullDenseInvW c F0 F_next stm)
    (hcvm : stm.core.cur_vars = s.core.cur_vars + 1) (hfuelm : stm.core.fuel = s.core.fuel)
    (hsbm : stm.scratch.scratch_buf = s.scratch.scratch_buf)
    (htmm : stm.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrm : stm.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hmono : FidBvaArenaMono s.core stm.core)
    (hresm : stm.scratch.res_sz = s.scratch.res_sz)
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (_hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hq_lt : q.toNat < 2 * s.core.cur_vars)
    (hresm_ent : (cnfOfClauses F_next).EntailsClause (cnfClause [(fresh ^^^ 1#32).toNat, q.toNat]))
    (hmm : (FullMem c stm ⋆ R) mm)
    (hJ1b : ∀ xs m,
      (match xs with
       | (_mi, _dd, _ok, _ga, _ia, ()) =>
         ∃ st1 : FullState, S7StOk c F0 F_next s st1 ∧ (FullMem c st1 ⋆ R) m) →
      J1b xs m)
    (hJtop : ∀ xs m,
      (match xs with
       | (_dd', _ok', _ga', _ia', ()) =>
         ∃ st1 : FullState, (FullMem c st1 ⋆ R) m ∧ S7StOk c F0 F_next s st1) →
      Jtop xs m) :
    wp Γ Q X (s13BvaBinArmExpr c.hdr c.pFlags mi fresh q dd' true ga ia J1b Jtop) mm := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hclm := hinvm.1.core_ok
  unfold s13BvaBinArmExpr s9BOp64 s9BOp32 s9BCmp32
  c0_hsteps; c0_call hAddBin
  refine ⟨c, F0, F_next, stm, R, rfl, hinvm.1, hinvm.2.1, hinvm.2.2.2.2.2.1,
    fun _ _ => by simpa only [show (1 : BitVec 32) = 1#32 from rfl] using hresm_ent,
    hmm, fun _ _ fl1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1' hw1' _ _ _ hms1' => ?_⟩
  have hinv1' := s9_fullDenseInvW_of_addBin hinvm hlen1' hw1'
  c0_hfast_nogrp
  refine wp_join_group (ts := [.bool]) (fun _ md2 => md2 = m1)
    (fun _ (dd2, ()) md2 hmd2 => by
      subst md2; c0_hfast_nogrp
      refine wp_join_group (ts := [i32]) (fun (_, ()) mf => mf = m1)
        (fun _ (p14v, ()) mf hmf => by
          subst hmf
          exact s13_phase1b_bin_fl_wp hcv_s hinv1' hcvm hfuelm hsbm htmm htrm hmono
            hresm hfresh_nat hq_lt hms1' hJ1b hJtop)
        (fun Jt hJt => by c0_hfast <;> exact hJt _ m1 rfl))
    (fun Jdd2 hJdd2 => by c0_hfast <;> exact hJdd2 _ m1 rfl)

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

end
