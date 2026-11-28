/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.WpScan0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Candidate-Scan WP Proof for `Src.Factor` (`full_bva_scan_cands`)

Proves `full_bva_scan_cands_wp` (`step13BvaScanCandsSpec`) using `s13_scan_large_wp`
over `Proof.Factor.WpScan0` (`0` legacy imports, `0` placeholders, `XPost`-polymorphic).
-/

set_option autoImplicit false

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

public section

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

@[local bv_c0] private theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem bv32_one_toNat : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl

theorem s13_scan_large_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X → Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {row_off cur_qn : Val i32} {init_lits : Val i64} {J Jq : Cont [i32, i32, i32, i64]}
    {nql ncntd qi : Val i32} {ticks r_clines : Val i64} {qw : Val i32}
    {Js : Cont [i32, i32, i64]} {ar ws ws1 ws2 : List (BitVec 32)} {ant : BitVec 64} {ml : Mem 64}
    (hslen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hdw : DenseWatchesInv F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (hlm_clr : ∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarb s qw.toNat = false)
    (hws_l : ws.length = 2 * c.max_vars) (hws1_l : ws1.length = 2 * c.max_vars)
    (har_l : ar.length = c.arena_cap) (hnc_le : ncntd.toNat ≤ 2 * c.max_vars)
    (hbvaq : S13ScanArBvaqInv c s ar ws2 0 nql.toNat)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hcntd_ok : ∀ i < ncntd.toNat,
      (ws1[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧ (ws1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hml : (FullMem c
      { core := { s.core with arena := ar },
        scratch :=
          { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2, ant_sz := ant } } ⋆
      R) ml)
    (hExit : ∀ (nql_j nc_j : BitVec 32) (ticks_j : BitVec 64) ar_j ws_j ws1_j ql_j mj,
      nc_j.toNat ≤ 2 * c.max_vars → ws_j.length = 2 * c.max_vars → ws1_j.length = 2 * c.max_vars →
      S13ScanArBvaqInv c s ar_j ql_j 0 nql_j.toNat →
      FullWitnessInv c F0 F_cur { s.core with arena := ar_j } →
      (∀ i < nc_j.toNat,
        (ws1_j[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws1_j[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (FullMem c
        { core := { s.core with arena := ar_j },
          scratch :=
            { s.scratch with wsort := ws_j, work_stk1 := ws1_j, work_stk2 := ql_j, ant_sz := ant } }
        ⋆ R) mj →
      Js (nql_j, nc_j, ticks_j, ()) mj) :
    wp Γ Q X (s13ScanLarge row_off cur_qn c.hdr init_lits c.pVals c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pWsort c.pWorkStk1 c.pFlags c.pWorkStk2 c.pRepr r_clines
      J Jq nql ncntd qi ticks qw Js) ml := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hrepr_len := hcl.repr_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  let mkSt (ar' : List (BitVec 32)) (lm : List (BitVec 8)) (ws' ws1' ws2' : List (BitVec 32))
      (ant' : BitVec 64) : FullState :=
    { core := { s.core with arena := ar', lit_mark := lm }
      scratch :=
        { s.scratch with wsort := ws', work_stk1 := ws1', work_stk2 := ws2', ant_sz := ant' } }
  dsimp only [mkSt] at hml
  have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
  have hqw_sz_s : (s.core.arena[qw.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSizeCore s.core qw.toNat := by
    unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have har_lits_eq := s13_scan_cands_ar_lits_eq hcl hw hbvaq hqw_ref
  have hqw_sz_eq : (ar[qw.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSizeCore s.core qw.toNat := by
    have h1 := har_lits_eq.1
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
    rw [Option.some.inj h1]; exact hqw_sz_s
  have hqw2_n : (BitVec.setWidth 64 qw + 2).toNat = qw.toNat + 2 := by
    change (BitVec.setWidth 64 qw + 2#64).toNat = _; simp only [bv_c0]; omega
  have hqw2_mod : (qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = qw.toNat + 2 := by
    rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
  have hqw2_ar : (BitVec.setWidth 64 qw + 2).toNat < ar.length := by
    rw [hqw2_n, har_l]; have := hqw_wf.1; omega
  let csz_bv := ar[(BitVec.setWidth 64 qw + 2).toNat]'hqw2_ar
  have hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat := by
    dsimp only [csz_bv]; simp only [hqw2_n]; exact hqw_sz_eq
  have hcsz_mod : csz_bv = ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
      rw [hqw2_mod]; omega) := by
    dsimp only [csz_bv]; simp only [hqw2_n, hqw2_mod]
  dsimp only [s13ScanLarge, s13ScanHdr, s13Step, s13Steps, s13StepZ, s13StepsZ, s13Ld64, s13Ld32,
    s13Call64, s13Then, s13Else, s13GrpK4q, s13GrpB4q, s13GrpK3s, s13GrpB4m, s13GrpK4c, s13GrpK5mp,
    s13DummyVal, s13DummyTup, full_bva_scan_cands_body]
  c0_hfast_nogrp
  refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8))
    (fun ⟨min_l, min_d, fc, jf, _⟩ => (min_l, min_d, fc, jf, ()))
    (fun ⟨min_l, _min_d, _, _, lm1⟩ _mf =>
      LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 csz_bv.toNat lm1 ∧
      (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) ∧
      (FullMem c (mkSt ar lm1 ws ws1 ws2 ant) ⋆ R) _mf)
    (fun _ ⟨min_l, min_d, fc, _jf, lm1⟩ mf ⟨hlm1_inv, hmin_ok, hmf⟩ => ?_)
    (fun Jm hJm => ?_)
  · dsimp only [mkSt] at hmf
    c0_hfast_nogrp
    refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 64 × BitVec 32 ×
        List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × List (BitVec 32))
      (fun ⟨nql_j, nc_j, ticks_j, jf_j, _, _, _, _⟩ => (nql_j, nc_j, ticks_j, jf_j, ()))
      (fun ⟨nql_j, nc_j, _ticks_j, _jf_j, ar_j, ws_j, ws1_j, ql_j⟩ mj =>
        nc_j.toNat ≤ 2 * c.max_vars ∧
        ws_j.length = 2 * c.max_vars ∧
        ws1_j.length = 2 * c.max_vars ∧
        S13ScanArBvaqInv c s ar_j ql_j 0 nql_j.toNat ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar_j } ∧
        (∀ i < nc_j.toNat,
          (ws1_j[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
          (ws1_j[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        (FullMem c (mkSt ar_j lm1 ws_j ws1_j ql_j ant) ⋆ R) mj)
      (fun _ ⟨nql_j, nc_j, ticks_j, _jf_j, ar_j, ws_j, ws1_j, ql_j⟩ mj
        ⟨hnc_j, hws_j_l, hws1_j_l, hbvaq_j, hw_j, hcntd_j, hmj⟩ => ?_)
      (fun Jc_join hJc_join => ?_)
    · clear hmf
      dsimp only [mkSt] at hmj
      have har_lits := (s13_scan_cands_ar_lits_eq hcl hw hbvaq_j hqw_ref).2
      have har_j_l := hbvaq_j.1
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (j, ()) mj => ∃ lmj, j.toNat ≤ csz_bv.toNat ∧
          LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat j.toNat csz_bv.toNat lmj ∧
          (FullMem c (mkSt ar_j lmj ws_j ws1_j ql_j ant) ⋆ R) mj)
        (fun (j, ()) _ => csz_bv.toNat - j.toNat)
        (fun Jc2 hJc2 => by
          c0_hfast; exact hJc2 (0#32, ()) _ ⟨lm1, Nat.zero_le _, hlm1_inv, hmj⟩)
        (fun Jc2 (j, ()) mj ⟨lmj, hj_le, hlmj_inv_j, hmj_c2⟩ ihc2 => ?_)
      clear hmj; dsimp only [mkSt] at hmj_c2
      have hlmj_l := hlmj_inv_j.1
      c0_hsplit
      · have hj_lt : j.toNat < csz_bv.toNat := by
          rw [hcsz_mod]; simpa only [] using (by assumption : _)
        have hcj_eq : ar_j[qw.toNat + 3 + j.toNat]'(by omega) =
            s.core.arena[qw.toNat + 3 + j.toNat]'(by omega) := by
          have h1 := har_lits j.toNat (by omega)
          rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
          exact Option.some.inj h1
        have hcj_lt : (s.core.arena[qw.toNat + 3 + j.toNat]'(by omega)).toNat <
            2 * s.core.cur_vars :=
          hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
            (fullArenaClauseLitsCore_getElem (by omega) (by omega)))
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
        have hidx_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
            qw.toNat + 3 + j.toNat := by
          change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
          simp only [bv_c0]; omega
        have hidx_ar : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat <
            ar_j.length := by rw [hidx_n, har_j_l]; omega
        have hcj_lm : (BitVec.setWidth 64
            (ar_j[(BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat]'hidx_ar)).toNat <
            lmj.length := by simp only [hidx_n, hset, hcj_eq]; omega
        c0_hfast
        simp only [hidx_n, hset] at hm
        try simp only [bv8_trunc_and_fd] at hm
        have hstep : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat (j.toNat + 1)
            csz_bv.toNat (lmj.set (ar_j[qw.toNat + 3 + j.toNat]'(by omega)).toNat
              ((lmj[(ar_j[qw.toNat + 3 + j.toNat]'(by omega)).toNat]'(by
                rw [hcj_eq]; omega)) &&& 0xFD#8)) := by
          have h0 := lmBit2Inv_clear_step hlm_len
            (fun l hl => (bv8_bit_zero_of_and_fe (hlm_clr l hl)).1)
            hlmj_inv_j hj_lt (by omega) (by omega)
          simpa only [← hcj_eq] using h0
        exact ihc2 (j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
          ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep, hm⟩
      · have hj_eq : j.toNat = csz_bv.toNat := by
          rw [hcsz_mod] at hj_le ⊢
          have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
            rw [hqw2_mod]; omega)).toNat := by simpa only [] using (by assumption : _)
          omega
        rw [hj_eq] at hlmj_inv_j
        have hlm_rest : lmj = s.core.lit_mark := lmBit2Inv_done hlm_len hlmj_inv_j
        rw [hlm_rest] at hmj_c2; c0_hfast
        exact hExit nql_j nc_j ticks_j ar_j ws_j ws1_j ql_j mj
          hnc_j hws_j_l hws1_j_l hbvaq_j hw_j hcntd_j hmj_c2
    · c0_hsplit
      · c0_hsplit
        · dsimp only
          have hmin_ne : min_l ≠ 0xFFFFFFFF#32 := hc; clear hc
          have hml_lt : min_l.toNat < 2 * s.core.cur_vars := hmin_ok hmin_ne
          have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
          have hml_sl := hdw.slices min_l.toNat hml_lt
          have h2ml_n : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat = 2 * min_l.toNat := by
            simp only [bv_c0]; omega
          have h2ml_mod : 2 * min_l.toNat % 2 ^ 64 = 2 * min_l.toNat :=
            Nat.mod_eq_of_lt (by omega)
          have hmoff_eq : (s.core.wvec[2 * min_l.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core min_l.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hmsz_eq : (s.core.wvec[2 * min_l.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core min_l.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let moff0 := fullWatchOffCore s.core min_l.toNat
          let msz0 := fullWatchSizeCore s.core min_l.toNat
          have h2ml_wv : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat <
              s.core.wvec.length := by rw [h2ml_n]; omega
          have h2ml1_wv : ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1#64).toNat < _
            simp only [bv_c0]; omega
          have hmd_repr : (BitVec.setWidth 64 min_d).toNat < 2 ^ 64 := by omega
          have hml_repr_w : (BitVec.setWidth 64 min_l).toNat < s.core.repr.length := by
            rw [hset, hrepr_len]; omega
          c0_hfast_nogrp
          fid_call hClines
          intro r_clines_min
          c0_hfast_nogrp
          refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 × BitVec 32 ×
              List (BitVec 32) × List (BitVec 8) × List (BitVec 32) × List (BitVec 32) ×
              List (BitVec 32))
            (fun ⟨nql2, nc2, ticks2, mp2, nnou2, _, _, _, _, _⟩ =>
              (nql2, nc2, ticks2, mp2, nnou2, ()))
            (fun ⟨nql2, nc2, _, _, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp =>
              nc2.toNat ≤ 2 * c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
              ws12.length = 2 * c.max_vars ∧ S13ScanArBvaqInv c s ar2 ql2 0 nql2.toNat ∧
              S13LmBit4Inv c lm1 ql2 0 nnou2.toNat lm2 ∧
              FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
              (∀ i < nc2.toNat,
                (ws12[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
                (ws12[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
              (FullMem c (mkSt ar2 lm2 ws2' ws12 ql2 ant) ⋆ R) mmp)
            (fun _ ⟨nql2, nc2, ticks2, _mp2, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp
                ⟨hnc2, hws2'_l, hws12_l, hbvaq2, hlm4_2, hw2, hcntd2, hmmp⟩ => ?_)
            (fun Jmp hJmp => ?_)
          · clear hmf
            dsimp only [mkSt] at hmmp
            have hql2_l := hbvaq2.2.1
            refine wp_loop_inv
              (fun (j, ()) mj4 => ∃ lmj4,
                j.toNat ≤ nnou2.toNat ∧ S13LmBit4Inv c lm1 ql2 j.toNat nnou2.toNat lmj4 ∧
                (FullMem c (mkSt ar2 lmj4 ws2' ws12 ql2 ant) ⋆ R) mj4)
              (fun (j, ()) _ => nnou2.toNat - j.toNat)
              (fun Jc4 hJc4 => by
                c0_hfast; exact hJc4 (0#32, ()) mmp ⟨lm2, Nat.zero_le _, hlm4_2, hmmp⟩)
              (fun Jc4 (j, ()) mj4 ⟨lmj4, hj4_le, hlmj4, hmj4⟩ ihc4 => ?_)
            clear hmmp; dsimp only [mkSt] at hmj4
            have hlmj4_l := hlmj4.1; have hnn2_le := hlmj4.2.1
            c0_hsplit
            · have hj4_lt : j.toNat < nnou2.toNat := by assumption
              have hj4_1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
              have hmxj : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 j).toNat =
                  c.max_vars + j.toNat := by simp only [bv_c0]; omega
              have hmxj_ql : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 j).toNat <
                  ql2.length := by rw [hmxj, hql2_l]; omega
              have ⟨hcl_lt, hstep4⟩ := s13LmBit4Inv_clear_step hlm1_inv.1 hql2_l
                (fun l hl => by
                  rw [lmBit2Inv_preserves_bit2 hlm1_inv hl]
                  exact (bv8_bit_zero_of_and_fe (hlm_clr l hl)).2)
                hlmj4 hj4_lt
              have hcl_lm : (BitVec.setWidth 64 (ql2[(BitVec.ofNat 64 c.max_vars +
                  BitVec.setWidth 64 j).toNat]'hmxj_ql)).toNat < lmj4.length := by
                simp only [hmxj, hset]; omega
              c0_hfast
              simp only [hmxj] at hm; simp only [hset] at hm
              try simp only [bv8_trunc_and_fb] at hm
              exact ihc4 (j + 1#32, ()) m (by dsimp only; rw [hj4_1]; omega)
                ⟨_, by rw [hj4_1]; omega, by rw [hj4_1]; exact hstep4, hm⟩
            · have hj4_eq : j.toNat = nnou2.toNat := by omega
              rw [hj4_eq] at hlmj4
              have hlm_eq1 : lmj4 = lm1 := s13LmBit4Inv_done hlm1_inv.1 hlmj4
              rw [hlm_eq1] at hmj4
              c0_hfast
              exact hJc_join ⟨nql2, nc2, ticks2, j, ar2, ws2', ws12, ql2⟩ _
                ⟨hnc2, hws2'_l, hws12_l, hbvaq2, hw2, hcntd2, hmj4⟩
          · have h21 : ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1).toNat =
                2 * min_l.toNat + 1 := by
              change ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1#64).toNat = _
              simp only [bv_c0]; omega
            have hmp := s13_scan_mp_wp (Γ := Γ) (Q := Q) (X := X) (c := c) (F0 := F0)
              (F_cur := F_cur) (s := s) (R := R) (row_off := row_off) (cur_qn := cur_qn)
              (init_lits := init_lits) (J := fun _ _ => False) (Jq := fun _ _ => False)
              (nql := nql) (ncntd := ncntd) (qi := qi) (ticks := ticks) (r_clines := r_clines)
              (qw := qw) (Js := Js) (csz_bv := csz_bv) (Jm := fun _ _ => False)
              (min_l := min_l) (min_d := min_d) (fc := fc) (jf := 0#32) (Jc_join := Jc_join)
              (moff := s.core.wvec[(BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat]'h2ml_wv)
              (msz := s.core.wvec[((BitVec.setWidth 64 min_l <<< (1 : Nat)) +
                1).toNat]'h2ml1_wv)
              (r_clines_min := r_clines_min) (Jmp := Jmp)
              hslen hw hdw hcl0
                (fun x hx => Or.inr (hw.arena.lits_lt qw.toNat hqw_ref hqw_ng x hx))
                (fun l hl => by
                  have h1 := congrArg (· &&& 6#8) (hlm_clr l (by omega))
                  rwa [BitVec.and_assoc, show (0xFE#8 &&& 6#8) = 6#8 from rfl,
                    BitVec.zero_and] at h1)
                hqw_ref hcsz_nat hlm1_inv
                hml_lt (by simpa only [h2ml_n] using hmoff_eq)
                (by simpa only [h21] using hmsz_eq)
                hnc_le hws_l hws1_l hbvaq hw_ar hcntd_ok hmf
              (fun nql2 nc2 ticks2 mp2 nnou2 ar2 lm2 ws2' ws12 ql2 mmp
                hnc2 hws2' hws12 hbvaq2 hlm42 hw2 hcntd2 hmmp =>
                hJmp ⟨nql2, nc2, ticks2, mp2, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp
                  ⟨hnc2, hws2', hws12, hbvaq2, hlm42, hw2, hcntd2, hmmp⟩)
            dsimp only [s13ScanMp, s13ScanLarge, s13ScanHdr, s13Step, s13Steps, s13StepZ,
              s13StepsZ, s13Ld64, s13Ld32, s13Call64, s13Then, s13Else, s13GrpK4q, s13GrpB4q,
              s13GrpK3s, s13GrpB4m, s13GrpK4c, s13GrpK5mp, s13DummyVal, s13DummyTup,
              full_bva_scan_cands_body] at hmp
            exact hmp
        · have hmin_eq : min_l = 0xFFFFFFFF#32 := hc; clear hc
          c0_hfast
          exact hJc_join ⟨nql, ncntd, ticks + 1#64, _, ar, ws, ws1, ws2⟩ mf
            ⟨hnc_le, hws_l, hws1_l, hbvaq, hw_ar, hcntd_ok, hmf⟩
      · have hfc_ne : fc ≠ 1#32 := hc; clear hc
        c0_hfast
        exact hJc_join ⟨nql, ncntd, ticks + 1#64, _, ar, ws, ws1, ws2⟩ mf
          ⟨hnc_le, hws_l, hws1_l, hbvaq, hw_ar, hcntd_ok, hmf⟩
  · refine wp_loop_inv
      (fun (min_l, min_d, fc, j, ()) mj => ∃ lmj, j.toNat ≤ csz_bv.toNat ∧
        LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj ∧
        (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) ∧
        (FullMem c (mkSt ar lmj ws ws1 ws2 ant) ⋆ R) mj)
      (fun (_, _, _, j, _) _ => csz_bv.toNat - j.toNat)
      (fun JmL hJmL => by
        c0_hfast; exact hJmL (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) ml
          ⟨s.core.lit_mark, Nat.zero_le _, lmBit2Inv_init hlm_len,
           fun h => absurd rfl h, hml⟩)
      (fun JmL (min_l, min_d, fc, j, ()) mj ⟨lmj, hj_le, hlmj_inv, hmin_ok, hmj⟩ ihm => ?_)
    clear hml; dsimp only [mkSt] at hmj
    have hlmj_l := hlmj_inv.1
    c0_hsplit
    · have hj_lt : j.toNat < csz_bv.toNat := by
        rw [hcsz_mod]; simpa only [] using (by assumption : _)
      have hj_sz : j.toNat < fullArenaClauseSizeCore s.core qw.toNat := by
        rw [← hcsz_nat]; exact hj_lt
      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
      have hqwj_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
          qw.toNat + 3 + j.toNat := by
        change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
        simp only [bv_c0]; omega
      have hl_eq : ar[qw.toNat + 3 + j.toNat]'(by omega) =
          s.core.arena[qw.toNat + 3 + j.toNat]'(by omega) := by
        have h1 := har_lits_eq.2 j.toNat hj_sz
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
        exact Option.some.inj h1
      have hl_lt : (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        rw [hl_eq]; exact hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
          (fullArenaClauseLitsCore_getElem hj_sz (by omega)))
      have h2l1_n : ((BitVec.setWidth 64 (ar[qw.toNat + 3 + j.toNat]'(by omega)) <<<
          (1 : Nat)) + 1).toNat = 2 * (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat + 1 := by
        let x := ar[qw.toNat + 3 + j.toNat]'(by omega)
        change ((BitVec.setWidth 64 x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1
        have hx : x.toNat < 2 ^ 32 := x.isLt
        rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64),
          show (1#64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.pow_one,
          Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]
        exact (Nat.mod_eq_of_lt (by omega : x.toNat * 2 + 1 < 2 ^ 64)).trans (by omega)
      have hqwj_ar : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat <
          ar.length := by rw [hqwj_n, har_l]; omega
      have hl_lm : (BitVec.setWidth 64
          (ar[(BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
          lmj.length := by simp only [hqwj_n, hset]; omega
      have h2l1_wv : ((BitVec.setWidth 64
          (ar[(BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar) <<<
          (1 : Nat)) + 1).toNat < s.core.wvec.length := by
        simp only [hqwj_n, h2l1_n]; omega
      have hl_repr : (BitVec.setWidth 64
          (ar[(BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
          s.core.repr.length := by rw [hrepr_len]; omega
      have hlmj_lift := s13_scan_cands_lmj_lift hlmj_inv hj_le
      have hl_lt_s : (s.core.arena[qw.toNat + 3 + j.toNat]'(by omega)).toNat <
          2 * c.max_vars := by rw [← hl_eq]; omega
      have hstep2_base : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1)
          (lmj.set (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat
            ((lmj[(ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat]'(by omega)) ||| 2#8)) := by
        have h0 := lmBit2Inv_or2 hlm_len hlmj_inv (by omega) hl_lt_s
        simpa only [← hl_eq] using h0
      c0_hfast
      · exact hJm ⟨min_l, min_d, fc + 1#32, j, lmj⟩ mj ⟨hlmj_lift, hmin_ok, hmj⟩
      · exact ihm (min_l, min_d, fc + 1#32, j + 1#32, ()) mj (by dsimp only; rw [hj1]; omega)
          ⟨lmj, by rw [hj1]; omega, by rw [hj1]; exact lmBit2Inv_skip hlmj_inv, hmin_ok, hmj⟩
      · refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
          ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base,
           fun _ => by simp only [hqwj_n]; exact hl_lt, ?_⟩
        simp only [hqwj_n, hset] at hm; try simp only [bv8_trunc_or_2] at hm
        exact hm
      · refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
          ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base,
           fun _ => by simp only [hqwj_n]; exact hl_lt, ?_⟩
        simp only [hqwj_n, hset] at hm; try simp only [bv8_trunc_or_2] at hm
        exact hm
      · refine ihm (min_l, min_d, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
          ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base, hmin_ok, ?_⟩
        simp only [hqwj_n, hset] at hm; try simp only [bv8_trunc_or_2] at hm
        exact hm
    · have hj_eq : j.toNat = csz_bv.toNat := by
        rw [hcsz_mod] at hj_le ⊢
        have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
          rw [hqw2_mod]; omega)).toNat := by simpa only [] using (by assumption : _)
        omega
      rw [hj_eq] at hlmj_inv; c0_hfast
      exact hJm ⟨min_l, min_d, fc, j, lmj⟩ mj ⟨hlmj_inv, hmin_ok, hmj⟩

private def s13ScanClearRetExpr (c : FullCfg) (nql_s nc_s : Val i32) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i32]])
    (fun Js =>
      Blocks.cons
        (fun p_1 =>
          Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                      args := (Arg.var p_1.fst, Arg.var nql_s, ()) } fun p_2 =>
          Expr.jnz (Arg.var p_2.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var p_1.fst, ()) } fun pa =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var pa.fst, Arg.imm 4, ()) } fun pb =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWorkStk2, Arg.var pb.fst, ()) } fun pc =>
             Expr.load i32 (Arg.var pc.fst) fun ld1 =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var ld1, ()) } fun pd =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var pd.fst, Arg.imm 4, ()) } fun pe =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pArena, Arg.var pe.fst, ()) } fun pf =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var p_1.fst, ()) } fun p3 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p3.fst, Arg.imm 4, ()) } fun p4 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWorkStk2, Arg.var p4.fst, ()) } fun p5 =>
             Expr.load i32 (Arg.var p5.fst) fun ld2 =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var ld2, ()) } fun p6 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p6.fst, Arg.imm 4, ()) } fun p7 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pArena, Arg.var p7.fst, ()) } fun p8 =>
             Expr.load i32 (Arg.var p8.fst) fun ld3 =>
             Expr.let_ { sig := [i32], code := OpCode.not i32,
                         args := (Arg.imm 33554432, ()) } fun p9 =>
             Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                         args := (Arg.var ld3, Arg.var p9.fst, ()) } fun p10 =>
             Expr.store (Arg.var p10.fst) (Arg.var pf.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var p_1.fst, Arg.imm 1, ()) } fun pn =>
                Expr.jump Js.fst (Arg.var pn.fst, ())))
            (Expr.ret (Arg.var nc_s, ())))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))

private theorem s13_scan_clear_ret_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {init_lits : Val i64} {nql_s nc_s : Val i32}
    {ar_s ws_s ws1_s ql_s : List (BitVec 32)} {ant_s : BitVec 64} {m0 : Mem 64}
    (hcl : s.core.LengthsOk c) (hsc : s.scratch.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core)
    (hnc_s : nc_s.toNat ≤ 2 * c.max_vars)
    (hws_s_l : ws_s.length = 2 * c.max_vars) (hws1_s_l : ws1_s.length = 2 * c.max_vars)
    (hbvaq_s : S13ScanArBvaqInv c s ar_s ql_s 0 nql_s.toNat)
    (hcntd_s : ∀ i < nc_s.toNat,
      (ws1_s[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
      (ws1_s[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hm0 : (FullMem c (FullState.mk { s.core with arena := ar_s }
      { s.scratch with
          wsort := ws_s, work_stk1 := ws1_s, work_stk2 := ql_s, ant_sz := ant_s }) ⋆ R) m0)
    (hQ : ∀ (nc' : BitVec 32) ws' ws1' ws2' ant' m',
      (FullState.mk s.core { s.scratch with
          wsort := ws', work_stk1 := ws1', work_stk2 := ws2', ant_sz := ant' }).LengthsOk c →
      nc'.toNat ≤ 2 * c.max_vars →
      (∀ i < nc'.toNat, (ws1'[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (FullMem c (FullState.mk s.core { s.scratch with
          wsort := ws', work_stk1 := ws1', work_stk2 := ws2', ant_sz := ant' }) ⋆ R) m' →
      Q (nc', ()) m') :
    wp Γ Q X (s13ScanClearRetExpr c nql_s nc_s) m0 := by
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le
  have hql_s_l := hbvaq_s.2.1; have hnql_s_le := hbvaq_s.2.2.1
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  unfold s13ScanClearRetExpr
  refine wp_loop_inv
    (fun (ci, ()) mci => ∃ arci,
      ci.toNat ≤ nql_s.toNat ∧ S13ScanArBvaqInv c s arci ql_s ci.toNat nql_s.toNat ∧
      ∃ ant', (FullMem c (FullState.mk { s.core with arena := arci }
        { s.scratch with
            wsort := ws_s, work_stk1 := ws1_s, work_stk2 := ql_s, ant_sz := ant' }) ⋆ R) mci)
    (fun (ci, ()) _ => nql_s.toNat - ci.toNat)
    (fun Jc hJc => by c0_hfast; exact hJc (0#32, ()) m0 ⟨ar_s, Nat.zero_le _, hbvaq_s, ant_s, hm0⟩)
    (fun Jc (ci, ()) mci ⟨arci, hci_le, hbvaq_ci, ant', hmci⟩ ihc => ?_)
  have harci_l := hbvaq_ci.1
  c0_hsplit
  · have hci_lt : ci.toNat < nql_s.toNat := by assumption
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
    have hidx_ref := (hbvaq_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt).1
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hidx_ref
    have hidx_wf := hw.arena.refs_wf _ hidx_ref
    have hstep := s13ScanArBvaqInv_clear_step har_len hbvaq_ci hci_lt (by omega)
    have hci_ql : (BitVec.setWidth 64 ci).toNat < ql_s.length := by rw [hset, hql_s_l]; omega
    have hidx_ar : (BitVec.setWidth 64 (ql_s[(BitVec.setWidth 64 ci).toNat]'hci_ql)).toNat <
        arci.length := by
      simp only [hset]; have := hidx_wf.1; rw [harci_l]; omega
    c0_hfast
    refine ihc (ci + 1#32, ()) _ (by dsimp only; rw [hci1]; omega)
      ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ant', ?_⟩
    simp only [hset] at *; assumption
  · have hci_eq : ci.toNat = nql_s.toNat := by omega
    rw [hci_eq] at hbvaq_ci
    have har_rest : arci = s.core.arena := s13ScanArBvaqInv_done har_len hbvaq_ci
    rw [har_rest] at hmci; c0_hfast
    exact hQ nc_s ws_s ws1_s ql_s ant' mci
      ⟨hcl, { hsc with wsort_len := hws_s_l, work_stk1_len := hws1_s_l, work_stk2_len := hql_s_l }⟩
      hnc_s hcntd_s hmci

theorem full_bva_scan_cands_wp (Γ : Env)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X → Γ "full_bva_clines_fid" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13BvaScanCandsSpec a m Q X →
      Func.wp Γ full_bva_scan_cands_body a m Q X := by
  rintro ⟨h, row_off, cur_qn, init_lits, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hslen, hw, _hnodup, _hext, hl0, hdm, _hil_le, hlm_clr, hrow_bd,
     hrow_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok; have hsc := hslen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hrepr_len := hcl.repr_len
  have hsb_len := hsc.scratch_buf_len; have hwsort_len := hsc.wsort_len
  have hws1_len := hsc.work_stk1_len; have hws2_len := hsc.work_stk2_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (ws ws1 ws2 : List (BitVec 32))
      (ant : BitVec 64) : FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2, ant_sz := ant } }
  unfold Func.wp full_bva_scan_cands_body
  c0_hfast_nogrp
  refine wp_call_of_spec _ _ (hClines _ _ _ _ fun r_clines => ?_)
  c0_hfast
  refine wp_loop_inv
    (fun (nql, ncntd, qi, ticks, ()) ml => ∃ ar ws ws1 ws2 ant,
      qi.toNat ≤ cur_qn.toNat ∧ ncntd.toNat ≤ 2 * c.max_vars ∧
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      S13ScanArBvaqInv c s ar ws2 0 nql.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      (∀ i < ncntd.toNat,
        (ws1[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c (mkSt ar s.core.lit_mark ws ws1 ws2 ant) ⋆ R) ml)
    (fun (_, _, qi, _, _) _ => cur_qn.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hfast; exact hJq (0#32, 0#32, 0#32, _, ()) m
        ⟨s.core.arena, s.scratch.wsort, s.scratch.work_stk1, s.scratch.work_stk2, s.scratch.ant_sz,
         Nat.zero_le _, Nat.zero_le _, hwsort_len, hws1_len, s13ScanArBvaqInv_init hslen,
         hw, fun _ h => by simp only [bv_c0] at h; omega, hm⟩)
    (fun Jq (nql, ncntd, qi, ticks, ()) ml hstate ihq => ?_)
  obtain ⟨ar, ws, ws1, ws2, ant, hqi_le, hnc_le, hws_l, hws1_l, hbvaq, hw_ar, hcntd_ok, hml⟩ :=
    hstate
  dsimp only [mkSt] at hml
  have har_l := hbvaq.1; have hws2_l := hbvaq.2.1; have hnql_le := hbvaq.2.2.1
  c0_hsplit
  · have hqi_lt := hc; clear hc
    have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by c0_bound
    have hrqi : (row_off + qi).toNat = row_off.toNat + qi.toNat := by c0_bound
    have hrqi_sb : (BitVec.setWidth 64 (row_off + qi)).toNat < s.scratch.scratch_buf.length := by
      rw [bv64_setWidth_32, hrqi, hsb_len]; omega
    have hqw_ok := hrow_ok qi.toNat hqi_lt
    let qw := s.scratch.scratch_buf[row_off.toNat + qi.toNat]'(by omega)
    have hrqi_mod : (row_off.toNat + qi.toNat) % 2 ^ 32 = row_off.toNat + qi.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hqw_mod : s.scratch.scratch_buf[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
        rw [hrqi_mod]; omega) = qw := by dsimp only [qw]; simp only [hrqi_mod]
    have hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw := by
      dsimp only [qw]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hqw_getD] at hqw_ok
    c0_hfast_nogrp
    refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 64 ×
        List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × BitVec 64)
      (fun ⟨nql_s, nc_s, ticks_s, _, _, _, _, _⟩ => (nql_s, nc_s, ticks_s, ()))
      (fun ⟨nql_s, nc_s, _ticks_s, ar_s, ws_s, ws1_s, ql_s, ant_s⟩ ms =>
        nc_s.toNat ≤ 2 * c.max_vars ∧ ws_s.length = 2 * c.max_vars ∧
        ws1_s.length = 2 * c.max_vars ∧ S13ScanArBvaqInv c s ar_s ql_s 0 nql_s.toNat ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar_s } ∧
        (∀ i < nc_s.toNat,
          (ws1_s[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
          (ws1_s[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        (FullMem c (mkSt ar_s s.core.lit_mark ws_s ws1_s ql_s ant_s) ⋆ R) ms)
      (fun _ ⟨nql_s, nc_s, _ticks_s, ar_s, ws_s, ws1_s, ql_s, ant_s⟩ ms
          ⟨hnc_s, hws_s_l, hws1_s_l, hbvaq_s, hw_s, hcntd_s, hms⟩ => ?_)
      (fun Js hJs => ?_)
    · clear hml
      dsimp only [mkSt] at hms
      have hql_s_l := hbvaq_s.2.1; have hnql_s_le := hbvaq_s.2.2.1
      c0_hfast
      · exact s13_scan_clear_ret_wp hcl hsc hw hnc_s hws_s_l hws1_s_l hbvaq_s hcntd_s
          (by assumption) hQ
      · refine ihq (nql_s, nc_s, qi + 1#32, 0#64, ()) _ (by dsimp only; rw [hqi1]; omega) ?_
        dsimp only [mkSt]
        exact ⟨ar_s, ws_s, ws1_s, ql_s, _, by rw [hqi1]; omega, hnc_s, hws_s_l, hws1_s_l,
          hbvaq_s, hw_s, hcntd_s, by assumption⟩
      · exact s13_scan_clear_ret_wp hcl hsc hw hnc_s hws_s_l hws1_s_l hbvaq_s hcntd_s
          (by assumption) hQ
      · exact False.elim (hc trivial)
    · c0_hsplit
      · have hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32 := by
          intro h; apply hc; rwa [← hqw_mod] at h
        clear hc
        rw [ite_eq_left hbin_ne] at hqw_ok
        let q := qw &&& 0x7FFFFFFF#32
        have hq_lt : q.toNat < 2 * s.core.cur_vars := hqw_ok
        have hbin := s13_scan_bin_wp (Γ := Γ) (Q := Q) (X := X) hClines hslen hw hdw
          hws_l hws1_l hws2_l har_l hnc_le hcntd_ok
          (row_off := row_off) (cur_qn := cur_qn) (J := J) (Jq := Jq)
          (nql := nql) (ncntd := ncntd) (qi := qi) (ticks := ticks) (r_clines := r_clines)
          (qw := s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega))
          (Js := Js)
          (by dsimp only [q] at hq_lt; simp only [hset, hrqi]; exact hq_lt)
          hml
          (fun nc ticks_b wsp ws1p mlp hncp_le hwsp_l hws1p_l hcntdp hmlp =>
            hJs ⟨nql, nc, ticks_b, ar, wsp, ws1p, ws2, ant⟩ mlp
              ⟨hncp_le, hwsp_l, hws1p_l, hbvaq, hw_ar, hcntdp, hmlp⟩)
        dsimp only [s13ScanBin, s13ScanHdr, s13Step, s13Steps, s13StepZ, s13StepsZ, s13Ld64,
          s13Ld32, s13Call64, s13Then, s13Else, s13GrpK4q, s13GrpB4q, s13GrpK3s, s13GrpB4m,
          s13GrpK4c, s13GrpK5mp, s13DummyVal, s13DummyTup, full_bva_scan_cands_body] at hbin
        exact hbin
      · have hbin_eq : (qw &&& 0x80000000#32) = 0#32 := by
          have h1 : s.scratch.scratch_buf[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
            rw [hrqi_mod]; omega) &&& 0x80000000#32 = 0#32 := hc
          rwa [hqw_mod] at h1
        rw [ite_eq_right (fun h' => h' hbin_eq)] at hqw_ok
        obtain ⟨hqw_ref, hqw_ng⟩ := hqw_ok
        clear hc
        have hqw_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) = qw := by dsimp only [qw]; simp only [hset, hrqi]
        have hlg := s13_scan_large_wp (Γ := Γ) (Q := Q) (X := X) hClines hslen hw hdw hl0
          hlm_clr
          (row_off := row_off) (cur_qn := cur_qn)
          (J := fun _ _ => False) (Jq := fun _ _ => False)
          (nql := nql) (ncntd := ncntd) (qi := qi) (ticks := ticks) (r_clines := r_clines)
          (qw := s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega))
          (Js := Js)
          (by simpa only [hqw_eq] using hqw_ref)
          (by simpa only [hqw_eq] using hqw_ng)
          hws_l hws1_l har_l hnc_le hbvaq hw_ar hcntd_ok hml
          (fun nql_j nc_j ticks_j ar_j ws_j ws1_j ql_j mj
              hnc_j hws_j_l hws1_j_l hbvaq_j hw_j hcntd_j hmj =>
            hJs ⟨nql_j, nc_j, ticks_j, ar_j, ws_j, ws1_j, ql_j, ant⟩ mj
              ⟨hnc_j, hws_j_l, hws1_j_l, hbvaq_j, hw_j, hcntd_j, hmj⟩)
        dsimp only [s13ScanLarge, s13ScanHdr, s13Step, s13Steps, s13StepZ, s13StepsZ, s13Ld64,
          s13Ld32, s13Call64, s13Then, s13Else, s13GrpK4q, s13GrpB4q, s13GrpK3s, s13GrpB4m,
          s13GrpK4c, s13GrpK5mp, s13DummyVal, s13DummyTup, full_bva_scan_cands_body] at hlg
        exact hlg
  · clear hm
    c0_hfast_nogrp
    refine wp_loop_inv
      (fun (ci, ()) mci => ∃ arci,
        ci.toNat ≤ nql.toNat ∧ S13ScanArBvaqInv c s arci ws2 ci.toNat nql.toNat ∧
        (FullMem c (mkSt arci s.core.lit_mark ws ws1 ws2 ant) ⋆ R) mci)
      (fun (ci, ()) _ => nql.toNat - ci.toNat)
      (fun Jc hJc => by c0_hfast; exact hJc (0#32, ()) ml ⟨ar, Nat.zero_le _, hbvaq, hml⟩)
      (fun Jc (ci, ()) mci ⟨arci, hci_le, hbvaq_ci, hmci⟩ ihc => ?_)
    clear hml; dsimp only [mkSt] at hmci
    have harci_l := hbvaq_ci.1
    c0_hsplit
    · have hci_lt : ci.toNat < nql.toNat := by assumption
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
      have hidx_ref := (hbvaq_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt).1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hidx_ref
      have hidx_wf := hw.arena.refs_wf _ hidx_ref
      have hstep := s13ScanArBvaqInv_clear_step har_len hbvaq_ci hci_lt (by omega)
      have hci_ws2 : (BitVec.setWidth 64 ci).toNat < ws2.length := by rw [hset, hws2_l]; omega
      have hidx_ar : (BitVec.setWidth 64 (ws2[(BitVec.setWidth 64 ci).toNat]'hci_ws2)).toNat <
          arci.length := by
        simp only [hset]; have := hidx_wf.1; rw [harci_l]; have := hcl.arena_len_le; omega
      c0_hfast
      refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ?_⟩
      simp only [hset] at hm; exact hm
    · have hci_eq : ci.toNat = nql.toNat := by omega
      rw [hci_eq] at hbvaq_ci
      have har_rest : arci = s.core.arena := s13ScanArBvaqInv_done har_len hbvaq_ci
      rw [har_rest] at hmci; c0_hfast; exact hQ ncntd ws ws1 ws2 ant _
        ⟨hcl, { hsc with wsort_len := hws_l, work_stk1_len := hws1_l, work_stk2_len := hws2_l }⟩
        hnc_le hcntd_ok hmci

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
