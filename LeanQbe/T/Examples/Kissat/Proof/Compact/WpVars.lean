/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Compact.Inv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical WP Proof for `full_compact_vars` (`Proof.Compact.WpVars`)

Proves `full_compact_vars_wp` against `Proof.Compact.Spec.fullCompactVarsSpec`, matching
`Src.Compact.full_compact_vars_body` (preserving `fl[nv] = fl[ov]` and clearing `phases`,
`phases_target`, `phases_best`, `walk_best` over `[ncv, old_cv)`, plus updating `d.mv` and
`bva_cap` via `FullCfgCompat`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Compact
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private def CompactVarsL2Rest (c : FullCfg) (vals1 : List (BitVec 8))
    (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  (array (t := i8) c.pVals vals1 ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
    array (t := i8) c.pMark s.core.mrk) ⋆
  (array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pTrailPos s.core.trail_pos ⋆
    array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
  (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
    array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
    array (t := i32) c.pQPrev s.scratch.q_prev ⋆
    array (t := i32) c.pQNext s.scratch.q_next) ⋆
  (array (t := i32) c.pWsort s.scratch.wsort ⋆
    array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
    array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
    array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
  (array64 c.pSimSig s.scratch.sim_sig ⋆ array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
    array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
  FullScrDynArrs c s.scratch ⋆ c.pad

private def CompactVarsL3Rest (c : FullCfg) (vals1 : List (BitVec 8))
    (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  (array (t := i8) c.pVals vals1 ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
    array (t := i8) c.pMark s.core.mrk) ⋆
  (array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pTrailPos s.core.trail_pos ⋆
    array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
  (array (t := i32) c.pHeap s.scratch.heap ⋆
    array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆
  FullScrWksArrs c s.scratch ⋆
  (array64 c.pSimSig s.scratch.sim_sig ⋆ array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
    array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
  FullScrDynArrs c s.scratch ⋆ c.pad

private theorem focus_vars_loop2 {c : FullCfg} {vals1 : List (BitVec 8)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c { s with core := { s.core with vals := vals1 } } ⋆ R) m) :
    (array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
      array (t := i32) c.pReason s.core.rsns ⋆ array (t := i8) c.pPhases s.scratch.phases ⋆
      array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
      array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
      array (t := i8) c.pWalkBest s.scratch.walk_best ⋆
      array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      (CompactVarsL2Rest c vals1 s ⋆ R)) m := by
  have hhdr : hdrTailWords c { s with core := { s.core with vals := vals1 } } =
      hdrTailWords c s := rfl
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A FullScratchArrays
    FullScrByteArrs FullScrU32A FullScrWksArrs FullScrMetaArrs at hm
  rw [hhdr] at hm
  unfold CompactVarsL2Rest
  exact sep_ac hm

private theorem shift_vars_loop2_to_3 {c : FullCfg} {vals1 : List (BitVec 8)} {s : FullState}
    {fl2 lvl2 rsns2 : List (BitVec 32)} {ph2 pt2 pb2 wb2 : List (BitVec 8)}
    {sc2 : List (BitVec 64)} {qs2 : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array (t := i32) c.pFlags fl2 ⋆ array (t := i32) c.pLevel lvl2 ⋆
      array (t := i32) c.pReason rsns2 ⋆ array (t := i8) c.pPhases ph2 ⋆
      array (t := i8) c.pPhasesTarget pt2 ⋆ array (t := i8) c.pPhasesBest pb2 ⋆
      array (t := i8) c.pWalkBest wb2 ⋆ array64 c.pScore sc2 ⋆
      array (t := i32) c.pQStamp qs2 ⋆ (CompactVarsL2Rest c vals1 s ⋆ R)) m) :
    (array (t := i32) c.pFlags fl2 ⋆ array (t := i32) c.pLevel lvl2 ⋆
      array (t := i32) c.pReason rsns2 ⋆ array (t := i8) c.pPhases ph2 ⋆
      array (t := i8) c.pPhasesTarget pt2 ⋆ array (t := i8) c.pPhasesBest pb2 ⋆
      array (t := i8) c.pWalkBest wb2 ⋆ array64 c.pScore sc2 ⋆
      array (t := i32) c.pQStamp qs2 ⋆ array (t := i32) c.pQPrev s.scratch.q_prev ⋆
      array (t := i32) c.pQNext s.scratch.q_next ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
      (CompactVarsL3Rest c vals1 s ⋆ R)) m := by
  unfold CompactVarsL2Rest at hm
  unfold CompactVarsL3Rest FullScrWksArrs
  exact sep_ac hm

private theorem unfocus_vars_loop3 {c : FullCfg} {vals1 : List (BitVec 8)} {s : FullState}
    {fl3 lvl3 rsns3 : List (BitVec 32)} {ph3 pt3 pb3 wb3 : List (BitVec 8)}
    {sc3 : List (BitVec 64)} {qs3 qp3 qn3 ps3 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pFlags fl3 ⋆ array (t := i32) c.pLevel lvl3 ⋆
      array (t := i32) c.pReason rsns3 ⋆ array (t := i8) c.pPhases ph3 ⋆
      array (t := i8) c.pPhasesTarget pt3 ⋆ array (t := i8) c.pPhasesBest pb3 ⋆
      array (t := i8) c.pWalkBest wb3 ⋆ array64 c.pScore sc3 ⋆
      array (t := i32) c.pQStamp qs3 ⋆ array (t := i32) c.pQPrev qp3 ⋆
      array (t := i32) c.pQNext qn3 ⋆ array (t := i32) c.pPos ps3 ⋆
      (CompactVarsL3Rest c vals1 s ⋆ R)) m) :
    (FullMem c {
      core := { s.core with vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3 },
      scratch := {
        s.scratch with
        phases := ph3, phases_target := pt3, phases_best := pb3, walk_best := wb3,
        score := sc3, q_stamp := qs3, q_prev := qp3, q_next := qn3, pos := ps3 } } ⋆ R) m := by
  have hhdr : hdrTailWords c {
      core := { s.core with vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3 },
      scratch := {
        s.scratch with
        phases := ph3, phases_target := pt3, phases_best := pb3, walk_best := wb3,
        score := sc3, q_stamp := qs3, q_prev := qp3, q_next := qn3, pos := ps3 } } =
      hdrTailWords c s := rfl
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A FullScratchArrays
    FullScrByteArrs FullScrU32A FullScrMetaArrs
  rw [hhdr]
  unfold CompactVarsL3Rest at hm
  exact sep_ac hm

private structure VarsL3Lens (c : FullCfg)
    (fl3 lvl3 rsns3 qp3 qn3 qs3 ps3 : List (BitVec 32))
    (ph3 pt3 pb3 wb3 : List (BitVec 8)) (sc3 : List (BitVec 64)) : Prop where
  fl : fl3.length = c.max_vars
  lv : lvl3.length = c.max_vars
  rs : rsns3.length = c.max_vars
  qp : qp3.length = c.max_vars
  qn : qn3.length = c.max_vars
  qs : qs3.length = c.max_vars
  ps : ps3.length = c.max_vars
  ph : ph3.length = c.max_vars
  pt : pt3.length = c.max_vars
  pb : pb3.length = c.max_vars
  wb : wb3.length = c.max_vars
  sc : sc3.length = c.max_vars

public section

/-- Canonical WP proof for `full_compact_vars`. -/
theorem full_compact_vars_wp (Γ : Env) :
    ∀ a m Q X, compactVarsSpec a m Q X →
      Func.wp Γ full_compact_vars_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, ⟨hold, hncv_le, hinv_ok⟩, hm, hQ0⟩ :=
    FullCfgContract.elim hs
  let hQ : ∀ c' vals' fl' lvl' rsns' ft0 fd0 sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := fl', lvl := lvl', rsns := rsns',
                                frame_trail := s.core.frame_trail.set 0 ft0,
                                frame_dec := s.core.frame_dec.set 0 fd0,
                                trail_end := 0, propagated := 0, cur_level := 0,
                                unflushed := 0#64, confl_ref := 0xFFFFFFFF#64,
                                confl_type := 0#64, cur_vars := ncv.toNat, unassigned := ncv }
          scratch := sc' }
      FullCfgCompat c c' → s'.LengthsOk c' → ft0.toNat = 0 →
      (∀ l < 2 * c'.max_vars, l < 2 * old_cv.toNat → vals'[l]?.getD 0#8 = 0#8) →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → (FullMem c' s' ⋆ R) m' → Q () m' :=
    fun c' vals' fl' lvl' rsns' ft0 fd0 sc' m' hcmp hlen' hft0 hvals' hpres' hws1' hws2' hm' => by
      have hft_eq : ft0 = 0#32 := BitVec.eq_of_toNat_eq (by simpa using hft0)
      subst hft_eq
      exact hQ0 () c' _ m' hcmp hlen'
        ⟨rfl, rfl, ⟨fd0, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
         hvals', hpres', hws1', hws2'⟩ hm'
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv2_lt64 : 2 * old_cv.toNat < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
  have hcv_lt64 : old_cv.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ Nat.zero_lt_two) hcv2_lt64
  have hncv_lt64 : ncv.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hncv_le hcv_lt64
  have hmax2_lt : 2 * c.max_vars < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
  have h2cv_bd : 2 * old_cv.toNat ≤ 2 * c.max_vars := Nat.mul_le_mul_left 2 (hold ▸ hcv_le)
  have hold_max : old_cv.toNat ≤ c.max_vars := hold ▸ hcv_le
  have hncv_max : ncv.toNat ≤ c.max_vars := Nat.le_trans hncv_le hold_max
  have hmax_mul2 : c.max_vars ≤ 2 * c.max_vars := Nat.le_mul_of_pos_left _ Nat.zero_lt_two
  have hcv_lt_mul2 : old_cv.toNat ≤ 2 * old_cv.toNat := Nat.le_mul_of_pos_left _ Nat.zero_lt_two
  have h2cv_lt64 : 2 * old_cv.toNat + 1 ≤ 2 ^ 64 := by omega
  have hv_len := hlen.core_ok.vals_len
  have h2old : (old_cv <<< (1 : Nat)).toNat = 2 * old_cv.toNat := by bv_omega
  unfold Func.wp full_compact_vars_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (l, ()) m1 =>
      l.toNat ≤ 2 * old_cv.toNat ∧
      ∃ vals1 : List (BitVec 8), vals1.length = 2 * c.max_vars ∧
        (∀ i < l.toNat, vals1[i]? = some 0#8) ∧
        (FullMem c { s with core := { s.core with vals := vals1 } } ⋆ R) m1)
    (fun (l, ()) _ => 2 * old_cv.toNat - l.toNat)
    (fun J1 hLoop1 => ?_) ?_
  · c0_hsteps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.core.vals, hv_len,
      fun _ h => by simp at h, hm⟩
  · rintro J1 ⟨l, ⟨⟩⟩ m1 ⟨hl_le, vals1, hvl1, hz1, hm1⟩ hLoop1
    c0_hsplit
    · have hl_lt : l.toNat < 2 * old_cv.toNat := by c0_bound
      have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 :=
        cmp_bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hl_lt) hcv2_lt64)
      have hlt_v : l.toNat < vals1.length := hvl1 ▸ Nat.lt_of_lt_of_le hl_lt h2cv_bd
      c0_hsteps
      refine hLoop1 (l + (1 : BitVec 64), ()) _
        (by dsimp only; rw [hl1_eq]; exact Nat.sub_lt_sub_left hl_lt (Nat.le_refl _)) ?_
      refine ⟨by rw [hl1_eq]; exact hl_lt, _, ?_, fun i hi => ?_, by assumption⟩
      · rw [List.length_set, hvl1]
      · rw [hl1_eq] at hi
        by_cases hil : i = l.toNat
        · subst hil; exact List.getElem?_set_self hlt_v
        · rw [List.getElem?_set_ne (Ne.symm hil)]
          exact hz1 i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hil)
    · have hl_eq : l.toNat = 2 * old_cv.toNat := by c0_bound
      rw [hl_eq] at hz1
      clear hLoop1 J1
      have hfl_len := hlen.core_ok.flags_len
      have hlv_len := hlen.core_ok.lvl_len
      have hrs_len := hlen.core_ok.rsns_len
      have hft_len := hlen.core_ok.frame_trail_len
      have hfd_len := hlen.core_ok.frame_dec_len
      have hph_len := hlen.scratch_ok.phases_len
      have hpt_len := hlen.scratch_ok.phases_target_len
      have hpb_len := hlen.scratch_ok.phases_best_len
      have hwb_len := hlen.scratch_ok.walk_best_len
      have hsc_len := hlen.scratch_ok.score_len
      have hqs_len := hlen.scratch_ok.q_stamp_len
      have hqp_len := hlen.scratch_ok.q_prev_len
      have hqn_len := hlen.scratch_ok.q_next_len
      have hps_len := hlen.scratch_ok.pos_len
      have hws2_len := hlen.scratch_ok.work_stk2_len
      c0_hsteps_nogrp
      have hm1f := focus_vars_loop2 hm1
      clear hm1
      generalize hpInv : c.pWorkStk2 = pInv at *
      generalize hpFl : c.pFlags = pFl at *
      generalize hpLv : c.pLevel = pLv at *
      generalize hpRs : c.pReason = pRs at *
      generalize hpPh : c.pPhases = pPh at *
      generalize hpPt : c.pPhasesTarget = pPt at *
      generalize hpPb : c.pPhasesBest = pPb at *
      generalize hpWb : c.pWalkBest = pWb at *
      generalize hpSc : c.pScore = pSc at *
      generalize hpQs : c.pQStamp = pQs at *
      refine wp_loop_inv
        (fun (tgt_asg, bst_asg, nv, ()) m2 =>
          nv.toNat ≤ ncv.toNat ∧
          ∃ fl2 lvl2 rsns2 : List (BitVec 32),
            fl2.length = c.max_vars ∧ lvl2.length = c.max_vars ∧ rsns2.length = c.max_vars ∧
            ∃ ph2 pt2 pb2 wb2 : List (BitVec 8),
              ph2.length = c.max_vars ∧ pt2.length = c.max_vars ∧
              pb2.length = c.max_vars ∧ wb2.length = c.max_vars ∧
              ∃ sc2 : List (BitVec 64), sc2.length = c.max_vars ∧
                ∃ qs2 : List (BitVec 32), qs2.length = c.max_vars ∧
                  (array (t := i32) pInv s.scratch.work_stk2 ⋆
                    array (t := i32) pFl fl2 ⋆ array (t := i32) pLv lvl2 ⋆
                    array (t := i32) pRs rsns2 ⋆ array (t := i8) pPh ph2 ⋆
                    array (t := i8) pPt pt2 ⋆ array (t := i8) pPb pb2 ⋆
                    array (t := i8) pWb wb2 ⋆ array64 pSc sc2 ⋆
                    array (t := i32) pQs qs2 ⋆ (CompactVarsL2Rest c vals1 s ⋆ R)) m2)
        (fun (_, _, nv, ()) _ => ncv.toNat - nv.toNat)
        (fun J2 hLoop2 => ?_) ?_
      · c0_hsteps
        exact hLoop2 (0#64, 0#64, 0#64, ()) m1 ⟨Nat.zero_le _, s.core.flags, s.core.lvl,
          s.core.rsns, hfl_len, hlv_len, hrs_len, s.scratch.phases, s.scratch.phases_target,
          s.scratch.phases_best, s.scratch.walk_best, hph_len, hpt_len, hpb_len, hwb_len,
          s.scratch.score, hsc_len, s.scratch.q_stamp, hqs_len, hm1f⟩
      · clear hm1f
        rintro J2 ⟨tgt_asg, bst_asg, nv, ⟨⟩⟩ m2 ⟨hnv_le2, fl2, lvl2, rsns2, hfl2, hlv2, hrs2,
            ph2, pt2, pb2, wb2, hph2, hpt2, hpb2, hwb2, sc2, hsc2, qs2, hqs2, hm2⟩ hLoop2
        c0_hsplit
        · have hnv_lt : nv.toNat < ncv.toNat := by c0_bound
          have hnv_cm : nv.toNat < c.max_vars := Nat.lt_of_lt_of_le hnv_lt hncv_max
          have hnv_ws2 : nv.toNat < s.scratch.work_stk2.length :=
            hws2_len.symm ▸ Nat.lt_of_lt_of_le hnv_cm hmax_mul2
          have hov_lt : (s.scratch.work_stk2[nv.toNat]'hnv_ws2).toNat < old_cv.toNat := by
            have h := hinv_ok nv.toNat hnv_lt
            rw [List.getElem?_eq_getElem hnv_ws2, Option.getD_some] at h
            exact h
          let ov := (s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64
          have hov64_lt : ov.toNat < old_cv.toNat := by
            dsimp only [ov]; rw [zext_toNat _ (by decide)]; exact hov_lt
          have hov_cm : ov.toNat < c.max_vars := Nat.lt_of_lt_of_le hov64_lt hold_max
          dsimp only [ov] at hov_cm
          have hnv1_eq : (nv + (1 : BitVec 64)).toNat = nv.toNat + 1 :=
            cmp_bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hnv_lt) hncv_lt64)
          have hnv_fl : nv.toNat < fl2.length := hfl2.symm ▸ hnv_cm
          have hov_fl : (BitVec.setWidth 64 (s.scratch.work_stk2[nv.toNat]'hnv_ws2)).toNat <
              fl2.length := hfl2.symm ▸ hov_cm
          have hnv_ph : nv.toNat < ph2.length := hph2.symm ▸ hnv_cm
          have hov_ph : (BitVec.setWidth 64 (s.scratch.work_stk2[nv.toNat]'hnv_ws2)).toNat <
              ph2.length := hph2.symm ▸ hov_cm
          have hnv_pt : nv.toNat < pt2.length := hpt2.symm ▸ hnv_cm
          have hov_pt : (BitVec.setWidth 64 (s.scratch.work_stk2[nv.toNat]'hnv_ws2)).toNat <
              pt2.length := hpt2.symm ▸ hov_cm
          have hnv_pb : nv.toNat < pb2.length := hpb2.symm ▸ hnv_cm
          have hov_pb : (BitVec.setWidth 64 (s.scratch.work_stk2[nv.toNat]'hnv_ws2)).toNat <
              pb2.length := hpb2.symm ▸ hov_cm
          have hnv_wb : nv.toNat < wb2.length := hwb2.symm ▸ hnv_cm
          have hov_wb : (BitVec.setWidth 64 (s.scratch.work_stk2[nv.toNat]'hnv_ws2)).toNat <
              wb2.length := hwb2.symm ▸ hov_cm
          have hnv_sc : nv.toNat < sc2.length := hsc2.symm ▸ hnv_cm
          have hov_sc : (BitVec.setWidth 64 (s.scratch.work_stk2[nv.toNat]'hnv_ws2)).toNat <
              sc2.length := hsc2.symm ▸ hov_cm
          have hnv_qs : nv.toNat < qs2.length := hqs2.symm ▸ hnv_cm
          have hov_qs : (BitVec.setWidth 64 (s.scratch.work_stk2[nv.toNat]'hnv_ws2)).toNat <
              qs2.length := hqs2.symm ▸ hov_cm
          have hnv_lv : nv.toNat < lvl2.length := hlv2.symm ▸ hnv_cm
          have hnv_rs : nv.toNat < rsns2.length := hrs2.symm ▸ hnv_cm
          clear hinv_ok hov_lt hov64_lt
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun _ mA =>
              (array (t := i32) pInv s.scratch.work_stk2 ⋆
                array (t := i32) pFl (fl2.set nv.toNat (fl2[ov.toNat]'(hfl2 ▸ hov_cm))) ⋆
                array (t := i32) pLv lvl2 ⋆ array (t := i32) pRs rsns2 ⋆
                array (t := i8) pPh (ph2.set nv.toNat (ph2[ov.toNat]'(hph2 ▸ hov_cm))) ⋆
                array (t := i8) pPt (pt2.set nv.toNat (pt2[ov.toNat]'(hpt2 ▸ hov_cm))) ⋆
                array (t := i8) pPb (pb2.set nv.toNat (pb2[ov.toNat]'(hpb2 ▸ hov_cm))) ⋆
                array (t := i8) pWb wb2 ⋆ array64 pSc sc2 ⋆
                array (t := i32) pQs qs2 ⋆ (CompactVarsL2Rest c vals1 s ⋆ R)) mA)
            (fun _ ⟨tgt_asg', ⟨⟩⟩ mA hmA => by
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ mB => mB = mA)
                (fun _ ⟨bst_asg', ⟨⟩⟩ mB hmB => by
                  rw [hmB] at *
                  clear hmB mB
                  c0_hsteps
                  refine hLoop2 (tgt_asg', bst_asg', nv + (1 : BitVec 64), ()) _
                    (by dsimp only; rw [hnv1_eq]; exact Nat.sub_lt_sub_left hnv_lt (Nat.le_refl _))
                    ⟨by rw [hnv1_eq]; exact hnv_lt,
                     fl2.set nv.toNat (fl2[ov.toNat]'(hfl2 ▸ hov_cm)),
                     lvl2.set nv.toNat 0#32, rsns2.set nv.toNat 0xFFFFFFFF#32,
                     by rw [List.length_set]; exact hfl2,
                     by rw [List.length_set]; exact hlv2,
                     by rw [List.length_set]; exact hrs2,
                     ph2.set nv.toNat (ph2[ov.toNat]'(hph2 ▸ hov_cm)),
                     pt2.set nv.toNat (pt2[ov.toNat]'(hpt2 ▸ hov_cm)),
                     pb2.set nv.toNat (pb2[ov.toNat]'(hpb2 ▸ hov_cm)),
                     wb2.set nv.toNat (wb2[ov.toNat]'(hwb2 ▸ hov_cm)),
                     by rw [List.length_set]; exact hph2,
                     by rw [List.length_set]; exact hpt2,
                     by rw [List.length_set]; exact hpb2,
                     by rw [List.length_set]; exact hwb2,
                     sc2.set nv.toNat (sc2[ov.toNat]'(hsc2 ▸ hov_cm)),
                     by rw [List.length_set]; exact hsc2,
                     qs2.set nv.toNat (qs2[ov.toNat]'(hqs2 ▸ hov_cm)),
                     by rw [List.length_set]; exact hqs2, by
                       try rw [Std.ExtHashMap.sep_emp] at *
                       exact sep_ac ‹_›⟩)
                (fun Jb hJb => by c0_hsplit <;> (c0_hsteps; exact hJb (_, ()) mA rfl)))
            (fun Jt hJt => by
              c0_hsplit <;> (c0_hsteps; exact hJt (_, ()) _ (by
                try rw [Std.ExtHashMap.sep_emp] at *
                exact sep_ac ‹_›)))
        · clear hLoop2 J2 hinv_ok hws2_len hncv_lt64
          subst hpInv hpFl hpLv hpRs hpPh hpPt hpPb hpWb hpSc hpQs
          have hm2s := shift_vars_loop2_to_3 hm2
          clear hm2
          c0_hsteps_nogrp
          generalize hpFl : c.pFlags = pFl at *
          generalize hpLv : c.pLevel = pLv at *
          generalize hpRs : c.pReason = pRs at *
          generalize hpPh : c.pPhases = pPh at *
          generalize hpPt : c.pPhasesTarget = pPt at *
          generalize hpPb : c.pPhasesBest = pPb at *
          generalize hpWb : c.pWalkBest = pWb at *
          generalize hpSc : c.pScore = pSc at *
          generalize hpQs : c.pQStamp = pQs at *
          generalize hpQp : c.pQPrev = pQp at *
          generalize hpQn : c.pQNext = pQn at *
          generalize hpPs : c.pPos = pPs at *
          refine wp_loop_inv
            (fun (v, ()) m3 =>
              v.toNat ≤ old_cv.toNat ∧
              ∃ fl3 lvl3 rsns3 qp3 qn3 qs3 ps3 : List (BitVec 32),
                ∃ ph3 pt3 pb3 wb3 : List (BitVec 8),
                  ∃ sc3 : List (BitVec 64),
                    VarsL3Lens c fl3 lvl3 rsns3 qp3 qn3 qs3 ps3 ph3 pt3 pb3 wb3 sc3 ∧
                    (array (t := i32) pFl fl3 ⋆ array (t := i32) pLv lvl3 ⋆
                      array (t := i32) pRs rsns3 ⋆ array (t := i8) pPh ph3 ⋆
                      array (t := i8) pPt pt3 ⋆ array (t := i8) pPb pb3 ⋆
                      array (t := i8) pWb wb3 ⋆ array64 pSc sc3 ⋆
                      array (t := i32) pQs qs3 ⋆ array (t := i32) pQp qp3 ⋆
                      array (t := i32) pQn qn3 ⋆ array (t := i32) pPs ps3 ⋆
                      (CompactVarsL3Rest c vals1 s ⋆ R)) m3)
            (fun (v, ()) _ => old_cv.toNat - v.toNat)
            (fun J3 hLoop3 => ?_) ?_
          · c0_hsteps
            exact hLoop3 (ncv, ()) m2 ⟨hncv_le, fl2, lvl2, rsns2, s.scratch.q_prev,
              s.scratch.q_next, qs2, s.scratch.pos, ph2, pt2, pb2, wb2, sc2,
              ⟨hfl2, hlv2, hrs2, hqp_len, hqn_len, hqs2, hps_len,
               hph2, hpt2, hpb2, hwb2, hsc2⟩, hm2s⟩
          · clear hm2s hfl2 hlv2 hrs2 hqp_len hqn_len hqs2 hps_len hph2 hpt2 hpb2 hwb2 hsc2
              hfl_len hlv_len hrs_len hph_len hpt_len hpb_len hwb_len hsc_len hqs_len
              fl2 lvl2 rsns2 ph2 pt2 pb2 wb2 sc2 qs2
            rintro J3 ⟨v, ⟨⟩⟩ m3 ⟨hv_le3, fl3, lvl3, rsns3, qp3, qn3, qs3, ps3,
                ph3, pt3, pb3, wb3, sc3, hl3, hm3⟩ hLoop3
            c0_hsplit
            · have hv_lt : v.toNat < old_cv.toNat := by c0_bound
              have hv_cm : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hold_max
              have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 :=
                cmp_bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hv_lt) hcv_lt64)
              have hv_fl : v.toNat < fl3.length := hl3.fl ▸ hv_cm
              have hv_lv : v.toNat < lvl3.length := hl3.lv ▸ hv_cm
              have hv_rs : v.toNat < rsns3.length := hl3.rs ▸ hv_cm
              have hv_sc : v.toNat < sc3.length := hl3.sc ▸ hv_cm
              have hv_ph : v.toNat < ph3.length := hl3.ph ▸ hv_cm
              have hv_pt : v.toNat < pt3.length := hl3.pt ▸ hv_cm
              have hv_pb : v.toNat < pb3.length := hl3.pb ▸ hv_cm
              have hv_wb : v.toNat < wb3.length := hl3.wb ▸ hv_cm
              have hv_qs : v.toNat < qs3.length := hl3.qs ▸ hv_cm
              have hv_qp : v.toNat < qp3.length := hl3.qp ▸ hv_cm
              have hv_qn : v.toNat < qn3.length := hl3.qn ▸ hv_cm
              have hv_ps : v.toNat < ps3.length := hl3.ps ▸ hv_cm
              c0_hsteps
              refine hLoop3 (v + (1 : BitVec 64), ()) _
                (by dsimp only; rw [hv1_eq]; exact Nat.sub_lt_sub_left hv_lt (Nat.le_refl _))
                ⟨by rw [hv1_eq]; exact hv_lt,
                 fl3.set v.toNat 0#32, lvl3.set v.toNat 0#32, rsns3.set v.toNat 0xFFFFFFFF#32,
                 qp3.set v.toNat 0xFFFFFFFF#32, qn3.set v.toNat 0xFFFFFFFF#32,
                 qs3.set v.toNat 0#32, ps3.set v.toNat 0xFFFFFFFF#32,
                 ph3.set v.toNat 0#8, pt3.set v.toNat 0#8, pb3.set v.toNat 0#8, wb3.set v.toNat 1#8,
                 sc3.set v.toNat 0#64,
                 ⟨by rw [List.length_set]; exact hl3.fl, by rw [List.length_set]; exact hl3.lv,
                  by rw [List.length_set]; exact hl3.rs, by rw [List.length_set]; exact hl3.qp,
                  by rw [List.length_set]; exact hl3.qn, by rw [List.length_set]; exact hl3.qs,
                  by rw [List.length_set]; exact hl3.ps, by rw [List.length_set]; exact hl3.ph,
                  by rw [List.length_set]; exact hl3.pt, by rw [List.length_set]; exact hl3.pb,
                  by rw [List.length_set]; exact hl3.wb, by rw [List.length_set]; exact hl3.sc⟩,
                 ?_⟩
              · try rw [Std.ExtHashMap.sep_emp] at *
                exact sep_ac ‹_›
            · obtain ⟨hfl3, hlv3, hrs3, hqp3, hqn3, hqs3, hps3,
                  hph3, hpt3, hpb3, hwb3, hsc3⟩ := hl3
              subst hpFl hpLv hpRs hpPh hpPt hpPb hpWb hpSc hpQs hpQp hpQn hpPs
              have hm3u := unfocus_vars_loop3 hm3
              clear hm3
              have hft0 : 0 < s.core.frame_trail.length := by rw [hft_len]; exact Nat.zero_lt_succ _
              have hfd0 : 0 < s.core.frame_dec.length := by rw [hfd_len]; exact Nat.zero_lt_succ _
              have hc_mv_lt : c.mv < 2 ^ 64 :=
                Nat.lt_trans c.hmv (by unfold dimacsBound; decide)
              have hmax_lt64 : c.max_vars < 2 ^ 64 :=
                Nat.lt_trans c.hmaxv (by unfold dimacsBound; decide)
              have hmv_lt_max : ncv.toNat ≤ c.max_vars := hncv_max
              have hncv_bv : ncv = BitVec.ofNat 64 ncv.toNat :=
                (@bv_ofNat_toNat_eq 64 ncv).symm
              have hsub_bv : BitVec.ofNat 64 c.max_vars - ncv =
                  BitVec.ofNat 64 (c.max_vars - ncv.toNat) :=
                (congrArg (BitVec.ofNat 64 c.max_vars - ·) hncv_bv).trans
                  (cmp_bv_sub_ofNat hmv_lt_max hmax_lt64)
              let sc_final : FullScratch :=
                { s.scratch with
                  phases := ph3, phases_target := pt3, phases_best := pb3, walk_best := wb3,
                  score := sc3, q_stamp := qs3, q_prev := qp3, q_next := qn3, pos := ps3,
                  target_assigned := tgt_asg, best_assigned := bst_asg }
              let s_final : FullState :=
                { core := { s.core with
                    vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3,
                    frame_trail := s.core.frame_trail.set 0 0#32,
                    frame_dec := s.core.frame_dec.set 0 0xFFFFFFFF#32,
                    trail_end := 0, propagated := 0, cur_level := 0,
                    unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
                    cur_vars := ncv.toNat, unassigned := ncv }
                  scratch := sc_final }
              c0_hsteps_nogrp
              refine wp_join_group
                (fun () mJ =>
                  ∃ c' : FullCfg, FullCfgCompat c c' ∧ c'.mv ≤ ncv.toNat ∧
                    (FullMem c' s_final ⋆ R) mJ)
                ?_ ?_
              · rintro _ ⟨⟩ mJ ⟨c', hcompat', hcv_ge', hmJ⟩
                c0_hsteps
                refine hQ c' vals1 fl3 lvl3 rsns3 0#32 0xFFFFFFFF#32 sc_final mJ hcompat'
                  ?_ rfl (fun l _ hl => by rw [hz1 l hl]; rfl) ⟨rfl, rfl⟩ rfl rfl hmJ
                obtain ⟨_, _, _, hmax, _, har, hwc, hdel, hred, hext, hscr⟩ := hcompat'
                exact ⟨⟨hmax ▸ hvl1, hmax ▸ hlen.core_ok.lit_mark_len,
                    hmax ▸ hlen.core_ok.mrk_len, hmax ▸ hfl3, hmax ▸ hlv3, hmax ▸ hrs3,
                    hmax ▸ hlen.core_ok.trl_len, hmax ▸ hlen.core_ok.trail_pos_len,
                    hmax ▸ hlen.core_ok.tmp_len_arr, hmax ▸ hlen.core_ok.min_clr_len_arr,
                    hmax ▸ (by rw [List.length_set]; exact hft_len),
                    hmax ▸ (by rw [List.length_set]; exact hfd_len),
                    hmax ▸ hlen.core_ok.wvec_len, hmax ▸ hlen.core_ok.repr_len,
                    (by simp only [FullCfg.minDepth, hmax]; exact hlen.core_ok.min_stk_len),
                    har ▸ hlen.core_ok.arena_len_arr,
                    hwc ▸ hlen.core_ok.wstk_len_arr, hcv_ge', hmax ▸ hmv_lt_max,
                    har ▸ hlen.core_ok.arena_len_le, hwc ▸ hlen.core_ok.wlen_le,
                    Nat.zero_le _, Nat.zero_le _, hmax ▸ hlen.core_ok.tmp_len_le,
                    hmax ▸ hlen.core_ok.min_clr_len_le⟩,
                  ⟨hmax ▸ hlen.scratch_ok.walk_vals_len, hmax ▸ hph3, hmax ▸ hpt3,
                    hmax ▸ hpb3, hmax ▸ hwb3, hmax ▸ hlen.scratch_ok.heap_len_arr,
                    hmax ▸ hps3, hmax ▸ hlen.scratch_ok.shrink_stk_len, hmax ▸ hqp3,
                    hmax ▸ hqn3, hmax ▸ hqs3, hmax ▸ hlen.scratch_ok.wsort_len,
                    hmax ▸ hlen.scratch_ok.work_stk1_len, hmax ▸ hlen.scratch_ok.work_stk2_len,
                    hmax ▸ hlen.scratch_ok.tarjan_mark_len,
                    hmax ▸ hlen.scratch_ok.tarjan_reach_len, hmax ▸ hsc3,
                    hmax ▸ hlen.scratch_ok.sim_sig_len, hlen.scratch_ok.glue_used_len,
                    hlen.scratch_ok.last_learned_len, hdel ▸ hlen.scratch_ok.delayed_len_arr,
                    hred ▸ hlen.scratch_ok.red_refs_len, hext ▸ hlen.scratch_ok.extend_stk_len,
                    hscr ▸ hlen.scratch_ok.scratch_buf_len⟩⟩
              · intro Jmv hJmv
                c0_hsplit
                · have hlt_mv : ncv.toNat < c.mv := by
                    simpa only [Nat.mod_eq_of_lt hc_mv_lt] using hc
                  let c' := fullCfgShrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv)
                  refine LeanQbe.T.wp_store_sep (full_store_mv_mid ncv (by assumption)) ?_
                  intro m4 hm4
                  c0_hsteps_nogrp
                  refine LeanQbe.T.wp_load_of (full_load_max_vars_mid hm4) ?_
                  c0_hsteps_nogrp
                  have hm4' :
                      (FullMemShrinkMid c (BitVec.ofNat 64 ncv.toNat) _ ⋆ R) m4 :=
                    (show ∀ {x : BitVec 64},
                        ncv = x → (FullMemShrinkMid c x _ ⋆ R) m4 from fun h => h ▸ hm4)
                      hncv_bv
                  refine LeanQbe.T.wp_store_sep (by
                    rw [hsub_bv]
                    exact full_store_bva_mid (Nat.le_of_lt hlt_mv) hm4') ?_
                  intro m5 hm5
                  c0_hsteps
                  exact hJmv () m5 ⟨c', FullCfgCompat.shrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv),
                    Nat.le_refl _, compactMem_cast hm5 (by
                      dsimp only [s_final, sc_final]; simp only [← hncv_bv]; rfl)⟩
                · have hge_mv : c.mv ≤ ncv.toNat := by
                    have h1 : ¬ ncv.toNat < c.mv % 2 ^ 64 := hc
                    rw [Nat.mod_eq_of_lt hc_mv_lt] at h1
                    exact Nat.le_of_not_lt h1
                  c0_hsteps
                  exact hJmv () _ ⟨c, FullCfgCompat.refl c, hge_mv,
                    compactMem_cast (by assumption) (by dsimp only [s_final, sc_final]; rfl)⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
