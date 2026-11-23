/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof0
public import LeanQbe.T.Examples.Kissat.FullM7Proof
public import LeanQbe.T.Examples.Kissat.FullM7Splice

import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M7` Upstream Schedule & Probe Fix Proofs (`FullM7FidelitySchedFixProof`)

M1-clean, UNSAT-only completion (`public section`, `0` `@[expose]`, `XPost := False`, `0` SAT):
1. `full_probe_fid2_wp` (`FullM6Orch.m6ProbeSpec`, Q16 `NLOGN`, `src/probe.c:33-68` ordering,
   `backboneeffort = 20`, `factordelay = 4`).
2. `full_preprocess_fid2_wp` (`FullM6.fullM6PreprocessSpec`, `fastel = 0`).
3. Closed `37`-row `fidSchedFixSpecTable`, `fidSchedFixEnv`, `fidSchedFix_tableImpl`, and
   `fidSchedFix_moduleOk` + concrete `Mem 64` UNSAT NV (`nv_fid2_*`, `XPost := False`).
4. `FullM7Splice.patchFns` / `patchRows` compatibility over `FullM7.m7Module`:
   `fidSchedFixPatchRows`, `m7FidSchedFixModule`, `m7FidSchedFix_acyclic`,
   `m7FidSchedFix_moduleOk`, `m7FidSchedFix_solve_bytes_sound`, and `m7FidSchedFix_unsat_nv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix

open Std Std.Sat Std.ExtHashMap LeanQbe.T.Examples.LratBytes
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics
open Kraken.Bedrock2.Test

/-! ## 1. `full_probe_fid2_wp` (`FullM6Orch.m6ProbeSpec`) -/

section ProbeFid2

private theorem fid2_probe_ret_wm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s0 s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hk_ret : k () = .ret (Arg.imm r, ()))
    (hargs : vals args = (c.hdr, 0#64, BitVec.ofNat 64 s.scratch.search_ticks.toNat, ()) ∨
      vals args = (c.hdr, 0#64, s.scratch.search_ticks, ()))
    (hSetWm : ∀ a m' Q' X', m6HdrW2aSpec [i64, i64] [] a m' Q' X' →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hfu : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hr : r = 1#64 ∨ r = 20#64) (hu : r = 20#64 → F0.Unsat)
    (h1 : r = 1#64 → FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (.call "m6_hdr_set_watermark" (as := [i64, i64, i64]) (bs := []) args k) m := by
  obtain ⟨v, hv⟩ : ∃ v, vals args = (c.hdr, 0#64, v, ()) :=
    hargs.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  refine m6Hdr_call_m6HdrW2a hv (fun _ _ h => hSetWm _ _ _ _ h) hcfg hext hlen hm
    fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
  rw [hk_ret]; c0_hsteps_nogrp
  exact hQ ext' s' m' hlen' hext' (by rw [hc']; exact hfu) hr hu
    (fun h => let ⟨hi, hcl⟩ := h1 h
      ⟨fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hi hlen' hc' hms') hext',
        by rw [hc']; exact hcl⟩) hm'

private theorem fid2_dense_inconsistent_unsat {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} (hd : FullDenseInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat := by
  obtain ⟨F_cur, hw⟩ := hd.1.witness
  exact hw.ext_sound.2 (hw.inconsistent_sound hinc)

/-- Parametric `Func.wp` proof for `full_probe_fid2_body` against `FullM6Orch.m6ProbeSpec`. -/
theorem full_probe_fid2_wp (Γ : Env)
    (hDticks : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebuild : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweep : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X → Func.wp Γ full_probe_fid2_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_fid2_body full_probe_m6_body
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDticks _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths hm
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := hc0 ▸ hcl0
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ mW => ∃ extW sW, FullM6HdrInv c F0 extW sW ∧
        sW.core.cur_level = 0 ∧ sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c extW sW ⋆ R) mW) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ mW ⟨extW, sW, hinvW, hclW, hfuW, hmW⟩
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ mT => ∃ extT sT, FullM6HdrInv c F0 extT sT ∧
          sT.core.cur_level = 0 ∧ sT.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullM6HdrMem c extT sT ⋆ R) mT) ?_ ?_
      · rintro _ _ mT ⟨extT, sT, hinvT, hclT, hfuT, hmT⟩
        refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
        c0_hsteps_nogrp
        refine wp_loop_inv (fun (fr, fp, ()) mL => mL = mT ∧ fr.toNat ≤ 19)
          (fun (fr, _, _) _ => 19 - fr.toNat)
          (fun JL hJL => by
            c0_hsteps_nogrp
            exact hJL (1#64, 10#64, ()) mT ⟨rfl, by decide⟩)
          (fun JL (fr, fp, ()) mL ⟨hmL, hfr_le⟩ hJL => ?_)
        · have hmTfl : (FullMem c sT ⋆ (m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R)) mL := hmL ▸ hmTf
          refine wp_join_group (ts := []) (fun _ mEx => mEx = mL) ?_ ?_
          · rintro _ _ mEx hmEx
            have hmTex : (FullMem c sT ⋆ (m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R)) mEx :=
              hmEx ▸ hmTfl
            refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma => ma = mEx) ?_ ?_
            · rintro _ ⟨fe5, ⟨⟩⟩ ma hma
              have hmTfa : (FullMem c sT ⋆ (m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R)) ma :=
                hma ▸ hmTex
              refine wp_join_group (ts := []) (fun _ mRet => ∃ extRet sRet,
                  FullM6HdrInv c F0 extRet sRet ∧ sRet.core.cur_level = 0 ∧
                  sRet.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullM6HdrMem c extRet sRet ⋆ R) mRet) ?_ ?_
              · rintro _ _ mRet ⟨extRet, sRet, hinvRet, hclRet, hfuRet, hmRet⟩
                refine wp_m6Hdr_focus_frame hmRet fun hmRetf => ?_
                c0_hsteps_nogrp
                exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvRet.cfgOk hinvRet.extOk
                  hinvRet.sparse.lengths hfuRet (Or.inl rfl) (fun h => by cases h)
                  (fun _ => ⟨hinvRet, hclRet⟩) (fullM6HdrMem_unfocus hmRetf) (hQ 1#64)
              · intro Jret hJret; c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mInc => ∃ extInc sInc,
                    FullM6HdrInv c F0 extInc sInc ∧ sInc.core.cur_level = 0 ∧
                    sInc.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extInc sInc ⋆ R) mInc) ?_ ?_
                · rintro _ _ mInc ⟨extInc, sInc, hinvInc, hclInc, hfuInc, hmInc⟩
                  refine wp_m6Hdr_focus_frame hmInc fun hmIncf => ?_
                  c0_hsteps_nogrp
                  · exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvInc.cfgOk hinvInc.extOk
                      hinvInc.sparse.lengths hfuInc (Or.inr rfl)
                      (fun _ => fullM6HdrInv_inconsistent_unsat hinvInc ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmIncf) (hQ 20#64)
                  · exact hJret () mInc
                      ⟨extInc, sInc, hinvInc, hclInc, hfuInc, fullM6HdrMem_unfocus hmIncf⟩
                · intro Jinc hJinc; c0_hsteps_nogrp
                  · c0_call hEnter
                    refine ⟨c, F0, sT, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hinvT.sparse,
                      hmTfa, fun ok sF mF hclF hfuF hdenF hspF hmF => ?_⟩
                    have hmF' := fullM6HdrMem_unfocus hmF
                    c0_hsteps_nogrp
                    · have hdenF' := hdenF ‹_›
                      refine wp_join_group (ts := [i64]) (fun _ mB => mB = mF)
                        (fun _ ⟨fbud0, ⟨⟩⟩ mB hmB => by
                          subst mB
                          c0_hsteps_nogrp; c0_call hMin; intro fbud _; c0_hsteps_nogrp
                          c0_call hFactor
                          refine ⟨c, F0, sF, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hdenF',
                            hmF, fun _ sFc mFc hdenFc _ hfuFc _ hmFc => ?_⟩
                          c0_hsteps_nogrp; c0_call hRebuild
                          refine ⟨c, F0, sFc, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hdenFc,
                            hmFc, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                          have hinvR := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk hspR
                          have hmR' := fullM6HdrMem_unfocus hmR
                          have hfuR' : sR.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            rw [hfuFc] at hfuR; exact Nat.le_trans hfuR (Nat.le_trans hfuF hfuT)
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                            c0_hsteps_nogrp
                            exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                              hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                          · exact hJret () mR ⟨extT, sR, hinvR, hclR, hfuR', hmR'⟩)
                        (fun _ hJ0 => by c0_hsteps_nogrp <;> exact hJ0 (_, ()) mF rfl)
                    · have hinvF := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk (hspF ‹_›)
                      exact hJinc () mF ⟨extT, sF, hinvF, hclF, Nat.le_trans hfuF hfuT, hmF'⟩
                  · exact hJinc () ma ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTfa⟩
            · intro Je hJe; c0_hsteps_nogrp <;> exact hJe (_, ()) mEx rfl
          · intro Jex hJex; c0_hsteps_nogrp
            · have hfr_lt : fr.toNat < 19 := BitVec.lt_def.mp ‹_›
              have hfr1 : (fr + 1#64).toNat = fr.toNat + 1 := by c0_bound
              exact hJL (fr + 1#64, _, ()) mL (by dsimp only; omega) ⟨hmL, by omega⟩
            · exact hJex () mL rfl
            · exact hJex () mL rfl
      · intro JT hJT; c0_hsteps_nogrp
        · refine wp_m6Hdr_focus_frame hmW fun hmWf => ?_
          c0_hsteps_nogrp
          · c0_call hBackbone
            refine ⟨c, F0, sW, m6ExtMem (m6ExtAddr c.hdr) extW ⋆ R, rfl, hinvW.sparse, hmWf,
              fun rB sB mB hspB hclB _ hfuB hdB huB hmB => ?_⟩
            have hinvB := FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk hspB
            have hmB' := fullM6HdrMem_unfocus hmB
            c0_hsteps_nogrp
            · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
              c0_hsteps_nogrp
              exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                hinvB.sparse.lengths (Nat.le_trans hfuB hfuW) (Or.inr rfl)
                (fun _ => huB ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
            · exact hJT () mB ⟨extW, sB, hinvB, hclB, Nat.le_trans hfuB hfuW, hmB'⟩
          · exact hJT () mW ⟨extW, sW, hinvW, hclW, hfuW, fullM6HdrMem_unfocus hmWf⟩
        · c0_call hTail
          refine m6ProbeTailSpec_of hinvW hclW hmW
            fun rT extT sT mT hlT heT hfuT hdT huT h1T hmT => ?_
          c0_hsteps_nogrp
          · refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
            c0_hsteps_nogrp
            exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvW.cfgOk heT hlT
              (Nat.le_trans hfuT hfuW) (Or.inr rfl) (fun _ => huT ‹_›)
              (fun h => by cases h) (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
          · exact hJT () mT ⟨extT, sT, (h1T (hdT.resolve_right ‹_›)).1,
              (h1T (hdT.resolve_right ‹_›)).2, Nat.le_trans hfuT hfuW, hmT⟩
    · intro JW hJW; c0_hsteps_nogrp
      refine wp_loop_inv (fun (round, ()) mL => round.toNat ≤ 2 ∧
          ∃ extL sL, FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
            sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL)
        (fun (round, ()) _ => 2 - round.toNat)
        (fun JL hJL => by
          c0_hsteps_nogrp
          exact hJL (0#64, ()) m1 ⟨Nat.zero_le _, ext1, s1, hinv1, hcl1,
            by rw [hfu1]; exact Nat.le_refl _, hm1⟩)
        (fun JL (round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ hJL => ?_)
      · c0_hsteps_nogrp
        · have hnd_lt : round.toNat < 2 := BitVec.lt_def.mp ‹_›
          have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
          refine wp_join_group (ts := []) (fun _ mV => ∃ extV sV, FullM6HdrInv c F0 extV sV ∧
              sV.core.cur_level = 0 ∧ sV.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extV sV ⋆ R) mV) ?_ ?_
          · rintro _ _ mV ⟨extV, sV, hinvV, hclV, hfuV, hmV⟩
            refine wp_m6Hdr_focus_frame hmV fun hmVf => ?_
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mD => ∃ extD sD, FullM6HdrInv c F0 extD sD ∧
                sD.core.cur_level = 0 ∧ sD.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c extD sD ⋆ R) mD) ?_ ?_
            · rintro _ _ mD ⟨extD, sD, hinvD, hclD, hfuD, hmD⟩
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ mS => ∃ extS sS, FullM6HdrInv c F0 extS sS ∧
                  sS.core.cur_level = 0 ∧ sS.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullM6HdrMem c extS sS ⋆ R) mS) ?_ ?_
              · rintro _ _ mS ⟨extS, sS, hinvS, hclS, hfuS, hmS⟩
                refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
                c0_hsteps_nogrp
                · exact hJW (round, ()) mS
                    ⟨extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
                · exact hJL (round + 1#64, ()) mS (by dsimp only; omega)
                    ⟨by omega, extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
              · intro JS hJS; refine wp_m6Hdr_focus_frame hmD fun hmDf => ?_
                c0_hsteps_nogrp
                · c0_call hSubst
                  refine ⟨c, F0, sD, m6ExtMem (m6ExtAddr c.hdr) extD ⋆ R, rfl, hinvD.sparse, hmDf,
                    fun rS sS mS hspS hclS hfuS hdS huS hmS => ?_⟩
                  have hinvS := FullM6HdrInv.mk_inv hinvD.cfgOk hinvD.extOk hspS
                  have hmS' := fullM6HdrMem_unfocus hmS
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                    c0_hsteps_nogrp
                    exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvS.cfgOk hinvS.extOk
                      hinvS.sparse.lengths (Nat.le_trans hfuS hfuD) (Or.inr rfl)
                      (fun _ => huS ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmSf)
                      (hQ 20#64)
                  · exact hJS () mS ⟨extD, sS, hinvS, hclS, Nat.le_trans hfuS hfuD, hmS'⟩
                · exact hJS () mD ⟨extD, sD, hinvD, hclD, hfuD, fullM6HdrMem_unfocus hmDf⟩
            · intro JD hJD
              c0_hsteps_nogrp; c0_call hEnter
              refine ⟨c, F0, sV, m6ExtMem (m6ExtAddr c.hdr) extV ⋆ R, rfl, hinvV.sparse, hmVf,
                fun ok sE mE hclE hfuE hdenE hspE hmE => ?_⟩
              have hmE' := fullM6HdrMem_unfocus hmE
              c0_hsteps_nogrp
              · have hdenE' := hdenE ‹_›
                refine wp_join_group (ts := [i64]) (fun (dok, ()) mC => ∃ extC sC,
                    FullM6HdrCfgOk c ∧ M6HdrExtOk extC ∧
                    (if dok = 0#64 then FullSparseInv c F0 sC ∧ sC.core.cur_level = 0
                     else FullDenseInv c F0 sC) ∧
                    sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
                · rintro _ ⟨dok, ⟨⟩⟩ mC ⟨extC, sC, _, hextC, hinvC, hfuC, hmC⟩
                  refine wp_join_group (ts := []) (fun _ mD1 => ∃ extD1 sD1,
                      FullM6HdrInv c F0 extD1 sD1 ∧ sD1.core.cur_level = 0 ∧
                      sD1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c extD1 sD1 ⋆ R) mD1)
                    (fun _ _ mD1 ⟨extD1, sD1, hinvD1, hclD1, hfuD1, hmD1⟩ =>
                      hJD () mD1 ⟨extD1, sD1, hinvD1, hclD1, hfuD1, hmD1⟩) ?_
                  intro JD1 hJD1
                  c0_hsteps_nogrp
                  · have hdok_ne : dok ≠ 0#64 := ‹_›
                    rw [ite_eq_right hdok_ne] at hinvC
                    refine wp_join_group (ts := []) (fun _ mW2 => ∃ extW2 sW2,
                        FullM6HdrCfgOk c ∧ M6HdrExtOk extW2 ∧ FullDenseInv c F0 sW2 ∧
                        sW2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extW2 sW2 ⋆ R) mW2) ?_ ?_
                    · rintro _ _ mW2 ⟨extW2, sW2, _, hextW2, hdenW2, hfuW2, hmW2⟩
                      refine wp_m6Hdr_focus_frame hmW2 fun hmW2f => ?_
                      c0_hsteps_nogrp; c0_call hRebuild
                      refine ⟨c, F0, sW2, m6ExtMem (m6ExtAddr c.hdr) extW2 ⋆ R, rfl, hdenW2,
                        hmW2f, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextW2 hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      have hfuR' := Nat.le_trans hfuR hfuW2
                      c0_hsteps_nogrp
                      · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                          hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                          (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                      · exact hJD1 () mR ⟨extW2, sR, hinvR, hclR, hfuR', hmR'⟩
                    · intro JW2 hJW2
                      refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                        hinvV.cfgOk hextC hinvC.lengths hmC
                        fun ⟨del2, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                      have hdenCd := fullDenseInv_of_core_eq hinvC hlCd hcCd hmsCd.extPres
                      have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hcCd]; exact hfuC
                      c0_hsteps_nogrp
                      · exact hJW2 () mCd ⟨extCd, sCd, hinvV.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩
                      · refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                        c0_hsteps_nogrp; c0_call hSweep
                        refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenCd,
                          hmCdf, fun rS sS mS hdenS _ hfuS _ huS hmS => ?_⟩
                        have hfuS' := Nat.le_trans hfuS hfuCd
                        c0_hsteps_nogrp
                        · c0_call hRebuild
                          refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenS,
                            hmS, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                          have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextCd hspR
                          have hmR' := fullM6HdrMem_unfocus hmR
                          refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                          c0_hsteps_nogrp
                          exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                            hinvR.sparse.lengths (Nat.le_trans hfuR hfuS') (Or.inr rfl)
                            (fun _ => huS ‹_›) (fun h => by cases h)
                            (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                        · have hmS' := fullM6HdrMem_unfocus hmS
                          refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                              M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                              sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                            (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ =>
                              hJW2 () mSd ⟨extSd, sSd, hinvV.cfgOk, hextSd, hdenSd, hfuSd, hmSd⟩)
                            ?_
                          intro JSd hJSd; c0_hsteps_nogrp
                          refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                              M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                              sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                            (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ => by
                              refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                                hinvV.cfgOk hextSd hdenSd.lengths hmSd
                                fun _ extSd' sSd' mSd' hcSd hlSd hmsSd hextSd' _ hmSd' => ?_
                              exact hJSd () mSd' ⟨extSd', sSd', hextSd',
                                fullDenseInv_of_core_eq hdenSd hlSd hcSd hmsSd.extPres,
                                by rw [hcSd]; exact hfuSd, hmSd'⟩) ?_
                          intro JSdb hJSdb
                          refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                          c0_hsteps_nogrp
                          · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                              hinvV.cfgOk hextCd hdenS.lengths (fullM6HdrMem_unfocus hmSf)
                              fun _ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                            exact hJSd () mSd ⟨extSd, sSd, hextSd,
                              fullDenseInv_of_core_eq hdenS hlSd hcSd hmsSd.extPres,
                              by rw [hcSd]; exact hfuS', hmSd⟩
                          · exact hJSdb () mS
                              ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
                          · exact hJSdb () mS
                              ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
                  · rw [ite_eq_left (‹dok = 0#64›)] at hinvC
                    exact hJD1 () mC
                      ⟨extC, sC, FullM6HdrInv.mk_inv hinvV.cfgOk hextC hinvC.1, hinvC.2, hfuC, hmC⟩
                · intro JC hJC
                  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                    hinvV.cfgOk hinvV.extOk hdenE'.lengths hmE'
                    fun ⟨del1, ⟨⟩⟩ extEd sEd mEd hcEd hlEd hmsEd hextEd _ hmEd => ?_
                  have hdenEd := fullDenseInv_of_core_eq hdenE' hlEd hcEd hmsEd.extPres
                  have hfuEd : sEd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                    rw [hcEd]; exact Nat.le_trans hfuE hfuV
                  c0_hsteps_nogrp
                  · exact hJC (1#64, ()) mEd
                      ⟨extEd, sEd, hinvV.cfgOk, hextEd,
                        by rw [ite_eq_right (by decide)]; exact hdenEd,
                        hfuEd, hmEd⟩
                  · refine wp_m6Hdr_focus_frame hmEd fun hmEdf => ?_
                    c0_hsteps_nogrp; c0_call hCong
                    refine ⟨c, F0, sEd, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenEd, hmEdf,
                      fun rC sC mC hdenC _ hfuC hdomC huC hmC => ?_⟩
                    have hfuC' : sC.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfuC]; exact hfuEd
                    c0_hsteps_nogrp
                    · c0_call hRebuild
                      refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenC, hmC,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextEd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                        (fun _ => huC ‹_›) (fun h => by cases h)
                        (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                    · have hmC' := fullM6HdrMem_unfocus hmC
                      refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                          M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                          sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                        (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ => by
                          refine wp_join_group (ts := [i64]) (fun (dok2, ()) mDn => ∃ extDn sDn,
                              FullM6HdrCfgOk c ∧ M6HdrExtOk extDn ∧
                              (if dok2 = 0#64 then FullSparseInv c F0 sDn ∧ sDn.core.cur_level = 0
                               else FullDenseInv c F0 sDn) ∧
                              sDn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extDn sDn ⋆ R) mDn)
                            (fun _ ⟨dok2, ⟨⟩⟩ mDn ⟨extDn, sDn, _, hextDn, hinvDn, hfuDn, hmDn⟩ =>
                              hJC (dok2, ()) mDn
                                ⟨extDn, sDn, hinvV.cfgOk, hextDn, hinvDn, hfuDn, hmDn⟩) ?_
                          intro Jdn hJdn; c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                            c0_hsteps_nogrp; c0_call hRebuild
                            refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenCd,
                              hmCdf, fun rR sR mR hspR hclR hfuR hdomR huR hmR => ?_⟩
                            have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextCd hspR
                            have hmR' := fullM6HdrMem_unfocus hmR
                            have hfuR' := Nat.le_trans hfuR hfuCd
                            c0_hsteps_nogrp
                            · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                              c0_hsteps_nogrp
                              exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk
                                hinvR.extOk hinvR.sparse.lengths hfuR' (Or.inr rfl)
                                (fun _ => huR ‹_›) (fun h => by cases h)
                                (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                            · refine wp_join_group (ts := []) (fun _ mSb => ∃ extSb sSb,
                                  FullM6HdrInv c F0 extSb sSb ∧ sSb.core.cur_level = 0 ∧
                                  sSb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  (FullM6HdrMem c extSb sSb ⋆ R) mSb) ?_ ?_
                              · rintro _ _ mSb ⟨extSb, sSb, hinvSb, hclSb, hfuSb, hmSb⟩
                                refine wp_join_group (ts := [i64]) (fun (d2, ()) mE2 =>
                                    ∃ extE2 sE2, FullM6HdrCfgOk c ∧ M6HdrExtOk extE2 ∧
                                    (if d2 = 0#64
                                     then FullSparseInv c F0 sE2 ∧ sE2.core.cur_level = 0
                                     else FullDenseInv c F0 sE2) ∧
                                    sE2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                    (FullM6HdrMem c extE2 sE2 ⋆ R) mE2)
                                  (fun _ ⟨d2, ⟨⟩⟩ mE2 ⟨extE2, sE2, _, heE2, hiE2, hfE2, hmE2⟩ =>
                                    hJdn (d2, ()) mE2
                                      ⟨extE2, sE2, hinvV.cfgOk, heE2, hiE2, hfE2, hmE2⟩) ?_
                                intro JE2 hJE2
                                refine wp_m6Hdr_focus_frame hmSb fun hmSbf => ?_
                                c0_hsteps_nogrp; c0_call hEnter
                                refine ⟨c, F0, sSb, m6ExtMem (m6ExtAddr c.hdr) extSb ⋆ R, rfl,
                                  hinvSb.sparse, hmSbf,
                                  fun ok2 sE2 mE2 hclE2 hfuE2 hdenE2 hspE2 hmE2 => ?_⟩
                                have hmE2' := fullM6HdrMem_unfocus hmE2
                                c0_hsteps_nogrp
                                · exact hJE2 (1#64, ()) mE2 ⟨extSb, sE2, hinvV.cfgOk, hinvSb.extOk,
                                    by rw [ite_eq_right (by decide)]; exact hdenE2 ‹_›,
                                    Nat.le_trans hfuE2 hfuSb, hmE2'⟩
                                · have hinvE2 := FullM6HdrInv.mk_inv hinvV.cfgOk hinvSb.extOk
                                    (hspE2 ‹_›)
                                  refine wp_m6Hdr_focus_frame hmE2' fun hmE2f => ?_
                                  c0_hsteps_nogrp
                                  exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE2.cfgOk
                                    hinvE2.extOk hinvE2.sparse.lengths
                                    (Nat.le_trans hfuE2 hfuSb) (Or.inr rfl)
                                    (fun _ => fullM6HdrInv_inconsistent_unsat hinvE2 ‹_›)
                                    (fun h => by cases h) (fullM6HdrMem_unfocus hmE2f) (hQ 20#64)
                                · exact hJE2 (0#64, ()) mE2 ⟨extSb, sE2, hinvV.cfgOk, hinvSb.extOk,
                                    by rw [ite_eq_left rfl]; exact ⟨hspE2 ‹_›, hclE2⟩,
                                    Nat.le_trans hfuE2 hfuSb, hmE2'⟩
                              · intro JSb hJSb
                                refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                                c0_hsteps_nogrp
                                · c0_call hSubst
                                  refine ⟨c, F0, sR, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl,
                                    hinvR.sparse, hmRf,
                                    fun rS sS mS hspS hclS hfuS hdS huS hmS => ?_⟩
                                  have hinvS := FullM6HdrInv.mk_inv hinvV.cfgOk hextCd hspS
                                  have hmS' := fullM6HdrMem_unfocus hmS
                                  c0_hsteps_nogrp
                                  · refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                                    c0_hsteps_nogrp
                                    exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvS.cfgOk
                                      hinvS.extOk hinvS.sparse.lengths (Nat.le_trans hfuS hfuR')
                                      (Or.inr rfl) (fun _ => huS ‹_›) (fun h => by cases h)
                                      (fullM6HdrMem_unfocus hmSf) (hQ 20#64)
                                  · exact hJSb () mS
                                      ⟨extCd, sS, hinvS, hclS, Nat.le_trans hfuS hfuR', hmS'⟩
                                · exact hJSb () mR
                                    ⟨extCd, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                          · exact hJdn (1#64, ()) mCd ⟨extCd, sCd, hinvV.cfgOk, hextCd,
                              by rw [ite_eq_right (by decide)]; exact hdenCd,
                              hfuCd, hmCd⟩)
                        ?_
                      intro JCd hJCd; c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                          M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                          sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                        (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ => by
                          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                            hinvV.cfgOk hextCd hdenCd.lengths hmCd
                            fun _ extCd' sCd' mCd' hcCd hlCd hmsCd hextCd' _ hmCd' => ?_
                          exact hJCd () mCd' ⟨extCd', sCd', hextCd',
                            fullDenseInv_of_core_eq hdenCd hlCd hcCd hmsCd.extPres,
                            by rw [hcCd]; exact hfuCd, hmCd'⟩) ?_
                      intro JCdb hJCdb
                      refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                      c0_hsteps_nogrp
                      · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                          hinvV.cfgOk hextEd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                          fun _ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                        exact hJCd () mCd ⟨extCd, sCd, hextCd,
                          fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres,
                          by rw [hcCd]; exact hfuC', hmCd⟩
                      · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC',
                          fullM6HdrMem_unfocus hmCf⟩
                      · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC',
                          fullM6HdrMem_unfocus hmCf⟩
              · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hinvV.extOk (hspE ‹_›)
                refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                c0_hsteps_nogrp
                exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hinvE.extOk
                  hinvE.sparse.lengths (Nat.le_trans hfuE hfuV) (Or.inr rfl)
                  (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
              · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hinvV.extOk (hspE ‹_›)
                exact hJD () mE ⟨extV, sE, hinvE, hclE, Nat.le_trans hfuE hfuV, hmE'⟩
          · intro JV hJV; c0_hsteps_nogrp
            · exact hJV () mL ⟨extL, sL, hinvL, hclL, hfuL, hmL⟩
            · c0_call hViv
              refine FullM6OrchAdapters.m6aVivifySpec_of hinvL.cfgOk hinvL.extOk hinvL.sparse hmL
                fun rV extV sV mV ⟨hextV, _⟩ hspV ⟨hclV, _⟩ hfuV hdomV huV hmV => ?_
              have hinvV := FullM6HdrInv.mk_inv hinvL.cfgOk hextV hspV
              have hfuV' := Nat.le_trans hfuV hfuL
              c0_hsteps_nogrp
              · refine wp_m6Hdr_focus_frame hmV fun hmVf => ?_
                c0_hsteps_nogrp
                exact fid2_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvV.cfgOk hextV
                  hspV.lengths hfuV' (Or.inr rfl) (fun _ => huV ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmVf) (hQ 20#64)
              · exact hJV () mV ⟨extV, sV, hinvV, hclV, hfuV', hmV⟩
        · exact hJW (round, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, hmL⟩
  · intro J1 hJ1; c0_hsteps_nogrp
    · exact hJ1 () m0 ⟨ext0, s0, hinv0, hcl0', hc0 ▸ rfl, hm0⟩
    · refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
      c0_hsteps_nogrp
      let s0a : FullState :=
        { s0 with
          scratch := { s0.scratch with probings := s0.scratch.probings + 1#64 } }
      have hst0a := fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
        (s0.scratch.probings + 1#64)
      refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma =>
          (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) ma)
        (fun _ ⟨parg, ⟨⟩⟩ ma hma => by
          c0_hsteps_nogrp; c0_call hLog10
          refine m7Log10Q16Spec_of fun qlog _ _ => ?_
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) mb =>
              (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mb)
            (fun _ ⟨pc, ⟨⟩⟩ mb hmb => by
              c0_hsteps_nogrp; c0_call hScale
              refine ⟨c, _, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hst0a.1, hmb,
                fun sd => ?_⟩
              c0_hsteps_nogrp
              have hst1 := fullState_upd_probe_step hinv0.sparse.lengths
                (s0.scratch.conflicts + sd) (s0.scratch.probings + 1#64)
              have hinv1 := fullM6HdrInv_of_probeStep hinv0 hst1
              exact hJ1 () _ ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0',
                by rw [hst1.2.1, hc0], fullM6HdrMem_unfocus (by assumption)⟩)
            (fun Jp hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption)))
        (fun Ja hJa => by c0_hsteps_nogrp <;> exact hJa (_, ()) _ (by assumption))

end ProbeFid2

/-! ## 2. `full_preprocess_fid2_wp` (`FullM6.fullM6PreprocessSpec`) -/

section PreprocessFid2

private theorem fid2_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' →
      Γ "full_propagate" [i64] [i64] a m' Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom _ hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid2_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private abbrev Fid2PrePost (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) c' ext' s' m',
    FullM4Compact.FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' →
    M6HdrExtOk ext' → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
    s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
    (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
    (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem fid2Pre_ret10 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (10#64, ()) m' :=
  hQ 10#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk
    (Or.inr (Or.inr (Or.inl rfl))) hfu (fun h => by cases h) (fun h => by cases h)
    (fun _ => hinv.sparse.2.2.2.1.2) hm

private theorem fid2Pre_ret20 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hlen : s'.LengthsOk c') (hcfg : FullM6HdrCfgOk c') (hext : M6HdrExtOk ext')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hu : F0.Unsat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (20#64, ()) m' :=
  hQ 20#64 c' ext' s' m' hcmp hlen hcfg hext (Or.inr (Or.inr (Or.inr rfl))) hfu
    (fun _ => hu) (fun h => by cases h) (fun h => by cases h) hm

private theorem fid2Pre_ret20_inc {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hinc : s'.core.inconsistent ≠ 0#64) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (20#64, ()) m' :=
  fid2Pre_ret20 hQ hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk hfu
    (fullM6HdrInv_inconsistent_unsat hinv hinc) hm

private theorem fid2Pre_ret0_inv {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (0#64, ()) m' :=
  hQ 0#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk (Or.inl rfl) hfu
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm

private theorem fid2_pre_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {Q : Post [i64]} {X : XPost} {J2 : Cont []}
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hinv1 : FullM6HdrInv c F0 ext s1) (hcl1' : s1.core.cur_level = 0)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm1 : (FullM6HdrMem c ext s1 ⋆ R) m1)
    (hJ2 : ∀ xs m2, (∃ s2, FullM6HdrInv c F0 ext s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s2 ⋆ R) m2) → J2 xs m2)
    (hQ : Fid2PrePost c F0 s R Q) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_7 =>
      Expr.load i64 (Arg.var p_7.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_8 =>
          Expr.jnz (Arg.var p_8.fst)
            (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ())
                fun p_9 =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_9.fst, Arg.imm 2, ()))
                  fun p_10 =>
                Expr.jnz (Arg.var p_10.fst) (Expr.ret (Arg.imm 20, ()))
                  (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                      fun p_11 =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                        (Arg.var p_11.fst, Arg.imm 1, ())) fun p_12 =>
                      Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm 20, ()))
                        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                          Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump J2 ()))))
            (Expr.jump J2 ())) m1 := by
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
    c0_call hSweep
    refine ⟨c, F0, F_cur1, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
      hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2,
      fun hpos => by omega, hm1f,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
        wu' fred' ni' nr' nb' oom' sc' mS hlenS hsr hexlenS hws2S hllS hwS hndS
        _ _ _ h20S _ hmS => ?_⟩
    have hmS' := fullM6HdrMem_unfocus hmS
    let sSc : FullCoreState := { s1.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      arena := arena', arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := 0#64,
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      oom := oom' }
    let sS : FullState := { core := sSc, scratch := sc' }
    have hinvWS : FullM6HdrInvW c F0 F_cur1 ext sS :=
      FullM6HdrInvW.mk_inv hinv1.cfgOk hinv1.extOk
        ⟨hlenS, hwS, hinv1.sparse.2.1, hndS,
          ⟨hllS, (by change sc'.extend_len ≤ c.extend_cap; rw [hexlenS]
                     exact hinv1.sparse.2.2.2.1.2)⟩,
          hinv1.sparse.2.2.2.2⟩
    c0_hsteps_nogrp
    · exact fid2Pre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfu1 (h20S ‹_›).2 hmS'
    · refine fid2_call_bcp rfl hProp hinvWS hmS'
        fun pr sP mP hinvWP hclP _ _ hfuP _ hrP1 hmP => ?_
      have hinvP := hinvWP.toInv; have hfuP' := Nat.le_trans hfuP hfu1
      c0_hsteps_nogrp
      · exact fid2Pre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk hinvP.extOk hfuP'
          (fid2_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hcl1') (hrP1 ‹_›).2.2) hmP
      · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
        c0_hsteps_nogrp
        have hinvP' : FullM6HdrInv c F0 ext
            { sP with core := { sP.core with unflushed := 0#64 } } :=
          FullM6HdrInv.mk_inv hinvP.cfgOk hinvP.extOk ⟨⟨⟨{ hinvP.sparse.lengths.core_ok with
              vals_len := hinvP.sparse.lengths.core_ok.vals_len }, hinvP.sparse.lengths.scratch_ok⟩,
            ⟨F_cur1, { hinvWP.sparseW.2.1 with
              arena := { hinvWP.sparseW.2.1.arena with len_ok := hinvWP.sparseW.2.1.arena.len_ok }
              watches := hinvWP.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
              }⟩⟩, hinvP.sparse.2.1, hinvP.sparse.2.2.1, hinvP.sparse.2.2.2.1, hinvP.sparse.2.2.2.2⟩
        exact hJ2 () _ ⟨_, hinvP', hclP ▸ hcl1', hfuP', fullM6HdrMem_unfocus (by assumption)⟩
  · exact hJ2 () m1 ⟨s1, hinv1, hcl1', hfu1, fullM6HdrMem_unfocus hm1f⟩

private theorem fid2_pre_compact_step {Γ : Env} {c c0 : FullCfg} {hdr : BitVec 64}
    {F0 : CNF Nat} {ext : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [i64]} {X : XPost} {JC : Cont []}
    (hCompNeed : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hhdr : c0.hdr = hdr)
    (hcmp0 : FullM4Compact.FullCfgCompat c c0) (hinv0 : FullM6HdrInv c0 F0 ext s0)
    (hcl0 : s0.core.cur_level = 0) (hfu0 : s0.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm0f : (FullMem c0 s0 ⋆ (m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R)) m0)
    (hJC : ∀ xs mC, (∃ cC sC, FullM4Compact.FullCfgCompat c cC ∧
      FullM6HdrInv cC F0 ext sC ∧ sC.core.cur_level = 0 ∧
      sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem cC ext sC ⋆ R) mC) → JC xs mC)
    (hQ : Fid2PrePost c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var hdr, ())
        fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var hdr, ()) fun p_13 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 20, ()))
              fun p_14 =>
            Expr.jnz (Arg.var p_14.fst) (Expr.ret (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
                  fun p_15 =>
                Expr.jnz (Arg.var p_15.fst) (Expr.ret (Arg.imm 0, ())) (Expr.jump JC ())))
        (Expr.jump JC ())) m0 := by
  subst hhdr
  have hlen0 := hinv0.sparse.lengths
  c0_hsteps_nogrp; c0_call hCompNeed
  refine ⟨c0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hlen0,
    by have := hlen0.core_ok.trail_end_le; have := hlen0.core_ok.cur_vars_le
       have := c0.hmaxv; unfold dimacsBound at *; omega,
    hm0f, fun need _ => ?_⟩
  c0_hsteps_nogrp
  · c0_call hCompact
    refine ⟨c0, F0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hinv0.sparse, hm0f,
      fun rC cC sC mC hcmpC hspC hrC _ hfuC huC h1C hmC => ?_⟩
    have hcfgC := M6HdrCfgOk_of_le (by rw [hcmpC.hdr]; exact M6HdrCfgOk_le hinv0.cfgOk)
    have hinvC := FullM6HdrInv.mk_inv hcfgC hinv0.extOk hspC; have hfuC' := Nat.le_trans hfuC hfu0
    have hmC' := fullM6HdrMem_unfocus (hcmpC.hdr ▸ hmC); have hcmpC' := hcmp0.trans hcmpC
    c0_hsteps_nogrp
    · exact fid2Pre_ret20 hQ hcmpC' hspC.lengths hcfgC hinvC.extOk hfuC' (huC ‹_›) hmC'
    · exact fid2Pre_ret0_inv hQ hcmpC' hinvC hfuC' hmC'
    · exact hJC () mC ⟨cC, sC, hcmpC', hinvC, h1C ‹_›, hfuC', hmC'⟩
  · exact hJC () m0 ⟨c0, s0, hcmp0, hinv0, hcl0, hfu0, fullM6HdrMem_unfocus hm0f⟩

/-- Parametric `Func.wp` proof for `full_preprocess_fid2_body` against `fullM6PreprocessSpec`
(`fastel = 0`). -/
theorem full_preprocess_fid2_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X →
      Γ "full_lucky" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ full_preprocess_fid2_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_preprocess_fid2_body full_preprocess_m6_body
  obtain ⟨F_cur, hw0⟩ := hinv.sparse.1.witness
  have hinvW0 : FullM6HdrInvW c F0 F_cur ext s := FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
    ⟨hinv.sparse.lengths, hw0, hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1,
      hinv.sparse.2.2.2.2⟩
  c0_hsteps_nogrp
  refine fid2_call_bcp rfl hProp hinvW0 hm
    fun r1 s1 m1 hinvW1 hcl1 _ _ hfu1 _ hr1_1 hm1 => ?_
  have hinv1 := hinvW1.toInv; have hcl1' : s1.core.cur_level = 0 := hcl1 ▸ hcl0
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · exact fid2Pre_ret20 hQ (.refl c) hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk hfu1
      (fid2_conflict_level0_unsat hinvW1.sparseW.2.1 hcl1' (hr1_1 ‹_›).2.2)
      (fullM6HdrMem_unfocus hm1f)
  · exact fid2Pre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · exact fid2Pre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hsteps_nogrp
      · exact fid2Pre_ret10 hQ (.refl c) hinv2 hfu2 (fullM6HdrMem_unfocus hm2f)
      · c0_call hLucky
        refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hcl2, hm2f,
          fun lk s3 m3 hlen3 hlk hfu3 _ hu3 hsp3 h10_3 hm3 => ?_⟩
        have hm3' := fullM6HdrMem_unfocus hm3; have hfu3' := Nat.le_trans hfu3 hfu2
        let mkInv3 : lk ≠ 20#64 → lk ≠ 10#64 →
            FullM6HdrInv c F0 ext s3 ∧ s3.core.cur_level = 0 := fun h20 h10 =>
          let h02 : lk = 0#64 ∨ lk = 2#64 := by
            rcases hlk with rfl | rfl | rfl | rfl <;>
              (first | exact Or.inl rfl | exact Or.inr rfl | contradiction)
          let ⟨hs3, hc3⟩ := hsp3 h02
          ⟨FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hs3, hc3⟩
        c0_hsteps_nogrp
        · rw [‹lk = 20#64›]
          exact fid2Pre_ret20 hQ (.refl c) hlen3 hinv2.cfgOk hinv2.extOk hfu3' (hu3 ‹_›) hm3'
        · rw [‹lk = 10#64›]
          exact hQ 10#64 c ext s3 m3 (.refl c) hlen3 hinv2.cfgOk hinv2.extOk
            (Or.inr (Or.inr (Or.inl rfl))) hfu3' (fun _ => by cases ‹_›)
            (fun h => by cases h) (fun _ => h10_3 ‹_›) hm3'
        · exact fid2Pre_ret20_inc hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' ‹_› hm3'
        · exact fid2Pre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · exact fid2Pre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · obtain ⟨hinv3, hcl3⟩ := mkInv3 ‹_› ‹_›
          refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ c4 s4,
              FullM4Compact.FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext s4 ∧
              s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c4 ext s4 ⋆ R) m4) ?_ ?_
          · rintro _ _ m4 ⟨c4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩; rw [← hcmp4.hdr]
            refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
            c0_hsteps_nogrp
            · exact fid2Pre_ret20_inc hQ hcmp4 hinv4 hfu4 ‹_› (fullM6HdrMem_unfocus hm4f)
            · exact fid2Pre_ret0_inv hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
            · exact fid2Pre_ret10 hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
            · c0_call hScale
              refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl, hinv4.sparse.lengths,
                hm4f, fun sd1 => ?_⟩
              c0_hsteps_nogrp; c0_call hScale
              refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl,
                (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                by assumption, fun sd2 => ?_⟩
              c0_hsteps_nogrp
              have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
              have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                s4.scratch.elim_bound
              have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
              have hm4' := fullM6HdrMem_unfocus (by assumption)
              c0_call hProbe
              refine m6ProbeSpec_of hinv4' (by rw [hst4'.2.1, hst4.2.1]; exact hcl4) hm4'
                fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
              have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
              c0_hsteps_nogrp
              · exact fid2Pre_ret20 hQ hcmp4 hlen5 hinv4'.cfgOk hext5 hfu5' (hu5 ‹_›) hm5
              · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                c0_hsteps_nogrp
                · exact fid2Pre_ret20_inc hQ hcmp4 hinv5 hfu5' ‹_› (fullM6HdrMem_unfocus hm5f)
                · exact fid2Pre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                · exact fid2Pre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                · refine wp_join_group (fun (_ : Tup Val []) m6 => ∃ c6 s6,
                        FullM4Compact.FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext5 s6 ∧
                        s6.core.cur_level = 0 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c6 ext5 s6 ⋆ R) m6) ?_ ?_
                  · rintro _ _ m6 ⟨c6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
                    rw [hcmp4.hdr, ← hcmp6.hdr]
                    refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
                    c0_hsteps_nogrp
                    · exact fid2Pre_ret20_inc hQ hcmp6 hinv6 hfu6 ‹_› (fullM6HdrMem_unfocus hm6f)
                    · exact fid2Pre_ret0_inv hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                    · exact fid2Pre_ret10 hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                    · c0_call hScale
                      refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                        hinv6.sparse.lengths, hm6f, fun sd3 => ?_⟩
                      c0_hsteps_nogrp; c0_call hScale
                      refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                        (fullState_upd_probe_step hinv6.sparse.lengths sd3
                          s6.scratch.probings).1,
                        by assumption, fun sd4 => ?_⟩
                      c0_hsteps_nogrp
                      have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd3
                        s6.scratch.probings
                      have hst6' := fullState_upd_elim_step hst6.1 sd4 s6.scratch.eliminations
                        s6.scratch.elim_bound
                      have hinv6' := fullM6HdrInv_of_probeStep hinv6
                        (probeStep_trans hst6 hst6')
                      exact hQ 1#64 c6 ext5 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk
                        hinv6'.extOk (Or.inr (Or.inl rfl))
                        (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
                        (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
                        (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
                  · exact fun _ hJC2 => wp_m6Hdr_focus_frame hm5 fun hm5f =>
                      fid2_pre_compact_step hCompNeed hCompact rfl hcmp4 hinv5 hcl5 hfu5' hm5f
                        hJC2 hQ
          · exact fun _ hJC1 =>
              fid2_pre_compact_step hCompNeed hCompact rfl (.refl c) hinv3 hcl3 hfu3' hm3 hJC1 hQ
    · exact fun _ hJ2 =>
        fid2_pre_unflushed hProp hSweep hinv1 hcl1' hfu1 (fullM6HdrMem_unfocus hm1f) hJ2 hQ

end PreprocessFid2

/-! ## 3. Closed `37`-Row `fidSchedFixSpecTable`, `fidSchedFixEnv`, & `ModuleOk` -/

section ModuleOkSection

/-- `5`-row `SpecEntry` replacement list preserving exact `m7SpecTable` `Spec`s. -/
def fidSchedFixPatchRows : List SpecEntry :=
  [ ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩ ]

/-- Empty helper-row insertion list for `FullM7Splice.patchRows`. -/
def fidSchedFixPatchInsRows : List (Sym × List SpecEntry) := []

private def fidSchedFixExtRows : List SpecEntry :=
  [ ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  , ⟨"full_log10_q16_m7", [i64], [i64], m7Log10Q16Spec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], FullM6OrchAdapters.m6aVivifySpec, true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  , ⟨"full_compact_needed", [i64], [.bool], FullM6CompactFlush.fullCompactNeededM6Spec, true⟩
  , ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩ ]

/-- Closed `37`-row specification table for `fidSchedFixModule` (`5` defined functions + `32`
external callees, all `noExit = true`). -/
def fidSchedFixSpecTable : List SpecEntry := fidSchedFixPatchRows ++ fidSchedFixExtRows

theorem fidSchedFixSpecTable_length : fidSchedFixSpecTable.length = 37 := by rfl

theorem fidSchedFixSpecTable_sigs :
    fidSchedFixSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fidSchedFixModule.fns.map Fn.sig ++ fidSchedFixModule.externs.map Extern.sig := by rfl

theorem fidSchedFixSpecTable_nodup : (fidSchedFixSpecTable.map SpecEntry.name).Nodup := by
  have heq : fidSchedFixSpecTable.map SpecEntry.name =
      fidSchedFixModule.fns.map Fn.name ++ fidSchedFixModule.externs.map Extern.name := by rfl
  rw [heq]; decide

theorem fidSchedFixSpecTable_noExit : ∀ e ∈ fidSchedFixSpecTable, e.noExit = true :=
  fun e he => List.all_eq_true.mp (by rfl : fidSchedFixSpecTable.all (·.noExit) = true) e he

/-- Closed environment induced by `fidSchedFixSpecTable`. -/
def fidSchedFixEnv : Env := Env.ofTable fidSchedFixSpecTable

theorem fidSchedFixEnv_noExit : ∀ f as bs xs m Q X X',
    fidSchedFixEnv f as bs xs m Q X → fidSchedFixEnv f as bs xs m Q X' :=
  fun _ _ _ _ _ _ _ h => env_ofTable_noExit_all (by rfl) _ _ _ _ _ _ _ h

private theorem fidSchedFixEnv_row (idx : Nat) (e : SpecEntry)
    (hidx : fidSchedFixSpecTable[idx]? = some e) (xs : Tup Val e.as) (m : Mem 64) (Q : Post e.rs)
    (X : XPost) (hs : e.eff xs m Q X) : fidSchedFixEnv e.name e.as e.rs xs m Q X :=
  env_ofTable_row_at hidx fidSchedFixSpecTable_nodup hs

theorem fidSchedFix_tableImpl :
    TableImpl fidSchedFixEnv fidSchedFixFns fidSchedFixSpecTable := by
  let er := fun i n as rs sp (h : fidSchedFixSpecTable[i]? = some ⟨n, as, rs, sp, true⟩) =>
    fun a m Q X hs => fidSchedFixEnv_row i ⟨n, as, rs, sp, true⟩ h a m Q X hs
  let erM := fun i n as rs sp (h : fidSchedFixSpecTable[i]? = some ⟨n, as, rs, sp, true⟩)
      (hm : ∀ a m Q X, sp a m Q X → sp a m Q (fun _ _ _ _ => False)) =>
    fun a m Q X hs => fidSchedFixEnv_noExit _ _ _ _ _ _ _ X
      (fidSchedFixEnv_row i ⟨n, as, rs, sp, true⟩ h a m Q (fun _ _ _ _ => False) (hm a m Q X hs))
  let erW := fun i n ea rs
      (h : fidSchedFixSpecTable[i]? = some ⟨n, i64 :: ea, rs, m6HdrW2aSpec ea rs, true⟩) =>
    erM i n (i64 :: ea) rs (m6HdrW2aSpec ea rs) h fun _ _ _ _ hs => m6HdrW2aSpec_monoX hs
  have hL10 : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      fidSchedFixEnv "full_log10_q16_m7" [i64] [i64] a m Q X :=
    erM 12 _ _ _ _ rfl fun _ _ _ _ hs => m7Log10Q16Spec_monoX hs
  have hViv := erM 26 _ _ _ _ rfl fun _ _ _ _ hs => FullM6OrchAdapters.m6aVivifySpec_monoX hs
  have hTail := erM 2 _ _ _ _ rfl fun _ _ _ _ hs => m6ProbeTailSpec_monoX hs
  have hProbe := erM 3 _ _ _ _ rfl fun _ _ _ _ hs => m6ProbeSpec_monoX hs
  rw [fidSchedFixFns_eq_patchFns]
  refine tableImpl_cons
      (SpecEntry.Impl.of (full_reduce_fid2_wp fidSchedFixEnv (er 5 _ _ _ _ rfl) hL10
        (er 10 _ _ _ _ rfl) (erW 8 _ _ _ rfl) (erW 14 _ _ _ rfl) (er 9 _ _ _ _ rfl)
        (er 11 _ _ _ _ rfl) (er 6 _ _ _ _ rfl) (er 7 _ _ _ _ rfl) (er 13 _ _ _ _ rfl)))
    (tableImpl_cons
      (SpecEntry.Impl.of (full_eliminate_fid2_wp fidSchedFixEnv (er 15 _ _ _ _ rfl) hL10
        (er 16 _ _ _ _ rfl) (er 17 _ _ _ _ rfl) (er 18 _ _ _ _ rfl) (er 19 _ _ _ _ rfl)
        (er 20 _ _ _ _ rfl) (er 21 _ _ _ _ rfl)))
      (tableImpl_cons
        (SpecEntry.Impl.of (full_probe_tail_fid2_wp fidSchedFixEnv
          (er 22 _ _ _ _ rfl) (er 23 _ _ _ _ rfl)))
        (tableImpl_cons
          (SpecEntry.Impl.of (full_probe_fid2_wp fidSchedFixEnv (erW 24 _ _ _ rfl) hL10
            (er 25 _ _ _ _ rfl) hViv (er 17 _ _ _ _ rfl) (erW 27 _ _ _ rfl)
            (er 28 _ _ _ _ rfl) (er 21 _ _ _ _ rfl) (erW 14 _ _ _ rfl) (erW 29 _ _ _ rfl)
            (erW 30 _ _ _ rfl) (er 31 _ _ _ _ rfl) (er 32 _ _ _ _ rfl) hTail
            (er 22 _ _ _ _ rfl) (er 18 _ _ _ _ rfl) (er 33 _ _ _ _ rfl)))
          (tableImpl_cons
            (SpecEntry.Impl.of (full_preprocess_fid2_wp fidSchedFixEnv (er 7 _ _ _ _ rfl)
              (er 13 _ _ _ _ rfl) (er 34 _ _ _ _ rfl) (er 35 _ _ _ _ rfl) (er 36 _ _ _ _ rfl)
              (er 25 _ _ _ _ rfl) hProbe))
            (tableImpl_nil fidSchedFixEnv fidSchedFixExtRows)))))

/-- Closed `ModuleOk` for standalone `fidSchedFixModule` (`5` functions + `32` externs). -/
theorem fidSchedFix_moduleOk : ModuleOk fidSchedFixEnv fidSchedFixModule :=
  Env.ofTable_moduleOk fidSchedFix_acyclic (allFns_of_mem fidSchedFix_fns_wf) fidSchedFix_tableImpl

end ModuleOkSection

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvFid2_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 : (cnfClause [0]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1; simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvFid2_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl; have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore nvOneLitState.core → False := fun _ hr => by
    rw [show fullArenaClauseRefsCore nvOneLitState.core = [] from rfl] at hr; cases hr
  have hi0 : ∀ i, i < nvOneLitState.core.trail_end → i = 0 := fun _ hi => by rw [hte] at hi; omega
  have hL0 : ∀ L, L ≤ nvOneLitState.core.cur_level → L = 0 := fun _ hL => by rw [hcl] at hL; omega
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact .empty)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) :=
    CNF.entails_clause_def.mpr fun _ hα =>
      (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hi0 i hi]; decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hi0 i hi, hi0 j hj]
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hi0 i hi]; exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hp => by rw [hi0 j hj] at hp; exact absurd hp.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hi0 i hi]; exact hent0
      trail_pos_inv := fun i hi => by rw [hi0 i hi]; rfl
      level0_rsn_none := fun i hi _ => by rw [hi0 i hi]; rfl
      frame_trail_lt := fun L hL => by rw [hL0 L hL]; decide
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        rw [hL0 L1 (by omega), hL0 L2 hL2]; exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => absurd rfl (hi0 i hi ▸ hne)
      reason_lit_mem := fun i hi hne => absurd rfl (hi0 i hi ▸ hne) }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => (hr0 r hr).elim,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by simp only [nvOneLitState, nvOneLitScratch,
      List.getElem?_replicate, show i < 16 by omega, ↓reduceIte, Option.getD_some],
      Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem fid2_nv_wp {f : Sym} {as rs : List Ty} {sp : Spec as rs} (idx : Nat)
    (hidx : fidSchedFixSpecTable[idx]? = some ⟨f, as, rs, sp, true⟩)
    (pre post : List Fn) (fn : Fn)
    (hsplit : fidSchedFixFns = pre ++ fn :: post) (hname : fn.name = f) (has : fn.as = as)
    (hrs : fn.rs = rs) (body : Func as rs) (hbody : has ▸ hrs ▸ fn.body = body) :
    ∀ (a : Tup Val as) m Q, sp a m Q (fun _ _ _ _ => False) →
      Func.wp fidSchedFixEnv body a m Q (fun _ _ _ _ => False) := by
  subst has hrs hname hbody
  let ⟨_, _, hwp⟩ := fidSchedFix_moduleOk.fnsOk pre fn post hsplit
  exact fun a m Q hs => hwp a m Q _
    (fidSchedFixEnv_row idx ⟨fn.name, fn.as, fn.rs, sp, true⟩ hidx a m Q
      (fun _ _ _ _ => False) hs)

private theorem nvFid2_hdrMem_emp :
    (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
  rw [sep_emp]; exact nvM6HdrMem_ok

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_reduce_fid2_body`. -/
theorem nv_fid2_reduce :
    Func.wp fidSchedFixEnv full_reduce_fid2_body (nvOneLitCfg.hdr, false, ())
      nvM6HdrMem (fun (r, ()) m' => ∃ ext' s',
        FullM6HdrInvW nvOneLitCfg nvOneLitF0 [[0], [1]] ext' s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  fid2_nv_wp 0 rfl [] (fidSchedFixFns.drop 1) fidSchedFixFns[0] rfl rfl rfl rfl
    full_reduce_fid2_body rfl _ nvM6HdrMem _ (m6ReduceSpec_of (FullM6HdrInvW.mk_inv nvM6HdrCfg_ok
      nvM6ExtWords_ok nvFid2_sparseW) nvFid2_hdrMem_emp
      fun r ext' s' m' hi' hr' _ _ _ _ _ _ hu' _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hi', hr', fun h => hu' h, hm'⟩)

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_eliminate_fid2_body`. -/
theorem nv_fid2_eliminate :
    Func.wp fidSchedFixEnv full_eliminate_fid2_body (nvOneLitCfg.hdr, true, ())
      nvOneLitMem (fun (r, ()) m' => ∃ s', FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  fid2_nv_wp 1 rfl (fidSchedFixFns.take 1) (fidSchedFixFns.drop 2) fidSchedFixFns[1] rfl rfl rfl
    rfl full_eliminate_fid2_body rfl _ nvOneLitMem _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvFid2_sparseW.toSparse, rfl,
      by rw [sep_emp]; exact nvOneLitMem_ok, fun r s' m' hsp' hcl' _ hr' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp', hcl', hr', nvFid2_unsat, hm'⟩⟩

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_probe_tail_fid2_body`. -/
theorem nv_fid2_probe_tail :
    Func.wp fidSchedFixEnv full_probe_tail_fid2_body (nvOneLitCfg.hdr, 0#64, ())
      nvM6HdrMem (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  fid2_nv_wp 2 rfl (fidSchedFixFns.take 2) (fidSchedFixFns.drop 3) fidSchedFixFns[2] rfl rfl rfl
    rfl full_probe_tail_fid2_body rfl _ nvM6HdrMem _ (m6ProbeTailSpec_of (FullM6HdrInvW.mk_inv
      nvM6HdrCfg_ok nvM6ExtWords_ok nvFid2_sparseW).toInv rfl nvFid2_hdrMem_emp
      fun r ext' s' m' _ _ _ hr' hu' h1' hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hr', hu', h1', hm'⟩)

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_probe_fid2_body`. -/
theorem nv_fid2_probe :
    Func.wp fidSchedFixEnv full_probe_fid2_body (nvOneLitCfg.hdr, true, ())
      nvM6HdrMem (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  fid2_nv_wp 3 rfl (fidSchedFixFns.take 3) (fidSchedFixFns.drop 4) fidSchedFixFns[3] rfl rfl rfl
    rfl full_probe_fid2_body rfl _ nvM6HdrMem _ (m6ProbeSpec_of (FullM6HdrInvW.mk_inv
      nvM6HdrCfg_ok nvM6ExtWords_ok nvFid2_sparseW).toInv rfl nvFid2_hdrMem_emp
      fun r ext' s' m' _ _ _ hr' hu' h1' hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hr', hu', h1', hm'⟩)

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_preprocess_fid2_body`. -/
theorem nv_fid2_preprocess :
    Func.wp fidSchedFixEnv full_preprocess_fid2_body (nvOneLitCfg.hdr, ())
      nvM6HdrMem (fun (r, ()) m' => ∃ c' ext' s', FullM4Compact.FullCfgCompat nvOneLitCfg c' ∧
        s'.LengthsOk c' ∧ FullM6HdrCfgOk c' ∧ M6HdrExtOk ext' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv c' nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem c' ext' s' m')
      (fun _ _ _ _ => False) :=
  fid2_nv_wp 4 rfl (fidSchedFixFns.take 4) (fidSchedFixFns.drop 5) fidSchedFixFns[4] rfl rfl rfl
    rfl full_preprocess_fid2_body rfl _ nvM6HdrMem _ (fullM6PreprocessSpec_of (FullM6HdrInvW.mk_inv
      nvM6HdrCfg_ok nvM6ExtWords_ok nvFid2_sparseW).toInv rfl nvFid2_hdrMem_emp
      fun r c' ext' s' m' hcmp' hlen' hcfg' hext' hr' _ hu' h1' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨c', ext', s', hcmp', hlen', hcfg', hext', hr', hu', h1', hm'⟩)

end ConcreteNonVacuity

/-! ## 5. `FullM7.m7Module` `patchFns` / `patchRows` Splicing (`ModuleOk` + UNSAT NV) -/

section M7SpliceCompat

/-- `410`-function unified `M7` list patched with `fidSchedFixPatchFns` via
`FullM7Splice.patchFns`. -/
def m7FidSchedFixFns : List Fn :=
  patchFns fidSchedFixPatchFns fidSchedFixPatchBefores m7Fns

/-- Closed `410`-function `M7 + FidelitySchedFix` module (`externs := []`, `exits := []`). -/
def m7FidSchedFixModule : LeanQbe.T.Module :=
  { fns := m7FidSchedFixFns, externs := [], exits := [] }

theorem fidSchedFixPatchRows_noExit :
    fidSchedFixPatchRows.all SpecEntry.noExit = true := by rfl

private theorem m7_idx_111 : m7Fns[111]?.map Fn.sig =
    some ("full_reduce_m6", [i64, .bool], [i64]) := by
  rw [m7_get_p1 (by decide)]; t_kernel_rfl

private theorem m7_idx_385 : m7Fns[385]?.map Fn.sig =
    some ("full_eliminate_m6", [i64, .bool], [i64]) := by
  rw [show (385 : Nat) = 276 + 109 by rfl, m7_get_p3]; t_kernel_rfl

private theorem m7_idx_401 : m7Fns[401]?.map Fn.sig =
    some ("full_probe_tail_m6", [i64, i64], [i64]) := by
  rw [show (401 : Nat) = 276 + 125 by rfl, m7_get_p3]; t_kernel_rfl

private theorem m7_idx_402 : m7Fns[402]?.map Fn.sig =
    some ("full_probe_m6", [i64, .bool], [i64]) := by
  rw [show (402 : Nat) = 276 + 126 by rfl, m7_get_p3]; t_kernel_rfl

private theorem m7_idx_403 : m7Fns[403]?.map Fn.sig =
    some ("full_preprocess_m6", [i64], [i64]) := by
  rw [show (403 : Nat) = 276 + 127 by rfl, m7_get_p3]; t_kernel_rfl

theorem m7FidSchedFix_patched_rows_sigs (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (patchRows fidSchedFixPatchRows fidSchedFixPatchInsRows (m7SpecTable tBve solveSpec)).map
        (fun e => (e.name, e.as, e.rs)) =
      m7FidSchedFixFns.map Fn.sig := by
  obtain ⟨f111, hf111, hs111⟩ := sig_of_map_idx m7_idx_111
  obtain ⟨f385, hf385, hs385⟩ := sig_of_map_idx m7_idx_385
  obtain ⟨f401, hf401, hs401⟩ := sig_of_map_idx m7_idx_401
  obtain ⟨f402, hf402, hs402⟩ := sig_of_map_idx m7_idx_402
  obtain ⟨f403, hf403, hs403⟩ := sig_of_map_idx m7_idx_403
  have hsFn : ∀ r ∈ fidSchedFixPatchFns, ∀ f ∈ m7Fns, r.name = f.name → r.sig = f.sig := by
    intro r hr f hf hnm
    rw [fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
    rcases (List.mem_cons.mp hr) with rfl | hr
    · have hfx := fn_eq_of_mem_idx m7_names_nodup hf hf111
        (hnm.symm.trans (congrArg Prod.fst hs111.symm))
      subst hfx; exact hs111.symm
    rcases (List.mem_cons.mp hr) with rfl | hr
    · have hfx := fn_eq_of_mem_idx m7_names_nodup hf hf385
        (hnm.symm.trans (congrArg Prod.fst hs385.symm))
      subst hfx; exact hs385.symm
    rcases (List.mem_cons.mp hr) with rfl | hr
    · have hfx := fn_eq_of_mem_idx m7_names_nodup hf hf401
        (hnm.symm.trans (congrArg Prod.fst hs401.symm))
      subst hfx; exact hs401.symm
    rcases (List.mem_cons.mp hr) with rfl | hr
    · have hfx := fn_eq_of_mem_idx m7_names_nodup hf hf402
        (hnm.symm.trans (congrArg Prod.fst hs402.symm))
      subst hfx; exact hs402.symm
    rcases List.mem_singleton.mp hr with rfl
    · have hfx := fn_eq_of_mem_idx m7_names_nodup hf hf403
        (hnm.symm.trans (congrArg Prod.fst hs403.symm))
      subst hfx; exact hs403.symm
  have hsRow : ∀ r ∈ fidSchedFixPatchRows, ∀ e ∈ m7SpecTable tBve solveSpec,
      r.name = e.name → (r.name, r.as, r.rs) = (e.name, e.as, e.rs) := by
    intro r hr e he hnm
    have he_sig : (e.name, e.as, e.rs) ∈ (m7SpecTable tBve solveSpec).map
        (fun e => (e.name, e.as, e.rs)) :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    rw [m7SpecTable_sigs tBve solveSpec hBveSigs] at he_sig
    rcases List.mem_map.mp he_sig with ⟨f, hf, hfsig⟩
    have hrsig : (r.name, r.as, r.rs) ∈ fidSchedFixPatchFns.map Fn.sig := by
      rcases (List.mem_cons.mp hr) with rfl | hr
      · exact List.mem_map.mpr ⟨fid2ReduceM6Fn, List.mem_cons_self, rfl⟩
      rcases (List.mem_cons.mp hr) with rfl | hr
      · exact List.mem_map.mpr ⟨fid2EliminateM6Fn,
          List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
      rcases (List.mem_cons.mp hr) with rfl | hr
      · exact List.mem_map.mpr ⟨fid2ProbeTailM6Fn,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
      rcases (List.mem_cons.mp hr) with rfl | hr
      · exact List.mem_map.mpr ⟨fid2ProbeM6Fn,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩
      rcases List.mem_singleton.mp hr with rfl
      exact List.mem_map.mpr ⟨fid2PreprocessM6Fn,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))), rfl⟩
    rcases List.mem_map.mp hrsig with ⟨rfn, hrfn, hrfnsig⟩
    have h := hsFn rfn hrfn f hf
      ((congrArg Prod.fst hrfnsig).trans (hnm.trans (congrArg Prod.fst hfsig).symm))
    rw [← hfsig, ← hrfnsig]; exact h
  rw [fidSchedFixPatchInsRows, patchRows_nil, m7FidSchedFixFns, fidSchedFixPatchBefores,
    patchFns_nil, spliceRows_sigs hsRow, spliceFns_sigs hsFn,
    m7SpecTable_sigs tBve solveSpec hBveSigs]

theorem m7FidSchedFix_acyclic : m7FidSchedFixModule.checkAcyclic = true := by
  obtain ⟨f111, hf111, hs111⟩ := sig_of_map_idx m7_idx_111
  obtain ⟨f385, hf385, hs385⟩ := sig_of_map_idx m7_idx_385
  obtain ⟨f401, hf401, hs401⟩ := sig_of_map_idx m7_idx_401
  obtain ⟨f402, hf402, hs402⟩ := sig_of_map_idx m7_idx_402
  obtain ⟨f403, hf403, hs403⟩ := sig_of_map_idx m7_idx_403
  obtain ⟨g8, hg8, hs8⟩ := sig_of_map_idx (i := 8) (s := ("full_isqrt", [i64], [i64]))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g11, hg11, hs11⟩ := sig_of_map_idx (i := 11) (s := ("full_arena_next", [i64, i32], [i32]))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g31, hg31, hs31⟩ := sig_of_map_idx (i := 31)
    (s := ("full_log10_q16_m7", [i64], [i64]))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g32, hg32, hs32⟩ := sig_of_map_idx (i := 32)
    (s := ("full_scale_delta_m5", [i64, i64], [i64]))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g34, hg34, hs34⟩ := sig_of_map_idx (i := 34)
    (s := ("full_scale_delta", [i64, i64], [i64]))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g39, hg39, hs39⟩ := sig_of_map_idx (i := 39)
    (s := ("full_backtrack", [i64, i64], []))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g61, hg61, hs61⟩ := sig_of_map_idx (i := 61)
    (s := ("m6_hdr_recompute_tiers", [i64], []))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g66, hg66, hs66⟩ := sig_of_map_idx (i := 66)
    (s := ("m6_hdr_delaying", [i64, i64], [.bool]))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g67, hg67, hs67⟩ := sig_of_map_idx (i := 67)
    (s := ("m6_hdr_bump_delay", [i64, i64], []))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g68, hg68, hs68⟩ := sig_of_map_idx (i := 68)
    (s := ("m6_hdr_reduce_delay", [i64, i64], []))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g71, hg71, hs71⟩ := sig_of_map_idx (i := 71)
    (s := ("m6_hdr_set_watermark", [i64, i64, i64], []))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g86, hg86, hs86⟩ := sig_of_map_idx (i := 86) (s := ("full_propagate", [i64], [i64]))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g104, hg104, hs104⟩ := sig_of_map_idx (i := 104)
    (s := ("full_arena_sweep", [i64], [i64]))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g105, hg105, hs105⟩ := sig_of_map_idx (i := 105)
    (s := ("full_mark_reasons", [i64, .bool], []))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g109, hg109, hs109⟩ := sig_of_map_idx (i := 109)
    (s := ("full_sort_reds", [i64, i64], []))
    (by rw [m7_get_p1 (by decide)]; t_kernel_rfl)
  obtain ⟨g184, hg184, hs184⟩ := sig_of_map_idx (i := 184) (s := ("full_lucky", [i64], [i64]))
    (by rw [show (184 : Nat) = 112 + 72 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl)
  obtain ⟨g218, hg218, hs218⟩ := sig_of_map_idx (i := 218)
    (s := ("full_vivify_m6_hdr", [i64], [i64]))
    (by rw [show (218 : Nat) = 112 + 106 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl)
  obtain ⟨g226, hg226, hs226⟩ := sig_of_map_idx (i := 226)
    (s := ("full_backbone_m6", [i64, i64], [i64]))
    (by rw [show (226 : Nat) = 112 + 114 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl)
  obtain ⟨g229, hg229, hs229⟩ := sig_of_map_idx (i := 229)
    (s := ("full_transitive_m6", [i64, i64], [i64]))
    (by rw [show (229 : Nat) = 112 + 117 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl)
  obtain ⟨g235, hg235, hs235⟩ := sig_of_map_idx (i := 235)
    (s := ("full_substitute", [i64], [i64]))
    (by rw [show (235 : Nat) = 112 + 123 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl)
  obtain ⟨g236, hg236, hs236⟩ := sig_of_map_idx (i := 236)
    (s := ("full_enter_dense", [i64], [.bool]))
    (by rw [show (236 : Nat) = 112 + 124 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl)
  obtain ⟨g237, hg237, hs237⟩ := sig_of_map_idx (i := 237)
    (s := ("full_rebuild_watches", [i64], [i64]))
    (by rw [show (237 : Nat) = 112 + 125 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl)
  obtain ⟨g275, hg275, hs275⟩ := sig_of_map_idx (i := 275)
    (s := ("full_congruence_dense", [i64, i64], [i64]))
    (by rw [show (275 : Nat) = 112 + 163 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl)
  obtain ⟨g299, hg299, hs299⟩ := sig_of_map_idx (i := 299)
    (s := ("full_sweep_dense_m6", [i64, i64, i64], [i64]))
    (by rw [show (299 : Nat) = 276 + 23 by rfl, m7_get_p3]; t_kernel_rfl)
  obtain ⟨g311, hg311, hs311⟩ := sig_of_map_idx (i := 311)
    (s := ("full_forward_sub", [i64, i64], [i64]))
    (by rw [show (311 : Nat) = 276 + 35 by rfl, m7_get_p3]; t_kernel_rfl)
  obtain ⟨g352, hg352, hs352⟩ := sig_of_map_idx (i := 352)
    (s := ("full_factor", [i64, i64], [i64]))
    (by rw [show (352 : Nat) = 276 + 76 by rfl, m7_get_p3]; t_kernel_rfl)
  obtain ⟨g353, hg353, hs353⟩ := sig_of_map_idx (i := 353)
    (s := ("full_compact_needed", [i64], [.bool]))
    (by rw [show (353 : Nat) = 276 + 77 by rfl, m7_get_p3]; t_kernel_rfl)
  obtain ⟨g365, hg365, hs365⟩ := sig_of_map_idx (i := 365)
    (s := ("full_compact", [i64], [i64]))
    (by rw [show (365 : Nat) = 276 + 89 by rfl, m7_get_p3]; t_kernel_rfl)
  obtain ⟨g374, hg374, hs374⟩ := sig_of_map_idx (i := 374)
    (s := ("full_min_u64", [i64, i64], [i64]))
    (by rw [show (374 : Nat) = 276 + 98 by rfl, m7_get_p3]; t_kernel_rfl)
  obtain ⟨g376, hg376, hs376⟩ := sig_of_map_idx (i := 376)
    (s := ("full_elim_dticks", [i64, .bool], [i64]))
    (by rw [show (376 : Nat) = 276 + 100 by rfl, m7_get_p3]; t_kernel_rfl)
  obtain ⟨g383, hg383, hs383⟩ := sig_of_map_idx (i := 383)
    (s := ("full_elim_bve_m7", [i64, i64], [i64]))
    (by rw [show (383 : Nat) = 276 + 107 by rfl, m7_get_p3]; t_kernel_rfl)
  obtain ⟨g400, hg400, hs400⟩ := sig_of_map_idx (i := 400)
    (s := ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
    (by rw [show (400 : Nat) = 276 + 124 by rfl, m7_get_p3]; t_kernel_rfl)
  have hsig : ∀ r ∈ fidSchedFixPatchFns, ∀ f ∈ m7Fns, r.name = f.name → r.sig = f.sig := by
    intro r hr f hf hnm
    rw [fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf111
        (hnm.symm.trans (congrArg Prod.fst hs111.symm))
      subst hf0; exact hs111.symm
    rcases List.mem_cons.mp hr with rfl | hr
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf385
        (hnm.symm.trans (congrArg Prod.fst hs385.symm))
      subst hf0; exact hs385.symm
    rcases List.mem_cons.mp hr with rfl | hr
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf401
        (hnm.symm.trans (congrArg Prod.fst hs401.symm))
      subst hf0; exact hs401.symm
    rcases List.mem_cons.mp hr with rfl | hr
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf402
        (hnm.symm.trans (congrArg Prod.fst hs402.symm))
      subst hf0; exact hs402.symm
    rcases List.mem_singleton.mp hr with rfl
    · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf403
        (hnm.symm.trans (congrArg Prod.fst hs403.symm))
      subst hf0; exact hs403.symm
  dsimp only [m7FidSchedFixModule, m7FidSchedFixFns, fidSchedFixPatchBefores]
  rw [patchFns_nil]
  refine spliceModule_checkAcyclic (M := m7Module) m7_acyclic hsig ?_
  intro pre f post r hsplit hr hnm
  dsimp only [m7Module] at hsplit ⊢
  simp only [List.map_nil, List.append_nil] at hsplit ⊢
  rw [fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have hn0 : f.name = f111.name := hnm.symm.trans (congrArg Prod.fst hs111.symm)
    have hc : fid2ReduceM6Fn.checkCallsOk
        [ ("full_isqrt", [i64], [i64]), ("full_backtrack", [i64, i64], [])
        , ("full_propagate", [i64], [i64]), ("m6_hdr_recompute_tiers", [i64], [])
        , ("full_mark_reasons", [i64, .bool], []), ("full_arena_next", [i64, i32], [i32])
        , ("full_sort_reds", [i64, i64], []), ("full_log10_q16_m7", [i64], [i64])
        , ("full_arena_sweep", [i64], [i64])
        , ("m6_hdr_set_watermark", [i64, i64, i64], []) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs8 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg8 (by decide)
    · exact hs39 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg39 (by decide)
    · exact hs86 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg86 (by decide)
    · exact hs61 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg61 (by decide)
    · exact hs105 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg105 (by decide)
    · exact hs11 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg11 (by decide)
    · exact hs109 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg109 (by decide)
    · exact hs31 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg31 (by decide)
    · exact hs104 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg104 (by decide)
    · exact hs71 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf111 hn0 hg71 (by decide)
  rcases List.mem_cons.mp hr with rfl | hr
  · have hn0 : f.name = f385.name := hnm.symm.trans (congrArg Prod.fst hs385.symm)
    have hc : fid2EliminateM6Fn.checkCallsOk
        [ ("full_elim_dticks", [i64, .bool], [i64]), ("full_log10_q16_m7", [i64], [i64])
        , ("full_scale_delta", [i64, i64], [i64]), ("full_enter_dense", [i64], [.bool])
        , ("full_min_u64", [i64, i64], [i64]), ("full_forward_sub", [i64, i64], [i64])
        , ("full_elim_bve_m7", [i64, i64], [i64]), ("full_rebuild_watches", [i64], [i64]) ] [] =
        true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs376 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg376 (by decide)
    · exact hs31 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg31 (by decide)
    · exact hs34 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg34 (by decide)
    · exact hs236 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg236 (by decide)
    · exact hs374 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg374 (by decide)
    · exact hs311 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg311 (by decide)
    · exact hs383 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg383 (by decide)
    · exact hs237 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg237 (by decide)
  rcases List.mem_cons.mp hr with rfl | hr
  · have hn0 : f.name = f401.name := hnm.symm.trans (congrArg Prod.fst hs401.symm)
    have hc : fid2ProbeTailM6Fn.checkCallsOk
        [ ("full_backbone_m6", [i64, i64], [i64])
        , ("full_transitive_m6", [i64, i64], [i64]) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hs226 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf401 hn0 hg226 (by decide)
    · exact hs229 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf401 hn0 hg229 (by decide)
  rcases List.mem_cons.mp hr with rfl | hr
  · have hn0 : f.name = f402.name := hnm.symm.trans (congrArg Prod.fst hs402.symm)
    have hc : fid2ProbeM6Fn.checkCallsOk
        [ ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
        , ("full_log10_q16_m7", [i64], [i64]), ("full_scale_delta_m5", [i64, i64], [i64])
        , ("full_vivify_m6_hdr", [i64], [i64]), ("full_enter_dense", [i64], [.bool])
        , ("m6_hdr_delaying", [i64, i64], [.bool]), ("full_congruence_dense", [i64, i64], [i64])
        , ("full_rebuild_watches", [i64], [i64]), ("m6_hdr_set_watermark", [i64, i64, i64], [])
        , ("m6_hdr_reduce_delay", [i64, i64], []), ("m6_hdr_bump_delay", [i64, i64], [])
        , ("full_sweep_dense_m6", [i64, i64, i64], [i64]), ("full_substitute", [i64], [i64])
        , ("full_probe_tail_m6", [i64, i64], [i64]), ("full_backbone_m6", [i64, i64], [i64])
        , ("full_min_u64", [i64, i64], [i64]), ("full_factor", [i64, i64], [i64]) ] [] =
        true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact hs400 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg400 (by decide)
    · exact hs31 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg31 (by decide)
    · exact hs32 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg32 (by decide)
    · exact hs218 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg218 (by decide)
    · exact hs236 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg236 (by decide)
    · exact hs66 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg66 (by decide)
    · exact hs275 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg275 (by decide)
    · exact hs237 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg237 (by decide)
    · exact hs71 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg71 (by decide)
    · exact hs68 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg68 (by decide)
    · exact hs67 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg67 (by decide)
    · exact hs299 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg299 (by decide)
    · exact hs235 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg235 (by decide)
    · exact hs401 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hf401 (by decide)
    · exact hs226 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg226 (by decide)
    · exact hs374 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg374 (by decide)
    · exact hs352 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg352 (by decide)
  rcases List.mem_singleton.mp hr with rfl
  · have hn0 : f.name = f403.name := hnm.symm.trans (congrArg Prod.fst hs403.symm)
    have hc : fid2PreprocessM6Fn.checkCallsOk
        [ ("full_propagate", [i64], [i64]), ("full_arena_sweep", [i64], [i64])
        , ("full_lucky", [i64], [i64]), ("full_compact_needed", [i64], [.bool])
        , ("full_compact", [i64], [i64]), ("full_scale_delta_m5", [i64, i64], [i64])
        , ("full_probe_m6", [i64, .bool], [i64]) ] [] = true := by rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs86 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf403 hn0 hg86 (by decide)
    · exact hs104 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf403 hn0 hg104 (by decide)
    · exact hs184 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf403 hn0 hg184 (by decide)
    · exact hs353 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf403 hn0 hg353 (by decide)
    · exact hs365 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf403 hn0 hg365 (by decide)
    · exact hs32 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf403 hn0 hg32 (by decide)
    · exact hs402 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf403 hn0 hf402 (by decide)

/-- Generic `TableImpl` bridge over any environment `Γ` implementing all `fidSchedFixPatchFns`
callees, ready for unified Target A `FullM7Splice.patchFns` composition. -/
theorem fidSchedFixPatch_tableImpl_of (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hArenaSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hElimDt : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X → Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hProbeDt : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hScaleM5 : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweepD : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    TableImpl Γ fidSchedFixPatchFns fidSchedFixPatchRows := by
  rw [fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns]; unfold fidSchedFixPatchRows
  exact
    ⟨ SpecEntry.Impl.of (full_reduce_fid2_wp Γ hIsqrt hLog10 hArenaNext hRecomp hSetWm hMarkRsn
        hSortReds hBacktrack hProp hArenaSweep)
    , SpecEntry.Impl.of (full_eliminate_fid2_wp Γ hElimDt hLog10 hScale hEnter hMin hFwd hBve hReb)
    , SpecEntry.Impl.of (full_probe_tail_fid2_wp Γ hBone hTrans)
    , SpecEntry.Impl.of (full_probe_fid2_wp Γ hProbeDt hLog10 hScaleM5 hViv hEnter hDelay hCong
        hReb hSetWm hRedD hBumpD hSweepD hSubst hTail hBone hMin hFactor)
    , SpecEntry.Impl.of (full_preprocess_fid2_wp Γ hProp hArenaSweep hLucky hCompNeed hCompact
        hScaleM5 hProbe)
    , trivial ⟩

/-- `ModuleOk` for `m7FidSchedFixModule` (`410` fns with `fidSchedFixPatchFns` spliced in via
`patchFns`), inheriting all `405` untouched functions directly from `mkM7Env_moduleOk`. -/
theorem m7FidSchedFix_moduleOk
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hElimBve : (⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :
      SpecEntry) ∈ tBve)
    (hElimDticks : (⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve solveSpec)
    (hSweepDense : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64],
      FullDefSweep.fullSweepDenseSpec, true⟩ : SpecEntry) ∈ m7SpecTable tBve solveSpec)
    (hProbeTail : (⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve solveSpec)
    (hProbe : (⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve solveSpec)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tBve solveSpec) m7FidSchedFixModule := by
  have hm :=
    mkM7Env_moduleOk tBve solveSpec hWeaken hSolveMonoX hBveSigs hBveNoExit hBveSpecs hBveOk
  have hnd := m7SpecTable_nodup tBve solveSpec hBveSigs
  have htBve : ∀ e ∈ tBve, e ∈ m7SpecTable tBve solveSpec := m7SpecTable_tBve_mem hBveSigs
  have hc1 := m7Part1Callees_of_sub (m7SpecTable_part1_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc1p := m7Part1PfxCallees_of_sub
    (m7SpecTable_part1_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc2 := m7Part2Callees_of_sub (m7SpecTable_part2_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc2p := m7Part2PfxCallees_of_sub
    (m7SpecTable_part2_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc3p := m7Part3PfxCallees_of_sub
    (m7SpecTable_part3Pfx_mem (tBve := tBve) (solveSpec := solveSpec))
  let rProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      mkM7Env tBve solveSpec "full_propagate" [i64] [i64] a m Q X :=
    m7_fullPropagate_to_bcpS15 (mkM7Env_row_mem hnd _ _ _ _ hc1.propagate)
  let rLog10 := mkM7Env_row_mem hnd _ _ _ _ hc1.log10Q16M7
    (fun _ _ _ _ h => m7Log10Q16Spec_monoX h)
  let rArSwp := mkM7Env_row_mem hnd _ _ _ _ (m7SpecTable_pfx_mem _ m7OrchPfxRows_specs.arenaSweep)
  let rMrkRsn := mkM7Env_row_mem hnd _ _ _ _ (m7SpecTable_pfx_mem _ m7OrchPfxRows_specs.markReasons)
  have hPatch := fidSchedFixPatch_tableImpl_of (mkM7Env tBve solveSpec)
    (mkM7Env_row_mem hnd _ _ _ _ hc1.isqrt) rLog10 (mkM7Env_row_mem hnd _ _ _ _ hc1.arenaNext)
    (mkM7Env_row_mem hnd _ _ _ _ hc1p.recomputeTiers (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (mkM7Env_row_mem hnd _ _ _ _ hc1.hdrSetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    rMrkRsn (mkM7Env_row_mem hnd _ _ _ _ hc1p.sortReds)
    (mkM7Env_row_mem hnd _ _ _ _ hc1.backtrack) rProp rArSwp
    (mkM7Env_row_mem hnd _ _ _ _ hElimDticks) (mkM7Env_row_mem hnd _ _ _ _ hc1.scaleDelta)
    (mkM7Env_row_mem hnd _ _ _ _ hc2.enterDense) (mkM7Env_row_mem hnd _ _ _ _ hc3p.minU64)
    (mkM7Env_row_mem hnd _ _ _ _ (htBve _ hBveSpecs.fwdSub))
    (mkM7Env_row_mem hnd _ _ _ _ (htBve _ hElimBve))
    (mkM7Env_row_mem hnd _ _ _ _ hc2.rebuildWatches)
    (mkM7Env_row_mem hnd _ _ _ _ hc2p.backboneM6)
    (mkM7Env_row_mem hnd _ _ _ _ hc2p.transitiveM6)
    (mkM7Env_row_mem hnd _ _ _ _ hc3p.probeDticks (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (mkM7Env_row_mem hnd _ _ _ _ hc1.scaleDeltaM5)
    (mkM7Env_row_mem hnd _ _ _ _ hc2p.vivifyM6Hdr
      (fun _ _ _ _ h => FullM6OrchAdapters.m6aVivifySpec_monoX h))
    (mkM7Env_row_mem hnd _ _ _ _ hc1p.delaying (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (mkM7Env_row_mem hnd _ _ _ _ hc2p.congruenceDense)
    (mkM7Env_row_mem hnd _ _ _ _ hc1p.reduceDelay (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (mkM7Env_row_mem hnd _ _ _ _ hc1p.bumpDelay (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (mkM7Env_row_mem hnd _ _ _ _ hSweepDense) (mkM7Env_row_mem hnd _ _ _ _ hc2p.substitute)
    (mkM7Env_row_mem hnd _ _ _ _ hProbeTail (fun _ _ _ _ h => m6ProbeTailSpec_monoX h))
    (mkM7Env_row_mem hnd _ _ _ _ hc3p.factor) (mkM7Env_row_mem hnd _ _ _ _ hc2p.lucky)
    (mkM7Env_row_mem hnd _ _ _ _ hc3p.compactNeeded) (mkM7Env_row_mem hnd _ _ _ _ hc3p.compact)
    (mkM7Env_row_mem hnd _ _ _ _ hProbe (fun _ _ _ _ h => m6ProbeSpec_monoX h))
  rw [m7FidSchedFixModule, m7FidSchedFixFns, fidSchedFixPatchBefores, patchFns_nil]
  refine spliceModule_moduleOk_sameEnv hm
    (by have hA := m7FidSchedFix_acyclic
        dsimp only [m7FidSchedFixModule, m7FidSchedFixFns, fidSchedFixPatchBefores] at hA
        rw [patchFns_nil] at hA
        dsimp only [m7Module]
        exact hA) ?_ ?_
  · intro r hr
    rw [fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact full_reduce_fid2_wf
    rcases List.mem_cons.mp hr with rfl | hr
    · exact full_eliminate_fid2_wf
    rcases List.mem_cons.mp hr with rfl | hr
    · exact full_probe_tail_fid2_wf
    rcases List.mem_cons.mp hr with rfl | hr
    · exact full_probe_fid2_wf
    rcases List.mem_singleton.mp hr with rfl
    · exact full_preprocess_fid2_wf
  · intro r hr xs m Q X hs
    rw [fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have hsp := mkM7Env_elim_of_mem (m7SpecTable_pfx_mem _ m7OrchPfxRows_specs.reduceM6) hnd hs
      exact hPatch.1.2 xs m Q X hsp
    rcases List.mem_cons.mp hr with rfl | hr
    · have hsp := mkM7Env_elim_of_mem (htBve _ hBveSpecs.eliminateM6) hnd hs
      exact hPatch.2.1.2 xs m Q X hsp
    rcases List.mem_cons.mp hr with rfl | hr
    · have hsp := mkM7Env_elim_of_mem hProbeTail hnd hs
      exact hPatch.2.2.1.2 xs m Q X hsp
    rcases List.mem_cons.mp hr with rfl | hr
    · have hsp := mkM7Env_elim_of_mem hProbe hnd hs
      exact hPatch.2.2.2.1.2 xs m Q X hsp
    rcases List.mem_singleton.mp hr with rfl
    · have hsp := mkM7Env_elim_of_mem (m7SpecTable_pfx_mem _ m7OrchPfxRows_specs.preprocessM6)
        hnd hs
      exact hPatch.2.2.2.2.1.2 xs m Q X hsp

theorem m7FidSchedFix_solveBytes_mem :
    FullM6Orch.m6oSolveBytesFn ∈ m7FidSchedFixModule.fns := by
  rw [m7FidSchedFixModule, m7FidSchedFixFns, fidSchedFixPatchBefores, patchFns_nil]
  refine spliceFns_mem_of_ne m7oSolveBytesFn_mem fun r hr => ?_
  rw [fidSchedFixPatchFns, fidSchedFixFns_eq_patchFns] at hr
  rcases List.mem_cons.mp hr with rfl | hr
  · decide
  rcases List.mem_cons.mp hr with rfl | hr
  · decide
  rcases List.mem_cons.mp hr with rfl | hr
  · decide
  rcases List.mem_cons.mp hr with rfl | hr
  · decide
  rcases List.mem_singleton.mp hr with rfl
  · decide

/-- Top-level `kissat_solve_bytes` soundness for `m7FidSchedFixModule`. -/
theorem m7FidSchedFix_solve_bytes_sound
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hElimBve : (⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :
      SpecEntry) ∈ tBve)
    (hElimDticks : (⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesSpec)
    (hSweepDense : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64],
      FullDefSweep.fullSweepDenseSpec, true⟩ : SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesSpec)
    (hProbeTail : (⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesSpec)
    (hProbe : (⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesSpec)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  spliceModule_solve_bytes_sound
    (m7FidSchedFix_moduleOk tBve fullM6SolveBytesSpec
      (fun _ _ _ _ h => fullM6SolveBytesCoreModelSpec_of_spec h)
      (fun _ _ _ _ _ h => fullM6SolveBytesSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hElimBve hElimDticks hSweepDense hProbeTail hProbe hBveOk)
    m7FidSchedFix_solveBytes_mem
    (fun _ _ _ _ hs =>
      (mkM7Env_solve_bytes_iff tBve fullM6SolveBytesSpec hBveSigs).mpr
        (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Concrete deterministic UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`m7FidSchedFixModule`. -/
theorem m7FidSchedFix_unsat_nv
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hElimBve : (⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :
      SpecEntry) ∈ tBve)
    (hElimDticks : (⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesCoreModelSpec)
    (hSweepDense : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64],
      FullDefSweep.fullSweepDenseSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesCoreModelSpec)
    (hProbeTail : (⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesCoreModelSpec)
    (hProbe : (⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesCoreModelSpec)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tBve fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  spliceModule_unsat_nv
    (m7FidSchedFix_moduleOk tBve fullM6SolveBytesCoreModelSpec
      (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => fullM6SolveBytesCoreModelSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hElimBve hElimDticks hSweepDense hProbeTail hProbe hBveOk)
    m7FidSchedFix_solveBytes_mem
    (fun _ _ _ _ hs =>
      (mkM7Env_solve_bytes_iff tBve fullM6SolveBytesCoreModelSpec hBveSigs).mpr
        (fullM6SolveBytesCoreModelSpec_monoX hs))

end M7SpliceCompat

end LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
