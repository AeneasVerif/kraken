/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVA Proofs — Part 3b (`full_probe_m6_fid_wp`)

M1-clean UNSAT-only parametric `(Γ : Env)` `Func.wp` proof (`public section`, firewall-clean,
`0` axioms, `XPost`-polymorphic) for `full_probe_m6_body` against
canonical `FullM6Orch.m6ProbeSpec` (`GAP-BVA-03`: `700M` initial / `dticks / 20` incremental
tick budget without `8192` truncation).
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7Search
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics


/-! ## 3. `full_probe_m6_fid_wp` (`FullM6Orch.m6ProbeSpec`, `GAP-BVA-03`) -/

section ProbeFid

private theorem fidProbeRetWm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s0 s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hk_ret : k () = .ret (Arg.imm r, ()))
    (hargs : vals args = (c.hdr, 0#64, BitVec.ofNat 64 s.scratch.search_ticks.toNat, ()) ∨
      vals args = (c.hdr, 0#64, s.scratch.search_ticks, ()))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
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
  have hargs' : ∃ v, vals args = (c.hdr, 0#64, v, ()) :=
    hargs.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  obtain ⟨v, hv⟩ := hargs'
  refine m6Hdr_call_m6HdrW2a hv (fun _ _ h => hSetWm _ _ _ _ h) hcfg hext hlen hm
    fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
  rw [hk_ret]; c0_hsteps_nogrp
  exact hQ ext' s' m' hlen' hext' (by rw [hc']; exact hfu) hr hu
    (fun h => let ⟨hi, hcl⟩ := h1 h
      ⟨fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hi hlen' hc' hms') hext',
        by rw [hc']; exact hcl⟩) hm'

private theorem fid_scratch_probe_upd_eq (sc : FullScratch) (lim : BitVec 64) :
    ({ sc with probe_limit := lim } : FullScratch) =
      { sc with probe_limit := lim, probings := sc.probings } := by
  cases sc; rfl

private theorem fid_probe_init_call {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext0 : List (BitVec 64)} {s s0a : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {parg : BitVec 64}
    {J1 : Cont []}
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hScaleM5 : EnvSpec Γ "full_scale_delta_m5" FullFastSched.schedScaleDeltaSpec)
    (hinv0a : FullM6HdrInv c F0 ext0 s0a) (hcl0a : s0a.core.cur_level = 0)
    (hfu0a : s0a.core.fuel = s.core.fuel)
    (hm0af : (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m)
    (hJ1 : ∀ xs m1, (∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
        s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧
        (FullM6HdrMem c ext1 s1 ⋆ R) m1) → J1 xs m1) :
    wp Γ Q X
      (.call "full_log10_q16_m7" (as := [i64]) (bs := [i64]) (Arg.var parg, ()) fun r =>
        .group (sig := [[i64]]) (fun _Js => Blocks.cons (fun p =>
          .let_ (Op.mk (.mul i64) (Arg.imm 100, Arg.var p.fst, ())) fun p2 =>
          .let_ (Op.mk (.mul i64) (Arg.var p2.fst, Arg.var r.fst, ())) fun p3 =>
          .let_ (Op.mk (.sext 32 64) (Arg.imm 16, ())) fun p4 =>
          .let_ (Op.mk (.lshr i64) (Arg.var p3.fst, Arg.var p4.fst, ())) fun p5 =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p6 =>
          .load i64 (Arg.var p6.fst) fun ld1 =>
          .call "full_scale_delta_m5" (as := [i64, i64]) (bs := [i64])
            (Arg.var c.hdr, Arg.var p5.fst, ()) fun psd =>
          .let_ (Op.mk (.add i64) (Arg.var ld1, Arg.var psd.fst, ())) fun p7 =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 976, ())) fun p8 =>
          .store (t := i64) (Arg.var p7.fst) (Arg.var p8.fst) (.jump J1 ())) Blocks.nil)
        fun Js =>
        .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 984, ())) fun p0 =>
        .load i64 (Arg.var p0.fst) fun ld0 =>
        .let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld0, Arg.imm 100000000, ())) fun p1 =>
        .jnz (Arg.var p1.fst) (.jump Js.fst (Arg.imm 100000000, ()))
          (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 984, ())) fun p9 =>
           .load i64 (Arg.var p9.fst) fun ld2 => .jump Js.fst (Arg.var ld2, ()))) m := by
  c0_call hLog10
  refine m7Log10Q16Spec_of fun qlog _ _ => ?_
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) mb =>
      (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mb)
    (fun _ ⟨pc, ⟨⟩⟩ mb hmb => by
      c0_hsteps_nogrp; c0_call hScaleM5
      refine ⟨c, s0a, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hinv0a.sparse.lengths, hmb,
        fun sd => ?_⟩
      c0_hsteps_nogrp
      have hst1 := fullState_upd_probe_step hinv0a.sparse.lengths (s0a.scratch.conflicts + sd)
        s0a.scratch.probings
      have hinv1 := fullM6HdrInv_of_probeStep hinv0a hst1
      have hm_lim : (FullMem c { s0a with scratch := { s0a.scratch with
          probe_limit := s0a.scratch.conflicts + sd } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m := by assumption
      rw [fid_scratch_probe_upd_eq] at hm_lim
      exact hJ1 () m ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0a,
        by rw [hst1.2.1, hfu0a], fullM6HdrMem_unfocus hm_lim⟩)
    (fun _ hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption))

end ProbeFid

/-- Parametric `Func.wp` proof for `full_probe_m6_body` against canonical `FullM6Orch.m6ProbeSpec`
(`GAP-BVA-03`: upstream `700M` / `dticks / 20` factor tick budget, `factordelay = 4`, no `8192`
cap). -/
theorem full_probe_m6_fid_wp (Γ : Env)
    (hProbeDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hScaleM5 : EnvSpec Γ "full_scale_delta_m5" FullFastSched.schedScaleDeltaSpec)
    (hViv : EnvSpec Γ "full_vivify_m6_hdr" m6aVivifySpec)
    (hEnter : EnvSpec Γ "full_enter_dense" FullFastSched.schedEnterDenseSpec)
    (hDelay : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCong : EnvSpec Γ "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
    (hReb : EnvSpec Γ "full_rebuild_watches" Full.fullRebuildWatchesSpec)
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRedD : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBumpD : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSweepD : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSubst : EnvSpec Γ "full_substitute" Full.fullSubstituteSpec)
    (hTail : EnvSpec Γ "full_probe_tail_m6" m6ProbeTailSpec)
    (hBone : EnvSpec Γ "full_backbone_m6" FullM3Backbone.fullBackboneSpec)
    (hFactor : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec) :
    ∀ a m Q X, m6ProbeSpec a m Q X → Func.wp Γ full_probe_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_m6_body
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hProbeDt _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths hm
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := by rw [hc0]; exact hcl0
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  c0_hsteps_nogrp
  let s0a : FullState :=
    { s0 with scratch := { s0.scratch with probings := s0.scratch.probings + 1#64 } }
  have hst0a := fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
    (s0.scratch.probings + 1#64)
  have hinv0a := fullM6HdrInv_of_probeStep hinv0 hst0a
  have hcl0a : s0a.core.cur_level = 0 := by rw [hst0a.2.1]; exact hcl0'
  have hm0a : (FullM6HdrMem c ext0 s0a ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
        (fun (max_r, ()) mM => mM = m1 ∧ max_r.toNat ≤ 2) ?_
        (fun _ hJM => by c0_hsteps <;> exact hJM (_, ()) m1 ⟨rfl, by decide⟩)
    rintro _ ⟨max_r, ⟨⟩⟩ mM ⟨hmM_eq, hmax_le⟩
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
            · rintro _ ⟨fe4, ⟨⟩⟩ ma hma
              have hmTfa : (FullMem c sT ⋆ (m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R)) ma :=
                hma ▸ hmTex
              refine wp_join_group (ts := []) (fun _ mRet => ∃ extRet sRet,
                  FullM6HdrInv c F0 extRet sRet ∧ sRet.core.cur_level = 0 ∧
                  sRet.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullM6HdrMem c extRet sRet ⋆ R) mRet)
                ?_ ?_
              · rintro _ _ mRet ⟨extRet, sRet, hinvRet, hclRet, hfuRet, hmRet⟩
                refine wp_m6Hdr_focus_frame hmRet fun hmRetf => ?_
                c0_hsteps_nogrp
                exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvRet.cfgOk hinvRet.extOk
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
                  · exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvInc.cfgOk hinvInc.extOk
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
                        (fun _ ⟨fbud, ⟨⟩⟩ mB hmB => by
                          subst hmB
                          c0_hsteps_nogrp
                          c0_call hFactor
                          refine ⟨c, F0, sF, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hdenF',
                            hmF, fun _ sFc mFc hdenFc _ hfuFc _ hmFc => ?_⟩
                          c0_hsteps_nogrp; c0_call hReb
                          refine ⟨c, F0, sFc, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hdenFc,
                            hmFc, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                          have hinvR := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk hspR
                          have hmR' := fullM6HdrMem_unfocus hmR
                          have hfuR' : sR.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            rw [hfuFc] at hfuR; exact Nat.le_trans hfuR (Nat.le_trans hfuF hfuT)
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                            c0_hsteps_nogrp
                            exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                              hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                          · exact hJret () mR ⟨extT, sR, hinvR, hclR, hfuR', hmR'⟩)
                        (fun _ hJ0 => by c0_hsteps_nogrp <;> exact hJ0 (_, ()) mF rfl)
                    · have hinvF := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk (hspF ‹_›)
                      exact hJinc () mF ⟨extT, sF, hinvF, hclF, Nat.le_trans hfuF hfuT, hmF'⟩
                  · exact hJinc () ma ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTfa⟩
                  · exact hJinc () ma ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTfa⟩
            · intro Je hJe; c0_hsteps_nogrp <;> exact hJe (_, ()) mEx rfl
          · intro Jex hJex; c0_hsteps_nogrp
            · have hfr_lt : fr.toNat < 19 := BitVec.lt_def.mp ‹_›
              have hfr1 : (fr + 1#64).toNat = fr.toNat + 1 := by c0_bound
              exact hJL (fr + 1#64, _, ()) mL (by dsimp only; omega) ⟨hmL, by omega⟩
            all_goals exact hJex () mL rfl
      · intro JT hJT; c0_hsteps_nogrp
        · refine wp_m6Hdr_focus_frame hmW fun hmWf => ?_
          c0_hsteps_nogrp
          · c0_call hBone
            refine ⟨c, F0, sW, m6ExtMem (m6ExtAddr c.hdr) extW ⋆ R, rfl, hinvW.sparse, hmWf,
              fun rB sB mB hspB hclB _ hfuB _ huB hmB => ?_⟩
            have hinvB := FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk hspB
            have hmB' := fullM6HdrMem_unfocus hmB
            c0_hsteps_nogrp
            · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
              c0_hsteps_nogrp
              exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
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
            exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvW.cfgOk heT hlT
              (Nat.le_trans hfuT hfuW) (Or.inr rfl) (fun _ => huT ‹_›)
              (fun h => by cases h) (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
          · exact hJT () mT ⟨extT, sT, (h1T (hdT.resolve_right ‹_›)).1,
              (h1T (hdT.resolve_right ‹_›)).2, Nat.le_trans hfuT hfuW, hmT⟩
    · intro JW hJW
      clear hm s0a hst0a hinv0a hcl0a hm0a s0 hc0 hlen0 hms0 hext0 hinv0 hcl0'
      c0_hsteps_nogrp
      refine wp_loop_inv (fun (round, ()) mL => round.toNat ≤ max_r.toNat ∧
          ∃ extL sL, FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
            sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL)
        (fun (round, ()) _ => max_r.toNat - round.toNat)
        (fun JL hJL => by
          c0_hsteps_nogrp
          exact hJL (0#64, ()) mM ⟨Nat.zero_le _, ext1, s1, hinv1, hcl1,
            by rw [hfu1]; exact Nat.le_refl _, hmM_eq ▸ hm1⟩)
        (fun JL (round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ hJL => ?_)
      · c0_hsteps_nogrp
        · have hnd_lt : round.toNat < max_r.toNat := BitVec.lt_def.mp ‹_›
          have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
          refine wp_join_group (ts := []) (fun _ mV => ∃ extV sV, FullM6HdrInv c F0 extV sV ∧
              sV.core.cur_level = 0 ∧ sV.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extV sV ⋆ R) mV) ?_ ?_
          · rintro _ _ mV ⟨extV, sV, hinvV, hclV, hfuV, hmV⟩
            let before_unass := sV.core.unassigned
            refine wp_m6Hdr_focus_frame hmV fun hmVf => ?_
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mD => ∃ extD sD, FullM6HdrInv c F0 extD sD ∧
                sD.core.cur_level = 0 ∧ sD.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c extD sD ⋆ R) mD) ?_ ?_
            · rintro _ _ mD ⟨extD, sD, hinvD, hclD, hfuD, hmD⟩
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ mS => ∃ extS sS,
                  FullM6HdrInv c F0 extS sS ∧ sS.core.cur_level = 0 ∧
                  sS.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extS sS ⋆ R) mS) ?_ ?_
              · rintro _ _ mS ⟨extS, sS, hinvS, hclS, hfuS, hmS⟩
                refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
                c0_hsteps_nogrp
                · exact hJW (round, ()) mS ⟨extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
                · exact hJL (round + 1#64, ()) mS (by dsimp only; omega)
                    ⟨by omega, extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
              · intro JS hJS; refine wp_m6Hdr_focus_frame hmD fun hmDf => ?_
                c0_hsteps_nogrp
                · c0_call hSubst
                  refine ⟨c, F0, sD, m6ExtMem (m6ExtAddr c.hdr) extD ⋆ R, rfl, hinvD.sparse, hmDf,
                    fun rS sS mS hspS hclS hfuS _ huS hmS => ?_⟩
                  have hinvS := FullM6HdrInv.mk_inv hinvD.cfgOk hinvD.extOk hspS
                  have hmS' := fullM6HdrMem_unfocus hmS
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                    c0_hsteps_nogrp
                    exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvS.cfgOk hinvS.extOk
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
                refine wp_join_group (ts := [i64]) (fun (dense_ok, ()) mC =>
                    ∃ extC sC, M6HdrExtOk extC ∧
                      (dense_ok ≠ 0#64 → FullDenseInv c F0 sC) ∧
                      (dense_ok = 0#64 → FullM6HdrInv c F0 extC sC ∧ sC.core.cur_level = 0) ∧
                      sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
                · rintro _ ⟨dense_ok, ⟨⟩⟩ mC ⟨extC, sC, hextC, hCden, hCsp, hfuC, hmC⟩
                  refine wp_join_group (ts := []) (fun _ mD1 => ∃ extD1 sD1,
                      FullM6HdrInv c F0 extD1 sD1 ∧ sD1.core.cur_level = 0 ∧
                      sD1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c extD1 sD1 ⋆ R) mD1)
                    (fun _ _ mD1 hD1 => hJD () mD1 hD1) ?_
                  intro JD1 hJD1
                  c0_hsteps_nogrp
                  · have hdenC := hCden ‹_›
                    refine wp_join_group (ts := []) (fun _ mW2 => ∃ extW2 sW2,
                        M6HdrExtOk extW2 ∧ FullDenseInv c F0 sW2 ∧
                        sW2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extW2 sW2 ⋆ R) mW2) ?_ ?_
                    · rintro _ _ mW2 ⟨extW2, sW2, hextW2, hdenW2, hfuW2, hmW2⟩
                      refine wp_m6Hdr_focus_frame hmW2 fun hmW2f => ?_
                      c0_hsteps_nogrp; c0_call hReb
                      refine ⟨c, F0, sW2, m6ExtMem (m6ExtAddr c.hdr) extW2 ⋆ R, rfl, hdenW2, hmW2f,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextW2 hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      have hfuR' := Nat.le_trans hfuR hfuW2
                      c0_hsteps_nogrp
                      · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                          hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                          (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                      · exact hJD1 () mR ⟨extW2, sR, hinvR, hclR, hfuR', hmR'⟩
                    · intro JW2 hJW2
                      refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                        hinvV.cfgOk hextC hdenC.lengths hmC
                        fun ⟨del2, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                      have hdenCd := fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres
                      have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hcCd]; exact hfuC
                      c0_hsteps_nogrp
                      · exact hJW2 () mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩
                      · refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                        c0_hsteps_nogrp; c0_call hSweepD
                        refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenCd,
                          hmCdf, fun rS sS mS hdenS _ hfuS _ huS hmS => ?_⟩
                        have hfuS' := Nat.le_trans hfuS hfuCd
                        c0_hsteps_nogrp
                        · c0_call hReb
                          refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenS, hmS,
                            fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                          have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextCd hspR
                          have hmR' := fullM6HdrMem_unfocus hmR
                          refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                          c0_hsteps_nogrp
                          exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                            hinvR.sparse.lengths (Nat.le_trans hfuR hfuS') (Or.inr rfl)
                            (fun _ => huS ‹_›) (fun h => by cases h)
                            (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                        · have hmS' := fullM6HdrMem_unfocus hmS
                          refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                              M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                              sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                            (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ =>
                              hJW2 () mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩) ?_
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
                          · exact hJSdb () mS ⟨extCd, sS, hextCd, hdenS, hfuS',
                              fullM6HdrMem_unfocus hmSf⟩
                          · exact hJSdb () mS ⟨extCd, sS, hextCd, hdenS, hfuS',
                              fullM6HdrMem_unfocus hmSf⟩
                  · obtain ⟨hinvC, hclC⟩ := hCsp ‹_›
                    exact hJD1 () mC ⟨extC, sC, hinvC, hclC, hfuC, hmC⟩
                · intro JC hJC
                  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                    hinvV.cfgOk hinvV.extOk hdenE'.lengths hmE'
                    fun ⟨del1, ⟨⟩⟩ extEd sEd mEd hcEd hlEd hmsEd hextEd _ hmEd => ?_
                  have hdenEd := fullDenseInv_of_core_eq hdenE' hlEd hcEd hmsEd.extPres
                  have hfuEd : sEd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                    rw [hcEd]; exact Nat.le_trans hfuE hfuV
                  c0_hsteps_nogrp
                  · exact hJC (1#64, ()) mEd ⟨extEd, sEd, hextEd, (fun _ => hdenEd),
                      (fun h => by cases h), hfuEd, hmEd⟩
                  · refine wp_m6Hdr_focus_frame hmEd fun hmEdf => ?_
                    c0_hsteps_nogrp; c0_call hCong
                    refine ⟨c, F0, sEd, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenEd, hmEdf,
                      fun rC sC mC hdenC _ hfuC _ huC hmC => ?_⟩
                    have hfuC' : sC.core.fuel.toNat ≤ s.core.fuel.toNat := by
                      rw [hfuC]; exact hfuEd
                    c0_hsteps_nogrp
                    · c0_call hReb
                      refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenC, hmC,
                        fun rR sR mR hspR hclR hfuR _ _ hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextEd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                        (fun _ => huC ‹_›) (fun h => by cases h)
                        (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                    · have hmC' := fullM6HdrMem_unfocus hmC
                      refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                          M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                          sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extCd sCd ⋆ R) mCd) ?_ ?_
                      · rintro _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩
                        refine wp_join_group (ts := [i64]) (fun (dense_ok, ()) mC =>
                            ∃ extC sC, M6HdrExtOk extC ∧
                              (dense_ok ≠ 0#64 → FullDenseInv c F0 sC) ∧
                              (dense_ok = 0#64 →
                                FullM6HdrInv c F0 extC sC ∧ sC.core.cur_level = 0) ∧
                              sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extC sC ⋆ R) mC)
                          (fun _ ⟨dense_ok, ⟨⟩⟩ mC hC => hJC (dense_ok, ()) mC hC) ?_
                        intro JC' hJC'
                        refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                        c0_hsteps_nogrp
                        · c0_call hReb
                          refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenCd,
                            hmCdf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                          have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextCd hspR
                          have hmR' := fullM6HdrMem_unfocus hmR
                          have hfuR' := Nat.le_trans hfuR hfuCd
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                            c0_hsteps_nogrp
                            exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                              hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                          · refine wp_join_group (ts := []) (fun _ mSb => ∃ extSb sSb,
                                FullM6HdrInv c F0 extSb sSb ∧ sSb.core.cur_level = 0 ∧
                                sSb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                (FullM6HdrMem c extSb sSb ⋆ R) mSb) ?_ ?_
                            · rintro _ _ mSb ⟨extSb, sSb, hinvSb, hclSb, hfuSb, hmSb⟩
                              refine wp_join_group (ts := [i64]) (fun (dense_ok, ()) mC =>
                                  ∃ extC sC, M6HdrExtOk extC ∧
                                    (dense_ok ≠ 0#64 → FullDenseInv c F0 sC) ∧
                                    (dense_ok = 0#64 → FullM6HdrInv c F0 extC sC ∧
                                      sC.core.cur_level = 0) ∧
                                    sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                    (FullM6HdrMem c extC sC ⋆ R) mC)
                                (fun _ ⟨dense_ok, ⟨⟩⟩ mC hC => hJC' (dense_ok, ()) mC hC) ?_
                              intro JC'' hJC''
                              refine wp_m6Hdr_focus_frame hmSb fun hmSbf => ?_
                              c0_hsteps_nogrp
                              c0_call hEnter
                              refine ⟨c, F0, sSb, m6ExtMem (m6ExtAddr c.hdr) extSb ⋆ R, rfl,
                                hinvSb.sparse, hmSbf,
                                fun okB sE2 mE2 hclE2 hfuE2 hdenE2 hspE2 hmE2 => ?_⟩
                              have hmE2' := fullM6HdrMem_unfocus hmE2
                              have hfuE2' := Nat.le_trans hfuE2 hfuSb
                              c0_hsteps_nogrp
                              · exact hJC'' (1#64, ()) mE2 ⟨extSb, sE2, hinvSb.extOk,
                                  (fun _ => hdenE2 ‹_›), (fun h => by cases h), hfuE2', hmE2'⟩
                              · have hinvE2 := FullM6HdrInv.mk_inv hinvV.cfgOk hinvSb.extOk
                                  (hspE2 ‹_›)
                                refine wp_m6Hdr_focus_frame hmE2' fun hmE2f => ?_
                                c0_hsteps_nogrp
                                exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvE2.cfgOk
                                  hinvE2.extOk hinvE2.sparse.lengths hfuE2' (Or.inr rfl)
                                  (fun _ => fullM6HdrInv_inconsistent_unsat hinvE2 ‹_›)
                                  (fun h => by cases h) (fullM6HdrMem_unfocus hmE2f) (hQ 20#64)
                              · exact hJC'' (0#64, ()) mE2 ⟨extSb, sE2, hinvSb.extOk,
                                  (fun h => absurd rfl h),
                                  (fun _ => ⟨FullM6HdrInv.mk_inv hinvV.cfgOk hinvSb.extOk
                                    (hspE2 ‹_›), hclE2⟩),
                                  hfuE2', hmE2'⟩
                            · intro JSb hJSb
                              refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                              c0_hsteps_nogrp
                              · c0_call hSubst
                                refine ⟨c, F0, sR, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl,
                                  hinvR.sparse, hmRf, fun rS sS mS hspS hclS hfuS _ huS hmS => ?_⟩
                                have hinvS := FullM6HdrInv.mk_inv hinvV.cfgOk hextCd hspS
                                have hmS' := fullM6HdrMem_unfocus hmS
                                c0_hsteps_nogrp
                                · refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                                  c0_hsteps_nogrp
                                  exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvS.cfgOk
                                    hinvS.extOk hinvS.sparse.lengths (Nat.le_trans hfuS hfuR')
                                    (Or.inr rfl) (fun _ => huS ‹_›) (fun h => by cases h)
                                    (fullM6HdrMem_unfocus hmSf) (hQ 20#64)
                                · exact hJSb () mS ⟨extCd, sS, hinvS, hclS,
                                    Nat.le_trans hfuS hfuR', hmS'⟩
                              · exact hJSb () mR ⟨extCd, sR, hinvR, hclR, hfuR',
                                  fullM6HdrMem_unfocus hmRf⟩
                        · exact hJC' (1#64, ()) mCd ⟨extCd, sCd, hextCd, (fun _ => hdenCd),
                            (fun h => by cases h), hfuCd, fullM6HdrMem_unfocus hmCdf⟩
                      · intro JCd hJCd; c0_hsteps_nogrp
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
                exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hinvE.extOk
                  hinvE.sparse.lengths (Nat.le_trans hfuE hfuV) (Or.inr rfl)
                  (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
              · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hinvV.extOk (hspE ‹_›)
                exact hJD () mE ⟨extV, sE, hinvE, hclE, Nat.le_trans hfuE hfuV, hmE'⟩
          · intro JV hJV; c0_hsteps_nogrp
            · exact hJV () mL ⟨extL, sL, hinvL, hclL, hfuL, hmL⟩
            · c0_call hViv
              refine m6aVivifySpec_of hinvL.cfgOk hinvL.extOk hinvL.sparse hmL
                fun rV extV sV mV ⟨hextV, _⟩ hspV ⟨hclV, _⟩ hfuV hrV huV hmV => ?_
              have hinvV := FullM6HdrInv.mk_inv hinvL.cfgOk hextV hspV
              have hfuV' := Nat.le_trans hfuV hfuL
              c0_hsteps_nogrp
              · refine wp_m6Hdr_focus_frame hmV fun hmVf => ?_
                c0_hsteps_nogrp
                exact fidProbeRetWm rfl (Or.inr rfl) hSetWm hinvV.cfgOk hextV
                  hinvV.sparse.lengths hfuV' (Or.inr rfl) (fun _ => huV ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmVf) (hQ 20#64)
              · exact hJV () mV ⟨extV, sV, hinvV, hclV, hfuV', hmV⟩
        · exact hJW (round, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, hmL⟩
  · intro J1 hJ1; c0_hsteps_nogrp
    · exact hJ1 () _ ⟨ext0, s0a, hinv0a, hcl0a, by rw [hst0a.2.1, hc0], hm0a⟩
    · refine wp_m6Hdr_focus_frame hm0a fun hm0af => ?_
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma =>
          (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) ma)
        (fun _ ⟨parg, ⟨⟩⟩ ma hma =>
          fid_probe_init_call hLog10 hScaleM5 hinv0a hcl0a (by rw [hst0a.2.1, hc0]) hma hJ1)
        (fun _ hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption))

end LeanQbe.T.Examples.Kissat.FullFidelityBva

end
