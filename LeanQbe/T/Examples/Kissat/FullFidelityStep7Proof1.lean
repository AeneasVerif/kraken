/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof1a
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 7 Proofs — Shard 1 (`FullFidelityStep7Proof1`)

Parametric `(Γ : Env)` UNSAT-only `Func.wp` proofs (`public section`, `XPost`-polymorphic,
`std3` axioms only, `0` SAT model proofs) for all `9` Step-7 functions in Shard 1
(re-exporting items `1..7` via `public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof1a`):
8. `fidStep7ProbeM6Fn` (`full_probe_m6`) -> `FullM6Orch.m6ProbeSpec`
9. `fidStep7SearchM6Fn` (`full_search_m6`) -> `FullM6.fullM6SearchSpec`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Proof
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 8. `full_probe_m6_step7_wp` (`FullM6Orch.m6ProbeSpec`) -/

section ProbeStep7

private theorem s7ProbeRetWm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
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

private theorem s7_scratch_probe_upd_eq (sc : FullScratch) (lim : BitVec 64) :
    ({ sc with probe_limit := lim } : FullScratch) =
      { sc with probe_limit := lim, probings := sc.probings } := by
  cases sc; rfl

private theorem s7_probe_init_call {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
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
      rw [s7_scratch_probe_upd_eq] at hm_lim
      exact hJ1 () m ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0a,
        by rw [hst1.2.1, hfu0a], fullM6HdrMem_unfocus hm_lim⟩)
    (fun _ hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption))

end ProbeStep7

/-- Parametric `Func.wp` proof for `fidStep7ProbeM6Fn` (`full_probe_m6`, `saved_st`,
watermark `1ULL` factor call counter, restoring `search_ticks`) against `FullM6Orch.m6ProbeSpec`. -/
theorem full_probe_m6_step7_wp (Γ : Env)
    (hProbeDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hScaleM5 : EnvSpec Γ "full_scale_delta_m5" FullFastSched.schedScaleDeltaSpec)
    (hViv : EnvSpec Γ "full_vivify_m6_hdr" m6aVivifySpec)
    (hEnter : EnvSpec Γ "full_enter_dense" FullFastSched.schedEnterDenseSpec)
    (hDelay : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCong : EnvSpec Γ "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
    (hReb : EnvSpec Γ "full_rebuild_watches" Full.fullRebuildWatchesSpec)
    (hGetWm : EnvSpec Γ "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64]))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRedD : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBumpD : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSweepD : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSubst : EnvSpec Γ "full_substitute" Full.fullSubstituteSpec)
    (hTail : EnvSpec Γ "full_probe_tail_m6" m6ProbeTailSpec)
    (hBone : EnvSpec Γ "full_backbone_m6" FullM3Backbone.fullBackboneSpec)
    (hFactor : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec) :
    ∀ a m Q X, m6ProbeSpec a m Q X → Func.wp Γ fidStep7ProbeM6Fn.body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp fidStep7ProbeM6Fn full_probe_m6_body; dsimp only
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hProbeDt _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths (fullM6HdrMem_unfocus hmf)
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
        (fun _ hJM => by c0_hsteps <;> exact hJM (_, ()) m1 ⟨rfl, by bv_omega⟩)
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
            exact hJL (1#64, 10#64, ()) mT ⟨rfl, by bv_omega⟩)
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
                let sRet' : FullState :=
                  { sRet with scratch :=
                    { sRet.scratch with search_ticks := s.scratch.search_ticks } }
                have hspRet' : FullSparseInv c F0 sRet' :=
                  FullM3CongBva.fullSparseInv_with_scratch_keep hinvRet.sparse
                    { hinvRet.sparse.lengths.scratch_ok with
                      walk_vals_len := hinvRet.sparse.lengths.scratch_ok.walk_vals_len } rfl rfl
                have hinvRet' := FullM6HdrInv.mk_inv hinvRet.cfgOk hinvRet.extOk hspRet'
                exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvRet'.cfgOk hinvRet'.extOk
                  hinvRet'.sparse.lengths hfuRet (Or.inl rfl) (fun h => by cases h)
                  (fun _ => ⟨hinvRet', hclRet⟩) (fullM6HdrMem_unfocus (by assumption)) (hQ 1#64)
              · intro Jret hJret; c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mInc => ∃ extInc sInc,
                    FullM6HdrInv c F0 extInc sInc ∧ sInc.core.cur_level = 0 ∧
                    sInc.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extInc sInc ⋆ R) mInc) ?_ ?_
                · rintro _ _ mInc ⟨extInc, sInc, hinvInc, hclInc, hfuInc, hmInc⟩
                  refine wp_m6Hdr_focus_frame hmInc fun hmIncf => ?_
                  c0_hsteps_nogrp
                  · exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvInc.cfgOk hinvInc.extOk
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
                      refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hGetWm _ _ _ _ h)
                        hinvT.cfgOk hinvT.extOk hdenF'.lengths hmF'
                        fun ⟨_wm1, ⟨⟩⟩ extF1 sF1 mF1 hcF1 hlF1 hmsF1 hextF1 _ hmF1 => ?_
                      have hdenF1 := fullDenseInv_of_core_eq hdenF' hlF1 hcF1 hmsF1.extPres
                      c0_hsteps_nogrp
                      refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h)
                        hinvT.cfgOk hextF1 hdenF1.lengths hmF1
                        fun _ extF2 sF2 mF2 hcF2 hlF2 hmsF2 hextF2 _ hmF2 => ?_
                      have hdenF2 := fullDenseInv_of_core_eq hdenF1 hlF2 hcF2 hmsF2.extPres
                      have hmF2f := fullM6HdrMem_focus hmF2
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i64]) (fun _ mB => mB = mF2)
                        (fun _ ⟨fbud, ⟨⟩⟩ mB hmB => by
                          subst hmB
                          c0_hsteps_nogrp
                          c0_call hFactor
                          refine ⟨c, F0, sF2, m6ExtMem (m6ExtAddr c.hdr) extF2 ⋆ R, rfl, hdenF2,
                            hmF2f, fun _ sFc mFc hdenFc _ hfuFc _ hmFc => ?_⟩
                          c0_hsteps_nogrp; c0_call hReb
                          refine ⟨c, F0, sFc, m6ExtMem (m6ExtAddr c.hdr) extF2 ⋆ R, rfl, hdenFc,
                            hmFc, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                          have hinvR := FullM6HdrInv.mk_inv hinvT.cfgOk hextF2 hspR
                          have hmR' := fullM6HdrMem_unfocus hmR
                          have hfuR' : sR.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            rw [hfuFc, hcF2, hcF1] at hfuR
                            exact Nat.le_trans hfuR (Nat.le_trans hfuF hfuT)
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                            c0_hsteps_nogrp
                            exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                              hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                          · exact hJret () mR ⟨extF2, sR, hinvR, hclR, hfuR', hmR'⟩)
                        (fun _ hJ0 => by c0_hsteps_nogrp <;> exact hJ0 (_, ()) mF2 rfl)
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
              exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
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
            exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvW.cfgOk heT hlT
              (Nat.le_trans hfuT hfuW) (Or.inr rfl) (fun _ => huT ‹_›)
              (fun h => by cases h) (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
          · exact hJT () mT ⟨extT, sT, (h1T (hdT.resolve_right ‹_›)).1,
              (h1T (hdT.resolve_right ‹_›)).2, Nat.le_trans hfuT hfuW, hmT⟩
    · intro JW hJW
      clear hm hmf s0a hst0a hinv0a hcl0a hm0a s0 hc0 hlen0 hms0 hext0 hinv0 hcl0'
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
                    exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvS.cfgOk hinvS.extOk
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
                        exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
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
                          exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
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
                      exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
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
                            exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
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
                                exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvE2.cfgOk
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
                                  exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvS.cfgOk
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
                exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hinvE.extOk
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
                exact s7ProbeRetWm rfl (Or.inr rfl) hSetWm hinvV.cfgOk hextV
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
          s7_probe_init_call hLog10 hScaleM5 hinv0a hcl0a (by rw [hst0a.2.1, hc0]) hma hJ1)
        (fun _ hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption))

/-! ## 9. `full_search_m6_step7_wp` (`FullM6.fullM6SearchSpec`) -/

section SearchStep7

private def s7SearchVariant (c : FullCfg) (s : FullState) : Nat :=
  (c.max_vars + 1) * s.core.fuel.toNat + (c.max_vars - s.core.trail_end)

private theorem s7_searchVariant_dec {c c' : FullCfg} {s s1 s' : FullState}
    (hmveq : c'.max_vars = c.max_vars) (hfu_pos : 0 < s.core.fuel.toNat)
    (hfu1 : s1.core.fuel.toNat < s.core.fuel.toNat)
    (hfu_le : s'.core.fuel.toNat ≤ s1.core.fuel.toNat)
    (hle_te' : s'.core.trail_end ≤ c'.max_vars) :
    s7SearchVariant c' s' < s7SearchVariant c s := by
  unfold s7SearchVariant; rw [hmveq]
  have h1 : s'.core.fuel.toNat ≤ s.core.fuel.toNat - 1 := by omega
  have hmul : (c.max_vars + 1) * s'.core.fuel.toNat ≤
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) :=
    Nat.mul_le_mul_left (c.max_vars + 1) h1
  have hs_mul : (c.max_vars + 1) * s.core.fuel.toNat =
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := by
    have hsub : s.core.fuel.toNat - 1 + 1 = s.core.fuel.toNat := by omega
    calc (c.max_vars + 1) * s.core.fuel.toNat
        = (c.max_vars + 1) * (s.core.fuel.toNat - 1 + 1) := by rw [hsub]
      _ = (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := Nat.mul_succ _ _
  omega

private theorem s7_searchVariant_dec_fuel {c c' : FullCfg} {s s1 s' : FullState}
    (hmveq : c'.max_vars = c.max_vars) (hfu_pos : 0 < s.core.fuel.toNat)
    (hfu1_pos : 0 < s1.core.fuel.toNat) (hfu1_le : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hfu_le : s'.core.fuel.toNat ≤ s1.core.fuel.toNat - 1)
    (hle_te' : s'.core.trail_end ≤ c'.max_vars) :
    s7SearchVariant c' s' < s7SearchVariant c s := by
  unfold s7SearchVariant; rw [hmveq]
  have h1 : s'.core.fuel.toNat ≤ s.core.fuel.toNat - 1 := by omega
  have hmul : (c.max_vars + 1) * s'.core.fuel.toNat ≤
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) :=
    Nat.mul_le_mul_left (c.max_vars + 1) h1
  have hs_mul : (c.max_vars + 1) * s.core.fuel.toNat =
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := by
    have hsub : s.core.fuel.toNat - 1 + 1 = s.core.fuel.toNat := by omega
    calc (c.max_vars + 1) * s.core.fuel.toNat
        = (c.max_vars + 1) * (s.core.fuel.toNat - 1 + 1) := by rw [hsub]
      _ = (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := Nat.mul_succ _ _
  omega

private theorem s7_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_propagate" fullBcpS15Spec)
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → FullTrailExt s.core s'.core →
      FullArenaPermEq s.core s'.core → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom _ hr1 _ _ hm'
  have hnd' : Full.FullArenaVarsNodup s' := by
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
  exact hk r s' m' hinv' htr' hperm' hfu' hdom hr1 ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem s7_call_analyze {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hcok : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_analyze_m6_hdr" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (m6HdrAnalyzeSpec_of hinv hcok hm
    fun r ext' s' m' hext' hlen' hr _ hfu _ hu _ h1 hm' =>
      hk r ext' s' m' hext' hlen' hr hfu hu h1 hm')

private theorem s7_call_reduce {Γ : Env} {force : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, force, ()))
    (hΓ : EnvSpec Γ "full_reduce_m6" m6ReduceSpec)
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reduce_m6" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (m6ReduceSpec_of hinv hm fun r ext' s' m' hinv' hr _ hfu _ _ _ _ hu _ _ hm' =>
    hk r ext' s' m' hinv' hr hfu hu hm')

private theorem s7_call_switchMode {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_switch_mode_m7" m7SwitchModeSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core = s.core →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_switch_mode_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hΓ _ _ _ X (m7SwitchModeSpec_of hinv.sparse.lengths ((fullM6HdrMem_iff ..).mp hm)
    fun s' m' hc' hl' hp' _ _ _ hm' => ?_)
  exact hk s' m' (fullM6HdrInv_of_core_eq hinv hl' hc' hp'.1) hc'
    ((fullM6HdrMem_iff ..).mpr hm')

private theorem s7_call_restartDue {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_restart_due" Full.fullRestartDueSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core = s.core →
      (r = 0#64 ∨ r = 1#64) → (FullM6HdrMem c ext s' ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_restart_due" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hΓ _ _ _ X ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse.lengths,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hlen ⟨hdom, hpres⟩ hm'
  have hceq : s'.core = s.core := @Full.fullCoreState_agrees_with_scratch c s s' hcore
  exact hk r s' m' (fullM6HdrInv_of_core_eq hinv hlen hceq hpres) hceq hdom
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem s7_call_restart {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_restart" Full.fullRestartSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel = s.core.fuel → (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_restart" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hinv.sparse; have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ _ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hcore.coreInv,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hc' hcl' hpres' hm'
  have hinv' := FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk ⟨hc', ⟨hsp.2.1.1, hsp.2.1.2⟩,
    hsp.2.2.1, ⟨hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr,
      by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩,
    hsp.2.2.2.2⟩
  exact hk s' m' hinv' hcl' rfl ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem s7_call_reorder {Γ : Env} {budget : BitVec 64} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, budget, ()))
    (hΓ : EnvSpec Γ "full_reorder_m6" m4ReorderSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel = s.core.fuel →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reorder_m6" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hΓ _ _ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r s' m' hsp' _ _ hfu' hm'
  exact hk r s' m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu'
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem s7_call_rephase {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_rephase" m7RephaseSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_rephase" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hΓ _ _ _ X (m7RephaseSpec_of hinv.sparse ((fullM6HdrMem_iff c ext s R m).mp hm) ?_)
  intro vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m' hsp' _ _ _ hfu' _ _ hm'
  exact hk _ m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu'
    ((fullM6HdrMem_iff c ext _ R m').mpr hm')

private theorem s7_call_simplify {Γ : Env} {dp de : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, dp, de, ()))
    (hΓ : EnvSpec Γ "full_simplify_m6" fullM6SimplifySpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (c' : FullCfg) (ext' : List (BitVec 64)) (s' : FullState)
      (m' : Mem 64),
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_simplify_m6" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (fullM6SimplifySpec_of hinv hm hk)

private theorem s7_call_decideFid {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "m6_hdr_decide_fid" m6HdrDecideSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → (r = 0#64 ∨ r = 1#64) →
      s'.core.fuel = s.core.fuel →
      (r = 0#64 → s'.core.cur_level = s.core.cur_level ∧ s'.core.trail_end = s.core.trail_end) →
      (r = 1#64 → s'.core.cur_level = s.core.cur_level + 1 ∧
        s'.core.trail_end = s.core.trail_end + 1) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "m6_hdr_decide_fid" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hinv.sparse; have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ _ _ X (m6HdrDecideSpec_of hcore hm ?_)
  intro r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext' m' s'
    hcore' hpres' hdom h0 h1 hm'
  have hinv' := FullM6HdrInv.mk_inv hcore'.cfgOk hcore'.extOk ⟨hcore'.coreInv,
    ⟨hsp.2.1.1, hsp.2.1.2⟩, hsp.2.2.1,
    ⟨hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr,
      by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩,
    hsp.2.2.2.2⟩
  exact hk r ext' s' m' hinv' hdom rfl h0 (fun hr1 => ⟨(h1 hr1).1, (h1 hr1).2.1⟩) hm'

private theorem s7_upd_fuel_m6Inv {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (hinv : FullM6HdrInv c F0 ext s) (f' : BitVec 64)
    {F_cur : List (List Nat)} (hw : FullWitnessInv c F0 F_cur s.core) :
    let s' : FullState := { s with core := { s.core with fuel := f' } }
    FullM6HdrInv c F0 ext s' :=
  FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk ⟨⟨⟨{ hinv.sparse.lengths.core_ok with
    vals_len := hinv.sparse.lengths.core_ok.vals_len }, hinv.sparse.lengths.scratch_ok⟩,
    ⟨F_cur, { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }⟩⟩,
    hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1, hinv.sparse.2.2.2.2⟩

private theorem s7_upd_fuel_m6InvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (f' : BitVec 64) :
    FullM6HdrInvW c F0 F_cur ext { s with core := { s.core with fuel := f' } } :=
  FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk ⟨⟨{ hinv.sparseW.1.core_ok with
    vals_len := hinv.sparseW.1.core_ok.vals_len }, hinv.sparseW.1.scratch_ok⟩,
    { hinv.sparseW.2.1 with
      arena := { hinv.sparseW.2.1.arena with len_ok := hinv.sparseW.2.1.arena.len_ok }
      watches := hinv.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    hinv.sparseW.2.2.1, hinv.sparseW.2.2.2.1, hinv.sparseW.2.2.2.2.1,
    hinv.sparseW.2.2.2.2.2⟩

private theorem s7_search_simplify_cont {Γ : Env} {c0 c : FullCfg} {F0 : CNF Nat}
    {s s1 s2 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {sr : BitVec 64} {c3 : FullCfg} {ext3 : List (BitVec 64)} {s3 : FullState} {m3 : Mem 64}
    {cont : Expr Val Cont [i64]}
    (hcompat : FullCfgCompat c0 c) (hcomp3 : FullCfgCompat c c3)
    (hlen3 : s3.LengthsOk c3) (hcfg3 : FullM6HdrCfgOk c3) (hext3 : M6HdrExtOk ext3)
    (hcore2 : s2.core = s1.core)
    (hfu_pos : 0 < s.core.fuel.toNat) (hfu1_pos : 0 < s1.core.fuel.toNat)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hfu1_pred : (s1.core.fuel - 1#64).toNat = s1.core.fuel.toNat - 1)
    (hfu3 : s3.core.fuel.toNat ≤ (s2.core.fuel - 1#64).toNat)
    (hu3 : sr = 20#64 → F0.Unsat)
    (hs1 : sr = 1#64 → FullM6HdrInv c3 F0 ext3 s3 ∧ s3.core.cur_level = 0)
    (hm3 : (FullM6HdrMem c3 ext3 s3 ⋆ R) m3)
    (hQ : ∀ (r : BitVec 64) (c' : FullCfg) (ext' : List (BitVec 64)) (s' : FullState)
        (m' : Mem 64),
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m')
    (hcont : FullM6HdrInv c3 F0 ext3 s3 → s7SearchVariant c3 s3 < s7SearchVariant c s →
      wp Γ Q X cont m3) :
    wp Γ Q X
      (.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var sr, Arg.imm 20, ())) fun p =>
        .jnz (Arg.var p.fst) (.ret (Arg.imm 20, ()))
          (.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var sr, Arg.imm 1, ())) fun p1 =>
            .jnz (Arg.var p1.fst) (.ret (Arg.imm 0, ())) cont)) m3 := by
  have hcompat3 := hcompat.trans hcomp3
  c0_hsteps_nogrp
  · exact hQ 20#64 c3 ext3 s3 m3 hcompat3 hlen3 hcfg3 hext3
      (Or.inr (Or.inr rfl)) (fun _ => hu3 hc) (fun hc => by cases hc) hm3
  · exact hQ 0#64 c3 ext3 s3 m3 hcompat3 hlen3 hcfg3 hext3
      (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
  · obtain ⟨hinv3, _⟩ := hs1 hc
    rw [hcore2, hfu1_pred] at hfu3
    exact hcont hinv3 (s7_searchVariant_dec_fuel hcomp3.max_vars hfu_pos hfu1_pos hfu1 hfu3
      (Nat.le_trans hinv3.sparse.lengths.core_ok.trail_end_le
        hinv3.sparse.lengths.core_ok.cur_vars_le))

end SearchStep7

/-- Parametric `Func.wp` proof for `fidStep7SearchM6Fn` (`full_search_m6`, resetting
`search_ticks`, `mode_saved_ticks`, `M6_WM_PROBE_TICKS`, and `fwd_str_cnt` after
`full_lucky_late_m7`) against `FullM6.fullM6SearchSpec`. -/
theorem full_search_m6_step7_wp (Γ : Env)
    (hLuckyLate : EnvSpec Γ "full_lucky_late_m7" m7LuckyLateSpec)
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hProp : EnvSpec Γ "full_propagate" fullBcpS15Spec)
    (hAnalyze : EnvSpec Γ "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hReduce : EnvSpec Γ "full_reduce_m6" m6ReduceSpec)
    (hSwitch : EnvSpec Γ "full_switch_mode_m7" m7SwitchModeSpec)
    (hRstDue : EnvSpec Γ "full_restart_due" Full.fullRestartDueSpec)
    (hRst : EnvSpec Γ "full_restart" Full.fullRestartSpec)
    (hReorder : EnvSpec Γ "full_reorder_m6" m4ReorderSpec)
    (hRephase : EnvSpec Γ "full_rephase" m7RephaseSpec)
    (hSimplify : EnvSpec Γ "full_simplify_m6" fullM6SimplifySpec)
    (hDecideFid : EnvSpec Γ "m6_hdr_decide_fid" m6HdrDecideSpec) :
    ∀ a m Q X, fullM6SearchSpec a m Q X → Func.wp Γ fidStep7SearchM6Fn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6SearchSpec_elim hs with ⟨c0, F0, ext0, s0, R, rfl, hinv0, _, hm0, hQ⟩
  unfold Func.wp fidStep7SearchM6Fn full_search_m6_body; dsimp only
  c0_hsteps_nogrp
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  c0_hsteps_nogrp; c0_call hLuckyLate
  refine m7LuckyLateSpec_of hinv0.sparse hm0f
    fun lr sL mL hlenL hdomL _ _ huL hspL h10L hmL => ?_
  have hmL' := fullM6HdrMem_unfocus hmL
  c0_hsteps_nogrp
  · have hl := hc; rw [hl]
    exact hQ 10#64 c0 ext0 sL mL (FullCfgCompat.refl c0) hlenL hinv0.cfgOk hinv0.extOk
      (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => h10L hl) hmL'
  · have hl := hc; rw [hl]
    exact hQ 20#64 c0 ext0 sL mL (FullCfgCompat.refl c0) hlenL hinv0.cfgOk hinv0.extOk
      (Or.inr (Or.inr rfl)) (fun _ => huL hl) (fun h => by cases h) hmL'
  · have hlkr02 : lr = 0#64 ∨ lr = 2#64 := by
      rcases hdomL with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl (by assumption)
      · exact absurd rfl hc
    have hsp_lk := (hspL hlkr02).1
    let sL1 : FullState :=
      { sL with scratch := { sL.scratch with search_ticks := 0#64, mode_saved_ticks := 0#64 } }
    have hspL1 : FullSparseInv c0 F0 sL1 :=
      FullM3CongBva.fullSparseInv_with_scratch_keep hsp_lk
        { hsp_lk.lengths.scratch_ok with
          walk_vals_len := hsp_lk.lengths.scratch_ok.walk_vals_len } rfl rfl
    have hinvL1 := FullM6HdrInv.mk_inv hinv0.cfgOk hinv0.extOk hspL1
    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h)
      hinvL1.cfgOk hinvL1.extOk hinvL1.sparse.lengths (fullM6HdrMem_unfocus (by assumption))
      fun _ extL2 sL2 mL2 hcL2 hlL2 hmsL2 hextL2 _ hmL2 => ?_
    have hinvL2 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinvL1 hlL2 hcL2 hmsL2) hextL2
    refine wp_m6Hdr_focus_frame hmL2 fun hmL2f => ?_
    c0_hsteps_nogrp
    let sL3 : FullState := { sL2 with scratch := { sL2.scratch with fwd_str_cnt := 0#64 } }
    have hspL3 : FullSparseInv c0 F0 sL3 :=
      FullM3CongBva.fullSparseInv_with_scratch_keep hinvL2.sparse
        { hinvL2.sparse.lengths.scratch_ok with
          walk_vals_len := hinvL2.sparse.lengths.scratch_ok.walk_vals_len } rfl rfl
    have hinvL3 := FullM6HdrInv.mk_inv hinvL2.cfgOk hinvL2.extOk hspL3
    have hmL3 : (FullM6HdrMem c0 extL2 sL3 ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
    clear_value sL3
    clear hspL3 hinvL2 hcL2 hlL2 hmsL2 hextL2 hinvL1 hspL1 sL1 hsp_lk
    refine wp_while_state (ts := [i64, i64, i64])
        (α := BitVec 64 × BitVec 64 × BitVec 64 × FullCfg × List (BitVec 64) × FullState)
        (fun ⟨rlim, reord, lrc, _, _, _⟩ => (rlim, reord, lrc, ()))
        (fun ⟨_, _, _, c, _, s⟩ => s7SearchVariant c s)
        (fun ⟨_, _, _, c, ext, s⟩ ml =>
          FullCfgCompat c0 c ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) ml)
        (fun J hJ => by
          c0_hsteps
          exact hJ (10000#64, 0#64, 0xFFFFFFFFFFFFFFFF#64, c0, extL2, sL3) _
            ⟨FullCfgCompat.refl c0, hinvL3, hmL3⟩)
        ?_
    rintro J ⟨rlim, reord, last_red, c, ext, s⟩ ml ⟨hcompat, hinv, hml⟩ ih
    rw [← hcompat.hdr]
    have hsp := hinv.sparse; have hlen := hsp.lengths
    have hmx := c.hmaxv; unfold LratBytes.dimacsBound at hmx
    have hml_f := fullM6HdrMem_focus hml
    c0_hsplit
    rotate_left; · cases hc
    c0_hsteps
    · exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
        (fun hc => by cases hc) (fun hc => by cases hc) hml
    · exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
        (fun hc => by cases hc) (fun hc => by cases hc) hml
    · have hfu_pos : 0 < s.core.fuel.toNat := by
        have hpos : s.core.fuel.toNat ≠ 0 :=
          fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
        omega
      have hm1_pred : (s.core.fuel - 1#64).toNat = s.core.fuel.toNat - 1 := by bv_omega
      obtain ⟨F_cur, hinvW⟩ := fullM6HdrInv_exists_witness hinv
      refine s7_call_bcp rfl hProp hinvW hml ?_
      intro pr s1 m1 hinvW1 htr1 _ hfu1 hdom1 hr1 hm1
      have hinv1 := hinvW1.toInv; have hlen1 := hinv1.sparse.lengths
      have hm1_f := fullM6HdrMem_focus hm1
      c0_hsteps_nogrp
      · exact hQ 0#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inl rfl)
          (fun hc => by cases hc) (fun hc => by cases hc) hm1
      · c0_hstep; c0_hsteps_nogrp
        · obtain ⟨hfu_lt, _, hcok1⟩ := hr1 hc
          refine s7_call_analyze rfl hAnalyze hinvW1 hcok1 hm1 ?_
          intro ast ext2 s2 m2 hext2 hlen2 hast hfu2 hu2 ha1 hm2
          c0_hsteps
          · exact hQ 20#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inr (Or.inr rfl))
              (fun _ => hu2 hc) (fun hc => by cases hc) hm2
          · exact hQ 0#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inl rfl)
              (fun hc => by cases hc) (fun hc => by cases hc) hm2
          · exact ih (rlim, reord, last_red, c, ext2, s2) m2
              (s7_searchVariant_dec rfl hfu_pos hfu_lt hfu2 (Nat.le_trans hlen2.core_ok.trail_end_le
                hlen2.core_ok.cur_vars_le))
              ⟨hcompat, (ha1 hc).1.toInv, hm2⟩
        · exact hQ 10#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inr (Or.inl rfl))
            (fun hc => by cases hc) (fun _ => hinv1.sparse.2.2.2.1.2) hm1
        · exact hQ 0#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inl rfl)
            (fun hc => by cases hc) (fun hc => by cases hc) hm1
        · have hfu1_pos : 0 < s1.core.fuel.toNat :=
            Nat.pos_of_ne_zero fun h0 => ‹s1.core.fuel ≠ 0#64›
              (BitVec.eq_of_toNat_eq (by simpa using h0))
          have hfu1_pred : (s1.core.fuel - 1#64).toNat = s1.core.fuel.toNat - 1 := by c0_bound
          have hmu_rare : ∀ {c' : FullCfg} {ext' : List (BitVec 64)} {s' : FullState},
              c'.max_vars = c.max_vars → s'.core.fuel.toNat ≤ s1.core.fuel.toNat - 1 →
              FullM6HdrInv c' F0 ext' s' → s7SearchVariant c' s' < s7SearchVariant c s :=
            fun hmveq hfule hinv' =>
              s7_searchVariant_dec_fuel hmveq hfu_pos hfu1_pos hfu1 hfule
                (Nat.le_trans hinv'.sparse.lengths.core_ok.trail_end_le
                  hinv'.sparse.lengths.core_ok.cur_vars_le)
          c0_hstep; c0_hsteps_nogrp
          · have hinvW1r := s7_upd_fuel_m6InvW hinvW1 (s1.core.fuel - 1#64)
            refine s7_call_reduce rfl hReduce hinvW1r (fullM6HdrMem_unfocus (by assumption)) ?_
            intro rr ext3 s3 m3 hinvW3 _ hfu3 hu3 hm3
            dsimp only at hfu3
            have hinv3 := hinvW3.toInv; have hlen3 := hinv3.sparse.lengths
            c0_hsteps!
            · exact hQ 20#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                (Or.inr (Or.inr rfl)) (fun _ => hu3 hc) (fun hc => by cases hc) hm3
            · exact hQ 0#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
            · exact ih (rlim, reord, s1.scratch.conflicts, c, ext3, s3) m3
                (hmu_rare rfl (by rw [hfu1_pred] at hfu3; exact hfu3) hinv3)
                ⟨hcompat, hinv3, hm3⟩
          · c0_hstep; c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
              (fun x => (x, ())) (fun _ => True) ?_
              (fun _ hJmd => by c0_hsteps <;> exact hJmd _ trivial)
            intro _ _ _
            c0_hsplit
            · c0_hsteps
              have hinv1m := s7_upd_fuel_m6Inv hinv1 (s1.core.fuel - 1#64) hinvW1.sparseW.2.1
              refine s7_call_switchMode rfl hSwitch hinv1m (fullM6HdrMem_unfocus (by assumption))
                ?_
              intro s2 m2 hinv2 hcore2 hm2
              dsimp only at hcore2
              c0_hsteps!
              exact ih (rlim, reord, last_red, c, ext, s2) m2
                (hmu_rare rfl (by rw [hcore2, hfu1_pred]; exact le_refl _) hinv2)
                ⟨hcompat, hinv2, hm2⟩
            · c0_hstep; c0_hsteps_nogrp
              refine s7_call_restartDue rfl hRstDue hinv1 (fullM6HdrMem_unfocus (by assumption)) ?_
              intro rdu s2 m2 hinv2 hcore2 _ hm2
              have hm2_f := fullM6HdrMem_focus hm2
              c0_hsplit
              · c0_hsteps
                have hinv2r := s7_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                  (hcore2 ▸ hinvW1.sparseW.2.1)
                refine s7_call_restart rfl hRst hinv2r (fullM6HdrMem_unfocus (by assumption)) ?_
                intro s3 m3 hinv3 _ hfu3 hm3
                dsimp only at hfu3
                c0_hsteps!
                exact ih (rlim, reord, last_red, c, ext, s3) m3
                  (hmu_rare rfl (by first
                    | (rw [hfu3]; try rw [hcore2]; rw [hfu1_pred]; exact le_refl _)
                    | (try rw [hcore2] at hfu3; rw [hfu1_pred] at hfu3; exact hfu3)) hinv3)
                  ⟨hcompat, hinv3, hm3⟩
              · c0_hstep; c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mr => (FullM6HdrMem c ext s2 ⋆ R) mr) ?_
                  (fun _ hJr => by
                    have hm2_f' := fullM6HdrMem_focus hm2
                    c0_hsteps_nogrp
                    · have hinv2o := s7_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                        (hcore2 ▸ hinvW1.sparseW.2.1)
                      refine s7_call_reorder rfl hReorder hinv2o
                        (fullM6HdrMem_unfocus (by assumption)) ?_
                      intro _ s3 m3 hinv3 hfu3 hm3
                      dsimp only at hfu3
                      c0_hsteps!
                      exact ih (s2.scratch.conflicts + 10000#64 * (reord + 1#64), reord + 1#64,
                          last_red, c, ext, s3) m3
                        (hmu_rare rfl (by first
                          | (rw [hfu3]; try rw [hcore2]; rw [hfu1_pred]; exact le_refl _)
                          | (try rw [hcore2] at hfu3; rw [hfu1_pred] at hfu3; exact hfu3)) hinv3)
                        ⟨hcompat, hinv3, hm3⟩
                    · exact hJr () m2 hm2
                    · exact hJr () m2 hm2)
                rintro _ _ mr hmr
                c0_hstep
                refine wp_join_group (ts := []) (fun _ mp => (FullM6HdrMem c ext s2 ⋆ R) mp) ?_
                  (fun _ hJp => by
                    have hm_f := fullM6HdrMem_focus hmr
                    c0_hsteps_nogrp
                    · have hinv2p := s7_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                        (hcore2 ▸ hinvW1.sparseW.2.1)
                      refine s7_call_rephase rfl hRephase hinv2p
                        (fullM6HdrMem_unfocus (by assumption)) ?_
                      intro s3 m3 hinv3 hfu3 hm3
                      dsimp only at hfu3
                      c0_hsteps!
                      exact ih (rlim, reord, last_red, c, ext, s3) m3
                        (hmu_rare rfl (by first
                          | (rw [hfu3]; try rw [hcore2]; rw [hfu1_pred]; exact le_refl _)
                          | (try rw [hcore2] at hfu3; rw [hfu1_pred] at hfu3; exact hfu3)) hinv3)
                        ⟨hcompat, hinv3, hm3⟩
                    · exact hJp () mr hmr
                    · exact hJp () mr hmr)
                rintro _ _ mp hmp
                c0_hstep
                refine wp_join_group (ts := []) (fun _ mq => (FullM6HdrMem c ext s2 ⋆ R) mq) ?_
                  (fun _ hJq => by
                    have hm_f := fullM6HdrMem_focus hmp
                    c0_hsteps_nogrp
                    · have hinv2p := s7_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                        (hcore2 ▸ hinvW1.sparseW.2.1)
                      refine s7_call_simplify (dp := true) (de := false) rfl hSimplify hinv2p
                        (fullM6HdrMem_unfocus (by assumption)) ?_
                      intro sr c3 ext3 s3 m3 hcomp3 hlen3 hcfg3 hext3 _ hfu3 hu3 hs1 hm3
                      refine s7_search_simplify_cont hcompat hcomp3 hlen3 hcfg3 hext3 hcore2
                        hfu_pos hfu1_pos hfu1 hfu1_pred hfu3 hu3 hs1 hm3 hQ fun hinv3 hdec => ?_
                      c0_hsteps!
                      exact ih (rlim, reord, last_red, c3, ext3, s3) m3 hdec
                        ⟨hcompat.trans hcomp3, hinv3, hm3⟩
                    · exact hJq () mp hmp
                    · exact hJq () mp hmp)
                rintro _ _ mq hmq
                c0_hstep
                refine wp_join_group (ts := []) (fun _ me => (FullM6HdrMem c ext s2 ⋆ R) me) ?_
                  (fun _ hJe => by
                    have hm_f := fullM6HdrMem_focus hmq
                    c0_hsteps_nogrp
                    · have hinv2e := s7_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                        (hcore2 ▸ hinvW1.sparseW.2.1)
                      refine s7_call_simplify (dp := false) (de := true) rfl hSimplify hinv2e
                        (fullM6HdrMem_unfocus (by assumption)) ?_
                      intro sr c3 ext3 s3 m3 hcomp3 hlen3 hcfg3 hext3 _ hfu3 hu3 hs1 hm3
                      refine s7_search_simplify_cont hcompat hcomp3 hlen3 hcfg3 hext3 hcore2
                        hfu_pos hfu1_pos hfu1 hfu1_pred hfu3 hu3 hs1 hm3 hQ fun hinv3 hdec => ?_
                      c0_hsteps!
                      exact ih (rlim, reord, last_red, c3, ext3, s3) m3 hdec
                        ⟨hcompat.trans hcomp3, hinv3, hm3⟩
                    · exact hJe () mq hmq
                    · exact hJe () mq hmq)
                rintro _ _ me hme
                refine s7_call_decideFid rfl hDecideFid hinv2 hme ?_
                intro dr ext3 s3 m3 hinv3 hdomd hfu3 h0d h1d hm3
                have hlen3 := hinv3.sparse.lengths
                have hm3_f := fullM6HdrMem_focus hm3
                c0_hsteps!
                · exact hQ 10#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                    (Or.inr (Or.inl rfl)) (fun hc => by cases hc)
                    (fun _ => hinv3.sparse.2.2.2.1.2) hm3
                · exact hQ 0#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                    (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
                · have hdr1 : dr = 1#64 := hdomd.resolve_left hc
                  obtain ⟨_, hte3⟩ := h1d hdr1
                  have hte_lt : s.core.trail_end < s3.core.trail_end := by
                    have := htr1.1; rw [hcore2] at hte3; omega
                  have hte3_le : s3.core.trail_end ≤ c.max_vars :=
                    Nat.le_trans hlen3.core_ok.trail_end_le hlen3.core_ok.cur_vars_le
                  have hmu_dec : s7SearchVariant c s3 < s7SearchVariant c s := by
                    unfold s7SearchVariant; rw [hfu3, hcore2]
                    have hmul : (c.max_vars + 1) * s1.core.fuel.toNat ≤
                        (c.max_vars + 1) * s.core.fuel.toNat :=
                      Nat.mul_le_mul_left (c.max_vars + 1) hfu1
                    have hte0_le : s.core.trail_end ≤ c.max_vars :=
                      Nat.le_trans hlen.core_ok.trail_end_le hlen.core_ok.cur_vars_le
                    omega
                  exact ih (rlim, reord, last_red, c, ext3, s3) m3 hmu_dec
                    ⟨hcompat, hinv3, hm3⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep7

end
