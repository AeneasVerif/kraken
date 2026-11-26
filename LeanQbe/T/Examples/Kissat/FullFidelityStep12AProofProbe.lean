/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12A
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof1a
public import LeanQbe.T.Examples.Kissat.FullM7Search
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-12A Probe Proof (`FullFidelityStep12AProofProbe`)

Parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`, `XPost`-polymorphic) for `full_probe_m6` (`P0-1`: zeros
`glue_used[32]` before `full_sweep_dense_m6` and gates sweep delay reduction on
`sa > sb && swept > 0ULL && (sa - sb) * 1000ULL >= swept`, preserving `FullM6Orch.m6ProbeSpec`).
-/

set_option autoImplicit false

local elab "c0_hsteps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_hsteps_prune" : tactic =>
  `(tactic| c0_hsteps_nogrp <;>
    (first
     | exact absurd (by assumption : true = false) (by decide)
     | exact absurd (by assumption : false = true) (by decide)
     | exact absurd (by assumption : !false = false) (by decide)
     | exact absurd (by assumption : !true = true) (by decide)
     | skip))

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12A

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullFidelityStep7 (step7SortBinWatchesSpec)
open LeanQbe.T.Examples.Kissat.FullM3Backbone LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullDefSweep (fullSweepDenseSpec)
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM6Hdr LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7Search
open scoped Full.FullArenaTactics FullM6Hdr.M6HdrTactics FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. Helpers -/

private theorem s12a_probe_ret_wm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
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

private theorem s12a_dense_zero_gu32 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with glue_used := s.scratch.glue_used.set 32 0#32 } } :=
  let sc_ok := h.lengths.scratch_ok
  h.of_safetySlice
    ⟨h.lengths.core_ok, { sc_ok with glue_used_len := (by simp [sc_ok.glue_used_len]) }⟩
    rfl ⟨rfl, rfl⟩

private theorem s12a_probe_set_search_ticks {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s) (st : BitVec 64) :
    FullM6HdrInv c F0 ext { s with scratch := { s.scratch with search_ticks := st } } :=
  let hsc := h.sparse.lengths.scratch_ok
  fullM6HdrInv_of_core_eq h
    ⟨h.sparse.lengths.core_ok, { hsc with last_learned_len := hsc.last_learned_len }⟩
    rfl ⟨rfl, rfl⟩

private theorem s12a_scratch_probe_upd_eq (s : FullState) (pl : BitVec 64) :
    ({ s with scratch := { s.scratch with probe_limit := pl, probings := s.scratch.probings } } :
      FullState) =
      { s with scratch := { s.scratch with probe_limit := pl } } := by
  cases s with | mk core sc => cases sc; rfl

private theorem s12a_probe_init_call {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext0 : List (BitVec 64)} {s s0a : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {parg : BitVec 64} {J1 : Cont []}
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScaleM5 : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
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
      have hm_lim :
          (FullMem c
            { s0a with scratch := { s0a.scratch with probe_limit := s0a.scratch.conflicts + sd } }
            ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m := by assumption
      rw [← s12a_scratch_probe_upd_eq s0a (s0a.scratch.conflicts + sd)] at hm_lim
      exact hJ1 () m ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0a,
        by rw [hst1.2.1, hfu0a], fullM6HdrMem_unfocus hm_lim⟩)
    (fun _ hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption))

/-! ## 2. Parametric `Func.wp` Proof for `full_probe_m6` -/

/-- Step-12A `full_probe_m6` (`(sa - sb) * 1000 >= swept` sweep delay check) preserves
`FullM6Orch.m6ProbeSpec`. -/
theorem full_probe_m6_step12a_wp (Γ : Env)
    (hProbeDt : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScaleM5 : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, m6aVivifySpec a m Q X → Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X → Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebNosort : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweepD : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, fullBackboneSpec a m Q X → Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hSortBin : ∀ a m Q X, step7SortBinWatchesSpec a m Q X →
      Γ "full_sort_bin_watches_fid" [i64] [] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X → Func.wp Γ full_probe_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_m6_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsteps_nogrp
  let saved_st := s.scratch.search_ticks
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
    clear hm s0a hst0a hinv0a hcl0a hm0a s0 hc0 hlen0 hms0 hext0 hinv0 hcl0' hProbeDt
      hLog10 hScaleM5
    refine wp_join_group (ts := [.bool]) (fun _ mT => ∃ extT sT, FullM6HdrInv c F0 extT sT ∧
        sT.core.cur_level = 0 ∧ sT.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c extT sT ⋆ R) mT) ?_ ?_
    · rintro _ ⟨bin_dirty, ⟨⟩⟩ mT ⟨extT, sT, hinvT, hclT, hfuT, hmT⟩
      refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64, i64]) (fun (fr, _fp, ()) mL => mL = mT ∧ fr.toNat ≤ 19)
        (fun (fr, _, ()) _ => 19 - fr.toNat)
        (fun JL hJL => by c0_hsteps_nogrp; exact hJL (1#64, 10#64, ()) mT ⟨rfl, by decide⟩)
        (fun JL (fr, fp, ()) mL ⟨hmL, hfr_le⟩ ihL => ?_)
      · rcases hmL with rfl
        refine wp_join_group (ts := []) (fun _ mEx => mEx = mL) ?_ ?_
        · rintro _ ⟨⟩ mEx rfl
          clear ihL
          refine wp_join_group (ts := [i64]) (fun _ mf => mf = mEx)
            (fun _ ⟨fe4, ⟨⟩⟩ mf hmf => ?_)
            (fun _ hJfe => by
              c0_hsteps_nogrp <;> exact hJfe (_, ()) mEx rfl)
          subst mf
          c0_hsteps_nogrp
          refine wp_join_group (ts := [.bool]) (fun _ mF => ∃ extF sF,
              FullM6HdrInv c F0 extF sF ∧ sF.core.cur_level = 0 ∧
              sF.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extF sF ⋆ R) mF) ?_ ?_
          · rintro _ ⟨bin_dF, ⟨⟩⟩ mF ⟨extF, sF, hinvF, hclF, hfuF, hmF⟩
            refine wp_join_group (ts := []) (fun _ mB => ∃ extB sB,
                FullM6HdrInv c F0 extB sB ∧ sB.core.cur_level = 0 ∧
                sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extB sB ⋆ R) mB) ?_ ?_
            · rintro _ ⟨⟩ mB ⟨extB, sB, hinvB, hclB, hfuB, hmB⟩
              refine wp_m6Hdr_focus_frame hmB fun hmBf => ?_
              c0_hsteps_nogrp
              have hmB' := fullM6HdrMem_unfocus (by assumption)
              have hinvB' := s12a_probe_set_search_ticks hinvB saved_st
              exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB'.cfgOk hinvB'.extOk
                hinvB'.sparse.lengths hfuB (Or.inl rfl) (fun h => by cases h)
                (fun _ => ⟨hinvB', hclB⟩) hmB' (hQ 1#64)
            · intro JB hJB
              c0_hsteps_nogrp
              · refine wp_m6Hdr_focus_frame hmF fun hmFf => ?_
                obtain ⟨F_curB, hwB⟩ := hinvF.sparse.1.witness
                have hinvWB : FullSparseInvW c F0 F_curB sF :=
                  ⟨hinvF.sparse.lengths, hwB, hinvF.sparse.2.1, hinvF.sparse.2.2.1,
                   hinvF.sparse.2.2.2.1, hinvF.sparse.2.2.2.2⟩
                c0_call hSortBin
                refine ⟨c, F0, F_curB, sF, m6ExtMem (m6ExtAddr c.hdr) extF ⋆ R, rfl, hinvWB, hmFf,
                  fun wstk' mB' hwc hinvWB' _ hmB' => ?_⟩
                exact hJB () mB' ⟨extF, { sF with core := { sF.core with wstk := wstk' } },
                  FullM6HdrInv.mk_inv hinvF.cfgOk hinvF.extOk hinvWB'.toSparse,
                  hclF, hfuF, fullM6HdrMem_unfocus hmB'⟩
              · exact hJB () mF ⟨extF, sF, hinvF, hclF, hfuF, hmF⟩
          · intro JF hJF
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mInc => ∃ extInc sInc,
                FullM6HdrInv c F0 extInc sInc ∧ sInc.core.cur_level = 0 ∧
                sInc.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c extInc sInc ⋆ R) mInc)
              ?_ ?_
            · rintro _ ⟨⟩ mInc ⟨extInc, sInc, hinvInc, hclInc, hfuInc, hmInc⟩
              refine wp_m6Hdr_focus_frame hmInc fun hmIncf => ?_
              c0_hsteps_nogrp
              · exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvInc.cfgOk hinvInc.extOk
                  hinvInc.sparse.lengths hfuInc (Or.inr rfl)
                  (fun _ => fullM6HdrInv_inconsistent_unsat hinvInc ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmIncf) (hQ 20#64)
              · exact hJF (bin_dirty, ()) mInc
                  ⟨extInc, sInc, hinvInc, hclInc, hfuInc, fullM6HdrMem_unfocus hmIncf⟩
            · intro Jinc hJinc
              refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
              c0_hsteps_nogrp
              · c0_call hEnter
                refine ⟨c, F0, sT, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hinvT.sparse, hmTf,
                  fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
                have hmE' := fullM6HdrMem_unfocus hmE
                have hfuE' := Nat.le_trans hfuE hfuT
                c0_hsteps_nogrp
                · have hdenE' := hdenE ‹_›
                  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hGetWm _ _ _ _ h) hinvT.cfgOk
                    hinvT.extOk hdenE'.lengths hmE'
                    fun ⟨wval, ⟨⟩⟩ extW sW mW hcW hlW hmsW hextW _ hmW => ?_
                  have hdenW := fullDenseInv_of_core_eq hdenE' hlW hcW hmsW.extPres
                  have hfuW : sW.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcW]; exact hfuE'
                  c0_hsteps_nogrp
                  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hinvT.cfgOk
                    hextW hlW hmW fun _ extS sS mS hcS hlS hmsS hextS _ hmS => ?_
                  have hdenS := fullDenseInv_of_core_eq hdenW hlS hcS hmsS.extPres
                  have hfuS : sS.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcS]; exact hfuW
                  refine wp_join_group (ts := [i64]) (fun _ mb => mb = mS)
                    (fun _ ⟨fbud, ⟨⟩⟩ mb hmb => ?_)
                    (fun _ hJfb => by c0_hsplit <;> (c0_hsteps_nogrp; exact hJfb (_, ()) _ rfl))
                  subst hmb
                  refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
                  c0_call hFactor
                  refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extS ⋆ R, rfl, hdenS, hmSf,
                    fun _ sFa mFa hdenFa _ hfuFa _ hmFa => ?_⟩
                  have hfuFa' : sFa.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfuFa]; exact hfuS
                  c0_call hRebNosort
                  refine ⟨c, F0, sFa, m6ExtMem (m6ExtAddr c.hdr) extS ⋆ R, rfl, hdenFa, hmFa,
                    fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                  have hinvR := FullM6HdrInv.mk_inv hinvT.cfgOk hextS hspR
                  have hmR' := fullM6HdrMem_unfocus hmR
                  have hfuR' := Nat.le_trans hfuR hfuFa'
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextS
                      hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · exact hJF (true, ()) mR ⟨extS, sR, hinvR, hclR, hfuR', hmR'⟩
                · have hinvE := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk (hspE ‹_›)
                  exact hJinc () mE ⟨extT, sE, hinvE, hclE, hfuE', hmE'⟩
              all_goals exact hJinc () _ ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
        · intro Jex hJex
          c0_hsteps_nogrp
          · have hfr_lt : fr.toNat < 19 :=
              Nat.lt_of_lt_of_eq (BitVec.lt_def.mp (by assumption : fr < 19#64)) (by decide)
            have hfr1 : (fr + 1#64).toNat = fr.toNat + 1 := by bv_omega
            exact ihL (fr + 1#64, fp * 10#64, ()) mL (by dsimp only; rw [hfr1]; omega)
              ⟨rfl, by rw [hfr1]; omega⟩
          all_goals exact hJex () mL rfl
    · intro JT hJT
      cases initial
      · -- `!initial`
        c0_hsteps_prune
        refine wp_join_group (ts := [.bool, i64]) (fun (bin_b, _rnd, ()) mB => ∃ extB sB,
            FullM6HdrInv c F0 extB sB ∧ sB.core.cur_level = 0 ∧
            sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extB sB ⋆ R) mB)
          (fun _ (bin_b, _rnd, ()) mB ⟨extB, sB, hinvB, hclB, hfuB, hmB⟩ =>
            hJT (bin_b, ()) mB ⟨extB, sB, hinvB, hclB, hfuB, hmB⟩) ?_
        intro Jbrk hJbrk
        c0_hsteps_nogrp
        refine wp_loop_inv (fun (bin_dL, round, ()) mL => round.toNat ≤ 2 ∧
            ∃ extL sL, FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
              sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL)
          (fun (_bin, round, ()) _ => 2 - round.toNat)
          (fun JL hJL => by
            c0_hsteps_nogrp
            exact hJL (false, 0#64, ()) m1
              ⟨Nat.zero_le _, ext1, s1, hinv1, hcl1, by rw [hfu1]; exact Nat.le_refl _, hm1⟩)
          (fun JL (bin_dL, round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ ihL => ?_)
        · c0_hsteps_nogrp
          · have hnd_lt : round.toNat < 2 := by
              have h := BitVec.lt_def.mp (by assumption : round < 2#64)
              exact Nat.lt_of_lt_of_eq h (by decide)
            have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
            let before_unass := sL.core.unassigned
            refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
            c0_hsteps_nogrp
            have hmL' := fullM6HdrMem_unfocus hmLf
            refine wp_join_group (ts := [.bool]) (fun _ mC => ∃ extC sC,
                FullM6HdrInv c F0 extC sC ∧ sC.core.cur_level = 0 ∧
                sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
            · rintro _ ⟨bin_dC, ⟨⟩⟩ mC ⟨extC, sC, hinvC, hclC, hfuC, hmC⟩
              refine wp_join_group (ts := []) (fun _ mS1 => ∃ extS1 sS1,
                  FullM6HdrInv c F0 extS1 sS1 ∧ sS1.core.cur_level = 0 ∧
                  sS1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extS1 sS1 ⋆ R) mS1)
                ?_ ?_
              · rintro _ _ mS1 ⟨extS1, sS1, hinvS1, hclS1, hfuS1, hmS1⟩
                refine wp_join_group (ts := []) (fun _ mB1 => ∃ extB1 sB1,
                    FullM6HdrInv c F0 extB1 sB1 ∧ sB1.core.cur_level = 0 ∧
                    sB1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extB1 sB1 ⋆ R) mB1) ?_ ?_
                · rintro _ _ mB1 ⟨extB1, sB1, hinvB1, hclB1, hfuB1, hmB1⟩
                  dsimp only [Blocks.get_here, Blocks.get_there]
                  c0_call hViv
                  refine m6aVivifySpec_of hinvB1.cfgOk hinvB1.extOk hinvB1.sparse hmB1
                    fun rV extV sV mV ⟨hextV, _⟩ hspV ⟨hclV, _⟩ hfuV _ huV hmV => ?_
                  have hinvV := FullM6HdrInv.mk_inv hinvB1.cfgOk hextV hspV
                  have hfuV' := Nat.le_trans hfuV hfuB1
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmV fun hmVf => ?_
                    c0_hsteps_nogrp
                    exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvV.cfgOk hextV
                      hinvV.sparse.lengths hfuV' (Or.inr rfl) (fun _ => huV ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmVf) (hQ 20#64)
                  · refine wp_join_group (ts := [.bool]) (fun _ mSw => ∃ extSw sSw,
                        FullM6HdrInv c F0 extSw sSw ∧ sSw.core.cur_level = 0 ∧
                        sSw.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extSw sSw ⋆ R) mSw) ?_ ?_
                    · rintro _ ⟨bin_dSw, ⟨⟩⟩ mSw ⟨extSw, sSw, hinvSw, hclSw, hfuSw, hmSw⟩
                      dsimp only [Blocks.get_here, Blocks.get_there]
                      refine wp_join_group (ts := []) (fun _ mS2 => ∃ extS2 sS2,
                          FullM6HdrInv c F0 extS2 sS2 ∧ sS2.core.cur_level = 0 ∧
                          sS2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extS2 sS2 ⋆ R) mS2) ?_ ?_
                      · rintro _ _ mS2 ⟨extS2, sS2, hinvS2, hclS2, hfuS2, hmS2⟩
                        dsimp only [Blocks.get_here, Blocks.get_there]; c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ mTr => ∃ extTr sTr,
                            FullM6HdrInv c F0 extTr sTr ∧ sTr.core.cur_level = 0 ∧
                            sTr.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extTr sTr ⋆ R) mTr) ?_ ?_
                        · rintro _ _ mTr ⟨extTr, sTr, hinvTr, hclTr, hfuTr, hmTr⟩
                          dsimp only [Blocks.get_here, Blocks.get_there]; c0_hsteps_nogrp
                          refine wp_join_group (ts := []) (fun _ mB2 => ∃ extB2 sB2,
                              FullM6HdrInv c F0 extB2 sB2 ∧ sB2.core.cur_level = 0 ∧
                              sB2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extB2 sB2 ⋆ R) mB2) ?_ ?_
                          · rintro _ _ mB2 ⟨extB2, sB2, hinvB2, hclB2, hfuB2, hmB2⟩
                            refine wp_m6Hdr_focus_frame hmB2 fun hmB2f => ?_
                            c0_hsteps_nogrp
                            · exact hJbrk (bin_dSw, round, ()) mB2
                                ⟨extB2, sB2, hinvB2, hclB2, hfuB2, fullM6HdrMem_unfocus hmB2f⟩
                            · exact ihL (bin_dSw, round + 1#64, ()) mB2 (by dsimp only; omega)
                                ⟨by omega, extB2, sB2, hinvB2, hclB2, hfuB2,
                                  fullM6HdrMem_unfocus hmB2f⟩
                          · intro JB2 hJB2
                            refine wp_m6Hdr_focus_frame hmTr fun hmTrf => ?_
                            c0_hsteps_nogrp
                            · c0_call hBone
                              refine ⟨c, F0, sTr, m6ExtMem (m6ExtAddr c.hdr) extTr ⋆ R, rfl,
                                hinvTr.sparse, hmTrf, fun rB sB mB hspB hclB _ hfuB _ huB hmB => ?_⟩
                              have hinvB := FullM6HdrInv.mk_inv hinvTr.cfgOk hinvTr.extOk hspB
                              have hmB' := fullM6HdrMem_unfocus hmB
                              have hfuB' := Nat.le_trans hfuB hfuTr
                              c0_hsteps_nogrp
                              · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
                                c0_hsteps_nogrp
                                exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB.cfgOk
                                  hinvB.extOk hinvB.sparse.lengths hfuB' (Or.inr rfl)
                                  (fun _ => huB ‹_›) (fun h => by cases h)
                                  (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
                              · exact hJB2 () mB ⟨extTr, sB, hinvB, hclB, hfuB', hmB'⟩
                            · exact hJB2 () mTr ⟨extTr, sTr, hinvTr, hclTr, hfuTr,
                                fullM6HdrMem_unfocus hmTrf⟩
                        · intro JTr hJTr
                          refine wp_m6Hdr_focus_frame hmS2 fun hmS2f => ?_
                          c0_hsteps_nogrp
                          · c0_call hTrans
                            refine ⟨c, F0, sS2, m6ExtMem (m6ExtAddr c.hdr) extS2 ⋆ R, rfl,
                              hinvS2.sparse, hmS2f,
                              fun rT sT mT hspT hclT _ _ hfuT _ huT hmT => ?_⟩
                            have hinvT := FullM6HdrInv.mk_inv hinvS2.cfgOk hinvS2.extOk hspT
                            have hmT' := fullM6HdrMem_unfocus hmT
                            have hfuT' := Nat.le_trans hfuT hfuS2
                            c0_hsteps_nogrp
                            · refine wp_m6Hdr_focus_frame hmT' fun hmTf => ?_
                              c0_hsteps_nogrp
                              exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvT.cfgOk
                                hinvT.extOk hinvT.sparse.lengths hfuT' (Or.inr rfl)
                                (fun _ => huT ‹_›) (fun h => by cases h)
                                (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
                            · exact hJTr () mT ⟨extS2, sT, hinvT, hclT hclS2, hfuT', hmT'⟩
                          · exact hJTr () mS2 ⟨extS2, sS2, hinvS2, hclS2, hfuS2,
                              fullM6HdrMem_unfocus hmS2f⟩
                      · intro JS2 hJS2
                        refine wp_m6Hdr_focus_frame hmSw fun hmSwf => ?_
                        c0_hsteps_nogrp
                        · c0_call hSubst
                          refine ⟨c, F0, sSw, m6ExtMem (m6ExtAddr c.hdr) extSw ⋆ R, rfl,
                            hinvSw.sparse, hmSwf, fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu =>
                              ?_⟩
                          have hinvSu := FullM6HdrInv.mk_inv hinvSw.cfgOk hinvSw.extOk hspSu
                          have hmSu' := fullM6HdrMem_unfocus hmSu
                          have hfuSu' := Nat.le_trans hfuSu hfuSw
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                            c0_hsteps_nogrp
                            exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk
                              hinvSu.extOk hinvSu.sparse.lengths hfuSu' (Or.inr rfl)
                              (fun _ => huSu ‹_›) (fun h => by cases h)
                              (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                          · exact hJS2 () mSu ⟨extSw, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
                        · exact hJS2 () mSw ⟨extSw, sSw, hinvSw, hclSw, hfuSw,
                            fullM6HdrMem_unfocus hmSwf⟩
                    · -- Inproc `M6_DELAY_SWEEP` block (`P0-1`)
                      intro JSw hJSw
                      refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                        hinvV.cfgOk hinvV.extOk hinvV.sparse.lengths hmV
                        fun ⟨delSw, ⟨⟩⟩ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                      have hinvSd := fullM6HdrInv_with_ext
                        (fullM6HdrInv_of_m6Pres hinvV hlSd hcSd hmsSd) hextSd
                      have hclSd : sSd.core.cur_level = 0 := by rw [hcSd]; exact hclV
                      have hfuSd : sSd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hcSd]; exact hfuV'
                      c0_hsteps_nogrp
                      · exact hJSw (bin_dC, ()) mSd ⟨extSd, sSd, hinvSd, hclSd, hfuSd, hmSd⟩
                      · refine wp_join_group (ts := [.bool])
                            (fun _ mW => ∃ extW sW,
                              FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                              sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extW sW ⋆ R) mW)
                          (fun _ p mp hp => by
                            dsimp only [Blocks.get_here, Blocks.get_there]; exact hJSw p mp hp) ?_
                        intro JSw' hJSw'
                        refine wp_m6Hdr_focus_frame hmSd fun hmSdf => ?_
                        c0_hsteps_nogrp
                        · c0_call hEnter
                          refine ⟨c, F0, sSd, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl,
                            hinvSd.sparse, hmSdf, fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
                          have hmE' := fullM6HdrMem_unfocus hmE
                          have hfuE' := Nat.le_trans hfuE hfuSd
                          c0_hsteps_nogrp
                          · have hdenE' := hdenE ‹_›
                            refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                            have hgu32E : 32 < sE.scratch.glue_used.length := by
                              rw [hdenE'.lengths.scratch_ok.glue_used_len]; decide
                            c0_hsteps_nogrp
                            have hdenEz := s12a_dense_zero_gu32 hdenE'
                            c0_call hSweepD
                            refine ⟨c, F0, _, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl, hdenEz,
                              by assumption, fun rSw sSw mSw hdenSw hclSw hfuSw hrSw huSw hmSw =>
                              ?_⟩
                            have hfuSw' := Nat.le_trans hfuSw hfuE'
                            have hgu32Sw : 32 < sSw.scratch.glue_used.length := by
                              rw [hdenSw.lengths.scratch_ok.glue_used_len]; decide
                            c0_hsteps_nogrp
                            · c0_call hRebNosort
                              refine ⟨c, F0, sSw, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl,
                                hdenSw, hmSw, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                              have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextSd hspR
                              have hmR' := fullM6HdrMem_unfocus hmR
                              refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                              c0_hsteps_nogrp
                              exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextSd
                                hinvR.sparse.lengths (Nat.le_trans hfuR hfuSw') (Or.inr rfl)
                                (fun _ => huSw ‹_›) (fun h => by cases h)
                                (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                            · have hmSw' := fullM6HdrMem_unfocus hmSw
                              refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                                  M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                                  sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                              · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                                refine wp_m6Hdr_focus_frame hmDl fun hmDlf => ?_
                                c0_hsteps_nogrp
                                c0_call hRebNosort
                                refine ⟨c, F0, sDl, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl,
                                  hdenDl, hmDlf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                                have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextDl hspR
                                have hmR' := fullM6HdrMem_unfocus hmR
                                have hfuR' := Nat.le_trans hfuR hfuDl
                                c0_hsteps_nogrp
                                · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                                  c0_hsteps_nogrp
                                  exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk
                                    hextDl hinvR.sparse.lengths hfuR' (Or.inr rfl)
                                    (fun _ => huR ‹_›) (fun h => by cases h)
                                    (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                                · exact hJSw' (true, ()) mR ⟨extDl, sR, hinvR, hclR, hfuR', hmR'⟩
                              · intro JDl hJDl
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                                    M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                                    sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                    (FullM6HdrMem c extDl sDl ⋆ R) mDl)
                                  (fun _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩ => by
                                    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                                      hinvV.cfgOk hextDl hdenDl.lengths hmDl
                                      fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                                    exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                                      fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                                      by rw [hcDl]; exact hfuDl, hmDl'⟩) ?_
                                intro JDb hJDb
                                refine wp_m6Hdr_focus_frame hmSw' fun hmSwf => ?_
                                have hgu32Sw : 32 < sSw.scratch.glue_used.length := by
                                  rw [hdenSw.lengths.scratch_ok.glue_used_len]; decide
                                c0_hsteps_nogrp
                                · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                                    hinvV.cfgOk hextSd hdenSw.lengths (fullM6HdrMem_unfocus hmSwf)
                                    fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                                  exact hJDl () mDl ⟨extDl, sDl, hextDl,
                                    fullDenseInv_of_core_eq hdenSw hlDl hcDl hmsDl.extPres,
                                    by rw [hcDl]; exact hfuSw', hmDl⟩
                                all_goals
                                  exact hJDb () _ ⟨extSd, sSw, hextSd, hdenSw, hfuSw',
                                    fullM6HdrMem_unfocus hmSwf⟩
                          · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hextSd (hspE ‹_›)
                            refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                            c0_hsteps_nogrp
                            exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hextSd
                              hinvE.sparse.lengths hfuE' (Or.inr rfl)
                              (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
                          · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hextSd (hspE ‹_›)
                            exact hJSw' (bin_dC, ()) mE ⟨extSd, sE, hinvE, hclE, hfuE', hmE'⟩
                · intro JB1 hJB1
                  refine wp_m6Hdr_focus_frame hmS1 fun hmS1f => ?_
                  c0_hsteps_nogrp
                  · c0_call hBone
                    refine ⟨c, F0, sS1, m6ExtMem (m6ExtAddr c.hdr) extS1 ⋆ R, rfl,
                      hinvS1.sparse, hmS1f, fun rB sB mB hspB hclB _ hfuB _ huB hmB => ?_⟩
                    have hinvB := FullM6HdrInv.mk_inv hinvS1.cfgOk hinvS1.extOk hspB
                    have hmB' := fullM6HdrMem_unfocus hmB
                    have hfuB' := Nat.le_trans hfuB hfuS1
                    c0_hsteps_nogrp
                    · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
                      c0_hsteps_nogrp
                      exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                        hinvB.sparse.lengths hfuB' (Or.inr rfl) (fun _ => huB ‹_›)
                        (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
                    · exact hJB1 () mB ⟨extS1, sB, hinvB, hclB, hfuB', hmB'⟩
                  · exact hJB1 () mS1 ⟨extS1, sS1, hinvS1, hclS1, hfuS1, fullM6HdrMem_unfocus hmS1f⟩
              · intro JS1 hJS1
                refine wp_m6Hdr_focus_frame hmC fun hmCf => ?_
                c0_hsteps_nogrp
                · c0_call hSubst
                  refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extC ⋆ R, rfl, hinvC.sparse, hmCf,
                    fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu => ?_⟩
                  have hinvSu := FullM6HdrInv.mk_inv hinvC.cfgOk hinvC.extOk hspSu
                  have hmSu' := fullM6HdrMem_unfocus hmSu
                  have hfuSu' := Nat.le_trans hfuSu hfuC
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                    c0_hsteps_nogrp
                    exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hinvSu.extOk
                      hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                  · exact hJS1 () mSu ⟨extC, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
                · exact hJS1 () mC ⟨extC, sC, hinvC, hclC, hfuC, fullM6HdrMem_unfocus hmCf⟩
            · intro JC hJC
              refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                hinvL.cfgOk hinvL.extOk hinvL.sparse.lengths hmL'
                fun ⟨delC, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
              have hinvCd := fullM6HdrInv_with_ext
                (fullM6HdrInv_of_m6Pres hinvL hlCd hcCd hmsCd) hextCd
              have hclCd : sCd.core.cur_level = 0 := by rw [hcCd]; exact hclL
              have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfuL
              c0_hsteps_nogrp
              · exact hJC (bin_dL, ()) mCd ⟨extCd, sCd, hinvCd, hclCd, hfuCd, hmCd⟩
              · refine wp_join_group (ts := [.bool]) (fun _ mW => ∃ extW sW,
                    FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                    sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extW sW ⋆ R) mW)
                  (fun _ p mp hp => by
                    dsimp only [Blocks.get_here, Blocks.get_there]; exact hJC p mp hp) ?_
                intro JC' hJC'
                refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                c0_hsteps_nogrp
                · c0_call hEnter
                  refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hinvCd.sparse,
                    hmCdf, fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
                  have hmE' := fullM6HdrMem_unfocus hmE
                  have hfuE' := Nat.le_trans hfuE hfuCd
                  c0_hsteps_nogrp
                  · have hdenE' := hdenE ‹_›
                    refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                    c0_hsteps_nogrp; c0_call hCong
                    refine ⟨c, F0, sE, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenE', hmEf,
                      fun rC sC mC hdenC _ hfuC _ huC hmC => ?_⟩
                    have hfuC' := Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat hfuC)) hfuE'
                    c0_hsteps_nogrp
                    · c0_call hRebNosort
                      refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenC, hmC,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextCd
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                        (fun _ => huC ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmRf)
                        (hQ 20#64)
                    · have hmC' := fullM6HdrMem_unfocus hmC
                      refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                          M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                          sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                      · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                        refine wp_m6Hdr_focus_frame hmDl fun hmDlf => ?_
                        c0_hsteps_nogrp
                        c0_call hRebNosort
                        refine ⟨c, F0, sDl, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl, hdenDl,
                          hmDlf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                        have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextDl hspR
                        have hmR' := fullM6HdrMem_unfocus hmR
                        have hfuR' := Nat.le_trans hfuR hfuDl
                        c0_hsteps_nogrp
                        · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                          c0_hsteps_nogrp
                          exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextDl
                            hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                            (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                        · exact hJC' (true, ()) mR ⟨extDl, sR, hinvR, hclR, hfuR', hmR'⟩
                      · intro JDl hJDl
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                            M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                            sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extDl sDl ⋆ R) mDl)
                          (fun _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩ => by
                            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                              hinvL.cfgOk hextDl hdenDl.lengths hmDl
                              fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                            exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                              fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                              by rw [hcDl]; exact hfuDl, hmDl'⟩) ?_
                        intro JDb hJDb
                        refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                        c0_hsteps_nogrp
                        · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                            hinvL.cfgOk hextCd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                            fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                          exact hJDl () mDl ⟨extDl, sDl, hextDl,
                            fullDenseInv_of_core_eq hdenC hlDl hcDl hmsDl.extPres,
                            by rw [hcDl]; exact hfuC', hmDl⟩
                        · exact hJDb () mC
                            ⟨extCd, sC, hextCd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                        · exact hJDb () mC
                            ⟨extCd, sC, hextCd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                  · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd (hspE ‹_›)
                    refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                    c0_hsteps_nogrp
                    exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hextCd
                      hinvE.sparse.lengths hfuE' (Or.inr rfl)
                      (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
                  · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd (hspE ‹_›)
                    exact hJC' (bin_dL, ()) mE ⟨extCd, sE, hinvE, hclE, hfuE', hmE'⟩
          · exact hJbrk (bin_dL, round, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, hmL⟩
      · -- `initial = true`
        c0_hsteps_prune
        refine wp_join_group (ts := [.bool, .bool]) (fun (bin_dC, subst_e, ()) mC => ∃ extC sC,
            FullM6HdrInv c F0 extC sC ∧ sC.core.cur_level = 0 ∧
            sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
        · rintro _ ⟨bin_dC, subst_e, ⟨⟩⟩ mC ⟨extC, sC, hinvC, hclC, hfuC, hmC⟩
          refine wp_join_group (ts := []) (fun _ mB => ∃ extB sB,
              FullM6HdrInv c F0 extB sB ∧ sB.core.cur_level = 0 ∧
              sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extB sB ⋆ R) mB) ?_ ?_
          · rintro _ ⟨⟩ mB ⟨extB, sB, hinvB, hclB, hfuB, hmB⟩
            refine wp_join_group (ts := [.bool, .bool]) (fun (bin_dS, subst_eS, ()) mS =>
                ∃ extS sS, FullM6HdrInv c F0 extS sS ∧ sS.core.cur_level = 0 ∧
                sS.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extS sS ⋆ R) mS) ?_ ?_
            · rintro _ ⟨bin_dS, subst_eS, ⟨⟩⟩ mS ⟨extS, sS, hinvS, hclS, hfuS, hmS⟩
              refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
              c0_hsteps_nogrp
              · c0_call hSubst
                refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extS ⋆ R, rfl, hinvS.sparse, hmSf,
                  fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu => ?_⟩
                have hinvSu := FullM6HdrInv.mk_inv hinvS.cfgOk hinvS.extOk hspSu
                have hmSu' := fullM6HdrMem_unfocus hmSu
                have hfuSu' := Nat.le_trans hfuSu hfuS
                c0_hsteps_nogrp
                · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                  c0_hsteps_nogrp
                  exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hinvSu.extOk
                    hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                    (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                · exact hJT (bin_dS, ()) mSu ⟨extS, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
              · exact hJT (bin_dS, ()) mS ⟨extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
              · exact hJT (bin_dS, ()) mS ⟨extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
            · -- Initial `M6_DELAY_SWEEP` block (`P0-1`)
              intro JSw hJSw
              refine wp_m6Hdr_focus_frame hmB fun hmBf => ?_
              refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                hinvB.cfgOk hinvB.extOk hinvB.sparse.lengths (fullM6HdrMem_unfocus hmBf)
                fun ⟨delSw, ⟨⟩⟩ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
              have hinvSd := fullM6HdrInv_with_ext
                (fullM6HdrInv_of_m6Pres hinvB hlSd hcSd hmsSd) hextSd
              have hclSd : sSd.core.cur_level = 0 := by rw [hcSd]; exact hclB
              have hfuSd : sSd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcSd]; exact hfuB
              c0_hsteps_nogrp
              · exact hJSw (bin_dC, subst_e, ()) mSd ⟨extSd, sSd, hinvSd, hclSd, hfuSd, hmSd⟩
              · refine wp_join_group (ts := [.bool, .bool]) (fun _ mW => ∃ extW sW,
                    FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                    sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extW sW ⋆ R) mW)
                  (fun _ p mp hp => by
                    dsimp only [Blocks.get_here, Blocks.get_there]; exact hJSw p mp hp) ?_
                intro JSw' hJSw'
                refine wp_m6Hdr_focus_frame hmSd fun hmSdf => ?_
                c0_hsteps_nogrp
                · c0_call hEnter
                  refine ⟨c, F0, sSd, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl, hinvSd.sparse,
                    hmSdf, fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
                  have hmE' := fullM6HdrMem_unfocus hmE
                  have hfuE' := Nat.le_trans hfuE hfuSd
                  c0_hsteps_nogrp
                  · have hdenE' := hdenE ‹_›
                    refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                    have hgu32E : 32 < sE.scratch.glue_used.length := by
                      rw [hdenE'.lengths.scratch_ok.glue_used_len]; decide
                    c0_hsteps_nogrp
                    have hdenEz := s12a_dense_zero_gu32 hdenE'
                    c0_call hSweepD
                    refine ⟨c, F0, _, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl, hdenEz,
                      by assumption, fun rSw sSw mSw hdenSw hclSw hfuSw hrSw huSw hmSw => ?_⟩
                    have hfuSw' := Nat.le_trans hfuSw hfuE'
                    have hgu32Sw : 32 < sSw.scratch.glue_used.length := by
                      rw [hdenSw.lengths.scratch_ok.glue_used_len]; decide
                    c0_hsteps_nogrp
                    · c0_call hRebNosort
                      refine ⟨c, F0, sSw, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl, hdenSw, hmSw,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvB.cfgOk hextSd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextSd
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuSw') (Or.inr rfl)
                        (fun _ => huSw ‹_›) (fun h => by cases h)
                        (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                    · have hmSw' := fullM6HdrMem_unfocus hmSw
                      refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                          M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                          sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                      · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                        refine wp_m6Hdr_focus_frame hmDl fun hmDlf => ?_
                        c0_hsteps_nogrp
                        c0_call hRebNosort
                        refine ⟨c, F0, sDl, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl, hdenDl,
                          hmDlf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                        have hinvR := FullM6HdrInv.mk_inv hinvB.cfgOk hextDl hspR
                        have hmR' := fullM6HdrMem_unfocus hmR
                        have hfuR' := Nat.le_trans hfuR hfuDl
                        c0_hsteps_nogrp
                        · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                          c0_hsteps_nogrp
                          exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextDl
                            hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                            (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                        · refine wp_join_group (ts := [.bool]) (fun _ mW => ∃ extW sW,
                              FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                              sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extW sW ⋆ R) mW)
                            (fun _ p mp hp => by
                              dsimp only [Blocks.get_here, Blocks.get_there]
                              exact hJSw' (true, p.1, ()) mp hp) ?_
                          intro JCe hJCe
                          refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                          c0_hsteps_nogrp
                          · c0_call hSubst
                            refine ⟨c, F0, sR, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl,
                              hinvR.sparse, hmRf, fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu =>
                                ?_⟩
                            have hinvSu := FullM6HdrInv.mk_inv hinvR.cfgOk hextDl hspSu
                            have hmSu' := fullM6HdrMem_unfocus hmSu
                            have hfuSu' := Nat.le_trans hfuSu hfuR'
                            c0_hsteps_nogrp
                            · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                              c0_hsteps_nogrp
                              exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hextDl
                                hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                                (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                            · exact hJCe (false, ()) mSu
                                ⟨extDl, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
                          · exact hJCe (false, ()) mR
                              ⟨extDl, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                          · exact hJCe (subst_e, ()) mR
                              ⟨extDl, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                      · intro JDl hJDl
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                            M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                            sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extDl sDl ⋆ R) mDl)
                          (fun _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩ => by
                            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                              hinvB.cfgOk hextDl hdenDl.lengths hmDl
                              fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                            exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                              fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                              by rw [hcDl]; exact hfuDl, hmDl'⟩) ?_
                        intro JDb hJDb
                        refine wp_m6Hdr_focus_frame hmSw' fun hmSwf => ?_
                        have hgu32Sw : 32 < sSw.scratch.glue_used.length := by
                          rw [hdenSw.lengths.scratch_ok.glue_used_len]; decide
                        c0_hsteps_nogrp
                        · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                            hinvB.cfgOk hextSd hdenSw.lengths (fullM6HdrMem_unfocus hmSwf)
                            fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                          exact hJDl () mDl ⟨extDl, sDl, hextDl,
                            fullDenseInv_of_core_eq hdenSw hlDl hcDl hmsDl.extPres,
                            by rw [hcDl]; exact hfuSw', hmDl⟩
                        all_goals
                          exact hJDb () _ ⟨extSd, sSw, hextSd, hdenSw, hfuSw',
                            fullM6HdrMem_unfocus hmSwf⟩
                  · have hinvE := FullM6HdrInv.mk_inv hinvB.cfgOk hextSd (hspE ‹_›)
                    refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                    c0_hsteps_nogrp
                    exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hextSd
                      hinvE.sparse.lengths hfuE' (Or.inr rfl)
                      (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
                  · have hinvE := FullM6HdrInv.mk_inv hinvB.cfgOk hextSd (hspE ‹_›)
                    exact hJSw' (bin_dC, subst_e, ()) mE ⟨extSd, sE, hinvE, hclE, hfuE', hmE'⟩
          · intro JB hJB
            refine wp_m6Hdr_focus_frame hmC fun hmCf => ?_
            c0_hsteps_nogrp
            · c0_call hBone
              refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extC ⋆ R, rfl, hinvC.sparse, hmCf,
                fun rB sB mB hspB hclB _ hfuB _ huB hmB => ?_⟩
              have hinvB := FullM6HdrInv.mk_inv hinvC.cfgOk hinvC.extOk hspB
              have hmB' := fullM6HdrMem_unfocus hmB
              have hfuB' := Nat.le_trans hfuB hfuC
              c0_hsteps_nogrp
              · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
                c0_hsteps_nogrp
                exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                  hinvB.sparse.lengths hfuB' (Or.inr rfl) (fun _ => huB ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
              · exact hJB () mB ⟨extC, sB, hinvB, hclB, hfuB', hmB'⟩
            · exact hJB () mC ⟨extC, sC, hinvC, hclC, hfuC, fullM6HdrMem_unfocus hmCf⟩
        · intro JC hJC
          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
            hinv1.cfgOk hinv1.extOk hinv1.sparse.lengths hm1
            fun ⟨delC, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
          have hinvCd := fullM6HdrInv_with_ext
            (fullM6HdrInv_of_m6Pres hinv1 hlCd hcCd hmsCd) hextCd
          have hclCd : sCd.core.cur_level = 0 := by rw [hcCd]; exact hcl1
          have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by
            rw [hcCd, hfu1]; exact Nat.le_refl _
          c0_hsteps_nogrp
          · exact hJC (false, true, ()) mCd ⟨extCd, sCd, hinvCd, hclCd, hfuCd, hmCd⟩
          · refine wp_join_group (ts := [.bool, .bool]) (fun _ mW => ∃ extW sW,
                FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extW sW ⋆ R) mW)
              (fun _ p mp hp => by
                dsimp only [Blocks.get_here, Blocks.get_there]; exact hJC p mp hp) ?_
            intro JC' hJC'
            refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
            c0_hsteps_nogrp
            · c0_call hEnter
              refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hinvCd.sparse, hmCdf,
                fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
              have hmE' := fullM6HdrMem_unfocus hmE
              have hfuE' := Nat.le_trans hfuE hfuCd
              c0_hsteps_nogrp
              · have hdenE' := hdenE ‹_›
                refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                c0_hsteps_nogrp; c0_call hCong
                refine ⟨c, F0, sE, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenE', hmEf,
                  fun rC sC mC hdenC _ hfuC _ huC hmC => ?_⟩
                have hfuC' := Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat hfuC)) hfuE'
                c0_hsteps_nogrp
                · c0_call hRebNosort
                  refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenC, hmC,
                    fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                  have hinvR := FullM6HdrInv.mk_inv hinv1.cfgOk hextCd hspR
                  have hmR' := fullM6HdrMem_unfocus hmR
                  refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                  c0_hsteps_nogrp
                  exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextCd
                    hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                    (fun _ => huC ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmRf)
                    (hQ 20#64)
                · have hmC' := fullM6HdrMem_unfocus hmC
                  refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                      M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                      sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                  · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                    refine wp_m6Hdr_focus_frame hmDl fun hmDlf => ?_
                    c0_hsteps_nogrp
                    · c0_call hRebNosort
                      refine ⟨c, F0, sDl, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl, hdenDl,
                        hmDlf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinv1.cfgOk hextDl hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      have hfuR' := Nat.le_trans hfuR hfuDl
                      c0_hsteps_nogrp
                      · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextDl
                          hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                          (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                      · refine wp_join_group (ts := [.bool]) (fun _ mW => ∃ extW sW,
                            FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                            sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extW sW ⋆ R) mW)
                          (fun _ p mp hp => by
                            dsimp only [Blocks.get_here, Blocks.get_there]
                            exact hJC' (true, p.1, ()) mp hp) ?_
                        intro JCe hJCe
                        refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        · c0_call hSubst
                          refine ⟨c, F0, sR, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl,
                            hinvR.sparse, hmRf, fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu =>
                              ?_⟩
                          have hinvSu := FullM6HdrInv.mk_inv hinvR.cfgOk hextDl hspSu
                          have hmSu' := fullM6HdrMem_unfocus hmSu
                          have hfuSu' := Nat.le_trans hfuSu hfuR'
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                            c0_hsteps_nogrp
                            exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hextDl
                              hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                          · exact hJCe (false, ()) mSu
                              ⟨extDl, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
                        · exact hJCe (false, ()) mR
                            ⟨extDl, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                        · exact hJCe (true, ()) mR
                            ⟨extDl, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                  · intro JDl hJDl
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                        M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                        sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extDl sDl ⋆ R) mDl)
                      (fun _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩ => by
                        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                          hinv1.cfgOk hextDl hdenDl.lengths hmDl
                          fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                        exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                          fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                          by rw [hcDl]; exact hfuDl, hmDl'⟩) ?_
                    intro JDb hJDb
                    refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                    c0_hsteps_nogrp
                    · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                        hinv1.cfgOk hextCd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                        fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                      exact hJDl () mDl ⟨extDl, sDl, hextDl,
                        fullDenseInv_of_core_eq hdenC hlDl hcDl hmsDl.extPres,
                        by rw [hcDl]; exact hfuC', hmDl⟩
                    · exact hJDb () mC ⟨extCd, sC, hextCd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                    · exact hJDb () mC ⟨extCd, sC, hextCd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
              · have hinvE := FullM6HdrInv.mk_inv hinv1.cfgOk hextCd (hspE ‹_›)
                refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                c0_hsteps_nogrp
                exact s12a_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hextCd
                  hinvE.sparse.lengths hfuE' (Or.inr rfl)
                  (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
              · have hinvE := FullM6HdrInv.mk_inv hinv1.cfgOk hextCd (hspE ‹_›)
                exact hJC' (false, true, ()) mE ⟨extCd, sE, hinvE, hclE, hfuE', hmE'⟩
  · intro J1 hJ1
    cases initial
    · c0_hsteps_prune
      refine wp_m6Hdr_focus_frame hm0a fun hm0af => ?_
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma =>
          (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) ma)
        (fun _ ⟨parg, ⟨⟩⟩ ma hma =>
          s12a_probe_init_call hLog10 hScaleM5 hinv0a hcl0a (by rw [hst0a.2.1, hc0]) hma hJ1)
        (fun _ hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption))
    · c0_hsteps_prune
      exact hJ1 () _ ⟨ext0, s0a, hinv0a, hcl0a, by rw [hst0a.2.1, hc0], hm0a⟩
