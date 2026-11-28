/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proofs for `Src.Bump` Part 0 (`Proof.Bump.Wp0`)

Canonical `Func.wp` proofs for the first `6` functions of `Src.Bump.fns`:
`full_rescale_m6`, `full_rescale`, `full_bump_var`, `full_bump_decay`,
`full_queue_renumber`, `full_queue_mtf`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Bump

open Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Bump
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
open LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

public section

private theorem bv64_shl1_nat {v : BitVec 64} (h : 2 * v.toNat < 2 ^ 64) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  simpa using bv64_shl1_toNat h

private theorem hlen_upd_score {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {sc' : List (BitVec 64)} (hsc : sc'.length = c.max_vars) :
    ({ s with scratch := { s.scratch with score := sc' } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with score_len := hsc }⟩

private theorem hlen_upd_scinc {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (v : BitVec 64) :
    ({ s with scratch := { s.scratch with scinc := v } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with score_len := hlen.scratch_ok.score_len }⟩

private theorem hlen_upd_qprev {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {qp : List (BitVec 32)} (hqp : qp.length = c.max_vars) :
    ({ s with scratch := { s.scratch with q_prev := qp } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with q_prev_len := hqp }⟩

private theorem hlen_upd_qnext {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {qn : List (BitVec 32)} (hqn : qn.length = c.max_vars) :
    ({ s with scratch := { s.scratch with q_next := qn } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with q_next_len := hqn }⟩

private theorem hlen_upd_qfirst {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (qf : BitVec 64) :
    ({ s with scratch := { s.scratch with q_first := qf } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with q_prev_len := hlen.scratch_ok.q_prev_len }⟩

private theorem hlen_upd_qlast {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (ql : BitVec 64) :
    ({ s with scratch := { s.scratch with q_last := ql } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with q_prev_len := hlen.scratch_ok.q_prev_len }⟩

private theorem hlen_upd_queue {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {qp qn qs : List (BitVec 32)} {qf ql qsi qss qcs : BitVec 64}
    (hqp : qp.length = c.max_vars) (hqn : qn.length = c.max_vars)
    (hqs : qs.length = c.max_vars) :
    ({ s with scratch := { s.scratch with
      q_prev := qp, q_next := qn, q_stamp := qs, q_first := qf, q_last := ql,
      q_search_idx := qsi, q_search_stamp := qss, q_cur_stamp := qcs } } :
      FullState).LengthsOk c :=
  ⟨hlen.core_ok,
    { hlen.scratch_ok with q_prev_len := hqp, q_next_len := hqn, q_stamp_len := hqs }⟩

private theorem probePres_upd_score (s : FullState) (sc' : List (BitVec 64)) :
    FullProbeScratchPres s { s with scratch := { s.scratch with score := sc' } } := by
  simp [FullProbeScratchPres, FullExtScratchPres]

private theorem probePres_upd_scinc (s : FullState) (v : BitVec 64) :
    FullProbeScratchPres s { s with scratch := { s.scratch with scinc := v } } := by
  simp [FullProbeScratchPres, FullExtScratchPres]

private theorem probePres_upd_score_scinc (s : FullState) (sc' : List (BitVec 64))
    (v : BitVec 64) :
    FullProbeScratchPres s
      { s with scratch := { s.scratch with score := sc', scinc := v } } := by
  simp [FullProbeScratchPres, FullExtScratchPres]

private theorem probePres_upd_queue (s : FullState)
    (qp qn qs : List (BitVec 32)) (qf ql qsi qss qcs : BitVec 64) :
    FullProbeScratchPres s
      { s with scratch := { s.scratch with
        q_prev := qp, q_next := qn, q_stamp := qs, q_first := qf, q_last := ql,
        q_search_idx := qsi, q_search_stamp := qss, q_cur_stamp := qcs } } := by
  simp [FullProbeScratchPres, FullExtScratchPres]

theorem full_rescale_m6_wp (Γ : Env)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hDiv : Γ.Has "f64u_div" f64uPure2Spec) :
    ∀ a m Q X, fullRescaleSpec a m Q X →
      Func.wp Γ full_rescale_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hok := hlen.core_ok
  obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hsc_len := hsok.score_len
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  unfold Func.wp full_rescale_m6_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (_mx, mi, ()) m1 => m = m1 ∧ mi.toNat ≤ s.core.cur_vars)
    (fun (_mx, mi, ()) _ => s.core.cur_vars - mi.toNat)
    (fun J1 hJ1 => by
      c0_hsteps_nogrp
      exact hJ1 (0#64, 0#64, ()) m ⟨rfl, Nat.zero_le _⟩)
    (fun J1 (mx, mi, ()) m1 ⟨hm1, hmi_le⟩ ih1 => ?_)
  · rcases hm1 with rfl
    rw [Blocks.get_here]
    c0_hsteps_nogrp
    · have hmi_lt : mi.toNat < s.core.cur_vars := by
        have h1 : mi.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
        rwa [bv64_ofNat_toNat hcv_lt64] at h1
      have hmip1 : (mi + 1#64).toNat = mi.toNat + 1 := by bv_omega
      have hmi_sc : mi.toNat < s.scratch.score.length := by rw [hsc_len]; omega
      c0_hsteps_nogrp
      refine wp_join_group (fun (_mx', ()) m2 => m = m2)
        (fun _ ⟨mx', ⟨⟩⟩ m2 hm2 => by
          rcases hm2 with rfl
          c0_hsteps_nogrp
          exact ih1 (mx', mi + 1#64, ()) m (by dsimp only; omega)
            ⟨rfl, by rw [hmip1]; omega⟩)
        (fun J2 hJ2 => by
          c0_hsteps_nogrp
          · exact hJ2 (_, ()) m rfl
          · exact hJ2 (_, ()) m rfl)
    · refine wp_join_group (fun (resc, ()) m2 => m = m2)
        (fun _ ⟨resc, ⟨⟩⟩ m2 hm2 => by
          rcases hm2 with rfl
          c0_hsteps_nogrp
          refine wp_call_of_spec _ _ (hDiv _ _ _ _ fun factor => ?_)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (vi, ()) m3 => ∃ sc3 : List (BitVec 64),
              sc3.length = c.max_vars ∧ vi.toNat ≤ s.core.cur_vars ∧
              (FullMem c { s with scratch := { s.scratch with score := sc3 } } ⋆ R) m3)
            (fun (vi, ()) _ => s.core.cur_vars - vi.toNat)
            (fun J3 hJ3 => by
              c0_hsteps_nogrp
              exact hJ3 (0#64, ()) m ⟨s.scratch.score, hsc_len, Nat.zero_le _, hm⟩)
            (fun J3 (vi, ()) m3 ⟨sc3, hsc3, hvi_le, hm3⟩ ih3 => ?_)
          · rw [Blocks.get_here]
            c0_hsteps_nogrp
            · have hvi_lt : vi.toNat < s.core.cur_vars := by
                have h1 : vi.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
                rwa [bv64_ofNat_toNat hcv_lt64] at h1
              have hvip1 : (vi + 1#64).toNat = vi.toNat + 1 := by bv_omega
              have hvi_sc3 : vi.toNat < sc3.length := by rw [hsc3]; omega
              c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hMul _ _ _ _ fun nsc => ?_)
              c0_hsteps_nogrp
              exact ih3 (vi + 1#64, ()) _ (by dsimp only; omega)
                ⟨sc3.set vi.toNat nsc, by simp [hsc3], by rw [hvip1]; omega, by assumption⟩
            · refine wp_call_of_spec _ _ (hMul _ _ _ _ fun ninc => ?_)
              c0_hsteps_nogrp
              exact hQ () { s with scratch := { s.scratch with score := sc3, scinc := ninc } } _
                rfl (hlen_upd_scinc (hlen_upd_score hlen hsc3) ninc)
                (probePres_upd_score_scinc s sc3 ninc) (by assumption))
        (fun J2 hJ2 => by
          c0_hsteps_nogrp
          · exact hJ2 (_, ()) m rfl
          · exact hJ2 (_, ()) m rfl)

theorem full_rescale_wp (Γ : Env)
    (hRescaleM6 : Γ.Has "full_rescale_m6" fullRescaleSpec) :
    ∀ a m Q X, fullRescaleSpec a m Q X →
      Func.wp Γ full_rescale_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp full_rescale_body
  c0_hsteps_nogrp
  c0_call hRescaleM6
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  intro _ s' m' hcore' hlen' hpres' hm'
  c0_hsteps_nogrp
  exact hQ () s' m' hcore' hlen' hpres' hm'

theorem full_bump_var_wp (Γ : Env)
    (hAdd : Γ.Has "f64u_add" f64uPure2Spec)
    (hHeapUp : Γ.Has "full_heap_up" fullHeapUpSpec)
    (hRescale : Γ.Has "full_rescale" fullRescaleSpec) :
    ∀ a m Q X, fullBumpVarSpec a m Q X →
      Func.wp Γ full_bump_var_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hok := hlen.core_ok
  obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hsc_len := hsok.score_len
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hv_z : (BitVec.setWidth 64 v).toNat = v.toNat := zext_toNat v (by decide)
  unfold Func.wp full_bump_var_body
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (fullProbeScratchPres_refl s) hm
  · have hv_lt : v.toNat < s.core.cur_vars := by
      have h1 : (BitVec.setWidth 64 v).toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
        c0_bound
      rwa [hv_z, bv64_ofNat_toNat hcv_lt64] at h1
    have hv_sc : (BitVec.setWidth 64 v).toNat < s.scratch.score.length := by
      rw [hv_z, hsc_len]; omega
    c0_hsteps_nogrp
    refine wp_call_of_spec _ _ (hAdd _ _ _ _ fun nsc => ?_)
    c0_hsteps_nogrp
    let s1 : FullState := { s with scratch := { s.scratch with
      score := s.scratch.score.set v.toNat nsc } }
    have hlen1 : s1.LengthsOk c := hlen_upd_score hlen (by simp [hsc_len])
    have hpres1 : FullProbeScratchPres s s1 := probePres_upd_score s _
    have hm1 : (FullMem c s1 ⋆ R) m := by
      dsimp only [s1]
      rw [← hv_z]
      assumption
    refine wp_join_group
      (fun _ m2 => ∃ s2 : FullState, PreservesCoreSlice FullState.core s s2 ∧
        s2.LengthsOk c ∧ FullProbeScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ _ m2 ⟨s2, hcore2, hlen2, hpres2, hm2⟩ => by
        c0_hsteps_nogrp
        refine wp_join_group
          (fun _ m3 => ∃ s3 : FullState, PreservesCoreSlice FullState.core s s3 ∧
            s3.LengthsOk c ∧ FullProbeScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
          (fun _ _ m3 ⟨s3, hcore3, hlen3, hpres3, hm3⟩ => by
            c0_hsteps_nogrp
            exact hQ () s3 m3 hcore3 hlen3 hpres3 hm3)
          (fun J2 hJ2 => by
            c0_hsteps_nogrp
            · c0_call hRescale
              refine ⟨c, s2, R, rfl, hlen2, hm2, ?_⟩
              intro _ s3 m3 hcore3 hlen3 hpres3 hm3
              c0_hsteps_nogrp
              exact hJ2 () m3 ⟨s3, hcore2.trans hcore3, hlen3,
                fullProbeScratchPres_trans hpres2 hpres3, hm3⟩
            · exact hJ2 () m2 ⟨s2, hcore2, hlen2, hpres2, hm2⟩))
      (fun J1 hJ1 => by
        c0_hsteps_nogrp
        · c0_call hHeapUp
          exact ⟨c, s1, R, rfl, hlen1, hm1, fun _ s2 m2 hcore2 hlen2 hpres2 hm2 => by
            c0_hsteps_nogrp
            exact hJ1 () m2 ⟨s2, hcore2, hlen2,
              fullProbeScratchPres_trans hpres1 hpres2.1, hm2⟩⟩
        · exact hJ1 () m ⟨s1, rfl, hlen1, hpres1, hm1⟩)

theorem full_bump_decay_wp (Γ : Env)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hRescale : Γ.Has "full_rescale" fullRescaleSpec) :
    ∀ a m Q X, fullBumpDecaySpec a m Q X →
      Func.wp Γ full_bump_decay_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  unfold Func.wp full_bump_decay_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hMul _ _ _ _ fun ninc => ?_)
  c0_hsteps_nogrp
  let s1 : FullState := { s with scratch := { s.scratch with scinc := ninc } }
  have hlen1 : s1.LengthsOk c := hlen_upd_scinc hlen ninc
  have hpres1 : FullProbeScratchPres s s1 := probePres_upd_scinc s ninc
  refine wp_join_group
    (fun _ m2 => ∃ s2 : FullState, PreservesCoreSlice FullState.core s s2 ∧
      s2.LengthsOk c ∧ FullProbeScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ _ m2 ⟨s2, hcore2, hlen2, hpres2, hm2⟩ => by
      c0_hsteps_nogrp
      exact hQ () s2 m2 hcore2 hlen2 hpres2 hm2)
    (fun J1 hJ1 => by
      c0_hsteps_nogrp
      · c0_call hRescale
        refine ⟨c, s1, R, rfl, hlen1, by assumption, ?_⟩
        intro _ s2 m2 hcore2 hlen2 hpres2 hm2
        c0_hsteps_nogrp
        exact hJ1 () m2 ⟨s2, hcore2, hlen2, fullProbeScratchPres_trans hpres1 hpres2, hm2⟩
      · exact hJ1 () _ ⟨s1, rfl, hlen1, hpres1, by assumption⟩)

theorem full_queue_renumber_wp (Γ : Env) :
    ∀ a m Q X, fullQueueRenumberSpec a m Q X →
      Func.wp Γ full_queue_renumber_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hok := hlen.core_ok
  obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hqs_len := hsok.q_stamp_len
  obtain hqn_len := hsok.q_next_len
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  unfold Func.wp full_queue_renumber_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (st, cur, steps, ()) m1 => ∃ qs1 : List (BitVec 32),
      qs1.length = c.max_vars ∧ steps.toNat ≤ s.core.cur_vars ∧
      (FullMem c { s with scratch := { s.scratch with q_stamp := qs1 } } ⋆ R) m1)
    (fun (_st, _cur, steps, ()) _ => s.core.cur_vars - steps.toNat)
    (fun J1 hJ1 => by
      c0_hsteps_nogrp
      exact hJ1 (0#32, s.scratch.q_first, 0#64, ()) m
        ⟨s.scratch.q_stamp, hqs_len, Nat.zero_le _, hm⟩)
    (fun J1 (st, cur, steps, ()) m1 ⟨qs1, hqs1, hst_le, hm1⟩ ih1 => ?_)
  rw [Blocks.get_here]
  refine wp_join_group
    (fun _ m2 => ∃ qs2 : List (BitVec 32), qs2.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with q_stamp := qs2 } } ⋆ R) m2)
    (fun _ _ m2 ⟨qs2, hqs2, hm2⟩ => by
      c0_hsteps_nogrp
      refine wp_join_group
        (fun _ m3 => ∃ s3 : FullState, s3.core = s.core ∧ s3.LengthsOk c ∧
          FullProbeScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
        (fun _ _ m3 ⟨s3, hcore3, hlen3, hpres3, hm3⟩ => by
          c0_hsteps_nogrp
          exact hQ () s3 m3 hcore3 hlen3 hpres3 hm3)
        (fun J2 hJ2 => by
          let s2 : FullState := { s with scratch := { s.scratch with
            q_stamp := qs2, q_cur_stamp := BitVec.setWidth 64 st } }
          have hlen2 : s2.LengthsOk c :=
            hlen_upd_queue hlen hsok.q_prev_len hqn_len hqs2
          have hpres2 : FullProbeScratchPres s s2 :=
            probePres_upd_queue s _ _ qs2 _ _ _ _ _
          c0_hsteps_nogrp
          · have hqsi_lt : s.scratch.q_search_idx.toNat < s.core.cur_vars := by
              have h1 : s.scratch.q_search_idx.toNat <
                  (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
              rwa [bv64_ofNat_toNat hcv_lt64] at h1
            have hqsi_qs : s.scratch.q_search_idx.toNat < qs2.length := by rw [hqs2]; omega
            c0_hsteps_nogrp
            let s3 : FullState := { s with scratch := { s.scratch with
              q_stamp := qs2, q_cur_stamp := BitVec.setWidth 64 st,
              q_search_stamp := BitVec.setWidth 64
                (qs2[s.scratch.q_search_idx.toNat]'hqsi_qs) } }
            have hlen3 : s3.LengthsOk c :=
              hlen_upd_queue hlen hsok.q_prev_len hqn_len hqs2
            have hpres3 : FullProbeScratchPres s s3 :=
              probePres_upd_queue s _ _ qs2 _ _ _ _ _
            exact hJ2 () _ ⟨s3, rfl, hlen3, hpres3, by assumption⟩
          · exact hJ2 () _ ⟨s2, rfl, hlen2, hpres2, by assumption⟩))
    (fun Jb hJb => by
      c0_hsteps_nogrp
      · have hcur_lt : cur.toNat < s.core.cur_vars := by
          have h1 : cur.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
          rwa [bv64_ofNat_toNat hcv_lt64] at h1
        have hst_lt : steps.toNat < s.core.cur_vars := by
          have h1 : steps.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
          rwa [bv64_ofNat_toNat hcv_lt64] at h1
        have hstp1 : (steps + 1).toNat = steps.toNat + 1 := by bv_omega
        have hcur_qs : cur.toNat < qs1.length := by rw [hqs1]; omega
        have hcur_qn : cur.toNat < s.scratch.q_next.length := by rw [hqn_len]; omega
        c0_hsteps_nogrp
        exact ih1 _ _ (by dsimp only; rw [hstp1]; omega)
          ⟨qs1.set cur.toNat (st + 1#32), by simp [hqs1], by rw [hstp1]; omega, by assumption⟩
      · exact hJb () m1 ⟨qs1, hqs1, hm1⟩
      · exact hJb () m1 ⟨qs1, hqs1, hm1⟩)

private def QueueMtfState (c : FullCfg) (s s1 : FullState) (R : Mem 64 → Prop)
    (m1 : Mem 64) : Prop :=
  s1.core = s.core ∧ s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m1

private theorem queue_mtf_search_wp {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {v pv0 : BitVec 32} {m : Mem 64} {J1 : Cont []}
    (hv_lt : v.toNat < s.core.cur_vars)
    (hv_z : (BitVec.setWidth 64 v).toNat = v.toNat)
    (hlen : s.LengthsOk c)
    (hpv_def : pv0 = s.scratch.q_prev[v.toNat]'(by
      have := hlen.core_ok.cur_vars_le; rw [hlen.scratch_ok.q_prev_len]; omega))
    (hm : (FullMem c s ⋆ R) m)
    (hJ1 : ∀ qsi1 qss1 : BitVec 64, ∀ m1,
      let s1 : FullState := { s with scratch := { s.scratch with
        q_search_idx := qsi1, q_search_stamp := qss1 } }
      QueueMtfState c s s1 R m1 → J1 () m1) :
    let cv := BitVec.ofNat 64 s.core.cur_vars
    wp Γ Q X
      (.group (sig := [[]]) (fun _ => .cons (fun _ => .jump J1 ()) .nil) fun Js =>
        .let_ { sig := [i32], code := .zext 32 64, args := (.var pv0, ()) } fun p =>
        .let_ { sig := [i64, i64], code := .cmp .ult i64 .bool (by decide),
                args := (.var p.fst, .var cv, ()) } fun p =>
        .jnz (.var p.fst)
          (.let_ { sig := [i32], code := .zext 32 64, args := (.var pv0, ()) } fun p =>
           .let_ { sig := [i64, i64], code := .add i64,
                   args := (.var c.hdr, .imm 624, ()) } fun p1 =>
           .store (t := i64) (.var p.fst) (.var p1.fst)
           (.let_ { sig := [i32], code := .zext 32 64, args := (.var pv0, ()) } fun p =>
            .let_ { sig := [i64, i64], code := .mul i64, args := (.var p.fst, .imm 4, ()) } fun p =>
            .let_ { sig := [i64, i64], code := .add i64,
                    args := (.var c.pQStamp, .var p.fst, ()) } fun p =>
            .load i32 (.var p.fst) fun ld =>
            .let_ { sig := [i32], code := .zext 32 64, args := (.var ld, ()) } fun p =>
            .let_ { sig := [i64, i64], code := .add i64,
                    args := (.var c.hdr, .imm 632, ()) } fun p2 =>
            .store (t := i64) (.var p.fst) (.var p2.fst) (.jump Js.fst ())))
          (.let_ { sig := [i32], code := .zext 32 64, args := (.var v, ()) } fun p =>
           .let_ { sig := [i64, i64], code := .mul i64, args := (.var p.fst, .imm 4, ()) } fun p =>
           .let_ { sig := [i64, i64], code := .add i64, args := (.var c.pQNext, .var p.fst, ()) }
             fun p =>
           .load i32 (.var p.fst) fun nv0 =>
           .group (sig := [[]]) (fun _ => .cons (fun _ => .jump Js.fst ()) .nil) fun Js1 =>
           .let_ { sig := [i32], code := .zext 32 64, args := (.var nv0, ()) } fun p =>
           .let_ { sig := [i64, i64], code := .cmp .ult i64 .bool (by decide),
                   args := (.var p.fst, .var cv, ()) } fun p =>
           .jnz (.var p.fst)
             (.let_ { sig := [i32], code := .zext 32 64, args := (.var nv0, ()) } fun p =>
              .let_ { sig := [i64, i64], code := .add i64,
                      args := (.var c.hdr, .imm 624, ()) } fun p1 =>
              .store (t := i64) (.var p.fst) (.var p1.fst)
              (.let_ { sig := [i32], code := .zext 32 64, args := (.var nv0, ()) } fun p =>
               .let_ { sig := [i64, i64], code := .mul i64, args := (.var p.fst, .imm 4, ()) }
                 fun p =>
               .let_ { sig := [i64, i64], code := .add i64,
                       args := (.var c.pQStamp, .var p.fst, ()) } fun p =>
               .load i32 (.var p.fst) fun ld =>
               .let_ { sig := [i32], code := .zext 32 64, args := (.var ld, ()) } fun p =>
               .let_ { sig := [i64, i64], code := .add i64,
                       args := (.var c.hdr, .imm 632, ()) } fun p2 =>
               .store (t := i64) (.var p.fst) (.var p2.fst) (.jump Js1.fst ())))
             (.jump Js1.fst ()))) m := by
  have hcv_le := hlen.core_ok.cur_vars_le
  have hqs_len := hlen.scratch_ok.q_stamp_len
  have hqp_len := hlen.scratch_ok.q_prev_len
  have hqn_len := hlen.scratch_ok.q_next_len
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by
    unfold Ref.dimacsBound at hmaxv; omega
  subst hpv_def
  refine wp_join_group
    (fun _ m1 => ∃ qsi1 qss1 : BitVec 64,
      QueueMtfState c s { s with scratch := { s.scratch with
        q_search_idx := qsi1, q_search_stamp := qss1 } } R m1)
    (fun _ _ m1 ⟨qsi1, qss1, hm1⟩ => by
      c0_hsteps_nogrp
      exact hJ1 qsi1 qss1 m1 hm1)
    (fun _ hJs => by
      c0_hsteps_nogrp
      · have hpv_lt : (s.scratch.q_prev[v.toNat]'(by rw [hqp_len]; omega)).toNat <
            s.core.cur_vars := by
          have h1 : (BitVec.setWidth 64
              (s.scratch.q_prev[v.toNat]'(by rw [hqp_len]; omega))).toNat <
              (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
          rw [zext_toNat _ (by decide), bv64_ofNat_toNat hcv_lt64] at h1
          exact h1
        have hpv_qs : (BitVec.setWidth 64
            (s.scratch.q_prev[v.toNat]'(by rw [hqp_len]; omega))).toNat <
            s.scratch.q_stamp.length := by
          rw [zext_toNat _ (by decide), hqs_len]; omega
        c0_hsteps_nogrp
        let qsi1 := BitVec.setWidth 64 (s.scratch.q_prev[v.toNat]'(by rw [hqp_len]; omega))
        let qss1 := BitVec.setWidth 64 (s.scratch.q_stamp[qsi1.toNat]'(by
          rw [hqs_len]; dsimp [qsi1]; rw [zext_toNat _ (by decide)]; omega))
        exact hJs () _ ⟨qsi1, qss1, rfl,
          hlen_upd_queue hlen hqp_len hqn_len hqs_len,
          probePres_upd_queue s _ _ _ _ _ _ _ _, by dsimp [qsi1, qss1]; assumption⟩
      · have hv_qn : (BitVec.setWidth 64 v).toNat < s.scratch.q_next.length := by
          rw [hv_z, hqn_len]; omega
        c0_hsteps_nogrp
        refine wp_join_group
          (fun _ m1 => ∃ qsi1 qss1 : BitVec 64,
            QueueMtfState c s { s with scratch := { s.scratch with
              q_search_idx := qsi1, q_search_stamp := qss1 } } R m1)
          (fun _ _ m1 ⟨qsi1, qss1, hm1⟩ => by
            c0_hsteps_nogrp
            exact hJs () m1 ⟨qsi1, qss1, hm1⟩)
          (fun _ hJs1 => by
            c0_hsteps_nogrp
            · have hnv_lt : (s.scratch.q_next[v.toNat]'(by rw [hqn_len]; omega)).toNat <
                  s.core.cur_vars := by
                have h1 : (BitVec.setWidth 64
                    (s.scratch.q_next[v.toNat]'(by rw [hqn_len]; omega))).toNat <
                    (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
                rw [zext_toNat _ (by decide), bv64_ofNat_toNat hcv_lt64] at h1
                exact h1
              have hnv_qs : (BitVec.setWidth 64
                  (s.scratch.q_next[v.toNat]'(by rw [hqn_len]; omega))).toNat <
                  s.scratch.q_stamp.length := by
                rw [zext_toNat _ (by decide), hqs_len]; omega
              c0_hsteps_nogrp
              let qsi1 := BitVec.setWidth 64
                (s.scratch.q_next[v.toNat]'(by rw [hqn_len]; omega))
              let qss1 := BitVec.setWidth 64 (s.scratch.q_stamp[qsi1.toNat]'(by
                rw [hqs_len]; dsimp [qsi1]; rw [zext_toNat _ (by decide)]; omega))
              exact hJs1 () _ ⟨qsi1, qss1, rfl,
                hlen_upd_queue hlen hqp_len hqn_len hqs_len,
                probePres_upd_queue s _ _ _ _ _ _ _ _, by dsimp [qsi1, qss1]; assumption⟩
            · exact hJs1 () m ⟨s.scratch.q_search_idx, s.scratch.q_search_stamp,
                rfl, hlen, fullProbeScratchPres_refl s, hm⟩))

theorem full_queue_mtf_wp (Γ : Env)
    (hRenumber : Γ.Has "full_queue_renumber" fullQueueRenumberSpec) :
    ∀ a m Q X, fullQueueMtfSpec a m Q X →
      Func.wp Γ full_queue_mtf_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hok := hlen.core_ok
  obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hval_len := hok.vals_len
  obtain hqp_len := hsok.q_prev_len
  obtain hqn_len := hsok.q_next_len
  obtain hqs_len := hsok.q_stamp_len
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hv_z : (BitVec.setWidth 64 v).toNat = v.toNat := zext_toNat v (by decide)
  unfold Func.wp full_queue_mtf_body
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (fullProbeScratchPres_refl s) hm
  · exact hQ () s m rfl hlen (fullProbeScratchPres_refl s) hm
  · have hv_lt : v.toNat < s.core.cur_vars := by
      have h1 : (BitVec.setWidth 64 v).toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
        c0_bound
      rwa [hv_z, bv64_ofNat_toNat hcv_lt64] at h1
    have hv2_lt : ((BitVec.setWidth 64 v) <<< (1 : Nat)).toNat < s.core.vals.length := by
      rw [bv64_shl1_nat (by rw [hv_z]; omega), hv_z, hval_len]; omega
    have hv_qp : v.toNat < s.scratch.q_prev.length := by rw [hqp_len]; omega
    have hv_qn : v.toNat < s.scratch.q_next.length := by rw [hqn_len]; omega
    have hv_qs : v.toNat < s.scratch.q_stamp.length := by rw [hqs_len]; omega
    refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, QueueMtfState c s s1 R m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩ => by
        have hqp1_s : s1.scratch.q_prev.length = c.max_vars := hlen1.scratch_ok.q_prev_len
        have hqn1_s : s1.scratch.q_next.length = c.max_vars := hlen1.scratch_ok.q_next_len
        have hqs1_s : s1.scratch.q_stamp.length = c.max_vars := hlen1.scratch_ok.q_stamp_len
        have hv_qp1 : (BitVec.setWidth 64 v).toNat < s1.scratch.q_prev.length := by
          rw [hv_z, hqp1_s]; omega
        have hv_qn1 : (BitVec.setWidth 64 v).toNat < s1.scratch.q_next.length := by
          rw [hv_z, hqn1_s]; omega
        c0_hsteps_nogrp
        let pv := s1.scratch.q_prev[v.toNat]'(by rw [hqp1_s]; omega)
        let nv := s1.scratch.q_next[v.toNat]'(by rw [hqn1_s]; omega)
        refine wp_join_group (fun _ m2 => ∃ s2 : FullState, QueueMtfState c s s2 R m2)
          (fun _ _ m2 ⟨s2, hcore2, hlen2, hpres2, hm2⟩ => by
            c0_hsteps_nogrp
            refine wp_join_group (fun _ m3 => ∃ s3 : FullState, QueueMtfState c s s3 R m3)
              (fun _ _ m3 ⟨s3, hcore3, hlen3, hpres3, hm3⟩ => by
                c0_hsteps_nogrp
                have hv_qp3 : (BitVec.setWidth 64 v).toNat < s3.scratch.q_prev.length := by
                  rw [hv_z, hlen3.scratch_ok.q_prev_len]; omega
                c0_hsteps_nogrp
                refine wp_join_group (fun _ m4 => ∃ s4 : FullState, QueueMtfState c s s4 R m4)
                  (fun _ _ m4 ⟨s4, hcore4, hlen4, hpres4, hm4⟩ => by
                    c0_hsteps_nogrp
                    refine wp_join_group (fun _ m5 => ∃ s5 : FullState, QueueMtfState c s s5 R m5)
                      (fun _ _ m5 ⟨s5, hcore5, hlen5, hpres5, hm5⟩ => by
                        c0_hsteps_nogrp
                        refine wp_join_group
                          (fun _ m6 => ∃ s6 : FullState, QueueMtfState c s s6 R m6)
                          (fun _ _ m6 ⟨s6, hcore6, hlen6, hpres6, hm6⟩ => by
                            c0_hsteps_nogrp
                            exact hQ () s6 m6 hcore6 hlen6 hpres6 hm6)
                          (fun _ hJ6 => by
                            have hv2_lt5 : ((BitVec.setWidth 64 v) <<< (1 : Nat)).toNat <
                                s5.core.vals.length := by
                              rw [hcore5]; exact hv2_lt
                            have hqs5 : s5.scratch.q_stamp.length = c.max_vars :=
                              hlen5.scratch_ok.q_stamp_len
                            c0_hsteps_nogrp
                            · have hv_qs5 : (BitVec.setWidth 64 v).toNat <
                                  s5.scratch.q_stamp.length := by
                                rw [hv_z, hqs5]; omega
                              c0_hsteps_nogrp
                              let s6 : FullState := { s5 with scratch := { s5.scratch with
                                q_search_idx := BitVec.setWidth 64 v,
                                q_search_stamp := BitVec.setWidth 64
                                  (s5.scratch.q_stamp[v.toNat]'(by rw [hqs5]; omega)) } }
                              exact hJ6 () _ ⟨s6, hcore5,
                                hlen_upd_queue hlen5 hlen5.scratch_ok.q_prev_len
                                  hlen5.scratch_ok.q_next_len hqs5,
                                fullProbeScratchPres_trans hpres5
                                  (probePres_upd_queue s5 _ _ _ _ _ _ _ _),
                                by assumption⟩
                            · exact hJ6 () m5 ⟨s5, hcore5, hlen5, hpres5, hm5⟩))
                      (fun _ hJst => by
                        c0_hsteps_nogrp
                        · c0_call hRenumber
                          refine ⟨c, s4, R, rfl, hlen4, hm4,
                            fun _ s5 m5 hcore5 hlen5 hpres5 hm5 => ?_⟩
                          c0_hsteps_nogrp
                          exact hJst () m5 ⟨s5, by
                            dsimp only [PreservesCoreSlice, fullSafetySlice] at hcore5
                            exact hcore5.trans hcore4,
                            hlen5, fullProbeScratchPres_trans hpres4 hpres5, hm5⟩
                        · have hqs4 : s4.scratch.q_stamp.length = c.max_vars :=
                            hlen4.scratch_ok.q_stamp_len
                          have hv_qs4 : (BitVec.setWidth 64 v).toNat <
                              s4.scratch.q_stamp.length := by
                            rw [hv_z, hqs4]; omega
                          c0_hsteps_nogrp
                          let s5 : FullState := { s4 with scratch := { s4.scratch with
                            q_cur_stamp := s4.scratch.q_cur_stamp + 1#64,
                            q_stamp := s4.scratch.q_stamp.set v.toNat
                              ((s4.scratch.q_cur_stamp + 1#64).setWidth 32) } }
                          exact hJst () _ ⟨s5, hcore4,
                            hlen_upd_queue hlen4 hlen4.scratch_ok.q_prev_len
                              hlen4.scratch_ok.q_next_len (by simp [hqs4]),
                            fullProbeScratchPres_trans hpres4
                              (probePres_upd_queue s4 _ _ _ _ _ _ _ _),
                            by assumption⟩))
                  (fun _ hJold => by
                    let ql3 := s3.scratch.q_last.setWidth 32
                    let qp4 := s3.scratch.q_prev.set v.toNat ql3
                    have hqp4 : qp4.length = c.max_vars := by
                      simp [qp4, hlen3.scratch_ok.q_prev_len]
                    have hqn3 : s3.scratch.q_next.length = c.max_vars :=
                      hlen3.scratch_ok.q_next_len
                    c0_hsteps_nogrp
                    · let s4 : FullState := { s3 with scratch := { s3.scratch with
                        q_prev := qp4, q_last := BitVec.setWidth 64 v,
                        q_first := BitVec.setWidth 64 v } }
                      exact hJold () _ ⟨s4, hcore3,
                        hlen_upd_queue hlen3 hqp4 hqn3 hlen3.scratch_ok.q_stamp_len,
                        fullProbeScratchPres_trans hpres3
                          (probePres_upd_queue s3 qp4 _ _ _ _ _ _ _),
                        by assumption⟩
                    · have hol_lt : ql3.toNat < s.core.cur_vars := by
                        have h1 : (BitVec.setWidth 64 ql3).toNat <
                            (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                          dsimp only [ql3]; c0_bound
                        rw [zext_toNat _ (by decide), bv64_ofNat_toNat hcv_lt64] at h1
                        dsimp [ql3] at *; exact h1
                      have hol_qn : (BitVec.setWidth 64 ql3).toNat < s3.scratch.q_next.length := by
                        rw [zext_toNat _ (by decide), hqn3]; omega
                      c0_hsteps_nogrp
                      let s4 : FullState := { s3 with scratch := { s3.scratch with
                        q_prev := qp4, q_last := BitVec.setWidth 64 v,
                        q_next := s3.scratch.q_next.set (BitVec.setWidth 64 ql3).toNat v } }
                      exact hJold () _ ⟨s4, hcore3,
                        hlen_upd_queue hlen3 hqp4 (by simp [hqn3]) hlen3.scratch_ok.q_stamp_len,
                        fullProbeScratchPres_trans hpres3
                          (probePres_upd_queue s3 qp4 _ _ _ _ _ _ _),
                        by assumption⟩))
              (fun _ hJnv => by
                c0_hsteps_nogrp
                · let s3 : FullState := { s2 with scratch := { s2.scratch with
                    q_last := BitVec.setWidth 64 pv } }
                  exact hJnv () _ ⟨s3, hcore2, hlen_upd_qlast hlen2 _,
                    fullProbeScratchPres_trans hpres2
                      (probePres_upd_queue s2 _ _ _ _ _ _ _ _),
                    by assumption⟩
                · have hnv_lt : nv.toNat < s.core.cur_vars := by
                    have h1 : (BitVec.setWidth 64 nv).toNat <
                        (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                      dsimp only [nv]; c0_bound
                    rw [zext_toNat _ (by decide), bv64_ofNat_toNat hcv_lt64] at h1
                    dsimp [nv] at *; exact h1
                  have hnv_qp : (BitVec.setWidth 64 nv).toNat < s2.scratch.q_prev.length := by
                    rw [zext_toNat _ (by decide), hlen2.scratch_ok.q_prev_len]; omega
                  c0_hsteps_nogrp
                  let s3 : FullState := { s2 with scratch := { s2.scratch with
                    q_prev := s2.scratch.q_prev.set (BitVec.setWidth 64 nv).toNat pv } }
                  exact hJnv () _ ⟨s3, hcore2,
                    hlen_upd_qprev hlen2 (by simp [hlen2.scratch_ok.q_prev_len]),
                    fullProbeScratchPres_trans hpres2
                      (probePres_upd_queue s2 _ _ _ _ _ _ _ _),
                    by assumption⟩))
          (fun _ hJpv => by
            let s1a : FullState := { s1 with scratch := { s1.scratch with
              q_prev := s1.scratch.q_prev.set v.toNat 0xFFFFFFFF#32,
              q_next := s1.scratch.q_next.set v.toNat 0xFFFFFFFF#32 } }
            have hqp1a : s1a.scratch.q_prev.length = c.max_vars := by simp [s1a, hqp1_s]
            have hqn1a : s1a.scratch.q_next.length = c.max_vars := by simp [s1a, hqn1_s]
            have hlen1a : s1a.LengthsOk c :=
              hlen_upd_queue hlen1 hqp1a hqn1a hqs1_s
            have hpres1a : FullProbeScratchPres s s1a :=
              fullProbeScratchPres_trans hpres1 (probePres_upd_queue s1 _ _ _ _ _ _ _ _)
            c0_hsteps_nogrp
            · let s2 : FullState := { s1a with scratch := { s1a.scratch with
                q_first := BitVec.setWidth 64 nv } }
              exact hJpv () _ ⟨s2, hcore1, hlen_upd_qfirst hlen1a _,
                fullProbeScratchPres_trans hpres1a
                  (probePres_upd_queue s1a _ _ _ _ _ _ _ _),
                by assumption⟩
            · have hpv_lt : pv.toNat < s.core.cur_vars := by
                have h1 : (BitVec.setWidth 64 pv).toNat <
                    (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                  dsimp only [pv]; c0_bound
                rw [zext_toNat _ (by decide), bv64_ofNat_toNat hcv_lt64] at h1
                dsimp [pv] at *; exact h1
              have hpv_qn : (BitVec.setWidth 64 pv).toNat < s1a.scratch.q_next.length := by
                rw [zext_toNat _ (by decide), hqn1a]; omega
              c0_hsteps_nogrp
              let s2 : FullState := { s1a with scratch := { s1a.scratch with
                q_next := s1a.scratch.q_next.set (BitVec.setWidth 64 pv).toNat nv } }
              exact hJpv () _ ⟨s2, hcore1,
                hlen_upd_qnext hlen1a (by simp [s1a, hqn1_s]),
                fullProbeScratchPres_trans hpres1a
                  (probePres_upd_queue s1a _ _ _ _ _ _ _ _),
                by assumption⟩))
      (fun J0 hJ0 => by
        c0_hsteps_nogrp
        · have hv_qp0 : (BitVec.setWidth 64 v).toNat < s.scratch.q_prev.length := by
            rw [hv_z, hqp_len]; omega
          exact queue_mtf_search_wp hv_lt hv_z hlen rfl hm
            (fun qsi1 qss1 m1 hm1 => hJ0 () m1 ⟨_, hm1⟩)
        · exact hJ0 () m ⟨s, rfl, hlen, fullProbeScratchPres_refl s, hm⟩
        · exact hJ0 () m ⟨s, rfl, hlen, fullProbeScratchPres_refl s, hm⟩)

end

end LeanQbe.T.Examples.Kissat.Proof.Bump
