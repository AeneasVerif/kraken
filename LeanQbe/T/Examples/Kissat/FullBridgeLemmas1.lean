module

public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullMinLemmas
import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Parts 1b–4 (`Stage 4`)

Bridges canonical `FullSpec2`/`FullSpec3` table entries across the first 4 shards (`26` fns):
- Part 1b (`FullHeurWalkLemmas`, #12–17, `6` fns): `full_queue_renumber`, `full_queue_mtf`,
  `full_tick_rel`, `full_ema_update`, `full_save_target_best`, `full_recompute_tiers`.
- Part 2 (`FullPropDecLemmas`, `9` fns): `full_find_repl`, `full_assign_level`, `full_prop_lit`,
  `full_propagate_ignore`, `full_propagate`, `full_decide`, `full_warmup`, `full_rephase`,
  `full_restart`.
- Part 3 (`FullMinLemmas`, `8` fns): `full_tmp_less`, `full_min_mark`, `full_sort_tmp_sift`,
  `full_sort_tmp`, `full_min_lit`, `full_shrink_lower`, `full_shrink_blk`, `full_min_shrink`.
- Part 4 (`FullDimacsBodyLemmas`, `3` fns): `full_skip_cl`, `full_ingest_cl`, `full_parse_body`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## Part 1b: `FullHeurWalkLemmas` (#12–17) -/

section Part1b

open scoped FullArenaTactics FullHeurWalkTactics
open FullBridgeHelpers

theorem full_queue_renumber_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullQueueRenumberSpec a m Q X → Func.wp Γ full_queue_renumber_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hcv_le := hok.cur_vars_le
  c0_steps
  refine wp_loop_safety_slice_pure (ts := [i32, i64, i64]) (fullSafetySlice c) s R
    (fun s1 (_st, _cur, steps, ()) => steps.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s1)
    (fun (_st, _cur, steps, ()) => s.core.cur_vars - steps.toNat)
    (fun J hLoop => ?_)
    (fun J s1 (st, cur, steps, ()) m1 hcore1 hlen1 ⟨hsle, hpres1⟩ hm1 hLoop1 => ?_)
  · c0_steps; exact hLoop s _ m hm rfl hlen ⟨by simp, probePres_refl s⟩
  · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
    have hceq1 : s1.core = s.core := hcore1
    obtain hsok1 := hlen1.scratch_ok
    obtain hqnl1 := hsok1.q_next_len; obtain hqsl1 := hsok1.q_stamp_len
    have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
      bv64_ofNat_toNat (by omega)
    c0_clean; c0_steps
    · have hcur_lt : cur.toNat < s.core.cur_vars := by
        have h1 : cur.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
          rw [hceq1] at *; c0_bound
        omega
      have hst_lt : steps.toNat < s.core.cur_vars := by
        have h1 : steps.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
          rw [hceq1] at *; c0_bound
        omega
      have hstp1 : (steps + 1).toNat = steps.toNat + 1 := by bv_omega
      c0_clean; c0_steps
      refine hLoop1 _ (_, _, steps + 1, ()) m hm (by dsimp only; omega) rfl ?_
        ⟨by dsimp only; omega, hpres1⟩
      exact hlen_upd_q hlen1 hsok1.q_prev_len hqnl1 (by simp [hqsl1])
    all_goals
      refine hQ () _ m ?_ ?_ ?_ hm <;>
        first
        | exact hcore1
        | exact hlen_upd_q hlen1 hsok1.q_prev_len hqnl1 hqsl1
        | exact hpres1

theorem full_queue_mtf_bridge_wp (Γ : Env)
    (hRen : ∀ a m Q X, fullQueueRenumberSpec a m Q X →
      Γ "full_queue_renumber" [i64] [] a m Q X) :
    ∀ a m Q X, fullQueueMtfSpec a m Q X → Func.wp Γ full_queue_mtf_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le; obtain hvl := hok.vals_len
  obtain hqpl := hsok.q_prev_len; obtain hqnl := hsok.q_next_len; obtain hqsl := hsok.q_stamp_len
  c0_to_group
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · have hv_lt : v.toNat < s.core.cur_vars := by
      have h1 : v.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
      have := bv64_ofNat_toNat (n := s.core.cur_vars) (by omega); omega
    have hv64 : (BitVec.setWidth 64 v).toNat < s.core.cur_vars := by
      rw [zext_toNat _ (by decide)]; exact hv_lt
    have hv2 : (v.setWidth 64 <<< (1 : Nat)).toNat < s.core.vals.length := by
      rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq, hvl]; omega
    c0_clean; c0_to_group
    refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩ => ?_) ?_
    · have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok
      obtain hqpl1 := hsok1.q_prev_len; obtain hqnl1 := hsok1.q_next_len
      c0_to_group
      refine wp_join_group
        (fun _ m2 => ∃ s2 : FullState, PreservesCoreSlice FullState.core s s2 ∧
          s2.LengthsOk c ∧ FullProbeScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ _ m2 ⟨s2, hcore2, hlen2, hpres2, hm2⟩ => ?_) ?_
      · have hceq2 : s2.core = s.core := hcore2
        obtain hsok2 := hlen2.scratch_ok
        obtain hqpl2 := hsok2.q_prev_len; obtain hqnl2 := hsok2.q_next_len
        c0_to_group
        refine wp_join_group
          (fun _ m3 => ∃ s3 : FullState, PreservesCoreSlice FullState.core s s3 ∧
            s3.LengthsOk c ∧ FullProbeScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
          (fun _ _ m3 ⟨s3, hcore3, hlen3, hpres3, hm3⟩ => ?_) ?_
        · have hceq3 : s3.core = s.core := hcore3
          obtain hsok3 := hlen3.scratch_ok
          obtain hqpl3 := hsok3.q_prev_len; obtain hqnl3 := hsok3.q_next_len
          c0_to_group
          refine wp_join_group
            (fun _ m4 => ∃ s4 : FullState, PreservesCoreSlice FullState.core s s4 ∧
              s4.LengthsOk c ∧ FullProbeScratchPres s s4 ∧ (FullMem c s4 ⋆ R) m4)
            (fun _ _ m4 ⟨s4, hcore4, hlen4, hpres4, hm4⟩ => ?_) ?_
          · have hceq4 : s4.core = s.core := hcore4
            obtain hsok4 := hlen4.scratch_ok
            obtain hqnl4 := hsok4.q_next_len; obtain hqsl4 := hsok4.q_stamp_len
            c0_to_group
            refine wp_join_group
              (fun _ m5 => ∃ s5 : FullState, PreservesCoreSlice FullState.core s s5 ∧
                s5.LengthsOk c ∧ FullProbeScratchPres s s5 ∧ (FullMem c s5 ⋆ R) m5)
              (fun _ _ m5 ⟨s5, hcore5, hlen5, hpres5, hm5⟩ => ?_) ?_
            · have hceq5 : s5.core = s.core := hcore5
              obtain hsok5 := hlen5.scratch_ok
              obtain hqsl5 := hsok5.q_stamp_len
              have hv2_5 : (v.setWidth 64 <<< (1 : Nat)).toNat < s5.core.vals.length := by
                rw [hceq5]; exact hv2
              c0_clean; c0_steps
              · refine hQ () _ m ?_ ?_ ?_ hm
                · exact hcore5
                · exact hlen_upd_q hlen5 hsok5.q_prev_len hsok5.q_next_len hqsl5
                · exact hpres5
              · exact hQ () s5 m5 hcore5 hlen5 hpres5 hm5
            · intro J5 hJ5; c0_steps
              · refine wp_safety_slice_call hRen (fun _ => True) trivial rfl hlen4 hm4
                  fun _ s5 m5 hcore5 hlen5 _ hpres5 hm5 => ?_
                dsimp only [fullSafetySlice] at hm5 hlen5
                c0_steps
                exact hJ5 () m5 ⟨s5, hcore4.trans hcore5, hlen5,
                  probePres_trans hpres4 hpres5, hm5⟩
              · refine hJ5 () m ⟨_, ?_, ?_, ?_, hm⟩
                · exact hcore4
                · exact hlen_upd_q hlen4 hsok4.q_prev_len hqnl4 (by simp [hqsl4])
                · exact hpres4
          · intro J4 hJ4; c0_steps
            all_goals
              refine hJ4 () m ⟨_, ?_, ?_, ?_, hm⟩
              · exact hcore3
              · exact hlen_upd_q hlen3 (by simp [hqpl3]) (by simp [hqnl3]) hsok3.q_stamp_len
              · exact hpres3
        · intro J3 hJ3; c0_steps
          · refine hJ3 () m ⟨_, ?_, ?_, ?_, hm⟩
            · exact hcore2
            · exact hlen_upd_q hlen2 hqpl2 hqnl2 hsok2.q_stamp_len
            · exact hpres2
          · have hv_eq : (BitVec.setWidth 64 v).toNat = v.toNat := zext_toNat v (by decide)
            have hnv_lt : (BitVec.setWidth 64 (s1.scratch.q_next[(BitVec.setWidth 64 v).toNat]'(
                by rw [hqnl1]; omega))).toNat < s2.scratch.q_prev.length := by
              have h1 : (s1.scratch.q_next[(BitVec.setWidth 64 v).toNat]'(
                  by rw [hqnl1]; omega)).toNat < s.core.cur_vars % 2 ^ 64 := by
                simp only [hv_eq]; omega
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
            c0_clean; c0_steps
            refine hJ3 () m ⟨_, ?_, ?_, ?_, hm⟩
            · exact hcore2
            · exact hlen_upd_q hlen2 (by simp [hqpl2]) hqnl2 hsok2.q_stamp_len
            · exact hpres2
      · intro J2 hJ2; c0_steps
        · refine hJ2 () m ⟨_, ?_, ?_, ?_, hm⟩
          · exact hcore1
          · exact hlen_upd_q hlen1 (by simp [hqpl1]) (by simp [hqnl1]) hsok1.q_stamp_len
          · exact hpres1
        · have hpv_lt : (BitVec.setWidth 64 (s1.scratch.q_prev[(BitVec.setWidth 64 v).toNat]'(
              by rw [hqpl1]; omega))).toNat < s1.scratch.q_next.length := by
            have h1 : (s1.scratch.q_prev[(BitVec.setWidth 64 v).toNat]'(
                by rw [hqpl1]; omega)).toNat < s1.core.cur_vars % 2 ^ 64 := by
              rw [hceq1]; c0_bound
            rw [hceq1] at h1
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
            rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
          c0_clean; c0_steps
          refine hJ2 () m ⟨_, ?_, ?_, ?_, hm⟩
          · exact hcore1
          · exact hlen_upd_q hlen1 (by simp [hqpl1]) (by simp [hqnl1]) hsok1.q_stamp_len
          · exact hpres1
    · intro J1 hJ1; c0_steps
      all_goals
        refine hJ1 () m ⟨_, ?_, ?_, ?_, hm⟩ <;>
          first
          | exact rfl
          | exact hlen_upd_q hlen hqpl hqnl hqsl
          | exact probePres_refl s

theorem full_tick_rel_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullTickRelSpec a m Q X → Func.wp Γ full_tick_rel_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  c0_to_group
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩ => ?_) ?_
    · c0_to_group
      · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1
      · refine wp_join_group (fun _ m2 => m1 = m2) (fun _ _ m2 hm2 => ?_) ?_
        · rcases hm2 with rfl; c0_to_group
          refine wp_join_group (fun _ m3 => m1 = m3) (fun _ _ m3 hm3 => ?_) ?_
          · rcases hm3 with rfl; c0_to_group
            refine wp_join_group (fun _ m4 => m1 = m4) (fun _ _ m4 hm4 => ?_) ?_
            · rcases hm4 with rfl; c0_steps
              all_goals
                refine hQ () _ m ?_ ?_ ?_ hm
                · exact hcore1
                · exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                · exact hpres1
            · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
          · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
        · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
    · intro Jm hJm; c0_steps
      · refine hJm _ _ ⟨_, ?_, ?_, ?_, hm⟩
        · exact rfl
        · exact hlen_upd_scalar hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        · exact probePres_refl s
      · exact hJm _ _ ⟨s, rfl, hlen, probePres_refl s, hm⟩

theorem full_ema_update_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullEmaUpdateSpec a m Q X → Func.wp Γ full_ema_update_body a m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  c0_to_group
  refine wp_join_group (fun _ m1 => m = m1) (fun _ _ m1 hm1 => ?_) ?_
  · rcases hm1 with rfl; c0_to_group
    refine wp_join_group (fun _ m2 => m = m2) (fun _ _ m2 hm2 => ?_) ?_
    · rcases hm2 with rfl; c0_to_group
      refine wp_join_group
        (fun _ m3 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
          s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m3)
        (fun _ _ m3 ⟨s1, hcore1, hlen1, hpres1, hm3⟩ => ?_) ?_
      · c0_to_group
        refine wp_join_group (fun _ m4 => m3 = m4) (fun _ _ m4 hm4 => ?_) ?_
        · rcases hm4 with rfl; c0_steps
          all_goals
            refine hQ () _ m ?_ ?_ ?_ hm
            · exact hcore1
            · exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            · exact hpres1
        · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
      · intro Jm hJm; c0_steps
        all_goals
          refine hJm _ _ ⟨_, ?_, ?_, ?_, hm⟩
          · exact rfl
          · exact hlen_upd_scalar hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          · exact probePres_refl s
    · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
  · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl

theorem full_save_target_best_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Func.wp Γ full_save_target_best_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hcv_le := hok.cur_vars_le; obtain hvl := hok.vals_len
  c0_to_group
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.target_assigned,
      s.scratch.best_assigned, s.scratch.phases_target, s.scratch.phases_best, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.target_assigned,
      s.scratch.best_assigned, s.scratch.phases_target, s.scratch.phases_best, rfl⟩ hm
  · refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧
        (∃ ta' ba' pt' pb', s1.scratch = { s.scratch with
          target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb' }) ∧
        (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hpres1, ⟨ta1, ba1, pt1, pb1, hsc1⟩, hm1⟩ => ?_) ?_
    · rw [Blocks.get_here]
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok; obtain hpbl1 := hsok1.phases_best_len
      c0_clean; c0_steps
      · refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s1 R
          (fun s2 (k, ()) => k.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s1 s2 ∧
            ∃ ba' pb', s2.scratch = { s1.scratch with best_assigned := ba', phases_best := pb' })
          (fun (k, ()) => s.core.cur_vars - k.toNat)
          (fun J hLoop => ?_)
          (fun J s2 (k, ()) m2 hcore2 hlen2 ⟨hk2, hpres2, ba2, pb2, hsc2⟩ hm2 hLoop2 => ?_)
        · c0_steps
          refine hLoop _ (0#64, ()) m hm rfl ?_
            ⟨by simp, probePres_refl s1, _, s1.scratch.phases_best, rfl⟩
          exact hlen_upd_phases hlen1 hsok1.phases_target_len hpbl1
        · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
          have hceq2 : s2.core = s1.core := hcore2
          obtain hsok2 := hlen2.scratch_ok; obtain hpbl2 := hsok2.phases_best_len
          c0_clean; c0_steps
          · have hk_lt : k.toNat < s.core.cur_vars := by
              have h1 : k.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                rw [hceq2, hceq1] at *; c0_bound
              rw [bv64_ofNat_toNat (by omega)] at h1; exact h1
            have hk2_lt : (k <<< (1 : Nat)).toNat < s2.core.vals.length := by
              have hsh : (k <<< (1 : Nat)).toNat = 2 * k.toNat := by c0_bound
              rw [hsh, hceq2, hceq1, hvl]; omega
            have hkp1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
            c0_clean; c0_steps
            refine hLoop2 _ (k + 1, ()) m hm (by dsimp only; omega) rfl ?_
              ⟨by dsimp only; omega, hpres2, ba2, _, by dsimp only; rw [hsc2]⟩
            exact hlen_upd_phases hlen2 hsok2.phases_target_len (by simp [hpbl2])
          · exact hQ () s2 m2 (hcore1.trans hcore2) hlen2
              ⟨probePres_trans hpres1 hpres2, ta1, ba2, pt1, pb2, by rw [hsc2, hsc1]⟩ hm2
      · exact hQ () s1 m1 hcore1 hlen1 ⟨hpres1, ta1, ba1, pt1, pb1, hsc1⟩ hm1
    · intro J1 hJ1; c0_steps
      · obtain hsok := hlen.scratch_ok; obtain hptl := hsok.phases_target_len
        refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s R
          (fun s1 (k, ()) => k.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s1 ∧
            ∃ ta' pt', s1.scratch = { s.scratch with target_assigned := ta', phases_target := pt' })
          (fun (k, ()) => s.core.cur_vars - k.toNat)
          (fun J hLoop => ?_)
          (fun J s1 (k, ()) m1 hcore1 hlen1 ⟨hk1, hpres1, ta1, pt1, hsc1⟩ hm1 hLoop1 => ?_)
        · c0_steps
          refine hLoop _ (0#64, ()) m hm rfl ?_
            ⟨by simp, probePres_refl s, _, s.scratch.phases_target, rfl⟩
          exact hlen_upd_phases hlen hptl hsok.phases_best_len
        · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
          have hceq1 : s1.core = s.core := hcore1
          obtain hsok1 := hlen1.scratch_ok; obtain hptl1 := hsok1.phases_target_len
          c0_clean; c0_steps
          · have hk_lt : k.toNat < s.core.cur_vars := by
              have h1 : k.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                rw [hceq1] at *; c0_bound
              rw [bv64_ofNat_toNat (by omega)] at h1; exact h1
            have hk2_lt : (k <<< (1 : Nat)).toNat < s1.core.vals.length := by
              have hsh : (k <<< (1 : Nat)).toNat = 2 * k.toNat := by c0_bound
              rw [hsh, hceq1, hvl]; omega
            have hkp1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
            c0_clean; c0_steps
            refine hLoop1 _ (k + 1, ()) m hm (by dsimp only; omega) rfl ?_
              ⟨by dsimp only; omega, hpres1, ta1, _, by dsimp only; rw [hsc1]⟩
            exact hlen_upd_phases hlen1 (by simp [hptl1]) hsok1.phases_best_len
          · exact hJ1 () m1 ⟨s1, hcore1, hlen1, hpres1,
              ⟨ta1, s.scratch.best_assigned, pt1, s.scratch.phases_best, hsc1⟩, hm1⟩
      · exact hJ1 () m ⟨s, rfl, hlen, probePres_refl s,
          ⟨s.scratch.target_assigned, s.scratch.best_assigned, s.scratch.phases_target,
            s.scratch.phases_best, rfl⟩, hm⟩

theorem full_recompute_tiers_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullRecomputeTiersSpec a m Q X →
      Func.wp Γ full_recompute_tiers_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hsok := hlen.scratch_ok; obtain hgl := hsok.glue_used_len
  c0_steps
  refine wp_loop_safety_slice_pure (ts := [i64, i64]) (fullSafetySlice c) s R
    (fun s1 (_tot, g, ()) => g.toNat ≤ 64 ∧ FullProbeScratchPres s s1)
    (fun (_tot, g, ()) => 64 - g.toNat)
    (fun J hLoop => ?_)
    (fun J s1 (tot, g, ()) m1 hcore1 hlen1 ⟨hg1, hpres1⟩ hm1 hLoop1 => ?_)
  · c0_steps; exact hLoop s _ m hm rfl hlen ⟨by simp, probePres_refl s⟩
  · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
    obtain hsok1 := hlen1.scratch_ok; obtain hgl1 := hsok1.glue_used_len
    c0_clean; c0_steps
    · have hg_lt : g.toNat < 64 := by c0_bound
      have hgp1 : (g + 1).toNat = g.toNat + 1 := by bv_omega
      c0_clean; c0_steps
      exact hLoop1 _ (_, g + 1, ()) m1 hm1 (by dsimp only; omega) rfl hlen1
        ⟨by dsimp only; omega, hpres1⟩
    · refine wp_loop_inv
        (fun (g', _t1, _acc, _got1, ()) mL => g'.toNat ≤ 64 ∧ mL = m1)
        (fun (g', _t1, _acc, _got1, ()) _ => 64 - g'.toNat)
        (fun J2 hLoop2 => ?_) ?_
      · c0_steps; exact hLoop2 _ m1 ⟨by simp, rfl⟩
      · rintro J2 ⟨g', t1, acc, got1, ⟨⟩⟩ mL ⟨hg', rfl⟩ hLoop2
        rw [Blocks.get_here]; c0_clean; c0_split
        · have hg'_lt : g'.toNat < 64 := by c0_bound
          have hg'p1 : (g' + 1).toNat = g'.toNat + 1 := by bv_omega
          c0_clean; c0_steps
          all_goals first
          | (refine hLoop2 _ _ ?_ ⟨?_, rfl⟩ <;> ((try dsimp only); omega))
          | (refine hQ () _ m ?_ ?_ ?_ hm <;>
              first
              | exact hcore1
              | exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              | exact hpres1)
        · c0_steps
          all_goals
            refine hQ () _ m ?_ ?_ ?_ hm <;>
              first
              | exact hcore1
              | exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              | exact hpres1
    · refine hQ () _ m ?_ ?_ ?_ hm
      · exact hcore1
      · exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact hpres1

end Part1b

/-! ## Part 2: `FullPropDecLemmas` (`4` fns) -/

section Part2

open scoped FullArenaTactics FullPropDecTactics

local macro "fp_nojoin" : tactic =>
  `(tactic| repeat (any_goals ((fail_if_success (apply wp_unroll_group)); fp_step)))

theorem full_find_repl_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullFindReplSpec a m Q X → Func.wp Γ full_find_repl_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hc3, hsz, hfit, hm, hNone, hSome⟩
  apply full_find_repl_wp Γ
  refine ⟨c, s, R, rfl, hlen, hc3, hsz, hfit, hm, ?_, hSome⟩
  intro hbad
  exact hNone fun k hk1 hk2 => hbad k hk1 hk2

theorem full_assign_level_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullAssignLevelSpec a m Q X → Func.wp Γ full_assign_level_body a m Q X :=
  full_assign_level_wp Γ

private theorem fullConflOkW_to_conflict {F_cur : List (List Nat)} {s : FullState}
    (h : FullPropDecSpecs.FullConflOkW F_cur s.core) : FullConflictOkW F_cur s := by
  rcases h with ⟨ht, h0, h1, hent, hf0, hf1⟩ | hr
  · exact Or.inl ⟨ht, h0, h1, hf0, hf1, hent⟩
  · exact Or.inr hr

private theorem fullConflictOkW_to_confl {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflictOkW F_cur s) : FullPropDecSpecs.FullConflOkW F_cur s.core := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | hr
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr hr

private theorem pdTrailExt_to_canon {k1 k2 : FullCoreState}
    (h : FullPropDecSpecs.FullTrailExt k1 k2) : FullTrailExt k1 k2 :=
  ⟨h.te_ge, h.trl_pref, h.lvl_pres⟩

private theorem canonTrailExt_to_pd {k1 k2 : FullCoreState}
    (h : FullTrailExt k1 k2) : FullPropDecSpecs.FullTrailExt k1 k2 :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem pdArenaPerm_to_canon {k1 k2 : FullCoreState} (hal : k2.arena_len = k1.arena_len)
    (h : FullPropDecSpecs.FullArenaPermEq k1 k2) : FullArenaPermEq k1 k2 :=
  ⟨hal, h.1, h.2⟩

private theorem canonArenaPerm_to_pd {k1 k2 : FullCoreState}
    (h : FullArenaPermEq k1 k2) : FullPropDecSpecs.FullArenaPermEq k1 k2 :=
  ⟨h.2.1, h.2.2⟩

private theorem fullArenaPerm_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem fullArenaPerm_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

theorem full_prop_lit_bridge_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullFindReplSpec a m Q X →
      Γ "full_find_repl" [i64, i64] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hAssignLevel : ∀ a m Q X, fullAssignLevelSpec a m Q X →
      Γ "full_assign_level" [i64, i32, i32] [i32] a m Q X) :
    ∀ a m Q X, fullPropLitSpec a m Q X → Func.wp Γ full_prop_lit_body a m Q X := by
  rintro ⟨h, lit, ign, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hoom, hm, hQ⟩
  refine full_prop_lit_wp Γ ?_ ?_ ?_ hAssignLevel _ _ _ _
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hoom, hm, ?_⟩
  · rintro ⟨h', cr, ⟨⟩⟩ m' Q' X' ⟨c', s', R', rfl, hl', hc3, hsz, hfit, hm', hN, hS⟩
    exact hFind _ _ _ _ ⟨c', s', R', rfl, hl', hc3, hsz, hfit, hm', hN, hS⟩
  · rintro ⟨h', l', w0, w1, cnt, ⟨⟩⟩ m' Q' X' ⟨c', s', R', rfl, hl', hlay, hc1, hc2, hm', hQ'⟩
    refine hPush _ _ _ _ ⟨c', s', R', rfl, hl', hlay, hc1, hc2, hm',
      fun ok wv ws wl wu wso m'' hl'' hly'' hoth hT hF hm'' =>
        hQ' ok wv ws wl wu wso m'' hl'' hly'' hoth hT (fun hf => (hF hf).1) hm''⟩
  · rintro ⟨h', l', rsn, alvl, ⟨⟩⟩ m' Q' X' ⟨c', s', R', rfl, hl', hm', hQ'⟩
    refine hAssignLvl _ _ _ _ ⟨c', s', R', rfl, hl', hm', ?_⟩
    split
    · next hgr => simpa only [hgr, ↓reduceIte] using hQ'
    · next hngr =>
      simp only [hngr, ↓reduceIte] at hQ' ⊢
      intro fl' un' ph' m'' hfl hph hm''
      exact hQ' fl' un'
        (if alvl = 0#32 then s'.core.unflushed + 1#64 else s'.core.unflushed)
        ph' m'' hfl hph hm''
  · dsimp only
    intro ok vals' flags' lvl' rsns' trl' tp' te' un' uf' wv' ar' ws' wl' wu' ct' cr' c0' c1' om'
      tk' wso' ph' m' hlen' hw' htr hpm hT hF hm'
    exact hQ ok vals' flags' lvl' rsns' trl' tp' te' un' uf' wv' ar' ws' wl' wu' ct' cr' c0' c1' om'
      tk' wso' ph' m' hlen' hw' (pdTrailExt_to_canon htr) (pdArenaPerm_to_canon rfl hpm)
      (fun hf => (hF hf).elim Or.inl fun ⟨hc, hign⟩ =>
        Or.inr ⟨fullConflOkW_to_conflict hc, hign⟩) hT hm'

theorem full_propagate_ignore_bridge_wp (Γ : Env)
    (hPropLit : ∀ a m Q X, fullPropLitSpec a m Q X →
      Γ "full_prop_lit" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullPropagateIgnoreSpec a m Q X →
      Func.wp Γ full_propagate_ignore_body a m Q X := by
  rintro ⟨h, ign, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  refine full_propagate_ignore_wp Γ ?_ _ _ _ _ ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  · rintro ⟨h', l', ign', ⟨⟩⟩ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hdm', hom', hm', hQ'⟩
    refine hPropLit _ _ _ _ ⟨c', F0', Fc', s', R', rfl, hl', hw', hdm', hom', hm', ?_⟩
    dsimp only
    intro ok vals' flags' lvl' rsns' trl' tp' te' un' uf' wv' ar' ws' wl' wu' ct' cr' c0' c1' om'
      tk' wso' ph' m'' hlen'' hw'' htr hpm hF hT hm''
    exact hQ' ok vals' flags' lvl' rsns' trl' tp' te' un' uf' wv' ar' ws' wl' wu' ct' cr' c0' c1'
      om' tk' wso' ph' m'' hlen'' hw'' (canonTrailExt_to_pd htr) (canonArenaPerm_to_pd hpm) hT
      (fun hf => (hF hf).elim Or.inl fun ⟨hc, hign⟩ =>
        Or.inr ⟨fullConflictOkW_to_confl hc, hign⟩) hm''
  · dsimp only
    intro r vals' flags' lvl' rsns' trl' tp' te' prop' un' uf' wv' ar' ws' wl' wu' fu'
      ct' cr' c0' c1' om' tk' wso' ph' m' hlen' hw' htr hpm hfu hr hr0 hr1 hr2 hnp hm'
    exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' un' uf' wv' ar' ws' wl' wu' fu'
      ct' cr' c0' c1' om' tk' wso' ph' m' hlen' hw' (pdTrailExt_to_canon htr)
      (pdArenaPerm_to_canon rfl hpm) hfu hr hr0
      (fun h1 => let ⟨hf, ho, hc, hign, _⟩ := hr1 h1
        ⟨hf, ho, fullConflOkW_to_conflict hc, hign⟩) hr2 hnp hm'

theorem full_propagate_bridge_wp (Γ : Env)
    (hPropIgn : ∀ a m Q X, fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullPropagateSpec a m Q X → Func.wp Γ full_propagate_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  refine full_propagate_wp Γ ?_ _ _ _ _ ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  · rintro ⟨h', ign', ⟨⟩⟩ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hdm', hm', hQ'⟩
    refine hPropIgn _ _ _ _ ⟨c', F0', Fc', s', R', rfl, hl', hw', hdm', hm', ?_⟩
    dsimp only
    intro r vals' flags' lvl' rsns' trl' tp' te' prop' un' uf' wv' ar' ws' wl' wu' fu'
      ct' cr' c0' c1' om' tk' wso' ph' m'' hlen'' hw'' htr hpm hfu hr hr0 hr1 hr2 hnp hm''
    exact hQ' r vals' flags' lvl' rsns' trl' tp' te' prop' un' uf' wv' ar' ws' wl' wu' fu'
      ct' cr' c0' c1' om' tk' wso' ph' m'' hlen'' hw'' (canonTrailExt_to_pd htr)
      (canonArenaPerm_to_pd hpm) hfu hr hr0
      (fun h1 => let ⟨hf, ho, hc, hign⟩ := hr1 h1
        ⟨hf, ho, fullConflictOkW_to_confl hc, hign,
          fun hl0 => level0_unsat_of_conflict_okW hw'' hl0 hc⟩) hr2 hnp hm''
  · dsimp only
    intro r vals' flags' lvl' rsns' trl' tp' te' prop' un' uf' wv' ar' ws' wl' wu' fu'
      ct' cr' c0' c1' om' tk' wso' ph' m' hlen' hw' htr hpm _ hfu hr hr0 hr1 hr2 hnp hm'
    exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' un' uf' wv' ar' ws' wl' wu' fu'
      ct' cr' c0' c1' om' tk' wso' ph' m' hlen' hw' (pdTrailExt_to_canon htr)
      (pdArenaPerm_to_canon rfl hpm) hfu hr hr0
      (fun h1 => let ⟨hf, ho, hc, _⟩ := hr1 h1; ⟨hf, ho, fullConflOkW_to_conflict hc⟩)
      hr2 hnp hm'

theorem full_decide_bridge_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullDecideSpec a m Q X → Func.wp Γ full_decide_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  refine full_decide_wp Γ ?_ ?_ _ _ _ _ ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
  · rintro ⟨h', ⟨⟩⟩ m' Q' X' ⟨c', s', R', rfl, hlen', hm', hQ'⟩
    apply hNextDec
    refine ⟨c', s', R', rfl, hlen', hm', ?_⟩
    rintro ⟨r, ⟨⟩⟩ s'' m'' hcore'' hlen'' ⟨hpres'', hr⟩ hm''
    rcases s'' with ⟨c_sc, sc'⟩
    dsimp only [fullSafetySlice] at hcore''
    cases hcore''
    exact hQ' r sc' m'' hlen''.scratch_ok hpres''.1 hpres''.2 hr hm''
  · rintro ⟨h', lit, rsn, ⟨⟩⟩ m' Q' X' ⟨c', s', R', rfl, hlen', hcl32, hm', hQ'⟩
    apply hAssign
    refine ⟨c', s', R', rfl, hlen', hcl32, hm', ?_⟩
    split
    · next hgr => simpa only [hgr, ↓reduceIte] using hQ'
    · next hngr =>
      simp only [hngr, ↓reduceIte] at hQ' ⊢
      intro flags' unass' phases' m'' hfl' hph' hm''
      exact hQ' flags' unass'
        (if s'.core.cur_level = 0 then s'.core.unflushed + 1#64 else s'.core.unflushed)
        phases' m'' hfl' hph' hm''
  · dsimp only
    intro r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m'
      hinv' hll' hext' hr hr0 hr1 hm'
    exact hQ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m'
      hinv' ⟨hll', hext'⟩ hr hr0 hr1 hm'

theorem full_rephase_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, fullWalkSpec a m Q X → Γ "full_walk" [i64] [] a m Q X)
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullRephaseSpec a m Q X → Func.wp Γ full_rephase_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  obtain ⟨F_cur, hw0⟩ := hinv.witness
  have hco0 := hinv.lengths.core_ok
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmaxv_pos : (0 : BitVec 64).toNat < s.core.cur_level →
      (0 : BitVec 64).toNat < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
    have := hco0.cur_vars_le; omega
  fp_steps
  c0_call hBt
  refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt64, hmaxv_pos, hw0.trail_lits_lt, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc1 m1
      hlen1 _ _ hcl' hpres1 _ _ _ hwinv1 _ hm1 => ?_⟩
  have hw1 : FullWitnessInv c F0 F_cur
      { s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unas' } :=
    hwinv1 F0 F_cur hw0 (Nat.zero_le _)
  have hinv1_raw : FullCoreInv c F0
      { core := { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unas' }
        scratch := sc1 } := ⟨hlen1, F_cur, hw1⟩
  have hcl'0 : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
  subst hcl'0
  let st1 : FullState :=
    { core := { s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := 0,
        unassigned := unas' }
      scratch := sc1 }
  have hinv1 : FullCoreInv c F0 st1 := hinv1_raw
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hinv1.lengths.core_ok.cur_vars_le
  have hll1 : sc1.last_learned = s.scratch.last_learned := hpres1.1.1
  have hext1 : sc1.extend_len = s.scratch.extend_len := hpres1.1.2
  fp_nojoin
  let sc2 : FullScratch := { sc1 with rephased := sc1.rephased + 1#64 }
  have hsc2_ok : sc2.LengthsOk c := { hinv1.lengths.scratch_ok with
    walk_vals_len := hinv1.lengths.scratch_ok.walk_vals_len }
  let st2 : FullState := { st1 with scratch := sc2 }
  have hinv2 : FullCoreInv c F0 st2 := hinv1.with_fuel_scratch hsc2_ok
  refine wp_join_group (fun (_k, ()) m2 => ∃ (fuel' : BitVec 64) (sc3 : FullScratch),
    sc3.LengthsOk c ∧ fuel'.toNat ≤ s.core.fuel.toNat ∧
    sc3.last_learned = s.scratch.last_learned ∧ sc3.extend_len = s.scratch.extend_len ∧
    (FullMem c { core := { st1.core with fuel := fuel' }, scratch := sc3 } ⋆ R) m2) ?_ ?_
  · rintro _ ⟨_k, ⟨⟩⟩ m2 ⟨fuel', sc3, hsc3, hfl3, hll3, hext3, hm2⟩
    refine wp_loop_inv
      (fun (k, ()) m3 => ∃ ptgt' : List (BitVec 8),
        k.toNat ≤ s.core.cur_vars ∧ ptgt'.length = c.max_vars ∧
        (FullMem c
          { core := { st1.core with fuel := fuel' }
            scratch := { sc3 with phases_target := ptgt' } } ⋆ R) m3)
      (fun (k, ()) _ => s.core.cur_vars - k.toNat)
      (fun L hL => by
        fp_steps
        exact hL (0#64, ()) m2 ⟨sc3.phases_target, Nat.zero_le _, hsc3.phases_target_len, hm2⟩)
      (fun L (k, ()) m3 ⟨ptgt', hk_le, hpt_len, hm3⟩ ih => ?_)
    have hph3 := hsc3.phases_len
    fp_steps
    · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
      have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
      exact ih (k + (1 : BitVec 64), ()) m (by dsimp only; omega)
        ⟨ptgt'.set k.toNat (sc3.phases[k.toNat]'(by omega)), by omega, by simp [hpt_len], hm⟩
    · c0_call hIlog10
      intro lg _ _
      fp_steps
      let sc4 : FullScratch := { sc3 with
        phases_target := ptgt', target_assigned := 0#64,
        rephase_limit := sc3.conflicts + 1000#64 + 100#64 * sc3.rephased * lg }
      have hsc4 : sc4.LengthsOk c := { hsc3 with phases_target_len := hpt_len }
      have hinv4 : FullCoreInv c F0 { core := { st1.core with fuel := fuel' }, scratch := sc4 } :=
        hinv1.with_fuel_scratch hsc4
      exact hQ vals' lvl' rsns' trl' tp' te' prop' unas' fuel' sc4 m hinv4 hfl3
        ⟨hll3, hext3⟩ hm
  · intro Jsel hJsel
    refine wp_join_group (fun () m0 => m = m0) ?_ ?_
    · rintro _ ⟨⟩ _ rfl
      refine wp_loop_inv
        (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
          k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
          (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
        (fun (k, ()) _ => s.core.cur_vars - k.toNat)
        (fun L hL => by
          fp_steps; refine hL (0#64, ()) m
            ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, ?_⟩
          dsimp only [st2, sc2]; exact hm)
        (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
      have hpb_l := hsc2_ok.phases_best_len
      fp_steps
      · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
        have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
        exact ih (k + (1 : BitVec 64), ()) m (by dsimp only; omega)
          ⟨ph'.set k.toNat (sc2.phases_best[k.toNat]'(by omega)), by omega, by simp [hph_l], hm⟩
      · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
        have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
        exact ih (k + (1 : BitVec 64), ()) m3 (by dsimp only; omega) ⟨ph', by omega, hph_l, hm3⟩
      · refine hJsel (_, ()) m ⟨s.core.fuel, { sc2 with phases := ph', best_assigned := 0#64 },
          { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, ?_⟩
        dsimp only [st2, sc2]; exact hm
    · intro Jbest hJbest
      fp_nojoin
      · exact hJbest () m rfl
      · exact hJbest () m rfl
      · apply wp_unroll_group; intro _ hJelse1
        refine wp_join_group (fun () m0 => m = m0) ?_ ?_
        · rintro _ ⟨⟩ _ rfl
          c0_call hWalk
          refine ⟨c, F0, st2, R, rfl, hinv2, by dsimp only [st2, sc2]; exact hm,
            fun fuel' sc3 m3 hlen3 hfl3 hpres3 hm3 => ?_⟩
          fp_steps
          exact hJsel (_, ()) m3 ⟨fuel', sc3, hlen3.scratch_ok, hfl3,
            hpres3.1.trans hll1, hpres3.2.trans hext1, hm3⟩
        · intro Jwalk hJwalk
          fp_nojoin
          · exact hJwalk () m rfl
          · exact hJwalk () m rfl
          · apply wp_unroll_group; intro _ hJelse2
            fp_nojoin
            · refine wp_loop_inv
                (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                  k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
                  (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                (fun (k, ()) _ => s.core.cur_vars - k.toNat)
                (fun L hL => by
                  fp_steps; refine hL (0#64, ()) m
                    ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, ?_⟩
                  dsimp only [st2, sc2]; exact hm)
                (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
              fp_steps
              · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
                have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
                exact ih (k + (1 : BitVec 64), ()) m (by dsimp only; omega)
                  ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
              · fp_steps
                refine hJsel (_, ()) m3 ⟨s.core.fuel, { sc2 with phases := ph' },
                  { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, ?_⟩
                dsimp only [st2, sc2]; exact hm3
            · refine wp_loop_inv
                (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                  k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
                  (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                (fun (k, ()) _ => s.core.cur_vars - k.toNat)
                (fun L hL => by
                  fp_steps; refine hL (0#64, ()) m
                    ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, ?_⟩
                  dsimp only [st2, sc2]; exact hm)
                (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
              fp_steps
              · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
                have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
                exact ih (k + (1 : BitVec 64), ()) m (by dsimp only; omega)
                  ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
              · fp_steps
                refine hJsel (_, ()) m3 ⟨s.core.fuel, { sc2 with phases := ph' },
                  { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, ?_⟩
                dsimp only [st2, sc2]; exact hm3

theorem full_restart_bridge_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullRestartSpec a m Q X → Func.wp Γ full_restart_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  fp_steps
  let sc0 : FullScratch := { s.scratch with restarts := s.scratch.restarts + 1#64 }
  have hsc0 : sc0.LengthsOk c := { hinv.lengths.scratch_ok with
    walk_vals_len := hinv.lengths.scratch_ok.walk_vals_len }
  let s0 : FullState := { s with scratch := sc0 }
  have hinv0 : FullCoreInv c F0 s0 := hinv.with_fuel_scratch hsc0
  c0_call hNextDec
  refine ⟨c, s0, R, rfl, hinv0.lengths, hm, ?_⟩
  rintro ⟨nv, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, _hnv⟩ hm1
  rcases s1 with ⟨c1, sc1⟩
  dsimp only [fullSafetySlice] at hcore1
  cases hcore1
  have hsc1 : sc1.LengthsOk c := hlen1.scratch_ok
  have hll1 : sc1.last_learned = s.scratch.last_learned := hpres1.1
  have hext1 : sc1.extend_len = s.scratch.extend_len := hpres1.2
  let s1 : FullState := { s with scratch := sc1 }
  have hm1 : (FullMem c s1 ⋆ R) m1 := hm1
  have hinv1 : FullCoreInv c F0 s1 := hinv.with_fuel_scratch hsc1
  have hcl1 := hinv1.lengths.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcl1.cur_vars_le
  have hcv_le1 : s1.core.cur_vars ≤ c.max_vars := hcl1.cur_vars_le
  have hte_le : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
  have hte_le1 : s1.core.trail_end ≤ s1.core.cur_vars := hcl1.trail_end_le
  have hfdec_l : s.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
  have hfdec_l1 : s1.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
  have hsc_l : s1.scratch.score.length = c.max_vars := hsc1.score_len
  have hqs_l : s1.scratch.q_stamp.length = c.max_vars := hsc1.q_stamp_len
  obtain ⟨F_cur, hw1⟩ := hinv1.witness
  have hcl_le : s.core.cur_level ≤ s.core.trail_end := hw1.cur_level_le
  have hcl_le1 : s1.core.cur_level ≤ s1.core.trail_end := hw1.cur_level_le
  fp_nojoin
  refine wp_join_group (fun (reuse, ()) m2 => reuse.toNat ≤ s.core.cur_level ∧ m1 = m2) ?_ ?_
  · rintro _ ⟨reuse, ⟨⟩⟩ _ ⟨hre_le, rfl⟩
    have hcl_lt64 : s1.core.cur_level < 2 ^ 64 := by change s.core.cur_level < 2 ^ 64; omega
    have hre_mv : reuse.toNat < s1.core.cur_level → reuse.toNat < c.max_vars := by
      intro hlt; change reuse.toNat < s.core.cur_level at hlt; omega
    c0_call hBt
    refine ⟨c, s1, R, rfl, hinv1.lengths, hcl_lt64, hre_mv, hw1.trail_lits_lt, hm1,
      fun vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc2 m3
        hlen3 _ _ hcl3 hpres3 _ _ _ hwinv3 _ hm3 => ?_⟩
    have hw3 := hwinv3 F0 F_cur hw1 hre_le
    have hinv3 : FullCoreInv c F0
        { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unas' }
          scratch := sc2 } := ⟨hlen3, F_cur, hw3⟩
    fp_steps
    exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc2 m3 hinv3
      (by rw [hcl3]; exact Nat.min_le_left _ _)
      ⟨hpres3.1.1.trans hll1, hpres3.1.2.trans hext1⟩ hm3
  · intro Jre hJre; fp_nojoin
    · have hnv_lt : nv.toNat < s.core.cur_vars := by
        have h1 : nv.toNat < s1.core.cur_vars % 2 ^ 64 := by assumption
        change nv.toNat < s.core.cur_vars % 2 ^ 64 at h1
        rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1; exact h1
      fp_steps
      · refine wp_loop_group
          (fun rem (reuse, ()) ml =>
            rem = s.core.cur_level - reuse.toNat ∧ reuse.toNat ≤ s.core.cur_level ∧ m1 = ml)
          ?_ ?_
        · rintro L rem ⟨reuse, ⟨⟩⟩ _ ih ⟨rfl, hre_le, rfl⟩
          fp_steps
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
          · have hre_lt : reuse.toNat < s.core.cur_level := by
              have h1 : reuse.toNat < s1.core.cur_level % 2 ^ 64 := by assumption
              change reuse.toNat < s.core.cur_level % 2 ^ 64 at h1
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at h1; exact h1
            have hre1 : (reuse + (1 : BitVec 64)).toNat = reuse.toNat + 1 := bv64_add1_toNat
              (by omega)
            exact ih _ (reuse + (1 : BitVec 64), ()) m1 (by omega) ⟨rfl, by omega, rfl⟩
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
        · intro L hL; fp_steps; exact hL s.core.cur_level (0#64, ()) m1
            ⟨by simp, Nat.zero_le _, rfl⟩
      · refine wp_loop_group
          (fun rem (reuse, ()) ml =>
            rem = s.core.cur_level - reuse.toNat ∧ reuse.toNat ≤ s.core.cur_level ∧ m1 = ml)
          ?_ ?_
        · rintro L rem ⟨reuse, ⟨⟩⟩ _ ih ⟨rfl, hre_le, rfl⟩
          fp_steps
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
          · have hre_lt : reuse.toNat < s.core.cur_level := by
              have h1 : reuse.toNat < s1.core.cur_level % 2 ^ 64 := by assumption
              change reuse.toNat < s.core.cur_level % 2 ^ 64 at h1
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at h1; exact h1
            have hre1 : (reuse + (1 : BitVec 64)).toNat = reuse.toNat + 1 := bv64_add1_toNat
              (by omega)
            exact ih _ (reuse + (1 : BitVec 64), ()) m1 (by omega) ⟨rfl, by omega, rfl⟩
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
        · intro L hL; fp_steps; exact hL s.core.cur_level (0#64, ()) m1
            ⟨by simp, Nat.zero_le _, rfl⟩
    · exact hJre (0#64, ()) m1 ⟨Nat.zero_le _, rfl⟩
    · exact hJre (0#64, ()) m1 ⟨Nat.zero_le _, rfl⟩

private theorem warmup_bv32_dec_even {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : Nat)).setWidth 32).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [Nat.pow_one]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem warmup_bv32_dec_odd {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (((v <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hev := warmup_bv32_dec_even hv
  rw [show (((v <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat =
      ((v <<< (1 : Nat)).setWidth 32).toNat ||| 1 from by simp [BitVec.toNat_or], hev]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    have h0 : Nat.testBit 1 (k + 1) = false := by rw [Nat.testBit_succ]; simp
    rw [h0, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]; congr 1; omega

private def warmupBridgeMask (k : FullCoreState) : FullCoreState :=
  { k with
    vals := [], flags := [], lvl := [], rsns := [], trl := [], trail_pos := [],
    frame_trail := [], frame_dec := [], trail_end := 0, propagated := 0, cur_level := 0,
    probing := 0#64, unassigned := 0#64, unflushed := 0#64, wvec := [], arena := [],
    wstk := [], wlen := 0, wusable := 0#64, fuel := 0#64, confl_type := 0#64,
    confl_ref := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64, oom := 0#64 }

private theorem warmupBridge_eq_upd {s st : FullState}
    (h : AgreesExcept warmupBridgeMask s.core st.core)
    (hcl : st.core.cur_level = s.core.cur_level) :
    st =
      { core := { s.core with
          vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns,
          trl := st.core.trl, trail_pos := st.core.trail_pos, frame_trail := st.core.frame_trail,
          frame_dec := st.core.frame_dec, trail_end := st.core.trail_end,
          propagated := st.core.propagated, probing := st.core.probing,
          unassigned := st.core.unassigned, unflushed := st.core.unflushed, wvec := st.core.wvec,
          arena := st.core.arena, wstk := st.core.wstk, wlen := st.core.wlen,
          wusable := st.core.wusable, fuel := st.core.fuel, confl_type := st.core.confl_type,
          confl_ref := st.core.confl_ref, confl_lit0 := st.core.confl_lit0,
          confl_lit1 := st.core.confl_lit1, oom := st.core.oom }
        scratch := st.scratch } := by
  have h1 := h.get FullCoreState.d_cur; have h2 := h.get FullCoreState.d_val
  have h3 := h.get FullCoreState.cur_vars; have h4 := h.get FullCoreState.arena_len
  have h5 := h.get FullCoreState.arena_garbage; have h6 := h.get FullCoreState.first_reducible
  have h7 := h.get FullCoreState.num_irred; have h8 := h.get FullCoreState.num_redundant
  have h9 := h.get FullCoreState.num_binary; have h10 := h.get FullCoreState.tmp_cnt
  have h11 := h.get FullCoreState.tmp_len; have h12 := h.get FullCoreState.min_clr_len
  have h13 := h.get FullCoreState.min_clr_full; have h14 := h.get FullCoreState.dense_mode
  have h15 := h.get FullCoreState.inconsistent; have h16 := h.get FullCoreState.lit_mark
  have h17 := h.get FullCoreState.mrk; have h18 := h.get FullCoreState.tmp
  have h19 := h.get FullCoreState.min_clr; have h20 := h.get FullCoreState.repr
  have h21 := h.get FullCoreState.min_stk
  cases st with | mk stc stsc =>
  cases s with | mk sc ssc =>
  cases stc; cases sc; simp only at *; subst_vars; rfl

theorem full_warmup_bridge_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWarmupSpec a m Q X → Func.wp Γ full_warmup_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_noop : Q () m :=
    hQ s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.propagated s.core.probing
      s.core.unassigned s.core.unflushed s.core.wvec s.core.arena s.core.wstk s.core.wlen
      s.core.wusable s.core.fuel s.core.confl_type s.core.confl_ref s.core.confl_lit0
      s.core.confl_lit1 s.core.oom s.scratch m hinv (fullArenaPerm_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) hm
  have hcv0 := hinv.lengths.core_ok.cur_vars_le
  have hte0 := hinv.lengths.core_ok.trail_end_le
  obtain ⟨_, hw0⟩ := hinv.witness
  have hcl0_le := hw0.cur_level_le
  fp_nojoin
  · exact hret_noop
  · exact hret_noop
  · have hcl0 : s.core.cur_level = 0 := by c0_bound
    let st0 : FullState := { s with core := { s.core with probing := 1#64 } }
    have hinv0 : FullCoreInv c F0 st0 := hinv.with_probing 1#64
    refine wp_loop_break_group
      (fun (_steps, ()) mb => ∃ st : FullState,
        FullCoreInv c F0 st ∧ AgreesExcept warmupBridgeMask s.core st.core ∧
        FullArenaPermEq s.core st.core ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        st.scratch.last_learned = s.scratch.last_learned ∧
        st.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c st ⋆ R) mb)
      (fun rem (steps, ()) ml => ∃ st : FullState,
        rem = s.core.cur_vars - steps.toNat ∧ steps.toNat ≤ s.core.cur_vars ∧
        FullCoreInv c F0 st ∧ AgreesExcept warmupBridgeMask s.core st.core ∧
        FullArenaPermEq s.core st.core ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        st.scratch.last_learned = s.scratch.last_learned ∧
        st.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c st ⋆ R) ml) ?_ ?_ ?_
    · rintro _ ⟨_steps, ⟨⟩⟩ mb ⟨st, hst_inv, hag, hperm, hfl, hll, hext, hmb⟩
      obtain ⟨Fc_b, hwb⟩ := hst_inv.witness
      have hcb := hst_inv.lengths.core_ok
      have hcl_lt64 : st.core.cur_level < 2 ^ 64 := by
        have := hwb.cur_level_le; have := hcb.trail_end_le; have := hcb.cur_vars_le; omega
      have hmaxv_pos : (0 : BitVec 64).toNat < st.core.cur_level →
          (0 : BitVec 64).toNat < c.max_vars := by
        intro _; have := hwb.cur_level_le; have := hcb.trail_end_le; have := hcb.cur_vars_le; omega
      fp_steps; c0_call hBt
      refine ⟨c, st, R, rfl, hst_inv.lengths, hcl_lt64, hmaxv_pos, hwb.trail_lits_lt, hmb,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc' m1
          hlen1 _ _ hcl' hpres1 _ _ _ hwinv1 _ hm1 => ?_⟩
      have hcl'0 : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
      subst hcl'0
      let st1 : FullState :=
        { core := { st.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := 0, unassigned := unas' }
          scratch := sc' }
      have hinv1 : FullCoreInv c F0 st1 := ⟨hlen1, Fc_b, hwinv1 F0 Fc_b hwb (Nat.zero_le _)⟩
      fp_steps
      let st2 : FullState := { st1 with core := { st1.core with probing := 0#64 } }
      have hinv2 : FullCoreInv c F0 st2 := hinv1.with_probing 0#64
      have hag2 : AgreesExcept warmupBridgeMask s.core st2.core :=
        hag.update (fun k => { k with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := 0,
          unassigned := unas', probing := 0#64 })
      have hst2_eq := warmupBridge_eq_upd hag2 (by dsimp [st2, st1]; omega)
      have hinv2' := hinv2; have hm2' : (FullMem c st2 ⋆ R) m := hm
      have hperm' : FullArenaPermEq s.core st2.core := hperm
      rw [hst2_eq] at hinv2' hm2' hperm'
      exact hQ st2.core.vals st2.core.flags st2.core.lvl st2.core.rsns st2.core.trl
        st2.core.trail_pos st2.core.frame_trail st2.core.frame_dec st2.core.trail_end
        st2.core.propagated st2.core.probing st2.core.unassigned st2.core.unflushed
        st2.core.wvec st2.core.arena st2.core.wstk st2.core.wlen st2.core.wusable
        st2.core.fuel st2.core.confl_type st2.core.confl_ref st2.core.confl_lit0
        st2.core.confl_lit1 st2.core.oom st2.scratch m hinv2' hperm' hfl
        ⟨hpres1.1.1.trans hll, hpres1.1.2.trans hext⟩ (fun _ => rfl) hm2'
    · rintro B L rem ⟨steps, ⟨⟩⟩ ml hB ih
        ⟨st, rfl, hst_le, hst_inv, hag, hperm, hfl, hll, hext, hml⟩
      have hcv_eq : st.core.cur_vars = s.core.cur_vars := hag.get FullCoreState.cur_vars
      have hdm_st : st.core.dense_mode = 0#64 := (hag.get FullCoreState.dense_mode).trans hdense0
      have hcv_le := hst_inv.lengths.core_ok.cur_vars_le
      fp_steps
      · have hst_lt : steps.toNat < s.core.cur_vars := by
          have h1 : steps.toNat < st.core.cur_vars % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt (by omega : st.core.cur_vars < 2 ^ 64)] at h1; omega
        have hst1_nat : (steps + (1 : BitVec 64)).toNat = steps.toNat + 1 := bv64_add1_toNat
          (by omega)
        c0_call hNextDec
        refine ⟨c, st, R, rfl, hst_inv.lengths, hml,
          fun ⟨v, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hp1, hv⟩ hm1 => ?_⟩
        rcases s1 with ⟨c1, sc1⟩; dsimp only [fullSafetySlice] at hcore1; cases hcore1
        let st1 : FullState := { st with scratch := sc1 }
        change (FullMem c { st with scratch := sc1 } ⋆ R) m1 at hm1
        have hinv1 : FullCoreInv c F0 st1 := hst_inv.with_fuel_scratch hlen1.scratch_ok
        have hcl1 := hinv1.lengths.core_ok
        have hph1 : sc1.phases.length = c.max_vars := hlen1.scratch_ok.phases_len
        have hftrl1 : st.core.frame_trail.length = c.max_vars + 1 := hcl1.frame_trail_len
        have hfdec1 : st.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
        fp_nojoin
        · exact hB (steps + (1 : BitVec 64), ()) m1
            ⟨st1, hinv1, hag, hperm, hfl, hp1.1.trans hll, hp1.2.trans hext, hm1⟩
        · obtain ⟨hv_lt, hval0⟩ := hv.resolve_left hc
          have hv_lt_max : v.toNat < c.max_vars := by omega
          have hv_lt30 : v.toNat < 2 ^ 30 := by omega
          refine wp_join_group (fun (lit, ()) m2 =>
            m1 = m2 ∧ (lit.toNat = 2 * v.toNat ∨ lit.toNat = 2 * v.toNat + 1)) ?_ ?_
          · rintro _ ⟨lit, ⟨⟩⟩ _ ⟨rfl, hlit_eq⟩
            have hte1 : st.core.trail_end ≤ st.core.cur_vars := hcl1.trail_end_le
            obtain ⟨_, hw1⟩ := hinv1.witness
            have hcl1_le : st.core.cur_level ≤ st.core.trail_end := hw1.cur_level_le
            have hcl1_lt : st.core.cur_level < 2 ^ 63 := by omega
            have hnlvl_nat : (BitVec.ofNat 64 st.core.cur_level + (1 : BitVec 64)).toNat =
                st.core.cur_level + 1 := by bv_omega
            fp_steps
            · exact hB (steps + (1 : BitVec 64), ()) m1
                ⟨st1, hinv1, hag, hperm, hfl, hp1.1.trans hll, hp1.2.trans hext, hm1⟩
            · have hnlvl_le : st.core.cur_level + 1 ≤ c.max_vars := by c0_bound
              have ⟨_, hun, hte_lt, _⟩ := full_decide_preserves_fullCore hinv1 hlen1.scratch_ok
                hcl1.flags_len hv_lt hval0 hlit_eq (flags' := st.core.flags)
                (unas' := st.core.unassigned) (unfl' := st.core.unflushed)
              have hte_lt' : st.core.trail_end < st.core.cur_vars := hte_lt
              let nlvl := st.core.cur_level + 1
              let ftrl' := st.core.frame_trail.set nlvl (BitVec.ofNat 32 st.core.trail_end)
              let fdec' := st.core.frame_dec.set nlvl lit
              let st2 : FullState :=
                { core := { st.core with
                    frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl }
                  scratch := sc1 }
              have hlen2 : st2.LengthsOk c :=
                ⟨{ hcl1 with frame_trail_len := by simp [st2, ftrl', hftrl1]
                             frame_dec_len := by simp [st2, fdec', hfdec1] }, hlen1.scratch_ok⟩
              have hm2 : (FullMem c st2 ⋆ R) m := by
                have hte_bv : (BitVec.ofNat 64 st.core.trail_end).setWidth 32 =
                    BitVec.ofNat 32 st.core.trail_end := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : st.core.trail_end < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : st.core.trail_end < 2 ^ 32)]
                simpa only [st2, ftrl', fdec', nlvl, hnlvl_nat, hte_bv] using hm
              have hng : ¬ (st2.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st2.core.trail_end ∨
                  st2.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                change ¬ (st1.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st1.core.trail_end ∨
                  st1.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
                simp only [hun, ne_eq, not_true_eq_false, or_false]
                change ¬ (st.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st.core.trail_end)
                omega
              c0_call hAssign
              refine ⟨c, st2, R, rfl, hlen2, by dsimp [st2, nlvl]; omega, hm2, ?_⟩
              simp only [hng, ↓reduceIte]
              intro flags' unas' phases' m3 hfl_l hph_l hm3
              have hsc3 : ({ sc1 with phases := phases' } : FullScratch).LengthsOk c :=
                { hlen1.scratch_ok with phases_len := hph_l }
              have ⟨hinv3, _, _, _⟩ := full_decide_preserves_fullCore hinv1 hsc3 hfl_l hv_lt hval0
                hlit_eq (flags' := flags') (unas' := unas') (unfl' := st.core.unflushed)
              have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
              have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
              let st3 : FullState :=
                { core := { st.core with
                    vals := (st.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
                    flags := flags', lvl := st.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
                    rsns := st.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
                    trl := st.core.trl.set st.core.trail_end lit,
                    trail_pos := st.core.trail_pos.set (lit.toNat / 2)
                      (BitVec.ofNat 32 st.core.trail_end),
                    frame_trail := ftrl', frame_dec := fdec', trail_end := st.core.trail_end + 1,
                    cur_level := nlvl, unassigned := unas' }
                  scratch := { sc1 with phases := phases' } }
              have hm3' : (FullMem c st3 ⋆ R) m3 := by
                simpa only [st3, st2, hnl_ne0, ↓reduceIte, hff] using hm3
              have hag3 : AgreesExcept warmupBridgeMask s.core st3.core :=
                hag.update (fun k => { k with
                  vals := st3.core.vals, flags := flags', lvl := st3.core.lvl,
                  rsns := st3.core.rsns, trl := st3.core.trl, trail_pos := st3.core.trail_pos,
                  frame_trail := ftrl', frame_dec := fdec', trail_end := st.core.trail_end + 1,
                  cur_level := nlvl, unassigned := unas' })
              obtain ⟨F_cur, hw3⟩ := hinv3.witness
              c0_call hProp
              refine ⟨c, F0, F_cur, st3, R, rfl, hinv3.lengths, hw3, hdm_st, hm3', ?_⟩
              dsimp only
              intro r vals'' flags'' lvl'' rsns'' trl'' tp'' te'' prop'' unas'' unfl''
                wvec'' arena'' wstk'' wlen'' wu'' fuel'' ctype'' cref'' c0'' c1'' oom''
                ticks'' wsort'' phases'' m4 hlen4 hw4 _ hperm4 hfl4 _ _ _ _ _ hm4
              let st4 : FullState :=
                { core := { st3.core with
                    vals := vals'', flags := flags'', lvl := lvl'', rsns := rsns'', trl := trl'',
                    trail_pos := tp'', trail_end := te'', propagated := prop'',
                    unassigned := unas'', unflushed := unfl'', wvec := wvec'', arena := arena'',
                    wstk := wstk'', wlen := wlen'', wusable := wu'', fuel := fuel'',
                    confl_type := ctype'', confl_ref := cref'', confl_lit0 := c0'',
                    confl_lit1 := c1'', oom := oom'' }
                  scratch := { st3.scratch with
                    search_ticks := ticks'', wsort := wsort'', phases := phases'' } }
              have hinv4 : FullCoreInv c F0 st4 := ⟨hlen4, F_cur, hw4⟩
              have hag4 : AgreesExcept warmupBridgeMask s.core st4.core :=
                hag3.update (fun k => { k with
                  vals := vals'', flags := flags'', lvl := lvl'', rsns := rsns'', trl := trl'',
                  trail_pos := tp'', trail_end := te'', propagated := prop'',
                  unassigned := unas'', unflushed := unfl'', wvec := wvec'', arena := arena'',
                  wstk := wstk'', wlen := wlen'', wusable := wu'', fuel := fuel'',
                  confl_type := ctype'', confl_ref := cref'', confl_lit0 := c0'',
                  confl_lit1 := c1'', oom := oom'' })
              have hperm4' : FullArenaPermEq s.core st4.core :=
                fullArenaPerm_trans hperm hperm4
              have hfl4' : st4.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl4 hfl
              fp_steps
              · exact hB (steps + (1 : BitVec 64), ()) m4 ⟨st4, hinv4, hag4, hperm4', hfl4',
                  hp1.1.trans hll, hp1.2.trans hext, hm4⟩
              · exact ih (s.core.cur_vars - (steps + (1 : BitVec 64)).toNat)
                  (steps + (1 : BitVec 64), ()) m4 (by omega)
                  ⟨st4, rfl, by omega, hinv4, hag4, hperm4', hfl4', hp1.1.trans hll,
                    hp1.2.trans hext, hm4⟩
          · intro Jlit hJlit; fp_steps
            · exact hJlit ((v <<< (1 : Nat)).setWidth 32 ||| 1#32, ()) m1
                ⟨rfl, Or.inr (warmup_bv32_dec_odd hv_lt30)⟩
            · exact hJlit ((v <<< (1 : Nat)).setWidth 32, ()) m1
                ⟨rfl, Or.inl (warmup_bv32_dec_even hv_lt30)⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hperm, hfl, hll, hext, hml⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hperm, hfl, hll, hext, hml⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hperm, hfl, hll, hext, hml⟩
    · intro _ L _ hL; fp_steps
      exact hL s.core.cur_vars (0#64, ()) m ⟨st0, by simp, Nat.zero_le _, hinv0,
        (AgreesExcept.refl warmupBridgeMask s.core).update (fun k => { k with probing := 1#64 }),
        fullArenaPerm_refl _, Nat.le_refl _, rfl, rfl, hm⟩

end Part2

/-! ## Part 3: `FullMinLemmas` (`8` fns) -/

section Part3

private theorem minMarkInv_to_canon {k : FullCoreState} {keep : List Nat}
    (h : FullMinSpecs.FullMinMarkInv k keep) : FullMinMarkInv k keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

private theorem canon_to_minMarkInv {k : FullCoreState} {keep : List Nat}
    (h : FullMinMarkInv k keep) : FullMinSpecs.FullMinMarkInv k keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

private theorem fullMinMarkSpec_to_min {Γ : Env}
    (hMm : ∀ a m Q X, fullMinMarkSpec a m Q X → Γ "full_min_mark" [i64, i32, i8] [] a m Q X) :
    ∀ a m Q X, FullMinSpecs.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X := by
  rintro ⟨h, v, tag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hMm _ m Q X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  dsimp only
  split
  · next hgr => simp only [hgr, ↓reduceIte] at hQ; exact hQ
  · next hngr =>
    simp only [hngr, ↓reduceIte] at hQ
    intro m' hm'
    dsimp only [fullMinMarkState, fullMinMarkCore] at hm'
    by_cases hcur : s.core.mrk[v.toNat]?.getD 0#8 = 0#8
    · have hne_f : (s.core.mrk[v.toNat]?.getD 0#8 ≠ 0#8) = False :=
        eq_false (Classical.not_not.mpr hcur)
      simp only [hne_f, ↓reduceIte] at hQ
      by_cases hlt : s.core.min_clr_len < s.core.cur_vars
      · simp only [hlt, ↓reduceIte, hcur] at hQ
        have hbv : BitVec.ofNat 32 v.toNat = v := by bv_omega
        simp only [hcur, true_and, hlt, ↓reduceIte, not_true_eq_false, hbv] at hm'
        exact hQ m' hm'
      · simp only [hlt, ↓reduceIte, hcur] at hQ
        simp only [hcur, true_and, hlt, ↓reduceIte] at hm'
        exact hQ m' hm'
    · simp only [ne_eq, hcur, not_false_eq_true, ↓reduceIte] at hQ
      simp only [hcur, false_and, ↓reduceIte] at hm'
      exact hQ m' hm'

theorem full_tmp_less_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullTmpLessSpec a m Q X → Func.wp Γ full_tmp_less_body a m Q X :=
  full_tmp_less_wp Γ

theorem full_min_mark_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullMinMarkSpec a m Q X → Func.wp Γ full_min_mark_body a m Q X := by
  rintro ⟨h, v, tag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  apply full_min_mark_wp Γ
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  dsimp only
  split
  · next hgr => simp only [hgr, ↓reduceIte] at hQ; exact hQ
  · next hngr =>
    simp only [hngr, ↓reduceIte] at hQ
    split
    · next hcur =>
      intro m' hm'
      have hcur_f : (s.core.mrk[v.toNat]?.getD 0#8 = 0#8) = False := eq_false hcur
      dsimp only [fullMinMarkState, fullMinMarkCore] at hQ
      simp only [hcur_f, false_and, ↓reduceIte] at hQ
      exact hQ m' hm'
    · next hncur =>
      have hcur0 : s.core.mrk[v.toNat]?.getD 0#8 = 0#8 := Classical.byContradiction hncur
      split
      · next hlt =>
        intro m' hm'
        have hbv : BitVec.ofNat 32 v.toNat = v := by bv_omega
        dsimp only [fullMinMarkState, fullMinMarkCore] at hQ
        simp only [hcur0, true_and, hlt, ↓reduceIte, not_true_eq_false, hbv] at hQ
        simp only [hcur0] at hm'
        exact hQ m' hm'
      · next hge =>
        intro m' hm'
        dsimp only [fullMinMarkState, fullMinMarkCore] at hQ
        simp only [hcur0, true_and, hge, ↓reduceIte] at hQ
        simp only [hcur0] at hm'
        exact hQ m' hm'

theorem full_sort_tmp_sift_bridge_wp (Γ : Env)
    (hTl : ∀ a m Q X, fullTmpLessSpec a m Q X →
      Γ "full_tmp_less" [i64, i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullSortTmpSiftSpec a m Q X → Func.wp Γ full_sort_tmp_sift_body a m Q X :=
  full_sort_tmp_sift_wp Γ hTl

theorem full_sort_tmp_bridge_wp (Γ : Env)
    (hSift : ∀ a m Q X, fullSortTmpSiftSpec a m Q X →
      Γ "full_sort_tmp_sift" [i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullSortTmpSpec a m Q X → Func.wp Γ full_sort_tmp_body a m Q X :=
  full_sort_tmp_wp Γ hSift

private theorem fullMinLitSpec_to_min {Γ : Env}
    (hMl : ∀ a m Q X, fullMinLitSpec a m Q X → Γ "full_min_lit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullMinSpecs.fullMinLitSpec a m Q X →
      Γ "full_min_lit" [i64, i32] [.bool] a m Q X := by
  rintro ⟨h, rl, ⟨⟩⟩ m Q X ⟨c, F0, s, ks, R, rfl, ho, hmi, hrl, hv, hl, h8, hm, hQ⟩
  refine hMl _ m Q X ⟨c, F0, s, ks, R, rfl, ho, minMarkInv_to_canon hmi, hrl, hv, hl, h8, hm,
    fun ok mrk' mstk' mclr' mcl' mcf' m' hlen' habv h2 h8' hmi' hok hm' =>
      hQ ok mrk' mstk' mclr' mcl' mcf' m' hlen' habv h2 h8' (canon_to_minMarkInv hmi')
        (fun ht => let ⟨hk, hm2⟩ := hok ht
          ⟨fun kp hsub => canon_to_minMarkInv (hk kp hsub), canon_to_minMarkInv hm2⟩) hm'⟩

theorem full_min_lit_bridge_wp (Γ : Env)
    (hMm : ∀ a m Q X, fullMinMarkSpec a m Q X → Γ "full_min_mark" [i64, i32, i8] [] a m Q X) :
    ∀ a m Q X, fullMinLitSpec a m Q X → Func.wp Γ full_min_lit_body a m Q X := by
  rintro ⟨h, rl, ⟨⟩⟩ m Q X ⟨c, F0, s, ks, R, rfl, ho, hmi, hrl, hv, hl, h8, hm, hQ⟩
  refine full_min_lit_wp Γ (fullMinMarkSpec_to_min hMm) _ m Q X
    ⟨c, F0, s, ks, R, rfl, ho, canon_to_minMarkInv hmi, hrl, hv, hl, h8, hm,
      fun ok mrk' mstk' mclr' mcl' mcf' m' hlen' habv h2 h8' hmi' hok hm' =>
        hQ ok mrk' mstk' mclr' mcl' mcf' m' hlen' habv h2 h8' (minMarkInv_to_canon hmi')
          (fun ht => let ⟨hk, hm2⟩ := hok ht
            ⟨fun kp hsub => minMarkInv_to_canon (hk kp hsub), minMarkInv_to_canon hm2⟩) hm'⟩

private theorem fullShrinkLowerSpec_to_min {Γ : Env}
    (hSl : ∀ a m Q X, fullShrinkLowerSpec a m Q X →
      Γ "full_shrink_lower" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullMinSpecs.fullShrinkLowerSpec a m Q X →
      Γ "full_shrink_lower" [i64, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, ot, ov, ⟨⟩⟩ m Q X ⟨c, F0, s, ks, R, rfl, ho, hmi, hov, hot, hv, hl, h8, hm, hQ⟩
  refine hSl _ m Q X ⟨c, F0, s, ks, R, rfl, ho, minMarkInv_to_canon hmi, hov, hot, hv, hl, h8, hm,
    fun ok mrk' mstk' mclr' mcl' mcf' m' hlen' habv h2 h8' hmi' hok hm' =>
      hQ ok mrk' mstk' mclr' mcl' mcf' m' hlen' habv h2 h8' (canon_to_minMarkInv hmi') hok hm'⟩

theorem full_shrink_lower_bridge_wp (Γ : Env)
    (hMm : ∀ a m Q X, fullMinMarkSpec a m Q X → Γ "full_min_mark" [i64, i32, i8] [] a m Q X)
    (hMl : ∀ a m Q X, fullMinLitSpec a m Q X → Γ "full_min_lit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullShrinkLowerSpec a m Q X → Func.wp Γ full_shrink_lower_body a m Q X := by
  rintro ⟨h, ot, ov, ⟨⟩⟩ m Q X ⟨c, F0, s, ks, R, rfl, ho, hmi, hov, hot, hv, hl, h8, hm, hQ⟩
  refine full_shrink_lower_wp Γ (fullMinMarkSpec_to_min hMm) (fullMinLitSpec_to_min hMl) _ m Q X
    ⟨c, F0, s, ks, R, rfl, ho, canon_to_minMarkInv hmi, hov, hot, hv, hl, h8, hm,
      fun ok mrk' mstk' mclr' mcl' mcf' m' hlen' habv h2 h8' hmi' hok hm' =>
        hQ ok mrk' mstk' mclr' mcl' mcf' m' hlen' habv h2 h8' (minMarkInv_to_canon hmi') hok hm'⟩

private theorem fullShrinkBlkSpec_to_min {Γ : Env}
    (hSb : ∀ a m Q X, fullShrinkBlkSpec a m Q X →
      Γ "full_shrink_blk" [i64, i64, i64, i32, i64] [] a m Q X) :
    ∀ a m Q X, FullMinSpecs.fullShrinkBlkSpec a m Q X →
      Γ "full_shrink_blk" [i64, i64, i64, i32, i64] [] a m Q X := by
  rintro ⟨h, beg, eb, bl, mtr, ⟨⟩⟩ m Q X
    ⟨c, F0, s, R, rfl, ho, hmi, h8, h1, h2, h3, h4, h5, h6, h7, h9, hm, hQ⟩
  refine hSb _ m Q X ⟨c, F0, s, R, rfl, ho, minMarkInv_to_canon hmi, h8, h1, h2, h3, h4, h5, h6,
    h7, h9, hm, fun tmp' mrk' mstk' mclr' mcl' mcf' sstk' m' ho' hmi' hab h8' h2' hout hbl hnd hent
      hkeep hm' =>
      hQ tmp' mrk' mstk' mclr' mcl' mcf' sstk' m' ho' (canon_to_minMarkInv hmi') hab h8' h2' hout
        hbl hnd hent hkeep hm'⟩

theorem full_shrink_blk_bridge_wp (Γ : Env)
    (hSl : ∀ a m Q X, fullShrinkLowerSpec a m Q X →
      Γ "full_shrink_lower" [i64, i32, i32] [.bool] a m Q X)
    (hMm : ∀ a m Q X, fullMinMarkSpec a m Q X → Γ "full_min_mark" [i64, i32, i8] [] a m Q X) :
    ∀ a m Q X, fullShrinkBlkSpec a m Q X → Func.wp Γ full_shrink_blk_body a m Q X := by
  rintro ⟨h, beg, eb, bl, mtr, ⟨⟩⟩ m Q X
    ⟨c, F0, s, R, rfl, ho, hmi, h8, h1, h2, h3, h4, h5, h6, h7, h9, hm, hQ⟩
  refine full_shrink_blk_wp Γ (fullShrinkLowerSpec_to_min hSl) (fullMinMarkSpec_to_min hMm) _ m Q X
    ⟨c, F0, s, R, rfl, ho, canon_to_minMarkInv hmi, h8, h1, h2, h3, h4, h5, h6, h7, h9, hm,
      fun tmp' mrk' mstk' mclr' mcl' mcf' sstk' m' ho' hmi' hab h8' h2' hout hbl hnd hent
        hkeep hm' =>
        hQ tmp' mrk' mstk' mclr' mcl' mcf' sstk' m' ho' (minMarkInv_to_canon hmi') hab h8' h2' hout
          hbl hnd hent hkeep hm'⟩

theorem full_min_shrink_bridge_wp (Γ : Env)
    (hSt : ∀ a m Q X, fullSortTmpSpec a m Q X → Γ "full_sort_tmp" [i64] [] a m Q X)
    (hMm : ∀ a m Q X, fullMinMarkSpec a m Q X → Γ "full_min_mark" [i64, i32, i8] [] a m Q X)
    (hMl : ∀ a m Q X, fullMinLitSpec a m Q X → Γ "full_min_lit" [i64, i32] [.bool] a m Q X)
    (hSb : ∀ a m Q X, fullShrinkBlkSpec a m Q X →
      Γ "full_shrink_blk" [i64, i64, i64, i32, i64] [] a m Q X) :
    ∀ a m Q X, fullMinShrinkSpec a m Q X → Func.wp Γ full_min_shrink_body a m Q X :=
  full_min_shrink_spec_wp Γ hSt (fullMinMarkSpec_to_min hMm) (fullMinLitSpec_to_min hMl)
    (fullShrinkBlkSpec_to_min hSb)

end Part3

/-! ## Part 4: `FullDimacsBodyLemmas` (`3` fns) -/

section Part4

theorem full_skip_cl_bridge_wp (Γ : Env)
    (hLit : ∀ a m Q X, kissatNextLitSpec a m Q X → Γ "kissat_next_lit" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSkipClSpec a m Q X → Func.wp Γ full_skip_cl_body a m Q X :=
  full_skip_cl_wp Γ hLit

theorem full_ingest_cl_bridge_wp (Γ : Env)
    (hLit : ∀ a m Q X, kissatNextLitSpec a m Q X → Γ "kissat_next_lit" [i64, i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullIngestClSpec a m Q X → Func.wp Γ full_ingest_cl_body a m Q X :=
  full_ingest_cl_wp Γ hLit hAssign hAddCl

theorem full_parse_body_bridge_wp (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClSpec a m Q X → Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_body a m Q X :=
  full_parse_body_wp Γ hSkip hIngest hSwc

end Part4

end LeanQbe.T.Examples.Kissat.Full
