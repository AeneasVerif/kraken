module

public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
public import LeanQbe.T.Examples.Kissat.FullMinLemmas
public import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Parts 1b–4 (`Stage 4`)

Bridges canonical `FullSpec2`/`FullSpec3` table entries across the first 4 shards:
- Part 1b (`FullHeurWalkLemmas`, #12–17): `full_queue_renumber`, `full_queue_mtf`,
  `full_tick_rel`, `full_ema_update`, `full_save_target_best`, `full_recompute_tiers`.
- Part 2 (`FullPropDecLemmas`): `full_find_repl`, `full_decide`, `full_rephase`, `full_restart`.
- Part 3 (`FullMinLemmas`): `full_tmp_less`, `full_min_mark`.
- Part 4 (`FullDimacsBodyLemmas`): `full_skip_cl`, `full_parse_body`.
-/

set_option autoImplicit false

@[expose] public section

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
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩ => ?_) ?_
    · rw [Blocks.get_here]
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok; obtain hpbl1 := hsok1.phases_best_len
      c0_clean; c0_steps
      · refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s1 R
          (fun s2 (k, ()) => k.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s1 s2)
          (fun (k, ()) => s.core.cur_vars - k.toNat)
          (fun J hLoop => ?_)
          (fun J s2 (k, ()) m2 hcore2 hlen2 ⟨hk2, hpres2⟩ hm2 hLoop2 => ?_)
        · c0_steps
          refine hLoop _ (0#64, ()) m hm rfl ?_ ⟨by simp, probePres_refl s1⟩
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
              ⟨by dsimp only; omega, hpres2⟩
            exact hlen_upd_phases hlen2 hsok2.phases_target_len (by simp [hpbl2])
          · exact hQ () s2 m2 (hcore1.trans hcore2) hlen2 (probePres_trans hpres1 hpres2) hm2
      · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1
    · intro J1 hJ1; c0_steps
      · obtain hsok := hlen.scratch_ok; obtain hptl := hsok.phases_target_len
        refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s R
          (fun s1 (k, ()) => k.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s1)
          (fun (k, ()) => s.core.cur_vars - k.toNat)
          (fun J hLoop => ?_)
          (fun J s1 (k, ()) m1 hcore1 hlen1 ⟨hk1, hpres1⟩ hm1 hLoop1 => ?_)
        · c0_steps
          refine hLoop _ (0#64, ()) m hm rfl ?_ ⟨by simp, probePres_refl s⟩
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
              ⟨by dsimp only; omega, hpres1⟩
            exact hlen_upd_phases hlen1 (by simp [hptl1]) hsok1.phases_best_len
          · exact hJ1 () m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩
      · exact hJ1 () m ⟨s, rfl, hlen, probePres_refl s, hm⟩

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

end Part2

/-! ## Part 3: `FullMinLemmas` (`2` fns) -/

section Part3

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
      dsimp only [fullMinMarkState] at hQ
      simp only [hcur_f, false_and, ↓reduceIte] at hQ
      exact hQ m' hm'
    · next hncur =>
      have hcur0 : s.core.mrk[v.toNat]?.getD 0#8 = 0#8 := Classical.byContradiction hncur
      split
      · next hlt =>
        intro m' hm'
        have hbv : BitVec.ofNat 32 v.toNat = v := by bv_omega
        dsimp only [fullMinMarkState] at hQ
        simp only [hcur0, true_and, hlt, ↓reduceIte, not_true_eq_false, hbv] at hQ
        simp only [hcur0] at hm'
        exact hQ m' hm'
      · next hge =>
        intro m' hm'
        dsimp only [fullMinMarkState] at hQ
        simp only [hcur0, true_and, hge, ↓reduceIte] at hQ
        simp only [hcur0] at hm'
        exact hQ m' hm'

end Part3

/-! ## Part 4: `FullDimacsBodyLemmas` (`2` fns) -/

section Part4

theorem full_skip_cl_bridge_wp (Γ : Env)
    (hLit : ∀ a m Q X, kissatNextLitSpec a m Q X → Γ "kissat_next_lit" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSkipClSpec a m Q X → Func.wp Γ full_skip_cl_body a m Q X :=
  full_skip_cl_wp Γ hLit

theorem full_parse_body_bridge_wp (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClSpec a m Q X → Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_body a m Q X :=
  full_parse_body_wp Γ hSkip hIngest hSwc

end Part4

end LeanQbe.T.Examples.Kissat.Full
