module

public import LeanQbe.T.Examples.Kissat.FullHeurWalkLemmas1

/-!
# Kissat `D-Full` Heuristic & Pure `Func.wp` Proofs — Part 2 (`Stage 4`)

Proves parametric `(Γ : Env)` `Func.wp` theorems for the remaining 6 `Full1.lean` functions:
12. `full_queue_renumber`, 13. `full_queue_mtf`, 14. `full_tick_rel`,
15. `full_ema_update`, 16. `full_save_target_best`, 17. `full_recompute_tiers`.
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

open scoped FullArenaTactics FullHeurWalkTactics
open FullHeurWalkSpecs

private theorem hlen_upd_scalar {c : FullCfg} {s s' : FullState}
    (h : FullState.LengthsOk c s) (hc : s'.core = s.core)
    (hs1 : s'.scratch.walk_vals = s.scratch.walk_vals)
    (hs2 : s'.scratch.phases = s.scratch.phases)
    (hs3 : s'.scratch.phases_target = s.scratch.phases_target)
    (hs4 : s'.scratch.phases_best = s.scratch.phases_best)
    (hs5 : s'.scratch.walk_best = s.scratch.walk_best)
    (hs6 : s'.scratch.heap = s.scratch.heap) (hs7 : s'.scratch.pos = s.scratch.pos)
    (hs8 : s'.scratch.shrink_stk = s.scratch.shrink_stk)
    (hs9 : s'.scratch.q_prev = s.scratch.q_prev) (hs10 : s'.scratch.q_next = s.scratch.q_next)
    (hs11 : s'.scratch.q_stamp = s.scratch.q_stamp) (hs12 : s'.scratch.wsort = s.scratch.wsort)
    (hs13 : s'.scratch.work_stk1 = s.scratch.work_stk1)
    (hs14 : s'.scratch.work_stk2 = s.scratch.work_stk2)
    (hs15 : s'.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (hs16 : s'.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hs17 : s'.scratch.score = s.scratch.score) (hs18 : s'.scratch.sim_sig = s.scratch.sim_sig)
    (hs19 : s'.scratch.glue_used = s.scratch.glue_used)
    (hs20 : s'.scratch.last_learned = s.scratch.last_learned)
    (hs21 : s'.scratch.delayed = s.scratch.delayed)
    (hs22 : s'.scratch.red_refs = s.scratch.red_refs)
    (hs23 : s'.scratch.extend_stk = s.scratch.extend_stk)
    (hs24 : s'.scratch.scratch_buf = s.scratch.scratch_buf) : FullState.LengthsOk c s' :=
  ⟨hc ▸ h.core_ok,
    { walk_vals_len := hs1 ▸ h.scratch_ok.walk_vals_len
      phases_len := hs2 ▸ h.scratch_ok.phases_len
      phases_target_len := hs3 ▸ h.scratch_ok.phases_target_len
      phases_best_len := hs4 ▸ h.scratch_ok.phases_best_len
      walk_best_len := hs5 ▸ h.scratch_ok.walk_best_len
      heap_len_arr := hs6 ▸ h.scratch_ok.heap_len_arr
      pos_len := hs7 ▸ h.scratch_ok.pos_len
      shrink_stk_len := hs8 ▸ h.scratch_ok.shrink_stk_len
      q_prev_len := hs9 ▸ h.scratch_ok.q_prev_len
      q_next_len := hs10 ▸ h.scratch_ok.q_next_len
      q_stamp_len := hs11 ▸ h.scratch_ok.q_stamp_len
      wsort_len := hs12 ▸ h.scratch_ok.wsort_len
      work_stk1_len := hs13 ▸ h.scratch_ok.work_stk1_len
      work_stk2_len := hs14 ▸ h.scratch_ok.work_stk2_len
      tarjan_mark_len := hs15 ▸ h.scratch_ok.tarjan_mark_len
      tarjan_reach_len := hs16 ▸ h.scratch_ok.tarjan_reach_len
      score_len := hs17 ▸ h.scratch_ok.score_len
      sim_sig_len := hs18 ▸ h.scratch_ok.sim_sig_len
      glue_used_len := hs19 ▸ h.scratch_ok.glue_used_len
      last_learned_len := hs20 ▸ h.scratch_ok.last_learned_len
      delayed_len_arr := hs21 ▸ h.scratch_ok.delayed_len_arr
      red_refs_len := hs22 ▸ h.scratch_ok.red_refs_len
      extend_stk_len := hs23 ▸ h.scratch_ok.extend_stk_len
      scratch_buf_len := hs24 ▸ h.scratch_ok.scratch_buf_len }⟩

private theorem hlen_upd_q {c : FullCfg} {s : FullState} (hlen : FullState.LengthsOk c s)
    {qf ql qsi qss qcs : BitVec 64} {qp qn qs : List (BitVec 32)}
    (hqp : qp.length = c.max_vars) (hqn : qn.length = c.max_vars)
    (hqs : qs.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with
      q_first := qf, q_last := ql, q_search_idx := qsi, q_search_stamp := qss,
      q_cur_stamp := qcs, q_prev := qp, q_next := qn, q_stamp := qs } } :=
  hlen.with_scratch { hlen.scratch_ok with
    q_prev_len := hqp, q_next_len := hqn, q_stamp_len := hqs }

private theorem hlen_upd_phases {c : FullCfg} {s : FullState} (hlen : FullState.LengthsOk c s)
    {ta ba : BitVec 64} {pt pb : List (BitVec 8)}
    (hpt : pt.length = c.max_vars) (hpb : pb.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with
      target_assigned := ta, best_assigned := ba, phases_target := pt, phases_best := pb } } :=
  hlen.with_scratch { hlen.scratch_ok with
    phases_target_len := hpt, phases_best_len := hpb }

/-! ## 5. VMTF queue (`full_queue_renumber`, `full_queue_mtf`) -/

theorem full_queue_renumber_wp (Γ : Env) :
    ∀ a m Q X, fullQueueRenumberSpec a m Q X → Func.wp Γ full_queue_renumber_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hcv_le := hok.cur_vars_le
  c0_steps
  refine wp_loop_safety_slice_pure (ts := [i32, i64, i64]) (fullSafetySlice c) s R
    (fun s1 (_st, _cur, steps, ()) => steps.toNat ≤ s.core.cur_vars ∧
      s1.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len)
    (fun (_st, _cur, steps, ()) => s.core.cur_vars - steps.toNat)
    (fun J hLoop => ?_)
    (fun J s1 (st, cur, steps, ()) m1 hcore1 hlen1 ⟨hsle, hw_eq, hll_eq, hel_eq⟩ hm1 hLoop1 =>
      ?_)
  · c0_steps; exact hLoop s _ m hm rfl hlen ⟨by simp, rfl, rfl, rfl⟩
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
        ⟨by dsimp only; omega, hw_eq, hll_eq, hel_eq⟩
      exact hlen_upd_q hlen1 hsok1.q_prev_len hqnl1 (by simp [hqsl1])
    all_goals
      refine hQ () _ m ?_ ?_ ?_ hm <;>
        first
        | exact hcore1
        | exact hlen_upd_q hlen1 hsok1.q_prev_len hqnl1 hqsl1
        | exact ⟨hw_eq, hll_eq, hel_eq⟩

theorem full_queue_mtf_wp (Γ : Env)
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
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl⟩ hm
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
        s1.LengthsOk c ∧ s1.scratch.work_stk1 = s.scratch.work_stk1 ∧
        s1.scratch.last_learned = s.scratch.last_learned ∧
        s1.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hw1, hll1, hel1, hm1⟩ => ?_) ?_
    · have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok
      obtain hqpl1 := hsok1.q_prev_len; obtain hqnl1 := hsok1.q_next_len
      c0_to_group
      refine wp_join_group
        (fun _ m2 => ∃ s2 : FullState, PreservesCoreSlice FullState.core s s2 ∧
          s2.LengthsOk c ∧ s2.scratch.work_stk1 = s.scratch.work_stk1 ∧
          s2.scratch.last_learned = s.scratch.last_learned ∧
          s2.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ _ m2 ⟨s2, hcore2, hlen2, hw2, hll2, hel2, hm2⟩ => ?_) ?_
      · have hceq2 : s2.core = s.core := hcore2
        obtain hsok2 := hlen2.scratch_ok
        obtain hqpl2 := hsok2.q_prev_len; obtain hqnl2 := hsok2.q_next_len
        c0_to_group
        refine wp_join_group
          (fun _ m3 => ∃ s3 : FullState, PreservesCoreSlice FullState.core s s3 ∧
            s3.LengthsOk c ∧ s3.scratch.work_stk1 = s.scratch.work_stk1 ∧
            s3.scratch.last_learned = s.scratch.last_learned ∧
            s3.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s3 ⋆ R) m3)
          (fun _ _ m3 ⟨s3, hcore3, hlen3, hw3, hll3, hel3, hm3⟩ => ?_) ?_
        · have hceq3 : s3.core = s.core := hcore3
          obtain hsok3 := hlen3.scratch_ok
          obtain hqpl3 := hsok3.q_prev_len; obtain hqnl3 := hsok3.q_next_len
          c0_to_group
          refine wp_join_group
            (fun _ m4 => ∃ s4 : FullState, PreservesCoreSlice FullState.core s s4 ∧
              s4.LengthsOk c ∧ s4.scratch.work_stk1 = s.scratch.work_stk1 ∧
              s4.scratch.last_learned = s.scratch.last_learned ∧
              s4.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s4 ⋆ R) m4)
            (fun _ _ m4 ⟨s4, hcore4, hlen4, hw4, hll4, hel4, hm4⟩ => ?_) ?_
          · have hceq4 : s4.core = s.core := hcore4
            obtain hsok4 := hlen4.scratch_ok
            obtain hqnl4 := hsok4.q_next_len; obtain hqsl4 := hsok4.q_stamp_len
            c0_to_group
            refine wp_join_group
              (fun _ m5 => ∃ s5 : FullState, PreservesCoreSlice FullState.core s s5 ∧
                s5.LengthsOk c ∧ s5.scratch.work_stk1 = s.scratch.work_stk1 ∧
                s5.scratch.last_learned = s.scratch.last_learned ∧
                s5.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s5 ⋆ R) m5)
              (fun _ _ m5 ⟨s5, hcore5, hlen5, hw5, hll5, hel5, hm5⟩ => ?_) ?_
            · have hceq5 : s5.core = s.core := hcore5
              obtain hsok5 := hlen5.scratch_ok
              obtain hqsl5 := hsok5.q_stamp_len
              have hv2_5 : (v.setWidth 64 <<< (1 : Nat)).toNat < s5.core.vals.length := by
                rw [hceq5]; exact hv2
              c0_clean; c0_steps
              · refine hQ () _ m ?_ ?_ ?_ hm
                · exact hcore5
                · exact hlen_upd_q hlen5 hsok5.q_prev_len hsok5.q_next_len hqsl5
                · exact ⟨hw5, hll5, hel5⟩
              · exact hQ () s5 m5 hcore5 hlen5 ⟨hw5, hll5, hel5⟩ hm5
            · intro J5 hJ5; c0_steps
              · refine wp_safety_slice_call hRen (fun _ => True) trivial rfl hlen4 hm4
                  fun _ s5 m5 hcore5 hlen5 _ ⟨hw5, hll5, hel5⟩ hm5 => ?_
                dsimp only [fullSafetySlice] at hm5 hlen5
                c0_steps
                exact hJ5 () m5 ⟨s5, hcore4.trans hcore5, hlen5, hw5.trans hw4,
                  hll5.trans hll4, hel5.trans hel4, hm5⟩
              · refine hJ5 () m ⟨_, ?_, ?_, ?_, ?_, ?_, hm⟩
                · exact hcore4
                · exact hlen_upd_q hlen4 hsok4.q_prev_len hqnl4 (by simp [hqsl4])
                · exact hw4
                · exact hll4
                · exact hel4
          · intro J4 hJ4; c0_steps
            all_goals
              refine hJ4 () m ⟨_, ?_, ?_, ?_, ?_, ?_, hm⟩
              · exact hcore3
              · exact hlen_upd_q hlen3 (by simp [hqpl3]) (by simp [hqnl3]) hsok3.q_stamp_len
              · exact hw3
              · exact hll3
              · exact hel3
        · intro J3 hJ3; c0_steps
          · refine hJ3 () m ⟨_, ?_, ?_, ?_, ?_, ?_, hm⟩
            · exact hcore2
            · exact hlen_upd_q hlen2 hqpl2 hqnl2 hsok2.q_stamp_len
            · exact hw2
            · exact hll2
            · exact hel2
          · have hv_eq : (BitVec.setWidth 64 v).toNat = v.toNat := zext_toNat v (by decide)
            have hnv_lt : (BitVec.setWidth 64 (s1.scratch.q_next[(BitVec.setWidth 64 v).toNat]'(
                by rw [hqnl1]; omega))).toNat < s2.scratch.q_prev.length := by
              have h1 : (s1.scratch.q_next[(BitVec.setWidth 64 v).toNat]'(
                  by rw [hqnl1]; omega)).toNat < s.core.cur_vars % 2 ^ 64 := by
                simp only [hv_eq]; omega
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
            c0_clean; c0_steps
            refine hJ3 () m ⟨_, ?_, ?_, ?_, ?_, ?_, hm⟩
            · exact hcore2
            · exact hlen_upd_q hlen2 (by simp [hqpl2]) hqnl2 hsok2.q_stamp_len
            · exact hw2
            · exact hll2
            · exact hel2
      · intro J2 hJ2; c0_steps
        · refine hJ2 () m ⟨_, ?_, ?_, ?_, ?_, ?_, hm⟩
          · exact hcore1
          · exact hlen_upd_q hlen1 (by simp [hqpl1]) (by simp [hqnl1]) hsok1.q_stamp_len
          · exact hw1
          · exact hll1
          · exact hel1
        · have hpv_lt : (BitVec.setWidth 64 (s1.scratch.q_prev[(BitVec.setWidth 64 v).toNat]'(
              by rw [hqpl1]; omega))).toNat < s1.scratch.q_next.length := by
            have h1 : (s1.scratch.q_prev[(BitVec.setWidth 64 v).toNat]'(
                by rw [hqpl1]; omega)).toNat < s1.core.cur_vars % 2 ^ 64 := by
              rw [hceq1]; c0_bound
            rw [hceq1] at h1
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
            rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
          c0_clean; c0_steps
          refine hJ2 () m ⟨_, ?_, ?_, ?_, ?_, ?_, hm⟩
          · exact hcore1
          · exact hlen_upd_q hlen1 (by simp [hqpl1]) (by simp [hqnl1]) hsok1.q_stamp_len
          · exact hw1
          · exact hll1
          · exact hel1
    · intro J1 hJ1; c0_steps
      all_goals
        refine hJ1 () m ⟨_, ?_, ?_, ?_, ?_, ?_, hm⟩ <;>
          first
          | exact rfl
          | exact hlen_upd_q hlen hqpl hqnl hqsl

/-! ## 6. Reluctant doubling & EMA (`full_tick_rel`, `full_ema_update`) -/

theorem full_tick_rel_wp (Γ : Env) :
    ∀ a m Q X, fullTickRelSpec a m Q X → Func.wp Γ full_tick_rel_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  c0_to_group
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ s1.scratch.last_learned = s.scratch.last_learned ∧
        s1.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hll1, hel1, hm1⟩ => ?_) ?_
    · c0_to_group
      · exact hQ () s1 m1 hcore1 hlen1 ⟨hll1, hel1⟩ hm1
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
                · exact ⟨hll1, hel1⟩
            · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
          · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
        · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
    · intro Jm hJm; c0_steps
      · refine hJm _ _ ⟨_, ?_, ?_, ?_, ?_, hm⟩
        · exact rfl
        · exact hlen_upd_scalar hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        · exact rfl
        · exact rfl
      · exact hJm _ _ ⟨s, rfl, hlen, rfl, rfl, hm⟩

theorem full_ema_update_wp (Γ : Env) :
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
          s1.LengthsOk c ∧ s1.scratch.last_learned = s.scratch.last_learned ∧
          s1.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s1 ⋆ R) m3)
        (fun _ _ m3 ⟨s1, hcore1, hlen1, hll1, hel1, hm3⟩ => ?_) ?_
      · c0_to_group
        refine wp_join_group (fun _ m4 => m3 = m4) (fun _ _ m4 hm4 => ?_) ?_
        · rcases hm4 with rfl; c0_steps
          all_goals
            refine hQ () _ m ?_ ?_ ?_ hm
            · exact hcore1
            · exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            · exact ⟨hll1, hel1⟩
        · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
      · intro Jm hJm; c0_steps
        all_goals
          refine hJm _ _ ⟨_, ?_, ?_, ?_, ?_, hm⟩
          · exact rfl
          · exact hlen_upd_scalar hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          · exact rfl
          · exact rfl
    · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
  · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl

/-! ## 7. Target/best phases & tiers (`full_save_target_best`, `full_recompute_tiers`) -/

theorem full_save_target_best_wp (Γ : Env) :
    ∀ a m Q X, fullSaveTargetBestSpec a m Q X → Func.wp Γ full_save_target_best_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hcv_le := hok.cur_vars_le; obtain hvl := hok.vals_len
  c0_to_group
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ s1.scratch.last_learned = s.scratch.last_learned ∧
        s1.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hll1, hel1, hm1⟩ => ?_) ?_
    · rw [Blocks.get_here]
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok; obtain hpbl1 := hsok1.phases_best_len
      c0_clean; c0_steps
      · refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s1 R
          (fun s2 (k, ()) => k.toNat ≤ s.core.cur_vars ∧
            s2.scratch.last_learned = s.scratch.last_learned ∧
            s2.scratch.extend_len = s.scratch.extend_len)
          (fun (k, ()) => s.core.cur_vars - k.toNat)
          (fun J hLoop => ?_)
          (fun J s2 (k, ()) m2 hcore2 hlen2 ⟨hk2, hll2, hel2⟩ hm2 hLoop2 => ?_)
        · c0_steps
          refine hLoop _ (0#64, ()) m hm rfl ?_ ⟨by simp, hll1, hel1⟩
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
              ⟨by dsimp only; omega, hll2, hel2⟩
            exact hlen_upd_phases hlen2 hsok2.phases_target_len (by simp [hpbl2])
          · exact hQ () s2 m2 (hcore1.trans hcore2) hlen2 ⟨hll2, hel2⟩ hm2
      · exact hQ () s1 m1 hcore1 hlen1 ⟨hll1, hel1⟩ hm1
    · intro J1 hJ1; c0_steps
      · obtain hsok := hlen.scratch_ok; obtain hptl := hsok.phases_target_len
        refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s R
          (fun s1 (k, ()) => k.toNat ≤ s.core.cur_vars ∧
            s1.scratch.last_learned = s.scratch.last_learned ∧
            s1.scratch.extend_len = s.scratch.extend_len)
          (fun (k, ()) => s.core.cur_vars - k.toNat)
          (fun J hLoop => ?_)
          (fun J s1 (k, ()) m1 hcore1 hlen1 ⟨hk1, hll1, hel1⟩ hm1 hLoop1 => ?_)
        · c0_steps
          refine hLoop _ (0#64, ()) m hm rfl ?_ ⟨by simp, rfl, rfl⟩
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
              ⟨by dsimp only; omega, hll1, hel1⟩
            exact hlen_upd_phases hlen1 (by simp [hptl1]) hsok1.phases_best_len
          · exact hJ1 () m1 ⟨s1, hcore1, hlen1, hll1, hel1, hm1⟩
      · exact hJ1 () m ⟨s, rfl, hlen, rfl, rfl, hm⟩

theorem full_recompute_tiers_wp (Γ : Env) :
    ∀ a m Q X, fullRecomputeTiersSpec a m Q X →
      Func.wp Γ full_recompute_tiers_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hsok := hlen.scratch_ok; obtain hgl := hsok.glue_used_len
  c0_steps
  refine wp_loop_safety_slice_pure (ts := [i64, i64]) (fullSafetySlice c) s R
    (fun s1 (tot, g, ()) => g.toNat ≤ 64 ∧
      s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len)
    (fun (_tot, g, ()) => 64 - g.toNat)
    (fun J hLoop => ?_)
    (fun J s1 (tot, g, ()) m1 hcore1 hlen1 ⟨hg1, hll1, hel1⟩ hm1 hLoop1 => ?_)
  · c0_steps; exact hLoop s _ m hm rfl hlen ⟨by simp, rfl, rfl⟩
  · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
    obtain hsok1 := hlen1.scratch_ok; obtain hgl1 := hsok1.glue_used_len
    c0_clean; c0_steps
    · have hg_lt : g.toNat < 64 := by c0_bound
      have hgp1 : (g + 1).toNat = g.toNat + 1 := by bv_omega
      c0_clean; c0_steps
      exact hLoop1 _ (_, g + 1, ()) m1 hm1 (by dsimp only; omega) rfl hlen1
        ⟨by dsimp only; omega, hll1, hel1⟩
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
              | exact ⟨hll1, hel1⟩)
        · c0_steps
          all_goals
            refine hQ () _ m ?_ ?_ ?_ hm <;>
              first
              | exact hcore1
              | exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              | exact ⟨hll1, hel1⟩
    · refine hQ () _ m ?_ ?_ ?_ hm
      · exact hcore1
      · exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact ⟨hll1, hel1⟩

end LeanQbe.T.Examples.Kissat.Full
