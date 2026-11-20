module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullHeurWalkLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Part 1a (`Stage 4`)

Bridges the first 11 `FullHeurWalkLemmas` functions onto canonical `FullSpec2` table entries:
`full_isqrt`, `full_ilog10`, `full_rng_next`, `full_wsort_sift`, `full_heap_up`,
`full_heap_down`, `full_heap_push`, `full_heap_pop`, `full_rescale`, `full_bump_var`,
`full_bump_decay`.
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

namespace FullBridgeHelpers

theorem probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem probePres_trans {s1 s2 s3 : FullState}
    (h12 : FullProbeScratchPres s1 s2) (h23 : FullProbeScratchPres s2 s3) :
    FullProbeScratchPres s1 s3 :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩,
    h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
    h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
    h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1, h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

theorem hlen_upd_scalar {c : FullCfg} {s s' : FullState}
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

theorem hlen_upd_hp_ps {c : FullCfg} {s : FullState}
    (hlen : FullState.LengthsOk c s) (hl' : Nat) (hp' ps' : List (BitVec 32))
    (hh : hp'.length = c.max_vars) (hp : ps'.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with
      heap_len := hl', heap := hp', pos := ps' } } :=
  hlen.with_scratch { hlen.scratch_ok with heap_len_arr := hh, pos_len := hp }

theorem hlen_upd_score {c : FullCfg} {s : FullState}
    (hlen : FullState.LengthsOk c s) (sc' : List (BitVec 64)) (hs : sc'.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with score := sc' } } :=
  hlen.with_scratch { hlen.scratch_ok with score_len := hs }

theorem hlen_upd_q {c : FullCfg} {s : FullState} (hlen : FullState.LengthsOk c s)
    {qf ql qsi qss qcs : BitVec 64} {qp qn qs : List (BitVec 32)}
    (hqp : qp.length = c.max_vars) (hqn : qn.length = c.max_vars)
    (hqs : qs.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with
      q_first := qf, q_last := ql, q_search_idx := qsi, q_search_stamp := qss,
      q_cur_stamp := qcs, q_prev := qp, q_next := qn, q_stamp := qs } } :=
  hlen.with_scratch { hlen.scratch_ok with
    q_prev_len := hqp, q_next_len := hqn, q_stamp_len := hqs }

theorem hlen_upd_phases {c : FullCfg} {s : FullState} (hlen : FullState.LengthsOk c s)
    {ta ba : BitVec 64} {pt pb : List (BitVec 8)}
    (hpt : pt.length = c.max_vars) (hpb : pb.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with
      target_assigned := ta, best_assigned := ba, phases_target := pt, phases_best := pb } } :=
  hlen.with_scratch { hlen.scratch_ok with
    phases_target_len := hpt, phases_best_len := hpb }

end FullBridgeHelpers

open FullBridgeHelpers

theorem full_isqrt_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullIsqrtSpec a m Q X → Func.wp Γ full_isqrt_body a m Q X :=
  full_isqrt_wp Γ

theorem full_ilog10_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullIlog10Spec a m Q X → Func.wp Γ full_ilog10_body a m Q X :=
  full_ilog10_wp Γ

theorem full_rng_next_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullRngNextSpec a m Q X → Func.wp Γ full_rng_next_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  c0_steps
  all_goals
    refine hQ _ _ _ ?_ ?_ ?_ hm
    · exact rfl
    · exact hlen_upd_scalar hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · exact rfl

theorem full_wsort_sift_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullWsortSiftSpec a m Q X → Func.wp Γ full_wsort_sift_body a m Q X := by
  rintro ⟨wvecPtr, wsPtr, start, n, ⟨⟩⟩ m Q X
    ⟨nlits, wvec, ws, R, hnlits, hsn, hn62, hn_ws, hlits, hheap, hm, hQ⟩
  apply full_wsort_sift_wp Γ
  refine ⟨wvec, ws, R, Nat.lt_trans hsn hn62, hn_ws, hn62, ?_, hm, ?_⟩
  · intro k hk; have := hlits k hk; omega
  · intro ws' m' hlen hperm hout _ hheap' hm'
    refine hQ ws' m' hlen hperm ?_ ?_ hm'
    · intro i hi
      by_cases hil : i < ws.length
      · exact hout i hi hil
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · have hmax : FullHeurWalkSpecs.fullWsortMaxHeap
          (FullHeurWalkSpecs.fullWsortKey wvec) ws start.toNat n.toNat start.toNat := by
        intro p hp hne
        have hp' : start.toNat + 1 ≤ p := by omega
        exact ⟨fun h1 => (hheap p hp' (by omega)).1 h1,
          fun h2 => (hheap p hp' (by omega)).2 h2⟩
      have hpar : FullHeurWalkSpecs.fullWsortHoleParent
          (FullHeurWalkSpecs.fullWsortKey wvec) ws start.toNat n.toNat start.toNat := by
        intro _ hle; omega
      have hres := hheap' start.toNat (le_refl _) hsn hmax hpar
      intro i hi0 hin
      simpa [FullHeurWalkSpecs.fullWsortKey] using hres i hi0 (by omega)

private theorem fullScratch_upd_hp_ps_eq {sc sc0 : FullScratch} {hp0 ps0 hp1 ps1 : List (BitVec 32)}
    (h : sc = { sc0 with heap := hp0, pos := ps0 }) :
    { sc with heap := hp1, pos := ps1 } = { sc0 with heap := hp1, pos := ps1 } := by
  subst h; rfl

theorem full_heap_up_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullHeapUpSpec a m Q X → Func.wp Γ full_heap_up_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len; obtain hsl := hsok.score_len
  c0_steps
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.heap, s.scratch.pos, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.heap, s.scratch.pos, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.heap, s.scratch.pos, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.heap, s.scratch.pos, rfl⟩ hm
  · obtain hv : v.toNat < s.core.cur_vars := by c0_bound
    obtain hp_lt : (s.scratch.pos[v.toNat]'(by omega)).toNat < s.core.cur_vars := by c0_bound
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
      (fun s1 (p, ()) => p.toNat < s.core.cur_vars ∧
        s1.scratch.heap_len = s.scratch.heap_len ∧ FullProbeScratchPres s s1 ∧
        ∃ hp' ps', s1.scratch = { s.scratch with heap := hp', pos := ps' })
      (fun (p, ()) => p.toNat)
      (fun J hLoop => ?_)
      (fun J s1 (p, ()) m1 hcore1 hlen1 ⟨hp1, hhl_eq, hpres1, hp1_l, ps1_l, hsc1⟩ hm1 hLoop1 => ?_)
    · c0_steps
      exact hLoop s (BitVec.setWidth 32 (s.scratch.pos[v.toNat]'(by omega)), ()) m hm rfl hlen
        ⟨by simpa [BitVec.toNat_setWidth] using hp_lt, rfl, probePres_refl s,
          s.scratch.heap, s.scratch.pos, rfl⟩
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok
      obtain hhl1 := hsok1.heap_len_arr; obtain hpl1 := hsok1.pos_len
      obtain hsl1 := hsok1.score_len
      c0_clean; c0_split
      · obtain hp0 : 0 < p.toNat := by c0_bound
        obtain hpp_lt : ((p - 1) >>> (1 : Nat)).toNat < p.toNat := by
          have hsub : (p - 1).toNat = p.toNat - 1 := by bv_omega
          rw [BitVec.toNat_ushiftRight, hsub]; simp [Nat.shiftRight_eq_div_pow]; omega
        obtain hpp_cv : ((p - 1) >>> (1 : Nat)).toNat < s.core.cur_vars := by omega
        obtain hpp64 : (BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat =
            ((p - 1) >>> (1 : Nat)).toNat := zext_toNat _ (by decide)
        have hpp_arr : (BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat <
            s1.scratch.heap.length := by rw [hhl1, hpp64]; omega
        c0_split
        · c0_steps
          refine hQ () _ m ?_ ?_ ?_ hm
          · exact hcore1.update _
          · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
          · exact ⟨hpres1, _, _, by dsimp only; rw [hsc1]⟩
        · obtain hpv_lt :
              (s1.scratch.heap[(BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat]'hpp_arr).toNat <
              s1.scratch.pos.length := by
            have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hceq1]
            have : (s1.scratch.heap[(BitVec.setWidth 64 ((p - 1) >>>
                (1 : Nat))).toNat]'hpp_arr).toNat < s.core.cur_vars := by
              rw [hceq1] at *; c0_bound
            omega
          c0_steps
          · refine hQ () _ m ?_ ?_ ?_ hm
            · exact hcore1.update _
            · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
            · exact ⟨hpres1, _, _, by dsimp only; rw [hsc1]⟩
          · refine hLoop1 _ ((p - 1) >>> (1 : Nat), ()) m hm (by dsimp only; omega) rfl ?_
              ⟨hpp_cv, hhl_eq, hpres1, _, _, fullScratch_upd_hp_ps_eq hsc1⟩
            exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
      · c0_steps
        refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1.update _
        · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
        · exact ⟨hpres1, _, _, by dsimp only; rw [hsc1]⟩

theorem full_heap_down_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullHeapDownSpec a m Q X → Func.wp Γ full_heap_down_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len; obtain hsl := hsok.score_len
  c0_steps
  · exact hQ () s m rfl hlen ⟨rfl, probePres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, probePres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, probePres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, probePres_refl s⟩ hm
  · obtain hv : v.toNat < s.core.cur_vars := by c0_bound
    obtain hhle : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ s.core.cur_vars := by c0_bound
    obtain hp0_lt : (s.scratch.pos[(v.setWidth 64).toNat]'(by
        rw [zext_toNat _ (by decide)]; omega)).toNat <
        (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
      have : (s.scratch.pos[(v.setWidth 64).toNat]'(by
          rw [zext_toNat _ (by decide)]; omega)).toNat < s.scratch.heap_len % 2 ^ 64 := by
        c0_bound
      simpa [BitVec.toNat_ofNat] using this
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
      (fun s1 (p, ()) => p.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧
        s1.scratch.heap_len = s.scratch.heap_len ∧ FullProbeScratchPres s s1)
      (fun (p, ()) => (BitVec.ofNat 64 s.scratch.heap_len).toNat - p.toNat)
      (fun J hLoop => ?_)
      (fun J s1 (p, ()) m1 hcore1 hlen1 ⟨hp, hhl_eq, hpres1⟩ hm1 hLoop1 => ?_)
    · c0_steps
      exact hLoop s (_, ()) m hm rfl hlen ⟨hp0_lt, rfl, probePres_refl s⟩
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok
      obtain hhl1 := hsok1.heap_len_arr; obtain hpl1 := hsok1.pos_len
      obtain hsl1 := hsok1.score_len
      obtain hp_mv : p.toNat < c.max_vars := by omega
      obtain hsh_p : (p.setWidth 64 <<< (1 : Nat)).toNat = 2 * p.toNat := by
        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq]; omega
      obtain hcp_toNat : ((p.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * p.toNat + 1 := by
        rw [BitVec.toNat_add, hsh_p]; simp; omega
      c0_split
      c0_split
      · c0_steps
        refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1.update _
        · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
        · exact ⟨hhl_eq, hpres1⟩
      · have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hceq1]
        have hhlen64 : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ c.max_vars := by omega
        have hcp_lt : 2 * p.toNat + 1 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
          have : (BitVec.setWidth 64 p <<< (1 : Nat) + 1).toNat <
              (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
          rw [hcp_toNat] at this; exact this
        have hcp_hlt : (BitVec.setWidth 64 p <<< (1 : Nat) + 1).toNat < s1.scratch.heap.length := by
          rw [hhl1, hcp_toNat]; omega
        c0_split
        · c0_steps
          refine hQ () _ m ?_ ?_ ?_ hm
          · exact hcore1.update _
          · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
          · exact ⟨hhl_eq, hpres1⟩
        · have hcv_lt : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
              1).toNat]'hcp_hlt).toNat < s.core.cur_vars := by
            have : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
                1).toNat]'hcp_hlt).toNat < s.core.cur_vars := by
              rw [hceq1] at *; c0_bound
            omega
          have hcv_sc : (BitVec.setWidth 64 (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
              1).toNat]'hcp_hlt)).toNat < s1.scratch.score.length := by
            rw [zext_toNat _ (by decide)]; omega
          c0_to_group
          · refine wp_join_group
              (fun (cp', cv', _csc', ()) m2 => p.toNat < cp'.toNat ∧
                cp'.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧
                cv'.toNat < s.core.cur_vars ∧ m1 = m2)
              (fun _ (cp', cv', csc', ()) m2 ⟨hgt, hlt, hcv_mv, hm2⟩ => ?_) ?_
            · rcases hm2 with rfl; c0_steps
              · refine hQ () _ m ?_ ?_ ?_ hm
                · exact hcore1.update _
                · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
                · exact ⟨hhl_eq, hpres1⟩
              · have hcp32 : (cp'.setWidth 32).toNat = cp'.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                refine hLoop1 _ (cp'.setWidth 32, ()) m hm (by dsimp only; omega) rfl ?_
                  ⟨by dsimp only; omega, hhl_eq, hpres1⟩
                exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
            · intro Jm hJm; c0_steps
              · have hsp_eq : (BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat =
                    2 * p.toNat + 2 := by
                  rw [BitVec.toNat_add, hcp_toNat]; simp; omega
                have hsp_lt : 2 * p.toNat + 2 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
                  have : (BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat <
                      (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
                  omega
                have hsv_mv : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat]'(
                    by rw [hhl1, hsp_eq]; omega)).toNat < s.core.cur_vars := by
                  rw [hceq1] at *; c0_bound
                have hsv_lt : (BitVec.setWidth 64
                    (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat]'(by
                      rw [hhl1, hsp_eq]; omega))).toNat < s1.scratch.score.length := by
                  rw [zext_toNat _ (by decide)]; omega
                c0_clean; c0_steps
                exact hJm ((BitVec.setWidth 64 p <<< (1 : Nat)) + 1 + 1, _, _, ()) m1
                  ⟨by rw [hsp_eq]; omega, by rw [hsp_eq]; omega, hsv_mv, rfl⟩
              all_goals
                refine hJm _ _ ⟨by rw [hcp_toNat]; omega, by rw [hcp_toNat]; omega, hcv_lt, rfl⟩
      · cases hc

theorem full_heap_push_bridge_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullHeapPushSpec a m Q X → Func.wp Γ full_heap_push_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len
  c0_steps
  · exact hQ () s m rfl hlen
      ⟨probePres_refl s, s.scratch.heap, s.scratch.pos, s.scratch.heap_len, rfl⟩ hm
  · exact hQ () s m rfl hlen
      ⟨probePres_refl s, s.scratch.heap, s.scratch.pos, s.scratch.heap_len, rfl⟩ hm
  · exact hQ () s m rfl hlen
      ⟨probePres_refl s, s.scratch.heap, s.scratch.pos, s.scratch.heap_len, rfl⟩ hm
  · refine wp_safety_slice_call hUp (fun _ => True) trivial rfl ?_ hm
      fun _ s' m' hcore' hlen' _ hpres' hm' => ?_
    · exact hlen_upd_hp_ps hlen _ _ _ (by simp [hhl]) (by simp [hpl])
    · dsimp only [fullSafetySlice] at hm' hlen'
      obtain ⟨hpr', hp', ps', hsc'⟩ := hpres'
      c0_steps
      exact hQ () s' m' ((PreservesCoreSlice.of_update _ s _ (fun _ => rfl)).trans hcore')
        hlen' ⟨hpr', hp', ps', _, by rw [hsc']⟩ hm'

theorem full_heap_pop_bridge_wp (Γ : Env)
    (hDown : ∀ a m Q X, fullHeapDownSpec a m Q X → Γ "full_heap_down" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullHeapPopSpec a m Q X → Func.wp Γ full_heap_pop_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len
  obtain hnlen_sub : 0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
      (BitVec.ofNat 64 s.scratch.heap_len - 1).toNat = s.scratch.heap_len - 1 :=
    fun ⟨hpos, hle⟩ => by
      have h1 := bv64_ofNat_toNat (n := s.scratch.heap_len) (by omega)
      have : 0 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by omega
      bv_omega
  c0_steps
  · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨Or.inl rfl, fun ⟨hpos, hle⟩ => by
      have h1 : (BitVec.ofNat 64 s.scratch.heap_len).toNat = 0 := by
        rw [bv64_ofNat_toNat (by omega)] at *; c0_bound
      rw [bv64_ofNat_toNat (by omega)] at h1; omega, probePres_refl s⟩ hm
  · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨Or.inl rfl, fun ⟨_, hle⟩ => by
      have h1 : s.core.cur_vars < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
      rw [bv64_ofNat_toNat (by omega)] at h1; omega, probePres_refl s⟩ hm
  all_goals first
  | (refine wp_safety_slice_call hDown (fun _ => True) trivial rfl ?_ hm
       fun _ s' m' hcore' hlen' _ ⟨hhl', hpres'⟩ hm' => ?_
     · exact hlen_upd_hp_ps hlen _ _ _ (by simp [hhl]) (by simp [hpl])
     · dsimp only [fullSafetySlice] at hm' hlen'
       c0_steps
       · exact hQ (0xFFFFFFFF#64, ()) s' m' hcore' hlen' ⟨Or.inl rfl, fun h => by
           rw [hhl']; exact hnlen_sub h, hpres'⟩ hm'
       · exact hQ _ s' m' hcore' hlen' ⟨Or.inr (by
           rw [fullCoreState_agrees_with_scratch hcore'] at *; c0_bound),
           fun h => by rw [hhl']; exact hnlen_sub h, hpres'⟩ hm')
  | (refine hQ (0xFFFFFFFF#64, ()) _ _ ?_ ?_ ?_ hm
     · exact rfl
     · exact hlen_upd_hp_ps hlen _ _ _ (by simp [hhl]) (by simp [hpl])
     · exact ⟨Or.inl rfl, hnlen_sub, probePres_refl s⟩)
  | (refine hQ _ _ _ ?_ ?_ ?_ hm
     · exact rfl
     · exact hlen_upd_hp_ps hlen _ _ _ (by simp [hhl]) (by simp [hpl])
     · exact ⟨Or.inr (by c0_bound), hnlen_sub, probePres_refl s⟩)

theorem full_rescale_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullRescaleSpec a m Q X → Func.wp Γ full_rescale_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok
  obtain hcv_le := hok.cur_vars_le
  c0_steps
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (v, ()) => v.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s1)
    (fun (v, ()) => s.core.cur_vars - v.toNat)
    (fun J hLoop => ?_)
    (fun J s1 (v, ()) m1 hcore1 hlen1 ⟨hv1, hpres1⟩ hm1 hLoop1 => ?_)
  · c0_steps; exact hLoop s (0#64, ()) m hm rfl hlen ⟨by simp, probePres_refl s⟩
  · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
    have hceq1 : s1.core = s.core := hcore1
    obtain hsok1 := hlen1.scratch_ok; obtain hsl1 := hsok1.score_len
    c0_clean; c0_steps
    · have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
        bv64_ofNat_toNat (by omega)
      have hv_lt : v.toNat < s.core.cur_vars := by
        have h1 : v.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
          rw [hceq1] at *; c0_bound
        omega
      have hvp1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
      refine hLoop1 _ (v + 1, ()) m hm (by dsimp only; omega) rfl ?_
        ⟨by dsimp only; omega, hpres1⟩
      exact hlen_upd_score hlen1 _ (by simp [hsl1])
    all_goals
      refine hQ () _ m ?_ ?_ ?_ hm
      · exact hcore1
      · exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact hpres1

theorem full_bump_var_bridge_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hRes : ∀ a m Q X, fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpVarSpec a m Q X → Func.wp Γ full_bump_var_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le; obtain hsl := hsok.score_len
  c0_steps
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  all_goals
    refine wp_safety_slice_call hUp (fun _ => True) trivial rfl ?_ hm
      fun _ s1 m1 hcore1 hlen1 _ hpres1 hm1 => ?_
    · exact hlen_upd_score hlen _ (by simp [hsl])
    · dsimp only [fullSafetySlice] at hm1 hlen1
      c0_steps
      all_goals first
      | (refine wp_safety_slice_call hRes (fun _ => True) trivial rfl hlen1 hm1
           fun _ s2 m2 hcore2 hlen2 _ hpres2 hm2 => ?_
         dsimp only [fullSafetySlice] at hm2 hlen2
         c0_steps
         exact hQ () s2 m2 (hcore1.trans hcore2) hlen2 (probePres_trans hpres1.1 hpres2) hm2)
      | exact hQ () s1 m1 hcore1 hlen1 hpres1.1 hm1

theorem full_bump_decay_bridge_wp (Γ : Env)
    (hRes : ∀ a m Q X, fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpDecaySpec a m Q X → Func.wp Γ full_bump_decay_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  c0_to_group
  refine wp_join_group
    (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
      s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ _ m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩ => ?_) ?_
  · c0_to_group
    refine wp_join_group
      (fun _ m2 => ∃ s2 : FullState, PreservesCoreSlice FullState.core s s2 ∧
        s2.LengthsOk c ∧ FullProbeScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ _ m2 ⟨s2, hcore2, hlen2, hpres2, hm2⟩ => ?_) ?_
    · c0_steps
      · refine wp_safety_slice_call hRes (fun _ => True) trivial rfl ?_ hm
          fun _ s3 m3 hcore3 hlen3 _ hpres3 hm3 => ?_
        · exact hlen_upd_scalar hlen2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        · dsimp only [fullSafetySlice] at hm3 hlen3
          c0_steps
          exact hQ () s3 m3 (hcore2.trans hcore3) hlen3 (probePres_trans hpres2 hpres3) hm3
      · refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore2
        · exact hlen_upd_scalar hlen2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        · exact hpres2
    · intro J2 hJ2; c0_steps
      all_goals first
      | (refine wp_safety_slice_call hRes (fun _ => True) trivial rfl hlen1 hm1
           fun _ s2 m2 hcore2 hlen2 _ hpres2 hm2 => ?_
         dsimp only [fullSafetySlice] at hm2 hlen2
         c0_steps
         exact hJ2 _ _ ⟨s2, hcore1.trans hcore2, hlen2, probePres_trans hpres1 hpres2, hm2⟩)
      | exact hJ2 _ _ ⟨s1, hcore1, hlen1, hpres1, hm1⟩
  · intro J1 hJ1; c0_steps
    · exact hJ1 _ _ ⟨s, rfl, hlen, probePres_refl s, hm⟩
    · exact hJ1 _ _ ⟨s, rfl, hlen, probePres_refl s, hm⟩

end LeanQbe.T.Examples.Kissat.Full
