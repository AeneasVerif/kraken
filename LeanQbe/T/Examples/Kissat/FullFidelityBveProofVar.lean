/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofVar0
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVE Parity Proofs — Part Var (`full_elim_bve_m7`, `full_eliminate_m6`)

UNSAT-only `Func.wp` proofs (`public section`, `0` `@[expose]`, `0` `*Lemmas*` in `public import`,
`XPost := False`, `std3` axioms only):
1. `full_elim_bve_m7_fid_wp`: certifies canonical `FullM3CongBva.m3ElimBveSpec` for
   `FullFidelityBve.full_elim_bve_m7_body` (resets `res_sz = 0`, checks `res_sz > res_lim`,
   decrements `fuel`, flushes units after each var, `0` `bce_cnt`).
2. `full_eliminate_m6_fid_wp`: certifies canonical `FullFastSched.schedEliminateSpec` for
   `FullFidelityBve.full_eliminate_m6_body` (Q16 `full_log10_q16_m7`, `res_lim`, no `full_factor`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics

/-! ## 1. Private Framing Helpers -/

private theorem fid_elim_denseInv_with_ws1_ss {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {ws1' : List (BitVec 32)} {ss' : List (BitVec 64)}
    (hws1 : ws1'.length = 2 * c.max_vars) (hss : ss'.length = c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  let sc' : FullScratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' }
  exact (m6_fullDenseInvW_with_scratch hdw (sc' := sc')
    { hdw.1.scratch_ok with work_stk1_len := hws1, sim_sig_len := hss } rfl rfl).toDense

private theorem fid_elim_denseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {scr' : FullScratch}
    (hok : scr'.LengthsOk c) (hll : scr'.last_learned = s.scratch.last_learned)
    (hel : scr'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := scr' } :=
  fullDenseInv_with_scratch_keep h hok hll hel

private theorem fid_elim_sparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {scr' : FullScratch}
    (hok : scr'.LengthsOk c) (hll : scr'.last_learned = s.scratch.last_learned)
    (hel : scr'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := scr' } :=
  fullSparseInv_with_scratch_keep h hok hll hel

private theorem fid_elim_tmkZero_of_init {s : FullState} {tmki : List (BitVec 32)}
    (hinit : ∀ k < s.core.cur_vars, tmki[k]?.getD 0#32 = 0#32) :
    TmkZero { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fun v hv => hinit v hv

private theorem fid_elim_denseInv_with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } :=
  fullDenseInv_with_flags h hfl

private theorem fid_elim_denseInv_with_flags_fuel {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars)
    (fuel' : BitVec 64) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl', fuel := fuel' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  exact (m8_fullDenseInvW_fuel (m6_fullDenseInvW_with_flags hdw hfl) fuel').toDense

/-! ## 2. `full_elim_bve_m7_fid_wp` (Canonical `FullM3CongBva.m3ElimBveSpec`) -/

/-- Certifies canonical `FullM3CongBva.m3ElimBveSpec` for
`FullFidelityBve.full_elim_bve_m7_body` (resets `h->res_sz = 0`, checks `h->res_sz > res_lim`,
decrements `h->fuel`, calls `full_dense_flush_units_m7` after each var, `0` `bce_cnt`). -/
theorem full_elim_bve_m7_fid_wp (Γ : Env)
    (hPop : ∀ a m Q X, FullM6BveFwd.fullBveHeapPopM6Spec a m Q X →
      Γ "full_bve_heap_pop_m7" [i64, i64] [i32] a m Q X)
    (hNbrs : ∀ a m Q X, FullM3CongBva.m3ElimCollectNbrsSpec a m Q X →
      Γ "full_bve_collect_nbrs_m7" [i64, i32] [i64] a m Q X)
    (hVar : ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X)
    (hFlush : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, FullM8CoreParity.m8BveHeapPushSpec a m Q X →
      Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Func.wp Γ FullFidelityBve.full_elim_bve_m7_body a m Q X := by
  rintro ⟨h, res_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, htmk0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv0_le := hden0.lengths.core_ok.cur_vars_le
  have hmcl0 := hden0.lengths.core_ok.min_clr_len_arr
  unfold Func.wp FullFidelityBve.full_elim_bve_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem_c (ci, ()) mc => ∃ mclrc : List (BitVec 32),
      mclrc.length = c.max_vars ∧ ci.toNat ≤ s0.core.cur_vars ∧
      rem_c = s0.core.cur_vars - ci.toNat ∧
      (FullMem c { s0 with core := { s0.core with min_clr := mclrc } } ⋆ R) mc)
    ?_ (fun Lc hLc => by
      c0_hsteps!
      exact hLc s0.core.cur_vars (0#64, ()) m0
        ⟨s0.core.min_clr, hmcl0, Nat.zero_le _, by simp, hm0⟩)
  rintro Lc rem_c ⟨ci, ⟨⟩⟩ mc hLc ⟨mclrc, hmclrc, hci_le, rfl, hmc⟩
  c0_hsplit
  · have hci_lt : ci.toNat < s0.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hmcl_b : ci.toNat < mclrc.length := by omega
    have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps!
    exact hLc (s0.core.cur_vars - (ci + 1#64).toNat) (ci + 1#64, ()) _ (by omega)
      ⟨_, by simp [hmclrc], by omega, rfl, hm⟩
  let sz : FullState :=
    { s0 with
      core := { s0.core with min_clr := mclrc }
      scratch := { s0.scratch with res_sz := 0#64 } }
  have hdenz : FullDenseInv c F0 sz := by
    obtain ⟨F_cur, hw0⟩ := hden0.exists_witness
    exact FullDenseInvW.toDense
      ⟨⟨{ hw0.1.core_ok with min_clr_len_arr := hmclrc },
        { hw0.1.scratch_ok with walk_vals_len := hw0.1.scratch_ok.walk_vals_len }⟩,
       fullWitnessInv_with_min_clr hw0.2.1 mclrc, hw0.2.2.1, hw0.2.2.2.1,
       hw0.2.2.2.2.1, hw0.2.2.2.2.2.1, hw0.2.2.2.2.2.2⟩
  have htmkz : TmkZero sz := htmk0.congr rfl rfl
  c0_hsteps_nogrp
  refine wp_loop_break_group (brkTs := [.bool, i64, .bool, i64]) (lpTs := [.bool, i64, .bool, i64])
    (fun (_hl, _hln, _lre, _rd, ()) mb => ∃ sb : FullState,
      FullDenseInv c F0 sb ∧ TmkZero sb ∧ sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sb ⋆ R) mb)
    (fun rem_r (hit_lim, hlen, _lre, round, ()) mr => ∃ sr : FullState,
      round.toNat ≤ 2 ∧ rem_r = 2 - round.toNat ∧
      hlen.toNat ≤ sr.core.cur_vars ∧
      FullDenseInv c F0 sr ∧ TmkZero sr ∧ sr.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sr ⋆ R) mr)
    ?_ ?_ ?_
  · rintro _ ⟨_hl, _hln, _lre, _rd, ⟨⟩⟩ mb ⟨sb, hdenb, htmkb, hfub, hmb⟩
    c0_hsteps_nogrp
    refine wp_join0 (P := fun mf => ∃ sf : FullState,
      FullDenseInv c F0 sf ∧ TmkZero sf ∧ sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sf ⋆ R) mf)
      (fun _ mf ⟨sf, hdenf, htmkf, hfuf, hmf⟩ => by
        c0_hsteps!
        · exact hQ 20#64 sf mf hdenf htmkf hfuf (Or.inr rfl)
            (fun _ => hdenf.inconsistent_unsat hc) hmf
        · exact hQ 1#64 sf mf hdenf htmkf hfuf (Or.inl rfl) (fun h => by cases h) hmf)
      (fun Jf hJf => by
        c0_hsplit
        · have hcvb := hdenb.lengths.core_ok.cur_vars_le
          have hflb := hdenb.lengths.core_ok.flags_len
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
            (fun _ comp _ => by
              c0_hsteps_nogrp
              refine wp_join0 (P := fun mj => ∃ sj : FullState,
                  FullDenseInv c F0 sj ∧ TmkZero sj ∧ sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                  (FullMem c sj ⋆ R) mj)
                (fun _ mj h => by c0_hsteps!; exact hJf mj h)
                (fun _ hJc => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join0 (P := fun mj => ∃ sj : FullState,
                        FullDenseInv c F0 sj ∧ TmkZero sj ∧
                        sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj)
                      (fun _ mj h => by c0_hsteps!; exact hJc mj h)
                      (fun _ hJc2 => by
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                            (fun x => (x, ())) (fun _ => True)
                            (fun _ nb0 _ => by
                              c0_hsteps_nogrp
                              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                (fun x => (x, ())) (fun _ => True)
                                (fun _ nb _ => by
                                  c0_hsteps_nogrp
                                  let sb1 : FullState :=
                                    { sb with scratch := { sb.scratch with elim_bound := nb } }
                                  have hden1 : FullDenseInv c F0 sb1 :=
                                    fid_elim_denseInv_with_scratch_keep hdenb
                                      { hdenb.lengths.scratch_ok with
                                        walk_vals_len := hdenb.lengths.scratch_ok.walk_vals_len }
                                      rfl rfl
                                  refine wp_loop_group (ts := [i64])
                                    (fun rem_k (k, ()) mk => ∃ flk : List (BitVec 32),
                                      flk.length = c.max_vars ∧ k.toNat ≤ sb.core.cur_vars ∧
                                      rem_k = sb.core.cur_vars - k.toNat ∧
                                      (FullMem c
                                        { sb1 with core := { sb1.core with flags := flk } } ⋆ R)
                                        mk)
                                    ?_ ?_
                                  · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk
                                      ⟨flk, hflk, hk_le, rfl, hmk⟩
                                    c0_hsplit
                                    · have hk_lt : k.toNat < sb.core.cur_vars := by
                                        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                      have hk_b : k.toNat < flk.length := by omega
                                      have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                                      c0_hsteps!
                                      exact hLk (sb.core.cur_vars - (k + 1#64).toNat)
                                        (k + 1#64, ()) _ (by omega)
                                        ⟨_, by simp [hflk], by omega, rfl, hm⟩
                                    · c0_hsteps!
                                      let sf : FullState :=
                                        { sb1 with core := { sb1.core with flags := flk } }
                                      exact hJc2 mk ⟨sf, fid_elim_denseInv_with_flags hden1 hflk,
                                        htmkb.congr rfl rfl, hfub, hmk⟩
                                  · intro Lk hLk; c0_hsteps!
                                    exact hLk sb.core.cur_vars (0#64, ()) _
                                      ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hm⟩)
                                (fun Jm hJm => by c0_hsplit <;> (c0_hsteps!; exact hJm _ trivial)))
                            (fun Jb hJb => by c0_hsplit <;> (c0_hsteps!; exact hJb _ trivial))
                        · c0_hsteps!; exact hJc2 mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)
                  · c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i64])
                      (fun rem_k (k, ()) mk => ∃ flk : List (BitVec 32),
                        flk.length = c.max_vars ∧ k.toNat ≤ sb.core.cur_vars ∧
                        rem_k = sb.core.cur_vars - k.toNat ∧
                        (FullMem c { sb with core := { sb.core with flags := flk } } ⋆ R) mk)
                      ?_ ?_
                    · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk ⟨flk, hflk, hk_le, rfl, hmk⟩
                      c0_hsplit
                      · have hk_lt : k.toNat < sb.core.cur_vars := by
                          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                        have hk_b : k.toNat < flk.length := by omega
                        have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                        c0_hsteps!
                        exact hLk (sb.core.cur_vars - (k + 1#64).toNat) (k + 1#64, ()) _ (by omega)
                          ⟨_, by simp [hflk], by omega, rfl, hm⟩
                      · c0_hsteps!
                        let sf : FullState := { sb with core := { sb.core with flags := flk } }
                        exact hJc mk ⟨sf, fid_elim_denseInv_with_flags hdenb hflk,
                          htmkb.congr rfl rfl, hfub, hmk⟩
                    · intro Lk hLk; c0_hsteps!
                      exact hLk sb.core.cur_vars (0#64, ()) mb
                        ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hmb⟩))
            (fun Jc hJc => by c0_hsteps! <;> exact hJc _ trivial)
        · c0_hsteps!; exact hJf mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)
  · rintro Br Lr rem_r ⟨hit_lim, hlen, lre, round, ⟨⟩⟩ mr hBr hLr
      ⟨sr, hrd_le, rfl, hhl_le, hdenr, htmkr, hfur, hmr⟩
    have hbrk_r : Br (hit_lim, hlen, lre, round, ()) mr :=
      hBr (hit_lim, hlen, lre, round, ()) mr ⟨sr, hdenr, htmkr, hfur, hmr⟩
    c0_hsplit
    · have hrd_lt : round.toNat < 2 := hc
      have hrd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
      c0_hsplit
      · c0_hsteps!; exact hbrk_r
      · c0_hsteps_nogrp
        obtain ⟨F_cur, hdwr⟩ := hdenr.exists_witness
        refine wp_call_of_spec _ _ (hFlush _ _ _ _ ?_)
        refine fullDenseFlushUnitsM6Spec_intro rfl hdwr hmr ?_
        intro ok_u su mu hdwu hcvu _ hfuu _ htmku _ _ _ _ _ hfu_uns hmu
        have hdenu : FullDenseInv c F0 su := hdwu.toDense
        have htmku' : TmkZero su := htmkr.congr hcvu htmku
        have hfuu' : su.core.fuel.toNat ≤ s0.core.fuel.toNat := by rw [hfuu]; exact hfur
        c0_hsplit
        · have hcvu_le := hdwu.1.core_ok.cur_vars_le
          have hws1u := hdwu.1.scratch_ok.work_stk1_len
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64])
            (fun rem_i (i, ()) mi => ∃ ws1 : List (BitVec 32),
              ws1.length = 2 * c.max_vars ∧ i.toNat ≤ su.core.cur_vars ∧
              rem_i = su.core.cur_vars - i.toNat ∧
              (FullMem c { su with scratch := { su.scratch with work_stk1 := ws1 } } ⋆ R)
                mi)
            ?_ ?_
          · rintro Li rem_i ⟨i, ⟨⟩⟩ mi hLi ⟨ws1, hws1, hi_le, rfl, hmi⟩
            c0_hsplit
            · have hi_lt : i.toNat < su.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
              have hmv_i : (BitVec.ofNat 64 c.max_vars + i).toNat < ws1.length := by
                rw [hws1]; c0_bound
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
              c0_hsteps!
              exact hLi (su.core.cur_vars - (i + 1#64).toNat) (i + 1#64, ()) _ (by omega)
                ⟨_, by simp [hws1], by omega, rfl, hm⟩
            · let su1 : FullState :=
                { su with scratch := { su.scratch with work_stk1 := ws1 } }
              have hdenu1 : FullDenseInv c F0 su1 :=
                fid_elim_denseInv_with_ws1_ss hdenu hws1 hdwu.1.scratch_ok.sim_sig_len
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64, i64])
                (fun rem_p (hl_p, ip, ()) mp => ∃ (ws1p : List (BitVec 32))
                    (ssp : List (BitVec 64)),
                  let sp : FullState :=
                    { su with scratch :=
                      { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                  ws1p.length = 2 * c.max_vars ∧ ssp.length = c.max_vars ∧
                  ip.toNat ≤ su.core.cur_vars ∧ rem_p = su.core.cur_vars - ip.toNat ∧
                  hl_p.toNat ≤ su.core.cur_vars ∧ (FullMem c sp ⋆ R) mp)
                ?_ ?_
              · rintro Lp rem_p ⟨hl_p, ip, ⟨⟩⟩ mp hLp
                  ⟨ws1p, ssp, hws1p, hssp, hip_le, rfl, hhlp_le, hmp⟩
                let sp : FullState :=
                  { su with scratch :=
                    { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                c0_hsplit
                · have hip_lt : ip.toNat < su.core.cur_vars := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                  have hip1 : (ip + 1#64).toNat = ip.toNat + 1 := by c0_bound
                  have hip_fl : ip.toNat < su.core.flags.length := by
                    rw [hdwu.1.core_ok.flags_len]; omega
                  have hip_vl : (ip <<< (1 : Nat)).toNat < su.core.vals.length := by
                    rw [hdwu.1.core_ok.vals_len]; c0_bound
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i64])
                    (α := BitVec 64 × List (BitVec 32) × List (BitVec 64))
                    (fun x => (x.1, ()))
                    (fun x mj =>
                      let sj : FullState :=
                        { su with scratch :=
                          { su.scratch with work_stk1 := x.2.1, sim_sig := x.2.2 } }
                      x.2.1.length = 2 * c.max_vars ∧ x.2.2.length = c.max_vars ∧
                      x.1.toNat ≤ su.core.cur_vars ∧ (FullMem c sj ⋆ R) mj)
                    (fun _ ⟨hl_j, ws1j, ssj⟩ mj ⟨hws1j, hssj, hhlj, hmj⟩ => by
                      c0_hsteps!
                      exact hLp (su.core.cur_vars - (ip + 1#64).toNat)
                        (hl_j, ip + 1#64, ()) mj (by omega)
                        ⟨ws1j, ssj, hws1j, hssj, by omega, rfl, hhlj, hmj⟩)
                    (fun Jp hJp => by
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_call_of_spec _ _ (hPush _ _ _ _ ?_)
                          refine m8BveHeapPushSpec_intro rfl
                            (fid_elim_denseInv_with_ws1_ss hdenu hws1p hssp).lengths hmp ?_
                          intro hl_n ws1n ssn mn hws1n hssn hhln hmn
                          c0_hsteps!
                          exact hJp (hl_n, ws1n, ssn) mn
                            ⟨hws1n, hssn, hhln hhlp_le, hmn⟩
                        · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                            ⟨hws1p, hssp, hhlp_le, hmp⟩
                      · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                          ⟨hws1p, hssp, hhlp_le, hmp⟩)
                · have hdensp : FullDenseInv c F0 sp :=
                    fid_elim_denseInv_with_ws1_ss hdenu hws1p hssp
                  have htmksp : TmkZero sp := htmku'.congr rfl rfl
                  c0_hsplit
                  · c0_hsteps!
                    exact hBr (hit_lim, hl_p, false, round, ()) mp
                      ⟨sp, hdensp, htmksp, hfuu', hmp⟩
                  · c0_hsteps_nogrp
                    refine wp_loop_break_group
                      (brkTs := [.bool, i64, .bool]) (lpTs := [i64, .bool])
                      (fun (hl_b, hl_len, re_b, ()) mb => ∃ sb : FullState,
                        hl_len.toNat ≤ sb.core.cur_vars ∧
                        FullDenseInv c F0 sb ∧ TmkZero sb ∧
                        sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sb ⋆ R) mb)
                      (fun rem_h (hl_h, re_h, ()) mh => ∃ sh : FullState,
                        hl_h.toNat ≤ sh.core.cur_vars ∧
                        rem_h = sh.core.fuel.toNat * (c.max_vars + 1) + hl_h.toNat ∧
                        FullDenseInv c F0 sh ∧ TmkZero sh ∧
                        sh.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sh ⋆ R) mh)
                      ?_ ?_ ?_
                    · rintro _ ⟨hl_b, hl_len, re_b, ⟨⟩⟩ mb
                        ⟨sb, hhlb, hdenb, htmkb, hfub, hmb⟩
                      c0_hsplit
                      · c0_hsteps!
                        exact hLr (2 - (round + 1#64).toNat)
                          (hl_b, hl_len, re_b, round + 1#64, ()) mb (by omega)
                          ⟨sb, by omega, rfl, hhlb, hdenb, htmkb, hfub, hmb⟩
                      · c0_hsteps!
                        exact hBr (hl_b, hl_len, re_b, round, ()) mb
                          ⟨sb, hdenb, htmkb, hfub, hmb⟩
                    · rintro Bh Lh rem_h ⟨hl_h, re_h, ⟨⟩⟩ mh hBh hLh
                        ⟨sh, hhlh, rfl, hdenh, htmkh, hfuh, hmh⟩
                      have hbrk_h : Bh (hit_lim, hl_h, re_h, ()) mh :=
                        hBh (hit_lim, hl_h, re_h, ()) mh
                          ⟨sh, hhlh, hdenh, htmkh, hfuh, hmh⟩
                      c0_hsplit
                      · have hhl_pos : 0 < hl_h.toNat := hc
                        have hhl_dec : (hl_h - 1#64).toNat = hl_h.toNat - 1 := by c0_bound
                        c0_hsplit
                        · have hfu_pos : 0 < sh.core.fuel.toNat := hc
                          have hfu_dec : (sh.core.fuel - 1#64).toNat =
                              sh.core.fuel.toNat - 1 := by c0_bound
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsplit
                              · c0_hsteps!
                                exact hBh (true, hl_h, re_h, ()) mh
                                  ⟨sh, hhlh, hdenh, htmkh, hfuh, hmh⟩
                              · c0_hsteps_nogrp
                                refine wp_call_of_spec _ _ (hPop _ _ _ _ ?_)
                                refine fullBveHeapPopM6Spec_intro rfl hdenh.lengths hmh ?_
                                intro v ws1_1 m1 hws1_1 hm1
                                let s1 : FullState :=
                                  { sh with scratch :=
                                    { sh.scratch with work_stk1 := ws1_1 } }
                                have hden1 : FullDenseInv c F0 s1 :=
                                  fid_elim_denseInv_with_ws1_ss hdenh hws1_1
                                    hdenh.lengths.scratch_ok.sim_sig_len
                                have htmk1 : TmkZero s1 := htmkh.congr rfl rfl
                                have hcv1_le := hden1.lengths.core_ok.cur_vars_le
                                have hhl_dec1 : (hl_h - 1#64).toNat ≤ s1.core.cur_vars := by
                                  dsimp only [s1]; rw [hhl_dec]; omega
                                c0_hsplit
                                · c0_hsteps!
                                  exact hLh _ (hl_h - 1#64, re_h, ()) m1
                                    (by dsimp only [s1]; rw [hhl_dec]; omega)
                                    ⟨s1, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                · c0_hsplit
                                  · c0_hsteps!
                                    exact hLh _ (hl_h - 1#64, re_h, ()) m1
                                      (by dsimp only [s1]; rw [hhl_dec]; omega)
                                      ⟨s1, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                  · have hv_lt : v.toNat < s1.core.cur_vars := by
                                      rw [Nat.mod_eq_of_lt
                                        (by omega : s1.core.cur_vars < 2 ^ 64)] at hc
                                      omega
                                    have hv_fl : (v.setWidth 64).toNat <
                                        s1.core.flags.length := by
                                      rw [hden1.lengths.core_ok.flags_len, m6_zext32_toNat]
                                      omega
                                    have hv_vl : (v.setWidth 64 <<< (1 : Nat)).toNat <
                                        s1.core.vals.length := by
                                      rw [hden1.lengths.core_ok.vals_len]; c0_bound
                                    c0_hsplit
                                    · c0_hsteps!
                                      exact hLh _ (hl_h - 1#64, re_h, ()) m1
                                        (by dsimp only [s1]; rw [hhl_dec]; omega)
                                        ⟨s1, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                    · c0_hsplit
                                      · c0_hsteps!
                                        exact hLh _ (hl_h - 1#64, re_h, ()) m1
                                          (by dsimp only [s1]; rw [hhl_dec]; omega)
                                          ⟨s1, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                      · c0_hsteps_nogrp
                                        let fl2 := s1.core.flags.set (v.setWidth 64).toNat
                                          (s1.core.flags[(v.setWidth 64).toNat]'hv_fl &&&
                                            ~~~16#32)
                                        let s2 : FullState :=
                                          { s1 with core :=
                                            { s1.core with
                                              flags := fl2
                                              fuel := s1.core.fuel - 1#64 } }
                                        have hden2 : FullDenseInv c F0 s2 :=
                                          fid_elim_denseInv_with_flags_fuel hden1
                                            (by simp [fl2, hden1.lengths.core_ok.flags_len])
                                            (s1.core.fuel - 1#64)
                                        have htmk2 : TmkZero s2 := htmk1.congr rfl rfl
                                        refine wp_call_of_spec _ _ (hNbrs _ _ _ _ ?_)
                                        refine ⟨c, F0, s2, R, rfl, hden2, htmk2, hm, ?_⟩
                                        intro nn mclr3 ws2_3 m3 _s3_n hl3 hnn_le _ hm3
                                        have hcv2_le := hden2.lengths.core_ok.cur_vars_le
                                        have hnn_mv : nn.toNat ≤ c.max_vars :=
                                          Nat.le_trans hnn_le hcv2_le
                                        let s3 : FullState :=
                                          { s2 with
                                            core := { s2.core with min_clr := mclr3 },
                                            scratch :=
                                              { s2.scratch with work_stk2 := ws2_3 } }
                                        have hden3 : FullDenseInv c F0 s3 :=
                                          fullDenseInv_with_min_clr_work_stk2 hden2
                                            hl3.core_ok.min_clr_len_arr
                                            hl3.scratch_ok.work_stk2_len
                                        have htmk3 : TmkZero s3 := htmk2.congr rfl rfl
                                        c0_hsteps_nogrp
                                        refine wp_call_of_spec _ _ (hVar _ _ _ _ ?_)
                                        refine ⟨c, F0, s3, R, rfl, hden3, htmk3, hv_lt,
                                          hm3, ?_⟩
                                        intro st s4 m4 hden4 htmk4 hcv4 hfu4 _ hst20 hm4
                                        have hfu4_dec : s4.core.fuel.toNat ≤
                                            sh.core.fuel.toNat - 1 := by
                                          change s4.core.fuel.toNat ≤
                                            (s1.core.fuel - 1#64).toNat at hfu4
                                          rw [show s1.core.fuel = sh.core.fuel from rfl,
                                            hfu_dec] at hfu4
                                          exact hfu4
                                        have hfu4' : s4.core.fuel.toNat ≤
                                            s0.core.fuel.toNat := by omega
                                        have hcv4_le := hden4.lengths.core_ok.cur_vars_le
                                        have hhl_s4 : (hl_h - 1#64).toNat ≤
                                            s4.core.cur_vars := by
                                          dsimp only [s3, s2, s1] at hcv4
                                          rw [hhl_dec]; omega
                                        c0_hsplit
                                        · c0_hsteps!
                                          exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                            (Or.inr rfl) (fun _ => hst20 hc) hm4
                                        · c0_hsplit
                                          · c0_hsteps!
                                            exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                              (Or.inr rfl)
                                              (fun _ => hden4.inconsistent_unsat hc) hm4
                                          · c0_hsplit
                                            · c0_hsteps!
                                              exact hBh (hit_lim, hl_h - 1#64, re_h, ())
                                                m4 ⟨s4, hhl_s4, hden4, htmk4, hfu4', hm4⟩
                                            · c0_hsteps_nogrp
                                              obtain ⟨F_cur4, hdw4⟩ :=
                                                hden4.exists_witness
                                              refine wp_call_of_spec _ _
                                                (hFlush _ _ _ _ ?_)
                                              refine fullDenseFlushUnitsM6Spec_intro rfl
                                                hdw4 hm4 ?_
                                              intro ok_f s5 m5 hdw5 hcv5 _ hfu5 _
                                                htmk5 _ _ _ _ _ hfu5_uns hm5
                                              have hden5 : FullDenseInv c F0 s5 :=
                                                hdw5.toDense
                                              have htmk5' : TmkZero s5 :=
                                                htmk4.congr hcv5 htmk5
                                              have hfu5_dec : s5.core.fuel.toNat ≤
                                                  sh.core.fuel.toNat - 1 := by
                                                rw [hfu5]; exact hfu4_dec
                                              have hfu5' : s5.core.fuel.toNat ≤
                                                  s0.core.fuel.toNat := by omega
                                              have hhl_s5 : (hl_h - 1#64).toNat ≤
                                                  s5.core.cur_vars := by
                                                rw [hcv5]; exact hhl_s4
                                              c0_hsplit
                                              · have hcont_4 : ∀ (hl_f : BitVec 64)
                                                    (re_f : Bool) (sf : FullState)
                                                    (mf : Mem 64),
                                                    hl_f.toNat ≤ sf.core.cur_vars →
                                                    FullDenseInv c F0 sf → TmkZero sf →
                                                    sf.core.fuel.toNat ≤
                                                      sh.core.fuel.toNat - 1 →
                                                    (FullMem c sf ⋆ R) mf →
                                                    Lh (hl_f, re_f, ()) mf :=
                                                  fun hl_f re_f sf mf hhlf hdenf htmkf
                                                      hfuf hmf => by
                                                    have hcvf :=
                                                      hdenf.lengths.core_ok.cur_vars_le
                                                    have hmul : sf.core.fuel.toNat *
                                                        (c.max_vars + 1) ≤
                                                        (sh.core.fuel.toNat - 1) *
                                                          (c.max_vars + 1) :=
                                                      Nat.mul_le_mul_right _ hfuf
                                                    have hsub : sh.core.fuel.toNat *
                                                        (c.max_vars + 1) =
                                                        (sh.core.fuel.toNat - 1) *
                                                          (c.max_vars + 1) +
                                                          (c.max_vars + 1) := by
                                                      rw [← Nat.succ_mul]; congr 1; omega
                                                    refine hLh
                                                      (sf.core.fuel.toNat *
                                                        (c.max_vars + 1) + hl_f.toNat)
                                                      (hl_f, re_f, ()) mf (by omega)
                                                      ⟨sf, hhlf, rfl, hdenf, htmkf,
                                                       by omega, hmf⟩
                                                refine wp_join_state (ts := [i64, .bool])
                                                  (α := BitVec 64 × Bool × FullState)
                                                  (fun x => (x.1, x.2.1, ()))
                                                  (fun x mj =>
                                                    x.1.toNat ≤ x.2.2.core.cur_vars ∧
                                                    FullDenseInv c F0 x.2.2 ∧
                                                    TmkZero x.2.2 ∧
                                                    x.2.2.core.fuel.toNat ≤
                                                      sh.core.fuel.toNat - 1 ∧
                                                    (FullMem c x.2.2 ⋆ R) mj)
                                                  (fun _ ⟨hl_f, re_f, sf⟩ mf
                                                      ⟨hhlf, hdenf, htmkf, hfuf, hmf⟩ => by
                                                    c0_hsteps!
                                                    exact hcont_4 hl_f re_f sf mf hhlf
                                                      hdenf htmkf hfuf hmf)
                                                  (fun Jn hJn => by
                                                    c0_hsplit
                                                    · c0_hsteps_nogrp
                                                      refine wp_loop_group
                                                        (ts := [i64, i64])
                                                        (fun rem_k (hl_k, k, ()) mk =>
                                                          ∃ sk : FullState,
                                                            k.toNat ≤ nn.toNat ∧
                                                            rem_k = nn.toNat - k.toNat ∧
                                                            hl_k.toNat ≤
                                                              sk.core.cur_vars ∧
                                                            sk.core.cur_vars =
                                                              s5.core.cur_vars ∧
                                                            FullDenseInv c F0 sk ∧
                                                            TmkZero sk ∧
                                                            sk.core.fuel.toNat ≤
                                                              sh.core.fuel.toNat - 1 ∧
                                                            (FullMem c sk ⋆ R) mk)
                                                        ?_ ?_
                                                      · rintro Lk rem_k ⟨hl_k, k, ⟨⟩⟩ mk
                                                          hLk ⟨sk, hk_le, rfl, hhlk, hcvk,
                                                            hdenk, htmkk, hfuk, hmk⟩
                                                        have hlkl := hdenk.lengths
                                                        c0_hsplit
                                                        · have hk_lt :
                                                              k.toNat < nn.toNat := hc
                                                          have hk1 : (k + 1#64).toNat =
                                                              k.toNat + 1 := by c0_bound
                                                          have hws2_k :=
                                                            hlkl.scratch_ok.work_stk2_len
                                                          have hk_w : k.toNat <
                                                              sk.scratch.work_stk2.length :=
                                                            by omega
                                                          let uk :=
                                                            sk.scratch.work_stk2[k.toNat]'
                                                              hk_w
                                                          c0_hsteps_nogrp
                                                          refine wp_join_state (ts := [i64])
                                                            (α := BitVec 64 × FullState)
                                                            (fun x => (x.1, ()))
                                                            (fun x mj =>
                                                              x.1.toNat ≤
                                                                x.2.core.cur_vars ∧
                                                              x.2.core.cur_vars =
                                                                s5.core.cur_vars ∧
                                                              FullDenseInv c F0 x.2 ∧
                                                              TmkZero x.2 ∧
                                                              x.2.core.fuel.toNat ≤
                                                                sh.core.fuel.toNat - 1 ∧
                                                              (FullMem c x.2 ⋆ R) mj)
                                                            (fun _ ⟨hl_j, sj⟩ mj
                                                                ⟨hhlj, hcvj, hdenj, htmkj,
                                                                  hfuj, hmj⟩ => by
                                                              c0_hsteps!
                                                              exact hLk
                                                                (nn.toNat -
                                                                  (k + 1#64).toNat)
                                                                (hl_j, k + 1#64, ()) mj
                                                                (by omega)
                                                                ⟨sj, by omega, rfl, hhlj,
                                                                 hcvj, hdenj, htmkj, hfuj,
                                                                 hmj⟩)
                                                            (fun Jk hJk => by
                                                              c0_hsplit
                                                              · have huk_lt : uk.toNat <
                                                                    sk.core.cur_vars := by
                                                                  rw [← hcvk,
                                                                    Nat.mod_eq_of_lt
                                                                      (by omega :
                                                                        sk.core.cur_vars <
                                                                          2 ^ 64)] at hc
                                                                  exact hc
                                                                have hflk_l :=
                                                                  hlkl.core_ok.flags_len
                                                                have huk_fl :
                                                                    (uk.setWidth 64).toNat <
                                                                    sk.core.flags.length :=
                                                                  by
                                                                    rw [hflk_l,
                                                                      m6_zext32_toNat]
                                                                    omega
                                                                c0_hsplit
                                                                · have hvlk_l :=
                                                                    hlkl.core_ok.vals_len
                                                                  have huk_vl :
                                                                      (uk.setWidth 64 <<<
                                                                        (1 : Nat)).toNat <
                                                                      sk.core.vals.length :=
                                                                    by
                                                                      rw [hvlk_l]; c0_bound
                                                                  c0_hsplit
                                                                  · c0_hsteps_nogrp
                                                                    let u64 :=
                                                                      (uk.setWidth 64).toNat
                                                                    let fl_u :=
                                                                      sk.core.flags.set u64
                                                                        (sk.core.flags[
                                                                          u64]'huk_fl |||
                                                                          16#32)
                                                                    let su_k : FullState :=
                                                                      { sk with core :=
                                                                        { sk.core with
                                                                          flags := fl_u } }
                                                                    have hflu_l :
                                                                        fl_u.length =
                                                                        c.max_vars := by
                                                                      simp only [fl_u,
                                                                        List.length_set,
                                                                        hflk_l]
                                                                    have hden_u :=
                                                                      fid_elim_denseInv_with_flags
                                                                        hdenk hflu_l
                                                                    refine wp_call_of_spec
                                                                      _ _ (hPush _ _ _ _ ?_)
                                                                    refine
                                                                      m8BveHeapPushSpec_intro
                                                                        rfl hden_u.lengths
                                                                        hm ?_
                                                                    intro hl_p ws1p ssp
                                                                      mp_ hws1p hssp hhlp
                                                                      hmp_
                                                                    c0_hsteps!
                                                                    let s_pu : FullState :=
                                                                      { su_k with
                                                                        scratch :=
                                                                          { su_k.scratch
                                                                            with
                                                                            work_stk1 :=
                                                                              ws1p,
                                                                            sim_sig :=
                                                                              ssp } }
                                                                    exact hJk (hl_p, s_pu)
                                                                      mp_
                                                                      ⟨hhlp hhlk, hcvk,
                                                                       fid_elim_denseInv_with_ws1_ss
                                                                         hden_u hws1p hssp,
                                                                       htmkk.congr rfl rfl,
                                                                       hfuk, hmp_⟩
                                                                  · c0_hsteps!
                                                                    exact hJk (hl_k, sk)
                                                                      mk ⟨hhlk, hcvk,
                                                                        hdenk, htmkk,
                                                                        hfuk, hmk⟩
                                                                · c0_hsteps!
                                                                  exact hJk (hl_k, sk) mk
                                                                    ⟨hhlk, hcvk, hdenk,
                                                                      htmkk, hfuk, hmk⟩
                                                              · c0_hsteps!
                                                                exact hJk (hl_k, sk) mk
                                                                  ⟨hhlk, hcvk, hdenk,
                                                                    htmkk, hfuk, hmk⟩)
                                                        · c0_hsteps!
                                                          exact hJn (hl_k, true, sk) mk
                                                            ⟨hhlk, hdenk, htmkk, hfuk, hmk⟩
                                                      · intro Lk hLk; c0_hsteps!
                                                        exact hLk nn.toNat
                                                          (hl_h - 1#64, 0#64, ()) m5
                                                          ⟨s5, Nat.zero_le _, by simp,
                                                           hhl_s5, rfl, hden5, htmk5',
                                                           hfu5_dec, hm5⟩
                                                    · c0_hsteps!
                                                      exact hJn (hl_h - 1#64, re_h, s5) m5
                                                        ⟨hhl_s5, hden5, htmk5', hfu5_dec,
                                                         hm5⟩)
                                              · c0_hsteps!
                                                exact hQ 20#64 s5 m5 hden5 htmk5' hfu5'
                                                  (Or.inr rfl)
                                                  (fun _ => hfu5_uns (by simpa using hc))
                                                  hm5
                            · c0_hsteps!; exact hbrk_h
                          · c0_hsteps!; exact hbrk_h
                        · c0_hsteps!; exact hbrk_h
                      · c0_hsteps!; exact hbrk_h
                    · intro _ Lh _ hLh; c0_hsteps!
                      exact hLh _ (hl_p, false, ()) mp
                        ⟨sp, hhlp_le, rfl, hdensp, htmksp, hfuu', hmp⟩
              · intro Lp hLp; c0_hsteps!
                exact hLp su.core.cur_vars (0#64, 0#64, ()) mi
                  ⟨ws1, su.scratch.sim_sig, hws1, hdwu.1.scratch_ok.sim_sig_len,
                   Nat.zero_le _, by simp, Nat.zero_le _, hmi⟩
          · intro Li hLi; c0_hsteps!
            exact hLi su.core.cur_vars (0#64, ()) mu
              ⟨su.scratch.work_stk1, hws1u, Nat.zero_le _, by simp, hmu⟩
        · c0_hsteps!
          exact hQ 20#64 su mu hdenu htmku' hfuu' (Or.inr rfl)
            (fun _ => hfu_uns (by simpa using hc)) hmu
        all_goals (c0_hsteps!; exact hbrk_r)
    · c0_hsteps!; exact hbrk_r
  · intro _ Lr _ hLr; c0_hsteps!
    exact hLr 2 (false, 0#64, false, 0#64, ()) _
      ⟨sz, Nat.zero_le _, rfl, Nat.zero_le _, hdenz, htmkz, Nat.le_refl _, hm⟩

/-! ## 3. `full_eliminate_m6_fid_wp` (Canonical `FullFastSched.schedEliminateSpec`) -/

/-- Certifies canonical `FullFastSched.schedEliminateSpec` for
`FullFidelityBve.full_eliminate_m6_body` (Q16 `full_log10_q16_m7`, `res_lim`, no `full_factor`). -/
theorem full_eliminate_m6_fid_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hLog : ∀ a m Q X, FullM7Search.m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ FullFidelityBve.full_eliminate_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hinv0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp FullFidelityBve.full_eliminate_m6_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hDticks _ _ _ _ ?_)
  refine ⟨c, s0, R, rfl, hinv0.lengths, hm0, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, _, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      refine wp_call_of_spec _ _ (hEnter _ _ _ _ ?_)
      refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
      intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
      c0_hsplit
      · have hden2 : FullDenseInv c F0 s2 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            refine wp_call_of_spec _ _ (hMin _ _ _ _ ?_); intro fbud _
            c0_hsteps_nogrp
            refine wp_call_of_spec _ _ (hFwd _ _ _ _ ?_)
            refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
            intro fs s3 m3 hden3 hcv3 hfu3 _ huf3 hm3
            have hcv2_le := hden2.lengths.core_ok.cur_vars_le
            let s3r : FullState :=
              { s3 with scratch := { s3.scratch with fwd_sub_cnt := s2.scratch.fwd_sub_cnt } }
            have hden3r : FullDenseInv c F0 s3r :=
              fid_elim_denseInv_with_scratch_keep hden3
                { hden3.lengths.scratch_ok with
                  walk_vals_len := hden3.lengths.scratch_ok.walk_vals_len } rfl rfl
            have hfu3r : s3r.core.fuel.toNat ≤ s0.core.fuel.toNat := by
              change s3.core.fuel.toNat ≤ s0.core.fuel.toNat; rw [hfu3]; omega
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hReb _ _ _ _ ?_)
              refine ⟨c, F0, s3r, R, rfl, hden3r, hm, ?_⟩
              intro _ s4 m4 hsp4 hcl4 hfu4 _ _ hm4
              c0_hsteps!
              exact hQ 20#64 s4 m4 hsp4 hcl4 (by omega) (Or.inr rfl) (fun _ => huf3 hc) hm4
            · let cv3 := s3r.core.cur_vars
              have hcv3_le : cv3 ≤ c.max_vars := hden3r.lengths.core_ok.cur_vars_le
              have htl3 := hden3r.lengths.scratch_ok.tarjan_mark_len
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64])
                (fun rem_t (ti, ()) mt => ∃ tmki : List (BitVec 32),
                  tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv3 ∧ rem_t = cv3 - ti.toNat ∧
                  (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                  (FullMem c { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } } ⋆
                    R) mt)
                ?_ ?_
              · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨tmki, htli, hti_le, rfl, hinit, hmt⟩
                c0_hsplit
                · have hti_lt : ti.toNat < cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                  have hti_b : ti.toNat < tmki.length := by omega
                  have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
                  c0_hsteps!
                  exact hLt (cv3 - (ti + 1#64).toNat) (ti + 1#64, ()) _ (by omega)
                    ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega, rfl, fun k hk => by
                       rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hti1 ▸ hk)) with h | h
                       · rw [List.getElem?_set_ne (by omega)]; exact hinit k h
                       · subst h; rw [List.getElem?_set_self hti_b, Option.getD_some], hm⟩
                · have hti_eq : ti.toNat = cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc
                    change ¬ti.toNat < cv3 at hc
                    omega
                  rw [hti_eq] at hinit
                  let s3t : FullState :=
                    { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
                  have hden3t : FullDenseInv c F0 s3t :=
                    fid_elim_denseInv_with_scratch_keep hden3r
                      { hden3r.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                  have htmk3t : TmkZero s3t := fid_elim_tmkZero_of_init hinit
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                    (fun b => (b, ())) (fun _ => True)
                    (fun _ base_t _ => by
                      c0_hsteps_nogrp
                      refine wp_call_of_spec _ _ (hBve _ _ _ _ ?_)
                      refine ⟨c, F0, s3t, R, rfl, hden3t, htmk3t, hmt, ?_⟩
                      intro res s4 m4 hden4 _ hfu4 _ hres_u hm4
                      have hfu4' : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        dsimp only [s3t, s3r] at hfu4
                        have hfu3' : s3.core.fuel.toNat ≤ s0.core.fuel.toNat := hfu3r
                        omega
                      c0_hsteps_nogrp
                      refine wp_call_of_spec _ _ (hReb _ _ _ _ ?_)
                      refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                      intro rr se me hspe hcle hfue _ hue hme
                      let se' : FullState :=
                        { se with scratch :=
                          { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                      have hspe' : FullSparseInv c F0 se' :=
                        fid_elim_sparseInv_with_scratch_keep hspe
                          { hspe.lengths.scratch_ok with
                            walk_vals_len := hspe.lengths.scratch_ok.walk_vals_len } rfl rfl
                      have hfue' : se'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        change se.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
                      c0_hsteps!
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hres_u hc) hm
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hue hc) hm
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hspe'.inconsistent_unsat hc) hm
                      · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl)
                          (fun h => by cases h) hm)
                    (fun Jb hJb => by c0_hsplit <;> (c0_hsteps!; exact hJb _ trivial))
              · intro Lt hLt; c0_hsteps!
                exact hLt cv3 (0#64, ()) _
                  ⟨s3r.scratch.tarjan_mark, htl3, Nat.zero_le _, by simp,
                   fun _ h => by simp at h, hm⟩)
          (fun Jfb hJfb => by c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial))
      · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
        let s2' : FullState :=
          { s2 with scratch := { s2.scratch with fwd_str_cnt := s2.scratch.search_ticks } }
        have hsp2' : FullSparseInv c F0 s2' :=
          fid_elim_sparseInv_with_scratch_keep hsp2
            { hsp2.lengths.scratch_ok with
              walk_vals_len := hsp2.lengths.scratch_ok.walk_vals_len } rfl rfl
        have hfu2' : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
          change s2.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
        c0_hsteps!
        · exact hQ 20#64 s2' _ hsp2' hcl2 hfu2' (Or.inr rfl)
            (fun _ => hsp2'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s2' _ hsp2' hcl2 hfu2' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps!; exact hJ1 s0 m0 ⟨hinv0, hcl0, Nat.le_refl _, hm0⟩
      · c0_hsteps_nogrp
        let s0a : FullState :=
          { s0 with scratch := { s0.scratch with eliminations := s0.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv0.lengths.core_ok,
           { hinv0.lengths.scratch_ok with
             walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }⟩
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ arg _ => by
            c0_hsteps_nogrp
            refine wp_call_of_spec _ _ (hLog _ _ _ _ ?_)
            refine m7Log10Q16Spec_of fun qlog _ _ => ?_
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
              (fun b => (b, ())) (fun _ => True)
              (fun _ ec _ => by
                c0_hsteps_nogrp
                refine wp_call_of_spec _ _ (hScale _ _ _ _ ?_)
                refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
                intro delta
                c0_hsteps!
                let s0b : FullState :=
                  { s0a with
                    scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
                have hinv0b : FullSparseInv c F0 s0b :=
                  fid_elim_sparseInv_with_scratch_keep hinv0
                    { hinv0.lengths.scratch_ok with
                      walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len } rfl rfl
                exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)
              (fun Jec hJec => by c0_hsplit <;> (c0_hsteps!; exact hJec _ trivial)))
          (fun Jarg hJarg => by c0_hsplit <;> (c0_hsteps!; exact hJarg _ trivial)))

end LeanQbe.T.Examples.Kissat.FullFidelityBve
