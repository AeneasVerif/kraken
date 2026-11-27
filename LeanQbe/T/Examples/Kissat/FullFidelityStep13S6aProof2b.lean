/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BBveFwd
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof2b0
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM6SweepProofDenseProp
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard `S6a` — BVE `full_bve_var_m7` Lift (`Proof2b`)

100% callee-parametric `(Γ : Env)` Step-13 `Func.wp` lift theorem (`0` cross-shard `S0..S5`
imports, `0` `@[expose]` on theorems/lemmas, `0` `import all`, `<= 100` cols, `<= std3`):
- `full_bve_var_m7_step13_wp` (`FullFidelityStep12B.full_bve_var_m7_body` over
  `step13SetInactiveSpec` -> `FullFastBveBudgets.fullBveVarDefSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open LeanQbe.T.Examples.Kissat.FullFidelityStep12B
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics

private theorem s6a_bve_var_fast_wp (Γ : Env)
    (hWeakenUnit : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken_unit_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, step13SetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s2 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {v occ_lim neg_off pos_mask neg_mask gf_idx rg_idx np nn : BitVec 32}
    {r_off : BitVec 64} {push_pos ext_ok : Bool}
    {J25 : Cont []} {m2 : Mem 64}
    (_hmx : c.max_vars < 2 * 2 ^ 28) (_hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hv_lt : v.toNat < s0.core.cur_vars) (hplnl : (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
      ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1)
    (_hneg_eq : neg_off = occ_lim) (hneg_off_lt : neg_off.toNat + occ_lim.toNat ≤ c.scratch_cap)
    (hnp_le : np.toNat ≤ occ_lim.toNat) (hnn_le : nn.toNat ≤ occ_lim.toNat)
    (hdw2 : FullDenseInvW c F0 F_cur s2) (hcv2 : s2.core.cur_vars = s0.core.cur_vars)
    (hfl2 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (htmk0 : TmkZero s2)
    (hent_p2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
      (s2.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n2' : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
      (s2.scratch.scratch_buf[neg_off.toNat + j]?.getD 0#32))
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJ25 : ∀ m', m' = m2 → J25 () m') :
    wp Γ Q X (bveFastAt45 Val Cont c.hdr v (BitVec.ofNat 64 c.scratch_cap)
      (decide (16384 ≤ c.scratch_cap)) occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
      c.pScratchBuf c.pVals c.pTmp c.pWvec ((BitVec.ofNat 64 s0.core.cur_vars) <<< (1 : Nat))
      (BitVec.ofNat 64 c.arena_cap) (BitVec.ofNat 64 c.wcap)
      (v <<< (1 : Nat)) ((v <<< (1 : Nat)) ||| 1#32) np nn push_pos ext_ok J25
      0#64 0#32 false (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => True)) m2 := by
  dsimp only [bveFastAt45, bveAt45, sL64, sL32, sL8, sLb, sD64, sD32, sD8, sC32, sCb,
    sT, sE, sB0, sB64, sB32, sBb, sB4, sB6, sB5, sK0, sKb, sK4, sK5, sK6]
  c0_hsplit
  · refine wp_join0 (P := fun mj => mj = m2 ∧ (np = 0#32 ∨ nn = 0#32))
      (fun _ mj ⟨hmj, hnp_nn⟩ => by
        rcases hmj.symm with rfl
        refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
          (fun sw moom =>
            FullDenseInvW c F0 F_cur sw ∧ TmkZero sw ∧
            sw.core.cur_vars = s0.core.cur_vars ∧
            sw.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
            (FullMem c sw ⋆ R) moom)
          (fun _ sw moom ⟨hdww, htmkw, hcvw, hflw, hmw⟩ => by
            c0_hsteps!
            let soom : FullState := { sw with core := { sw.core with oom := 1#64 } }
            exact hQ 2#64 soom _ (m6_fullDenseInvW_with_oom hdww 1#64).toDense htmkw
              (by dsimp only [soom]; omega) hflw (Or.inr (Or.inl rfl)) (by simp) hm)
          (fun J27 hJ27 => by
            refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
              (fun sp mp =>
                FullDenseInvW c F0 F_cur sp ∧ TmkZero sp ∧
                sp.core.cur_vars = s0.core.cur_vars ∧
                sp.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                (∀ j < nn.toNat, FullBveEntryOkW F_cur sp (2 * v.toNat + 1)
                  (sp.scratch.scratch_buf[neg_off.toNat + j]?.getD 0#32)) ∧
                (FullMem c sp ⋆ R) mp)
              (fun _ sp mp ⟨hdwp, htmkp, hcvp, hflp, hent_np, hmp⟩ => by
                refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                  (fun sn mn =>
                    FullDenseInvW c F0 F_cur sn ∧ TmkZero sn ∧
                    sn.core.cur_vars = s0.core.cur_vars ∧
                    sn.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                    (FullMem c sn ⋆ R) mn) ?_ ?_
                · intro _ sn mn ⟨hdwn, htmkn, hcvn, hfln, hmn⟩
                  c0_hsteps_nogrp
                  refine wp_call_of_spec _ _ (hSetInact _ _ _ _ ?_)
                  dsimp only [vals, Arg.val]
                  refine ⟨c, sn, R, rfl, hdwn.1, hmn, ?_⟩
                  rw [ite_eq_right (by omega)]
                  intro fl' unass' qp' qn' qs' qsi' qss' qf' ql' hp' ps' hl' m_i _ hlen_i hm_i
                  let si : FullState :=
                    { sn with
                      core := { sn.core with flags := fl', unassigned := unass' }
                      scratch := { sn.scratch with
                        q_prev := qp', q_next := qn', q_stamp := qs',
                        q_search_idx := qsi', q_search_stamp := qss',
                        q_first := qf', q_last := ql',
                        heap := hp', pos := ps', heap_len := hl' } }
                  have hdwi := s6a_var_fullDenseInvW_setInact13 hdwn hlen_i
                  c0_hsteps!
                  let sf : FullState :=
                    { si with scratch := { si.scratch with bve_cnt := si.scratch.bve_cnt + 1#64 } }
                  have hdwf := m6_fullDenseInvW_with_scratch hdwi (sc' := sf.scratch)
                    { hdwi.1.scratch_ok with } rfl rfl
                  exact hQ 1#64 sf _ hdwf.toDense (htmkn.congr rfl rfl)
                    (by dsimp only [sf, si]; omega) hfln (Or.inl rfl) (by simp) hm
                · intro J29 hJ29
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_call_of_spec _ _ (hWeakenUnit _ _ _ _ ?_)
                    dsimp only [vals, Arg.val]
                    refine ⟨c, F0, F_cur, sp, R, rfl, hdwp, htmkp,
                      by rw [hplnl.2, hcvp]; omega, by omega,
                      fun j hj => s6a_var_bveEntry_weak (hent_np j hj), hmp, ?_⟩
                    intro ok_w sw mw hdww htmkw hcvw hflw _ _ hmw
                    c0_hsplit
                    · c0_hsteps!
                      exact hJ29 sw mw ⟨hdww, htmkw, hcvw.trans hcvp, by rw [hflw]; exact hflp, hmw⟩
                    · c0_hsteps!
                      exact hJ27 sw mw ⟨hdww, htmkw, hcvw.trans hcvp, by rw [hflw]; exact hflp, hmw⟩
                  · c0_hsteps!
                    exact hJ29 sp mp ⟨hdwp, htmkp, hcvp, hflp, hmp⟩)
              (fun J28 hJ28 => by
                c0_hsplit
                · c0_hsteps_nogrp
                  refine wp_call_of_spec _ _ (hWeakenUnit _ _ _ _ ?_)
                  dsimp only [vals, Arg.val]
                  refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, htmk0,
                    by rw [hplnl.1, hcv2]; omega,
                    by rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]; omega,
                    fun i hi => by
                      rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                      exact s6a_var_bveEntry_weak (hent_p2 i hi),
                    hm2, ?_⟩
                  intro ok_w sw mw hdww htmkw hcvw hflw _ _ hmw
                  c0_hsplit
                  · c0_hsteps!
                    refine hJ28 sw mw
                      ⟨hdww, htmkw, hcvw.trans hcv2, by rw [hflw]; exact hfl2,
                        fun j hj => ?_, hmw⟩
                    exfalso
                    have hnp0 : np ≠ 0#32 := fun h => by subst h; simp at hc
                    have hnn0 := hnp_nn.resolve_left hnp0
                    rw [hnn0, show (0#32).toNat = 0 from rfl] at hj; omega
                  · c0_hsteps!
                    exact hJ27 sw mw
                      ⟨hdww, htmkw, hcvw.trans hcv2, by rw [hflw]; exact hfl2, hmw⟩
                · c0_hsteps!
                  exact hJ28 s2 m2 ⟨hdw2, htmk0, hcv2, hfl2, hent_n2', hm2⟩)))
      (fun J26 hJ26 => by
        c0_hsplit
        · c0_hsteps!; exact hJ26 m2 ⟨rfl, Or.inl hc⟩
        · c0_hsplit
          · c0_hsteps!; exact hJ26 m2 ⟨rfl, Or.inr hc⟩
          · c0_hsteps!; exact hJ25 m2 rfl)
  · c0_hsteps!; exact hJ25 m2 rfl

private theorem s6a_bve_var_fit_wp (Γ : Env)
    (hWeaken : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hWeakenUnit : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken_unit_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, step13SetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hCommit : ∀ a m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sf : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {v occ_lim neg_off pos_mask neg_mask gf_idx rg_idx np nn : BitVec 32}
    {r_off lim_cls rp r_cnt w_est : BitVec 64} {push_pos ext_ok fit : Bool}
    {mf : Mem 64}
    (_hmx : c.max_vars < 2 * 2 ^ 28) (_hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hv_lt : v.toNat < s0.core.cur_vars)
    (hplnl : (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
      ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1)
    (_hneg_eq : neg_off = occ_lim) (hneg_off_lt : neg_off.toNat + occ_lim.toNat ≤ c.scratch_cap)
    (hnp_le : np.toNat ≤ occ_lim.toNat) (hnn_le : nn.toNat ≤ occ_lim.toNat)
    (hrp_lo : r_off.toNat ≤ rp.toNat) (hrp_hi : rp.toNat ≤ c.scratch_cap)
    (hdwf : FullDenseInvW c F0 F_cur sf) (htmkf : TmkZero sf)
    (hcvf : sf.core.cur_vars = s0.core.cur_vars)
    (hflf : sf.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hresf : FullResBufOkW F_cur sf rp.toNat r_off.toNat)
    (hent_pf : ∀ k < np.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat)
      (sf.scratch.scratch_buf[k]?.getD 0#32))
    (hent_nf : ∀ k < nn.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat + 1)
      (sf.scratch.scratch_buf[neg_off.toNat + k]?.getD 0#32))
    (hmf : (FullMem c sf ⋆ R) mf)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (bveFitAt52 Val Cont c.hdr v (BitVec.ofNat 64 c.scratch_cap)
      (decide (16384 ≤ c.scratch_cap)) occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
      c.pScratchBuf c.pVals c.pTmp c.pWvec ((BitVec.ofNat 64 s0.core.cur_vars) <<< (1 : Nat))
      (BitVec.ofNat 64 c.arena_cap) (BitVec.ofNat 64 c.wcap)
      (v <<< (1 : Nat)) ((v <<< (1 : Nat)) ||| 1#32) np nn push_pos ext_ok lim_cls
      (rp, r_cnt, w_est, fit, ()) true 0#64 0#32 false (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)) mf := by
  dsimp only [bveFitAt52, bveAt52, bvePhaseAt45, bveAt45, sL64, sL32, sL8, sLb,
    sD64, sD32, sD8, sC32, sCb, sT, sE, sB0, sB64, sB32, sBb, sB4, sB6, sB5, sK0,
    sKb, sK4, sK5, sK6]
  c0_hsteps_nogrp
  refine wp_join_state (ts := [.bool]) (α := Bool × FullState) (fun x => (x.1, ()))
    (fun x mw =>
      FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
      x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (x.1 = true → FullResBufOkW F_cur x.2 rp.toNat r_off.toNat) ∧ (FullMem c x.2 ⋆ R) mw)
    (fun _ ⟨wok, sw⟩ mw ⟨hdww, htmkw, hcvw, hflw, hresw, hmw⟩ => by
      dsimp only at hcvw hflw
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hSetInact _ _ _ _ ?_)
        dsimp only [vals, Arg.val]
        refine ⟨c, sw, R, rfl, hdww.1, hmw, ?_⟩
        rw [ite_eq_right (by rw [hcvw]; omega)]
        intro fl' unass' qp' qn' qs' qsi' qss' qf' ql' hp' ps' hl' m_i _ hlen_i hm_i
        let si' : FullState :=
          { sw with
            core := { sw.core with flags := fl', unassigned := unass' }
            scratch := { sw.scratch with
              q_prev := qp', q_next := qn', q_stamp := qs',
              q_search_idx := qsi', q_search_stamp := qss',
              q_first := qf', q_last := ql',
              heap := hp', pos := ps', heap_len := hl' } }
        have hdwi' := s6a_var_fullDenseInvW_setInact13 hdww hlen_i
        c0_hsteps_nogrp
        let sbve : FullState :=
          { si' with scratch := { si'.scratch with bve_cnt := si'.scratch.bve_cnt + 1#64 } }
        have hdwbve := m6_fullDenseInvW_with_scratch hdwi' (sc' := sbve.scratch)
          { hdwi'.1.scratch_ok with } rfl rfl
        have hres_bve : FullResBufOkW F_cur sbve rp.toNat r_off.toNat :=
          s6a_var_resBuf_mono (s := sw) (s' := sbve) rfl (fun _ _ _ => rfl) (hresw hc)
        refine wp_call_of_spec _ _ (hCommit _ _ _ _ ?_)
        refine ⟨c, F0, F_cur, sbve, R, rfl, hdwbve, htmkw.congr rfl rfl,
          hrp_lo, hrp_hi, hres_bve, hm, ?_⟩
        intro cr_r sc mc hdwc htmkc hcvc hflc hcr_disj hcr20 hmc
        dsimp only [sbve, si'] at hcvc hflc
        c0_hsplit
        · c0_hsteps!
          exact hQ 20#64 sc mc hdwc.toDense htmkc (by omega) (by rw [hflc]; exact hflw)
            (Or.inr (Or.inr rfl)) (fun _ => hcr20 hc) hmc
        · c0_hsplit
          · c0_hsteps_nogrp
            refine wp_call_of_spec _ _ (hFlushUnits _ _ _ _ ?_)
            refine fullDenseFlushUnitsM6Spec_intro rfl hdwc hmc ?_
            intro ok_u su mu hdwu hcvu _ hflu _ htmku _ _ _ _ _ hfu hmu
            c0_hsplit
            · c0_hsteps!
              exact hQ cr_r su mu hdwu.toDense (htmkc.congr hcvu htmku)
                (by omega) (by rw [hflu, hflc]; exact hflw) hcr_disj (fun h => hcr20 h) hmu
            · c0_hsteps!
              exact hQ 20#64 su mu hdwu.toDense (htmkc.congr hcvu htmku)
                (by omega) (by rw [hflu, hflc]; exact hflw)
                (Or.inr (Or.inr rfl)) (fun _ => hfu (by simpa using hc)) hmu
          · c0_hsteps!
            exact hQ cr_r sc mc hdwc.toDense htmkc (by omega)
              (by rw [hflc]; exact hflw) hcr_disj hcr20 hmc
      · c0_hsteps!
        let soom : FullState := { sw with core := { sw.core with oom := 1#64 } }
        exact hQ 2#64 soom _ (m6_fullDenseInvW_with_oom hdww 1#64).toDense
          htmkw (by dsimp only [soom]; omega) hflw (Or.inr (Or.inl rfl)) (by simp) hm)
    (fun Jwk hJwk => by
      c0_hsplit
      · refine wp_join_state (ts := [.bool]) (α := Bool × FullState) (fun x => (x.1, ()))
          (fun x mw =>
            FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
            x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
            (x.1 = true → FullResBufOkW F_cur x.2 rp.toNat r_off.toNat) ∧ (FullMem c x.2 ⋆ R) mw)
          (fun _ x mw hx => by c0_hsteps!; exact hJwk x mw hx)
          (fun Jland hJland => by
            c0_hsteps_nogrp
            refine wp_call_of_spec _ _ (hWeaken _ _ _ _ ?_)
            dsimp only [vals, Arg.val]
            refine ⟨c, F0, F_cur, sf, R, rfl, hdwf, htmkf, by rw [hplnl.1, hcvf]; omega,
              by rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega,
              fun k hk => by
                rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                exact s6a_var_bveEntry_weak (hent_pf k hk),
              hmf, ?_⟩
            intro ok1 sw1 mw1 hdww1 htmkw1 hcvw1 hflw1 hscrw1 hrefsw1 hmw1
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hWeakenUnit _ _ _ _ ?_)
              dsimp only [vals, Arg.val]
              refine ⟨c, F0, F_cur, sw1, R, rfl, hdww1, htmkw1,
                by rw [hplnl.2, hcvw1, hcvf]; omega, by omega,
                fun k hk => by
                  rw [hscrw1]
                  have hwk := s6a_var_bveEntry_weak (hent_nf k hk)
                  unfold FullBveWeakItemOk at hwk ⊢; split at hwk
                  · next hb => rw [ite_eq_left hb] at ⊢; rw [hcvw1]; exact hwk
                  · next hb =>
                      rw [ite_eq_right hb] at ⊢; change _ ∈ fullArenaClauseRefs sw1
                      rw [hrefsw1]; exact hwk,
                hmw1, ?_⟩
              intro ok2 sw2 mw2 hdww2 htmkw2 hcvw2 hflw2 hscrw2 _ hmw2
              c0_hsplit
              · c0_hsteps!
                exact hJland (true, sw2) mw2
                  ⟨hdww2, htmkw2, hcvw2.trans (hcvw1.trans hcvf),
                   by rw [hflw2, hflw1]; exact hflf,
                   fun _ => s6a_var_resBuf_mono (s := sf) (s' := sw2) (hcvw2.trans hcvw1)
                     (fun _ _ _ => by rw [hscrw2, hscrw1]) hresf, hmw2⟩
              · c0_hsteps!
                exact hJland (false, sw2) mw2
                  ⟨hdww2, htmkw2, hcvw2.trans (hcvw1.trans hcvf),
                   by rw [hflw2, hflw1]; exact hflf, (fun h => by cases h), hmw2⟩
            · c0_hsteps!
              exact hJland (false, sw1) mw1
                ⟨hdww1, htmkw1, hcvw1.trans hcvf, by rw [hflw1]; exact hflf,
                 (fun h => by cases h), hmw1⟩)
      · refine wp_join_state (ts := [.bool]) (α := Bool × FullState) (fun x => (x.1, ()))
          (fun x mw =>
            FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
            x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
            (x.1 = true → FullResBufOkW F_cur x.2 rp.toNat r_off.toNat) ∧ (FullMem c x.2 ⋆ R) mw)
          (fun _ x mw hx => by c0_hsteps!; exact hJwk x mw hx)
          (fun Jland hJland => by
            c0_hsteps_nogrp
            refine wp_call_of_spec _ _ (hWeaken _ _ _ _ ?_)
            dsimp only [vals, Arg.val]
            refine ⟨c, F0, F_cur, sf, R, rfl, hdwf, htmkf, by rw [hplnl.2, hcvf]; omega,
              by omega, fun k hk => s6a_var_bveEntry_weak (hent_nf k hk), hmf, ?_⟩
            intro ok1 sw1 mw1 hdww1 htmkw1 hcvw1 hflw1 hscrw1 hrefsw1 hmw1
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hWeakenUnit _ _ _ _ ?_)
              dsimp only [vals, Arg.val]
              refine ⟨c, F0, F_cur, sw1, R, rfl, hdww1, htmkw1,
                by rw [hplnl.1, hcvw1, hcvf]; omega,
                by rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega,
                fun k hk => by
                  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add, hscrw1]
                  have hwk := s6a_var_bveEntry_weak (hent_pf k hk)
                  unfold FullBveWeakItemOk at hwk ⊢; split at hwk
                  · next hb => rw [ite_eq_left hb] at ⊢; rw [hcvw1]; exact hwk
                  · next hb =>
                      rw [ite_eq_right hb] at ⊢; change _ ∈ fullArenaClauseRefs sw1
                      rw [hrefsw1]; exact hwk,
                hmw1, ?_⟩
              intro ok2 sw2 mw2 hdww2 htmkw2 hcvw2 hflw2 hscrw2 _ hmw2
              c0_hsplit
              · c0_hsteps!
                exact hJland (true, sw2) mw2
                  ⟨hdww2, htmkw2, hcvw2.trans (hcvw1.trans hcvf),
                   by rw [hflw2, hflw1]; exact hflf,
                   fun _ => s6a_var_resBuf_mono (s := sf) (s' := sw2) (hcvw2.trans hcvw1)
                     (fun _ _ _ => by rw [hscrw2, hscrw1]) hresf, hmw2⟩
              · c0_hsteps!
                exact hJland (false, sw2) mw2
                  ⟨hdww2, htmkw2, hcvw2.trans (hcvw1.trans hcvf),
                   by rw [hflw2, hflw1]; exact hflf, (fun h => by cases h), hmw2⟩
            · c0_hsteps!
              exact hJland (false, sw1) mw1
                ⟨hdww1, htmkw1, hcvw1.trans hcvf, by rw [hflw1]; exact hflf,
                 (fun h => by cases h), hmw1⟩))

private theorem s6a_bve_var_defrag_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s2 si : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {v occ_lim neg_off pos_mask neg_mask gf_idx rg_idx np nn : BitVec 32}
    {r_off lim_cls rp r_cnt w_est : BitVec 64} {push_pos ext_ok fit : Bool}
    {mi : Mem 64} {Jpre : Cont [.bool]}
    (hdwi : FullDenseInvW c F0 F_cur si) (htmki : TmkZero si)
    (hcvi : si.core.cur_vars = s0.core.cur_vars)
    (hari : si.core.arena = s2.core.arena) (hali : si.core.arena_len = s2.core.arena_len)
    (hfli : si.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hres_i : FullResBufOkW F_cur si rp.toNat r_off.toNat)
    (hkeep_pi : ∀ k < np.toNat, si.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?)
    (hkeep_ni : ∀ k < nn.toNat,
      si.scratch.scratch_buf[neg_off.toNat + k]? = s2.scratch.scratch_buf[neg_off.toNat + k]?)
    (hmi : (FullMem c si ⋆ R) mi)
    (hJpre : ∀ (args : Tup Val [.bool]) mf,
      (∃ sf : FullState,
        FullDenseInvW c F0 F_cur sf ∧ TmkZero sf ∧
        sf.core.cur_vars = s0.core.cur_vars ∧ sf.core.arena = s2.core.arena ∧
        sf.core.arena_len = s2.core.arena_len ∧ sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
        FullResBufOkW F_cur sf rp.toNat r_off.toNat ∧
        (∀ k < np.toNat, sf.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
        (∀ k < nn.toNat,
          sf.scratch.scratch_buf[neg_off.toNat + k]? = s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
        (FullMem c sf ⋆ R) mf) →
      Jpre args mf) :
    wp Γ Q X (bveDefragAt52 Val Cont c.hdr v (BitVec.ofNat 64 c.scratch_cap)
      (decide (16384 ≤ c.scratch_cap)) occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
      c.pScratchBuf c.pVals c.pTmp c.pWvec ((BitVec.ofNat 64 s0.core.cur_vars) <<< (1 : Nat))
      (BitVec.ofNat 64 c.arena_cap) (BitVec.ofNat 64 c.wcap)
      (v <<< (1 : Nat)) ((v <<< (1 : Nat)) ||| 1#32) np nn push_pos ext_ok lim_cls
      (rp, r_cnt, w_est, fit, ()) Jpre 0#64 0#32 false (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)) mi := by
  dsimp only [bveDefragAt52, bveAt52, bvePhaseAt45, bveAt45, sL64, sL32, sL8, sLb,
    sD64, sD32, sD8, sC32, sCb, sT, sE, sB0, sB64, sB32, sBb, sB4, sB6, sB5, sK0,
    sKb, sK4, sK5, sK6]
  c0_hsplit
  · c0_hsteps_nogrp
    refine wp_join_state (ts := [.bool]) (α := Bool × FullState) (fun x => (x.1, ()))
      (fun x md =>
        FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
        x.2.core.arena = s2.core.arena ∧ x.2.core.arena_len = s2.core.arena_len ∧
        x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ FullResBufOkW F_cur x.2 rp.toNat r_off.toNat ∧
        (∀ k < np.toNat, x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
        (∀ k < nn.toNat,
          x.2.scratch.scratch_buf[neg_off.toNat + k]? =
            s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
        (FullMem c x.2 ⋆ R) md)
      (fun _ ⟨b45, s45⟩ md h45 => by c0_hsteps!; exact hJpre (b45, ()) md ⟨s45, h45⟩)
      (fun J45p hJ45p => by
        c0_hsplit
        · c0_hsteps!
          exact hJ45p (false, si) mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
            hres_i, hkeep_pi, hkeep_ni, hmi⟩
        · c0_hsteps_nogrp
          refine wp_join_state (ts := [.bool]) (α := Bool × FullState) (fun x => (x.1, ()))
            (fun x md =>
              FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
              x.2.core.arena = s2.core.arena ∧ x.2.core.arena_len = s2.core.arena_len ∧
              x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
              FullResBufOkW F_cur x.2 rp.toNat r_off.toNat ∧
              (∀ k < np.toNat, x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
              (∀ k < nn.toNat,
                x.2.scratch.scratch_buf[neg_off.toNat + k]? =
                  s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
              (FullMem c x.2 ⋆ R) md)
            (fun _ ⟨b52, s52⟩ md h52 => by c0_hsteps!; exact hJ45p (b52, s52) md h52)
            (fun J52p hJ52p => by
              c0_hsplit
              · c0_hsteps_nogrp
                refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                  (fun sd md =>
                    FullDenseInvW c F0 F_cur sd ∧ TmkZero sd ∧
                    sd.core.cur_vars = s0.core.cur_vars ∧ sd.core.arena = s2.core.arena ∧
                    sd.core.arena_len = s2.core.arena_len ∧
                    sd.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                    FullResBufOkW F_cur sd rp.toNat r_off.toNat ∧
                    (∀ k < np.toNat, sd.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                    (∀ k < nn.toNat,
                      sd.scratch.scratch_buf[neg_off.toNat + k]? =
                        s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
                    (FullMem c sd ⋆ R) md)
                  (fun _ sd md ⟨hdwd, htmkd, hcvd, hard, hald, hfld, hresd,
                      hkeep_pd, hkeep_nd, hmd⟩ => by
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [.bool]) (α := Bool × FullState)
                      (fun x => (x.1, ()))
                      (fun x md' =>
                        FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                        x.2.core.cur_vars = s0.core.cur_vars ∧
                        x.2.core.arena = s2.core.arena ∧ x.2.core.arena_len = s2.core.arena_len ∧
                        x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                        FullResBufOkW F_cur x.2 rp.toNat r_off.toNat ∧
                        (∀ k < np.toNat,
                          x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                        (∀ k < nn.toNat,
                          x.2.scratch.scratch_buf[neg_off.toNat + k]? =
                            s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
                        (FullMem c x.2 ⋆ R) md')
                      (fun _ ⟨b60, s60⟩ md' h60 => by c0_hsteps!; exact hJ52p (b60, s60) md' h60)
                      (fun J60p hJ60p => by
                        c0_hsplit
                        · c0_hsteps!
                          exact hJ60p (false, sd) md ⟨hdwd, htmkd, hcvd, hard, hald, hfld,
                            hresd, hkeep_pd, hkeep_nd, hmd⟩
                        · c0_hsteps!
                          exact hJ60p (fit, sd) md ⟨hdwd, htmkd, hcvd, hard, hald, hfld,
                            hresd, hkeep_pd, hkeep_nd, hmd⟩))
                  (fun Jd hJd => by
                    c0_hsplit
                    · c0_hsteps_nogrp
                      refine wp_call_of_spec _ _ (hDefrag _ _ _ _ ?_)
                      refine ⟨c, si, R, rfl, hdwi.1, (m6_denseWatchesInv_of_w hdwi).layout, hmi, ?_⟩
                      intro wvec' wstk' wlen' wsort' md sd hlen_d hlay_d _ hslice_d hmd
                      have hdwd := m6_fullDenseInvW_of_wstackDefrag hdwi hlen_d hlay_d hslice_d
                      c0_hsteps!
                      exact hJd sd md ⟨hdwd, htmki, hcvi, hari, hali, hfli,
                        s6a_var_resBuf_mono (s := si) (s' := sd) rfl (fun _ _ _ => rfl) hres_i,
                        hkeep_pi, hkeep_ni, hmd⟩
                    · c0_hsteps!
                      exact hJd si mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
                        hres_i, hkeep_pi, hkeep_ni, hmi⟩)
              · c0_hsteps!
                exact hJ52p (fit, si) mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
                  hres_i, hkeep_pi, hkeep_ni, hmi⟩))
  · c0_hsteps!
    exact hJpre (fit, ()) mi ⟨si, hdwi, htmki, hcvi, hari, hali, hfli,
      hres_i, hkeep_pi, hkeep_ni, hmi⟩

private theorem s6a_bve_var_phase_wp (Γ : Env)
    (hWeaken : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hWeakenUnit : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken_unit_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, step13SetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGatesFid : ∀ a m Q X, FullM8CoreParity.m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X)
    (hGatesM7 : ∀ a m Q X, FullM7BveGates.fullBveGatesM7Spec a m Q X →
      Γ "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s2 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {v occ_lim neg_off pos_mask neg_mask gf_idx rg_idx np nn : BitVec 32}
    {r_off : BitVec 64} {push_pos ext_ok : Bool} {m2 : Mem 64}
    (hmx : c.max_vars < 2 * 2 ^ 28) (hsc : c.scratch_cap ≤ 2 ^ 29)
    (hsc2048 : 2048 ≤ c.scratch_cap)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars) (hv_lt : v.toNat < s0.core.cur_vars)
    (hplnl : (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
      ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1)
    (hneg_eq : neg_off = occ_lim) (hocc_le_roff : occ_lim.toNat + occ_lim.toNat ≤ r_off.toNat)
    (hroff_le_sc : r_off.toNat ≤ c.scratch_cap)
    (hgf_lt : gf_idx.toNat < r_off.toNat) (hrg_lt : rg_idx.toNat < r_off.toNat)
    (hpm_lt_roff : ∀ i : BitVec 32, i.toNat < occ_lim.toNat →
      ((pos_mask + (i >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat)
    (hnm_lt_roff : ∀ j : BitVec 32, j.toNat < occ_lim.toNat →
      ((neg_mask + (j >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat)
    (hm8_eqs : 16384 ≤ c.scratch_cap → occ_lim = 2001#32 ∧ neg_off.toNat = 2001)
    (hm7_eqs : c.scratch_cap < 16384 → occ_lim = 512#32 ∧ neg_off.toNat = 512)
    (hnp_le : np.toNat ≤ occ_lim.toNat) (hnn_le : nn.toNat ≤ occ_lim.toNat)
    (hdw2 : FullDenseInvW c F0 F_cur s2) (htmk0 : TmkZero s2)
    (hcv2 : s2.core.cur_vars = s0.core.cur_vars) (hfl2 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hent_p2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
      (s2.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n2' : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
      (s2.scratch.scratch_buf[neg_off.toNat + j]?.getD 0#32))
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (bvePhaseAt45 Val Cont c.hdr v (BitVec.ofNat 64 c.scratch_cap)
      (decide (16384 ≤ c.scratch_cap)) occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
      c.pScratchBuf c.pVals c.pTmp c.pWvec ((BitVec.ofNat 64 s0.core.cur_vars) <<< (1 : Nat))
      (BitVec.ofNat 64 c.arena_cap) (BitVec.ofNat 64 c.wcap)
      (v <<< (1 : Nat)) ((v <<< (1 : Nat)) ||| 1#32) np nn push_pos ext_ok
      0#64 0#32 false (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => True)) m2 := by
  dsimp only [bvePhaseAt45, bveAt45, sL64, sL32, sL8, sLb, sD64, sD32, sD8, sC32, sCb,
    sT, sE, sB0, sB64, sB32, sBb, sB4, sB6, sB5, sK0, sKb, sK4, sK5, sK6]
  have hneg_off_lt : neg_off.toNat + occ_lim.toNat ≤ c.scratch_cap := by rw [hneg_eq]; omega
  c0_hsteps_nogrp
  refine wp_join_state (ts := [i64, i64, i64, .bool])
    (α := BitVec 64 × BitVec 64 × BitVec 64 × Bool × FullState)
    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ()))
    (fun x mi =>
      let si := x.2.2.2.2; let rp := x.1
      FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧ si.core.cur_vars = s0.core.cur_vars ∧
      si.core.arena = s2.core.arena ∧ si.core.arena_len = s2.core.arena_len ∧
      si.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ r_off.toNat ≤ rp.toNat ∧
      rp.toNat ≤ c.scratch_cap ∧ FullResBufOkW F_cur si rp.toNat r_off.toNat ∧
      (∀ k < np.toNat, si.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
      (∀ k < nn.toNat,
        si.scratch.scratch_buf[neg_off.toNat + k]? = s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
      (FullMem c si ⋆ R) mi)
    (fun _ ⟨rp, r_cnt, w_est, fit, si⟩ mi
        ⟨hdwi, htmki, hcvi, hari, hali, hfli, hrp_lo, hrp_hi, hres_i, hkeep_pi, hkeep_ni, hmi⟩ => by
      c0_hsteps_nogrp
      refine wp_join_state (ts := [.bool]) (α := Bool × FullState) (fun x => (x.1, ()))
        (fun x mp =>
          FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
          x.2.core.arena = s2.core.arena ∧ x.2.core.arena_len = s2.core.arena_len ∧
          x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ FullResBufOkW F_cur x.2 rp.toNat r_off.toNat ∧
          (∀ k < np.toNat, x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
          (∀ k < nn.toNat,
            x.2.scratch.scratch_buf[neg_off.toNat + k]? =
              s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
          (FullMem c x.2 ⋆ R) mp)
        (fun _ ⟨fit_f, sf⟩ mf ⟨hdwf, htmkf, hcvf, harf, half, hflf, hresf, hkeep_pf, hkeep_nf,
            hmf⟩ => by
          dsimp only at hcvf harf half hflf
          have hent_pf : ∀ k < np.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat)
              (sf.scratch.scratch_buf[k]?.getD 0#32) := fun k hk => by
            rw [hkeep_pf k hk]
            exact m8_bveEntry_congr_core (hent_p2 k hk) (hcvf.trans hcv2.symm) harf half
          have hent_nf : ∀ k < nn.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat + 1)
              (sf.scratch.scratch_buf[neg_off.toNat + k]?.getD 0#32) := fun k hk => by
            rw [hkeep_nf k hk]
            exact m8_bveEntry_congr_core (hent_n2' k hk) (hcvf.trans hcv2.symm) harf half
          c0_hsplit
          · exact s6a_bve_var_fit_wp Γ hWeaken hWeakenUnit hSetInact hCommit hFlushUnits
              (c := c) (F0 := F0) (F_cur := F_cur) (s0 := s0) (sf := sf) (R := R) (Q := Q) (X := X)
              (v := v) (occ_lim := occ_lim) (neg_off := neg_off) (pos_mask := pos_mask)
              (neg_mask := neg_mask) (gf_idx := gf_idx) (rg_idx := rg_idx) (np := np) (nn := nn)
              (r_off := r_off) (lim_cls := 0#64) (rp := rp) (r_cnt := r_cnt) (w_est := w_est)
              (fit := fit) (push_pos := push_pos) (ext_ok := ext_ok) (mf := mf)
              hmx hcv_le hv_lt hplnl hneg_eq hneg_off_lt hnp_le hnn_le hrp_lo hrp_hi hdwf htmkf
              hcvf hflf hresf hent_pf hent_nf hmf hQ
          · c0_hsteps!
            exact hQ 1#64 sf mf hdwf.toDense htmkf (by rw [hcvf]; exact Nat.le_refl _) hflf
              (Or.inl rfl) (by simp) hmf)
        (fun Jpre hJpre =>
          s6a_bve_var_defrag_wp Γ hDefrag (c := c) (F0 := F0) (F_cur := F_cur)
            (s0 := s0) (s2 := s2) (si := si) (R := R) (Q := Q) (X := X)
            (v := v) (occ_lim := occ_lim) (neg_off := neg_off) (pos_mask := pos_mask)
            (neg_mask := neg_mask) (gf_idx := gf_idx) (rg_idx := rg_idx) (np := np) (nn := nn)
            (r_off := r_off) (lim_cls := 0#64) (rp := rp) (r_cnt := r_cnt) (w_est := w_est)
            (fit := fit) (push_pos := push_pos) (ext_ok := ext_ok) (mi := mi) (Jpre := Jpre)
            hdwi htmki hcvi hari hali hfli hres_i hkeep_pi
            hkeep_ni hmi fun args mf ⟨sf, hsf⟩ => hJpre (args.1, sf) mf hsf))
    (fun J32 hJ32 => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
          (fun s3 m3 =>
            FullDenseInvW c F0 F_cur s3 ∧ TmkZero s3 ∧ s3.core.cur_vars = s0.core.cur_vars ∧
            s3.core.arena = s2.core.arena ∧ s3.core.arena_len = s2.core.arena_len ∧
            s3.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
            (∀ i < np.toNat, s3.scratch.scratch_buf[i]? = s2.scratch.scratch_buf[i]?) ∧
            (∀ j < nn.toNat,
              s3.scratch.scratch_buf[neg_off.toNat + j]? =
                s2.scratch.scratch_buf[neg_off.toNat + j]?) ∧
            (FullMem c s3 ⋆ R) m3)
          (fun _ s3 m3 ⟨hdw3, htmk3, hcv3, har3, hal3, hfl3, hp3, hn3, hm3⟩ => by
            have hent_p3 : ∀ i < np.toNat, FullBveEntryOkW F_cur s3 (2 * v.toNat)
                (s3.scratch.scratch_buf[i]?.getD 0#32) := fun i hi => by
              rw [hp3 i hi]
              exact m8_bveEntry_congr_core (hent_p2 i hi) (hcv3.trans hcv2.symm) har3 hal3
            have hent_n3 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s3 (2 * v.toNat + 1)
                (s3.scratch.scratch_buf[neg_off.toNat + j]?.getD 0#32) := fun j hj => by
              rw [hn3 j hj]
              exact m8_bveEntry_congr_core (hent_n2' j hj) (hcv3.trans hcv2.symm) har3 hal3
            have hpl_vl : ((v <<< (1 : Nat)).setWidth 64).toNat < s3.core.vals.length := by
              rw [hdw3.1.core_ok.vals_len, m6_zext32_toNat, hplnl.1]
              have := hdw3.1.core_ok.cur_vars_le; omega
            c0_hsplit
            · c0_hsteps!
              exact hQ 20#64 s3 m3 hdw3.toDense htmk3 (by rw [hcv3]; exact Nat.le_refl _) hfl3
                (Or.inr (Or.inr rfl)) (fun _ => hdw3.toDense.inconsistent_unsat hc) hm3
            · c0_hsplit
              · c0_hsteps!
                exact hQ 1#64 s3 m3 hdw3.toDense htmk3 (by rw [hcv3]; exact Nat.le_refl _) hfl3
                  (Or.inl rfl) (by simp) hm3
              · clear hc
                have hgf_sc : (gf_idx.setWidth 64).toNat < s3.scratch.scratch_buf.length := by
                  rw [hdw3.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
                have hrg_sc : (rg_idx.setWidth 64).toNat < s3.scratch.scratch_buf.length := by
                  rw [hdw3.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
                c0_hsteps_nogrp
                refine s6a_bve_var_resolve_loop_wp Γ hResPair hAssign
                  (occ_lim := occ_lim) (neg_off := neg_off) (pos_mask := pos_mask)
                  (neg_mask := neg_mask) (r_off := r_off)
                  (lim_cls := np.setWidth 64 + nn.setWidth 64 + s2.scratch.elim_bound)
                  (gf := (s3.scratch.scratch_buf[(gf_idx.setWidth 64).toNat]'hgf_sc != 0#32))
                  (rg := (s3.scratch.scratch_buf[(rg_idx.setWidth 64).toNat]'hrg_sc != 0#32))
                  (ext_ok := ext_ok) (J52 := J32) rfl
                  hmx hsc hv_lt hcv_le hneg_eq hocc_le_roff
                  hroff_le_sc hpm_lt_roff hnm_lt_roff hnp_le hnn_le hdw3 htmk3 hcv3 har3 hal3 hfl3
                  hp3 hn3 hent_p3 hent_n3 hm3 hQ (fun args mf ⟨sf, hsf⟩ =>
                    hJ32 (args.1, args.2.1, args.2.2.1, args.2.2.2.1, sf) mf hsf))
          (fun Jg hJg => by
            c0_hsplit
            · have hge16 : 16384 ≤ c.scratch_cap := hc
              obtain ⟨ho2001, hneg2001⟩ := hm8_eqs hge16
              have hnp2001 : np.toNat ≤ 2001 := by rw [ho2001] at hnp_le; exact hnp_le
              have hnn2001 : nn.toNat ≤ 2001 := by rw [ho2001] at hnn_le; exact hnn_le
              c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hGatesFid _ _ _ _ ?_)
              refine m8BveGatesSpec_intro rfl hdw2 htmk0 hge16 (by rw [hcv2]; exact hv_lt)
                hnp2001 hnn2001 hent_p2 (fun j hj => by rw [← hneg2001]; exact hent_n2' j hj)
                hm2 ?_
              intro s3 m3 hdw3 htmk3 hcv3 har3 hal3 hfl3 hp3 hn3 hm3
              c0_hsteps!
              exact hJg s3 m3 ⟨hdw3, htmk3, hcv3.trans hcv2, har3, hal3,
                le_trans hfl3 hfl2, hp3, fun j hj => by rw [hneg2001]; exact hn3 j hj, hm3⟩
            · have hlt16 : c.scratch_cap < 16384 := by omega
              obtain ⟨ho512, hneg512⟩ := hm7_eqs hlt16
              have hnp512 : np.toNat ≤ 512 := by rw [ho512] at hnp_le; exact hnp_le
              have hnn512 : nn.toNat ≤ 512 := by rw [ho512] at hnn_le; exact hnn_le
              c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hGatesM7 _ _ _ _ ?_)
              refine fullBveGatesM7Spec_intro rfl hdw2 htmk0 (by omega)
                (by rw [hcv2]; exact hv_lt) hnp512 hnn512 hent_p2
                (fun j hj => by rw [← hneg512]; exact hent_n2' j hj) hm2 ?_
              intro s3 m3 hdw3 htmk3 hcv3 har3 hal3 hfl3 hp3 hn3 hm3
              c0_hsteps!
              exact hJg s3 m3 ⟨hdw3, htmk3, hcv3.trans hcv2, har3, hal3,
                le_trans hfl3 hfl2, hp3, fun j hj => by rw [hneg512]; exact hn3 j hj, hm3⟩)
      · c0_hsteps!
        exact hJ32 (r_off, 0#64, 0#64, ext_ok, s2) m2
          ⟨hdw2, htmk0, hcv2, rfl, rfl, hfl2, Nat.le_refl _, hroff_le_sc,
           .nil, fun _ _ => rfl, fun _ _ => rfl, hm2⟩)

private def bvePostLayout (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (d64 : V i64) (db : V .bool) (dJ32 : L [i32]) (dJ64 : L [i64]) : Expr V L [i64] :=
  FullFidelityStep12B.full_bve_var_m7_body V L (h, v, ())
    |> sL64 d64 |> sD64 scap |> sLb db |> sE
    |> sLb use_m8
    |> sB32 dJ32 occ_lim |> sB32 dJ32 neg_off |> sB32 dJ32 pos_mask |> sB32 dJ32 neg_mask
    |> sB32 dJ32 gf_idx |> sB32 dJ32 rg_idx |> sB64 dJ64 r_off

private def bveJ2000Body (V : Ty → Type) (L : List Ty → Type) (h : V i64) (v : V i32)
    (scap : V i64) (use_m8 : V .bool)
    (occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : V i32) (r_off : V i64)
    (scr vals tmp wvec cv2 acap wcap : V i64) (pl nl np nn : V i32)
    (d64 : V i64) (_d32 : V i32) (db : V .bool)
    (dJ0 : L []) (dJ64 : L [i64]) (dJ32 : L [i32]) : Expr V L [i64] :=
  bvePostLayout V L h v scap use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
      d64 db dJ32 dJ64
    |> sL64 d64 |> sD64 scr |> sL64 d64 |> sD64 vals
    |> sL64 d64 |> sD64 tmp |> sL64 d64 |> sD64 wvec
    |> sL64 d64 |> sD64 d64 |> sL64 d64 |> sL64 cv2
    |> sL64 d64 |> sD64 acap |> sL64 d64 |> sD64 wcap
    |> sL32 pl |> sL32 nl |> sC32 np
    |> sL64 d64 |> sL64 d64 |> sL64 d64 |> sC32 nn
    |> sLb db |> sE |> sLb db |> sE |> sB0 dJ0

private theorem s6a_bve_var_ext_wp (Γ : Env)
    (hExtNeed : ∀ a m Q X, Full.fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hWeakenUnit : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken_unit_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, step13SetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGatesFid : ∀ a m Q X, FullM8CoreParity.m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X)
    (hGatesM7 : ∀ a m Q X, FullM7BveGates.fullBveGatesM7Spec a m Q X →
      Γ "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s2 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {v occ_lim neg_off pos_mask neg_mask gf_idx rg_idx np nn : BitVec 32}
    {r_off : BitVec 64} {m2 : Mem 64}
    (hmx : c.max_vars < 2 * 2 ^ 28) (hsc : c.scratch_cap ≤ 2 ^ 29)
    (hsc2048 : 2048 ≤ c.scratch_cap)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars) (hv_lt : v.toNat < s0.core.cur_vars)
    (hplnl : (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
      ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1)
    (hneg_eq : neg_off = occ_lim) (hocc_le_roff : occ_lim.toNat + occ_lim.toNat ≤ r_off.toNat)
    (hroff_le_sc : r_off.toNat ≤ c.scratch_cap)
    (hneg_off_lt : neg_off.toNat + occ_lim.toNat ≤ c.scratch_cap)
    (hgf_lt : gf_idx.toNat < r_off.toNat) (hrg_lt : rg_idx.toNat < r_off.toNat)
    (hpm_lt_roff : ∀ i : BitVec 32, i.toNat < occ_lim.toNat →
      ((pos_mask + (i >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat)
    (hnm_lt_roff : ∀ j : BitVec 32, j.toNat < occ_lim.toNat →
      ((neg_mask + (j >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat)
    (hm8_eqs : 16384 ≤ c.scratch_cap → occ_lim = 2001#32 ∧ neg_off.toNat = 2001)
    (hm7_eqs : c.scratch_cap < 16384 → occ_lim = 512#32 ∧ neg_off.toNat = 512)
    (hnp_le : np.toNat ≤ occ_lim.toNat) (hnn_le : nn.toNat ≤ occ_lim.toNat)
    (hdw2 : FullDenseInvW c F0 F_cur s2) (htmk0 : TmkZero s2)
    (hcv2 : s2.core.cur_vars = s0.core.cur_vars)
    (hfl2 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hent_p2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
      (s2.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n2' : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
      (s2.scratch.scratch_buf[neg_off.toNat + j]?.getD 0#32))
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (bveJ2000Body Val Cont c.hdr v (BitVec.ofNat 64 c.scratch_cap)
      (decide (16384 ≤ c.scratch_cap)) occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
      c.pScratchBuf c.pVals c.pTmp c.pWvec ((BitVec.ofNat 64 s0.core.cur_vars) <<< (1 : Nat))
      (BitVec.ofNat 64 c.arena_cap) (BitVec.ofNat 64 c.wcap)
      (v <<< (1 : Nat)) ((v <<< (1 : Nat)) ||| 1#32) np nn 0#64 0#32 false
      (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)) m2 := by
  dsimp only [bveJ2000Body, bvePostLayout, sL64, sL32, sL8, sLb, sD64, sD32, sD8, sC32, sCb,
    sT, sE, sB0, sB64, sB32, sBb, sB4, sB6, sB5, sK0, sKb, sK4, sK5, sK6]
  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
    (fun _ => True) ?_ (fun Jep hJep => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hExtNeed _ _ _ _ ?_)
        dsimp only [vals, Arg.val]
        refine ⟨c, s2, R, rfl, hdw2.1, by simp; omega, fun i hi => by
          rw [show ((0 : BitVec 32)).toNat = 0 from rfl, Nat.zero_add]
          exact s6a_var_bveEntry_extNeed hdw2 (hent_p2 i hi), hm2, ?_⟩
        intro en1; c0_hsteps!; exact hJep en1 trivial
      · c0_hsteps!; exact hJep 0#64 trivial)
  intro _ ext_p _
  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
    (fun _ => True) ?_ (fun Jen hJen => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hExtNeed _ _ _ _ ?_)
        dsimp only [vals, Arg.val]
        refine ⟨c, s2, R, rfl, hdw2.1, by omega, fun j hj => by
          exact s6a_var_bveEntry_extNeed hdw2 (hent_n2' j hj), hm2, ?_⟩
        intro en2; c0_hsteps!; exact hJen en2 trivial
      · c0_hsteps!; exact hJen 0#64 trivial)
  intro _ ext_n _
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
    (fun _ => True) ?_ (fun Jneed hJneed => by
      refine wp_join_state_pure (ts := []) (α := Unit) (fun _ => ()) (fun _ => True) ?_ ?_
      · intro _ _ _
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
          (fun _ => True) ?_ ?_
        · intro _ x _; c0_hsteps!; exact hJneed x trivial
        · intro Jz hJz
          c0_hsplit
          · c0_hsteps!; exact hJz 1#64 trivial
          · c0_hsplit
            · c0_hsteps!; exact hJz 1#64 trivial
            · c0_hsteps!; exact hJz 0#64 trivial
      · intro Jthen hJthen
        c0_hsplit
        · c0_hsteps!; exact hJthen () trivial
        · c0_hsplit
          · c0_hsteps!; exact hJthen () trivial
          · refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
              (fun _ => True) ?_ ?_
            · intro _ x _; c0_hsteps!; exact hJneed (x + 1#64) trivial
            · intro Jp hJp
              c0_hsplit <;> (c0_hsteps!; exact hJp _ trivial))
  intro _ ext_need _
  refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun x => (x, ()))
    (fun _ => True) ?_ (fun Jeok hJeok => by
      c0_hsplit
      · c0_hsplit
        · c0_hsteps!; exact hJeok true trivial
        · c0_hsteps!; exact hJeok false trivial
      · c0_hsteps!; exact hJeok false trivial)
  intro _ ext_ok _
  c0_hsteps_nogrp
  refine wp_join0 (P := fun mj => mj = m2)
    (fun _ mj hmj => by
      rcases hmj.symm with rfl
      dsimp only [Blocks.get]
      exact s6a_bve_var_phase_wp Γ hWeaken hWeakenUnit hSetInact hGatesFid hGatesM7
        hResPair hAssign hDefrag hCommit hFlushUnits
        (c := c) (F0 := F0) (F_cur := F_cur) (s0 := s0) (s2 := s2) (R := R)
        (Q := Q) (X := X) (v := v) (occ_lim := occ_lim) (neg_off := neg_off)
        (pos_mask := pos_mask) (neg_mask := neg_mask) (gf_idx := gf_idx)
        (rg_idx := rg_idx) (np := np) (nn := nn) (r_off := r_off)
        (push_pos := ext_p.ule ext_n) (ext_ok := ext_ok) (m2 := m2)
        hmx hsc hsc2048 hcv_le
        hv_lt hplnl hneg_eq hocc_le_roff hroff_le_sc hgf_lt hrg_lt hpm_lt_roff
        hnm_lt_roff hm8_eqs hm7_eqs hnp_le hnn_le hdw2 htmk0 hcv2 hfl2
        hent_p2 hent_n2' hm2 hQ)
    (fun J25 hJ25 =>
      s6a_bve_var_fast_wp Γ hWeakenUnit hSetInact
        (pos_mask := pos_mask) (neg_mask := neg_mask) (gf_idx := gf_idx)
        (rg_idx := rg_idx) (r_off := r_off)
        (push_pos := ext_p.ule ext_n) (ext_ok := ext_ok)
        hmx hcv_le hv_lt hplnl hneg_eq hneg_off_lt hnp_le hnn_le hdw2 hcv2
        hfl2 htmk0 hent_p2 hent_n2' hm2 hQ hJ25)

private theorem s6a_bve_var_collect_wp (Γ : Env)
    (hCollect : ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m7" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, Full.fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hWeakenUnit : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken_unit_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, step13SetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGatesFid : ∀ a m Q X, FullM8CoreParity.m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X)
    (hGatesM7 : ∀ a m Q X, FullM7BveGates.fullBveGatesM7Spec a m Q X →
      Γ "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {v occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : BitVec 32}
    {r_off : BitVec 64} {use_m8 : Bool} {m0 : Mem 64}
    (huse_m8 : use_m8 = decide (16384 ≤ c.scratch_cap))
    (hmx : c.max_vars < 2 * 2 ^ 28) (hsc : c.scratch_cap ≤ 2 ^ 29)
    (hsc2048 : 2048 ≤ c.scratch_cap)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars) (hv_lt : v.toNat < s0.core.cur_vars)
    (hplnl : (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
      ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1)
    (hplnl1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
      ((v <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = 2 * v.toNat + 1)
    (hneg_eq : neg_off = occ_lim) (hocc_le_roff : occ_lim.toNat + occ_lim.toNat ≤ r_off.toNat)
    (hroff_le_sc : r_off.toNat ≤ c.scratch_cap)
    (hgf_lt : gf_idx.toNat < r_off.toNat) (hrg_lt : rg_idx.toNat < r_off.toNat)
    (hpm_lt_roff : ∀ i : BitVec 32, i.toNat < occ_lim.toNat →
      ((pos_mask + (i >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat)
    (hnm_lt_roff : ∀ j : BitVec 32, j.toNat < occ_lim.toNat →
      ((neg_mask + (j >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat)
    (hm8_eqs : 16384 ≤ c.scratch_cap → occ_lim = 2001#32 ∧ neg_off.toNat = 2001)
    (hm7_eqs : c.scratch_cap < 16384 → occ_lim = 512#32 ∧ neg_off.toNat = 512)
    (hdw0 : FullDenseInvW c F0 F_cur s0) (htmk0 : TmkZero s0)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (bvePostLayout Val Cont c.hdr v (BitVec.ofNat 64 c.scratch_cap)
      use_m8 occ_lim neg_off pos_mask neg_mask gf_idx rg_idx r_off
      0#64 false (fun _ _ => True) (fun _ _ => True)) m0 := by
  subst huse_m8
  dsimp only [bvePostLayout, sL64, sL32, sL8, sLb, sD64, sD32, sD8, sC32, sCb,
    sT, sE, sB0, sB64, sB32, sBb, sB4, sB6, sB5, sK0, sKb, sK4, sK5, sK6]
  have hneg_off_lt : neg_off.toNat + occ_lim.toNat ≤ c.scratch_cap := by rw [hneg_eq]; omega
  have hneg_ptr : c.pScratchBuf + neg_off.setWidth 64 * 4#64 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * neg_off.toNat) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, m6_zext32_toNat, show (4#64 : BitVec 64).toNat = 4 from rfl,
      BitVec.toNat_ofNat]
    have : neg_off.toNat < 2 ^ 32 := neg_off.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hCollect _ _ _ _ ?_)
  dsimp only [vals, Arg.val]
  refine ⟨c, F0, F_cur, s0, 0, R, rfl, hdw0, by rw [hplnl.1]; omega,
    by simp, by simp; omega, hm0, ?_⟩
  intro np scr1 m1; dsimp only; intro hsc1 hout1 hnp_ok hm1
  let s1 : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
  have hdw1 : FullDenseInvW c F0 F_cur s1 := m8_fullDenseInvW_scr hdw0 hsc1
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hCollect _ _ _ _ ?_)
  dsimp only [vals, Arg.val]
  refine ⟨c, F0, F_cur, s1, neg_off.toNat, R, rfl, hdw1,
    by dsimp only [s1]; rw [hplnl1.2]; omega, hneg_ptr, hneg_off_lt, hm1, ?_⟩
  intro nn scr2 m2; dsimp only; intro hsc2 hout2 hnn_ok hm2
  let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
  have hdw2 : FullDenseInvW c F0 F_cur s2 := m8_fullDenseInvW_scr hdw1 hsc2
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s2 m2 hdw2.toDense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
      (by simp) hm2
  · have hnp_ne : np ≠ 0xFFFFFFFF#32 := hc
    c0_hsplit
    · c0_hsteps!
      exact hQ 1#64 s2 m2 hdw2.toDense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
        (by simp) hm2
    · have hnn_ne : nn ≠ 0xFFFFFFFF#32 := hc
      obtain ⟨hnp_le, hent_p1⟩ := hnp_ok.resolve_left hnp_ne
      obtain ⟨hnn_le, hent_n2⟩ := hnn_ok.resolve_left hnn_ne
      have hent_p2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
          (scr2[i]?.getD 0#32) := fun i hi => by
        rw [hout2 i (by omega) (Or.inl (by rw [hneg_eq]; omega))]
        have h := hent_p1 i hi; rw [Nat.zero_add, hplnl.1] at h
        exact m8_bveEntry_congr_core h rfl rfl rfl
      have hent_n2' : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
          (scr2[neg_off.toNat + j]?.getD 0#32) := fun j hj => by
        have h := hent_n2 j hj; rw [hplnl1.2] at h; exact h
      c0_hsteps_nogrp
      refine wp_join0 (P := fun mj => mj = m2)
        (fun _ mj hmj => by
          rcases hmj.symm with rfl
          exact s6a_bve_var_ext_wp Γ hExtNeed hWeaken hWeakenUnit hSetInact hGatesFid hGatesM7
            hResPair hAssign hDefrag hCommit hFlushUnits
            (c := c) (F0 := F0) (F_cur := F_cur) (s0 := s0) (s2 := s2) (R := R) (Q := Q) (X := X)
            (v := v) (occ_lim := occ_lim) (neg_off := neg_off) (pos_mask := pos_mask)
            (neg_mask := neg_mask) (gf_idx := gf_idx) (rg_idx := rg_idx) (np := np) (nn := nn)
            (r_off := r_off) (m2 := m2)
            hmx hsc hsc2048 hcv_le hv_lt
            hplnl hneg_eq hocc_le_roff hroff_le_sc hneg_off_lt hgf_lt hrg_lt hpm_lt_roff
            hnm_lt_roff hm8_eqs hm7_eqs hnp_le hnn_le hdw2 htmk0 rfl (Nat.le_refl _)
            hent_p2 hent_n2' hm2 hQ)
        (fun J2000 hJ2000 => by
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · c0_hsteps!
                exact hQ 1#64 s2 m2 hdw2.toDense htmk0 (Nat.le_refl _) (Nat.le_refl _)
                  (Or.inl rfl) (by simp) hm2
              · c0_hsteps!; exact hJ2000 m2 rfl
            · c0_hsteps!; exact hJ2000 m2 rfl
          · c0_hsteps!; exact hJ2000 m2 rfl)

/-- Certifies canonical `FullFastBveBudgets.fullBveVarDefSpec` for
`FullFidelityStep12B.full_bve_var_m7_body` over Step-13 `step13SetInactiveSpec`. -/
public theorem full_bve_var_m7_step13_wp (Γ : Env)
    (hCollect : ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m7" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, Full.fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hWeakenUnit : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken_unit_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, step13SetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGatesFid : ∀ a m Q X, FullM8CoreParity.m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X)
    (hGatesM7 : ∀ a m Q X, FullM7BveGates.fullBveGatesM7Spec a m Q X →
      Γ "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Func.wp Γ FullFidelityStep12B.full_bve_var_m7_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hd0, htmk0, hv_lt, hm0, hQ⟩
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmx hsc harc hwc
  obtain ⟨F_cur, hdw0⟩ := hd0.exists_witness
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl1 := s6a_var_pl_nl_eq v (by omega)
  have hplnl : (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
      ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := hplnl1
  have hcv2_eq : (BitVec.ofNat 64 s0.core.cur_vars <<< (1 : Nat)).toNat = 2 * s0.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  unfold Func.wp FullFidelityStep12B.full_bve_var_m7_body
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s0 m0 hd0 htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl) (by simp) hm0
  · have hsc2048 : 2048 ≤ c.scratch_cap := by
      rw [Nat.mod_eq_of_lt (by omega), show (2048 : BitVec 64).toNat = 2048 from rfl] at hc; omega
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (16384 ≤ c.scratch_cap ∧ x = 2001#32) ∨ (c.scratch_cap < 16384 ∧ x = 512#32))
      ?_ (fun J1 hJ1 => by
        c0_hsplit
        · c0_hsteps!
          exact hJ1 2001#32 (Or.inl ⟨by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega, rfl⟩)
        · c0_hsteps!
          exact hJ1 512#32 (Or.inr ⟨by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega, rfl⟩))
    intro _ occ_lim hocc_cas
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => x = occ_lim) ?_ (fun J2 hJ2 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ2 2001#32 ho.symm
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ2 512#32 ho.symm)
    intro _ neg_off hneg_eq
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4002#32) ∨ (occ_lim = 512#32 ∧ x = 1024#32))
      ?_ (fun J3 hJ3 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ3 4002#32 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ3 1024#32 (Or.inr ⟨ho, rfl⟩))
    intro _ pos_mask hpm_cas
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4066#32) ∨ (occ_lim = 512#32 ∧ x = 1040#32))
      ?_ (fun J4 hJ4 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ4 4066#32 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ4 1040#32 (Or.inr ⟨ho, rfl⟩))
    intro _ neg_mask hnm_cas
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4130#32) ∨ (occ_lim = 512#32 ∧ x = 1056#32))
      ?_ (fun J5 hJ5 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ5 4130#32 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ5 1056#32 (Or.inr ⟨ho, rfl⟩))
    intro _ gf_idx hgf_cas
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4131#32) ∨ (occ_lim = 512#32 ∧ x = 1057#32))
      ?_ (fun J6 hJ6 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ6 4131#32 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ6 1057#32 (Or.inr ⟨ho, rfl⟩))
    intro _ rg_idx hrg_cas
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4192#64) ∨ (occ_lim = 512#32 ∧ x = 1088#64))
      ?_ (fun J7 hJ7 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ7 4192#64 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ7 1088#64 (Or.inr ⟨ho, rfl⟩))
    intro _ r_off hroff_cas
    obtain ⟨hocc_le_roff, hroff_le_sc, hgf_lt, hrg_lt, hpm_lt_roff, hnm_lt_roff,
      hm8_eqs, hm7_eqs⟩ :=
      s6a_var_layout_ok hsc2048 hocc_cas hneg_eq hpm_cas hnm_cas hgf_cas hrg_cas hroff_cas
    clear hocc_cas hpm_cas hnm_cas hgf_cas hrg_cas hroff_cas
    have huse_m8 :
        BitVec.ule 16384 (BitVec.ofNat 64 c.scratch_cap) = decide (16384 ≤ c.scratch_cap) := by
      simp only [BitVec.ule, show (16384 : BitVec 64).toNat = 16384 from rfl,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)]
    exact s6a_bve_var_collect_wp Γ hCollect hExtNeed hWeaken hWeakenUnit hSetInact hGatesFid
      hGatesM7 hResPair hAssign hDefrag hCommit hFlushUnits
      (c := c) (F0 := F0) (F_cur := F_cur) (s0 := s0) (R := R) (Q := Q) (X := X)
      (v := v) (occ_lim := occ_lim) (neg_off := neg_off) (pos_mask := pos_mask)
      (neg_mask := neg_mask) (gf_idx := gf_idx) (rg_idx := rg_idx) (r_off := r_off)
      (use_m8 := BitVec.ule 16384 (BitVec.ofNat 64 c.scratch_cap)) (m0 := m0) huse_m8
      hmx (by omega) hsc2048 hcv_le hv_lt hplnl hplnl1 hneg_eq hocc_le_roff hroff_le_sc
      hgf_lt hrg_lt hpm_lt_roff hnm_lt_roff hm8_eqs hm7_eqs hdw0 htmk0 hm0 hQ

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
