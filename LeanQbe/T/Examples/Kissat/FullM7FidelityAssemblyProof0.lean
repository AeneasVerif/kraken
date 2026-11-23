/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyPart1
public import LeanQbe.T.Examples.Kissat.FullM7Proof
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof
public import LeanQbe.T.Examples.Kissat.FullM7BvaV5FixProof
import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof2
import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
import LeanQbe.T.Examples.Kissat.FullFastAdapters
import LeanQbe.T.Examples.Kissat.FullFastTmkLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullBveVarLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` `M7Fidelity` Proof Foundation (`FullM7FidelityAssemblyProof0`)

100% additive UNSAT-only base `ModuleOk` and adapted `V5` BVE proofs (`public section`,
`0` `@[expose]`, `0` SAT model proofs, `0` upstream edits):
1. `m7FidSolveBytesSpec`: transparent UNSAT-only + `UnitUnsatTrace` specification (`0` SAT).
2. `m7Fid_forward_sub_wp`: `FullFastBveBudgets.fullForwardSubFastSpec` over
   `full_forward_sub_m7v5_body` directly wired to `FullM7BveGates.fullFwdCheckClM7Spec`.
3. Transparent `m7FidOrchPfxRows` (`21`), `m7FidBveRows` (`43`), `m7FidRowsPart3Pfx` (`129`),
   and complete `410/410` base `m7FidBase_moduleOk : ModuleOk m7FidBaseEnv m7Module`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Fidelity

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7

/-! ## 0. Transparent UNSAT-Only Core `kissat_solve_bytes` Specification -/

/-- Transparent UNSAT-only `kissat_solve_bytes` contract (`r ∈ {0, 10, 20}`,
`r = 20 → cnf.Unsat`, deterministic `UnitUnsatTrace → r = 20`, frame `R`; zero SAT proofs). -/
def m7FidSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

theorem m7FidSolveBytesSpec_intro {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m)
    (hQ : ∀ r m',
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (∀ mv nc i0,
        cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
        fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
        i0 ≤ cnfBytes.length →
        parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
        UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
        r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    m7FidSolveBytesSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m Q X :=
  ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩

theorem m7FidSolveBytesSpec_monoX
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7FidSolveBytesSpec xs m Q X) :
    m7FidSolveBytesSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem m7FidSolveBytesSpec_to_coreModel
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : m7FidSolveBytesSpec xs m Q X) :
    fullM6SolveBytesCoreModelSpec xs m Q X := by
  rcases xs with ⟨cp, cl, wp_, wl, fu, ⟨⟩⟩
  obtain ⟨cbs, wlen, R, rfl, rfl, hcf, hwf, hm, hQ⟩ := h
  exact fullM6SolveBytesCoreModelSpec_intro hcf hwf hm fun r m' hd hu _ htr hm' =>
    hQ r m' hd hu htr hm'

/-! ## 1. `m7Fid_forward_sub_wp` (`FullM7BveGates.fullFwdCheckClM7Spec`) -/

section ForwardSubSection

open FullFastBveBudgets FullFastSched FullM3CongBva FullM6BveFwd Full.FullArenaTactics
open FullM7BvaV5Fix
open scoped Full.FullArenaTactics FullM6ProofUtil.M6ProofUtilTactics

local macro "m7v5_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem v5_zero_mem_arenaRefs3 {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      simp only [show 0 + 3 ≤ n + 1 by omega, ↓reduceIte]
      exact List.mem_cons_self

/-- Parametric `Func.wp` proof for `full_forward_sub_m7v5`, certifying canonical
`FullFastBveBudgets.fullForwardSubFastSpec`. -/
theorem m7Fid_forward_sub_wp (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hCollectSort : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Γ "full_fwd_collect_sort_m7" [i64] [i64] a m Q X)
    (hFlushLarge : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hCheckCl : ∀ a m Q X, FullM7BveGates.fullFwdCheckClM7Spec a m Q X →
      Γ "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X)
    (hConnectSub : ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Γ "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hReconnect : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Γ "full_fwd_reconnect_irred_m7" [i64] [] a m Q X) :
    ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Func.wp Γ full_forward_sub_m7v5_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hd0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hrc := c.hred
  unfold dimacsBound at hmx harc hrc
  obtain ⟨F_cur, hw0⟩ := hd0.exists_witness
  unfold Func.wp full_forward_sub_m7v5_body
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s0 m0 hd0 rfl rfl (Or.inl rfl) (by simp) hm0
  · c0_hsteps_nogrp
    m7v5_call hDedup
    refine ⟨c, F0, F_cur, s0, R, rfl, hw0, hm0, ?_⟩
    intro ok1 s1 m1 hdw1 hcv1 hfl1 hf1 hm1
    c0_hsplit
    · c0_hsteps_nogrp
      m7v5_call hFlushUnits
      refine fullDenseFlushUnitsM6Spec_intro rfl hdw1 hm1 ?_
      intro ok2 s2 m2 hdw2 hcv2 _ hfl2 _ _ _ _ _ _ _ hf2 hm2
      c0_hsplit
      · c0_hsteps_nogrp
        m7v5_call hCollectSort
        refine fullFwdCollectSortM6Spec_intro rfl hdw2 hm2 ?_
        intro ncand s3 m3 hdw3 hcv3 hal3 hfl3 _ _ _ hnc_le hrr3 hm3
        c0_hsplit
        · c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ()))
            (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
            (fun _ r ⟨hr_disj, hr20⟩ => by
              c0_hsteps!
              exact hQ r s3 m3 hdw3.toDense (hcv3.trans (hcv2.trans hcv1))
                (hfl3.trans (hfl2.trans hfl1)) hr_disj hr20 hm3)
            (fun J7 hJ7 => by
              c0_hsplit
              · c0_hsteps!
                exact hJ7 20#64 ⟨Or.inr rfl, fun _ =>
                  hdw3.2.1.ext_sound.2 (hdw3.2.1.inconsistent_sound hc)⟩
              · c0_hsteps!; exact hJ7 1#64 ⟨Or.inl rfl, by simp⟩)
        · c0_hsteps_nogrp
          m7v5_call hFlushLarge
          refine fullFwdFlushLargeM6Spec_intro rfl hdw3 hm3 ?_
          intro s4 m4 hdw4 hcv4 har4 hal4 hfl4 _ _ _ hrr4 _ _ _ _ hm4
          have hrr4_ok : ∀ k < ncand.toNat,
              (s4.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s4 := by
            intro k hk; rw [hrr4]
            have hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s3 := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, hal4]
            rw [hrefs4]; exact hrr3 k hk
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64, i64])
            (fun r_lp (i, rem, ()) ml => ∃ sl : FullState,
              i.toNat ≤ ncand.toNat ∧ r_lp = ncand.toNat - i.toNat ∧
              FullDenseInvW c F0 F_cur sl ∧
              sl.core.cur_vars = s0.core.cur_vars ∧ sl.core.fuel = s0.core.fuel ∧
              fullArenaClauseRefs sl = fullArenaClauseRefs s4 ∧
              sl.scratch.red_refs = s4.scratch.red_refs ∧
              (FullMem c sl ⋆ R) ml)
            ?_ ?_
          · rintro L r_lp ⟨i, rem, ⟨⟩⟩ ml hL
              ⟨sl, hi_le, rfl, hdwl, hcvl, hfll, hrefsl, hrrl, hml⟩
            refine wp_join0 (P := fun mb => mb = ml)
              (fun _ mb hmb => by
                rcases hmb.symm with rfl
                refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                  (fun sf mf =>
                    FullDenseInvW c F0 F_cur sf ∧
                    sf.core.cur_vars = s0.core.cur_vars ∧ sf.core.fuel = s0.core.fuel ∧
                    (FullMem c sf ⋆ R) mf)
                  (fun _ sf mf ⟨hdwf, hcvf, hflf, hmf⟩ => by
                    c0_hsteps_nogrp
                    c0_hsplit
                    · c0_hsteps!
                      exact hQ 20#64 sf mf hdwf.toDense hcvf hflf (Or.inr rfl)
                        (fun _ => hdwf.2.1.ext_sound.2 (hdwf.2.1.inconsistent_sound hc)) hmf
                    · c0_hsteps_nogrp
                      m7v5_call hFlushUnits
                      refine fullDenseFlushUnitsM6Spec_intro rfl hdwf hmf ?_
                      intro ok_f s5 m5 hdw5 hcv5 _ hfl5 _ _ _ _ _ _ _ hf5 hm5
                      c0_hsplit
                      · c0_hsteps_nogrp
                        m7v5_call hReconnect
                        refine fullFwdReconnectIrredM6Spec_intro rfl hdw5 hm5 ?_
                        intro s6 m6 hdw6 hcv6 _ hfl6 _ _ hm6
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                            (fun r => (r, ()))
                            (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
                            (fun _ r ⟨hr_disj, hr20⟩ => by
                              c0_hsteps!
                              exact hQ r s6 m6 hdw6.toDense (hcv6.trans (hcv5.trans hcvf))
                                (hfl6.trans (hfl5.trans hflf)) hr_disj hr20 hm6)
                            (fun J20 hJ20 => by
                              c0_hsplit
                              · c0_hsteps!
                                exact hJ20 20#64 ⟨Or.inr rfl, fun _ =>
                                  hdw6.2.1.ext_sound.2 (hdw6.2.1.inconsistent_sound hc)⟩
                              · c0_hsteps!; exact hJ20 1#64 ⟨Or.inl rfl, by simp⟩)
                      · c0_hsteps!
                        exact hQ 20#64 s5 m5 hdw5.toDense (hcv5.trans hcvf) (hfl5.trans hflf)
                          (Or.inr rfl) (fun _ => hf5 (by simpa using hc)) hm5)
                  (fun Jc hJc => by
                    c0_hsplit
                    · c0_hsplit
                      · have hcvl_le := hdwl.1.core_ok.cur_vars_le
                        c0_hsteps_nogrp
                        -- Loop 1: clear `FL_SUBSUME` on `0 ..< cv`
                        refine wp_loop_group (ts := [i64])
                          (fun rem_v (v, ()) mv => ∃ fl_v : List (BitVec 32),
                            let sv : FullState :=
                              { sl with core := { sl.core with flags := fl_v } }
                            fl_v.length = c.max_vars ∧ v.toNat ≤ sl.core.cur_vars ∧
                            rem_v = sl.core.cur_vars - v.toNat ∧ (FullMem c sv ⋆ R) mv)
                          ?_ ?_
                        · rintro Lv rem_v ⟨v, ⟨⟩⟩ mv hLv ⟨fl_v, hflv, hv_le, rfl, hmv⟩
                          c0_hsplit
                          · have hv_lt : v.toNat < sl.core.cur_vars := by
                              rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                            have hv_fl : v.toNat < fl_v.length := by omega
                            have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
                            c0_hsteps!
                            exact hLv (sl.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) _
                              (by omega) ⟨_, by simp [hflv], by omega, rfl, hm⟩
                          · -- Loop 2 (`P1-3`): re-arm `FL_SUBSUME` on remaining `rr[i ..< ncand)`
                            let sv0 : FullState :=
                              { sl with core := { sl.core with flags := fl_v } }
                            have hdw_v0 : FullDenseInvW c F0 F_cur sv0 :=
                              m6_fullDenseInvW_with_flags hdwl hflv
                            c0_hsteps_nogrp
                            refine wp_loop_group (ts := [i64])
                              (fun rem_ri (ri, ()) mri => ∃ fl_r : List (BitVec 32),
                                let sr : FullState :=
                                  { sv0 with core := { sv0.core with flags := fl_r } }
                                fl_r.length = c.max_vars ∧ ri.toNat ≤ ncand.toNat ∧
                                rem_ri = ncand.toNat - ri.toNat ∧ (FullMem c sr ⋆ R) mri)
                              ?_ ?_
                            · rintro Lri rem_ri ⟨ri, ⟨⟩⟩ mri hLri
                                ⟨fl_r, hflr, hri_le, rfl, hmri⟩
                              c0_hsplit
                              · have hri_lt : ri.toNat < ncand.toNat := hc
                                have hri_rr : ri.toNat < sv0.scratch.red_refs.length := by
                                  rw [hdw_v0.1.scratch_ok.red_refs_len]; omega
                                have hrcr_ref : (sv0.scratch.red_refs[ri.toNat]'hri_rr).toNat ∈
                                    fullArenaClauseRefs sv0 := by
                                  change _ ∈ fullArenaClauseRefs sl
                                  rw [hrefsl]
                                  have h0 := hrr4_ok ri.toNat hri_lt
                                  rw [← hrrl, List.getElem?_eq_getElem hri_rr,
                                    Option.getD_some] at h0
                                  exact h0
                                let rcr := sv0.scratch.red_refs[ri.toNat]'hri_rr
                                have hrcr_wf := hdw_v0.2.1.arena.refs_wf rcr.toNat hrcr_ref
                                have hal_r := hdw_v0.1.core_ok.arena_len_le
                                have har_len := hdw_v0.1.core_ok.arena_len_arr
                                have hrcr_ar : (rcr.setWidth 64).toNat < sv0.core.arena.length := by
                                  rw [har_len, m6_zext32_toNat]; omega
                                have hri1 : (ri + 1#64).toNat = ri.toNat + 1 := by c0_bound
                                c0_hsteps_nogrp
                                refine wp_join0 (P := fun mj => ∃ fl' : List (BitVec 32),
                                    fl'.length = c.max_vars ∧
                                    (FullMem c { sv0 with core := { sv0.core with
                                      flags := fl' } } ⋆ R) mj)
                                  (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                    c0_hsteps!
                                    exact hLri (ncand.toNat - (ri + 1#64).toNat) (ri + 1#64, ()) mj
                                      (by omega) ⟨fl', hfl', by omega, rfl, hmj⟩)
                                  (fun Jri hJri => by
                                    c0_hsplit
                                    · have hrcr2_ar : (rcr.setWidth 64 + 2#64).toNat <
                                          sv0.core.arena.length := by
                                        rw [har_len]; c0_bound
                                      let rsz := sv0.core.arena[(rcr.setWidth 64 + 2#64).toNat]'
                                        hrcr2_ar
                                      have hrsz_eq : rsz.toNat =
                                          fullArenaClauseSizeCore sv0.core rcr.toNat := by
                                        unfold rsz fullArenaClauseSizeCore
                                        rw [List.getElem?_eq_getElem (by rw [har_len]; omega),
                                          Option.getD_some]
                                        exact congrArg BitVec.toNat (m6_getElem_congr
                                          (by rw [BitVec.toNat_add, m6_zext32_toNat,
                                            show (2#64 : BitVec 64).toNat = 2 from rfl,
                                            Nat.mod_eq_of_lt (by omega)]) _ _)
                                      c0_hsteps_nogrp
                                      refine wp_loop_group (ts := [i32])
                                        (fun rem_rk (rk, ()) mrk =>
                                          ∃ fl_rk : List (BitVec 32),
                                            let srk : FullState :=
                                              { sv0 with core := { sv0.core with flags := fl_rk } }
                                            fl_rk.length = c.max_vars ∧ rk.toNat ≤ rsz.toNat ∧
                                            rem_rk = rsz.toNat - rk.toNat ∧
                                            (FullMem c srk ⋆ R) mrk)
                                        ?_ ?_
                                      · rintro Lrk rem_rk ⟨rk, ⟨⟩⟩ mrk hLrk
                                          ⟨fl_rk, hflrk, hrk_le, rfl, hmrk⟩
                                        c0_hsplit
                                        · have hrk_lt : rk.toNat < rsz.toNat := hc
                                          have hpi_ar : (rcr.setWidth 64 + 3#64 +
                                                rk.setWidth 64).toNat <
                                              sv0.core.arena.length := by
                                            rw [har_len]; c0_bound
                                          have hrk1 : (rk + 1#32).toNat = rk.toNat + 1 := by
                                            c0_bound
                                          c0_hsteps_nogrp
                                          refine wp_join0 (P := fun mj =>
                                              ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                                              (FullMem c { sv0 with core := { sv0.core with
                                                flags := fl' } } ⋆ R) mj)
                                            (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                              c0_hsteps!
                                              exact hLrk (rsz.toNat - (rk + 1#32).toNat)
                                                (rk + 1#32, ()) mj (by omega)
                                                ⟨fl', hfl', by omega, rfl, hmj⟩)
                                            (fun Jrk hJrk => by
                                              c0_hsplit
                                              · have hlv_lt : ((sv0.core.arena[(rcr.setWidth 64 +
                                                    3#64 + rk.setWidth 64).toNat]'hpi_ar >>>
                                                    (1 : Nat)).setWidth 64).toNat <
                                                    fl_rk.length := by
                                                  have hpi_mod : (rcr.toNat + BitVec.toNat 3#64 +
                                                      rk.toNat) % 2 ^ 64 =
                                                      (rcr.setWidth 64 + 3#64 +
                                                        rk.setWidth 64).toNat := by
                                                    rw [BitVec.toNat_add, BitVec.toNat_add,
                                                      m6_zext32_toNat, m6_zext32_toNat,
                                                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                                                      Nat.mod_eq_of_lt (by omega),
                                                      Nat.mod_eq_of_lt (by omega),
                                                      Nat.mod_eq_of_lt (by omega)]
                                                  have har_eq : sv0.core.arena[(rcr.toNat +
                                                      BitVec.toNat 3#64 + rk.toNat) % 2 ^ 64]'(by
                                                        rw [hpi_mod]; exact hpi_ar) =
                                                      sv0.core.arena[(rcr.setWidth 64 + 3#64 +
                                                        rk.setWidth 64).toNat]'hpi_ar :=
                                                    m6_getElem_congr hpi_mod _ _
                                                  have hcv_mod :
                                                      sl.core.cur_vars % 2 ^ 64 =
                                                        sl.core.cur_vars :=
                                                    Nat.mod_eq_of_lt (by omega)
                                                  rw [hcv_mod] at hc
                                                  have hdiv_lt : (sv0.core.arena[(rcr.setWidth 64 +
                                                      3#64 + rk.setWidth 64).toNat]'
                                                      hpi_ar).toNat / 2 < sl.core.cur_vars := by
                                                    simpa [har_eq] using hc
                                                  have hsh1 :
                                                      ((sv0.core.arena[(rcr.setWidth 64 + 3#64 +
                                                            rk.setWidth 64).toNat]'hpi_ar
                                                          >>> (1 : Nat)) : BitVec 32).toNat =
                                                      (sv0.core.arena[(rcr.setWidth 64 + 3#64 +
                                                          rk.setWidth 64).toNat]'
                                                          hpi_ar).toNat / 2 := by
                                                    rw [BitVec.toNat_ushiftRight,
                                                      Nat.shiftRight_eq_div_pow]
                                                  rw [hflrk, m6_zext32_toNat, hsh1]; omega
                                                c0_hsteps!
                                                exact hJrk _ ⟨_, by simp [hflrk], hm⟩
                                              · c0_hsteps!; exact hJrk mrk ⟨fl_rk, hflrk, hmrk⟩)
                                        · c0_hsteps!; exact hJri mrk ⟨fl_rk, hflrk, hmrk⟩
                                      · intro Lrk hLrk; c0_hsteps!
                                        exact hLrk rsz.toNat (0#32, ()) mri
                                          ⟨fl_r, hflr, Nat.zero_le _, by simp, hmri⟩
                                    · c0_hsteps!; exact hJri mri ⟨fl_r, hflr, hmri⟩)
                              · -- Loop 3: arena scan for `PH_SUBSUME`
                                let sv1 : FullState :=
                                  { sv0 with core := { sv0.core with flags := fl_r } }
                                have hdw_v1 : FullDenseInvW c F0 F_cur sv1 :=
                                  m6_fullDenseInvW_with_flags hdw_v0 hflr
                                c0_hsteps_nogrp
                                refine wp_loop_group (ts := [i64])
                                  (fun rem_p (p, ()) mp => ∃ sp : FullState,
                                    p.toNat ≤ sp.core.arena_len ∧
                                    rem_p = sp.core.arena_len - p.toNat ∧
                                    (p.toNat = sp.core.arena_len ∨
                                      p.toNat ∈ fullArenaClauseRefs sp) ∧
                                    FullDenseInvW c F0 F_cur sp ∧
                                    sp.core.cur_vars = s0.core.cur_vars ∧
                                    sp.core.arena_len = sl.core.arena_len ∧
                                    sp.core.fuel = s0.core.fuel ∧
                                    (FullMem c sp ⋆ R) mp)
                                  ?_ ?_
                                · rintro Lp rem_p ⟨p, ⟨⟩⟩ mp hLp
                                    ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hmp⟩
                                  have hal_p := hdwp.1.core_ok.arena_len_le
                                  c0_hsplit
                                  · have hp_lt : p.toNat < sp.core.arena_len := by
                                      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                    have hp_ref : p.toNat ∈ fullArenaClauseRefs sp :=
                                      hp_mem.resolve_left (by omega)
                                    have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
                                    have hp_ar : p.toNat < sp.core.arena.length := by
                                      rw [hdwp.1.core_ok.arena_len_arr]; omega
                                    have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
                                      rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                                    have hp32 : (p.setWidth 32).toNat = p.toNat := by
                                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                                    let hdr_p := sp.core.arena[p.toNat]'hp_ar
                                    let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
                                    have hsz_p :
                                        sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
                                      unfold sz_p fullArenaClauseSizeCore
                                      rw [List.getElem?_eq_getElem (by
                                        rw [hdwp.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                                      exact congrArg BitVec.toNat
                                        (m6_getElem_congr (by c0_bound) _ _)
                                    c0_hsteps_nogrp
                                    m7v5_call hArenaNext
                                    dsimp only [vals, Arg.val]
                                    refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
                                    have hnb := fullArenaNextOff_bounds (ar := sp.core.arena)
                                      (alen := sp.core.arena_len) (cref := p.toNat) hwf_p.1
                                    have hnp_mem :=
                                      FullDenseWatchHelpers.fullArenaClauseRefs_next_mem
                                        hdwp.2.1.arena hp_ref
                                    let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena
                                      sp.core.arena_len (p.setWidth 32).toNat)).setWidth 64
                                    have hnp_toNat : np.toNat =
                                        fullArenaNextOff sp.core.arena
                                          sp.core.arena_len p.toNat := by
                                      dsimp only [np]
                                      rw [hp32, m6_zext32_toNat, BitVec.toNat_ofNat,
                                        Nat.mod_eq_of_lt (by omega)]
                                    c0_hsteps_nogrp
                                    refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                        FullDenseInvW c F0 F_cur sj ∧
                                        sj.core.cur_vars = s0.core.cur_vars ∧
                                        sj.core.arena_len = sl.core.arena_len ∧
                                        sj.core.fuel = s0.core.fuel ∧
                                        fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                        (FullMem c sj ⋆ R) mj)
                                      (fun _ mj ⟨sj, hdwj, hcvj, halj, hflj, hrefsj, hmj⟩ => by
                                        c0_hsteps!
                                        exact hLp (sj.core.arena_len - np.toNat) (np, ()) mj
                                          (by omega) ⟨sj, by omega, rfl, by
                                            rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
                                           hdwj, hcvj, halj, hflj, hmj⟩)
                                      (fun Jp hJp => by
                                        c0_hsplit
                                        · c0_hsteps_nogrp
                                          let v' := hdr_p &&& ~~~0x01000000#32
                                          let sc : FullState :=
                                            { sp with core := { sp.core with
                                              arena := sp.core.arena.set p.toNat v' } }
                                          have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                                            unfold hdr_p fullArenaHdr fullArenaHdrCore
                                            rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                                          have hcb := m6_bit24_clear_pres hdr_p
                                          have hset := m6_fullDenseInvW_set_hdr_bit24 hdwp hp_ref
                                            (v' := v') (by rw [← hhdr_eq]; exact hcb.1)
                                            (by rw [← hhdr_eq]; exact hcb.2)
                                          refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                              FullDenseInvW c F0 F_cur sj ∧
                                              sj.core.cur_vars = s0.core.cur_vars ∧
                                              sj.core.arena_len = sl.core.arena_len ∧
                                              sj.core.fuel = s0.core.fuel ∧
                                              fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                              (FullMem c sj ⋆ R) mj)
                                            (fun _ mj hmj => hJp mj hmj)
                                            (fun J52 hJ52 => by
                                              c0_hsplit
                                              · c0_hsteps_nogrp
                                                refine wp_loop_group (ts := [i32])
                                                  (fun rem_k (k, ()) mk =>
                                                    ∃ fl_k : List (BitVec 32),
                                                      let sk : FullState :=
                                                        { sc with core := { sc.core with
                                                          flags := fl_k } }
                                                      fl_k.length = c.max_vars ∧
                                                      k.toNat ≤ sz_p.toNat ∧
                                                      rem_k = sz_p.toNat - k.toNat ∧
                                                      (FullMem c sk ⋆ R) mk)
                                                  ?_ ?_
                                                · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk
                                                    ⟨fl_k, hflk, hk_le, rfl, hmk⟩
                                                  c0_hsplit
                                                  · have hk_lt : k.toNat < sz_p.toNat := hc
                                                    have hpi_ar : (p + 3#64 + k.setWidth 64).toNat <
                                                        sc.core.arena.length := by
                                                      rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                                                      c0_bound
                                                    c0_hsteps_nogrp
                                                    refine wp_join0 (P := fun mj => ∃ fl' : List
                                                        (BitVec 32),
                                                        fl'.length = c.max_vars ∧
                                                        (FullMem c { sc with core := { sc.core with
                                                          flags := fl' } } ⋆ R) mj)
                                                      (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                                        c0_hsteps!
                                                        exact hLk (sz_p.toNat - (k + 1#32).toNat)
                                                          (k + 1#32, ()) mj (by omega)
                                                          ⟨fl', hfl', by omega, rfl, hmj⟩)
                                                      (fun J65 hJ65 => by
                                                        c0_hsplit
                                                        · have hlv_lt : ((sc.core.arena[(p + 3#64 +
                                                              k.setWidth 64).toNat]'hpi_ar >>>
                                                              (1 : Nat)).setWidth 64).toNat <
                                                              fl_k.length := by
                                                            have hpi_mod : (p + 3#64 +
                                                                k.setWidth 64).toNat =
                                                                (p.toNat + BitVec.toNat 3#64 +
                                                                  k.toNat) % 2 ^ 64 := by
                                                              rw [BitVec.toNat_add,
                                                                BitVec.toNat_add,
                                                                m6_zext32_toNat]
                                                              simp only [BitVec.toNat_ofNat]
                                                              c0_bound
                                                            have har_eq : sc.core.arena[(p.toNat +
                                                                BitVec.toNat 3#64 +
                                                                k.toNat) % 2 ^ 64]'(by
                                                                  rw [hset.1.1.core_ok
                                                                    |>.arena_len_arr]
                                                                  c0_bound) =
                                                                sc.core.arena[(p + 3#64 +
                                                                  k.setWidth 64).toNat]'hpi_ar :=
                                                              m6_getElem_congr hpi_mod.symm _ _
                                                            have hcv_mod :
                                                                sl.core.cur_vars % 2 ^ 64 =
                                                                sl.core.cur_vars :=
                                                              Nat.mod_eq_of_lt (by
                                                                rw [hcvl]; have :=
                                                                  hset.1.1.core_ok.cur_vars_le
                                                                omega)
                                                            rw [hcv_mod] at hc
                                                            have hdiv_lt : (sc.core.arena[(p +
                                                                3#64 +
                                                                k.setWidth 64).toNat]'hpi_ar).toNat
                                                                / 2 < sl.core.cur_vars := by
                                                              simpa [har_eq] using hc
                                                            have hsh1 :
                                                                ((sc.core.arena[(p + 3#64 +
                                                                      k.setWidth 64).toNat]'hpi_ar
                                                                    >>> (1 : Nat)) :
                                                                  BitVec 32).toNat =
                                                                (sc.core.arena[(p + 3#64 +
                                                                    k.setWidth 64).toNat]'
                                                                    hpi_ar).toNat / 2 := by
                                                              rw [BitVec.toNat_ushiftRight,
                                                                Nat.shiftRight_eq_div_pow]
                                                            rw [hflk, m6_zext32_toNat, hsh1]
                                                            have := hset.1.1.core_ok.cur_vars_le
                                                            omega
                                                          c0_hsteps!
                                                          exact hJ65 _ ⟨_, by simp [hflk], hm⟩
                                                        · c0_hsteps!
                                                          exact hJ65 mk ⟨fl_k, hflk, hmk⟩)
                                                  · c0_hsteps!
                                                    exact hJ52 mk ⟨{ sc with core := { sc.core with
                                                      flags := fl_k } },
                                                      m6_fullDenseInvW_with_flags hset.1 hflk,
                                                      hcvp, halp, hflp, hset.2.1, hmk⟩
                                                · intro Lk hLk; c0_hsteps!
                                                  exact hLk sz_p.toNat (0#32, ()) m
                                                    ⟨sc.core.flags, hset.1.1.core_ok.flags_len,
                                                     Nat.zero_le _, by simp, hm⟩
                                              · refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                                    FullDenseInvW c F0 F_cur sj ∧
                                                    sj.core.cur_vars = s0.core.cur_vars ∧
                                                    sj.core.arena_len = sl.core.arena_len ∧
                                                    sj.core.fuel = s0.core.fuel ∧
                                                    fullArenaClauseRefs sj =
                                                      fullArenaClauseRefs sp ∧
                                                    (FullMem c sj ⋆ R) mj)
                                                  (fun _ mj hmj => hJ52 mj hmj)
                                                  (fun J55p hJ55p => by
                                                    c0_hsplit
                                                    · have hsz2 : 2 ≤ sz_p.toNat := hc
                                                      have hp3_ar : (p + 3#64).toNat <
                                                          sc.core.arena.length := by
                                                        rw [hset.1.1.core_ok.arena_len_arr]
                                                        c0_bound
                                                      have hp4_ar : (p + 4#64).toNat <
                                                          sc.core.arena.length := by
                                                        rw [hset.1.1.core_ok.arena_len_arr]
                                                        c0_bound
                                                      c0_hsteps_nogrp
                                                      refine wp_join_state (ts := [])
                                                        (α := List (BitVec 32)) (fun _ => ())
                                                        (fun fl1 m1 => fl1.length = c.max_vars ∧
                                                          (FullMem c { sc with
                                                            core := { sc.core with
                                                              flags := fl1 } } ⋆ R) m1)
                                                        (fun _ fl1 m1 ⟨hfl1, hm1⟩ => by
                                                          c0_hsteps_nogrp
                                                          refine wp_join_state (ts := [])
                                                            (α := List (BitVec 32)) (fun _ => ())
                                                            (fun fl2 m2 => fl2.length = c.max_vars ∧
                                                              (FullMem c { sc with core :=
                                                                { sc.core with flags := fl2 } } ⋆ R)
                                                                m2)
                                                            (fun _ fl2 m2 ⟨hfl2, hm2⟩ => by
                                                              c0_hsteps!
                                                              let s_fl2 : FullState :=
                                                                { sc with core := { sc.core with
                                                                  flags := fl2 } }
                                                              have hdw_fl2 :
                                                                  FullDenseInvW c F0 F_cur s_fl2 :=
                                                                m6_fullDenseInvW_with_flags hset.1
                                                                  hfl2
                                                              exact hJ55p m2 ⟨s_fl2, hdw_fl2,
                                                                hcvp, halp, hflp, hset.2.1, hm2⟩)
                                                            (fun J68 hJ68 => by
                                                              c0_hsplit
                                                              · have hv1_lt :
                                                                    ((sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar >>>
                                                                      (1 : Nat)).setWidth 64).toNat
                                                                      < fl1.length := by
                                                                  have hp4_mod : (p + 4#64).toNat =
                                                                      (p.toNat +
                                                                        BitVec.toNat 4#64) %
                                                                        2 ^ 64 := BitVec.toNat_add
                                                                          _ _
                                                                  have hsp_len :
                                                                      sp.core.arena.length =
                                                                        c.arena_cap := by
                                                                    have h0 :=
                                                                      hset.1.1.core_ok.arena_len_arr
                                                                    simpa [sc] using h0
                                                                  have hcv_mod : sl.core.cur_vars %
                                                                      2 ^ 64 = sl.core.cur_vars :=
                                                                    Nat.mod_eq_of_lt (by
                                                                      rw [hcvl]; have :=
                                                                        hset.1.1.core_ok.cur_vars_le
                                                                      omega)
                                                                  rw [hcv_mod] at hc
                                                                  have hne4 : p.toNat ≠
                                                                      (p.toNat +
                                                                        BitVec.toNat 4#64) %
                                                                        2 ^ 64 := by
                                                                    rw [← hp4_mod]; c0_bound
                                                                  have hset_ne1 :
                                                                      (sp.core.arena.set p.toNat
                                                                        (sp.core.arena[p.toNat]'(by
                                                                          rw [hsp_len]
                                                                          c0_bound) &&&
                                                                          ~~~(16777216 :
                                                                            BitVec 32)))[
                                                                          (p.toNat +
                                                                          BitVec.toNat 4#64) %
                                                                          2 ^ 64]'(by
                                                                            rw [List.length_set,
                                                                              hsp_len]
                                                                            c0_bound) =
                                                                        sp.core.arena[(p +
                                                                          4#64).toNat]'(by
                                                                            rw [hsp_len]
                                                                            c0_bound) :=
                                                                    (List.getElem_set_ne hne4
                                                                      _).trans (m6_getElem_congr
                                                                        hp4_mod.symm _ _)
                                                                  have hset_ne2 :
                                                                      sc.core.arena[(p +
                                                                        4#64).toNat]'hp4_ar =
                                                                        sp.core.arena[(p +
                                                                          4#64).toNat]'(by
                                                                            rw [hsp_len]
                                                                            c0_bound) :=
                                                                    by
                                                                    dsimp only [sc]
                                                                    exact List.getElem_set_ne
                                                                      (by c0_bound) _
                                                                  have hdiv_lt : (sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar).toNat / 2
                                                                      < sl.core.cur_vars := by
                                                                    have hc' :
                                                                        ((sp.core.arena.set p.toNat
                                                                          (sp.core.arena[p.toNat]'(
                                                                            by rw [hsp_len]
                                                                               c0_bound)
                                                                            &&& ~~~(16777216 :
                                                                              BitVec 32)))[(p.toNat
                                                                              + BitVec.toNat 4#64) %
                                                                            2 ^ 64]'(by
                                                                              rw [List.length_set,
                                                                                hsp_len]
                                                                              c0_bound)).toNat / 2 <
                                                                          sl.core.cur_vars := hc
                                                                    rw [hset_ne1] at hc'
                                                                    rw [hset_ne2]; exact hc'
                                                                  have hsh1 : ((sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar >>>
                                                                      (1 : Nat)) : BitVec 32).toNat
                                                                      = (sc.core.arena[(p +
                                                                        4#64).toNat]'hp4_ar).toNat /
                                                                        2 := by
                                                                    rw [BitVec.toNat_ushiftRight,
                                                                      Nat.shiftRight_eq_div_pow]
                                                                  rw [hfl1, m6_zext32_toNat, hsh1]
                                                                  have :=
                                                                    hset.1.1.core_ok.cur_vars_le
                                                                  omega
                                                                c0_hsteps!
                                                                exact hJ68 _ _ ⟨by simp [hfl1], hm⟩
                                                              · c0_hsteps!
                                                                exact hJ68 fl1 m1 ⟨hfl1, hm1⟩))
                                                        (fun J67 hJ67 => by
                                                          c0_hsplit
                                                          · have hv0_lt :
                                                                ((sc.core.arena[(p + 3#64).toNat]'
                                                                  hp3_ar >>> (1 : Nat)).setWidth
                                                                  64).toNat <
                                                                  sc.core.flags.length :=
                                                              by
                                                                have hp3_mod : (p + 3#64).toNat =
                                                                    (p.toNat + BitVec.toNat 3#64) %
                                                                      2 ^ 64 := BitVec.toNat_add _ _
                                                                have hsp_len :
                                                                    sp.core.arena.length =
                                                                      c.arena_cap := by
                                                                  have h0 :=
                                                                    hset.1.1.core_ok.arena_len_arr
                                                                  simpa [sc] using h0
                                                                have hcv_mod : sl.core.cur_vars %
                                                                    2 ^ 64 = sl.core.cur_vars :=
                                                                  Nat.mod_eq_of_lt (by
                                                                    rw [hcvl]; have :=
                                                                      hset.1.1.core_ok.cur_vars_le
                                                                    omega)
                                                                rw [hcv_mod] at hc
                                                                have hne3 : p.toNat ≠
                                                                    (p.toNat + BitVec.toNat 3#64) %
                                                                      2 ^ 64 := by
                                                                  rw [← hp3_mod]; c0_bound
                                                                have hset_ne1 :
                                                                    (sp.core.arena.set p.toNat
                                                                      (sp.core.arena[p.toNat]'(by
                                                                        rw [hsp_len]; c0_bound) &&&
                                                                        ~~~(16777216 : BitVec 32)))[
                                                                        (p.toNat +
                                                                        BitVec.toNat 3#64) %
                                                                        2 ^ 64]'(by
                                                                          rw [List.length_set,
                                                                            hsp_len]
                                                                          c0_bound) =
                                                                      sp.core.arena[(p +
                                                                        3#64).toNat]'(by
                                                                          rw [hsp_len]; c0_bound) :=
                                                                  (List.getElem_set_ne hne3 _).trans
                                                                    (m6_getElem_congr hp3_mod.symm _
                                                                      _)
                                                                have hset_ne2 :
                                                                    sc.core.arena[(p +
                                                                      3#64).toNat]'hp3_ar =
                                                                      sp.core.arena[(p +
                                                                        3#64).toNat]'(by
                                                                          rw [hsp_len]; c0_bound) :=
                                                                  by
                                                                  dsimp only [sc]
                                                                  exact List.getElem_set_ne
                                                                    (by c0_bound) _
                                                                have hdiv_lt : (sc.core.arena[(p +
                                                                    3#64).toNat]'hp3_ar).toNat / 2 <
                                                                    sl.core.cur_vars := by
                                                                  have hc' :
                                                                      ((sp.core.arena.set p.toNat
                                                                        (sp.core.arena[p.toNat]'(by
                                                                          rw [hsp_len]
                                                                          c0_bound) &&&
                                                                          ~~~(16777216 :
                                                                            BitVec 32)))[
                                                                          (p.toNat +
                                                                          BitVec.toNat 3#64) %
                                                                          2 ^ 64]'(by
                                                                            rw [List.length_set,
                                                                              hsp_len]
                                                                            c0_bound)).toNat / 2 <
                                                                        sl.core.cur_vars := hc
                                                                  rw [hset_ne1] at hc'
                                                                  rw [hset_ne2]; exact hc'
                                                                have hsh1 : ((sc.core.arena[(p +
                                                                    3#64).toNat]'hp3_ar >>>
                                                                    (1 : Nat)) : BitVec 32).toNat =
                                                                    (sc.core.arena[(p +
                                                                      3#64).toNat]'hp3_ar).toNat /
                                                                      2 := by
                                                                  rw [BitVec.toNat_ushiftRight,
                                                                    Nat.shiftRight_eq_div_pow]
                                                                rw [hset.1.1.core_ok.flags_len,
                                                                  m6_zext32_toNat, hsh1]
                                                                have := hset.1.1.core_ok.cur_vars_le
                                                                omega
                                                            c0_hsteps!
                                                            exact hJ67 _ _
                                                              ⟨by simp [hset.1.1.core_ok.flags_len],
                                                               hm⟩
                                                          · c0_hsteps!
                                                            exact hJ67 sc.core.flags m
                                                              ⟨hset.1.1.core_ok.flags_len, hm⟩)
                                                    · c0_hsteps!
                                                      exact hJ55p m ⟨sc, hset.1, hcvp, halp, hflp,
                                                        hset.2.1, hm⟩))
                                        · c0_hsteps!
                                          exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, rfl, hmp⟩)
                                  · c0_hsteps!; exact hJc sp mp ⟨hdwp, hcvp, hflp, hmp⟩
                                · intro Lp hLp; c0_hsteps!
                                  exact hLp sv1.core.arena_len (0#64, ()) mri
                                    ⟨sv1, Nat.zero_le _, by simp, by
                                      by_cases hz : sv1.core.arena_len = 0
                                      · exact Or.inl hz.symm
                                      · exact Or.inr (v5_zero_mem_arenaRefs3 hdw_v1.2.1.arena
                                          (Nat.pos_of_ne_zero hz)),
                                     hdw_v1, hcvl, rfl, hfll, hmri⟩
                            · intro Lri hLri; c0_hsteps!
                              exact hLri (ncand.toNat - i.toNat) (i, ()) mv
                                ⟨fl_v, hflv, hi_le, rfl, hmv⟩
                        · intro Lv hLv; c0_hsteps!
                          exact hLv sl.core.cur_vars (0#64, ()) ml
                            ⟨sl.core.flags, hdwl.1.core_ok.flags_len, Nat.zero_le _, by simp, hml⟩
                      · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩
                    · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩))
              (fun B hB => by
                c0_hsplit
                · have hi_lt : i.toNat < ncand.toNat := hc
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsplit
                      · have hi_rr : i.toNat < sl.scratch.red_refs.length := by
                          rw [hdwl.1.scratch_ok.red_refs_len]; omega
                        have hcr_ref : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                            fullArenaClauseRefs sl := by
                          rw [hrefsl]
                          have h0 := hrr4_ok i.toNat hi_lt
                          rw [← hrrl, List.getElem?_eq_getElem hi_rr, Option.getD_some] at h0
                          exact h0
                        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        m7v5_call hCheckCl
                        refine FullM7BveGates.fullFwdCheckClM7Spec_intro rfl hdwl hcr_ref hml ?_
                        intro ok_c sc mc hdwc hcvc _ hflc hrefsc _ hrrc hfc hmc
                        c0_hsplit
                        · have hcr_ref_c : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                              fullArenaClauseRefs sc := hrefsc.symm ▸ hcr_ref
                          refine wp_join0 (P := fun mj => ∃ sj : FullState,
                              FullDenseInvW c F0 F_cur sj ∧
                              sj.core.cur_vars = s0.core.cur_vars ∧ sj.core.fuel = s0.core.fuel ∧
                              fullArenaClauseRefs sj = fullArenaClauseRefs s4 ∧
                              sj.scratch.red_refs = s4.scratch.red_refs ∧
                              (FullMem c sj ⋆ R) mj)
                            (fun _ mj ⟨sj, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩ => by
                              c0_hsteps!
                              exact hL (ncand.toNat - (i + 1#64).toNat)
                                (i + 1#64, rem - 1#64, ()) mj (by omega)
                                ⟨sj, by omega, rfl, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩)
                            (fun Jcon hJcon => by
                              c0_hsplit
                              · c0_hsplit
                                · have hcr_ar :
                                      ((sl.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
                                        sc.core.arena.length := by
                                    have hwf_c := hdwc.2.1.arena.refs_wf _ hcr_ref_c
                                    have := hdwc.1.core_ok.arena_len_le
                                    rw [hdwc.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
                                  c0_hsplit
                                  · c0_hsteps_nogrp
                                    m7v5_call hConnectSub
                                    refine fullFwdConnectSubsumerM6Spec_intro rfl hdwc hcr_ref_c
                                      hmc ?_
                                    intro s_con m_con hdw_con hcv_con har_con hal_con hfl_con _ _
                                      hrr_con hm_con
                                    have hrefs_con : fullArenaClauseRefs s_con =
                                        fullArenaClauseRefs sc := by
                                      unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                      rw [har_con, hal_con]
                                    c0_hsteps!
                                    exact hJcon m_con ⟨s_con, hdw_con,
                                      hcv_con.trans (hcvc.trans hcvl),
                                      hfl_con.trans (hflc.trans hfll),
                                      hrefs_con.trans (hrefsc.trans hrefsl),
                                      hrr_con.trans (hrrc.trans hrrl), hm_con⟩
                                  · c0_hsteps!
                                    exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                      hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                                · c0_hsteps!
                                  exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                    hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                              · c0_hsteps!
                                exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                  hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩)
                        · c0_hsteps!
                          exact hQ 20#64 sc mc hdwc.toDense (hcvc.trans hcvl) (hflc.trans hfll)
                            (Or.inr rfl) (fun _ => hfc (by simpa using hc)) hmc
                      · c0_hsteps!; exact hB ml rfl
                    · c0_hsteps!; exact hB ml rfl
                  · c0_hsteps!; exact hB ml rfl
                · c0_hsteps!; exact hB ml rfl)
          · intro L hL; c0_hsteps!
            exact hL ncand.toNat (0#64, budget, ()) m4
              ⟨s4, Nat.zero_le _, by simp, hdw4,
               hcv4.trans (hcv3.trans (hcv2.trans hcv1)),
               hfl4.trans (hfl3.trans (hfl2.trans hfl1)), rfl, rfl, hm4⟩
      · c0_hsteps!
        exact hQ 20#64 s2 m2 hdw2.toDense (hcv2.trans hcv1) (hfl2.trans hfl1) (Or.inr rfl)
          (fun _ => hf2 (by simpa using hc)) hm2
    · c0_hsteps!
      exact hQ 20#64 s1 m1 hdw1.toDense hcv1 hfl1 (Or.inr rfl)
        (fun _ => hf1 (by simpa using hc)) hm1

end ForwardSubSection

/-! ## 2. Transparent `M7` Spec Tables & `410/410` Base `ModuleOk` -/

section BaseTableSection

open FullM7Proof
open scoped Full.FullArenaTactics

/-- Transparent `21`-row orchestrator prefix matching `FullM7Proof.m7OrchPfxFns`. -/
def m7FidOrchPfxRows : List SpecEntry :=
  [ ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩
  , ⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  , ⟨"full_lit_rank", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], Full.fullSweepBinsSpec, true⟩
  , ⟨"full_rewatch_arena", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩
  , ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], m7AnalyzeRsnHdrSpec, true⟩
  , ⟨"full_min_shrink", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩
  , ⟨"full_deduce_1uip", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], m7Deduce1uipHdrSpec, true⟩
  , ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_reorder_m6", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_simplify_m6", [i64, .bool, .bool], [i64], fullM6SimplifySpec, true⟩ ]

theorem m7FidOrchPfxRows_sigs :
    m7FidOrchPfxRows.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig := by
  rw [m7OrchPfxFns_eq]; t_kernel_rfl

theorem m7FidOrchPfxRows_noExit : m7FidOrchPfxRows.all SpecEntry.noExit = true := by rfl

theorem m7FidOrchPfxRows_specs : M7OrchPfxTblSpecs m7FidOrchPfxRows :=
  ⟨ List.mem_of_getElem? (i := 0) rfl, List.mem_of_getElem? (i := 1) rfl
  , List.mem_of_getElem? (i := 2) rfl, List.mem_of_getElem? (i := 3) rfl
  , List.mem_of_getElem? (i := 4) rfl, List.mem_of_getElem? (i := 5) rfl
  , List.mem_of_getElem? (i := 6) rfl, List.mem_of_getElem? (i := 7) rfl
  , List.mem_of_getElem? (i := 8) rfl, List.mem_of_getElem? (i := 9) rfl
  , List.mem_of_getElem? (i := 11) rfl, List.mem_of_getElem? (i := 12) rfl
  , List.mem_of_getElem? (i := 14) rfl, List.mem_of_getElem? (i := 16) rfl
  , List.mem_of_getElem? (i := 19) rfl, List.mem_of_getElem? (i := 20) rfl ⟩

/-- Transparent `43`-function `FullM7BveGates` + canonical alias slice inside `m7FnsPart3`. -/
def m7FidBveFns : List Fn :=
  FullM7BveGates.m7BveGates_fns.take 10 ++
  ([ m7ForwardSubCanonFn, m7BveCollectCanonFn ] ++
  ((FullM7BveGates.m7BveGates_fns.drop 10).take 20 ++
  ((FullM7BveGates.m7BveGates_fns.drop 30).take 1 ++
  ([ m7BveVarCanonFn ] ++
  (FullM7BveGates.m7BveGates_fns.drop 31 ++ [ m7EliminateM6Fn ])))))

theorem m7FidBveFns_length : m7FidBveFns.length = 43 := by t_kernel_rfl

section BveDefsSection

open FullFastBveBudgets FullFastSched FullM3CongBva FullM6BveFwd FullM7BveGates

def m7FidBveRows : List SpecEntry :=
  [ ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], fullDensePropUnitM6Spec, true⟩
  , ⟨"full_dense_flush_units_m7", [i64], [.bool], fullDenseFlushUnitsM6Spec, true⟩
  , ⟨"full_fwd_flush_large_m7", [i64], [], fullFwdFlushLargeM6Spec, true⟩
  , ⟨"full_fwd_reconnect_irred_m7", [i64], [], fullFwdReconnectIrredM6Spec, true⟩
  , ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32], fullFwdScanLitM7Spec, true⟩
  , ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], fullFwdCheckClM7Spec, true⟩
  , ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], fullFwdConnectSubsumerM6Spec, true⟩
  , ⟨"full_fwd_collect_sort_m7", [i64], [i64], fullFwdCollectSortM6Spec, true⟩
  , ⟨"full_forward_sub_m7", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect_m7", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_mark_and_m7", [i64, i32, i32, i32, i32, i32], [.bool],
      fullBveMarkAndM6Spec, true⟩
  , ⟨"full_bve_find_equiv_m7", [i64, i32, i32], [.bool], fullBveFindEquivM7Spec, true⟩
  , ⟨"full_bve_find_and_m7", [i64, i32, i32, i32], [.bool], fullBveFindAndM7Spec, true⟩
  , ⟨"full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool], fullBveGetTernM7Spec, true⟩
  , ⟨"full_bve_match_tern_m7", [i64, i32, i32, i32, i32, i32], [i32],
      fullBveMatchTernM7Spec, true⟩
  , ⟨"full_bve_find_ite_side_m7", [i64, i32, i32, i32, .bool], [.bool],
      fullBveFindIteSideM7Spec, true⟩
  , ⟨"full_bve_find_ite_m7", [i64, i32, i32, i32], [.bool], fullBveFindIteM7Spec, true⟩
  , ⟨"full_bve_xor_pat_m7", [i64, i32, i32, i32], [i32], fullBveXorPatM7Spec, true⟩
  , ⟨"full_bve_find_xor_m7", [i64, i32, i32, i32], [.bool], fullBveFindXorM7Spec, true⟩
  , ⟨"full_k6_watch_m7", [i64, i32, i32, i32, i32], [], fullK6WatchM7Spec, true⟩
  , ⟨"full_k6_assign_m7", [i64, i32, i32], [], fullK6AssignM7Spec, true⟩
  , ⟨"full_k6_mtf_m7", [i64, i32], [], fullK6MtfM7Spec, true⟩
  , ⟨"full_k6_backtrack_m7", [i64, i32], [], fullK6BacktrackM7Spec, true⟩
  , ⟨"full_k6_prop_m7", [i64], [i32], fullK6PropM7Spec, true⟩
  , ⟨"full_k6_ana_cl_m7", [i64, i32, i32], [], fullK6AnaClM7Spec, true⟩
  , ⟨"full_k6_analyze_m7", [i64, i32], [.bool], fullK6AnalyzeM7Spec, true⟩
  , ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], fullK6SolveM7Spec, true⟩
  , ⟨"full_k6_core_m7", [i64], [], fullK6CoreM7Spec, true⟩
  , ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩
  , ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩
  , ⟨"full_bve_var_m7", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var_key_m7", [i64, i32], [i64], fullBveVarKeyM6Spec, true⟩
  , ⟨"full_bve_heap_up_m7", [i64, i64, i32], [], fullBveHeapUpM6Spec, true⟩
  , ⟨"full_bve_heap_down_m7", [i64, i64, i32], [], fullBveHeapDownM6Spec, true⟩
  , ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], fullBveHeapPushM6Spec, true⟩
  , ⟨"full_bve_heap_pop_m7", [i64, i64], [i32], fullBveHeapPopM6Spec, true⟩
  , ⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩
  , ⟨"full_eliminate_m7", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩
  ]

def m7FidBveExternRows : List SpecEntry :=
  [ ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClTmkSpec, true⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  ]

def m7FidBveClosedRows : List SpecEntry := m7FidBveRows ++ m7FidBveExternRows

theorem m7FidBveRows_sigs :
    m7FidBveRows.map (fun e => (e.name, e.as, e.rs)) = m7FidBveFns.map Fn.sig := by
  unfold m7FidBveRows m7FidBveFns
  t_kernel_rfl

theorem m7FidBveRows_noExit : m7FidBveRows.all SpecEntry.noExit = true := by t_kernel_rfl

theorem m7FidBveRows_specs : FullM7Proof.M7BveAllTblSpecs m7FidBveRows :=
  ⟨List.mem_of_getElem? (i := 11) rfl, List.mem_of_getElem? (i := 10) rfl,
   List.mem_of_getElem? (i := 42) rfl⟩

end BveDefsSection

private def p3Sweep22Rows : List SpecEntry := FullM4Sweep.fullM4SweepSpecTable.take 22
private def p3SweepDenseM5Rows : List SpecEntry :=
  [⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩]
def p3FwdDedupBinsRows : List SpecEntry := (fullBaseTable.drop 145).take 1
private def p3BveCollectRows : List SpecEntry := (fullBaseTable.drop 148).take 1
private def p3BveResPairRows : List SpecEntry := (fullBaseTable.drop 151).take 1
private def p3BveWeakenRows : List SpecEntry :=
  [⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
    FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩]
private def p3BveTryBceRows : List SpecEntry := (fullBaseTable.drop 153).take 1
private def p3BveCommitResRows : List SpecEntry :=
  [⟨"full_bve_commit_res", [i64, i64, i64], [i64],
    FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩]
private def p3BveExtNeedRows : List SpecEntry := (fullBaseTable.drop 155).take 1
def p3Bve5Rows : List SpecEntry :=
  p3BveResPairRows ++ p3BveWeakenRows ++ p3BveTryBceRows ++ p3BveCommitResRows ++ p3BveExtNeedRows
def p3InitFreshVarRows : List SpecEntry :=
  [⟨"full_init_fresh_var", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩]
private def p3BvaHopRows : List SpecEntry := FullM4Bva.m4BvaSpecTable.take 3
private def p3BvaMatchLargeRows : List SpecEntry :=
  [⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], FullBvaHeap.fullBvaMatchLargeSpec, true⟩]
private def p3BvaScanCandsRows : List SpecEntry :=
  [⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], FullM4Bva.m4BvaScanCandsSpec, true⟩]
def p3BvaPickCandRows : List SpecEntry :=
  [⟨"full_bva_pick_cand", [i64, i32, i32], [i32], FullBvaHeap.fullBvaPickCandSpec, true⟩]
private def p3BvaFilterRowRows : List SpecEntry := (FullM4Bva.m4BvaSpecTable.drop 4).take 1
def p3BvaCommitRows : List SpecEntry :=
  [⟨"full_bva_commit", [i64, i32], [.bool], FullM4Bva.m4BvaCommitSpec, true⟩]
private def p3BvaTryLitM7Rows : List SpecEntry :=
  [⟨"full_bva_try_lit", [i64, i32, i64], [.bool], FullBvaHeap.fullBvaTryLitHeapSpec, true⟩]
private def p3FheapPairRows : List SpecEntry :=
  [ ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.fullFheapDownSpec, true⟩ ]
def p3FactorM7Rows : List SpecEntry :=
  [⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩]
def p3CfCompact3Rows : List SpecEntry :=
  [ ⟨"full_compact_needed", [i64], [.bool], FullM6CompactFlush.fullCompactNeededM6Spec, true⟩
  , ⟨"full_compact_flush", [i64], [i64], FullM4Compact.fullCompactFlushSpec, true⟩
  , ⟨"full_compact_mark_live", [i64], [], FullM4Compact.fullCompactMarkLiveSpec, true⟩ ]
def p3Compact10Rows : List SpecEntry := (FullM4Compact.compactSpecTable.drop 3).take 10
private def p3ReorderRows : List SpecEntry :=
  [ ⟨"full_reorder_weight_m7", [i64], [i64], FullM7Reorder.m7ReorderWeightSpec, true⟩
  , ⟨"full_reorder_sift_m7", [i64, i64, i64], [], FullM7Reorder.m7ReorderSiftSpec, true⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩ ]
private def p3VivBce4Rows : List SpecEntry :=
  [ ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4VivBce.fullBceSideM4Spec, true⟩
  , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.fullBcePairM4Spec, true⟩
  , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.fullBceVarM4Spec, true⟩
  , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩ ]
def p3SchedMinMaxRows : List SpecEntry :=
  [ ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩ ]
def p3ElimDticksRows : List SpecEntry :=
  [⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩]
private def p3M7Search14Rows : List SpecEntry :=
  [ ⟨"full_lcg_next_m7", [i64], [i64], FullM7Search.m7LcgNextSpec, true⟩
  , ⟨"full_m7_get64", [i64, i64], [i64], FullM7Search.m7Get64Spec, true⟩
  , ⟨"full_m7_set64", [i64, i64, i64], [], FullM7Search.m7Set64Spec, true⟩
  , ⟨"full_m7_state_init", [i64], [], FullM7Search.m7StateInitSpec, true⟩
  , ⟨"full_tumble_clause_m7", [i64, i32], [.bool], FullM7Search.m7TumbleClauseSpec, true⟩
  , ⟨"full_tumble_clauses_m7", [i64, i64], [i64], FullM7Search.m7TumbleClausesSpec, true⟩
  , ⟨"full_tumble_m7", [i64], [i64], FullM7Search.m7TumbleSpec, true⟩
  , ⟨"full_lucky_polar_m7", [i64], [i64], Full.fullLuckyPolarSpec, true⟩
  , ⟨"full_lucky_late_m7", [i64], [i64], FullM7Search.m7LuckyLateSpec, true⟩
  , ⟨"full_randec_step_m7", [i64], [], FullM7Search.m7RandecStepSpec, true⟩
  , ⟨"full_randec_var_m7", [i64], [i64], FullM7Search.m7RandecVarSpec, true⟩
  , ⟨"full_decide_m7", [i64], [i64], FullM7Search.m7DecideSpec, true⟩
  , ⟨"full_ema_swap_m7", [i64, i64, i64], [], FullM7Search.m7EmaSwapSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], FullM7Search.m7SwitchModeSpec, true⟩ ]
private def p3AdpProbeDticksRows : List SpecEntry :=
  [⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩]

/-- Part 3 prefix rows (`276..404`, `129` entries) aligned 1-to-1 with
`m7FnsPart3.take 129`. -/
def m7FidRowsPart3Pfx (tPfx tBve : List SpecEntry) : List SpecEntry :=
  p3Sweep22Rows ++ (p3SweepDenseM5Rows ++ ((tPfx.drop 15).take 1 ++ (p3FwdDedupBinsRows ++
  (tBve.take 32 ++ (p3Bve5Rows ++ ((tBve.drop 32).take 2 ++ (p3InitFreshVarRows ++
  (p3BvaHopRows ++ (p3BvaMatchLargeRows ++ (p3BvaScanCandsRows ++ (p3BvaPickCandRows ++
  (p3BvaFilterRowRows ++ (p3BvaCommitRows ++ (p3BvaTryLitM7Rows ++ (p3FheapPairRows ++
  (p3FactorM7Rows ++ (p3CfCompact3Rows ++ (p3Compact10Rows ++ (p3ReorderRows ++
  ((tPfx.drop 16).take 1 ++ (p3VivBce4Rows ++ (p3SchedMinMaxRows ++ (p3ElimDticksRows ++
  (tBve.drop 34 ++ (p3M7Search14Rows ++ (p3AdpProbeDticksRows ++
    (tPfx.drop 17).take 4))))))))))))))))))))))))))

/-! ## 3. Part 3 Prefix Function Decomposition & Metadata -/

private def p3Sweep22Fns : List Fn := FullM4Sweep.fullM4Sweep_fns.take 22
private def p3SweepDenseM5Fns : List Fn := (FullM5.m5Fns.drop 200).take 1
private def p3FwdDedupBinsFns : List Fn := (FullM5.m5Fns.drop 201).take 1
private def p3Bve5Fns : List Fn := (FullM5.m5Fns.drop 213).take 5
private def p3InitFreshVarFns : List Fn := [FullM7BvaFactor.m7InitFreshVarFn]
private def p3BvaHopFns : List Fn := (FullM5.m5Fns.drop 220).take 3
private def p3BvaMatchLargeFns : List Fn := (FullM5.m5Fns.drop 223).take 1
private def p3BvaScanCandsFns : List Fn := (FullM5.m5Fns.drop 224).take 1
private def p3BvaPickCandFns : List Fn := FullM6BvaNoHops.m6BvaNoHopsFns
private def p3BvaFilterRowFns : List Fn := (FullM5.m5Fns.drop 226).take 1
private def p3BvaCommitFns : List Fn := (FullM5.m5Fns.drop 227).take 1
private def p3BvaTryLitM7Fns : List Fn := [FullM7BvaFactor.m7BvaTryLitFn]
private def p3FheapPairFns : List Fn := (FullM5.m5Fns.drop 229).take 2
private def p3FactorM7Fns : List Fn := [FullM7BvaFactor.m7FactorFn]
private def p3CfCompact3Fns : List Fn :=
  [ FullM6CompactFlush.m6cfCompactNeededFn
  , FullM6CompactFlush.m6cfCompactFlushFn
  , FullM6CompactFlush.m6cfCompactMarkLiveFn ]
private def p3Compact10Fns : List Fn := (FullM5.m5Fns.drop 235).take 10
private def p3ReorderFns : List Fn := FullM7Reorder.m7ReorderFns
private def p3VivBce4Fns : List Fn := (FullM5.m5Fns.drop 248).take 4
private def p3SchedMinMaxFns : List Fn := (FullM5.m5Fns.drop 252).take 2
private def p3ElimDticksFns : List Fn := [m6CanonicalElimDticksFn]
private def p3M7Search14Fns : List Fn :=
  FullM7Search.m7Search_fns.take 4 ++ FullM7Search.m7Search_fns.drop 5
private def p3AdpProbeDticksFns : List Fn := [m6aProbeDticksM6HdrFn]

private def mf3PfxSeg : List Fn :=
  p3Sweep22Fns ++ (p3SweepDenseM5Fns ++ ((m7OrchPfxFns.drop 15).take 1 ++ (p3FwdDedupBinsFns ++
  (m7FidBveFns.take 32 ++ (p3Bve5Fns ++ ((m7FidBveFns.drop 32).take 2 ++ (p3InitFreshVarFns ++
  (p3BvaHopFns ++ (p3BvaMatchLargeFns ++ (p3BvaScanCandsFns ++ (p3BvaPickCandFns ++
  (p3BvaFilterRowFns ++ (p3BvaCommitFns ++ (p3BvaTryLitM7Fns ++ (p3FheapPairFns ++
  (p3FactorM7Fns ++ (p3CfCompact3Fns ++ (p3Compact10Fns ++ (p3ReorderFns ++
  ((m7OrchPfxFns.drop 16).take 1 ++ (p3VivBce4Fns ++ (p3SchedMinMaxFns ++ (p3ElimDticksFns ++
  (m7FidBveFns.drop 34 ++ (p3M7Search14Fns ++ (p3AdpProbeDticksFns ++
    (m7OrchPfxFns.drop 17).take 4))))))))))))))))))))))))))

private theorem mf3Pfx_eq : m7FnsPart3.take 129 = mf3PfxSeg := by
  unfold m7FnsPart3 mf3PfxSeg m7FidBveFns
  rw [m7OrchPfxFns_eq]
  t_kernel_rfl

private theorem bveAllSlice_sigs {tBve : List SpecEntry}
    (hsig : tBve.map (fun e => (e.name, e.as, e.rs)) = m7FidBveFns.map Fn.sig)
    (off n : Nat) :
    ((tBve.drop off).take n).map (fun e => (e.name, e.as, e.rs)) =
      ((m7FidBveFns.drop off).take n).map Fn.sig := by
  simp only [List.map_take, List.map_drop, hsig]

private theorem bveAllDrop_sigs {tBve : List SpecEntry}
    (hsig : tBve.map (fun e => (e.name, e.as, e.rs)) = m7FidBveFns.map Fn.sig)
    (off : Nat) :
    (tBve.drop off).map (fun e => (e.name, e.as, e.rs)) =
      (m7FidBveFns.drop off).map Fn.sig := by
  simp only [List.map_drop, hsig]

private theorem bveAllTake_sigs {tBve : List SpecEntry}
    (hsig : tBve.map (fun e => (e.name, e.as, e.rs)) = m7FidBveFns.map Fn.sig)
    (n : Nat) :
    (tBve.take n).map (fun e => (e.name, e.as, e.rs)) =
      (m7FidBveFns.take n).map Fn.sig := by
  simp only [List.map_take, hsig]

private theorem bveAllSlice_noExit {tBve : List SpecEntry}
    (hno : tBve.all SpecEntry.noExit = true) (off n : Nat) :
    ((tBve.drop off).take n).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at hno ⊢
  intro e he
  exact hno e (List.mem_of_mem_drop (List.mem_of_mem_take he))

private theorem bveAllDrop_noExit {tBve : List SpecEntry}
    (hno : tBve.all SpecEntry.noExit = true) (off : Nat) :
    (tBve.drop off).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at hno ⊢
  intro e he
  exact hno e (List.mem_of_mem_drop he)

private theorem bveAllTake_noExit {tBve : List SpecEntry}
    (hno : tBve.all SpecEntry.noExit = true) (n : Nat) :
    (tBve.take n).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at hno ⊢
  intro e he
  exact hno e (List.mem_of_mem_take he)

theorem m7FidRowsPart3Pfx_sigs {tPfx tBve : List SpecEntry}
    (hsigP : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hsigB : tBve.map (fun e => (e.name, e.as, e.rs)) = m7FidBveFns.map Fn.sig) :
    (m7FidRowsPart3Pfx tPfx tBve).map (fun e => (e.name, e.as, e.rs)) =
      (m7FnsPart3.take 129).map Fn.sig := by
  have s01 : p3Sweep22Rows.map (fun e => (e.name, e.as, e.rs)) = p3Sweep22Fns.map Fn.sig := by
    t_kernel_rfl
  have s02 : p3SweepDenseM5Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3SweepDenseM5Fns.map Fn.sig := by t_kernel_rfl
  have s03 : p3FwdDedupBinsRows.map (fun e => (e.name, e.as, e.rs)) =
      p3FwdDedupBinsFns.map Fn.sig := by t_kernel_rfl
  have s04 : p3Bve5Rows.map (fun e => (e.name, e.as, e.rs)) = p3Bve5Fns.map Fn.sig := by
    t_kernel_rfl
  have s05 : p3InitFreshVarRows.map (fun e => (e.name, e.as, e.rs)) =
      p3InitFreshVarFns.map Fn.sig := by t_kernel_rfl
  have s06 : p3BvaHopRows.map (fun e => (e.name, e.as, e.rs)) = p3BvaHopFns.map Fn.sig := by
    t_kernel_rfl
  have s07 : p3BvaMatchLargeRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaMatchLargeFns.map Fn.sig := by t_kernel_rfl
  have s08 : p3BvaScanCandsRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaScanCandsFns.map Fn.sig := by t_kernel_rfl
  have s09 : p3BvaPickCandRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaPickCandFns.map Fn.sig := by t_kernel_rfl
  have s10 : p3BvaFilterRowRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaFilterRowFns.map Fn.sig := by t_kernel_rfl
  have s11 : p3BvaCommitRows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaCommitFns.map Fn.sig := by t_kernel_rfl
  have s12 : p3BvaTryLitM7Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3BvaTryLitM7Fns.map Fn.sig := by t_kernel_rfl
  have s13 : p3FheapPairRows.map (fun e => (e.name, e.as, e.rs)) =
      p3FheapPairFns.map Fn.sig := by t_kernel_rfl
  have s14 : p3FactorM7Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3FactorM7Fns.map Fn.sig := by t_kernel_rfl
  have s15 : p3CfCompact3Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3CfCompact3Fns.map Fn.sig := by t_kernel_rfl
  have s16 : p3Compact10Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3Compact10Fns.map Fn.sig := by t_kernel_rfl
  have s17 : p3ReorderRows.map (fun e => (e.name, e.as, e.rs)) = p3ReorderFns.map Fn.sig := by
    t_kernel_rfl
  have s18 : p3VivBce4Rows.map (fun e => (e.name, e.as, e.rs)) = p3VivBce4Fns.map Fn.sig := by
    t_kernel_rfl
  have s19 : p3SchedMinMaxRows.map (fun e => (e.name, e.as, e.rs)) =
      p3SchedMinMaxFns.map Fn.sig := by t_kernel_rfl
  have s20 : p3ElimDticksRows.map (fun e => (e.name, e.as, e.rs)) =
      p3ElimDticksFns.map Fn.sig := by t_kernel_rfl
  have s21 : p3M7Search14Rows.map (fun e => (e.name, e.as, e.rs)) =
      p3M7Search14Fns.map Fn.sig := by t_kernel_rfl
  have s22 : p3AdpProbeDticksRows.map (fun e => (e.name, e.as, e.rs)) =
      p3AdpProbeDticksFns.map Fn.sig := by t_kernel_rfl
  rw [mf3Pfx_eq]
  simp only [m7FidRowsPart3Pfx, mf3PfxSeg, List.map_append, s01, s02, s03, s04, s05, s06, s07, s08,
    s09, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22,
    pfx21Slice_sigs hsigP, bveAllTake_sigs hsigB, bveAllSlice_sigs hsigB, bveAllDrop_sigs hsigB]

theorem m7FidRowsPart3Pfx_noExit {tPfx tBve : List SpecEntry}
    (hnoP : tPfx.all SpecEntry.noExit = true) (hnoB : tBve.all SpecEntry.noExit = true) :
    (m7FidRowsPart3Pfx tPfx tBve).all SpecEntry.noExit = true := by
  have n01 : p3Sweep22Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n02 : p3SweepDenseM5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n03 : p3FwdDedupBinsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n04 : p3Bve5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n05 : p3InitFreshVarRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n06 : p3BvaHopRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n07 : p3BvaMatchLargeRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n08 : p3BvaScanCandsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n09 : p3BvaPickCandRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n10 : p3BvaFilterRowRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n11 : p3BvaCommitRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n12 : p3BvaTryLitM7Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n13 : p3FheapPairRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n14 : p3FactorM7Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n15 : p3CfCompact3Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n16 : p3Compact10Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n17 : p3ReorderRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n18 : p3VivBce4Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n19 : p3SchedMinMaxRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n20 : p3ElimDticksRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n21 : p3M7Search14Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n22 : p3AdpProbeDticksRows.all SpecEntry.noExit = true := by t_kernel_rfl
  simp only [m7FidRowsPart3Pfx, List.all_append, n01, n02, n03, n04, n05, n06, n07, n08, n09, n10,
    n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22,
    pfx21Slice_noExit hnoP, bveAllTake_noExit hnoB, bveAllSlice_noExit hnoB,
    bveAllDrop_noExit hnoB, Bool.and_self]

theorem m7FidPart3Callees_of_sub {tPfx tBve tbl : List SpecEntry}
    (hsub : ∀ e ∈ m7FidRowsPart3Pfx tPfx tBve, e ∈ tbl) : FullM7Proof.M7Part3TailCallees tbl := by
  have sub_s : ∀ e ∈ p3M7Search14Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 25 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  exact ⟨ sub_s _ (List.mem_of_getElem? (i := 8) rfl)
    , sub_s _ (List.mem_of_getElem? (i := 13) rfl)
    , sub_s _ (List.mem_of_getElem? (i := 11) rfl) ⟩

theorem m7FidRowsPart3Pfx_tPfx_mem {tPfx tBve : List SpecEntry} {i : Nat}
    (h15 : 15 ≤ i) (hi : i < 21) (hit : i < tPfx.length) :
    tPfx[i] ∈ m7FidRowsPart3Pfx tPfx tBve := by
  unfold m7FidRowsPart3Pfx
  rcases Nat.lt_or_ge i 16 with h16 | h16
  · (iterate 2 apply List.mem_append_right); apply List.mem_append_left
    exact m7_mem_drop_take_of_lt tPfx h15 h16 hit
  · rcases Nat.lt_or_ge i 17 with h17 | h17
    · (iterate 20 apply List.mem_append_right); apply List.mem_append_left
      exact m7_mem_drop_take_of_lt tPfx h16 h17 hit
    · (iterate 27 apply List.mem_append_right)
      exact m7_mem_drop_take_of_lt tPfx h17 (by omega) hit

theorem m7FidRowsPart3Pfx_tBve_mem {tPfx tBve : List SpecEntry} {i : Nat}
    (hi : i < 43) (hit : i < tBve.length) :
    tBve[i] ∈ m7FidRowsPart3Pfx tPfx tBve := by
  unfold m7FidRowsPart3Pfx
  rcases Nat.lt_or_ge i 32 with h32 | h32
  · (iterate 4 apply List.mem_append_right); apply List.mem_append_left
    have h32' : i < 0 + 32 := by omega
    have he := m7_mem_drop_take_of_lt tBve (Nat.zero_le _) h32' hit
    simpa [List.drop_zero] using he
  · rcases Nat.lt_or_ge i 34 with h34 | h34
    · (iterate 6 apply List.mem_append_right); apply List.mem_append_left
      exact m7_mem_drop_take_of_lt tBve h32 h34 hit
    · (iterate 24 apply List.mem_append_right); apply List.mem_append_left
      have hj : i - 34 < (tBve.drop 34).length := by rw [List.length_drop]; omega
      have hget : (tBve.drop 34)[i - 34]'hj = tBve[i]'hit := by
        rw [List.getElem_drop]; congr 1; omega
      rw [← hget]; exact List.getElem_mem hj

/-! ## 4. Canonical `full_bce_m4` WP Adapter (`schedEnterDenseSpec` + `Full.fullPropagateSpec`) -/

section BceCanonSection

open LeanQbe.T.Examples.Kissat.FullM4VivBce
open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics M4Tactics

private theorem bv64_toNat_setWidth32_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

private theorem mf_bce_m4_wp (Γ : Env)
    (hEnterDense : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hBceVar : ∀ a m Q X, fullBceVarM4Spec a m Q X →
      Γ "full_bce_var_m4" [i64, i32] [] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullBceM4Spec a m Q X → Func.wp Γ full_bce_m4_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hcl0, hm0, hQ⟩
  have hmx : c.max_vars < 2 ^ 30 := Nat.lt_of_lt_of_le c.hmaxv (by decide)
  unfold Func.wp full_bce_m4_body
  fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 hcl0 (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 hcl0 (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · fvt_steps
    c0_call hEnterDense
    refine ⟨c, F0, s, R, rfl, hsp0, hm0, fun ok s1 m1 hcl1 hfl1 hok_t hok_f hm1 => ?_⟩
    fvt_to_group
    · have hdn1 : FullDenseInv c F0 s1 := hok_t (by c0_bound)
      obtain ⟨F_cur1, hdw1⟩ := FullBveVarHelpers.fullDenseInv_exists_witness hdn1
      have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hdw1.1.core_ok.cur_vars_le
      fvt_steps
      refine wp_loop_inv (ts := [i64, i64])
        (fun (v, done, ()) ml => ∃ sl : FullState,
          FullDenseInvW c F0 F_cur1 sl ∧ sl.core.cur_vars = s1.core.cur_vars ∧
          sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧ v.toNat ≤ s1.core.cur_vars ∧
          (FullMem c sl ⋆ R) ml)
        (fun (v, _, _) _ => s1.core.cur_vars - v.toNat) ?_ ?_
      · intro J hJ; fvt_steps
        exact hJ (0#64, 0#64, ()) m1 ⟨s1, hdw1, rfl, hfl1, Nat.zero_le _, hm1⟩
      · intro J ⟨v, done, ⟨⟩⟩ ml ⟨sl, hinvl, hcvl, hfll, hv_le, hml⟩ ih
        have hv_lt_cv_of : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat →
            v.toNat < s1.core.cur_vars := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact id
        fvt_to_group
        refine wp_join_group (ts := [])
          (fun () m_ex => ∃ s_ex : FullState,
            FullDenseInvW c F0 F_cur1 s_ex ∧ s_ex.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullMem c s_ex ⋆ R) m_ex) ?_ ?_
        · rintro _ ⟨⟩ m_ex ⟨s_ex, hinv_ex, hfl_ex, hm_ex⟩
          c0_call hRebuild
          refine ⟨c, F0, s_ex, R, rfl, hinv_ex.toDense, hm_ex,
            fun rr s3 m3 hsp3 hcl3 hfl3 _ h20_3 hm3 => ?_⟩
          fvt_steps
          · exact hQ 20#64 s3 m3 hsp3 hcl3 (Nat.le_trans hfl3 hfl_ex) (Or.inr rfl)
              (fun _ => h20_3 (by c0_bound)) hm3
          · exact hQ 20#64 s3 m3 hsp3 hcl3 (Nat.le_trans hfl3 hfl_ex) (Or.inr rfl)
              (fun _ => m4_unsat_of_inconsistent hsp3 (by c0_bound)) hm3
          · obtain ⟨F_cur3, hsw3⟩ := hsp3.exists_witness
            c0_call hProp
            refine ⟨c, F0, F_cur3, s3, R, rfl, hsw3.1, hsw3.2.1, hsw3.2.2.2.2.2, hm3,
              fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
                ticks_p wsort_p phases_p m_p hlen_p hw_p _ hperm_p hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s4 : FullState :=
              { s3 with
                core := { s3.core with
                  vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                  trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                  unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                  arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                  fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                  confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                scratch := { s3.scratch with
                  search_ticks := ticks_p, wsort := wsort_p, phases := phases_p } }
            have hsw4 : FullSparseInvW c F0 F_cur3 s4 :=
              m4_sparseInvW_of_prop_canon hsw3 hlen_p hw_p hperm_p
            have hfl4 : s4.core.fuel.toNat ≤ s.core.fuel.toNat :=
              Nat.le_trans hfl_p (Nat.le_trans hfl3 hfl_ex)
            fvt_steps
            all_goals first
              | exact hQ 1#64 s4 m_p hsw4.toSparse hcl3 hfl4 (Or.inl rfl)
                  (fun h => by cases h) hm_p
              | exact hQ 20#64 s4 m_p hsw4.toSparse hcl3 hfl4 (Or.inr rfl)
                  (fun _ => FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl3
                    (hpr1 (by c0_bound)).2.2) hm_p
        · intro Jex hJex
          fvt_to_group
          · have hv_lt : v.toNat < s1.core.cur_vars := hv_lt_cv_of (by c0_bound)
            have hv_fl : v.toNat < sl.core.flags.length := by
              rw [hinvl.1.core_ok.flags_len]; omega
            have hv2_lt : (v <<< (BitVec.toNat (1 : BitVec 64) % 64)).toNat <
                sl.core.vals.length := by
              rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
                Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hinvl.1.core_ok.vals_len]
              omega
            have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
            refine wp_join_group (ts := [i64])
              (fun (done', ()) mj => ∃ sj : FullState,
                FullDenseInvW c F0 F_cur1 sj ∧ sj.core.cur_vars = s1.core.cur_vars ∧
                sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj) ?_ ?_
            · rintro _ ⟨done', ⟨⟩⟩ mj ⟨sj, hinvj, hcvj, hflj, hmj⟩
              fvt_steps
              exact ih (v + 1#64, done', ()) mj (by dsimp only; omega)
                ⟨sj, hinvj, hcvj, hflj, by omega, hmj⟩
            · intro Jv hJv
              fvt_steps
              · c0_call hBceVar
                refine ⟨c, F0, F_cur1, sl, R, rfl, hinvl,
                  by rw [bv64_toNat_setWidth32_lt (by omega), hcvl]; exact hv_lt, hml,
                  fun sv mv hinvv hcvv hflv hmv =>
                    hJv (done + 1#64, ()) mv ⟨sv, hinvv, hcvv.trans hcvl,
                      by rw [hflv]; exact hfll, hmv⟩⟩
              · exact hJv (done, ()) ml ⟨sl, hinvl, hcvl, hfll, hml⟩
              · exact hJv (done, ()) ml ⟨sl, hinvl, hcvl, hfll, hml⟩
          all_goals exact hJex () ml ⟨sl, hinvl, hfll, hml⟩
    · have hsp1 : FullSparseInv c F0 s1 := hok_f (by c0_bound)
      fvt_steps
      · exact hQ 20#64 s1 m1 hsp1 hcl1 hfl1 (Or.inr rfl)
          (fun _ => m4_unsat_of_inconsistent hsp1 (by c0_bound)) hm1
      · exact hQ 1#64 s1 m1 hsp1 hcl1 hfl1 (Or.inl rfl)
          (fun h => by cases h) hm1

end BceCanonSection

/-! ## 5. Part 3 Prefix Segment `TableImpl` Proofs -/

private theorem mf3CfCompact3_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hFlush : (⟨"full_flush_trail", [i64], [i64],
      FullM6CompactFlush.fullFlushTrailSpec, true⟩ : SpecEntry) ∈ tbl)
    (hSweep : (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p3CfCompact3Fns p3CfCompact3Rows := by
  unfold p3CfCompact3Fns p3CfCompact3Rows
  exact ⟨ SpecEntry.Impl.of (FullM6CompactFlush.full_compact_needed_m6cf_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CompactFlush.full_compact_flush_m6cf_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hFlush) (envRow_mem hnd _ _ _ _ hSweep))
    , SpecEntry.Impl.of (FullM6CompactFlush.full_compact_mark_live_m6cf_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNext)), trivial ⟩

private theorem mf3Reorder_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3ReorderRows, e ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p3ReorderFns p3ReorderRows := by
  have hfn : p3ReorderFns =
      [ ⟨"full_reorder_weight_m7", [i64], [i64], FullM7Reorder.full_reorder_weight_m7_body⟩
      , ⟨"full_reorder_sift_m7", [i64, i64, i64], [], FullM7Reorder.full_reorder_sift_m7_body⟩
      , ⟨"full_reorder_queue_m7", [i64], [i64], FullM7Reorder.full_reorder_queue_m7_body⟩ ] :=
    rfl
  have er := envRowAt hnd hown
  rw [hfn]; unfold p3ReorderRows
  exact ⟨ SpecEntry.Impl.of (FullM7Reorder.full_reorder_weight_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Reorder.full_reorder_sift_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Reorder.full_reorder_queue_m7_wp (Env.ofTable tbl)
        (er 0 rfl (fun _ _ _ _ h => FullM7Reorder.m7ReorderWeightSpec_noExit h))
        (envRow_mem hnd _ _ _ _ hNext)
        (er 1 rfl (fun _ _ _ _ h => FullM7Reorder.m7ReorderSiftSpec_noExit h))), trivial ⟩

private theorem mf3VivBce4_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3VivBce4Rows, e ∈ tbl)
    (hBce : (⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool],
      Full.fullBveTryBceSpec, true⟩ : SpecEntry) ∈ tbl)
    (hEp2 : (⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ : SpecEntry) ∈ tbl)
    (hEpCl : (⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ : SpecEntry) ∈ tbl)
    (hDelBin : (⟨"full_delete_binary", [i64, i32, i32], [], Full.fullDeleteBinarySpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hCol : (⟨"full_bve_collect", [i64, i32, i64, i32], [i32], Full.fullBveCollectSpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hEd : (⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hReb : (⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3VivBce4Fns p3VivBce4Rows := by
  have hfn : p3VivBce4Fns =
      [ ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
          FullM4VivBce.full_bce_side_m4_body⟩
      , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.full_bce_pair_m4_body⟩
      , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.full_bce_var_m4_body⟩
      , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.full_bce_m4_body⟩ ] := by t_kernel_rfl
  have er := envRowAt hnd hown
  rw [hfn]; unfold p3VivBce4Rows
  exact ⟨ SpecEntry.Impl.of (FullM4VivBce.full_bce_side_m4_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hBce)
        (m6_extend_push2_tmk_to_canon (envRow_mem hnd _ _ _ _ hEp2))
        (m6_extend_push_cl_tmk_to_canon (envRow_mem hnd _ _ _ _ hEpCl))
        (envRow_mem hnd _ _ _ _ hDelBin))
    , SpecEntry.Impl.of (FullM4VivBce.full_bce_pair_m4_wp (Env.ofTable tbl)
        (er 0 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM4VivBce.full_bce_var_m4_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hCol) (er 1 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (mf_bce_m4_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hEd)
        (er 2 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hReb)
        (envRow_mem hnd _ _ _ _ hProp)), trivial ⟩

private theorem mf3M7Search14_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p3M7Search14Rows, e ∈ tbl)
    (hLog : (⟨"full_log10_q16_m7", [i64], [i64], FullM7Search.m7Log10Q16Spec, true⟩ : SpecEntry) ∈
      tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hIlog : (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈ tbl)
    (hHeapDn : (⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hNDV : (⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hAsg : (⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ : SpecEntry) ∈ tbl)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl)
    (hScan : (⟨"full_lucky_scan", [i64, .bool, .bool], [i64], Full.fullLuckyScanSpec, true⟩ :
      SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p3M7Search14Fns p3M7Search14Rows := by
  have hfn : p3M7Search14Fns =
      [ ⟨"full_lcg_next_m7", [i64], [i64], FullM7Search.full_lcg_next_m7_body⟩
      , ⟨"full_m7_get64", [i64, i64], [i64], FullM7Search.full_m7_get64_body⟩
      , ⟨"full_m7_set64", [i64, i64, i64], [], FullM7Search.full_m7_set64_body⟩
      , ⟨"full_m7_state_init", [i64], [], FullM7Search.full_m7_state_init_body⟩
      , ⟨"full_tumble_clause_m7", [i64, i32], [.bool], FullM7Search.full_tumble_clause_m7_body⟩
      , ⟨"full_tumble_clauses_m7", [i64, i64], [i64], FullM7Search.full_tumble_clauses_m7_body⟩
      , ⟨"full_tumble_m7", [i64], [i64], FullM7Search.full_tumble_m7_body⟩
      , ⟨"full_lucky_polar_m7", [i64], [i64], FullM7Search.full_lucky_polar_m7_body⟩
      , ⟨"full_lucky_late_m7", [i64], [i64], FullM7Search.full_lucky_late_m7_body⟩
      , ⟨"full_randec_step_m7", [i64], [], FullM7Search.full_randec_step_m7_body⟩
      , ⟨"full_randec_var_m7", [i64], [i64], FullM7Search.full_randec_var_m7_body⟩
      , ⟨"full_decide_m7", [i64], [i64], FullM7Search.full_decide_m7_body⟩
      , ⟨"full_ema_swap_m7", [i64, i64, i64], [], FullM7Search.full_ema_swap_m7_body⟩
      , ⟨"full_switch_mode_m7", [i64], [], FullM7Search.full_switch_mode_m7_body⟩ ] := rfl
  have er := envRowAt hnd hown
  have rLcg := er 0 rfl (fun _ _ _ _ h => FullM7Search.m7LcgNextSpec_monoX h)
  have rGet := er 1 rfl (fun _ _ _ _ h => FullM7Search.m7Get64Spec_monoX h)
  have rSet := er 2 rfl (fun _ _ _ _ h => FullM7Search.m7Set64Spec_monoX h)
  have rInit := er 3 rfl (fun _ _ _ _ h => FullM7Search.m7StateInitSpec_monoX h)
  have rTc := er 4 rfl (fun _ _ _ _ h => FullM7Search.m7TumbleClauseSpec_monoX h)
  have rTcs := er 5 rfl (fun _ _ _ _ h => FullM7Search.m7TumbleClausesSpec_monoX h)
  have rPol := er 7 rfl (fun _ _ _ _ h => h)
  have rRv := er 10 rfl (fun _ _ _ _ h => FullM7Search.m7RandecVarSpec_monoX h)
  have rEma := er 12 rfl (fun _ _ _ _ h => FullM7Search.m7EmaSwapSpec_monoX h)
  have rLog := envRow_mem hnd _ _ _ _ hLog (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h)
  have rNext := envRow_mem hnd _ _ _ _ hNext
  have rAsg := envRow_mem hnd _ _ _ _ hAsg
  rw [hfn]; unfold p3M7Search14Rows
  exact ⟨ SpecEntry.Impl.of (FullM7Search.full_lcg_next_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Search.full_m7_get64_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Search.full_m7_set64_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Search.full_m7_state_init_wp (Env.ofTable tbl) rGet rSet)
    , SpecEntry.Impl.of (FullM7Search.full_tumble_clause_m7_wp (Env.ofTable tbl) rLcg)
    , SpecEntry.Impl.of (FullM7Search.full_tumble_clauses_m7_wp (Env.ofTable tbl) rNext rTc)
    , SpecEntry.Impl.of (FullM7Search.full_tumble_m7_wp (Env.ofTable tbl) rTcs)
    , SpecEntry.Impl.of (FullM7Search.full_lucky_polar_m7_wp (Env.ofTable tbl) rNext)
    , SpecEntry.Impl.of (FullM7Search.full_lucky_late_m7_wp (Env.ofTable tbl) rPol
        (envRow_mem hnd _ _ _ _ hScan) rAsg (envRow_mem hnd _ _ _ _ hBt)
        (envRow_mem hnd _ _ _ _ hProp))
    , SpecEntry.Impl.of (FullM7Search.full_randec_step_m7_wp (Env.ofTable tbl) rInit rGet rSet)
    , SpecEntry.Impl.of (FullM7Search.full_randec_var_m7_wp (Env.ofTable tbl)
        rLcg rInit rGet rSet rLog)
    , SpecEntry.Impl.of (FullM7Search.full_decide_m7_wp (Env.ofTable tbl) rRv
        (envRow_mem hnd _ _ _ _ hNDV) rAsg)
    , SpecEntry.Impl.of (FullM7Search.full_ema_swap_m7_wp (Env.ofTable tbl) rInit rGet rSet)
    , SpecEntry.Impl.of (FullM7Search.full_switch_mode_m7_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hIlog) (envRow_mem hnd _ _ _ _ hHeapDn) rEma rLog)
    , trivial ⟩

/-- `AllFns Fn.Wf` for all `134` functions of `m7FnsPart3`. -/
theorem m7FnsPart3_wf : AllFns Fn.Wf m7FnsPart3 :=
  FullM6Transport.allFns_of_mem fun f hf => FullM7.m7Fns_wf f (by
    unfold FullM7.m7Fns; exact List.mem_append_right _ hf)

/-- Certifies all `129` prefix functions of `m7FnsPart3` against `m7FidRowsPart3Pfx tPfx tBve`
in `Env.ofTable tbl`, parameterized over `hPfxOk` (`[15..20]`) and `hBveOk` (`43` fns). -/
theorem m7FidRowsPart3Pfx_tableImpl {tPfx tBve tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hPfxLen : m7OrchPfxFns.length = tPfx.length)
    (hPfxOk : TableImpl (Env.ofTable tbl) m7OrchPfxFns tPfx)
    (hBveLen : m7FidBveFns.length = tBve.length)
    (hBveOk : TableImpl (Env.ofTable tbl) m7FidBveFns tBve)
    (hBveSpecs : FullM7Proof.M7BveAllTblSpecs tBve)
    (htBve : ∀ e ∈ tBve, e ∈ tbl)
    (hPfxSpecs : FullM7Proof.M7OrchPfxTblSpecs tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hc1 : FullM7Proof.M7Part1Callees tbl) (hc2 : FullM7Proof.M7Part2Callees tbl)
    (hOwn : ∀ e ∈ m7FidRowsPart3Pfx tPfx tBve, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) (m7FnsPart3.take 129) (m7FidRowsPart3Pfx tPfx tBve) := by
  have sub_sw22 : ∀ e ∈ p3Sweep22Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx; exact List.mem_append_left _ h)
  have sub_fwd : ∀ e ∈ p3FwdDedupBinsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 3 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_b5 : ∀ e ∈ p3Bve5Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 5 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_ifv : ∀ e ∈ p3InitFreshVarRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 7 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_bhop : ∀ e ∈ p3BvaHopRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 8 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_bml : ∀ e ∈ p3BvaMatchLargeRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 9 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_bsc : ∀ e ∈ p3BvaScanCandsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 10 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_bpc : ∀ e ∈ p3BvaPickCandRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 11 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_bfr : ∀ e ∈ p3BvaFilterRowRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 12 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_bcom : ∀ e ∈ p3BvaCommitRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 13 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_btl : ∀ e ∈ p3BvaTryLitM7Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 14 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_fh : ∀ e ∈ p3FheapPairRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 15 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_fac : ∀ e ∈ p3FactorM7Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 16 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_cfc : ∀ e ∈ p3CfCompact3Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 17 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_cmp10 : ∀ e ∈ p3Compact10Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 18 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_reord : ∀ e ∈ p3ReorderRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 19 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_bce4 : ∀ e ∈ p3VivBce4Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 21 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have sub_srch14 : ∀ e ∈ p3M7Search14Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 25 apply List.mem_append_right)
    exact List.mem_append_left _ h)
  have rDef := htPfx _ hPfxSpecs.wstackDefrag
  have rWp := htPfx _ hPfxSpecs.watchPush
  have rRew := htPfx _ hPfxSpecs.rewatchArena
  have rSwp := htPfx _ hPfxSpecs.arenaSweep
  have rBveCol := htBve _ hBveSpecs.bveCollect
  have rSwpVar := sub_sw22 _ (List.mem_of_getElem? (i := 21) rfl)
  have rTryBce := sub_b5 _ (List.mem_of_getElem? (i := 2) rfl)
  have rIfv := sub_ifv _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaML := sub_bml _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaSC := sub_bsc _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaPC := sub_bpc _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaFR := sub_bfr _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaCom := sub_bcom _ (List.mem_of_getElem? (i := 0) rfl)
  have rBvaTL := sub_btl _ (List.mem_of_getElem? (i := 0) rfl)
  have rFhUp := sub_fh _ (List.mem_of_getElem? (i := 0) rfl)
  have rFhDn := sub_fh _ (List.mem_of_getElem? (i := 1) rfl)
  have rCmpFl := sub_cfc _ (List.mem_of_getElem? (i := 1) rfl)
  have rCmpMl := sub_cfc _ (List.mem_of_getElem? (i := 2) rfl)
  have rMaxU : (⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩ :
      SpecEntry) ∈ tbl := hOwn _ (by
    unfold m7FidRowsPart3Pfx
    (iterate 22 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
  have ps : ∀ off n,
      TableImpl (Env.ofTable tbl) ((m7OrchPfxFns.drop off).take n) ((tPfx.drop off).take n) :=
    tableImpl_drop_take hPfxLen hPfxOk
  have hlen_p : ∀ (off n : Nat),
      ((m7OrchPfxFns.drop off).take n).length = ((tPfx.drop off).take n).length := by
    intro off n; simp [hPfxLen]
  have bs : ∀ off n,
      TableImpl (Env.ofTable tbl) ((m7FidBveFns.drop off).take n) ((tBve.drop off).take n) :=
    tableImpl_drop_take hBveLen hBveOk
  have hlen_b_tk : ∀ (n : Nat), (m7FidBveFns.take n).length = (tBve.take n).length := by
    intro n; simp [hBveLen]
  have hlen_b_sl : ∀ (off n : Nat),
      ((m7FidBveFns.drop off).take n).length = ((tBve.drop off).take n).length := by
    intro off n; simp [hBveLen]
  have hlen_b_dr : ∀ (off : Nat), (m7FidBveFns.drop off).length = (tBve.drop off).length := by
    intro off; simp [hBveLen]
  have ib_tk32 : TableImpl (Env.ofTable tbl) (m7FidBveFns.take 32) (tBve.take 32) := by
    simpa only [List.drop_zero] using bs 0 32
  have ib_dr34 : TableImpl (Env.ofTable tbl) (m7FidBveFns.drop 34) (tBve.drop 34) := by
    have h43 : m7FidBveFns.length = 43 := m7FidBveFns_length
    have he1 : m7FidBveFns.drop 34 = (m7FidBveFns.drop 34).take 9 :=
      (List.take_of_length_le (by rw [List.length_drop, h43]; omega)).symm
    have he2 : tBve.drop 34 = (tBve.drop 34).take 9 :=
      (List.take_of_length_le (by rw [List.length_drop, ← hBveLen, h43]; omega)).symm
    rw [he1, he2]; exact bs 34 9
  have i_sw22 : TableImpl (Env.ofTable tbl) p3Sweep22Fns p3Sweep22Rows :=
    (modTakeSliceTransport FullM4Sweep.fullM4SweepEnv_moduleOk
      FullM4Sweep.fullM4SweepSpecTable_nodup (by t_kernel_rfl) 0 22 (by decide)
      [ FullM4Sweep.fullM4SweepSpecTable[24]'(by decide)
      , FullM4Sweep.fullM4SweepSpecTable[27]'(by decide)
      , FullM4Sweep.fullM4SweepSpecTable[28]'(by decide) ]
      (by t_kernel_rfl)
      (m7_memC (List.getElem_mem _) (m7_memC (List.getElem_mem _) (m7_mem1 (List.getElem_mem _))))
      hnd sub_sw22 (m7_memC hc1.rngNext (m7_memC hc2.addUnit (m7_mem1 hc2.addBin)))).2
  have i_swdm5 : TableImpl (Env.ofTable tbl) p3SweepDenseM5Fns p3SweepDenseM5Rows :=
    m7_oneImpl rfl rfl (FullM5Orch.full_sweep_dense_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rSwpVar))
  have i_fwd : TableImpl (Env.ofTable tbl) p3FwdDedupBinsFns p3FwdDedupBinsRows :=
    (fullSliceTransport 145 1
      [⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩]
      (by t_kernel_rfl) (m7_mem1 (fullRow_at 102 _)) hnd sub_fwd (m7_mem1 hc2.addUnit)).2
  have i_bve5 : TableImpl (Env.ofTable tbl) p3Bve5Fns p3Bve5Rows := by
    have sub_rp : ∀ e ∈ p3BveResPairRows, e ∈ tbl := fun _ h => sub_b5 _ (by
      unfold p3Bve5Rows; (iterate 4 apply List.mem_append_left); exact h)
    have sub_tb : ∀ e ∈ p3BveTryBceRows, e ∈ tbl := fun _ h => sub_b5 _ (by
      unfold p3Bve5Rows; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_right _ h)
    have sub_en : ∀ e ∈ p3BveExtNeedRows, e ∈ tbl := fun _ h => sub_b5 _ (by
      unfold p3Bve5Rows; exact List.mem_append_right _ h)
    have i_rp := (fullSliceTransport 151 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_rp
      (fun _ h => nomatch h)).2
    have i_wk : TableImpl (Env.ofTable tbl) (Full.fullFns.drop 152 |>.take 1) p3BveWeakenRows :=
      m7_oneImpl rfl rfl (FullFast.fast_bve_weaken_tmk_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hc2.extendPush2) (envRow_mem hnd _ _ _ _ hc2.deleteBinary)
        (envRow_mem hnd _ _ _ _ hc2.extendPushCl))
    have i_tb := (fullSliceTransport 153 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_tb
      (fun _ h => nomatch h)).2
    have i_cr : TableImpl (Env.ofTable tbl) (Full.fullFns.drop 154 |>.take 1) p3BveCommitResRows :=
      m7_oneImpl rfl rfl (FullFast.fast_bve_commit_res_tmk_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hc1.allocCl) (envRow_mem hnd _ _ _ _ rWp)
        (envRow_mem hnd _ _ _ _ hc2.addBin) (envRow_mem hnd _ _ _ _ hc2.addUnit))
    have i_en := (fullSliceTransport 155 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_en
      (fun _ h => nomatch h)).2
    have hf : p3Bve5Fns =
        (Full.fullFns.drop 151).take 1 ++ (Full.fullFns.drop 152).take 1 ++
        (Full.fullFns.drop 153).take 1 ++ (Full.fullFns.drop 154).take 1 ++
        (Full.fullFns.drop 155).take 1 := by t_kernel_rfl
    rw [hf]; unfold p3Bve5Rows
    exact tableImpl_append rfl (tableImpl_append rfl (tableImpl_append rfl
      (tableImpl_append rfl i_rp i_wk) i_tb) i_cr) i_en
  have i_ifv : TableImpl (Env.ofTable tbl) p3InitFreshVarFns p3InitFreshVarRows :=
    m7_oneImpl rfl rfl (FullM7BvaFactor.full_init_fresh_var_m7_heap_wp (Env.ofTable tbl))
  have i_bhop : TableImpl (Env.ofTable tbl) p3BvaHopFns p3BvaHopRows :=
    (modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
      0 3 (by decide) [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_bhop
      (fun _ h => nomatch h)).2
  have i_bml : TableImpl (Env.ofTable tbl) p3BvaMatchLargeFns p3BvaMatchLargeRows :=
    m7_oneImpl rfl rfl (FullBvaHeap.full_bva_match_large_wp (Env.ofTable tbl))
  have i_bsc : TableImpl (Env.ofTable tbl) p3BvaScanCandsFns p3BvaScanCandsRows :=
    m7_oneImpl rfl rfl (FullM4Bva.m4_bva_scan_cands_wp (Env.ofTable tbl))
  have i_bpc : TableImpl (Env.ofTable tbl) p3BvaPickCandFns p3BvaPickCandRows :=
    m7_oneImpl rfl rfl (FullM6BvaNoHops.m6_bva_pick_cand_no_hops_wp (Env.ofTable tbl))
  have i_bfr : TableImpl (Env.ofTable tbl) p3BvaFilterRowFns p3BvaFilterRowRows :=
    (modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
      4 1 (by decide) [FullM4Bva.m4BvaSpecTable[19]'(by decide)] (by t_kernel_rfl)
      (m7_mem1 (List.getElem_mem _)) hnd sub_bfr (m7_mem1 rBvaML)).2
  have i_bcom : TableImpl (Env.ofTable tbl) p3BvaCommitFns p3BvaCommitRows :=
    m7_oneImpl rfl rfl (FullM5DenseSafe.full_bva_commit_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rDef) (envRow_mem hnd _ _ _ _ rIfv)
      (envRow_mem hnd _ _ _ _ hc2.addBin) (envRow_mem hnd _ _ _ _ hc1.allocCl)
      (envRow_mem hnd _ _ _ _ rWp) (envRow_mem hnd _ _ _ _ hc2.deleteBinary)
      (envRow_mem hnd _ _ _ _ hc1.unwatchLarge))
  have i_btl : TableImpl (Env.ofTable tbl) p3BvaTryLitM7Fns p3BvaTryLitM7Rows :=
    m7_oneImpl rfl rfl (FullM7BvaFactor.full_bva_try_lit_m7_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rBvaSC) (envRow_mem hnd _ _ _ _ rBvaPC)
      (envRow_mem hnd _ _ _ _ rBvaFR) (envRow_mem hnd _ _ _ _ rBvaCom))
  have i_fh : TableImpl (Env.ofTable tbl) p3FheapPairFns p3FheapPairRows := by
    have hfn : p3FheapPairFns =
        [ ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.full_fheap_up_body⟩
        , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [],
            FullBvaHeap.full_fheap_down_body⟩ ] := by t_kernel_rfl
    rw [hfn]; unfold p3FheapPairRows
    exact ⟨ SpecEntry.Impl.of (FullBvaHeap.full_fheap_up_wp (Env.ofTable tbl))
      , SpecEntry.Impl.of (FullBvaHeap.full_fheap_down_wp (Env.ofTable tbl)), trivial ⟩
  have i_fac : TableImpl (Env.ofTable tbl) p3FactorM7Fns p3FactorM7Rows :=
    m7_oneImpl rfl rfl (FullM7BvaFactor.full_factor_m7_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rFhUp) (envRow_mem hnd _ _ _ _ rFhDn)
      (envRow_mem hnd _ _ _ _ rBvaTL))
  have i_cfc := mf3CfCompact3_impl hnd hc1.flushTrail rSwp hc1.arenaNext
  have i_cmp10 : TableImpl (Env.ofTable tbl) p3Compact10Fns p3Compact10Rows :=
    (modTakeSliceTransport FullM4Compact.compact_moduleOk FullM4Compact.compactSpecTable_nodup
      (by t_kernel_rfl) 3 10 (by decide)
      [ FullM4Compact.compactSpecTable[1]'(by decide)
      , FullM4Compact.compactSpecTable[2]'(by decide)
      , FullM4Compact.compactSpecTable[13]'(by decide)
      , FullM4Compact.compactSpecTable[14]'(by decide)
      , FullM4Compact.compactSpecTable[15]'(by decide)
      , FullM4Compact.compactSpecTable[18]'(by decide) ]
      (by t_kernel_rfl)
      (m7_memC (List.getElem_mem _) <| m7_memC (List.getElem_mem _) <|
        m7_memC (List.getElem_mem _) <| m7_memC (List.getElem_mem _) <|
        m7_memC (List.getElem_mem _) <| m7_mem1 (List.getElem_mem _))
      hnd sub_cmp10
      (m7_memC rCmpFl <| m7_memC rCmpMl <| m7_memC hc1.arenaNext <|
        m7_memC rDef <| m7_memC rWp <| m7_mem1 rRew)).2
  have i_reord := mf3Reorder_impl hnd sub_reord hc1.arenaNext
  have i_bce4 := mf3VivBce4_impl hnd sub_bce4 rTryBce hc2.extendPush2 hc2.extendPushCl
    hc2.deleteBinary rBveCol hc2.enterDense hc2.rebuildWatches hc1.propagate
  have i_minmax : TableImpl (Env.ofTable tbl) p3SchedMinMaxFns p3SchedMinMaxRows := by
    have hfn : p3SchedMinMaxFns =
        [ ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.full_min_u64_body⟩
        , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.full_max_u64_body⟩ ] := by
      t_kernel_rfl
    rw [hfn]; unfold p3SchedMinMaxRows
    exact ⟨ SpecEntry.Impl.of (FullFastSched.sched_min_u64_wp (Env.ofTable tbl))
      , SpecEntry.Impl.of (FullFastSched.sched_max_u64_wp (Env.ofTable tbl)), trivial ⟩
  have i_edticks : TableImpl (Env.ofTable tbl) p3ElimDticksFns p3ElimDticksRows :=
    m7_oneImpl rfl rfl (FullM5Orch.full_elim_dticks_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rMaxU))
  have i_srch14 := mf3M7Search14_impl hnd sub_srch14 hc1.log10Q16M7 hc1.arenaNext hc1.ilog10
    hc1.heapDown hc2.nextDecVar hc1.assign hc1.backtrack hc1.propagate hc2.luckyScan
  have i_adp15 : TableImpl (Env.ofTable tbl) p3AdpProbeDticksFns p3AdpProbeDticksRows :=
    m7_oneImpl rfl rfl (full_probe_dticks_m6_hdr_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.hdrGetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)))
  rw [mf3Pfx_eq]; unfold mf3PfxSeg m7FidRowsPart3Pfx
  refine tableImpl_append rfl i_sw22 (tableImpl_append rfl i_swdm5 ?_)
  refine tableImpl_append (hlen_p 15 1) (ps 15 1) (tableImpl_append rfl i_fwd ?_)
  refine tableImpl_append (hlen_b_tk 32) ib_tk32 (tableImpl_append rfl i_bve5 ?_)
  refine tableImpl_append (hlen_b_sl 32 2) (bs 32 2) (tableImpl_append rfl i_ifv ?_)
  refine tableImpl_append rfl i_bhop (tableImpl_append rfl i_bml (tableImpl_append rfl i_bsc ?_))
  refine tableImpl_append rfl i_bpc (tableImpl_append rfl i_bfr (tableImpl_append rfl i_bcom ?_))
  refine tableImpl_append rfl i_btl (tableImpl_append rfl i_fh (tableImpl_append rfl i_fac ?_))
  refine tableImpl_append rfl i_cfc (tableImpl_append rfl i_cmp10 (tableImpl_append rfl i_reord ?_))
  refine tableImpl_append (hlen_p 16 1) (ps 16 1) (tableImpl_append rfl i_bce4 ?_)
  refine tableImpl_append rfl i_minmax (tableImpl_append rfl i_edticks ?_)
  refine tableImpl_append (hlen_b_dr 34) ib_dr34 (tableImpl_append rfl i_srch14 ?_)
  exact tableImpl_append rfl i_adp15 (ps 17 4)

theorem m7FidPart3PfxCallees_of_sub {tPfx tBve tbl : List SpecEntry}
    (hOwnPfx : ∀ e ∈ m7FidRowsPart3Pfx tPfx tBve, e ∈ tbl) : FullM7Proof.M7Part3PfxCallees tbl :=
  ⟨ hOwnPfx _ (by
      unfold m7FidRowsPart3Pfx; apply List.mem_append_right
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  , hOwnPfx _ (by
      unfold m7FidRowsPart3Pfx; (iterate 16 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  , hOwnPfx _ (by
      unfold m7FidRowsPart3Pfx; (iterate 17 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  , hOwnPfx _ (by
      unfold m7FidRowsPart3Pfx; (iterate 18 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 9) rfl))
  , hOwnPfx _ (by
      unfold m7FidRowsPart3Pfx; (iterate 19 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))
  , hOwnPfx _ (by
      unfold m7FidRowsPart3Pfx; (iterate 22 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  , hOwnPfx _ (by
      unfold m7FidRowsPart3Pfx; (iterate 26 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl)) ⟩

def m7FidOrchTailRows
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    List SpecEntry :=
  [ ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_search", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩ ]

theorem m7FidOrchTailRows_sigs
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m7FidOrchTailRows solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      (m7FnsPart3.drop 129).map Fn.sig := by
  unfold m7FidOrchTailRows m7FnsPart3
  t_kernel_rfl

theorem m7FidOrchTailRows_noExit
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m7FidOrchTailRows solveSpec).all SpecEntry.noExit = true := by
  unfold m7FidOrchTailRows
  rfl

theorem m7FidOrchTail_solve_mem (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m7FidOrchTailRows solveSpec ∧
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m7FidOrchTailRows solveSpec :=
  ⟨ List.mem_of_getElem? (i := 1) rfl, List.mem_of_getElem? (i := 4) rfl ⟩

/-- `5`-fn orchestration tail (`FullM7.m7FnsPart3.drop 129`, `full_search_m6` through
`kissat_solve_bytes`). -/
def m7FidOrchTailFns : List Fn :=
  [ ⟨"full_search_m6", [i64], [i64], FullM7.full_search_m6_body⟩
  , ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      FullM6Orch.kissat_solve_bytes_m6_body⟩
  , ⟨"full_preprocess", [i64], [i64], FullM6Orch.full_preprocess_body⟩
  , ⟨"full_search", [i64], [i64], FullM6Orch.full_search_body⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      FullM6Orch.kissat_solve_bytes_body⟩ ]

private theorem mfOrchTailFns_eq_drop :
    m7FnsPart3.drop 129 = m7FidOrchTailFns := by
  unfold m7FidOrchTailFns m7FnsPart3; t_kernel_rfl

/-- Parametric `TableImpl` for `m7FidOrchTailFns` (`FullM7.m7FnsPart3.drop 129`) against
`m7FidOrchTailRows solveSpec`. -/
private theorem mfOrchTail_tableImpl (Γ : Env)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hLuckyLate : ∀ a m Q X, FullM7Search.m7LuckyLateSpec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, FullM7Search.m7SwitchModeSpec a m Q X →
      Γ "full_switch_mode_m7" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X →
      Γ "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m7RephaseSpec a m Q X →
      Γ "full_rephase" [i64] [] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, FullM7Search.m7DecideSpec a m Q X →
      Γ "full_decide_m7" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hSearchM6 : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Γ "full_search_m6" [i64] [i64] a m Q X)
    (hSolveM6 : ∀ a m Q X, solveSpec a m Q X →
      Γ "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    TableImpl Γ m7FidOrchTailFns (m7FidOrchTailRows solveSpec) := by
  unfold m7FidOrchTailFns m7FidOrchTailRows
  refine tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
      wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
    (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
        wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
      (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
          wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
        (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
            wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
          (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
              wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
            (tableImpl_nil Γ [])))))
  · exact full_search_m6_m7_wp Γ hLuckyLate hProp hAnalyze hReduce hSwitch hRstDue hRst
      hReorder hRephase hSimplify hDecide xs m Q (fun _ _ _ _ => False) hs
  · exact kissat_solve_bytes_m6_core_wp Γ hMemInit hParse hPre hSearchM6 hExt hCheck xs m Q
      (fun _ _ _ _ => False) (hWeaken xs m Q (fun _ _ _ _ => False) hs)
  · exact full_preprocess_wp Γ hPre xs m Q (fun _ _ _ _ => False) hs
  · exact full_search_wp Γ hSearchM6 xs m Q (fun _ _ _ _ => False) hs
  · exact kissat_solve_bytes_core_wp Γ solveSpec hSolveM6 xs m Q (fun _ _ _ _ => False) hs

/-- Component WP witnesses extracted from `mfOrchTail_tableImpl` (`405..409`) for closed
`spliceModule_moduleOk` tail discharge. -/
theorem mfOrchTail_wp (Γ : Env)
    (hLuckyLate : ∀ a m Q X, FullM7Search.m7LuckyLateSpec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, FullM7Search.m7SwitchModeSpec a m Q X →
      Γ "full_switch_mode_m7" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m7RephaseSpec a m Q X → Γ "full_rephase" [i64] [] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, FullM7Search.m7DecideSpec a m Q X →
      Γ "full_decide_m7" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hSearchM6 : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Γ "full_search_m6" [i64] [i64] a m Q X)
    (hSolveM6 : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Γ "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    (∀ a m Q X, fullM6SearchSpec a m Q X →
      Func.wp Γ FullM7.full_search_m6_body a m Q X) ∧
    (∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Func.wp Γ FullM6Orch.kissat_solve_bytes_m6_body a m Q X) ∧
    (∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ FullM6Orch.full_preprocess_body a m Q X) ∧
    (∀ a m Q X, fullM6SearchSpec a m Q X →
      Func.wp Γ FullM6Orch.full_search_body a m Q X) ∧
    (∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Func.wp Γ FullM6Orch.kissat_solve_bytes_body a m Q X) := by
  exact ⟨
    fun xs m Q _ hs => wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
      (full_search_m6_m7_wp Γ hLuckyLate hProp hAnalyze hReduce hSwitch hRstDue hRst hReorder
        hRephase hSimplify hDecide xs m Q (fun _ _ _ _ => False) (fullM6SearchSpec_monoX hs)),
    fun xs m Q _ hs => wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
      (kissat_solve_bytes_m6_core_wp Γ hMemInit hParse hPre hSearchM6 hExt hCheck xs m Q
        (fun _ _ _ _ => False) (m7FidSolveBytesSpec_to_coreModel hs)),
    fun xs m Q _ hs => wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
      (full_preprocess_wp Γ hPre xs m Q (fun _ _ _ _ => False) (fullM6PreprocessSpec_monoX hs)),
    fun xs m Q _ hs => wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
      (full_search_wp Γ hSearchM6 xs m Q (fun _ _ _ _ => False) (fullM6SearchSpec_monoX hs)),
    fun xs m Q _ hs => wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
      (kissat_solve_bytes_core_wp Γ m7FidSolveBytesSpec hSolveM6 xs m Q
        (fun _ _ _ _ => False) (m7FidSolveBytesSpec_monoX hs))⟩

/-- Complete transparent `410`-row specification table for `m7Module`
(`solveSpec := m7FidSolveBytesSpec`, zero SAT model proofs). -/
def m7FidBaseTable : List SpecEntry :=
  m7FidRowsPart1 m7FidOrchPfxRows ++
    (m7RowsPart2 m7FidOrchPfxRows ++
      (m7FidRowsPart3Pfx m7FidOrchPfxRows m7FidBveRows ++
        m7FidOrchTailRows m7FidSolveBytesSpec))

/-- Closed `410`-row base `Env` for `m7Module` (pre-splice). -/
def m7FidBaseEnv : Env := Env.ofTable m7FidBaseTable

private theorem mf_len_eq_of_sigs_eq {fs : List Fn} {rs : List SpecEntry}
    (h : rs.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig) : fs.length = rs.length := by
  have h1 := congrArg List.length h
  simpa only [List.length_map] using h1.symm

theorem m7FidBaseTable_sigs :
    m7FidBaseTable.map (fun e => (e.name, e.as, e.rs)) = m7Fns.map Fn.sig := by
  have hm123 : m7Fns =
      m7FnsPart1 ++ (m7FnsPart2 ++ (m7FnsPart3.take 129 ++ m7FnsPart3.drop 129)) := by
    rw [m7Fns, List.append_assoc, List.take_append_drop]
  rw [hm123]
  unfold m7FidBaseTable
  simp only [List.map_append]
  rw [m7FidRowsPart1_sigs m7FidOrchPfxRows_sigs, m7RowsPart2_sigs m7FidOrchPfxRows_sigs,
    m7FidRowsPart3Pfx_sigs m7FidOrchPfxRows_sigs m7FidBveRows_sigs,
    m7FidOrchTailRows_sigs m7FidSolveBytesSpec]

theorem m7FidBaseTable_length : m7FidBaseTable.length = 410 :=
  (mf_len_eq_of_sigs_eq m7FidBaseTable_sigs).symm.trans m7Fns_length

theorem m7FidBaseTable_nodup : (m7FidBaseTable.map SpecEntry.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) m7FidBaseTable_sigs
  have hm' : m7FidBaseTable.map SpecEntry.name = m7Module.fns.map Fn.name := by
    dsimp only [m7Module]
    simp only [List.map_map, Function.comp_def, Fn.sig] at hm
    exact hm
  exact tbl_nodup_of_sigs m7_acyclic hm'

theorem m7FidBaseTable_noExit : m7FidBaseTable.all SpecEntry.noExit = true := by
  simp only [m7FidBaseTable, List.all_append, m7FidRowsPart1_noExit m7FidOrchPfxRows_noExit,
    m7RowsPart2_noExit m7FidOrchPfxRows_noExit,
    m7FidRowsPart3Pfx_noExit m7FidOrchPfxRows_noExit m7FidBveRows_noExit,
    m7FidOrchTailRows_noExit m7FidSolveBytesSpec, Bool.and_self]

theorem m7FidBaseEnv_noExit : ∀ f as bs xs m Q X X',
    m7FidBaseEnv f as bs xs m Q X → m7FidBaseEnv f as bs xs m Q X' :=
  env_ofTable_noExit_all m7FidBaseTable_noExit

theorem m7FidBase_elim_of_mem {e : SpecEntry} (he : e ∈ m7FidBaseTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : m7FidBaseEnv e.name e.as e.rs xs m Q X) : e.eff xs m Q X :=
  env_ofTable_elim_of_mem he m7FidBaseTable_nodup h

theorem m7FidBase_row_mem {f : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → m7FidBaseEnv f as bs xs m Q X :=
  envRow_mem m7FidBaseTable_nodup f as bs sp hmem hno

theorem m7FidBase_part1_mem : ∀ e ∈ m7FidRowsPart1 m7FidOrchPfxRows, e ∈ m7FidBaseTable :=
  fun _ h => List.mem_append_left _ h

theorem m7FidBase_part2_mem : ∀ e ∈ m7RowsPart2 m7FidOrchPfxRows, e ∈ m7FidBaseTable :=
  fun _ h => List.mem_append_right _ (List.mem_append_left _ h)

theorem m7FidBase_part3Pfx_mem :
    ∀ e ∈ m7FidRowsPart3Pfx m7FidOrchPfxRows m7FidBveRows, e ∈ m7FidBaseTable :=
  fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))

theorem m7FidBase_tail_mem :
    ∀ e ∈ m7FidOrchTailRows m7FidSolveBytesSpec, e ∈ m7FidBaseTable :=
  fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))

theorem m7FidBase_pfx_mem : ∀ e ∈ m7FidOrchPfxRows, e ∈ m7FidBaseTable := by
  have hlen : m7FidOrchPfxRows.length = 21 := rfl
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, rfl⟩
  have hi21 : i < 21 := hlen ▸ hi
  rcases Nat.lt_or_ge i 10 with h10 | h10
  · exact m7FidBase_part1_mem _ (m7FidRowsPart1_tPfx_mem h10 hi)
  · rcases Nat.lt_or_ge i 15 with h15 | h15
    · exact m7FidBase_part2_mem _ (m7RowsPart2_tPfx_mem h10 h15 hi)
    · exact m7FidBase_part3Pfx_mem _ (m7FidRowsPart3Pfx_tPfx_mem h15 hi21 hi)

theorem m7FidBase_bve_mem : ∀ e ∈ m7FidBveRows, e ∈ m7FidBaseTable := by
  have hlen : m7FidBveRows.length = 43 := rfl
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, rfl⟩
  have hi43 : i < 43 := hlen ▸ hi
  exact m7FidBase_part3Pfx_mem _ (m7FidRowsPart3Pfx_tBve_mem hi43 hi)

theorem m7FidBase_solve_bytes_iff {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidBaseEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      m7FidSolveBytesSpec xs m Q (fun _ _ _ _ => False) := by
  have hmem := m7FidBase_tail_mem _ (m7FidOrchTail_solve_mem m7FidSolveBytesSpec).2
  exact ⟨fun h => env_ofTable_elim_of_mem hmem m7FidBaseTable_nodup h,
    fun h => Env.ofTable_of_mem hmem m7FidBaseTable_nodup h⟩

theorem m7FidP3DedupBins_mem :
    (⟨"full_fwd_dedup_bins", [i64], [.bool], Full.fullFwdDedupBinsSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 3 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

theorem m7FidP3Bve5_mem {i : Nat} (hi : i < p3Bve5Rows.length) :
    p3Bve5Rows[i] ∈ m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 5 apply List.mem_append_right)
    exact List.mem_append_left _ (List.getElem_mem hi))

theorem m7FidP3InitFreshVar_mem :
    (⟨"full_init_fresh_var", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 7 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

theorem m7FidP3Factor_mem :
    (⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 16 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

theorem m7FidP3MinU64_mem :
    (⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 22 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

theorem m7FidP3ElimDticks_mem :
    (⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 23 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

theorem m7FidBase_bvaCommit_mem :
    (⟨"full_bva_commit", [i64, i32], [.bool], FullM4Bva.m4BvaCommitSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 13 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

theorem m7FidBase_compactMarkLive_mem :
    (⟨"full_compact_mark_live", [i64], [], FullM4Compact.fullCompactMarkLiveSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 17 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))

theorem m7FidBase_compactVars_mem :
    (⟨"full_compact_vars", [i64, i64, i64], [], FullM4Compact.fullCompactVarsSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 18 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 4) rfl))

theorem m7FidBase_fixedBytes_mem :
    (⟨"full_fixed_bytes", [i64], [i64], Full.fullFixedBytesSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part1_mem _ m7FidP1FixedBytes_mem

theorem m7FidBase_calcMaxV_mem :
    (⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], Full.fullCalcMaxVSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part1_mem _ m7FidP1CalcMaxV_mem

theorem m7FidBase_sweepCopy_mem :
    (⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], Full.fullSweepCopySpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part1_mem _ m7FidP1SweepCopy_mem

theorem m7FidBase_heapUp_mem :
    (⟨"full_heap_up", [i64, i32], [], Full.fullHeapUpSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part1_mem _ m7FidP1HeapUp_mem

theorem m7FidBase_bvaScanCands_mem :
    (⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], FullM4Bva.m4BvaScanCandsSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 10 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

theorem m7FidBase_bvaFilterRow_mem :
    (⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4Bva.m4BvaFilterRowSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 12 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

theorem m7FidBase_m7Set64_mem :
    (⟨"full_m7_set64", [i64, i64, i64], [], FullM7Search.m7Set64Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 25 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))

theorem m7FidBase_emaSwap_mem :
    (⟨"full_ema_swap_m7", [i64, i64, i64], [], FullM7Search.m7EmaSwapSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 25 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 12) rfl))

section RowMems
open FullFastBveBudgets FullFastSched FullM3CongBva FullM6BveFwd FullM7BveGates

theorem m7FidBase_sweepDenseM6_mem :
    (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64],
      FullDefSweep.fullSweepDenseSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 15) rfl)

theorem m7FidBase_probeTailM6_mem :
    (⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 17) rfl)

theorem m7FidBase_probeM6_mem :
    (⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 18) rfl)

theorem m7FidBase_denseFlushUnits_mem :
    (⟨"full_dense_flush_units_m7", [i64], [.bool], fullDenseFlushUnitsM6Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 1) rfl)

theorem m7FidBase_fwdFlushLarge_mem :
    (⟨"full_fwd_flush_large_m7", [i64], [], fullFwdFlushLargeM6Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 2) rfl)

theorem m7FidBase_fwdReconnIrred_mem :
    (⟨"full_fwd_reconnect_irred_m7", [i64], [], fullFwdReconnectIrredM6Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 3) rfl)

theorem m7FidBase_fwdCheckCl_mem :
    (⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], fullFwdCheckClM7Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 5) rfl)

theorem m7FidBase_fwdConnSub_mem :
    (⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], fullFwdConnectSubsumerM6Spec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 6) rfl)

theorem m7FidBase_fwdColSort_mem :
    (⟨"full_fwd_collect_sort_m7", [i64], [i64], fullFwdCollectSortM6Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 7) rfl)

theorem m7FidBase_elimBveM7_mem :
    (⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 40) rfl)

theorem m7FidBase_searchM6_mem :
    (⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_tail_mem _ (List.mem_of_getElem? (i := 0) rfl)

theorem m7FidBase_preprocess_mem :
    (⟨"full_preprocess", [i64], [i64], fullM6PreprocessSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_tail_mem _ (List.mem_of_getElem? (i := 2) rfl)

theorem m7FidBase_search_mem :
    (⟨"full_search", [i64], [i64], fullM6SearchSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_tail_mem _ (List.mem_of_getElem? (i := 3) rfl)

theorem m7FidBase_deduce1uipM6Hdr_mem :
    (⟨"full_deduce_1uip_m6_hdr", [i64], [i64], m7Deduce1uipHdrSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 13) rfl)

theorem m7FidBase_bveVar_mem :
    (⟨"full_bve_var_m7", [i64, i32], [i64], fullBveVarDefSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 32) rfl)

theorem m7FidBase_bveHeapPush_mem :
    (⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], fullBveHeapPushM6Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 37) rfl)

theorem m7FidBase_bveHeapPop_mem :
    (⟨"full_bve_heap_pop_m7", [i64, i64], [i32], fullBveHeapPopM6Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 38) rfl)

theorem m7FidBase_bveCollectNbrs_mem :
    (⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 39) rfl)

end RowMems

theorem m7Fid_solve_bytes_m6_mem : FullM6Orch.m6oSolveBytesM6Fn ∈ m7Module.fns :=
  m7oSolveBytesM6Fn_mem

theorem m7Fid_solve_bytes_mem : FullM6Orch.m6oSolveBytesFn ∈ m7Module.fns :=
  m7oSolveBytesFn_mem

section BveTableImplSection

open FullFastBveBudgets FullFastSched FullM3CongBva FullM6BveFwd FullM7BveGates

private theorem mf_r {Γ : Env} {nm : String} {as bs : List Ty}
    {sp : Spec as bs}
    (hCal : ∀ e ∈ m7FidBveClosedRows, ∀ a m Q X, e.spec a m Q X → Γ e.name e.as e.rs a m Q X)
    (k : Nat) (hk : m7FidBveClosedRows[k]? = some ⟨nm, as, bs, sp, true⟩) :
    ∀ xs m Q X, sp xs m Q X → Γ nm as bs xs m Q X :=
  hCal ⟨nm, as, bs, sp, true⟩ (List.mem_of_getElem? hk)

private theorem mf_bve_noExit_spec :
    ∀ e ∈ m7FidBveClosedRows, ∀ a m Q X, e.spec a m Q X → e.eff a m Q X := by
  intro e he a m Q X hs
  simp only [m7FidBveClosedRows, m7FidBveRows, m7FidBveExternRows,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h <;>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    dsimp only [SpecEntry.eff] <;>
    simp only [↓reduceIte]
  all_goals first
    | exact hs
    | exact fullDensePropUnitM6Spec_noExit a m Q X hs
    | exact fullDenseFlushUnitsM6Spec_noExit a m Q X hs
    | exact fullFwdFlushLargeM6Spec_noExit a m Q X hs
    | exact fullFwdReconnectIrredM6Spec_noExit a m Q X hs
    | exact fullFwdScanLitM7Spec_noExit a m Q X hs
    | exact fullFwdCheckClM7Spec_noExit a m Q X hs
    | exact fullFwdConnectSubsumerM6Spec_noExit a m Q X hs
    | exact fullFwdCollectSortM6Spec_noExit a m Q X hs
    | exact fullBveMarkAndM6Spec_noExit a m Q X hs
    | exact fullBveFindEquivM7Spec_noExit a m Q X hs
    | exact fullBveFindAndM7Spec_noExit a m Q X hs
    | exact fullBveGetTernM7Spec_noExit a m Q X hs
    | exact fullBveMatchTernM7Spec_noExit a m Q X hs
    | exact fullBveFindIteSideM7Spec_noExit a m Q X hs
    | exact fullBveFindIteM7Spec_noExit a m Q X hs
    | exact fullBveXorPatM7Spec_noExit a m Q X hs
    | exact fullBveFindXorM7Spec_noExit a m Q X hs
    | exact fullK6WatchM7Spec_noExit a m Q X hs
    | exact fullK6AssignM7Spec_noExit a m Q X hs
    | exact fullK6MtfM7Spec_noExit a m Q X hs
    | exact fullK6BacktrackM7Spec_noExit a m Q X hs
    | exact fullK6PropM7Spec_noExit a m Q X hs
    | exact fullK6AnaClM7Spec_noExit a m Q X hs
    | exact fullK6AnalyzeM7Spec_noExit a m Q X hs
    | exact fullK6SolveM7Spec_noExit a m Q X hs
    | exact fullK6CoreM7Spec_noExit a m Q X hs
    | exact fullBveGatesM7Spec_noExit a m Q X hs
    | exact fullBveVarKeyM6Spec_noExit a m Q X hs
    | exact fullBveHeapUpM6Spec_noExit a m Q X hs
    | exact fullBveHeapDownM6Spec_noExit a m Q X hs
    | exact fullBveHeapPushM6Spec_noExit a m Q X hs
    | exact fullBveHeapPopM6Spec_noExit a m Q X hs

theorem m7Fid_bve_tableImpl_of_callees {Γ : Env}
    (hCal : ∀ e ∈ m7FidBveClosedRows, ∀ a m Q X, e.spec a m Q X → Γ e.name e.as e.rs a m Q X) :
    TableImpl Γ m7FidBveFns m7FidBveRows := by
  have i0 : SpecEntry.Impl Γ
      ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], full_dense_prop_unit_m7_body⟩
      ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], fullDensePropUnitM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_dense_prop_unit_m7_wp Γ (mf_r hCal 47 rfl))
  have i1 : SpecEntry.Impl Γ
      ⟨"full_dense_flush_units_m7", [i64], [.bool], full_dense_flush_units_m7_body⟩
      ⟨"full_dense_flush_units_m7", [i64], [.bool], fullDenseFlushUnitsM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_dense_flush_units_m7_wp Γ (mf_r hCal 0 rfl))
  have i2 : SpecEntry.Impl Γ
      ⟨"full_fwd_flush_large_m7", [i64], [], full_fwd_flush_large_m7_body⟩
      ⟨"full_fwd_flush_large_m7", [i64], [], fullFwdFlushLargeM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_flush_large_m7_wp Γ (mf_r hCal 44 rfl))
  have i3 : SpecEntry.Impl Γ
      ⟨"full_fwd_reconnect_irred_m7", [i64], [], full_fwd_reconnect_irred_m7_body⟩
      ⟨"full_fwd_reconnect_irred_m7", [i64], [], fullFwdReconnectIrredM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_reconnect_irred_m7_wp Γ
      (mf_r hCal 2 rfl) (mf_r hCal 43 rfl) (mf_r hCal 45 rfl))
  have i4 : SpecEntry.Impl Γ
      ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32], full_fwd_scan_lit_m7_body⟩
      ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32], fullFwdScanLitM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_scan_lit_m7_wp Γ)
  have i5 : SpecEntry.Impl Γ
      ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], full_fwd_check_cl_m7_body⟩
      ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], fullFwdCheckClM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_check_cl_m7_wp Γ
      (mf_r hCal 4 rfl) (mf_r hCal 46 rfl) (mf_r hCal 47 rfl)
      (mf_r hCal 48 rfl) (mf_r hCal 1 rfl))
  have i6 : SpecEntry.Impl Γ
      ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], full_fwd_connect_subsumer_m7_body⟩
      ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], fullFwdConnectSubsumerM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_connect_subsumer_m7_wp Γ (mf_r hCal 45 rfl))
  have i7 : SpecEntry.Impl Γ
      ⟨"full_fwd_collect_sort_m7", [i64], [i64], full_fwd_collect_sort_m7_body⟩
      ⟨"full_fwd_collect_sort_m7", [i64], [i64], fullFwdCollectSortM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_fwd_collect_sort_m7_wp Γ (mf_r hCal 43 rfl))
  have hFwdSub := full_forward_sub_m7_wp Γ
    (mf_r hCal 53 rfl) (mf_r hCal 1 rfl) (mf_r hCal 7 rfl)
    (mf_r hCal 2 rfl) (mf_r hCal 5 rfl) (mf_r hCal 6 rfl)
    (mf_r hCal 43 rfl) (mf_r hCal 3 rfl)
  have i8 : SpecEntry.Impl Γ
      ⟨"full_forward_sub_m7", [i64, i64], [i64], full_forward_sub_m7_body⟩
      ⟨"full_forward_sub_m7", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
    SpecEntry.Impl.of hFwdSub
  have i9 : SpecEntry.Impl Γ
      ⟨"full_bve_collect_m7", [i64, i32, i64, i32], [i32], full_bve_collect_m7_body⟩
      ⟨"full_bve_collect_m7", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩ :=
    SpecEntry.Impl.of (full_bve_collect_m7_wp Γ)
  have i10 : SpecEntry.Impl Γ FullM7.m7ForwardSubCanonFn
      ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
    SpecEntry.Impl.of hFwdSub
  have i11 : SpecEntry.Impl Γ FullM7.m7BveCollectCanonFn
      ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩ :=
    SpecEntry.Impl.of (full_bve_collect_m7_wp Γ)
  have i12 : SpecEntry.Impl Γ
      ⟨"full_bve_mark_and_m7", [i64, i32, i32, i32, i32, i32], [.bool],
        full_bve_mark_and_m7_body⟩
      ⟨"full_bve_mark_and_m7", [i64, i32, i32, i32, i32, i32], [.bool],
        fullBveMarkAndM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_mark_and_m7_wp Γ)
  have i13 : SpecEntry.Impl Γ
      ⟨"full_bve_find_equiv_m7", [i64, i32, i32], [.bool], full_bve_find_equiv_m7_body⟩
      ⟨"full_bve_find_equiv_m7", [i64, i32, i32], [.bool], fullBveFindEquivM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_equiv_m7_wp Γ)
  have i14 : SpecEntry.Impl Γ
      ⟨"full_bve_find_and_m7", [i64, i32, i32, i32], [.bool], full_bve_find_and_m7_body⟩
      ⟨"full_bve_find_and_m7", [i64, i32, i32, i32], [.bool], fullBveFindAndM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_and_m7_wp Γ)
  have i15 : SpecEntry.Impl Γ
      ⟨"full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool], full_bve_get_tern_m7_body⟩
      ⟨"full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool], fullBveGetTernM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_get_tern_m7_wp Γ)
  have i16 : SpecEntry.Impl Γ
      ⟨"full_bve_match_tern_m7", [i64, i32, i32, i32, i32, i32], [i32],
        full_bve_match_tern_m7_body⟩
      ⟨"full_bve_match_tern_m7", [i64, i32, i32, i32, i32, i32], [i32],
        fullBveMatchTernM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_match_tern_m7_wp Γ)
  have i17 : SpecEntry.Impl Γ
      ⟨"full_bve_find_ite_side_m7", [i64, i32, i32, i32, .bool], [.bool],
        full_bve_find_ite_side_m7_body⟩
      ⟨"full_bve_find_ite_side_m7", [i64, i32, i32, i32, .bool], [.bool],
        fullBveFindIteSideM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_ite_side_m7_wp Γ
      (mf_r hCal 15 rfl) (mf_r hCal 16 rfl))
  have i18 : SpecEntry.Impl Γ
      ⟨"full_bve_find_ite_m7", [i64, i32, i32, i32], [.bool], full_bve_find_ite_m7_body⟩
      ⟨"full_bve_find_ite_m7", [i64, i32, i32, i32], [.bool], fullBveFindIteM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_ite_m7_wp Γ (mf_r hCal 17 rfl))
  have i19 : SpecEntry.Impl Γ
      ⟨"full_bve_xor_pat_m7", [i64, i32, i32, i32], [i32], full_bve_xor_pat_m7_body⟩
      ⟨"full_bve_xor_pat_m7", [i64, i32, i32, i32], [i32], fullBveXorPatM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_xor_pat_m7_wp Γ)
  have i20 : SpecEntry.Impl Γ
      ⟨"full_bve_find_xor_m7", [i64, i32, i32, i32], [.bool], full_bve_find_xor_m7_body⟩
      ⟨"full_bve_find_xor_m7", [i64, i32, i32, i32], [.bool], fullBveFindXorM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_find_xor_m7_wp Γ (mf_r hCal 19 rfl))
  have i21 : SpecEntry.Impl Γ
      ⟨"full_k6_watch_m7", [i64, i32, i32, i32, i32], [], full_k6_watch_m7_body⟩
      ⟨"full_k6_watch_m7", [i64, i32, i32, i32, i32], [], fullK6WatchM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_watch_m7_wp Γ)
  have i22 : SpecEntry.Impl Γ
      ⟨"full_k6_assign_m7", [i64, i32, i32], [], full_k6_assign_m7_body⟩
      ⟨"full_k6_assign_m7", [i64, i32, i32], [], fullK6AssignM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_assign_m7_wp Γ)
  have i23 : SpecEntry.Impl Γ
      ⟨"full_k6_mtf_m7", [i64, i32], [], full_k6_mtf_m7_body⟩
      ⟨"full_k6_mtf_m7", [i64, i32], [], fullK6MtfM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_mtf_m7_wp Γ)
  have i24 : SpecEntry.Impl Γ
      ⟨"full_k6_backtrack_m7", [i64, i32], [], full_k6_backtrack_m7_body⟩
      ⟨"full_k6_backtrack_m7", [i64, i32], [], fullK6BacktrackM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_backtrack_m7_wp Γ)
  have i25 : SpecEntry.Impl Γ
      ⟨"full_k6_prop_m7", [i64], [i32], full_k6_prop_m7_body⟩
      ⟨"full_k6_prop_m7", [i64], [i32], fullK6PropM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_prop_m7_wp Γ (mf_r hCal 22 rfl))
  have i26 : SpecEntry.Impl Γ
      ⟨"full_k6_ana_cl_m7", [i64, i32, i32], [], full_k6_ana_cl_m7_body⟩
      ⟨"full_k6_ana_cl_m7", [i64, i32, i32], [], fullK6AnaClM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_ana_cl_m7_wp Γ)
  have i27 : SpecEntry.Impl Γ
      ⟨"full_k6_analyze_m7", [i64, i32], [.bool], full_k6_analyze_m7_body⟩
      ⟨"full_k6_analyze_m7", [i64, i32], [.bool], fullK6AnalyzeM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_analyze_m7_wp Γ
      (mf_r hCal 21 rfl) (mf_r hCal 22 rfl)
      (mf_r hCal 24 rfl) (mf_r hCal 23 rfl) (mf_r hCal 26 rfl))
  have i28 : SpecEntry.Impl Γ
      ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], full_k6_solve_m7_body⟩
      ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], fullK6SolveM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_solve_m7_wp Γ
      (mf_r hCal 25 rfl) (mf_r hCal 22 rfl)
      (mf_r hCal 24 rfl) (mf_r hCal 27 rfl))
  have i29 : SpecEntry.Impl Γ
      ⟨"full_k6_core_m7", [i64], [], full_k6_core_m7_body⟩
      ⟨"full_k6_core_m7", [i64], [], fullK6CoreM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_k6_core_m7_wp Γ)
  have i30 : SpecEntry.Impl Γ
      ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], full_bve_def_k6_m7_body⟩
      ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_def_k6_m7_wp Γ
      (mf_r hCal 21 rfl) (mf_r hCal 28 rfl) (mf_r hCal 29 rfl))
  have i31 : SpecEntry.Impl Γ
      ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], full_bve_gates_m7_body⟩
      ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_gates_m7_wp Γ
      (mf_r hCal 13 rfl) (mf_r hCal 14 rfl) (mf_r hCal 18 rfl)
      (mf_r hCal 20 rfl) (mf_r hCal 30 rfl))
  have hBveVar := full_bve_var_m7_wp Γ
    (mf_r hCal 9 rfl) (mf_r hCal 58 rfl) (mf_r hCal 55 rfl)
    (mf_r hCal 50 rfl) (mf_r hCal 31 rfl) (mf_r hCal 54 rfl)
    (mf_r hCal 44 rfl) (mf_r hCal 57 rfl) (mf_r hCal 1 rfl)
    (mf_r hCal 56 rfl) (mf_r hCal 51 rfl) (mf_r hCal 49 rfl)
    (mf_r hCal 52 rfl)
  have r32 : SpecEntry.Impl Γ
      ⟨"full_bve_var_m7", [i64, i32], [i64], full_bve_var_m7_body⟩
      ⟨"full_bve_var_m7", [i64, i32], [i64], fullBveVarDefSpec, true⟩ :=
    SpecEntry.Impl.of hBveVar
  have i33 : SpecEntry.Impl Γ FullM7.m7BveVarCanonFn
      ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩ :=
    SpecEntry.Impl.of hBveVar
  have i34 : SpecEntry.Impl Γ
      ⟨"full_bve_var_key_m7", [i64, i32], [i64], full_bve_var_key_m7_body⟩
      ⟨"full_bve_var_key_m7", [i64, i32], [i64], fullBveVarKeyM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_var_key_m7_wp Γ)
  have i35 : SpecEntry.Impl Γ
      ⟨"full_bve_heap_up_m7", [i64, i64, i32], [], full_bve_heap_up_m7_body⟩
      ⟨"full_bve_heap_up_m7", [i64, i64, i32], [], fullBveHeapUpM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_heap_up_m7_wp Γ)
  have i36 : SpecEntry.Impl Γ
      ⟨"full_bve_heap_down_m7", [i64, i64, i32], [], full_bve_heap_down_m7_body⟩
      ⟨"full_bve_heap_down_m7", [i64, i64, i32], [], fullBveHeapDownM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_heap_down_m7_wp Γ)
  have i37 : SpecEntry.Impl Γ
      ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], full_bve_heap_push_m7_body⟩
      ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], fullBveHeapPushM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_heap_push_m7_wp Γ
      (mf_r hCal 34 rfl) (mf_r hCal 35 rfl) (mf_r hCal 36 rfl))
  have i38 : SpecEntry.Impl Γ
      ⟨"full_bve_heap_pop_m7", [i64, i64], [i32], full_bve_heap_pop_m7_body⟩
      ⟨"full_bve_heap_pop_m7", [i64, i64], [i32], fullBveHeapPopM6Spec, true⟩ :=
    SpecEntry.Impl.of (full_bve_heap_pop_m7_wp Γ (mf_r hCal 36 rfl))
  have i39 : SpecEntry.Impl Γ
      ⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64], full_bve_collect_nbrs_m7_body⟩
      ⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩ :=
    SpecEntry.Impl.of (full_bve_collect_nbrs_m7_wp Γ)
  have i40 : SpecEntry.Impl Γ
      ⟨"full_elim_bve_m7", [i64, i64], [i64], full_elim_bve_m7_body⟩
      ⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :=
    SpecEntry.Impl.of (full_elim_bve_m7_wp Γ
      (mf_r hCal 1 rfl) (mf_r hCal 37 rfl) (mf_r hCal 38 rfl)
      (mf_r hCal 39 rfl) (mf_r hCal 32 rfl))
  have hElim := full_eliminate_m7_wp Γ
    (mf_r hCal 59 rfl) (mf_r hCal 60 rfl) (mf_r hCal 61 rfl)
    (mf_r hCal 63 rfl) (mf_r hCal 62 rfl) (mf_r hCal 8 rfl)
    (mf_r hCal 40 rfl) (mf_r hCal 64 rfl) (mf_r hCal 65 rfl)
  have i41 : SpecEntry.Impl Γ
      ⟨"full_eliminate_m7", [i64, .bool], [i64], full_eliminate_m7_body⟩
      ⟨"full_eliminate_m7", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
    SpecEntry.Impl.of hElim
  have i42 : SpecEntry.Impl Γ FullM7.m7EliminateM6Fn
      ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
    SpecEntry.Impl.of hElim
  unfold m7FidBveFns FullM7BveGates.m7BveGates_fns m7FidBveRows
  exact ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18,
    i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31, r32, i33, i34, i35, i36,
    i37, i38, i39, i40, i41, i42, trivial⟩

end BveTableImplSection

private theorem mf_bveClosed_callees :
    ∀ e ∈ m7FidBveClosedRows, ∀ a m Q X, e.spec a m Q X →
      m7FidBaseEnv e.name e.as e.rs a m Q X := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have rWp := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.watchPush
  have rWd := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag
  have rDedup := m7FidP3DedupBins_mem
  have rB0 := m7FidP3Bve5_mem (i := 0) (by decide)
  have rB1 := m7FidP3Bve5_mem (i := 1) (by decide)
  have rB2 := m7FidP3Bve5_mem (i := 2) (by decide)
  have rB3 := m7FidP3Bve5_mem (i := 3) (by decide)
  have rB4 := m7FidP3Bve5_mem (i := 4) (by decide)
  have rEdt := m7FidP3ElimDticks_mem
  have rMinU := m7FidP3MinU64_mem
  have rFac := m7FidP3Factor_mem
  intro e he a m Q X hsp
  have hnx := mf_bve_noExit_spec e he a m Q X hsp
  rw [m7FidBveClosedRows, List.mem_append] at he
  rcases he with hbve | hext
  · exact Env.ofTable_of_mem (m7FidBase_bve_mem e hbve) m7FidBaseTable_nodup hnx
  · simp only [m7FidBveExternRows, List.mem_cons, List.not_mem_nil, or_false] at hext
    rcases hext with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Env.ofTable_of_mem hc1.arenaNext m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rWd m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rWp m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc1.unwatchLarge m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc2.addUnit m7FidBaseTable_nodup hnx
    · exact m6_add_bin_m6_to_canon (envRow_mem m7FidBaseTable_nodup _ _ _ _ hc2.addBin)
        a m Q X hsp
    · exact Env.ofTable_of_mem hc2.deleteBinary m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc2.setInactive m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc2.extendPush2 m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc2.extendPushCl m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rDedup m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rB0 m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rB1 m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rB2 m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rB3 m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rB4 m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rEdt m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc1.ilog10 m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc1.scaleDelta m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rMinU m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc2.enterDense m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem rFac m7FidBaseTable_nodup hnx
    · exact Env.ofTable_of_mem hc2.rebuildWatches m7FidBaseTable_nodup hnx

/-- Closed `43`-row `TableImpl` for `m7FidBveFns` against `m7FidBveRows` under `m7FidBaseEnv`. -/
theorem m7Fid_bve_tableImpl : TableImpl m7FidBaseEnv m7FidBveFns m7FidBveRows :=
  m7Fid_bve_tableImpl_of_callees mf_bveClosed_callees

theorem m7Fid_orchPfx_tableImpl
    : TableImpl m7FidBaseEnv m7OrchPfxFns m7FidOrchPfxRows := by
  have hnd := m7FidBaseTable_nodup
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc1p := m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  let htPfx : ∀ e ∈ m7FidOrchPfxRows, e ∈ m7FidBaseTable := m7FidBase_pfx_mem
  let htBve : ∀ e ∈ m7FidBveRows, e ∈ m7FidBaseTable := m7FidBase_bve_mem
  have rArSwp := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 7) rfl))
  have rMrkRsn := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 8) rfl))
  have rAnaRsn := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 10) rfl))
    (fun _ _ _ _ h => m7AnalyzeRsnHdrSpec_monoX h)
  have rDed1uip := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 13) rfl))
    (fun _ _ _ _ h => m7Deduce1uipHdrSpec_monoX h)
  have rSwpDense := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 15) rfl))
  have rProbeTail := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 17) rfl))
    (fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
  have rProbeM6 := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 18) rfl))
    (fun _ _ _ _ h => m6ProbeSpec_monoX h)
  have rMsM6 := envRow_mem hnd _ _ _ _ hc2p.minShrinkM6
    (fun _ _ _ _ h => FullM7SpecBridges.m7MinShrinkSpec_monoX h)
  have hProp := m7_fullPropagate_to_bcpS15 (envRow_mem hnd _ _ _ _ hc1.propagate)
  rw [m7OrchPfxFns_eq]; unfold m7FidOrchPfxRows
  exact
    ⟨ SpecEntry.Impl.of (full_wstack_defrag_wp _ (envRow_mem hnd _ _ _ _ hc1p.wstackDefragM6))
    , SpecEntry.Impl.of (full_watch_push_wp _ (envRow_mem hnd _ _ _ _ hc1p.watchPushM6))
    , SpecEntry.Impl.of (full_rescale_wp _ (envRow_mem hnd _ _ _ _ hc1p.rescaleM6))
    , SpecEntry.Impl.of (full_parse_body_wp _ (envRow_mem hnd _ _ _ _ hc1p.parseBodyM6))
    , SpecEntry.Impl.of (full_lit_rank_wp _ (envRow_mem hnd _ _ _ _ hc1p.litRankM6))
    , SpecEntry.Impl.of (full_sweep_bins_wp _ (envRow_mem hnd _ _ _ _ hc1p.sweepBinsM6cf))
    , SpecEntry.Impl.of (full_rewatch_arena_wp _ (envRow_mem hnd _ _ _ _ hc1p.rewatchArenaM6))
    , SpecEntry.Impl.of (full_arena_sweep_wp _ (envRow_mem hnd _ _ _ _ hc1p.arenaSweepM6))
    , SpecEntry.Impl.of (full_mark_reasons_wp _ (envRow_mem hnd _ _ _ _ hc1p.markReasonsM6))
    , SpecEntry.Impl.of (full_reduce_m6_wp _ (envRow_mem hnd _ _ _ _ hc1.isqrt)
        (envRow_mem hnd _ _ _ _ hc1.ilog10) (envRow_mem hnd _ _ _ _ hc1.arenaNext)
        (envRow_mem hnd _ _ _ _ hc1p.recomputeTiers (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc1.hdrSetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        rMrkRsn (envRow_mem hnd _ _ _ _ hc1p.sortReds) (envRow_mem hnd _ _ _ _ hc1.backtrack)
        hProp rArSwp)
    , SpecEntry.Impl.of (full_analyze_rsn_m6_hdr_m7_wp _ (envRow_mem hnd _ _ _ _ hc2p.analyzeLit)
        (envRow_mem hnd _ _ _ _ hc1p.recordUsed (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)))
    , SpecEntry.Impl.of (full_min_shrink_any_wp _ rMsM6)
    , SpecEntry.Impl.of (full_deduce_1uip_wp _ (envRow_mem hnd _ _ _ _ hc2p.deduce1uipM6))
    , SpecEntry.Impl.of (full_deduce_1uip_m6_hdr_m7_wp _ (envRow_mem hnd _ _ _ _ hc2p.analyzeLit)
        rAnaRsn (envRow_mem hnd _ _ _ _ hc2p.clearAna) (envRow_mem hnd _ _ _ _ hc2p.otfsLarge)
        (envRow_mem hnd _ _ _ _ hc2p.otfsBin) (envRow_mem hnd _ _ _ _ hc2p.otfsSubsume))
    , SpecEntry.Impl.of (full_analyze_core_m6_m7_wp _ (envRow_mem hnd _ _ _ _ hc2p.oneLitConfl)
        (envRow_mem hnd _ _ _ _ hc2p.anaFailedLit
          (fun _ _ _ _ h => FullM6OrchAdapters.m6aAnaFailedLitSpec_monoX h))
        rDed1uip
        (envRow_mem hnd _ _ _ _ hc2p.restoreBumpAna
          (fun _ _ _ _ h => FullM6OrchAdapters.m6aRestoreBumpAnaSpec_monoX h))
        rMsM6 (envRow_mem hnd _ _ _ _ hc1.tickRel) (envRow_mem hnd _ _ _ _ hc1.emaUpdate)
        (envRow_mem hnd _ _ _ _ hc2p.learnClause))
    , SpecEntry.Impl.of (full_sweep_dense_m6_wp _ (envRow_mem hnd _ _ _ _ hc3p.sweepDenseM5))
    , SpecEntry.Impl.of (full_reorder_m6_wp _ (envRow_mem hnd _ _ _ _ hc3p.reorderQueueM7))
    , SpecEntry.Impl.of (full_probe_tail_m6_wp _ (envRow_mem hnd _ _ _ _ hc2p.backboneM6)
        (envRow_mem hnd _ _ _ _ hc2p.transitiveM6) (envRow_mem hnd _ _ _ _ hc3p.minU64)
        (envRow_mem hnd _ _ _ _ hc2p.probeRun)
        (envRow_mem hnd _ _ _ _ hc2p.vivifyM6Hdr
          (fun _ _ _ _ h => FullM6OrchAdapters.m6aVivifySpec_monoX h)))
    , SpecEntry.Impl.of (full_probe_m6_wp _
        (envRow_mem hnd _ _ _ _ hc3p.probeDticks (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc1.ilog10) (envRow_mem hnd _ _ _ _ hc1.scaleDeltaM5)
        (envRow_mem hnd _ _ _ _ hc2.enterDense)
        (envRow_mem hnd _ _ _ _ hc1p.delaying (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc2p.congruenceDense) (envRow_mem hnd _ _ _ _ hc2.rebuildWatches)
        (envRow_mem hnd _ _ _ _ hc1.hdrSetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc1p.reduceDelay (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc1p.bumpDelay (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        rSwpDense (envRow_mem hnd _ _ _ _ hc2p.substitute) rProbeTail
        (envRow_mem hnd _ _ _ _ hc2p.backboneM6) (envRow_mem hnd _ _ _ _ hc3p.minU64)
        (envRow_mem hnd _ _ _ _ hc3p.factor))
    , SpecEntry.Impl.of (full_preprocess_m6_wp _ hProp rArSwp (envRow_mem hnd _ _ _ _ hc2p.lucky)
        (envRow_mem hnd _ _ _ _ hc3p.compactNeeded) (envRow_mem hnd _ _ _ _ hc3p.compact)
        (envRow_mem hnd _ _ _ _ hc1.scaleDeltaM5) rProbeM6)
    , SpecEntry.Impl.of (full_simplify_m6_wp _ (envRow_mem hnd _ _ _ _ hc1.backtrack) rProbeM6
        (envRow_mem hnd _ _ _ _ (htBve _ m7FidBveRows_specs.eliminateM6))
        (envRow_mem hnd _ _ _ _ hc3p.compactNeeded) (envRow_mem hnd _ _ _ _ hc3p.compact))
    , trivial ⟩

private theorem mfPart3_tableImpl {tPfx tBve tbl : List SpecEntry}
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hnoExit : tbl.all SpecEntry.noExit = true)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxOk : TableImpl (Env.ofTable tbl) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7FidBveFns.map Fn.sig)
    (hBveOk : TableImpl (Env.ofTable tbl) m7FidBveFns tBve)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (htBve : ∀ e ∈ tBve, e ∈ tbl)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hc1 : M7Part1Callees tbl) (hc2 : M7Part2Callees tbl)
    (ht1Mem : (⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64],
        fullM6MemInitExactSpec, true⟩ : SpecEntry) ∈ tbl ∧
      (⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
        kissatCheckModelExactSpec, true⟩ : SpecEntry) ∈ tbl)
    (hOwnPfx : ∀ e ∈ m7FidRowsPart3Pfx tPfx tBve, e ∈ tbl)
    (hOwnTail : ∀ e ∈ m7FidOrchTailRows solveSpec, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) m7FnsPart3
      (m7FidRowsPart3Pfx tPfx tBve ++ m7FidOrchTailRows solveSpec) := by
  have hPfxLen : m7OrchPfxFns.length = tPfx.length := by
    have h1 := (congrArg List.length hPfxSigs).symm
    simpa only [List.length_map] using h1
  have hBveLen : m7FidBveFns.length = tBve.length := by
    have h1 := (congrArg List.length hBveSigs).symm
    simpa only [List.length_map] using h1
  have h129_len : (m7FnsPart3.take 129).length = (m7FidRowsPart3Pfx tPfx tBve).length := by
    have h1 := (congrArg List.length (m7FidRowsPart3Pfx_sigs hPfxSigs hBveSigs)).symm
    simpa only [List.length_map] using h1
  have hc3 := m7FidPart3Callees_of_sub hOwnPfx
  have rParseBody := htPfx _ hPfxSpecs.parseBody
  have rReduceM6 := htPfx _ hPfxSpecs.reduceM6
  have rReorderM6 := htPfx _ hPfxSpecs.reorderM6
  have rPreM6 := htPfx _ hPfxSpecs.preprocessM6
  have rSimpM6 := htPfx _ hPfxSpecs.simplifyM6
  have rSrchM6 : (⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ : SpecEntry) ∈ tbl :=
    hOwnTail _ (List.mem_of_getElem? (i := 0) rfl)
  have rSolveM6 : (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ tbl :=
    hOwnTail _ (List.mem_of_getElem? (i := 1) rfl)
  have i_pfx := m7FidRowsPart3Pfx_tableImpl hnd hPfxLen hPfxOk hBveLen hBveOk hBveSpecs htBve
    hPfxSpecs htPfx hc1 hc2 hOwnPfx
  have hLkLate := envRow_mem hnd _ _ _ _ hc3.luckyLateM7
    (fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h)
  have hMi := envRow_mem hnd _ _ _ _ ht1Mem.1
    (fun _ _ _ _ h => fullM6MemInitExactSpec_monoX h)
  have hPb := envRow_mem hnd _ _ _ _ rParseBody
  have hPr := envRow_mem hnd _ _ _ _ hc1.propagate
  have hAn := envRow_mem hnd _ _ _ _ hc2.analyzeM6 (fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h)
  have hRd := envRow_mem hnd _ _ _ _ rReduceM6 (fun _ _ _ _ h => m6ReduceSpec_monoX h)
  have hSw := envRow_mem hnd _ _ _ _ hc3.switchModeM7
    (fun _ _ _ _ h => FullM7Search.m7SwitchModeSpec_monoX h)
  have hRdDue := envRow_mem hnd _ _ _ _ hc2.restartDue
  have hRst := envRow_mem hnd _ _ _ _ hc2.restart
  have hReord := envRow_mem hnd _ _ _ _ rReorderM6
  have hReph := envRow_mem hnd _ _ _ _ hc2.rephase (fun _ _ _ _ h => m7RephaseSpec_monoX h)
  have hPreM6 := envRow_mem hnd _ _ _ _ rPreM6 (fun _ _ _ _ h => fullM6PreprocessSpec_monoX h)
  have hSimp := envRow_mem hnd _ _ _ _ rSimpM6 (fun _ _ _ _ h => fullM6SimplifySpec_monoX h)
  have hDec := envRow_mem hnd _ _ _ _ hc3.decideM7
    (fun _ _ _ _ h => FullM7Search.m7DecideSpec_monoX h)
  have hExt := envRow_mem hnd _ _ _ _ hc2.extend
  have hChk := envRow_mem hnd _ _ _ _ ht1Mem.2
  have hSrch := envRow_mem hnd _ _ _ _ rSrchM6 (fun _ _ _ _ h => fullM6SearchSpec_monoX h)
  have hSlv : ∀ a m Q X, solveSpec a m Q X →
      Env.ofTable tbl "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X :=
    fun a m Q X hs => env_ofTable_noExit_all hnoExit _ _ _ _ _ _ (fun _ _ _ _ => False) X
      (Env.ofTable_of_mem rSolveM6 hnd (hSolveMonoX a m Q X (fun _ _ _ _ => False) hs))
  have i_tail := mfOrchTail_tableImpl (Env.ofTable tbl) solveSpec hWeaken
    hLkLate hMi hPb hPr hAn hRd hSw hRdDue hRst hReord hReph hPreM6 hSimp hDec hExt hChk hSrch hSlv
  have h129 : m7FnsPart3.take 129 ++ m7FidOrchTailFns = m7FnsPart3 := by
    rw [← mfOrchTailFns_eq_drop, List.take_append_drop]
  rw [← h129]
  exact tableImpl_append h129_len i_pfx i_tail

/-- Closed `410/410` base `ModuleOk` for `FullM7.m7Module` under transparent `m7FidBaseEnv`
(`solveSpec := m7FidSolveBytesSpec`, `0` hooks, `0` SAT model proofs). -/
theorem m7FidBase_moduleOk : ModuleOk m7FidBaseEnv m7Module := by
  have hnd := m7FidBaseTable_nodup
  have hnoExit : m7FidBaseTable.all SpecEntry.noExit = true := m7FidBaseTable_noExit
  have hPfxLen : m7OrchPfxFns.length = m7FidOrchPfxRows.length :=
    mf_len_eq_of_sigs_eq m7FidOrchPfxRows_sigs
  have hPfxOk := m7Fid_orchPfx_tableImpl
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc1Tail := m7FidPart1TailCallees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2c := m7Part2CongCallees_of_sub m7FidBase_part2_mem
  have i1 : TableImpl m7FidBaseEnv m7FnsPart1 (m7FidRowsPart1 m7FidOrchPfxRows) :=
    m7FidRowsPart1_tableImpl (tbl := m7FidBaseTable) hnd hPfxLen hPfxOk m7FidBase_pfx_mem
      m7FidOrchPfxRows_specs m7FidBase_part1_mem
  have hcd : ∀ xs m Q X, FullM3CongBva.m3CongruenceDenseSpec xs m Q X →
      Func.wp m7FidBaseEnv FullM7.full_congruence_dense_body xs m Q X :=
    full_congruence_dense_m7_wp m7FidBaseEnv
      (envRow_mem hnd _ _ _ _ hc2c.extBin) (envRow_mem hnd _ _ _ _ hc2c.findUE)
      (envRow_mem hnd _ _ _ _ hc2c.extract)
      (envRow_mem hnd _ _ _ _ hc2c.iteAll
        (fun _ _ _ _ h => FullM7CongIte.m7ExtractIteAllM6Spec_monoX h))
      (envRow_mem hnd _ _ _ _ hc2c.work) (envRow_mem hnd _ _ _ _ hc2c.fwdSub)
  have i2 : TableImpl m7FidBaseEnv m7FnsPart2 (m7RowsPart2 m7FidOrchPfxRows) :=
    m7RowsPart2_tableImpl (tbl := m7FidBaseTable) hnd hPfxLen hPfxOk m7FidBase_pfx_mem
      m7FidOrchPfxRows_specs hc1 hcd m7FidBase_part2_mem
  have i3 : TableImpl m7FidBaseEnv m7FnsPart3
      (m7FidRowsPart3Pfx m7FidOrchPfxRows m7FidBveRows ++
        m7FidOrchTailRows m7FidSolveBytesSpec) :=
    mfPart3_tableImpl m7FidSolveBytesSpec
      (fun _ _ _ _ h => m7FidSolveBytesSpec_to_coreModel h)
      (fun _ _ _ _ _ h => m7FidSolveBytesSpec_monoX h)
      hnd hnoExit m7FidOrchPfxRows_sigs hPfxOk m7FidBveRows_sigs m7Fid_bve_tableImpl
      m7FidBveRows_specs m7FidBase_bve_mem m7FidOrchPfxRows_specs m7FidBase_pfx_mem
      hc1 hc2 hc1Tail m7FidBase_part3Pfx_mem m7FidBase_tail_mem
  have i23 : TableImpl m7FidBaseEnv (m7FnsPart2 ++ m7FnsPart3)
      (m7RowsPart2 m7FidOrchPfxRows ++
        (m7FidRowsPart3Pfx m7FidOrchPfxRows m7FidBveRows ++
          m7FidOrchTailRows m7FidSolveBytesSpec)) :=
    tableImpl_append (mf_len_eq_of_sigs_eq (m7RowsPart2_sigs m7FidOrchPfxRows_sigs)) i2 i3
  exact moduleOk_of_two_segments m7_acyclic (List.append_assoc m7FnsPart1 m7FnsPart2 m7FnsPart3)
    (mf_len_eq_of_sigs_eq (m7FidRowsPart1_sigs m7FidOrchPfxRows_sigs))
    m7FnsPart1_wf (allFns_append m7FnsPart2_wf m7FnsPart3_wf) i1 i23

end BaseTableSection

end LeanQbe.T.Examples.Kissat.FullM7Fidelity
