/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelitySweep
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofVar

/-!
# Kissat Full-Fidelity Sweep — `fid_sweep_vars_wp` (`FullFidelitySweepProofVar2`)

Separated from `FullFidelitySweepProofVar` to keep every module cleanly under `< 2,500` LOC while
certifying `full_m6_sweep_vars_body : m6SweepVarsSpec` (Fixes `3a`/`3b`/`3c`: `FL_SWEEP_INC`
round-completion separation, `8`-pass re-collection + immediate representative LIFO stack in
upper `tarjan_reach[cv .. 2*cv-1]`, `1x` Kitten ticks, and persistent cursor resume).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelitySweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep LeanQbe.T.Examples.Kissat.FullM8SweepV2
open Kraken.Bedrock2.Test
open FullArenaTactics K6MemATactics FidVarMemTactics
open scoped FullArenaTactics K6MemATactics FidVarMemTactics

private theorem fid_cv_u32_ptr {p : BitVec 64} {cv_n : Nat} {idx : BitVec 32}
    (hcv : cv_n < 2 ^ 31) (hi : idx.toNat ≤ cv_n) :
    p + (BitVec.ofNat 64 cv_n + idx.setWidth 64) * 4 =
      p + BitVec.ofNat 64 (4 * (cv_n + idx.toNat)) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h1 : idx.toNat < 2 ^ 32 := idx.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  rw [h4, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mul_comm]

private theorem fid_u32_shl1_idx (c : FullCfg) {cv_n : Nat} {ei : BitVec 32}
    (hcv : cv_n ≤ c.max_vars) (hei : ei.toNat < cv_n) :
    (BitVec.setWidth 64 (ei <<< (1 : Nat))).toNat < 2 * c.max_vars ∧
    (BitVec.setWidth 64 (ei <<< (1 : BitVec 32))).toNat < 2 * c.max_vars := by
  have hmx := maxVars_lt_2p31 c
  have h2 : (BitVec.setWidth 64 (ei <<< (1 : Nat))).toNat = 2 * ei.toNat := by bv_omega
  refine ⟨by rw [h2]; omega, ?_⟩
  change (BitVec.setWidth 64 (ei <<< (1 : Nat))).toNat < _
  rw [h2]; omega

private theorem fid_set_trc_getD_lt {trc : List (BitVec 32)} {cv k : Nat} {rv : BitVec 32}
    (hbd : ∀ i < k, (trc[i]?.getD 0#32).toNat < cv)
    {idx : Nat} (hne : ∀ i < k, i ≠ idx) :
    ∀ i < k, ((trc.set idx rv)[i]?.getD 0#32).toNat < cv := fun i hi => by
  rw [List.getElem?_set_ne (hne i hi).symm]
  exact hbd i hi

private theorem fid_u32_shl1_zext_toNat (v : BitVec 32) {n : Nat} (hn : n < 2 ^ 31)
    (hv : v.toNat < n) :
    (BitVec.setWidth 64 (v <<< (1 : Nat))).toNat = 2 * v.toNat := by
  have hlt : v.toNat < 2 ^ 31 := Nat.lt_trans hv hn
  bv_omega

private theorem fid_bv64_sub1_toNat {x : BitVec 64} (hx : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  bv_omega

private theorem fid_bv32_sub1_toNat {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  bv_omega

private theorem fid_cv_add_u32_toNat {cv_n : Nat} {idx : BitVec 32}
    (hcv : cv_n < 2 ^ 31) (hi : idx.toNat ≤ cv_n) :
    (BitVec.ofNat 64 cv_n + idx.setWidth 64).toNat = cv_n + idx.toNat := by
  have h1 : idx.toNat < 2 ^ 32 := idx.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]



private theorem fid_two_mul_lt {cv : Nat} (hcv : cv < 2 ^ 31) : 2 * cv < 2 ^ 64 := by omega

private theorem fid_u32_setWidth_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem fid_lt_2p64_of_2p31 {n : Nat} (hn : n < 2 ^ 31) : n < 2 ^ 64 := by omega

private theorem fid_bv64_add1_lt {v : BitVec 64} {n : Nat} (hv : v.toNat < n)
    (hn : n < 2 ^ 31) : (v + 1#64).toNat = v.toNat + 1 := bv64_add1_toNat (by omega)

private theorem fid_bv32_add1_lt {v : BitVec 32} {n : Nat} (hv : v.toNat < n)
    (hn : n < 2 ^ 31) : (v + 1#32).toNat = v.toNat + 1 := bv32_add1_toNat (by omega)

private theorem fid_sub_add1_lt {a n : Nat} (ha : a < n) : n - (a + 1) < n - a := by omega

private theorem fid_u32_shl1_vals_lt {v : BitVec 32} {cv mv len : Nat}
    (hv : v.toNat < cv) (hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hlen : len = 2 * mv) :
    (BitVec.setWidth 64 (v <<< (1 : Nat))).toNat < len := by
  rw [hlen, fid_u32_shl1_zext_toNat v hcv hv]; omega

private theorem fid_vals_shl1_lt {v : BitVec 64} {cv mv len : Nat}
    (hv : v.toNat < cv) (hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hlen : len = 2 * mv) :
    (v <<< (1 : Nat)).toNat < len := by
  rw [hlen, bv64_shl1_toNat (Nat.lt_trans hv hcv)]; omega

private theorem fid_wvec_pos_lt {v : BitVec 64} {cv mv len : Nat}
    (hv : v.toNat < cv) (hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hlen : len = 4 * mv) :
    (((v <<< (1 : BitVec 64)) <<< (1 : BitVec 64)) + (1 : BitVec 64)).toNat < len := by
  rw [hlen, bv64_wvec_pos_bv_toNat (Nat.lt_trans hv hcv)]; omega

private theorem fid_wvec_neg_lt {v : BitVec 64} {cv mv len : Nat}
    (hv : v.toNat < cv) (hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hlen : len = 4 * mv) :
    ((((v <<< (1 : BitVec 64)) ||| (1 : BitVec 64)) <<< (1 : BitVec 64)) +
      (1 : BitVec 64)).toNat < len := by
  rw [hlen, bv64_wvec_neg_bv_toNat (Nat.lt_trans hv hcv)]; omega

private theorem fid_lit_lt_two_mul {lit cv : Nat} (hcv : cv < 2 ^ 31)
    (h1 : lit < (cv <<< (1 : Nat)) % 2 ^ 64) : lit < 2 * cv := by
  rw [Nat.shiftLeft_eq] at h1; omega

private theorem fid_lit32_repr_lt {lit32 : BitVec 32} {cv mv len : Nat}
    (hlit : lit32.toNat < 2 * cv) (_hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hlen : len = 2 * mv) :
    (BitVec.setWidth 64 lit32).toNat < len := by
  rw [hlen, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega

private theorem fid_rv32_fl_lt {rv32 : BitVec 32} {cv mv len : Nat}
    (hrv : rv32.toNat < cv) (_hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hlen : len = mv) :
    (BitVec.setWidth 64 rv32).toNat < len := by
  rw [hlen, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega

private theorem fid_trc_push_lt {idx cv isz mv len : Nat}
    (hidx : idx = cv + isz) (hlen : len = 2 * mv) (hle : cv ≤ mv) (hisz : isz < cv) :
    idx < len := by omega

private theorem fid_trc_push_nc_ne {idx nc cv isz : Nat}
    (hidx : idx = cv + isz) (hnc : nc ≤ cv) : ∀ i < nc, i ≠ idx := fun i hi => by omega

private theorem fid_trc_push_prev_ne {j isz cv : Nat}
    (hj : j < isz) : cv + j ≠ cv + isz := by omega

private theorem fid_lt_of_add1_lt_ne {j isz : Nat}
    (hj : j < isz + 1) (hne : j ≠ isz) : j < isz := by omega

private theorem fid_sub1_le {a b : Nat} (hp : 0 < a) (hle : a ≤ b) : a - 1 ≤ b := by omega
private theorem fid_sub1_lt {a : Nat} (hp : 0 < a) : a - 1 < a := by omega

private theorem fid_pop_meas_lt {nc ci isz : Nat} (hp : 0 < isz) :
    nc - ci + (isz - 1) < nc - ci + isz := by omega

private theorem fid_push_meas_lt {nc ci ci' isz : Nat} (hc1 : ci' = ci + 1) (hlt : ci < nc) :
    nc - ci' + isz < nc - ci + isz := by omega

private theorem fid_trc_pop_lt {idx cv isz mv len : Nat}
    (hidx : idx = cv + (isz - 1)) (hlen : len = 2 * mv) (hle : cv ≤ mv)
    (hp : 0 < isz) (hisz : isz ≤ cv) : idx < len := by omega

private theorem fid_ci_trc_lt {ci : BitVec 32} {nc cv mv len : Nat}
    (hlen : len = 2 * mv) (_hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hnc : nc ≤ cv)
    (hci : ci.toNat < nc) : (ci.setWidth 64).toNat < len := by
  rw [hlen, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega

private theorem fid_ci_setWidth_eq {ci : BitVec 32} {nc cv : Nat}
    (_hcv : cv < 2 ^ 31) (_hnc : nc ≤ cv) (_hci : ci.toNat < nc) :
    (ci.setWidth 64).toNat = ci.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ci.isLt (by decide))]

theorem fid_sweep_vars_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDP : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec)
    (hCol : M6EnvSpec Γ "full_m6_collect_cands" m6CollectCandsSpec)
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec) :
    ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp Γ FullFidelitySweep.full_m6_sweep_vars_body args m Q X := by
  rintro ⟨h, budget, tlim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htmk, hm, hQ⟩
  unfold Func.wp FullFidelitySweep.full_m6_sweep_vars_body
  have hlen := hinv.lengths
  have hcap_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine fid_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  have hcap_ge : k6MinScr ≤ c.scratch_cap := by
    rcases Nat.lt_or_ge c.scratch_cap k6MinScr with hlt | hle
    · have hmv0 : k6MaxV c.scratch_cap = 0 := k6MaxV_eq_zero hlt
      have hmv0_32 : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := by
        rw [hmv0]; rfl
      have hnot : ¬ (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := hc
      exact absurd hmv0_32 hnot
    · exact hle
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  obtain ⟨F_cur, hwW⟩ := hinv.exists_witness
  have hdw : FullDenseInvW c F0 F_cur s := hwW
  refine fid_call_dense_prop hDP hdw hm
    (fun ok s1 m1 hdw1 hcv1 hfuel1 htmk1 _htrc1 _hok1 hno1 hm1 => ?_)
  c0_hsplit; rotate_left
  · have hokf : ok = false := by cases ok <;> first | rfl | exact hc
    c0_hsteps!
    exact hQ 20#64 s1 m1 (fid_denseInv_of_W hdw1) hcv1 (by rw [hfuel1]; exact Nat.le_refl _)
      (fid_tmkZero_congr htmk hcv1 htmk1) (Or.inr rfl) (fun _ => (hno1 hokf).1) hm1
  have hlen1 := hdw1.1
  have htmk1_z : M6TmkZero s1 := fid_tmkZero_congr htmk hcv1 htmk1
  have hmx := maxVars_lt_2p31 c
  have hcv1_le := hlen1.core_ok.cur_vars_le
  have hcv1_lt : s1.core.cur_vars < 2 ^ 31 := Nat.lt_of_le_of_lt hcv1_le hmx
  have hcv1_2p64 : s1.core.cur_vars < 2 ^ 64 := fid_lt_2p64_of_2p31 hcv1_lt
  obtain ⟨hgu1_28, hgu1_29, hgu1_30, hgu1_28', hgu1_29', hgu1_30'⟩ :=
    fid_gu_idx_lt hlen1.scratch_ok.glue_used_len
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s1 m1 (fid_denseInv_of_W hdw1) hcv1 (by rw [hfuel1]; exact Nat.le_refl _)
      htmk1_z (Or.inl rfl) (fun h => by simp at h) hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (_comp, ()) mc => mc = m1) ?_
    (fun _ hJc => by
      c0_hsplit
      · c0_hsteps!; exact hJc (5#32, ()) m1 rfl
      · c0_hsteps!; exact hJc (_, ()) m1 rfl)
  rintro _ ⟨comp0, ⟨⟩⟩ mc hmc
  subst mc
  c0_hsteps_nogrp
  -- Join after `if (!need_mark) { ... }`
  refine wp_join_group (ts := [i32, i64, .bool])
    (fun (_comp_a, _mo_a, _nm_a, ()) ma =>
      ∃ s_a : FullState, FullDenseInvW c F0 F_cur s_a ∧
        s_a.core.cur_vars = s1.core.cur_vars ∧ s_a.core.fuel = s1.core.fuel ∧
        M6TmkZero s_a ∧ (FullMem c s_a ⋆ R) ma) ?_ ?_
  · rintro _ ⟨comp_a, mo_a, nm_a, ⟨⟩⟩ ma ⟨s_a, hdw_a, hcv_a, hfl_a, htmk_a, hma⟩
    -- Join after `if (need_mark) { ... }`
    refine wp_join_group (ts := [])
      (fun () mb =>
        ∃ s_b : FullState, FullDenseInvW c F0 F_cur s_b ∧
          s_b.core.cur_vars = s1.core.cur_vars ∧ s_b.core.fuel = s1.core.fuel ∧
          M6TmkZero s_b ∧ (FullMem c s_b ⋆ R) mb) ?_ ?_
    · rintro _ _ mb ⟨s_b, hdw_b, hcv_b, hfl_b, htmk_b, hmb⟩
      obtain ⟨L, hL⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap_ge c.hscr := ⟨_, rfl⟩
      have hL_len : L.scrLen = c.scratch_cap := hL ▸ k6LayoutOfCap_scrLen hcap_ge c.hscr
      have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL]; rfl
      have hk_mv32 : BitVec.setWidth 32 (BitVec.ofNat 64 L.maxV) = L.mv32 := by
        have hmL := L.hmaxV
        apply BitVec.eq_of_toNat_eq
        unfold K6Layout.mv32
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        have hlt32 : L.maxV < 2 ^ 32 := Nat.lt_of_le_of_lt hmL.2 (by decide)
        have hlt64 : L.maxV < 2 ^ 64 := Nat.lt_of_le_of_lt hmL.2 (by decide)
        rw [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt hlt32]
      have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
          ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
            (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
        rw [← hL_mv, hk_mv32]
        simpa only [show (1280 : BitVec 32) = 1280#32 from rfl] using
          k6_ptr_base_k6Base L c.pScratchBuf
      c0_hsteps_nogrp
      try rw [hkptr_c0]
      have hk11_ptr := fid_k11_ptr (c := c) (L := L) hL_len
      have hk11_idx := fid_k11_idx (c := c) (L := L) hL_len
      have hk24_ptr := fid_k24_ptr (c := c) (L := L) hL_len
      have hk24_idx := fid_k24_idx (c := c) (L := L) hL_len
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (tl_c, ()) mt => tl_c.toNat ≤ 0xFFFFFFFF ∧ mt = mb)
        ?_ ?_
      ·
          rintro _ ⟨tl_c, ⟨⟩⟩ mt ⟨_htl_le, hmt⟩
          subst mt
          c0_hsteps_nogrp
          -- Join after outer `while (pass < 8u && ...)` loop
          refine wp_join_group (ts := [i64, i64, i32])
            (fun (_tl_e, _rem_e, _pass_e, ()) mp_ex =>
              ∃ s_e : FullState, FullDenseInvW c F0 F_cur s_e ∧
                s_e.core.cur_vars = s1.core.cur_vars ∧
                s_e.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                M6TmkZero s_e ∧ (FullMem c s_e ⋆ R) mp_ex) ?_ ?_
          ·
              rintro _ ⟨_tl_e, _rem_e, _pass_e, ⟨⟩⟩ mp_ex ⟨s_e, hdw_e, hcv_e, hfl_e, htmk_e, hm_e⟩
              have hfuel_all : s_e.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hfuel1] at hfl_e; exact hfl_e
              have hcv_all : s_e.core.cur_vars = s.core.cur_vars := hcv_e.trans hcv1
              c0_hsteps_nogrp
              c0_hsplit
              · c0_hsteps!
                exact hQ 20#64 s_e mp_ex (fid_denseInv_of_W hdw_e) hcv_all hfuel_all htmk_e
                  (Or.inr rfl)
                  (fun _ => (fid_denseInv_of_W hdw_e).inconsistent_unsat (by assumption)) hm_e
              · -- Post-loop `left_inc` check (`while (v < cv)`)
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64, i64])
                  (fun (_li_e, _v_e, ()) m_li =>
                    ∃ fl_li : List (BitVec 32), fl_li.length = c.max_vars ∧
                      (FullMem c { s_e with core := { s_e.core with flags := fl_li } } ⋆ R)
                        m_li)
                  (fun _ (_li_e, _v_e, ()) m_li ⟨fl_li, hfl_li, hm_li⟩ => by
                    let s_li : FullState :=
                      { s_e with core := { s_e.core with flags := fl_li } }
                    have hdw_li : FullDenseInvW c F0 F_cur s_li :=
                      fid_denseInvW_set_flags hdw_e hfl_li
                    have htmk_li : M6TmkZero s_li := fid_tmkZero_congr htmk_e rfl rfl
                    obtain ⟨hge_28, hge_29, hge_30, hge_28', hge_29', hge_30'⟩ :=
                      fid_gu_idx_lt hdw_li.1.scratch_ok.glue_used_len
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [])
                      (fun () m_end => ∃ gu_end : List (BitVec 32), gu_end.length = 64 ∧
                        (FullMem c { s_li with scratch :=
                          { s_li.scratch with glue_used := gu_end } } ⋆ R) m_end)
                      (fun _ () m_end ⟨gu_end, hgu_end, hm_end⟩ => by
                        c0_hsteps!
                        exact hQ 1#64 _ m_end
                          (fid_denseInv_of_W (fid_denseInvW_set_gu hdw_li hgu_end))
                          hcv_all hfuel_all (fid_tmkZero_congr htmk_li rfl rfl)
                          (Or.inl rfl) (fun h => by simp at h) hm_end)
                      (fun _ hJ_end => by
                        c0_hsplit
                        · c0_hsteps_nogrp
                          let gu_e1 := s_li.scratch.glue_used.set (29 : BitVec 64).toNat 0#32
                          let gu_e2 := gu_e1.set (30 : BitVec 64).toNat 0#32
                          have hgu_e2_len : gu_e2.length = 64 := by
                            simp [gu_e2, gu_e1, hdw_li.1.scratch_ok.glue_used_len]
                          obtain ⟨hge2_28, _, _, hge2_28', _, _⟩ := fid_gu_idx_lt hgu_e2_len
                          refine wp_join_group (ts := [])
                            (fun () m_e2 => ∃ gu_e : List (BitVec 32), gu_e.length = 64 ∧
                              (FullMem c { s_li with scratch :=
                                { s_li.scratch with glue_used := gu_e } } ⋆ R) m_e2)
                            (fun _ () m_e2 h => by c0_hsteps!; exact hJ_end () m_e2 h)
                            (fun _ hJe2 => by
                              c0_hsplit
                              · c0_hsteps!
                                refine hJe2 () _ ⟨_, ?_, by assumption⟩
                                simp only [List.length_set, hdw_e.1.scratch_ok.glue_used_len]
                              · c0_hsteps!
                                refine hJe2 () _ ⟨_, ?_, by assumption⟩
                                simp only [List.length_set, hdw_e.1.scratch_ok.glue_used_len])
                        · c0_hsteps!
                          exact hJ_end () m_li
                            ⟨s_li.scratch.glue_used, hdw_li.1.scratch_ok.glue_used_len, hm_li⟩))
                  (fun _ hJ_li => by
                    have hvals_len_e := hdw_e.1.core_ok.vals_len
                    have hwvec_len_e := hdw_e.1.core_ok.wvec_len
                    have hfl_len_e := hdw_e.1.core_ok.flags_len
                    clear hMaxV hCol hDP hSV hQ hgu1_28 hgu1_29 hgu1_30 hgu1_28' hgu1_29'
                      hgu1_30' hdw1 hdw_a hdw_b hm1 hma hmb hkptr_c0 hk11_ptr hk11_idx
                      hk24_ptr hk24_idx hk_mv32 hL_len hL_mv L hL
                    c0_hsteps_nogrp
                    refine wp_loop_inv (ts := [i64])
                      (fun (v_l, ()) mli => v_l.toNat ≤ s1.core.cur_vars ∧
                        ∃ fl_l : List (BitVec 32), fl_l.length = c.max_vars ∧
                          (FullMem c { s_e with core := { s_e.core with flags := fl_l } } ⋆ R)
                            mli)
                      (fun (v_l, ()) _ => s1.core.cur_vars - v_l.toNat)
                      (fun _ hJ_vl => by
                        c0_hsteps!
                        exact hJ_vl (0#64, ()) mp_ex
                          ⟨Nat.zero_le _, s_e.core.flags, hfl_len_e, hm_e⟩)
                      (fun _ (v_l, ()) mli ⟨hv_le, fl_l, hfl_l_len, hmli⟩ hJ_vl => by
                        c0_hsplit; rotate_left
                        · c0_hsteps!
                          exact hJ_li (_, v_l, ()) mli ⟨fl_l, hfl_l_len, hmli⟩
                        · have hv_lt : v_l.toNat < s1.core.cur_vars := by
                            have h1 : v_l.toNat < s1.core.cur_vars % 2 ^ 64 := hc
                            rwa [Nat.mod_eq_of_lt hcv1_2p64] at h1
                          have hv1 : (v_l + 1#64).toNat = v_l.toNat + 1 :=
                            fid_bv64_add1_lt hv_lt hcv1_lt
                          have hv_fl : v_l.toNat < fl_l.length := by
                            rw [hfl_l_len]; exact Nat.lt_of_lt_of_le hv_lt hcv1_le
                          have hv_vals : (v_l <<< (1 : Nat)).toNat < s_e.core.vals.length := by
                            exact fid_vals_shl1_lt hv_lt hcv1_lt hcv1_le hvals_len_e
                          have hpos_bd : (((v_l <<< (1 : BitVec 64)) <<< (1 : BitVec 64)) +
                              (1 : BitVec 64)).toNat < s_e.core.wvec.length := by
                            exact fid_wvec_pos_lt hv_lt hcv1_lt hcv1_le hwvec_len_e
                          have hneg_bd : ((((v_l <<< (1 : BitVec 64)) ||| (1 : BitVec 64)) <<<
                              (1 : BitVec 64)) + (1 : BitVec 64)).toNat <
                              s_e.core.wvec.length := by
                            exact fid_wvec_neg_lt hv_lt hcv1_lt hcv1_le hwvec_len_e
                          refine wp_join_group (ts := [i64])
                            (fun (_li_v, ()) m_v1 => ∃ fl' : List (BitVec 32),
                              fl'.length = c.max_vars ∧
                              (FullMem c { s_e with core := { s_e.core with flags := fl' } } ⋆
                                R) m_v1)
                            (fun _ (_li_v, ()) m_v1 ⟨fl', hfl', hm_v1⟩ => by
                              c0_hsteps!
                              exact hJ_vl (v_l + 1#64, ()) m_v1
                                (by dsimp only; rw [hv1]; exact fid_sub_add1_lt hv_lt)
                                ⟨by rw [hv1]; exact hv_lt, fl', hfl', hm_v1⟩)
                            (fun _ hJ_v1 => by
                              c0_hsplit; rotate_left
                              · c0_hsteps!; exact hJ_v1 (_, ()) mli ⟨fl_l, hfl_l_len, hmli⟩
                              refine wp_join_group (ts := [i64]) (fun (_li_v', ()) m20 => m20 = mli)
                                (fun _ (_li_v', ()) m20 hm20 => by
                                  subst hm20; c0_hsteps!
                                  refine hJ_v1 (_, ()) _ ⟨_, ?_, by assumption⟩
                                  simp only [List.length_set, hfl_l_len])
                                (fun _ hJ20 => by
                                  c0_hsplit; rotate_left
                                  · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                                  c0_hsteps_nogrp
                                  c0_hsplit; rotate_left
                                  · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                                  c0_hsplit; rotate_left
                                  · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                                  c0_hsplit
                                  · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                                  c0_hsplit; rotate_left
                                  · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                                  · c0_hsteps!
                                    exact hJ_li (_, _, ()) mli ⟨fl_l, hfl_l_len, hmli⟩))))
          ·
              intro _ hJ_p_ex
              clear hMaxV hgu1_28 hgu1_29 hgu1_30 hgu1_28' hgu1_29' hgu1_30' hdw1 hdw_a hm1
                hma hdw hwW hinv htmk hlen
              c0_hsteps_nogrp
              refine wp_loop_inv (ts := [i64, i64, i32])
                (fun (tl_p, rem_p, pass_l, ()) mp =>
                  pass_l.toNat ≤ 8 ∧
                  ∃ s_p : FullState, FullDenseInvW c F0 F_cur s_p ∧
                    s_p.core.cur_vars = s1.core.cur_vars ∧
                    s_p.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                    M6TmkZero s_p ∧ (FullMem c s_p ⋆ R) mp)
                (fun (_, _, pass_l, ()) _ => 8 - pass_l.toNat)
                (fun _ hJ_p => by
                  c0_hsteps!
                  exact hJ_p (tl_c, budget, 0#32, ()) mb
                    ⟨by decide, s_b, hdw_b, hcv_b, by rw [hfl_b]; exact Nat.le_refl _,
                      htmk_b, hmb⟩)
                (fun _ (tl_p, rem_p, pass_l, ()) mp
                    ⟨hpass_le, s_p, hdw_p, hcv_p, hfl_p, htmk_p, hm_p⟩ hJ_p => by
                  have h_ex_st :
                      ∃ s_e : FullState, FullDenseInvW c F0 F_cur s_e ∧
                        s_e.core.cur_vars = s1.core.cur_vars ∧
                        s_e.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                        M6TmkZero s_e ∧ (FullMem c s_e ⋆ R) mp :=
                    ⟨s_p, hdw_p, hcv_p, hfl_p, htmk_p, hm_p⟩
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ_p_ex (tl_p, rem_p, pass_l, ()) mp h_ex_st
                  have hpass_lt : pass_l.toNat < 8 := hc
                  have hpass1 : (pass_l + 1#32).toNat = pass_l.toNat + 1 :=
                    fid_bv32_add1_lt hpass_lt (by decide)
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ_p_ex (tl_p, rem_p, pass_l, ()) mp h_ex_st
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ_p_ex (tl_p, rem_p, pass_l, ()) mp h_ex_st
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ_p_ex (tl_p, rem_p, pass_l, ()) mp h_ex_st
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ_p_ex (tl_p, rem_p, pass_l, ()) mp h_ex_st
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ_p_ex (tl_p, rem_p, pass_l, ()) mp h_ex_st
                  refine fid_call_collect_cands hCol hdw_p.1 hm_p
                    (fun nc trc_c ws2_c m_c hlen_c hnc_c hbd_c hm_c => ?_)
                  let s_c : FullState :=
                    { s_p with scratch := { s_p.scratch with
                        tarjan_reach := trc_c, work_stk2 := ws2_c } }
                  have hdw_c : FullDenseInvW c F0 F_cur s_c :=
                    fid_denseInvW_set_trc_ws2 hdw_p hlen_c.scratch_ok.tarjan_reach_len
                      hlen_c.scratch_ok.work_stk2_len
                  have hcv_c : s_c.core.cur_vars = s1.core.cur_vars := hcv_p
                  have hfl_c : s_c.core.fuel.toNat ≤ s1.core.fuel.toNat := hfl_p
                  have htmk_c : M6TmkZero s_c := fid_tmkZero_congr htmk_p rfl rfl
                  have hnc_cv1 : nc.toNat ≤ s1.core.cur_vars := hcv_p ▸ hnc_c
                  c0_hsteps_nogrp
                  c0_hsplit
                  · c0_hsteps!
                    exact hJ_p_ex (tl_p, rem_p, pass_l, ()) m_c
                      ⟨s_c, hdw_c, hcv_c, hfl_c, htmk_c, hm_c⟩
                  · c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64, i64, i32, i32])
                      (fun (_tl_e, _rem_e, _ci_e, _isz_e, ()) me =>
                        ∃ s_e : FullState, FullDenseInvW c F0 F_cur s_e ∧
                          s_e.core.cur_vars = s1.core.cur_vars ∧
                          s_e.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                          M6TmkZero s_e ∧ (FullMem c s_e ⋆ R) me)
                      (fun _ (_tl_e, _rem_e, _ci_e, _isz_e, ()) me
                          ⟨s_e, hdw_e, hcv_e, hfl_e, htmk_e, hm_e⟩ => by
                        c0_hsteps!
                        exact hJ_p (_, _, pass_l + 1#32, ()) me
                          (by dsimp only; rw [hpass1]; exact fid_sub_add1_lt hpass_lt)
                          ⟨by rw [hpass1]; exact hpass_lt, s_e, hdw_e, hcv_e, hfl_e, htmk_e, hm_e⟩)
                      (fun _ hJ_ex => by
                        refine wp_loop_inv (ts := [i64, i64, i32, i32])
                          (fun (tl_l, rem_l, ci_l, isz_l, ()) ml =>
                            ci_l.toNat ≤ nc.toNat ∧ isz_l.toNat ≤ s1.core.cur_vars ∧
                            ∃ s_l : FullState, FullDenseInvW c F0 F_cur s_l ∧
                              s_l.core.cur_vars = s1.core.cur_vars ∧
                              s_l.core.fuel.toNat ≤ s1.core.fuel.toNat ∧ M6TmkZero s_l ∧
                              (∀ i < nc.toNat,
                                (s_l.scratch.tarjan_reach[i]?.getD 0#32).toNat <
                                  s1.core.cur_vars) ∧
                              (∀ j < isz_l.toNat,
                                (s_l.scratch.tarjan_reach[s1.core.cur_vars + j]?.getD
                                  0#32).toNat < s1.core.cur_vars) ∧
                              (FullMem c s_l ⋆ R) ml)
                          (fun (_, rem_l, ci_l, isz_l, ()) _ =>
                            (nc.toNat - ci_l.toNat + isz_l.toNat) +
                            (2 * s1.core.cur_vars + 1) * rem_l.toNat)
                          (fun _ hJ_in => by
                            c0_hsteps!
                            refine hJ_in (tl_p, rem_p, 0#32, 0#32, ()) m_c
                              ⟨Nat.zero_le _, Nat.zero_le _, s_c, hdw_c, hcv_c, hfl_c, htmk_c, ?_,
                                fun _ hj => absurd (by simp at hj) False.elim, hm_c⟩
                            intro i hi; exact hcv_p ▸ hbd_c i hi)
                          (fun _ (tl_l, rem_l, ci_l, isz_l, ()) ml
                              ⟨hci_le, hisz_le, s_l, hdw_l, hcv_l, hfl_l, htmk_l,
                                hbd_cands, hbd_istk, hm_l⟩ hJ_in => by
                            have hcv_all_l : s_l.core.cur_vars = s.core.cur_vars :=
                              hcv_l.trans hcv1
                            have hfl_all_l : s_l.core.fuel.toNat ≤ s.core.fuel.toNat := by
                              rw [hfuel1] at hfl_l; exact hfl_l
                            have h_in_ex : ∃ s_e : FullState, FullDenseInvW c F0 F_cur s_e ∧
                                s_e.core.cur_vars = s1.core.cur_vars ∧
                                s_e.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                                M6TmkZero s_e ∧ (FullMem c s_e ⋆ R) ml :=
                              ⟨s_l, hdw_l, hcv_l, hfl_l, htmk_l, hm_l⟩
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ_ex (tl_l, rem_l, ci_l, isz_l, ()) ml h_in_ex
                            have hrem_pos : 0 < rem_l.toNat := hc
                            have hrem1 : (rem_l - 1#64).toNat = rem_l.toNat - 1 :=
                              fid_bv64_sub1_toNat hrem_pos
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ_ex (tl_l, rem_l, ci_l, isz_l, ()) ml h_in_ex
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ_ex (tl_l, rem_l, ci_l, isz_l, ()) ml h_in_ex
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ_ex (tl_l, rem_l, ci_l, isz_l, ()) ml h_in_ex
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ_ex (tl_l, rem_l, ci_l, isz_l, ()) ml h_in_ex
                            refine wp_join_group (ts := [i32, i32, i32])
                              (fun (ci_p, isz_p, v_p, ()) m_p =>
                                v_p.toNat < s1.core.cur_vars ∧
                                ci_p.toNat ≤ nc.toNat ∧ isz_p.toNat ≤ s1.core.cur_vars ∧
                                isz_p.toNat ≤ isz_l.toNat ∧
                                nc.toNat - ci_p.toNat + isz_p.toNat <
                                  nc.toNat - ci_l.toNat + isz_l.toNat ∧
                                ∃ gu_p : List (BitVec 32), gu_p.length = 64 ∧
                                  (FullMem c { s_l with scratch :=
                                    { s_l.scratch with glue_used := gu_p } } ⋆ R) m_p)
                              (fun _ (ci_p, isz_p, v_p, ()) m_p
                                  ⟨hv_lt, hci_p, hisz_p, hisz_p_le, hmeas_p, gu_p, hgu_p, hm_p⟩ =>
                                by
                                let s_p1 : FullState :=
                                  { s_l with scratch := { s_l.scratch with glue_used := gu_p } }
                                have hdw_p1 : FullDenseInvW c F0 F_cur s_p1 :=
                                  fid_denseInvW_set_gu hdw_l hgu_p
                                have htmk_p1 : M6TmkZero s_p1 := fid_tmkZero_congr htmk_l rfl rfl
                                have hlen_p1 := hdw_p1.1
                                have hv_fl : v_p.toNat < s_p1.core.flags.length := by
                                  exact fid_rv32_fl_lt hv_lt hcv1_lt hcv1_le
                                    hlen_p1.core_ok.flags_len
                                have hv_vals : (BitVec.setWidth 64 (v_p <<< (1 : Nat))).toNat <
                                    s_p1.core.vals.length := by
                                  exact fid_u32_shl1_vals_lt hv_lt hcv1_lt hcv1_le
                                    hlen_p1.core_ok.vals_len
                                refine wp_join_group (ts := [i64, i64, i32])
                                  (fun (_tl_n, rem_n, isz_n, ()) mn =>
                                    (rem_n.toNat < rem_l.toNat ∨
                                      (rem_n = rem_l ∧
                                        nc.toNat - ci_p.toNat + isz_n.toNat <
                                          nc.toNat - ci_l.toNat + isz_l.toNat)) ∧
                                    isz_n.toNat ≤ s1.core.cur_vars ∧
                                    ∃ s_n : FullState, FullDenseInvW c F0 F_cur s_n ∧
                                      s_n.core.cur_vars = s1.core.cur_vars ∧
                                      s_n.core.fuel.toNat ≤ s1.core.fuel.toNat ∧ M6TmkZero s_n ∧
                                      (∀ i < nc.toNat,
                                        (s_n.scratch.tarjan_reach[i]?.getD 0#32).toNat <
                                          s1.core.cur_vars) ∧
                                      (∀ j < isz_n.toNat,
                                        (s_n.scratch.tarjan_reach[s1.core.cur_vars + j]?.getD
                                          0#32).toNat < s1.core.cur_vars) ∧
                                      (FullMem c s_n ⋆ R) mn)
                                  (fun _ (tl_n, rem_n, isz_n, ()) mn
                                      ⟨hrem_ord, hisz_n, s_n, hdw_n, hcv_n,
                                      hfl_n, htmk_n, hbd_cn, hbd_in, hm_n⟩ => by
                                    c0_hsteps!
                                    refine hJ_in (tl_n, rem_n, ci_p, isz_n, ()) mn ?_
                                      ⟨hci_p, hisz_n, s_n, hdw_n, hcv_n, hfl_n, htmk_n, hbd_cn,
                                        hbd_in, hm_n⟩
                                    dsimp only
                                    rcases hrem_ord with hlt | ⟨rfl, hlt⟩
                                    · have hnc_ci : nc.toNat - ci_p.toNat ≤ s1.core.cur_vars :=
                                        Nat.le_trans (Nat.sub_le _ _) hnc_cv1
                                      have h2 : nc.toNat - ci_p.toNat + isz_n.toNat <
                                          2 * s1.core.cur_vars + 1 := by
                                        rw [Nat.two_mul]
                                        exact Nat.lt_succ_of_le (Nat.add_le_add hnc_ci hisz_n)
                                      have hmul :
                                          (2 * s1.core.cur_vars + 1) * (rem_n.toNat + 1) ≤
                                            (2 * s1.core.cur_vars + 1) * rem_l.toNat :=
                                        Nat.mul_le_mul_left _ hlt
                                      rw [Nat.mul_succ, Nat.add_comm] at hmul
                                      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right h2 _)
                                        (Nat.le_trans hmul (Nat.le_add_left _ _))
                                    · exact Nat.add_lt_add_right hlt _)
                                  (fun _ hJ_lp => by
                                    have h_skip :
                                        (rem_l.toNat < rem_l.toNat ∨
                                          (rem_l = rem_l ∧
                                            nc.toNat - ci_p.toNat + isz_p.toNat <
                                              nc.toNat - ci_l.toNat + isz_l.toNat)) ∧
                                        isz_p.toNat ≤ s1.core.cur_vars ∧
                                        ∃ s_n : FullState, FullDenseInvW c F0 F_cur s_n ∧
                                          s_n.core.cur_vars = s1.core.cur_vars ∧
                                          s_n.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                                          M6TmkZero s_n ∧
                                          (∀ i < nc.toNat,
                                            (s_n.scratch.tarjan_reach[i]?.getD 0#32).toNat <
                                              s1.core.cur_vars) ∧
                                          (∀ j < isz_p.toNat,
                                            (s_n.scratch.tarjan_reach[s1.core.cur_vars + j]?.getD
                                              0#32).toNat < s1.core.cur_vars) ∧
                                          (FullMem c s_n ⋆ R) m_p :=
                                      ⟨Or.inr ⟨rfl, hmeas_p⟩, hisz_p, s_p1, hdw_p1, hcv_l, hfl_l,
                                        htmk_p1, hbd_cands,
                                        fun j hj =>
                                          hbd_istk j (Nat.lt_of_lt_of_le hj hisz_p_le),
                                        hm_p⟩
                                    c0_hsplit; rotate_left
                                    · c0_hsteps!; exact hJ_lp (tl_l, rem_l, isz_p, ()) m_p h_skip
                                    c0_hsplit; rotate_left
                                    · c0_hsteps!; exact hJ_lp (tl_l, rem_l, isz_p, ()) m_p h_skip
                                    c0_hsteps_nogrp
                                    refine fid_call_sweep_var_fl_gu hSV (by assumption) hdw_l
                                      (by rw [List.length_set, hdw_l.1.core_ok.flags_len]) hgu_p
                                      hcap_ge (hcv_l ▸ hv_lt) htmk_l
                                      (fun r3 s3 m3 hdw3 hcv3 hfl3 htmk3 htrc3 _hr3 hunsat3
                                        hm3 => ?_)
                                    c0_hsplit
                                    · c0_hsteps!
                                      exact hQ 20#64 s3 m3 (fid_denseInv_of_W hdw3)
                                        (hcv3.trans hcv_all_l) (Nat.le_trans hfl3 hfl_all_l) htmk3
                                        (Or.inr rfl) (fun _ => hunsat3 hc) hm3
                                    · have htrc3_eq : s3.scratch.tarjan_reach =
                                          s_l.scratch.tarjan_reach := htrc3
                                      refine wp_join_group (ts := [])
                                        (fun () md => ∃ s_d : FullState,
                                          FullDenseInvW c F0 F_cur s_d ∧
                                          s_d.core.cur_vars = s1.core.cur_vars ∧
                                          s_d.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                                          M6TmkZero s_d ∧
                                          s_d.scratch.tarjan_reach = s_l.scratch.tarjan_reach ∧
                                          (FullMem c s_d ⋆ R) md)
                                        (fun _ () md ⟨s_d, hdw_d, hcv_d, hfl_d, htmk_d,
                                            htrc_d, hm_d⟩ => by
                                          have hscr_d : s_d.scratch.scratch_buf.length =
                                              c.scratch_cap := hdw_d.1.scratch_ok.scratch_buf_len
                                          have hk11_sd : (BitVec.setWidth 64
                                              (BitVec.ofNat 32 (L.k6Base + 11))).toNat <
                                              s_d.scratch.scratch_buf.length := hscr_d ▸ hk11_idx
                                          c0_hsteps_nogrp
                                          try rw [hk11_ptr]
                                          c0_hsteps_nogrp
                                          refine wp_join_group (ts := [i64])
                                            (fun (_tl_n, ()) mj' => mj' = md)
                                            (fun _ (tl_n, ()) mj' hmj' => by
                                              subst mj'
                                              c0_hsteps_nogrp
                                              refine wp_join_group (ts := [i32])
                                                (fun (isz_f, ()) mf =>
                                                  isz_f.toNat ≤ s1.core.cur_vars ∧
                                                  ∃ s_f : FullState, FullDenseInvW c F0 F_cur s_f ∧
                                                    s_f.core.cur_vars = s1.core.cur_vars ∧
                                                    s_f.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                                                    M6TmkZero s_f ∧
                                                    (∀ i < nc.toNat,
                                                      (s_f.scratch.tarjan_reach[i]?.getD 0#32).toNat
                                                        < s1.core.cur_vars) ∧
                                                    (∀ j < isz_f.toNat,
                                                      (s_f.scratch.tarjan_reach[
                                                        s1.core.cur_vars + j]?.getD 0#32).toNat <
                                                        s1.core.cur_vars) ∧
                                                    (FullMem c s_f ⋆ R) mf)
                                                (fun _ (isz_f, ()) mf hmf => by
                                                  c0_hsteps!
                                                  refine hJ_lp (tl_n, rem_l - 1#64, isz_f, ()) mf
                                                    ⟨Or.inl ?_, hmf⟩
                                                  rw [hrem1]
                                                  exact Nat.sub_lt hrem_pos Nat.zero_lt_one) ?_
                                              · intro _ hJ_sub
                                                c0_hsplit; rotate_left
                                                · c0_hsteps!
                                                  exact hJ_sub (isz_p, ()) md
                                                    ⟨hisz_p, s_d, hdw_d, hcv_d, hfl_d, htmk_d,
                                                      fun i hi => htrc_d ▸ hbd_cands i hi,
                                                      fun j hj => htrc_d ▸ hbd_istk j
                                                        (Nat.lt_of_lt_of_le hj hisz_p_le),
                                                      hm_d⟩
                                                · have hk24_sd : (BitVec.setWidth 64
                                                      (BitVec.ofNat 32 (L.k6Base + 24))).toNat <
                                                      s_d.scratch.scratch_buf.length :=
                                                    hscr_d ▸ hk24_idx
                                                  c0_hsteps_nogrp
                                                  try rw [hk24_ptr]
                                                  c0_hsteps_nogrp
                                                  refine wp_loop_inv (ts := [i32, i32])
                                                    (fun (isz_e, ei_l, ()) me =>
                                                      ei_l.toNat ≤ s1.core.cur_vars ∧
                                                      isz_e.toNat ≤ s1.core.cur_vars ∧
                                                      ∃ s_e' : FullState,
                                                        FullDenseInvW c F0 F_cur s_e' ∧
                                                        s_e'.core.cur_vars = s1.core.cur_vars ∧
                                                        s_e'.core.fuel.toNat ≤ s1.core.fuel.toNat ∧
                                                        M6TmkZero s_e' ∧
                                                        (∀ i < nc.toNat,
                                                          (s_e'.scratch.tarjan_reach[i]?.getD
                                                            0#32).toNat < s1.core.cur_vars) ∧
                                                        (∀ j < isz_e.toNat,
                                                          (s_e'.scratch.tarjan_reach[
                                                            s1.core.cur_vars + j]?.getD
                                                            0#32).toNat <
                                                            s1.core.cur_vars) ∧
                                                        (FullMem c s_e' ⋆ R) me)
                                                    (fun (_, ei_l, ()) _ =>
                                                      s1.core.cur_vars - ei_l.toNat)
                                                    (fun _ hJ_ei => by
                                                      c0_hsteps!
                                                      exact hJ_ei (isz_p, 0#32, ()) md
                                                        ⟨Nat.zero_le _, hisz_p, s_d, hdw_d, hcv_d,
                                                          hfl_d, htmk_d,
                                                          fun i hi => htrc_d ▸ hbd_cands i hi,
                                                          fun j hj => htrc_d ▸ hbd_istk j
                                                            (Nat.lt_of_lt_of_le hj hisz_p_le),
                                                          hm_d⟩)
                                                    (fun _ (isz_e, ei_l, ()) me
                                                        ⟨hei_le, hisz_e, s_e', hdw_e', hcv_e',
                                                          hfl_e', htmk_e', hbd_ce, hbd_ie, hm_e'⟩
                                                        hJ_ei => by
                                                      have h_ei_ex :
                                                          isz_e.toNat ≤ s1.core.cur_vars ∧
                                                          ∃ s_f : FullState,
                                                            FullDenseInvW c F0 F_cur s_f ∧
                                                            s_f.core.cur_vars = s1.core.cur_vars ∧
                                                            s_f.core.fuel.toNat ≤
                                                              s1.core.fuel.toNat ∧
                                                            M6TmkZero s_f ∧
                                                            (∀ i < nc.toNat,
                                                              (s_f.scratch.tarjan_reach[i]?.getD
                                                                0#32).toNat < s1.core.cur_vars) ∧
                                                            (∀ j < isz_e.toNat,
                                                              (s_f.scratch.tarjan_reach[
                                                                s1.core.cur_vars + j]?.getD
                                                                0#32).toNat < s1.core.cur_vars) ∧
                                                            (FullMem c s_f ⋆ R) me :=
                                                        ⟨hisz_e, s_e', hdw_e', hcv_e', hfl_e',
                                                          htmk_e', hbd_ce, hbd_ie, hm_e'⟩
                                                      c0_hsplit; rotate_left
                                                      · c0_hsteps!
                                                        exact hJ_sub (isz_e, ()) me h_ei_ex
                                                      c0_hsplit; rotate_left
                                                      · c0_hsteps!
                                                        exact hJ_sub (isz_e, ()) me h_ei_ex
                                                      have hei_lt :
                                                          ei_l.toNat < s1.core.cur_vars := by
                                                        have h1 : ei_l.toNat <
                                                            s1.core.cur_vars % 2 ^ 64 := hc
                                                        rwa [Nat.mod_eq_of_lt hcv1_2p64] at h1
                                                      have hei1 : (ei_l + 1#32).toNat =
                                                          ei_l.toNat + 1 :=
                                                        fid_bv32_add1_lt hei_lt hcv1_lt
                                                      have heqb_bd :=
                                                        (fid_u32_shl1_idx c hcv1_le hei_lt).2
                                                      have hws2_bd :
                                                          (BitVec.setWidth 64
                                                            (ei_l <<< (1 : BitVec 32))).toNat <
                                                            s_e'.scratch.work_stk2.length := by
                                                        rw [hdw_e'.1.scratch_ok.work_stk2_len]
                                                        exact heqb_bd
                                                      c0_hsteps_nogrp
                                                      refine wp_join_group (ts := [i32])
                                                        (fun (isz_l', ()) ml' =>
                                                          isz_l'.toNat ≤ s1.core.cur_vars ∧
                                                          ∃ s_n : FullState,
                                                            FullDenseInvW c F0 F_cur s_n ∧
                                                            s_n.core.cur_vars = s1.core.cur_vars ∧
                                                            s_n.core.fuel.toNat ≤
                                                              s1.core.fuel.toNat ∧
                                                            M6TmkZero s_n ∧
                                                            (∀ i < nc.toNat,
                                                              (s_n.scratch.tarjan_reach[i]?.getD
                                                                0#32).toNat < s1.core.cur_vars) ∧
                                                            (∀ j < isz_l'.toNat,
                                                              (s_n.scratch.tarjan_reach[
                                                                s1.core.cur_vars + j]?.getD
                                                                0#32).toNat < s1.core.cur_vars) ∧
                                                            (FullMem c s_n ⋆ R) ml') ?_ ?_
                                                      ·
                                                          rintro _ ⟨isz_l', ⟨⟩⟩ ml' hml'
                                                          c0_hsteps!
                                                          exact hJ_ei (isz_l', ei_l + 1#32, ()) ml'
                                                            (by dsimp only; rw [hei1]
                                                                exact fid_sub_add1_lt hei_lt)
                                                            ⟨by rw [hei1]; exact hei_lt, hml'⟩
                                                      ·
                                                          intro _ hJ_lit
                                                          c0_hsplit; rotate_left
                                                          · c0_hsteps!
                                                            exact hJ_lit (isz_e, ()) me h_ei_ex
                                                          have hlit_lt :
                                                              (s_e'.scratch.work_stk2[
                                                                (BitVec.setWidth 64
                                                                  (ei_l <<<
                                                                    (1 : BitVec 32))).toNat]'
                                                                hws2_bd).toNat <
                                                                2 * s1.core.cur_vars := by
                                                            have h1 :
                                                                (s_e'.scratch.work_stk2[
                                                                  (ei_l <<<
                                                                    (1 : BitVec 32)).toNat]'
                                                                  (fid_u32_setWidth_toNat _ ▸
                                                                    hws2_bd)).toNat <
                                                                2 * (s1.core.cur_vars % 2 ^ 64) %
                                                                  2 ^ 64 := hc
                                                            rw [Nat.mod_eq_of_lt hcv1_2p64,
                                                              Nat.mod_eq_of_lt
                                                                (fid_two_mul_lt hcv1_lt)] at h1
                                                            simpa only [fid_u32_setWidth_toNat]
                                                              using h1
                                                          have hlit_rp :
                                                              (BitVec.setWidth 64
                                                                (s_e'.scratch.work_stk2[
                                                                  (BitVec.setWidth 64
                                                                    (ei_l <<<
                                                                      (1 : BitVec 32))).toNat]'
                                                                  hws2_bd)).toNat <
                                                                s_e'.core.repr.length := by
                                                            exact fid_lit32_repr_lt hlit_lt
                                                              hcv1_lt hcv1_le
                                                              hdw_e'.1.core_ok.repr_len
                                                          c0_hsteps_nogrp
                                                          refine wp_join_group (ts := [i32])
                                                            (fun (isz_r', ()) mr' =>
                                                              isz_r'.toNat ≤ s1.core.cur_vars ∧
                                                              ∃ s_n : FullState,
                                                                FullDenseInvW c F0 F_cur s_n ∧
                                                                s_n.core.cur_vars =
                                                                  s1.core.cur_vars ∧
                                                                s_n.core.fuel.toNat ≤
                                                                  s1.core.fuel.toNat ∧
                                                                M6TmkZero s_n ∧
                                                                (∀ i < nc.toNat,
                                                                  (s_n.scratch.tarjan_reach[i]?.getD
                                                                    0#32).toNat <
                                                                    s1.core.cur_vars) ∧
                                                                (∀ j < isz_r'.toNat,
                                                                  (s_n.scratch.tarjan_reach[
                                                                    s1.core.cur_vars + j]?.getD
                                                                    0#32).toNat <
                                                                    s1.core.cur_vars) ∧
                                                                (FullMem c s_n ⋆ R) mr') ?_ ?_
                                                          ·
                                                              rintro _ ⟨isz_r', ⟨⟩⟩ mr' hmr'
                                                              c0_hsteps!
                                                              exact hJ_lit (isz_r', ()) mr' hmr'
                                                          ·
                                                              intro _ hJ_rv
                                                              c0_hsplit; rotate_left
                                                              · c0_hsteps!
                                                                exact hJ_rv (isz_e, ()) me h_ei_ex
                                                              have hrv_lt' :
                                                                  ((s_e'.core.repr[
                                                                    (BitVec.setWidth 64
                                                                      (s_e'.scratch.work_stk2[
                                                                        (BitVec.setWidth 64
                                                                          (ei_l <<<
                                                                            1#32)).toNat]'
                                                                        hws2_bd)).toNat]'
                                                                      hlit_rp) >>>
                                                                    (1 : BitVec 32)).toNat <
                                                                    s1.core.cur_vars := by
                                                                have h1 :
                                                                    ((s_e'.core.repr[
                                                                      (BitVec.setWidth 64
                                                                        (s_e'.scratch.work_stk2[
                                                                          (BitVec.setWidth 64
                                                                            (ei_l <<< 1#32)).toNat]'
                                                                          hws2_bd)).toNat]'
                                                                      hlit_rp) >>>
                                                                      (1 : BitVec 32)).toNat <
                                                                    s1.core.cur_vars % 2 ^ 64 := hc
                                                                rwa [Nat.mod_eq_of_lt
                                                                  hcv1_2p64] at h1
                                                              have hrv_fl' :
                                                                  (BitVec.setWidth 64
                                                                    ((s_e'.core.repr[
                                                                      (BitVec.setWidth 64
                                                                        (s_e'.scratch.work_stk2[
                                                                          (BitVec.setWidth 64
                                                                            (ei_l <<< 1#32)).toNat]'
                                                                          hws2_bd)).toNat]'
                                                                      hlit_rp) >>>
                                                                      (1 : BitVec 32))).toNat <
                                                                    s_e'.core.flags.length := by
                                                                exact fid_rv32_fl_lt hrv_lt'
                                                                  hcv1_lt hcv1_le
                                                                  hdw_e'.1.core_ok.flags_len
                                                              have hrv_vals' :
                                                                  (BitVec.setWidth 64
                                                                    (((s_e'.core.repr[
                                                                      (BitVec.setWidth 64
                                                                        (s_e'.scratch.work_stk2[
                                                                          (BitVec.setWidth 64
                                                                            (ei_l <<< 1#32)).toNat]'
                                                                          hws2_bd)).toNat]'
                                                                      hlit_rp) >>>
                                                                      (1 : BitVec 32)) <<<
                                                                      (1 : Nat))).toNat <
                                                                    s_e'.core.vals.length := by
                                                                exact fid_u32_shl1_vals_lt
                                                                  hrv_lt' hcv1_lt hcv1_le
                                                                  hdw_e'.1.core_ok.vals_len
                                                              c0_hsplit; rotate_left
                                                              · c0_hsteps!
                                                                exact hJ_rv (isz_e, ()) me h_ei_ex
                                                              c0_hsplit; rotate_left
                                                              · c0_hsteps!
                                                                exact hJ_rv (isz_e, ()) me h_ei_ex
                                                              c0_hsteps_nogrp
                                                              refine wp_join_group (ts := [i32])
                                                                (fun (isz_k, ()) mk =>
                                                                  isz_k.toNat ≤ s1.core.cur_vars ∧
                                                                  ∃ trc_k : List (BitVec 32),
                                                                    trc_k.length = 2 * c.max_vars ∧
                                                                    (∀ i < nc.toNat,
                                                                      (trc_k[i]?.getD 0#32).toNat <
                                                                        s1.core.cur_vars) ∧
                                                                    (∀ j < isz_k.toNat,
                                                                      (trc_k[s1.core.cur_vars +
                                                                        j]?.getD 0#32).toNat <
                                                                        s1.core.cur_vars) ∧
                                                                    (FullMem c
                                                                      { s_e' with scratch :=
                                                                        { s_e'.scratch with
                                                                          tarjan_reach :=
                                                                            trc_k } } ⋆ R)
                                                                      mk) ?_ ?_
                                                              ·
                                                                  rintro _ ⟨isz_k, ⟨⟩⟩ mk
                                                                    ⟨hisz_k, trc_k,
                                                                    htrc_k, hbd_ck, hbd_ik, hm_k⟩

                                                                  let s_k : FullState :=
                                                                    { s_e' with scratch :=
                                                                      { s_e'.scratch with
                                                                        tarjan_reach := trc_k } }
                                                                  have hdw_k :=
                                                                    fid_denseInvW_set_trc hdw_e'
                                                                      htrc_k
                                                                  have hrv_fl_k :
                                                                      (BitVec.setWidth 64
                                                                        ((s_e'.core.repr[
                                                                          (BitVec.setWidth 64
                                                                            (s_e'.scratch.work_stk2[
                                                                              (BitVec.setWidth 64
                                                                                (ei_l <<<
                                                                                  1#32)).toNat]'
                                                                              hws2_bd)).toNat]'
                                                                          hlit_rp) >>>
                                                                          (1 : BitVec 32))).toNat <
                                                                        s_k.core.flags.length :=
                                                                    hrv_fl'
                                                                  c0_hsteps_nogrp
                                                                  c0_hsteps!
                                                                  have hfl_n :
                                                                      ∃ fl_n : List (BitVec 32),
                                                                        fl_n.length = c.max_vars ∧
                                                                        (FullMem c
                                                                          { s_k with core :=
                                                                            { s_k.core with
                                                                              flags := fl_n }
                                                                          } ⋆ R)
                                                                          m := by
                                                                    refine ⟨_, ?_, hm⟩
                                                                    dsimp only [s_k]
                                                                    rw [List.length_set]
                                                                    exact hdw_e'.1.core_ok.flags_len
                                                                  obtain
                                                                    ⟨fl_n, hfl_len_n, hm_n⟩ :=
                                                                    hfl_n
                                                                  exact hJ_rv (isz_k, ()) _
                                                                    ⟨hisz_k, _,
                                                                      fid_denseInvW_set_flags hdw_k
                                                                        hfl_len_n,
                                                                      hcv_e', hfl_e',
                                                                      fid_tmkZero_congr htmk_e'
                                                                        rfl rfl,
                                                                      hbd_ck, hbd_ik,
                                                                      hm_n⟩
                                                              ·
                                                                intro _ hJ_push
                                                                have htrc_len_e' :=
                                                                  hdw_e'.1.scratch_ok
                                                                    |>.tarjan_reach_len
                                                                have h_nopush :
                                                                    isz_e.toNat ≤ s1.core.cur_vars ∧
                                                                    ∃ trc_k : List (BitVec 32),
                                                                      trc_k.length =
                                                                        2 * c.max_vars ∧
                                                                      (∀ i < nc.toNat,
                                                                        (trc_k[i]?.getD 0#32).toNat
                                                                          < s1.core.cur_vars) ∧
                                                                      (∀ j < isz_e.toNat,
                                                                        (trc_k[s1.core.cur_vars
                                                                            + j]?.getD 0#32).toNat
                                                                          < s1.core.cur_vars) ∧
                                                                      (FullMem c
                                                                        { s_e' with scratch :=
                                                                          { s_e'.scratch with
                                                                            tarjan_reach :=
                                                                              trc_k } } ⋆ R)
                                                                        me :=
                                                                  ⟨hisz_e,
                                                                    s_e'.scratch.tarjan_reach,
                                                                    htrc_len_e', hbd_ce, hbd_ie,
                                                                    hm_e'⟩
                                                                c0_hsplit; rotate_left
                                                                · c0_hsteps!
                                                                  exact hJ_push
                                                                    (isz_e, ()) me h_nopush
                                                                c0_hsplit; rotate_left
                                                                · c0_hsteps!
                                                                  exact hJ_push
                                                                    (isz_e, ()) me h_nopush
                                                                have hisz_lt : isz_e.toNat <
                                                                    s1.core.cur_vars := by
                                                                  have h1 : isz_e.toNat <
                                                                      s1.core.cur_vars %
                                                                        2 ^ 64 := hc
                                                                  rwa [Nat.mod_eq_of_lt
                                                                    hcv1_2p64] at h1
                                                                have hisz1 :
                                                                    (isz_e + 1#32).toNat =
                                                                      isz_e.toNat + 1 :=
                                                                  fid_bv32_add1_lt hisz_lt hcv1_lt
                                                                have hpush_idx :
                                                                    (BitVec.ofNat 64
                                                                        s1.core.cur_vars +
                                                                      isz_e.setWidth 64).toNat =
                                                                      s1.core.cur_vars +
                                                                        isz_e.toNat :=
                                                                  fid_cv_add_u32_toNat hcv1_lt
                                                                    (Nat.le_of_lt hisz_lt)
                                                                have htrc_push' :
                                                                    (BitVec.ofNat 64
                                                                        s1.core.cur_vars +
                                                                      isz_e.setWidth 64).toNat <
                                                                      (s_e'.scratch
                                                                        |>.tarjan_reach).length :=
                                                                  fid_trc_push_lt hpush_idx
                                                                    htrc_len_e' hcv1_le hisz_lt
                                                                have htrc_push :
                                                                    s1.core.cur_vars +
                                                                        isz_e.toNat <
                                                                      (s_e'.scratch
                                                                        |>.tarjan_reach).length :=
                                                                  hpush_idx ▸ htrc_push'
                                                                c0_hsteps!
                                                                refine hJ_push
                                                                  (isz_e + 1#32, ()) _
                                                                  ⟨by rw [hisz1]; exact hisz_lt,
                                                                    _,
                                                                    by simp only [List.length_set,
                                                                      htrc_len_e'],
                                                                    fid_set_trc_getD_lt hbd_ce
                                                                      (fid_trc_push_nc_ne
                                                                        hpush_idx hnc_cv1),
                                                                    fun j hj => ?_,
                                                                    by assumption⟩
                                                                rw [hisz1] at hj
                                                                rw [hpush_idx]
                                                                by_cases hje : j = isz_e.toNat
                                                                · subst hje
                                                                  rw [List.getElem?_set_self
                                                                      htrc_push,
                                                                    Option.getD_some]
                                                                  exact hrv_lt'
                                                                · have hj_lt :=
                                                                    fid_lt_of_add1_lt_ne hj hje
                                                                  rw [List.getElem?_set_ne
                                                                    (fid_trc_push_prev_ne
                                                                      hj_lt).symm]
                                                                  exact hbd_ie j hj_lt))
                                            (fun _ hJ87 => by
                                              c0_hsplit
                                              · c0_hsteps!; exact hJ87 (_, ()) md rfl
                                              · c0_hsteps!; exact hJ87 (_, ()) md rfl))
                                        (fun _ hJ_dp => by
                                          c0_hsplit
                                          · refine fid_call_dense_prop hDP hdw3 hm3
                                              (fun ok4 s4 m4 hdw4 hcv4 hfl4 htmk4 htrc4 _hok4
                                                hno4 hm4 => ?_)
                                            c0_hsplit
                                            · c0_hsteps_nogrp
                                              exact hJ_dp () m4
                                                ⟨s4, hdw4, hcv4.trans (hcv3.trans hcv_l),
                                                by rw [hfl4]; exact Nat.le_trans hfl3 hfl_l,
                                                fid_tmkZero_congr htmk3 hcv4 htmk4,
                                                htrc4.trans htrc3_eq, hm4⟩
                                            · have hokf : ok4 = false := by
                                                cases ok4 <;> first | rfl | exact hc
                                              c0_hsteps!
                                              exact hQ 20#64 s4 m4
                                                (fid_denseInv_of_W hdw4)
                                                (hcv4.trans (hcv3.trans hcv_all_l))
                                                (by rw [hfl4]; exact Nat.le_trans hfl3 hfl_all_l)
                                                (fid_tmkZero_congr htmk3 hcv4 htmk4) (Or.inr rfl)
                                                (fun _ => (hno4 hokf).1) hm4
                                          · c0_hsteps_nogrp
                                            exact hJ_dp () m3 ⟨s3, hdw3, hcv3.trans hcv_l,
                                              Nat.le_trans hfl3 hfl_l, htmk3, htrc3_eq, hm3⟩)))
                              (fun _ hJ_pop => by
                                c0_hsplit
                                · have hisz_pos : 0 < isz_l.toNat := hc
                                  have hisz1 : (isz_l - 1#32).toNat = isz_l.toNat - 1 :=
                                    fid_bv32_sub1_toNat hisz_pos
                                  have hisz_sub_le : (isz_l - 1#32).toNat ≤ s1.core.cur_vars := by
                                    rw [hisz1]; exact fid_sub1_le hisz_pos hisz_le
                                  have hisz_sub_le_l : (isz_l - 1#32).toNat ≤ isz_l.toNat := by
                                    rw [hisz1]; exact Nat.sub_le _ _
                                  have hisz_sub_lt : (isz_l - 1#32).toNat < isz_l.toNat := by
                                    rw [hisz1]; exact fid_sub1_lt hisz_pos
                                  have hpop_idx := fid_cv_add_u32_toNat hcv1_lt hisz_sub_le
                                  have hpop_idx' :
                                      (BitVec.ofNat 64 s1.core.cur_vars +
                                        (isz_l - 1#32).setWidth 64).toNat =
                                        s1.core.cur_vars + (isz_l.toNat - 1) := by
                                    rw [hpop_idx, hisz1]
                                  have hpop_trc :
                                      (BitVec.ofNat 64 s1.core.cur_vars +
                                        (isz_l - 1#32).setWidth 64).toNat <
                                        s_l.scratch.tarjan_reach.length :=
                                    fid_trc_pop_lt hpop_idx'
                                      hdw_l.1.scratch_ok.tarjan_reach_len hcv1_le hisz_pos hisz_le
                                  c0_hsteps!
                                  have hv_lt_p := hbd_istk (isz_l - 1#32).toNat hisz_sub_lt
                                  rw [← hpop_idx, List.getElem?_eq_getElem hpop_trc,
                                    Option.getD_some] at hv_lt_p
                                  exact hJ_pop (ci_l, isz_l - 1#32, _, ()) ml
                                    ⟨hv_lt_p, hci_le, hisz_sub_le, hisz_sub_le_l,
                                      by rw [hisz1]; exact fid_pop_meas_lt hisz_pos,
                                      s_l.scratch.glue_used, hdw_l.1.scratch_ok.glue_used_len,
                                      hm_l⟩
                                · have hisz0 : isz_l.toNat = 0 := Nat.eq_zero_of_not_pos hc
                                  c0_hsplit; rotate_left
                                  · c0_hsteps!
                                    exact hJ_ex (tl_l, rem_l, ci_l, isz_l, ()) ml
                                      ⟨s_l, hdw_l, hcv_l, hfl_l, htmk_l, hm_l⟩
                                  have hci_lt : ci_l.toNat < nc.toNat := hc
                                  have hci1 : (ci_l + 1#32).toNat = ci_l.toNat + 1 :=
                                    fid_bv32_add1_lt (Nat.lt_of_lt_of_le hci_lt hnc_cv1) hcv1_lt
                                  have hci_trc : (ci_l.setWidth 64).toNat <
                                      s_l.scratch.tarjan_reach.length := by
                                    exact fid_ci_trc_lt hdw_l.1.scratch_ok.tarjan_reach_len
                                      hcv1_lt hcv1_le hnc_cv1 hci_lt
                                  have hv_lt_c :
                                      (s_l.scratch.tarjan_reach[(ci_l.setWidth 64).toNat]'
                                        hci_trc).toNat < s1.core.cur_vars := by
                                    have hci_m : (ci_l.setWidth 64).toNat = ci_l.toNat := by
                                      exact fid_ci_setWidth_eq hcv1_lt hnc_cv1 hci_lt
                                    have h1 := hbd_cands ci_l.toNat hci_lt
                                    rwa [← hci_m, List.getElem?_eq_getElem hci_trc,
                                      Option.getD_some] at h1
                                  obtain ⟨_, _, hgul_30, _, _, hgul_30'⟩ :=
                                    fid_gu_idx_lt hdw_l.1.scratch_ok.glue_used_len
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i32])
                                    (fun (_cur_n, ()) m_cur => m_cur = ml)
                                    ?_ ?_
                                  · rintro _ ⟨cur_n, ⟨⟩⟩ m_cur hmc
                                    subst hmc
                                    c0_hsteps!
                                    refine hJ_pop (ci_l + 1#32, isz_l, _, ()) _
                                      ⟨hv_lt_c, by rw [hci1]; exact hci_lt, hisz_le, Nat.le_refl _,
                                        fid_push_meas_lt hci1 hci_lt, _, ?_, by assumption⟩
                                    simp only [List.length_set, hdw_l.1.scratch_ok.glue_used_len]
                                  · intro _ hJ_cur
                                    c0_hsplit
                                    · c0_hsteps!; exact hJ_cur (_, ()) ml rfl
                                    · c0_hsteps!; exact hJ_cur (_, ()) ml rfl))))
      · intro _ hJt
        c0_hsplit
        · c0_hsteps!; exact hJt (0xFFFFFFFF#64, ()) mb ⟨by decide, rfl⟩
        · have hle : tlim.toNat ≤ 0xFFFFFFFF := Nat.le_of_not_lt hc
          c0_hsteps!; exact hJt (tlim, ()) mb ⟨hle, rfl⟩
    · -- Body of `if (need_mark)`
      intro _ hJb
      c0_hsplit
      · -- `need_mark == true`: mark active unassigned vars, set `gu[29] = 1`, `gu[30] = 0`
        clear hMaxV hCol hDP hSV hQ hgu1_28 hgu1_29 hgu1_30 hgu1_28' hgu1_29' hgu1_30' hdw1 hm1
          comp0 hdw hwW hinv htmk hlen hcap_ge hcap_lt hmx hcv1 hfuel1 htmk1
          _htrc1 hno1
        c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i64])
          (fun (v_l, ()) ml => v_l.toNat ≤ s1.core.cur_vars ∧
            ∃ fl_l : List (BitVec 32), fl_l.length = c.max_vars ∧
              (FullMem c { s_a with core := { s_a.core with flags := fl_l } } ⋆ R) ml)
          (fun (v_l, ()) _ => s1.core.cur_vars - v_l.toNat)
          ?_ ?_
        ·
            intro _ hJ_m
            c0_hsteps!
            exact hJ_m (0#64, ()) ma
              ⟨Nat.zero_le _, s_a.core.flags, hdw_a.1.core_ok.flags_len, hma⟩
        ·
            rintro _ ⟨v_l, ⟨⟩⟩ ml ⟨hv_le, fl_l, hfl_l_len, hml⟩ hJ_m
            c0_hsplit; rotate_left
            · let s_m : FullState := { s_a with core := { s_a.core with flags := fl_l } }
              have hdw_m : FullDenseInvW c F0 F_cur s_m := fid_denseInvW_set_flags hdw_a hfl_l_len
              obtain ⟨_, hgm_29, hgm_30, _, hgm_29', hgm_30'⟩ :=
                fid_gu_idx_lt hdw_m.1.scratch_ok.glue_used_len
              c0_hsteps_nogrp
              have hgu_m1 : (s_m.scratch.glue_used.set (29 : BitVec 64).toNat
                  1#32).length = 64 := by
                simp only [List.length_set, hdw_m.1.scratch_ok.glue_used_len]
              obtain ⟨_, _, hgm1_30, _, _, hgm1_30'⟩ := fid_gu_idx_lt hgu_m1
              c0_hsteps!
              have hgu_m2 : ((s_m.scratch.glue_used.set (29 : BitVec 64).toNat 1#32).set
                  (30 : BitVec 64).toNat 0#32).length = 64 := by
                simp only [List.length_set, hdw_m.1.scratch_ok.glue_used_len]
              exact hJb () _ ⟨_, fid_denseInvW_set_gu hdw_m hgu_m2, hcv_a, hfl_a,
                fid_tmkZero_congr htmk_a rfl rfl, by assumption⟩
            · have hv_lt : v_l.toNat < s1.core.cur_vars := by
                have h1 : v_l.toNat < s1.core.cur_vars % 2 ^ 64 := hc
                rwa [Nat.mod_eq_of_lt hcv1_2p64] at h1
              have hv1 : (v_l + 1#64).toNat = v_l.toNat + 1 := fid_bv64_add1_lt hv_lt hcv1_lt
              have hv_fl : v_l.toNat < fl_l.length := by
                rw [hfl_l_len]; exact Nat.lt_of_lt_of_le hv_lt hcv1_le
              have hv_vals : (v_l <<< (1 : Nat)).toNat < s_a.core.vals.length := by
                exact fid_vals_shl1_lt hv_lt hcv1_lt hcv1_le hdw_a.1.core_ok.vals_len
              have hpos_bd : (((v_l <<< (1 : BitVec 64)) <<< (1 : BitVec 64)) +
                  (1 : BitVec 64)).toNat < s_a.core.wvec.length := by
                exact fid_wvec_pos_lt hv_lt hcv1_lt hcv1_le hdw_a.1.core_ok.wvec_len
              have hneg_bd : ((((v_l <<< (1 : BitVec 64)) ||| (1 : BitVec 64)) <<<
                  (1 : BitVec 64)) + (1 : BitVec 64)).toNat < s_a.core.wvec.length := by
                exact fid_wvec_neg_lt hv_lt hcv1_lt hcv1_le hdw_a.1.core_ok.wvec_len
              refine wp_join_group (ts := [])
                (fun () mv1 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                  (FullMem c { s_a with core := { s_a.core with flags := fl' } } ⋆ R) mv1)
                (fun _ () mv1 ⟨fl', hfl', hmv1⟩ => by
                  c0_hsteps!
                  exact hJ_m (v_l + 1#64, ()) mv1
                    (by dsimp only; rw [hv1]; exact fid_sub_add1_lt hv_lt)
                    ⟨by rw [hv1]; exact hv_lt, fl', hfl', hmv1⟩)
                (fun _ hJ_v1 => by
                  refine wp_join_group (ts := []) (fun () m30 => m30 = ml)
                    (fun _ () m30 hm30 => by
                      subst hm30; c0_hsteps!
                      refine hJ_v1 () _ ⟨_, ?_, by assumption⟩
                      simp only [List.length_set, hfl_l_len])
                    (fun _ hJ30 => by
                      c0_hsplit; rotate_left
                      · c0_hsteps!; exact hJ30 () ml rfl
                      c0_hsplit; rotate_left
                      · c0_hsteps!; exact hJ30 () ml rfl
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [])
                        (fun () m36 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                          (FullMem c { s_a with core := { s_a.core with flags := fl' } } ⋆ R) m36)
                        (fun _ () m36 h => by c0_hsteps!; exact hJ_v1 () m36 h)
                        (fun _ hJ36 => by
                          refine wp_join_group (ts := []) (fun () m38 => m38 = ml)
                            (fun _ () m38 hm38 => by
                              subst hm38; c0_hsteps!
                              refine hJ36 () _ ⟨_, ?_, by assumption⟩
                              simp only [List.length_set, hfl_l_len])
                            (fun _ hJ38 => by
                              c0_hsplit; rotate_left
                              · c0_hsteps!; exact hJ38 () ml rfl
                              c0_hsplit; rotate_left
                              · c0_hsteps!; exact hJ38 () ml rfl
                              c0_hsplit; rotate_left
                              · c0_hsteps!; exact hJ38 () ml rfl
                              c0_hsplit; rotate_left
                              · c0_hsteps!; exact hJ38 () ml rfl
                              c0_hsteps!
                              refine hJ36 () _ ⟨_, ?_, by assumption⟩
                              simp only [List.length_set, hfl_l_len]))))
      · c0_hsteps!; exact hJb () ma ⟨s_a, hdw_a, hcv_a, hfl_a, htmk_a, hma⟩
  · -- Body of `if (!need_mark)`
    intro _ hJa
    clear hMaxV hCol hDP hSV hQ
    c0_hsplit
    · c0_hsteps!; exact hJa (_, _, _, ()) m1 ⟨s1, hdw1, rfl, rfl, htmk1_z, hm1⟩
    · -- `need_mark == false`: scan remaining `FL_SWEEP_INC` vars
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64, i64])
        (fun (rem_l, v_l, ()) ml => v_l.toNat ≤ s1.core.cur_vars ∧
          ∃ fl_l : List (BitVec 32), fl_l.length = c.max_vars ∧
            (FullMem c { s1 with core := { s1.core with flags := fl_l } } ⋆ R) ml)
        (fun (_, v_l, ()) _ => s1.core.cur_vars - v_l.toNat)
        ?_ ?_
      ·
          intro _ hJ_r
          c0_hsteps!
          exact hJ_r (0#64, 0#64, ()) m1
            ⟨Nat.zero_le _, s1.core.flags, hlen1.core_ok.flags_len, hm1⟩
      ·
          rintro _ ⟨rem_l, v_l, ⟨⟩⟩ ml ⟨hv_le, fl_l, hfl_l_len, hml⟩ hJ_r
          c0_hsplit; rotate_left
          · let s_r : FullState := { s1 with core := { s1.core with flags := fl_l } }
            have hdw_r : FullDenseInvW c F0 F_cur s_r := fid_denseInvW_set_flags hdw1 hfl_l_len
            have htmk_r : M6TmkZero s_r := fid_tmkZero_congr htmk1_z rfl rfl
            obtain ⟨hgr_28, _, _, hgr_28', _, _⟩ := fid_gu_idx_lt hdw_r.1.scratch_ok.glue_used_len
            refine wp_join_group (ts := [i32, i64, .bool])
              (fun (_c24, _m24, _n24, ()) m24 =>
                ∃ s_a : FullState, FullDenseInvW c F0 F_cur s_a ∧
                  s_a.core.cur_vars = s1.core.cur_vars ∧ s_a.core.fuel = s1.core.fuel ∧
                  M6TmkZero s_a ∧ (FullMem c s_a ⋆ R) m24)
              (fun _ (c24, m24, n24, ()) m_24 h => by
                c0_hsteps!; exact hJa (c24, m24, n24, ()) m_24 h)
              (fun _ hJ24 => by
                c0_hsplit
                · -- `rem_inc == 0`: bump `gu[28]`, recompute `comp`/`max_occ`, `need_mark = true`
                  refine wp_join_group (ts := [])
                    (fun () m_g => ∃ gu_g : List (BitVec 32), gu_g.length = 64 ∧
                      (FullMem c { s_r with scratch := { s_r.scratch with glue_used := gu_g } } ⋆ R)
                        m_g)
                    (fun _ () m_g ⟨gu_g, hgu_g, hm_g⟩ => by
                      obtain ⟨hgg_28, _, _, hgg_28', _, _⟩ := fid_gu_idx_lt hgu_g
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i32]) (fun (_comp', ()) m_c' => m_c' = m_g)
                        (fun _ (_comp', ()) m_c' hmc' => by
                          subst m_c'
                          c0_hsteps!
                          exact hJ24 (_, _, true, ()) m_g
                            ⟨_, fid_denseInvW_set_gu hdw_r hgu_g, rfl, rfl,
                              fid_tmkZero_congr htmk_r rfl rfl, hm_g⟩)
                        (fun _ hJc' => by
                          c0_hsplit
                          · c0_hsteps!; exact hJc' (5#32, ()) m_g rfl
                          · c0_hsteps!; exact hJc' (_, ()) m_g rfl))
                    (fun _ hJg => by
                      c0_hsplit
                      · c0_hsteps!
                        refine hJg () _ ⟨_, ?_, by assumption⟩
                        simp only [List.length_set, hdw1.1.scratch_ok.glue_used_len]
                      · c0_hsteps!
                        exact hJg () ml ⟨s_r.scratch.glue_used, hdw_r.1.scratch_ok.glue_used_len,
                          hml⟩)
                · c0_hsteps!; exact hJ24 (_, _, _, ()) ml ⟨s_r, hdw_r, rfl, rfl, htmk_r, hml⟩)
          · have hv_lt : v_l.toNat < s1.core.cur_vars := by
              have h1 : v_l.toNat < s1.core.cur_vars % 2 ^ 64 := hc
              rwa [Nat.mod_eq_of_lt hcv1_2p64] at h1
            have hv1 : (v_l + 1#64).toNat = v_l.toNat + 1 := fid_bv64_add1_lt hv_lt hcv1_lt
            have hv_fl : v_l.toNat < fl_l.length := by
              rw [hfl_l_len]; exact Nat.lt_of_lt_of_le hv_lt hcv1_le
            have hv_vals : (v_l <<< (1 : Nat)).toNat < s1.core.vals.length := by
              exact fid_vals_shl1_lt hv_lt hcv1_lt hcv1_le hlen1.core_ok.vals_len
            have hpos_bd : (((v_l <<< (1 : BitVec 64)) <<< (1 : BitVec 64)) +
                (1 : BitVec 64)).toNat < s1.core.wvec.length := by
              exact fid_wvec_pos_lt hv_lt hcv1_lt hcv1_le hlen1.core_ok.wvec_len
            have hneg_bd : ((((v_l <<< (1 : BitVec 64)) ||| (1 : BitVec 64)) <<<
                (1 : BitVec 64)) + (1 : BitVec 64)).toNat < s1.core.wvec.length := by
              exact fid_wvec_neg_lt hv_lt hcv1_lt hcv1_le hlen1.core_ok.wvec_len
            refine wp_join_group (ts := [i64])
              (fun (rem', ()) mv1 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                (FullMem c { s1 with core := { s1.core with flags := fl' } } ⋆ R) mv1)
              (fun _ (rem', ()) mv1 ⟨fl', hfl', hmv1⟩ => by
                c0_hsteps!
                exact hJ_r (rem', v_l + 1#64, ()) mv1
                  (by dsimp only; rw [hv1]; exact fid_sub_add1_lt hv_lt)
                  ⟨by rw [hv1]; exact hv_lt, fl', hfl', hmv1⟩)
              (fun _ hJ_v1 => by
                c0_hsplit; rotate_left
                · c0_hsteps!; exact hJ_v1 (_, ()) ml ⟨fl_l, hfl_l_len, hml⟩
                refine wp_join_group (ts := [i64])
                  (fun (rem28, ()) m28 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                    (FullMem c { s1 with core := { s1.core with flags := fl' } } ⋆ R) m28)
                  (fun _ (rem28, ()) m28 h => by c0_hsteps!; exact hJ_v1 (rem28, ()) m28 h)
                  (fun _ hJ28 => by
                    c0_hsplit; rotate_left
                    · c0_hsteps!
                      refine hJ28 (_, ()) _ ⟨_, ?_, by assumption⟩
                      simp only [List.length_set, hfl_l_len]
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64])
                      (fun (rem32, ()) m32 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                        (FullMem c { s1 with core := { s1.core with flags := fl' } } ⋆ R) m32)
                      (fun _ (rem32, ()) m32 h => by c0_hsteps!; exact hJ28 (rem32, ()) m32 h)
                      (fun _ hJ32 => by
                        refine wp_join_group (ts := []) (fun () m34 => m34 = ml)
                          (fun _ () m34 hm34 => by
                            subst hm34; c0_hsteps!
                            refine hJ32 (_, ()) _ ⟨_, ?_, by assumption⟩
                            simp only [List.length_set, hfl_l_len])
                          (fun _ hJ34 => by
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ34 () ml rfl
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ34 () ml rfl
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ34 () ml rfl
                            c0_hsplit; rotate_left
                            · c0_hsteps!; exact hJ34 () ml rfl
                            c0_hsteps!
                            exact hJ32 (_, ()) ml ⟨fl_l, hfl_l_len, hml⟩))))

end LeanQbe.T.Examples.Kissat.FullFidelitySweep

end
