module

public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Proofs — Part 3 (Structural Gate Extraction)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
- `full_bve_find_equiv_m7_wp`
- `full_bve_find_and_m7_wp`
- `full_bve_match_tern_m7_wp`
- `full_bve_find_ite_side_m7_wp`
- `full_bve_find_ite_m7_wp`
- `full_bve_xor_pat_m7_wp`
- `full_bve_find_xor_m7_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Shared Scratch, `lit_mark`, and Literal Helpers -/

private theorem m7_p3_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have h1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h2 : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, h1, BitVec.toNat_ofNat]
    have h1m : 1 % 2 ^ 32 = 1 := rfl
    rw [h1m]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, Nat.mul_mod_right]
      simp [show (2 * v.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div (by omega : 0 < 2)]
  exact ⟨h1, h2⟩

private theorem m7_p3_bveEntry_mono_scratch {F_cur : List (List Nat)} {s : FullState}
    {sc' : FullScratch} {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    FullBveEntryOkW F_cur { s with scratch := sc' } lit w := h

private theorem m7_p3_bveEntry_mono_lm {F_cur : List (List Nat)} {s : FullState}
    {lm' : List (BitVec 8)} {sc' : FullScratch} {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    FullBveEntryOkW F_cur { s with core := { s.core with lit_mark := lm' }, scratch := sc' }
      lit w := by
  unfold FullBveEntryOkW at h ⊢; exact h

private theorem m7_p3_fullDenseInvW_lm_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hlm_len : lm'.length = 2 * c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8)
    {scr' : List (BitVec 32)} (hscr_len : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with lit_mark := lm' }
        scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len },
    { h.1.scratch_ok with scratch_buf_len := hscr_len }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m7_p3_lm_set_at {c : FullCfg} {lm : List (BitVec 8)} {x_idx : Nat}
    (_hlm : lm.length = 2 * c.max_vars) (_hx : x_idx < 2 * c.max_vars) {v : BitVec 8}
    {P : Nat → Prop} (hprev : ∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 → P y)
    (hnew : P x_idx) :
    ∀ y < 2 * c.max_vars, (lm.set x_idx v)[y]?.getD 0#8 ≠ 0#8 → P y := by
  intro y hy hnz
  by_cases hyx : y = x_idx
  · subst hyx; exact hnew
  · rw [List.getElem?_set_ne (Ne.symm hyx)] at hnz; exact hprev y hy hnz

private theorem m7_p3_lm_clear_step {c : FullCfg} {lm : List (BitVec 8)} {x_idx : Nat}
    (hlm : lm.length = 2 * c.max_vars) (hx : x_idx < 2 * c.max_vars) {P : Nat → Prop}
    (hprev : ∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 → y = x_idx ∨ P y) :
    ∀ y < 2 * c.max_vars, (lm.set x_idx 0#8)[y]?.getD 0#8 ≠ 0#8 → P y := by
  intro y hy hnz
  by_cases hyx : y = x_idx
  · subst hyx
    rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz; exact absurd rfl hnz
  · rw [List.getElem?_set_ne (Ne.symm hyx)] at hnz; exact (hprev y hy hnz).resolve_left hyx

private theorem m7_p3_mask_lt_16 (idx : BitVec 32) (hi : idx.toNat < 512) :
    (idx >>> (5 : Nat)).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

private theorem m7_p3_mask_idx_lo (base idx : BitVec 32)
    (hb : base.toNat = 1024 ∨ base.toNat = 1040) (hi : idx.toNat < 512) :
    1024 ≤ (base + (idx >>> (5 : Nat))).toNat ∧
    (base + (idx >>> (5 : Nat))).toNat < 1056 := by
  have hm := m7_p3_mask_lt_16 idx hi
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega

private theorem m7_p3_and7fff_lt {n : Nat} (w : BitVec 32) (hb : (w &&& 0x80000000#32) ≠ 0#32)
    (hok : (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < n) :
    (w &&& 0x7FFFFFFF#32).toNat < n := hok hb

private theorem m7_p3_u32_and7fff_or8000 (j : BitVec 32) (hj : j.toNat < 512) :
    ((j ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = j := by
  apply BitVec.eq_of_toNat_eq
  have h1 : ((j ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (j &&& 0x7FFFFFFF#32) := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
    have h0 : ((0x80000000#32 &&& 0x7FFFFFFF#32) : BitVec 32)[i] = false := by
      have : (0x80000000#32 &&& 0x7FFFFFFF#32) = 0#32 := by decide
      rw [this]; simp
    simp only [BitVec.getElem_and] at h0; rw [Bool.and_or_distrib_right, h0, Bool.or_false]
  rw [h1, BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem m7_p3_u32_and7fff_self (j : BitVec 32) (hj : j.toNat < 512) :
    (j &&& 0x7FFFFFFF#32).toNat = j.toNat := by
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

/-! ## 2. `full_bve_find_equiv_m7` -/

/-- Parametric `Func.wp` proof for `full_bve_find_equiv_m7`. -/
theorem full_bve_find_equiv_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveFindEquivM7Spec a m Q X →
      Func.wp Γ full_bve_find_equiv_m7_body a m Q X := by
  rintro ⟨h, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1088, hnp512, hnn512, hp_ok, hn_ok, hm0, hQ⟩ :=
    fullBveFindEquivM7Spec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  unfold Func.wp full_bve_find_equiv_m7_body
  c0_hsteps_nogrp
  -- Loop 1: mark `lm[ot] = 1` for unassigned binary occurrences in `scr[0 ..< np)`
  refine wp_loop_group (ts := [i32, i32])
    (fun rem1 (bin_p, i, ()) m1 => ∃ lm1 : List (BitVec 8),
      let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
      lm1.length = 2 * c.max_vars ∧ i.toNat ≤ np.toNat ∧ rem1 = np.toNat - i.toNat ∧
      bin_p.toNat ≤ i.toNat ∧
      (bin_p = 0#32 → ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 = 0#8) ∧
      (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
        ∃ u < i.toNat, let w := s0.scratch.scratch_buf[u]?.getD 0#32;
          (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
      (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro L1 rem1 ⟨bin_p, i, ⟨⟩⟩ m1 hL1 ⟨lm1, hlm1, hi_le, rfl, hbp_le, hbp0, hmark1, hm1⟩
    c0_hsplit
    · have hi_lt : i.toNat < np.toNat := hc
      have hi_sc : (i.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
        rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
      let wp := s0.scratch.scratch_buf[(i.setWidth 64).toNat]'hi_sc
      have hwp_get : s0.scratch.scratch_buf[i.toNat]?.getD 0#32 = wp := by
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
          Option.getD_some]
        exact m6_getElem_congr (m6_zext32_toNat i).symm _ _
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8)) (fun x => (x.1, ()))
        (fun x mj => x.2.length = 2 * c.max_vars ∧ x.1.toNat ≤ i.toNat + 1 ∧
          (x.1 = 0#32 → ∀ z < 2 * c.max_vars, x.2[z]?.getD 0#8 = 0#8) ∧
          (∀ z < 2 * c.max_vars, x.2[z]?.getD 0#8 ≠ 0#8 →
            ∃ u < i.toNat + 1, let w := s0.scratch.scratch_buf[u]?.getD 0#32;
              (w &&& 0x80000000#32) ≠ 0#32 ∧ z = (w &&& 0x7FFFFFFF#32).toNat) ∧
          (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
        (fun _ ⟨bp', lm'⟩ mj ⟨hlm', hbp', hbp0', hmk', hmj⟩ => by
          dsimp only at hbp' hbp0' hmk' hmj
          c0_hsteps!
          exact hL1 (np.toNat - (i + 1#32).toNat) (bp', i + 1#32, ()) mj (by omega)
            ⟨lm', hlm', by omega, rfl, by omega, hbp0', fun z hz hnz => by
              obtain ⟨u, hu, hw⟩ := hmk' z hz hnz; exact ⟨u, by omega, hw⟩, hmj⟩)
        (fun J1 hJ1 => by
          have hkeep : J1 (bin_p, ()) m1 := by
            refine hJ1 (bin_p, lm1) m1 ⟨hlm1, by dsimp only; omega, hbp0, fun z hz hnz => ?_, hm1⟩
            obtain ⟨u, hu, hw⟩ := hmark1 z hz hnz; exact ⟨u, by omega, hw⟩
          c0_hsplit
          · have hwp_bin : (wp &&& 0x80000000#32) ≠ 0#32 := hc
            have hot_lt : (wp &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
              have h1 := hp_ok i.toNat hi_lt; dsimp only at h1; rw [hwp_get] at h1
              exact h1 hwp_bin
            have hot_v : ((wp &&& 0x7FFFFFFF#32).setWidth 64).toNat < s0.core.vals.length := by
              rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
              (fun x => (x.1, ()))
              (fun x mj => x.2.length = 2 * c.max_vars ∧ x.1.toNat ≤ i.toNat + 1 ∧
                (x.1 = 0#32 → ∀ z < 2 * c.max_vars, x.2[z]?.getD 0#8 = 0#8) ∧
                (∀ z < 2 * c.max_vars, x.2[z]?.getD 0#8 ≠ 0#8 →
                  ∃ u < i.toNat + 1, let w := s0.scratch.scratch_buf[u]?.getD 0#32;
                    (w &&& 0x80000000#32) ≠ 0#32 ∧ z = (w &&& 0x7FFFFFFF#32).toNat) ∧
                (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
              (fun _ ⟨bp', lm'⟩ mj ⟨hlm', hbp', hbp0', hmk', hmj⟩ => by
                dsimp only at hbp' hbp0' hmk' hmj
                c0_hsteps!
                exact hJ1 (bp', lm') mj ⟨hlm', hbp', hbp0', hmk', hmj⟩)
              (fun J1i hJ1i => by
                c0_hsplit
                · have hot_lm : ((wp &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm1.length := by
                    rw [hlm1, m6_zext32_toNat]; omega
                  have hbp1 : (bin_p + 1#32).toNat = bin_p.toNat + 1 := by c0_bound
                  have hcv := hdw0.1.core_ok.cur_vars_le
                  let lm_n := lm1.set ((wp &&& 0x7FFFFFFF#32).setWidth 64).toNat 1#8
                  have hbp_n_le : (bin_p + 1#32).toNat ≤ i.toNat + 1 := by omega
                  have hbp_n_ne : ∀ h : bin_p + 1#32 = 0#32, False := fun h => by
                    have h0 : (bin_p + 1#32).toNat = 0 := congrArg BitVec.toNat h
                    rw [hbp1] at h0; omega
                  c0_hsteps!
                  exact hJ1i (bin_p + 1#32, lm_n) _
                    ⟨by simp [lm_n, hlm1], by dsimp only; omega,
                      fun h => False.elim (hbp_n_ne h),
                      m7_p3_lm_set_at hlm1 (by rw [m6_zext32_toNat]; omega)
                        (fun z hz hnz => by
                          obtain ⟨u, hu, hw⟩ := hmark1 z hz hnz; exact ⟨u, by omega, hw⟩)
                        ⟨i.toNat, by omega,
                          by rw [hwp_get, m6_zext32_toNat]; exact ⟨hwp_bin, rfl⟩⟩,
                      hm⟩
                · c0_hsteps!
                  exact hJ1i (bin_p, lm1) m1
                    ⟨hlm1, by dsimp only; omega, hbp0, fun z hz hnz => by
                      obtain ⟨u, hu, hw⟩ := hmark1 z hz hnz; exact ⟨u, by omega, hw⟩, hm1⟩)
          · c0_hsteps!; exact hkeep)
    · have hi_eq : i.toNat = np.toNat := by omega
      c0_hsplit
      · have hclr1 : ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 = 0#8 := hbp0 hc
        let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
        have hdw1 := m7_p3_fullDenseInvW_lm_scr hdw0 hlm1 hclr1 hdw0.1.scratch_ok.scratch_buf_len
        c0_hsteps!; exact hQ false lm1 s0.scratch.scratch_buf m1 hdw1
          hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm1
      · -- Loop 2: scan `scr[512 ..< 512 + nn)` for matching binary `ot ^ 1` in `lm1`
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i32, i32, i32]) (lpTs := [i32])
          (fun (ml_b, mj_b, _, ()) mb => mb = m1 ∧
            (ml_b = 0xFFFFFFFF#32 ∨ mj_b.toNat < nn.toNat))
          (fun rem2 (j, ()) m2 => m2 = m1 ∧ j.toNat ≤ nn.toNat ∧ rem2 = nn.toNat - j.toNat)
          ?_ ?_ ?_
        · rintro _ ⟨ml_b, mj_b, _, ⟨⟩⟩ mb ⟨hmb, hmb_ok⟩
          subst mb
          -- Loop 3: clear `lm1[wp & PW_LIT_MASK]` for `0 ..< np`
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem3 (ic, ()) m3 => ∃ lm3 : List (BitVec 8),
              let s3 : FullState := { s0 with core := { s0.core with lit_mark := lm3 } }
              lm3.length = 2 * c.max_vars ∧ ic.toNat ≤ np.toNat ∧
              rem3 = np.toNat - ic.toNat ∧
              (∀ x < 2 * c.max_vars, lm3[x]?.getD 0#8 ≠ 0#8 →
                ∃ u, ic.toNat ≤ u ∧ u < np.toNat ∧
                  let w := s0.scratch.scratch_buf[u]?.getD 0#32;
                  (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
              (FullMem c s3 ⋆ R) m3)
            ?_ ?_
          · rintro L3 rem3 ⟨ic, ⟨⟩⟩ m3 hL3 ⟨lm3, hlm3, hic_le, rfl, hrem3, hm3⟩
            c0_hsplit
            · have hic_lt : ic.toNat < np.toNat := hc
              have hic_sc : (ic.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
                rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
              let wc := s0.scratch.scratch_buf[(ic.setWidth 64).toNat]'hic_sc
              have hwc_get : s0.scratch.scratch_buf[ic.toNat]?.getD 0#32 = wc := by
                rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                  Option.getD_some]
                exact m6_getElem_congr (m6_zext32_toNat ic).symm _ _
              have hic1 : (ic + 1#32).toNat = ic.toNat + 1 := by c0_bound
              have hcv := hdw0.1.core_ok.cur_vars_le
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ m3' => ∃ lm3' : List (BitVec 8),
                  let s3' : FullState := { s0 with core := { s0.core with lit_mark := lm3' } }
                  lm3'.length = 2 * c.max_vars ∧
                  (∀ x < 2 * c.max_vars, lm3'[x]?.getD 0#8 ≠ 0#8 →
                    ∃ u, ic.toNat + 1 ≤ u ∧ u < np.toNat ∧
                      let w := s0.scratch.scratch_buf[u]?.getD 0#32;
                      (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
                  (FullMem c s3' ⋆ R) m3')
                (fun _ _ m3' ⟨lm3', hlm3', hrem3', hm3'⟩ => by
                  c0_hsteps!
                  exact hL3 (np.toNat - (ic + 1#32).toNat) (ic + 1#32, ()) m3' (by omega)
                    ⟨lm3', hlm3', by omega, rfl, fun y hy hnz => by
                      obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem3' y hy hnz
                      exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm3'⟩)
                (fun _ hJ3 => by
                  c0_hsplit
                  · have hwc_bin : (wc &&& 0x80000000#32) ≠ 0#32 := hc
                    have hot_lt : (wc &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                      have h1 := hp_ok ic.toNat hic_lt; dsimp only at h1; rw [hwc_get] at h1
                      exact h1 hwc_bin
                    have hot_lm : ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm3.length := by
                      rw [hlm3, m6_zext32_toNat]; omega
                    c0_hsteps!
                    refine hJ3 () _
                      ⟨lm3.set ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8, by simp [hlm3],
                       m7_p3_lm_clear_step hlm3 (by rw [m6_zext32_toNat]; omega) (fun y hy hnz => by
                         obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem3 y hy hnz
                         rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                         · left; rw [m6_zext32_toNat, hyeq, hwc_get]
                         · right; exact ⟨u, by omega, hu2, hwu, hyeq⟩), hm⟩
                  · c0_hsteps!
                    refine hJ3 () m3
                      ⟨lm3, hlm3, fun y hy hnz => by
                        obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem3 y hy hnz
                        rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                        · have hwc_c0 :
                              s0.scratch.scratch_buf[ic.toNat]'(by
                                rw [hdw0.1.scratch_ok.scratch_buf_len]; omega) = wc := by
                            rw [← hwc_get, List.getElem?_eq_getElem (by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                          have h0 := hc; rw [hwc_c0] at h0
                          rw [hwc_get] at hwu; exact absurd h0 hwu
                        · exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm3⟩)
            · have hic_eq : ic.toNat = np.toNat := by omega
              have hclr3 : ∀ x < 2 * c.max_vars, lm3[x]?.getD 0#8 = 0#8 := fun x hx =>
                Classical.byContradiction fun hnz => by
                  obtain ⟨u, hu1, hu2, _⟩ := hrem3 x hx hnz; omega
              let s3 : FullState := { s0 with core := { s0.core with lit_mark := lm3 } }
              have hdw3 :=
                m7_p3_fullDenseInvW_lm_scr hdw0 hlm3 hclr3 hdw0.1.scratch_ok.scratch_buf_len
              c0_hsplit
              · c0_hsteps!; exact hQ false lm3 s0.scratch.scratch_buf m3 hdw3
                  hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm3
              · have hml_ne : ml_b ≠ 0xFFFFFFFF#32 := hc
                have hmj_lt : mj_b.toNat < nn.toNat := hmb_ok.resolve_left hml_ne
                have hmj_m : (1040#32 + (mj_b >>> (5 : Nat))).toNat <
                    s0.scratch.scratch_buf.length := by
                  have hb := m7_p3_mask_idx_lo 1040#32 mj_b (Or.inr rfl) (by omega)
                  rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                -- Loop 4: locate matching `i < np` and write bitmasks (`1024..1057`)
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i32])
                  (fun rem4 (im, ()) m4 => m4 = m3 ∧ im.toNat ≤ np.toNat ∧
                    rem4 = np.toNat - im.toNat)
                  ?_ ?_
                · rintro L4 rem4 ⟨im, ⟨⟩⟩ m4 hL4 ⟨hm4, him_le, rfl⟩
                  subst m4
                  c0_hsplit
                  · have him_lt : im.toNat < np.toNat := hc
                    have him_sc : (im.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
                      rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
                    have him1 : (im + 1#32).toNat = im.toNat + 1 := by c0_bound
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ m4' => m4' = m3)
                      (fun _ _ m4' hm4' => by
                        subst m4'
                        c0_hsteps!
                        exact hL4 (np.toNat - (im + 1#32).toNat) (im + 1#32, ()) m3
                          (by omega) ⟨rfl, by omega, rfl⟩)
                      (fun _ hJ4 => by
                        c0_hsplit
                        · c0_hsplit
                          · have him_m : (1024#32 + (im >>> (5 : Nat))).toNat <
                                s0.scratch.scratch_buf.length := by
                              have hb := m7_p3_mask_idx_lo 1024#32 im (Or.inl rfl) (by omega)
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            have h1056 : 1056 < s0.scratch.scratch_buf.length := by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            have h1057 : 1057 < s0.scratch.scratch_buf.length := by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                            c0_hsteps!
                            have hlen0 := hdw0.1.scratch_ok.scratch_buf_len
                            have him_bd := m7_p3_mask_idx_lo 1024#32 im (Or.inl rfl) (by omega)
                            have hmj_bd := m7_p3_mask_idx_lo 1040#32 mj_b (Or.inr rfl) (by omega)
                            refine hQ true lm3 ?_ m ?_ ?_ ?_ ?_
                            rotate_left 4
                            · exact hm
                            · exact m7_p3_fullDenseInvW_lm_scr hdw0 hlm3 hclr3 (by simp [hlen0])
                            · simp [hlen0]
                            · have him_idx :
                                  ((1024 + im >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                    1024 + im.toNat / 32 := by
                                rw [m6_zext32_toNat, BitVec.toNat_add,
                                  show (1024 : BitVec 32).toNat = 1024 from rfl,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                              have hmj_idx :
                                  ((1040 + mj_b >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                    1040 + mj_b.toNat / 32 := by
                                rw [m6_zext32_toNat, BitVec.toNat_add,
                                  show (1040 : BitVec 32).toNat = 1040 from rfl,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                              intro idx hidx hor
                              rw [him_idx, hmj_idx,
                                List.getElem?_set_ne
                                  (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                                List.getElem?_set_ne
                                  (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                                List.getElem?_set_ne (by omega),
                                List.getElem?_set_ne (by omega)]
                          · c0_hsteps!; exact hJ4 () m3 rfl
                        · c0_hsteps!; exact hJ4 () m3 rfl)
                  · c0_hsteps!; exact hQ false lm3 s0.scratch.scratch_buf m3 hdw3
                      hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm3
                · intro L4 hL4; c0_hsteps!; exact hL4 np.toNat (0#32, ()) m3
                    ⟨rfl, Nat.zero_le _, by simp⟩
          · intro L3 hL3; c0_hsteps!; exact hL3 np.toNat (0#32, ()) m1
              ⟨lm1, hlm1, Nat.zero_le _, by simp, fun x hx hnz => by
                obtain ⟨u, hu, hw⟩ := hmark1 x hx hnz; exact ⟨u, Nat.zero_le _, by omega, hw⟩,
               hm1⟩
        · rintro B2 L2 rem2 ⟨j, ⟨⟩⟩ m2 hB2 hL2 ⟨hm2, hj_le, rfl⟩
          subst m2
          c0_hsplit
          · have hj_lt : j.toNat < nn.toNat := hc
            have hj_sc : ((512#32 + j).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
              rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
            let wn := s0.scratch.scratch_buf[((512#32 + j).setWidth 64).toNat]'hj_sc
            have hwn_get : s0.scratch.scratch_buf[512 + j.toNat]?.getD 0#32 = wn := by
              rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                Option.getD_some]
              exact m6_getElem_congr (by rw [m6_zext32_toNat]; c0_bound) _ _
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            refine wp_join_group (fun _ m2' => m2' = m1)
              (fun _ _ m2' hm2' => by
                subst m2'
                c0_hsteps!
                exact hL2 (nn.toNat - (j + 1#32).toNat) (j + 1#32, ()) m1 (by omega)
                  ⟨rfl, by omega, rfl⟩)
              (fun _ hJ2 => by
                c0_hsplit
                · have hwn_bin : (wn &&& 0x80000000#32) ≠ 0#32 := hc
                  have hot_lt : (wn &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                    have h1 := hn_ok j.toNat hj_lt; dsimp only at h1; rw [hwn_get] at h1
                    exact h1 hwn_bin
                  have hot_v : ((wn &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                      s0.core.vals.length := by
                    rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                  have hotn_lt :
                      ((wn &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
                    change (wn &&& 0x7FFFFFFF#32).toNat ^^^ 1 < 2 * s0.core.cur_vars
                    have := fullInv_var_xor1 (wn &&& 0x7FFFFFFF#32).toNat; omega
                  have hotn_lm : (((wn &&& 0x7FFFFFFF#32) ^^^ 1#32).setWidth 64).toNat <
                      lm1.length := by
                    rw [hlm1, m6_zext32_toNat]; omega
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps!
                      exact hB2 (((wn &&& 0x7FFFFFFF#32) ^^^ 1#32), j, j, ()) m1
                        ⟨rfl, Or.inr hj_lt⟩
                    · c0_hsteps!; exact hJ2 _ m1 rfl
                  · c0_hsteps!; exact hJ2 _ m1 rfl
                · c0_hsteps!; exact hJ2 _ m1 rfl)
          · c0_hsteps!; exact hB2 (0xFFFFFFFF#32, 0#32, j, ()) m1 ⟨rfl, Or.inl rfl⟩
        · intro _ L2 _ hL2; c0_hsteps!; exact hL2 nn.toNat (0#32, ()) m1
            ⟨rfl, Nat.zero_le _, by simp⟩
  · intro L1 hL1; c0_hsteps!
    exact hL1 np.toNat (0#32, 0#32, ()) m0
      ⟨s0.core.lit_mark, hdw0.1.core_ok.lit_mark_len, Nat.zero_le _, by simp,
       Nat.zero_le _, fun _ => hdw0.2.2.1.2, fun x hx hnz =>
         absurd (hdw0.2.2.1.2 x hx) hnz, hm0⟩

/-! ## 3. `full_bve_match_tern_m7`, `full_bve_find_ite_side_m7`, `full_bve_find_ite_m7` -/

/-- Parametric `Func.wp` proof for `full_bve_match_tern_m7`. -/
theorem full_bve_match_tern_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveMatchTernM7Spec a m Q X →
      Func.wp Γ full_bve_match_tern_m7_body a m Q X := by
  rintro ⟨h, opp_lit, x, y, opp_off, opp_n, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1066, hooff, hon512, hent_n, hm0, hQ⟩ :=
    fullBveMatchTernM7Spec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  unfold Func.wp full_bve_match_tern_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (j, ()) mj => ∃ scr_j : List (BitVec 32),
      let sj : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_j } }
      scr_j.length = c.scratch_cap ∧ j.toNat ≤ opp_n.toNat ∧ rem = opp_n.toNat - j.toNat ∧
      (∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
        scr_j[i]? = s0.scratch.scratch_buf[i]?) ∧
      (FullMem c sj ⋆ R) mj)
    ?_ ?_
  · rintro L rem ⟨j, ⟨⟩⟩ mj hL ⟨scr_j, hscj, hj_le, rfl, hout_j, hmj⟩
    have h1058 : 1058 < scr_j.length := by rw [hscj]; omega
    c0_hsplit
    · c0_hsplit
      · have hj_lt : j.toNat < opp_n.toNat := by assumption
        have hoj_sc : ((opp_off + j).setWidth 64).toNat < scr_j.length := by
          rw [hscj, m6_zext32_toNat]; c0_bound
        have hwj_orig :
            scr_j[((opp_off + j).setWidth 64).toNat]'hoj_sc =
              s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := by
          have hoj_eq : ((opp_off + j).setWidth 64).toNat = opp_off.toNat + j.toNat := by
            rw [m6_zext32_toNat]; c0_bound
          have hget := hout_j (opp_off.toNat + j.toNat) (by omega) (Or.inl (by omega))
          have hoj' : opp_off.toNat + j.toNat < scr_j.length := by omega
          rw [List.getElem?_eq_getElem hoj'] at hget
          rw [← hget, Option.getD_some]
          exact m6_getElem_congr hoj_eq hoj_sc hoj'
        let scr_s := scr_j.set 1058 (scr_j[1058]'h1058 + 1#32)
        have hsc_s : scr_s.length = c.scratch_cap := by simp [scr_s, hscj]
        have hout_s : ∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
            scr_s[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor => by
          dsimp only [scr_s]; rw [List.getElem?_set_ne (by omega)]; exact hout_j i hi hor
        have hoj_sc_s : ((opp_off + j).setWidth 64).toNat < scr_s.length := by
          rw [hsc_s, m6_zext32_toNat]; c0_bound
        have hwj_s : scr_s[((opp_off + j).setWidth 64).toNat]'hoj_sc_s =
            s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := by
          rw [← hwj_orig]
          dsimp only [scr_s]
          rw [List.getElem_set_ne (by c0_bound)]
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mj' => mj' = m)
          (fun _ _ mj' hmj' => by
            subst mj'
            c0_hsteps!
            exact hL (opp_n.toNat - (j + 1#32).toNat) (j + 1#32, ()) m
              (by omega) ⟨scr_s, hsc_s, by omega, rfl, hout_s, hm⟩)
          (fun _ hJj => by
            -- Either binary (`(w & PW_BIN_FLAG) != 0`) or large arena clause loop
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ mb' => mb' = m)
                (fun _ _ mb' hmb' => by
                  subst mb'
                  c0_hsteps!; exact hQ (j ||| 0x80000000#32) scr_s m hsc_s hout_s
                    (Or.inr (by rw [m7_p3_u32_and7fff_or8000 j (by omega)]; exact hj_lt)) hm)
                (fun _ hJret => by
                  c0_hsplit
                  · c0_hsteps!; exact hJret () m rfl
                  · c0_hsplit
                    · c0_hsteps!; exact hJret () m rfl
                    · c0_hsteps!; exact hJj () m rfl)
            · let w := scr_s[((opp_off + j).setWidth 64).toNat]'hoj_sc_s
              have hent_j := hent_n j.toNat hj_lt
              rw [← hwj_s] at hent_j; unfold FullBveEntryOkW at hent_j
              rw [ite_eq_right (fun h => h hc)] at hent_j
              have href_j : w.toNat ∈ fullArenaClauseRefs s0 := hent_j.1
              have hng_j : fullArenaClauseGarb s0 w.toNat = false := hent_j.2
              have hwf := hdw0.2.1.arena.refs_wf w.toNat href_j
              have hw_bd : w.toNat + 3 + fullArenaClauseSizeCore s0.core w.toNat ≤
                  c.arena_cap := by
                have := hwf.2.2.1; have := hwf.2.2.2.1; omega
              have hsz_ge : 3 ≤ fullArenaClauseSizeCore s0.core w.toNat := hwf.2.1
              have hw2_ar : (w.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, m6_zext32_toNat,
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                omega
              let sz := s0.core.arena[(w.setWidth 64 + 2#64).toNat]'hw2_ar
              have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core w.toNat := by
                unfold sz fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                  Option.getD_some]
                exact congrArg BitVec.toNat (m6_getElem_congr (by
                  rw [BitVec.toNat_add, m6_zext32_toNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega)]) _ _)
              c0_hsteps_nogrp
              refine wp_loop_break_group (brkTs := [.bool, .bool, .bool, i32])
                (lpTs := [.bool, .bool, i32])
                (fun (ok_b, sx_b, sy_b, _, ()) mb => mb = m)
                (fun rem_k (sx_k, sy_k, k, ()) mk => mk = m ∧ k.toNat ≤ sz.toNat ∧
                  rem_k = sz.toNat - k.toNat)
                ?_ ?_ ?_
              · rintro _ ⟨ok_b, sx_b, sy_b, _, ⟨⟩⟩ mb hmb
                subst mb
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mb' => mb' = m)
                  (fun _ _ mb' hmb' => by subst mb'; c0_hsteps!; exact hJj () m rfl)
                  (fun _ hJskip => by
                    c0_hsplit
                    · c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun _ ms' => ms' = m)
                        (fun _ _ ms' hms' => by
                          subst ms'
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := []) (fun _ mo' => mo' = m)
                            (fun _ _ mo' hmo' => by
                              subst mo'
                              c0_hsteps!
                              exact hQ (j ||| 0x80000000#32) scr_s m hsc_s hout_s
                                (Or.inr (by
                                  rw [m7_p3_u32_and7fff_or8000 j (by omega)]; exact hj_lt)) hm)
                            (fun _ hJor => by
                              c0_hsplit
                              · c0_hsteps!; exact hJor () m rfl
                              · c0_hsplit
                                · c0_hsteps!; exact hJor () m rfl
                                · c0_hsteps!; exact hJskip () m rfl))
                        (fun _ hJns => by
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsteps!; exact hQ j scr_s m hsc_s hout_s
                                (Or.inr (by
                                  rw [m7_p3_u32_and7fff_self j (by omega)]; exact hj_lt)) hm
                            · c0_hsteps!; exact hJns () m rfl
                          · c0_hsteps!; exact hJns () m rfl)
                    · c0_hsteps!; exact hJskip () m rfl)
              · rintro Bk Lk rem_k ⟨sx_k, sy_k, k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                subst mk
                c0_hsplit
                · have hk_lt : k.toNat < sz.toNat := hc
                  have hwk_eq : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                      w.toNat + 3 + k.toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                      m6_zext32_toNat, BitVec.toNat_ofNat]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                  have hwk : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                      s0.core.arena.length := by
                    rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                  let l := s0.core.arena[(w.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hwk
                  have hl_lt : l.toNat < 2 * s0.core.cur_vars := by
                    have hmem : l.toNat ∈ fullArenaClauseLitsCore s0.core w.toNat := by
                      rw [mem_fullArenaClauseLitsCore_iff (by
                        rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                      exact ⟨k.toNat, by omega,
                        congrArg BitVec.toNat (m6_getElem_congr hwk_eq.symm _ _)⟩
                    exact hdw0.2.1.arena.lits_lt w.toNat href_j hng_j _ hmem
                  have hl_v : (l.setWidth 64).toNat < s0.core.vals.length := by
                    rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                  have hk1 : (k + 1 : BitVec 32).toNat = k.toNat + 1 := by c0_bound
                  c0_hsplit
                  · c0_hsteps!; exact hBk (false, sx_k, sy_k, k, ()) m rfl
                  · c0_hsteps_nogrp
                    refine wp_join_group (fun _ mk' => mk' = m)
                      (fun _ _ mk' hmk' => by
                        subst mk'
                        c0_hsteps!
                        exact hLk (sz.toNat - (k + 1 : BitVec 32).toNat) _ m (by omega)
                          ⟨rfl, by omega, rfl⟩)
                      (fun _ hJk => by
                        c0_hsplit
                        · c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_join_group (fun _ mk' => mk' = m)
                              (fun _ _ mk' hmk' => by subst mk'; c0_hsteps!; exact hJk _ m rfl)
                              (fun _ hJxy => by
                                c0_hsplit
                                · c0_hsteps!; exact hJxy _ m rfl
                                · c0_hsplit
                                  · c0_hsteps!; exact hJxy _ m rfl
                                  · c0_hsteps!; exact hBk (false, sx_k, sy_k, k, ()) m rfl)
                          · c0_hsteps!; exact hJk _ m rfl
                        · c0_hsteps!; exact hJk _ m rfl)
                · c0_hsteps!; exact hBk (true, sx_k, sy_k, k, ()) m rfl
              · intro _ Lk _ hLk; c0_hsteps!
                exact hLk sz.toNat (false, false, 0#32, ()) m ⟨rfl, Nat.zero_le _, by simp⟩)
      · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_j mj hscj hout_j (Or.inl rfl) hmj
    · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_j mj hscj hout_j (Or.inl rfl) hmj
  · intro L hL; c0_hsteps!
    exact hL opp_n.toNat (0#32, ()) m0
      ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, Nat.zero_le _, by simp,
       fun _ _ _ => rfl, hm0⟩

private theorem m7_p3_xor_idx_lt (m : BitVec 8) (k : BitVec 32)
    (hm : (m.setWidth 32).slt 2#32 = false)
    (hk : ¬ k.toNat ≤ (2 ^ 32 - 2 % 2 ^ 32 + m.toNat) % 2 ^ 32 / 2) :
    ((m.setWidth 32 - 2#32) >>> (1 : Nat)).toNat < k.toNat := by
  have hm_lt : m.toNat < 256 := m.isLt
  have hge2 : 2 ≤ m.toNat := by
    rcases Nat.lt_or_ge m.toNat 2 with hlt | hge
    · have h01 : m.toNat = 0 ∨ m.toNat = 1 := by omega
      rcases h01 with h | h
      · have hm0 : m = 0#8 := BitVec.eq_of_toNat_eq (by simp [h])
        rw [hm0] at hm; cases hm
      · have hm1 : m = 1#8 := BitVec.eq_of_toNat_eq (by simp [h])
        rw [hm1] at hm; cases hm
    · exact hge
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.pow_one]
  omega

private theorem m7_p3_xor_bit_lt (x : BitVec 32) (hx : x.toNat < 4) :
    (1#32 <<< (x.toNat % 32)).toNat < 16 := by
  have hcases : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 := by omega
  rcases hcases with h | h | h | h <;> simp [h]

/-- Parametric `Func.wp` proof for `full_bve_xor_pat_m7` (read-only). -/
theorem full_bve_xor_pat_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveXorPatM7Spec a m Q X →
      Func.wp Γ full_bve_xor_pat_m7_body a m Q X := by
  rintro ⟨h, v_lit, cr, k, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hlen0, hw0, href, hng, hk1, hk4, hm0, hQ⟩ :=
    fullBveXorPatM7Spec_elim hSpec
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hwf := hw0.arena.refs_wf cr.toNat href
  have hal_le := hlen0.core_ok.arena_len_le
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hlen0.core_ok.arena_len_arr]; c0_bound
  let sz := s0.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core cr.toNat := by
    unfold sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.arena_len_arr]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
  unfold Func.wp full_bve_xor_pat_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, i32, i32])
    (fun rem (pat, seen, i, ()) mi =>
      mi = m0 ∧ i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧ pat.toNat < 16)
    ?_ ?_
  · rintro L rem ⟨pat, seen, i, ⟨⟩⟩ mi hL ⟨rfl, hi_le, rfl, hpat_lt⟩
    c0_hsplit
    · have hi_lt : i.toNat < sz.toNat := hc
      have hcri : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat < s0.core.arena.length := by
        rw [hlen0.core_ok.arena_len_arr]; c0_bound
      let li := s0.core.arena[(cr.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
      have hli_lt : li.toNat < 2 * s0.core.cur_vars := by
        have hmem : li.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat := by
          rw [mem_fullArenaClauseLitsCore_iff (by rw [hlen0.core_ok.arena_len_arr]; omega)]
          exact ⟨i.toNat, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
        exact hw0.arena.lits_lt cr.toNat href hng _ hmem
      have hli_v : (li.setWidth 64).toNat < s0.core.vals.length := by
        rw [hlen0.core_ok.vals_len, m6_zext32_toNat]; omega
      have hli_lm : (li.setWidth 64).toNat < s0.core.lit_mark.length := by
        rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
        (fun x => (x.1, x.2, ())) (fun x => x.1.toNat < 16)
        (fun _ ⟨pat', seen'⟩ hpat' => by
          c0_hsteps!
          exact hL (sz.toNat - (i + 1#32).toNat) (pat', seen', i + 1#32, ()) mi
            (by omega) ⟨rfl, by omega, rfl, hpat'⟩)
        (fun J hJ => by
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
            · c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                (fun x => (x.1, x.2, ())) (fun x => x.1.toNat < 16)
                (fun _ ⟨pat', seen'⟩ hp' => by
                  c0_hsteps!; exact hJ (pat', seen') hp')
                (fun _ hJi => by
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                    · c0_hsplit
                      · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                      · c0_hsplit
                        · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                        · have hidx_ar :
                              (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                i.toNat) % 2 ^ 64 < s0.core.arena.length := by
                            rw [hlen0.core_ok.arena_len_arr]; c0_bound
                          have hli_c0 :
                              s0.core.arena[(cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                i.toNat) % 2 ^ 64]'hidx_ar = li :=
                            m6_getElem_congr (by c0_bound) _ hcri
                          have hidx_lm :
                              (s0.core.arena[(cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                i.toNat) % 2 ^ 64]'hidx_ar).toNat <
                                s0.core.lit_mark.length := by
                            rw [hli_c0, hlen0.core_ok.lit_mark_len]; omega
                          have hm_ge := (by assumption :
                            ((s0.core.lit_mark[(s0.core.arena[(cr.toNat +
                              BitVec.toNat (3 : BitVec 64) +
                              i.toNat) % 2 ^ 64]'hidx_ar).toNat]'hidx_lm).setWidth 32
                              ).slt 2#32 = false)
                          have hk_n := (by assumption :
                            ¬ k.toNat ≤ (2 ^ 32 - OfNat.ofNat 2 % 2 ^ 32 +
                              (s0.core.lit_mark[(s0.core.arena[(cr.toNat +
                                BitVec.toNat (3 : BitVec 64) +
                                i.toNat) % 2 ^ 64]'hidx_ar).toNat]'hidx_lm).toNat) %
                                2 ^ 32 / 2)
                          have hm_ge_li :
                              ((s0.core.lit_mark[(li.setWidth 64).toNat]'hli_lm).setWidth 32
                                ).slt 2#32 = false := by
                            simpa only [m6_zext32_toNat, ← hli_c0] using hm_ge
                          have hk_n_li :
                              ¬ k.toNat ≤ (2 ^ 32 - 2 % 2 ^ 32 +
                                (s0.core.lit_mark[(li.setWidth 64).toNat]'hli_lm).toNat) %
                                  2 ^ 32 / 2 := by
                            simpa only [m6_zext32_toNat, ← hli_c0] using hk_n
                          have hidx_lt :
                              (((s0.core.lit_mark[(li.setWidth 64).toNat]'hli_lm).setWidth 32 -
                                2#32) >>> (1 : Nat)).toNat < 4 := by
                            have hlt := m7_p3_xor_idx_lt
                              (s0.core.lit_mark[(li.setWidth 64).toNat]'hli_lm) k
                              hm_ge_li hk_n_li
                            omega
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                            (fun x => (x, ())) (fun x => x.toNat < 16)
                            (fun _ pat' hp' => by
                              c0_hsteps!; exact hJi (pat', seen ||| _) hp')
                            (fun _ hJp => by
                              c0_hsplit
                              · c0_hsteps!
                                refine hJp _ (by
                                  rw [BitVec.toNat_or]
                                  refine Nat.or_lt_two_pow
                                    (show pat.toNat < 2 ^ 4 from hpat_lt) ?_
                                  have hbit := m7_p3_xor_bit_lt _ hidx_lt
                                  dsimp only [li] at hbit
                                  exact hbit)
                              · c0_hsteps!; exact hJp pat hpat_lt)
                  · c0_hsteps!; exact hJi (pat, seen) hpat_lt)
          · c0_hsteps!; exact hJ (pat, seen) hpat_lt)
    · c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun r => (r, ()))
        (fun r => r = 0xFFFFFFFF#32 ∨ r.toNat < 16)
        (fun _ r hr => by c0_hsteps!; exact hQ r hr)
        (fun _ hJ => by
          c0_hsplit
          · c0_hsteps!; exact hJ pat (Or.inr hpat_lt)
          · c0_hsteps!; exact hJ 0xFFFFFFFF#32 (Or.inl rfl))
  · intro L hL; c0_hsteps!
    exact hL sz.toNat (0#32, 0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp, by decide⟩

/-! ## 5. `full_bve_find_and_m7` -/

/-- Parametric `Func.wp` proof for `full_bve_find_and_m7`. -/
theorem full_bve_find_and_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveFindAndM7Spec a m Q X →
      Func.wp Γ full_bve_find_and_m7_body a m Q X := by
  rintro ⟨h, lit, lit_n, opp_n, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1088, hlit_lt, hln, hon, hp_ok, hn_ok, hm0, hQ⟩ :=
    fullBveFindAndM7Spec_elim hSpec
  have hpol_lt : (lit &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hpol : lit &&& 1#32 = 0#32 ∨ lit &&& 1#32 = 1#32 := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hpol_lt with h0 | h1
    · left; apply BitVec.eq_of_toNat_eq
      rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega
    · right; apply BitVec.eq_of_toNat_eq
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; exact h1
  have hcases : (((lit &&& 1#32) <<< 9).toNat = 0 ∧
      (512#32 - ((lit &&& 1#32) <<< 9)).toNat = 512 ∧
      (1024#32 + ((lit &&& 1#32) <<< 4)).toNat = 1024 ∧
      (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))).toNat = 1040) ∨
      (((lit &&& 1#32) <<< 9).toNat = 512 ∧
      (512#32 - ((lit &&& 1#32) <<< 9)).toNat = 0 ∧
      (1024#32 + ((lit &&& 1#32) <<< 4)).toNat = 1040 ∧
      (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))).toNat = 1024) := by
    rcases hpol with h0 | h1
    · left; rw [h0]; exact ⟨by decide, by decide, by decide, by decide⟩
    · right; rw [h1]; exact ⟨by decide, by decide, by decide, by decide⟩
  have hlo : ((lit &&& 1#32) <<< 9).toNat + lit_n.toNat ≤ 1024 := by
    rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  have hoo : (512#32 - ((lit &&& 1#32) <<< 9)).toNat + opp_n.toNat ≤ 1024 := by
    rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  have hlm1_b : 1024 ≤ (1024#32 + ((lit &&& 1#32) <<< 4)).toNat := by
    rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  have hlm2_b : (1024#32 + ((lit &&& 1#32) <<< 4)).toNat + 16 ≤ 1056 := by
    rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  have hom1_b : 1024 ≤ (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))).toNat := by
    rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  have hom2_b : (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))).toNat + 16 ≤ 1056 := by
    rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  clear hpol_lt hpol hcases
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  unfold Func.wp full_bve_find_and_m7_body
  c0_hsteps_nogrp
  generalize (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))) = opp_mask at *
  generalize (1024#32 + ((lit &&& 1#32) <<< 4)) = lit_mask at *
  generalize (512#32 - ((lit &&& 1#32) <<< 9)) = opp_off at *
  generalize ((lit &&& 1#32) <<< 9) = lit_off at *
  -- Loop 1: mark binary opposite occurrences (`j < opp_n`)
  refine wp_loop_group (ts := [i32, i32])
    (fun rem1 (bin_cnt, j, ()) m1 => ∃ lm1 : List (BitVec 8),
      let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
      lm1.length = 2 * c.max_vars ∧ j.toNat ≤ opp_n.toNat ∧ rem1 = opp_n.toNat - j.toNat ∧
      bin_cnt.toNat ≤ j.toNat ∧
      (bin_cnt = 0#32 → ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 = 0#8) ∧
      (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
        ∃ u < j.toNat, let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
          (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
      (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro L1 rem1 ⟨bin_cnt, j, ⟨⟩⟩ m1 hL1 ⟨lm1, hlm1, hj_le, rfl, hbc_le, hbc0, hmk1, hm1⟩
    c0_hsplit
    · have hj_lt : j.toNat < opp_n.toNat := hc
      have hoj_sc : ((opp_off + j).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
        rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
      have hoj_eq : ((opp_off + j).setWidth 64).toNat = opp_off.toNat + j.toNat := by
        rw [m6_zext32_toNat]; c0_bound
      let wo := s0.scratch.scratch_buf[((opp_off + j).setWidth 64).toNat]'hoj_sc
      have hwo_get : s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 = wo := by
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
          Option.getD_some]
        exact m6_getElem_congr hoj_eq.symm _ hoj_sc
      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8)) (fun x => (x.1, ()))
        (fun ⟨bc, lm⟩ mj => lm.length = 2 * c.max_vars ∧ bc.toNat ≤ j.toNat + 1 ∧
          (bc = 0#32 → ∀ z < 2 * c.max_vars, lm[z]?.getD 0#8 = 0#8) ∧
          (∀ z < 2 * c.max_vars, lm[z]?.getD 0#8 ≠ 0#8 →
            ∃ u < j.toNat + 1, let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
              (w &&& 0x80000000#32) ≠ 0#32 ∧ z = (w &&& 0x7FFFFFFF#32).toNat) ∧
          (FullMem c { s0 with core := { s0.core with lit_mark := lm } } ⋆ R) mj)
        (fun _ ⟨bc', lm'⟩ mj ⟨hlm', hbc', hbc0', hmk', hmj⟩ => by
          c0_hsteps!
          exact hL1 (opp_n.toNat - (j + 1#32).toNat) (bc', j + 1#32, ()) mj (by omega)
            ⟨lm', hlm', by omega, rfl, by omega, hbc0', fun z hz hnz => by
              obtain ⟨u, hu, hw⟩ := hmk' z hz hnz; exact ⟨u, by omega, hw⟩, hmj⟩)
        (fun J1 hJ1 => by
          have hkeep : J1 (bin_cnt, ()) m1 := by
            refine hJ1 (bin_cnt, lm1) m1
              ⟨hlm1, by omega, hbc0, fun z hz hnz => ?_, hm1⟩
            obtain ⟨u, hu, hw⟩ := hmk1 z hz hnz; exact ⟨u, by omega, hw⟩
          c0_hsplit
          · have hwo_bin : (wo &&& 0x80000000#32) ≠ 0#32 := hc
            have hot_lt : (wo &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
              have h1 := hn_ok j.toNat hj_lt; rw [hwo_get] at h1
              unfold FullBveEntryOkW at h1; rw [ite_eq_left hwo_bin] at h1; exact h1.1
            have hot_v : ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat < s0.core.vals.length := by
              rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
              (fun x => (x.1, ()))
              (fun ⟨bc, lm⟩ mj => lm.length = 2 * c.max_vars ∧ bc.toNat ≤ j.toNat + 1 ∧
                (bc = 0#32 → ∀ z < 2 * c.max_vars, lm[z]?.getD 0#8 = 0#8) ∧
                (∀ z < 2 * c.max_vars, lm[z]?.getD 0#8 ≠ 0#8 →
                  ∃ u < j.toNat + 1, let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
                    (w &&& 0x80000000#32) ≠ 0#32 ∧ z = (w &&& 0x7FFFFFFF#32).toNat) ∧
                (FullMem c { s0 with core := { s0.core with lit_mark := lm } } ⋆ R) mj)
              (fun _ ⟨bc', lm'⟩ mj ⟨hlm', hbc', hbc0', hmk', hmj⟩ => by
                c0_hsteps!
                exact hJ1 (bc', lm') mj ⟨hlm', hbc', hbc0', hmk', hmj⟩)
              (fun J1i hJ1i => by
                c0_hsplit
                · have hot_lm : ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm1.length := by
                    rw [hlm1, m6_zext32_toNat]; omega
                  c0_hsteps_nogrp
                  · have hbc1 : (bin_cnt + 1#32).toNat = bin_cnt.toNat + 1 := by c0_bound
                    let lm_n := lm1.set ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat 1#8
                    have hbc_ne : ∀ h : bin_cnt + 1#32 = 0#32, False := fun h => by
                      have h0 : (bin_cnt + 1#32).toNat = 0 := congrArg BitVec.toNat h
                      rw [hbc1] at h0; omega
                    c0_hsteps!
                    exact hJ1i (bin_cnt + 1#32, lm_n) _
                      ⟨by simp [lm_n, hlm1], by omega,
                        fun h => False.elim (hbc_ne h),
                        m7_p3_lm_set_at hlm1 (by rw [m6_zext32_toNat]; omega)
                          (fun z hz hnz => by
                            obtain ⟨u, hu, hw⟩ := hmk1 z hz hnz; exact ⟨u, by omega, hw⟩)
                          ⟨j.toNat, Nat.lt_succ_self _, by
                            rw [m6_zext32_toNat, hwo_get]; exact ⟨hwo_bin, rfl⟩⟩, hm⟩
                  · c0_hsteps!
                    exact hJ1i (bin_cnt, lm1) m1
                      ⟨hlm1, by omega, hbc0, fun z hz hnz => by
                        obtain ⟨u, hu, hw⟩ := hmk1 z hz hnz; exact ⟨u, by omega, hw⟩, hm1⟩
                · c0_hsteps!
                  exact hJ1i (bin_cnt, lm1) m1
                    ⟨hlm1, by omega, hbc0, fun z hz hnz => by
                      obtain ⟨u, hu, hw⟩ := hmk1 z hz hnz; exact ⟨u, by omega, hw⟩, hm1⟩)
          · exact hkeep)
    · -- End of Loop 1
      c0_hsplit
      · -- `bin_cnt < 1`: clear `lm` loop `j < opp_n` and return `false`
        c0_hsteps_nogrp
        refine wp_loop_group (ts := [i32])
          (fun rem2 (jc, ()) m2 => ∃ lm2 : List (BitVec 8),
            let s2 : FullState := { s0 with core := { s0.core with lit_mark := lm2 } }
            lm2.length = 2 * c.max_vars ∧ jc.toNat ≤ opp_n.toNat ∧ rem2 = opp_n.toNat - jc.toNat ∧
            (∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 ≠ 0#8 →
              ∃ u, jc.toNat ≤ u ∧ u < opp_n.toNat ∧
                let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
                (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
            (FullMem c s2 ⋆ R) m2)
          ?_ ?_
        · rintro L2 rem2 ⟨jc, ⟨⟩⟩ m2 hL2 ⟨lm2, hlm2, hjc_le, rfl, hrem2, hm2⟩
          c0_hsplit
          · have hjc_lt : jc.toNat < opp_n.toNat := hc
            have hoj_sc : ((opp_off + jc).setWidth 64).toNat <
                s0.scratch.scratch_buf.length := by
              rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
            have hoj_eq : ((opp_off + jc).setWidth 64).toNat = opp_off.toNat + jc.toNat := by
              rw [m6_zext32_toNat]; c0_bound
            let wc := s0.scratch.scratch_buf[((opp_off + jc).setWidth 64).toNat]'hoj_sc
            have hwc_get : s0.scratch.scratch_buf[opp_off.toNat + jc.toNat]?.getD 0#32 = wc := by
              rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                Option.getD_some]
              exact m6_getElem_congr hoj_eq.symm _ hoj_sc
            have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            refine wp_join_group (ts := [])
              (fun _ m2' => ∃ lm2' : List (BitVec 8),
                let s2' : FullState := { s0 with core := { s0.core with lit_mark := lm2' } }
                lm2'.length = 2 * c.max_vars ∧
                (∀ x < 2 * c.max_vars, lm2'[x]?.getD 0#8 ≠ 0#8 →
                  ∃ u, jc.toNat + 1 ≤ u ∧ u < opp_n.toNat ∧
                    let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
                    (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
                (FullMem c s2' ⋆ R) m2')
              (fun _ _ m2' ⟨lm2', hlm2', hrem2', hm2'⟩ => by
                c0_hsteps!
                exact hL2 (opp_n.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) m2' (by omega)
                  ⟨lm2', hlm2', by omega, rfl, fun y hy hnz => by
                    obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2' y hy hnz
                    exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm2'⟩)
              (fun _ hJ2 => by
                c0_hsplit
                · have hwc_bin : (wc &&& 0x80000000#32) ≠ 0#32 := hc
                  have hot_lt : (wc &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                    have h1 := hn_ok jc.toNat hjc_lt; rw [hwc_get] at h1
                    unfold FullBveEntryOkW at h1; rw [ite_eq_left hwc_bin] at h1; exact h1.1
                  have hot_lm : ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm2.length := by
                    rw [hlm2, m6_zext32_toNat]; omega
                  c0_hsteps!
                  refine hJ2 () _
                    ⟨lm2.set ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8, by simp [hlm2],
                     m7_p3_lm_clear_step hlm2 (by rw [m6_zext32_toNat]; omega) (fun y hy hnz => by
                       obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2 y hy hnz
                       rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                       · left; rw [m6_zext32_toNat, hyeq, hwc_get]
                       · right; exact ⟨u, by omega, hu2, hwu, hyeq⟩), hm⟩
                · c0_hsteps!
                  refine hJ2 () m2
                    ⟨lm2, hlm2, fun y hy hnz => by
                      obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2 y hy hnz
                      rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                      · have hwc_c0 :
                            s0.scratch.scratch_buf[(opp_off.toNat + jc.toNat) % 2 ^ 32]'(by
                              rw [hdw0.1.scratch_ok.scratch_buf_len,
                                Nat.mod_eq_of_lt (by omega)]; omega) = wc := by
                          rw [← hwc_get, List.getElem?_eq_getElem (by
                            rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                          exact m6_getElem_congr (Nat.mod_eq_of_lt (by omega)) _ _
                        have h0 := hc; rw [hwc_c0] at h0; rw [hwc_get] at hwu
                        exact absurd h0 hwu
                      · exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm2⟩)
          · have hclr2 : ∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 = 0#8 := fun x hx =>
              Classical.byContradiction fun hnz => by
                obtain ⟨u, hu1, hu2, _⟩ := hrem2 x hx hnz; omega
            have hdw2 := m7_p3_fullDenseInvW_lm_scr hdw0 hlm2 hclr2
              hdw0.1.scratch_ok.scratch_buf_len
            c0_hsteps!
            exact hQ false lm2 s0.scratch.scratch_buf m2 hdw2
              hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm2
        · intro L2 hL2; c0_hsteps!
          exact hL2 opp_n.toNat (0#32, ()) m1
            ⟨lm1, hlm1, Nat.zero_le _, by simp, fun x hx hnz => by
              obtain ⟨u, hu, hw⟩ := hmk1 x hx hnz; exact ⟨u, Nat.zero_le _, by omega, hw⟩,
             hm1⟩
      · -- Main search loop: scan `i < lit_n` with `wp_loop_break_group`
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32])
          (fun (found_i, _i_b, ()) mb => mb = m1 ∧
            (found_i = 0xFFFFFFFF#32 ∨ (found_i.toNat < lit_n.toNat ∧
              let wf := s0.scratch.scratch_buf[lit_off.toNat + found_i.toNat]?.getD 0#32;
              (wf &&& 0x80000000#32) = 0#32)))
          (fun rem_i (i, ()) mi => mi = m1 ∧ i.toNat ≤ lit_n.toNat ∧
            rem_i = lit_n.toNat - i.toNat)
          ?_ ?_ ?_
        · rintro _ ⟨found_i, _ib, ⟨⟩⟩ mb ⟨rfl, hfound⟩
          c0_hsteps_nogrp
          -- Clear `lm` loop (`j < opp_n`) before testing `found_i`
          refine wp_loop_group (ts := [i32])
            (fun rem2 (jc, ()) m2 => ∃ lm2 : List (BitVec 8),
              let s2 : FullState := { s0 with core := { s0.core with lit_mark := lm2 } }
              lm2.length = 2 * c.max_vars ∧ jc.toNat ≤ opp_n.toNat ∧ rem2 = opp_n.toNat - jc.toNat ∧
              (∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 ≠ 0#8 →
                ∃ u, jc.toNat ≤ u ∧ u < opp_n.toNat ∧
                  let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
                  (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
              (FullMem c s2 ⋆ R) m2)
            ?_ ?_
          · rintro L2 rem2 ⟨jc, ⟨⟩⟩ m2 hL2 ⟨lm2, hlm2, hjc_le, rfl, hrem2, hm2⟩
            c0_hsplit
            · have hjc_lt : jc.toNat < opp_n.toNat := hc
              have hoj_sc : ((opp_off + jc).setWidth 64).toNat <
                  s0.scratch.scratch_buf.length := by
                rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
              have hoj_eq : ((opp_off + jc).setWidth 64).toNat = opp_off.toNat + jc.toNat := by
                rw [m6_zext32_toNat]; c0_bound
              let wc := s0.scratch.scratch_buf[((opp_off + jc).setWidth 64).toNat]'hoj_sc
              have hwc_get : s0.scratch.scratch_buf[opp_off.toNat + jc.toNat]?.getD 0#32 = wc := by
                rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                  Option.getD_some]
                exact m6_getElem_congr hoj_eq.symm _ hoj_sc
              have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ m2' => ∃ lm2' : List (BitVec 8),
                  let s2' : FullState := { s0 with core := { s0.core with lit_mark := lm2' } }
                  lm2'.length = 2 * c.max_vars ∧
                  (∀ x < 2 * c.max_vars, lm2'[x]?.getD 0#8 ≠ 0#8 →
                    ∃ u, jc.toNat + 1 ≤ u ∧ u < opp_n.toNat ∧
                      let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
                      (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
                  (FullMem c s2' ⋆ R) m2')
                (fun _ _ m2' ⟨lm2', hlm2', hrem2', hm2'⟩ => by
                  c0_hsteps!
                  exact hL2 (opp_n.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) m2' (by omega)
                    ⟨lm2', hlm2', by omega, rfl, fun y hy hnz => by
                      obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2' y hy hnz
                      exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm2'⟩)
                (fun _ hJ2 => by
                  c0_hsplit
                  · have hwc_bin : (wc &&& 0x80000000#32) ≠ 0#32 := hc
                    have hot_lt : (wc &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                      have h1 := hn_ok jc.toNat hjc_lt; rw [hwc_get] at h1
                      unfold FullBveEntryOkW at h1; rw [ite_eq_left hwc_bin] at h1; exact h1.1
                    have hot_lm : ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm2.length := by
                      rw [hlm2, m6_zext32_toNat]; omega
                    c0_hsteps!
                    refine hJ2 () _
                      ⟨lm2.set ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8, by simp [hlm2],
                       m7_p3_lm_clear_step hlm2 (by rw [m6_zext32_toNat]; omega)
                         (fun y hy hnz => by
                           obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2 y hy hnz
                           rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                           · left; rw [m6_zext32_toNat, hyeq, hwc_get]
                           · right; exact ⟨u, by omega, hu2, hwu, hyeq⟩), hm⟩
                  · c0_hsteps!
                    refine hJ2 () m2
                      ⟨lm2, hlm2, fun y hy hnz => by
                        obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2 y hy hnz
                        rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                        · have hwc_c0 :
                              s0.scratch.scratch_buf[(opp_off.toNat + jc.toNat) % 2 ^ 32]'(by
                                rw [hdw0.1.scratch_ok.scratch_buf_len,
                                  Nat.mod_eq_of_lt (by omega)]; omega) = wc := by
                            rw [← hwc_get, List.getElem?_eq_getElem (by
                              rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                            exact m6_getElem_congr (Nat.mod_eq_of_lt (by omega)) _ _
                          have h0 := hc; rw [hwc_c0] at h0; rw [hwc_get] at hwu
                          exact absurd h0 hwu
                        · exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm2⟩)
            · have hclr2 : ∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 = 0#8 := fun x hx =>
                Classical.byContradiction fun hnz => by
                  obtain ⟨u, hu1, hu2, _⟩ := hrem2 x hx hnz; omega
              have hdw2 := m7_p3_fullDenseInvW_lm_scr hdw0 hlm2 hclr2
                hdw0.1.scratch_ok.scratch_buf_len
              c0_hsplit
              · c0_hsteps!
                exact hQ false lm2 s0.scratch.scratch_buf m2 hdw2
                  hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm2
              · have hfi_ne : found_i ≠ 0xFFFFFFFF#32 := hc
                obtain ⟨hfi_lt, hw_bin0⟩ := hfound.resolve_left hfi_ne
                have hfi_sc : ((lit_off + found_i).setWidth 64).toNat <
                    s0.scratch.scratch_buf.length := by
                  rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
                have hfi_eq : ((lit_off + found_i).setWidth 64).toNat =
                    lit_off.toNat + found_i.toNat := by
                  rw [m6_zext32_toNat]; c0_bound
                let wf := s0.scratch.scratch_buf[((lit_off + found_i).setWidth 64).toNat]'hfi_sc
                have hwf_get : s0.scratch.scratch_buf[lit_off.toNat + found_i.toNat]?.getD 0#32 =
                    wf := by
                  rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                    Option.getD_some]
                  exact m6_getElem_congr hfi_eq.symm _ hfi_sc
                have hent_f := hp_ok found_i.toNat hfi_lt
                dsimp only at hent_f hw_bin0; rw [hwf_get] at hent_f hw_bin0
                unfold FullBveEntryOkW at hent_f; rw [ite_eq_right (fun h => h hw_bin0)] at hent_f
                have hwf_f := hdw0.2.1.arena.refs_wf wf.toNat hent_f.1
                have hwf_bd : wf.toNat + 3 + fullArenaClauseSizeCore s0.core wf.toNat ≤
                    c.arena_cap := by
                  have := hwf_f.2.2.1; have := hwf_f.2.2.2.1; omega
                have hfsz_ge : 3 ≤ fullArenaClauseSizeCore s0.core wf.toNat := hwf_f.2.1
                have hwf2_ar : (wf.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                  rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, m6_zext32_toNat,
                    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                let fsz := s0.core.arena[(wf.setWidth 64 + 2#64).toNat]'hwf2_ar
                have hfsz_eq : fsz.toNat = fullArenaClauseSizeCore s0.core wf.toNat := by
                  unfold fsz fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                    Option.getD_some]
                  exact congrArg BitVec.toNat (m6_getElem_congr (by
                    rw [BitVec.toNat_add, m6_zext32_toNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega)]) _ _)
                have hfi_mod : (lit_off.toNat + found_i.toNat) % 2 ^ 32 <
                    s0.scratch.scratch_buf.length := by
                  rw [hdw0.1.scratch_ok.scratch_buf_len, Nat.mod_eq_of_lt (by omega)]; omega
                have hwf_c0 :
                    s0.scratch.scratch_buf[(lit_off.toNat + found_i.toNat) % 2 ^ 32]'hfi_mod =
                      wf := by
                  rw [← hwf_get, List.getElem?_eq_getElem (by
                    rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                  exact m6_getElem_congr (Nat.mod_eq_of_lt (by omega)) _ _
                have hfsz_c0_idx :
                    ((s0.scratch.scratch_buf[(lit_off.toNat + found_i.toNat) % 2 ^ 32]'hfi_mod
                        ).toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                      (wf.setWidth 64 + 2#64).toNat := by
                  rw [hwf_c0, BitVec.toNat_add, m6_zext32_toNat,
                    show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                    show BitVec.toNat (2#64 : BitVec 64) = 2 from rfl]
                have hfsz_c0 : s0.core.arena[
                    ((s0.scratch.scratch_buf[(lit_off.toNat + found_i.toNat) % 2 ^ 32]'hfi_mod
                        ).toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hfsz_c0_idx]; exact hwf2_ar) = fsz :=
                  m6_getElem_congr hfsz_c0_idx _ hwf2_ar
                c0_hsteps_nogrp
                -- Mark literals of `wf` (`k < fsz`) and compute `uniq_need`
                refine wp_loop_group (ts := [i32, i32])
                  (fun rem3 (uniq_need, k, ()) m3 => ∃ lm3 : List (BitVec 8),
                    let s3 : FullState := { s0 with core := { s0.core with lit_mark := lm3 } }
                    lm3.length = 2 * c.max_vars ∧ k.toNat ≤ fsz.toNat ∧ rem3 = fsz.toNat - k.toNat ∧
                    (∀ x < 2 * c.max_vars, lm3[x]?.getD 0#8 ≠ 0#8 →
                      (x ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                      (x ^^^ 1) ≠ lit.toNat) ∧
                    (FullMem c s3 ⋆ R) m3)
                  ?_ ?_
                · rintro L3 rem3 ⟨uniq_need, k, ⟨⟩⟩ m3 hL3 ⟨lm3, hlm3, hk_le, rfl, hmk3, hm3⟩
                  c0_hsplit
                  · have hk_lt : k.toNat < fsz.toNat := hc
                    have hwk_eq : (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                        wf.toNat + 3 + k.toNat := by
                      rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                        m6_zext32_toNat, BitVec.toNat_ofNat]
                      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                    have hwk : (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                        s0.core.arena.length := by
                      rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                    let lf := s0.core.arena[(wf.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hwk
                    have hlf_mem : lf.toNat ∈ fullArenaClauseLitsCore s0.core wf.toNat := by
                      rw [mem_fullArenaClauseLitsCore_iff (by
                        rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                      exact ⟨k.toNat, by omega,
                        congrArg BitVec.toNat (m6_getElem_congr hwk_eq.symm _ _)⟩
                    have hlf_lt : lf.toNat < 2 * s0.core.cur_vars :=
                      hdw0.2.1.arena.lits_lt wf.toNat hent_f.1 hent_f.2 _ hlf_mem
                    have hlf_v : (lf.setWidth 64).toNat < s0.core.vals.length := by
                      rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                    have hlfn_lt : lf.toNat ^^^ 1 < 2 * s0.core.cur_vars := by
                      have := fullInv_var_xor1 lf.toNat; omega
                    have hlfn_lm : ((lf ^^^ 1#32).setWidth 64).toNat < lm3.length := by
                      rw [hlm3, m6_zext32_toNat, BitVec.toNat_xor, BitVec.toNat_ofNat]
                      rw [show (1 : Nat) % 2 ^ 32 = 1 from rfl]; omega
                    have hlfn_inv : ((lf ^^^ 1#32).setWidth 64).toNat ^^^ 1 = lf.toNat := by
                      have h := congrArg BitVec.toNat
                        (by rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] :
                          (lf ^^^ 1#32) ^^^ 1#32 = lf)
                      rw [BitVec.toNat_xor, BitVec.toNat_ofNat,
                        show (1 : Nat) % 2 ^ 32 = 1 from rfl] at h
                      rw [m6_zext32_toNat]; exact h
                    have hlf_c0_idx :
                        ((s0.scratch.scratch_buf[(lit_off.toNat + found_i.toNat) %
                            2 ^ 32]'hfi_mod).toNat + BitVec.toNat (3 : BitVec 64) +
                          k.toNat) % 2 ^ 64 =
                          (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat := by
                      rw [hwf_c0, hwk_eq, show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    have hlf_c0 : s0.core.arena[
                        ((s0.scratch.scratch_buf[(lit_off.toNat + found_i.toNat) %
                            2 ^ 32]'hfi_mod).toNat + BitVec.toNat (3 : BitVec 64) +
                          k.toNat) % 2 ^ 64]'(by
                        rw [hlf_c0_idx]; exact hwk) = lf :=
                      m6_getElem_congr hlf_c0_idx _ hwk
                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
                      (fun x => (x.1, ()))
                      (fun ⟨_, lm⟩ mj => lm.length = 2 * c.max_vars ∧
                        (∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 →
                          (y ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                          (y ^^^ 1) ≠ lit.toNat) ∧
                        (FullMem c { s0 with core := { s0.core with lit_mark := lm } } ⋆ R) mj)
                      (fun _ ⟨un', lm'⟩ mj ⟨hlm', hmk', hmj⟩ => by
                        c0_hsteps!
                        exact hL3 (fsz.toNat - (k + 1#32).toNat)
                          (un', k + 1#32, ()) mj (by omega) ⟨lm', hlm', by omega, rfl, hmk', hmj⟩)
                      (fun _ hJ3 => by
                        c0_hsplit
                        · have hlf_ne : lf.toNat ≠ lit.toNat := by
                            intro h; exact hc (by rw [hlf_c0]; exact BitVec.eq_of_toNat_eq h)
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsteps!
                              exact hJ3 (uniq_need + 1#32,
                                lm3.set ((lf ^^^ 1#32).setWidth 64).toNat 1#8) _
                                ⟨by simp [hlm3],
                                 m7_p3_lm_set_at hlm3 (by rw [← hlm3]; exact hlfn_lm) hmk3
                                   ⟨by rw [hlfn_inv]; exact hlf_mem,
                                    by rw [hlfn_inv]; exact hlf_ne⟩, hm⟩
                            · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3, hmk3, hm3⟩
                          · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3, hmk3, hm3⟩
                        · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3, hmk3, hm3⟩)
                  · -- Match binaries (`j < opp_n`) against `lm3`
                    c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i32, i32])
                      (fun rem4 (j, matched, ()) m4 =>
                        ∃ (lm4 : List (BitVec 8)) (scr4 : List (BitVec 32)),
                          let s4 : FullState :=
                            { s0 with core := { s0.core with lit_mark := lm4 }
                                      scratch := { s0.scratch with scratch_buf := scr4 } }
                          lm4.length = 2 * c.max_vars ∧ scr4.length = c.scratch_cap ∧
                          j.toNat ≤ opp_n.toNat ∧ rem4 = opp_n.toNat - j.toNat ∧
                          (∀ x < 2 * c.max_vars, lm4[x]?.getD 0#8 ≠ 0#8 →
                            (x ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                            (x ^^^ 1) ≠ lit.toNat) ∧
                          (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
                            scr4[i]? = s0.scratch.scratch_buf[i]?) ∧
                          (FullMem c s4 ⋆ R) m4)
                      ?_ ?_
                    · rintro L4 rem4 ⟨j, matched, ⟨⟩⟩ m4 hL4
                        ⟨lm4, scr4, hlm4, hsc4, hj_le, rfl, hmk4, hout4, hm4⟩
                      c0_hsplit
                      · have hj_lt : j.toNat < opp_n.toNat := hc
                        have hoj_sc : ((opp_off + j).setWidth 64).toNat < scr4.length := by
                          rw [hsc4, m6_zext32_toNat]; c0_bound
                        have hoj_eq : ((opp_off + j).setWidth 64).toNat =
                            opp_off.toNat + j.toNat := by
                          rw [m6_zext32_toNat]; c0_bound
                        let wo := scr4[((opp_off + j).setWidth 64).toNat]'hoj_sc
                        have hwo_get : s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 =
                            wo := by
                          have hg := hout4 (opp_off.toNat + j.toNat) (by omega) (Or.inl (by omega))
                          have hoj' : opp_off.toNat + j.toNat < scr4.length := by omega
                          rw [List.getElem?_eq_getElem hoj'] at hg
                          rw [← hg, Option.getD_some]
                          exact m6_getElem_congr hoj_eq.symm hoj' hoj_sc
                        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32])
                          (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
                          (fun x => (x.1, ()))
                          (fun ⟨_, lm, scr⟩ mj => lm.length = 2 * c.max_vars ∧
                            scr.length = c.scratch_cap ∧
                            (∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 →
                              (y ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                              (y ^^^ 1) ≠ lit.toNat) ∧
                            (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
                              scr[i]? = s0.scratch.scratch_buf[i]?) ∧
                            (FullMem c { s0 with core := { s0.core with lit_mark := lm }
                                                 scratch :=
                                                   { s0.scratch with scratch_buf := scr } } ⋆
                              R) mj)
                          (fun _ ⟨mt', lm', scr'⟩ mj ⟨hlm', hsc', hmk', hout', hmj⟩ => by
                            c0_hsteps!
                            exact hL4 (opp_n.toNat - (j + 1#32).toNat)
                              (j + 1#32, mt', ()) mj (by omega)
                              ⟨lm', scr', hlm', hsc', by omega, rfl, hmk', hout', hmj⟩)
                          (fun _ hJ4 => by
                            c0_hsplit
                            · have hwo_bin : (wo &&& 0x80000000#32) ≠ 0#32 := hc
                              have hot_lt :
                                  (wo &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                                have h1 := hn_ok j.toNat hj_lt
                                rw [hwo_get] at h1
                                unfold FullBveEntryOkW at h1; rw [ite_eq_left hwo_bin] at h1
                                exact h1.1
                              have hot_v : ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                  s0.core.vals.length := by
                                rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                              have hot_lm : ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                  lm4.length := by
                                rw [hlm4, m6_zext32_toNat]; omega
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [i32])
                                (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
                                (fun x => (x.1, ()))
                                (fun ⟨_, lm, scr⟩ mj => lm.length = 2 * c.max_vars ∧
                                  scr.length = c.scratch_cap ∧
                                  (∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 →
                                    (y ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                                    (y ^^^ 1) ≠ lit.toNat) ∧
                                  (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
                                    scr[i]? = s0.scratch.scratch_buf[i]?) ∧
                                  (FullMem c { s0 with core := { s0.core with lit_mark := lm }
                                                       scratch :=
                                                         { s0.scratch with
                                                           scratch_buf := scr } } ⋆ R) mj)
                                (fun _ p mj h => by c0_hsteps!; exact hJ4 p mj h)
                                (fun _ hJ4i => by
                                  have hjm : (opp_mask + (j >>> (5 : Nat))).toNat <
                                      scr4.length := by
                                    have h1 := m7_p3_mask_lt_16 j (by omega)
                                    rw [hsc4, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                                    omega
                                  have hjm_idx :
                                      ((opp_mask + (j >>> (5 : Nat))).setWidth 64).toNat =
                                        opp_mask.toNat + j.toNat / 32 := by
                                    have h1 := m7_p3_mask_lt_16 j (by omega)
                                    rw [m6_zext32_toNat, BitVec.toNat_add,
                                      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                      show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                                  have hjm_64 :
                                      ((opp_mask + (j >>> (5 : Nat))).setWidth 64).toNat <
                                        scr4.length := by
                                    rw [m6_zext32_toNat]; exact hjm
                                  c0_hsplit
                                  ·
                                      c0_hsteps!
                                      dsimp only at hm
                                      exact hJ4i (matched + 1#32,
                                        lm4.set ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8,
                                        scr4.set ((opp_mask + (j >>> (5 : Nat))).setWidth 64).toNat
                                          _) _
                                        ⟨by simp [hlm4], by simp [hsc4],
                                         fun y hy hnz => by
                                           by_cases hy_eq :
                                               y = ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat
                                           · subst hy_eq
                                             rw [List.getElem?_set_self hot_lm,
                                               Option.getD_some] at hnz
                                             exact absurd rfl hnz
                                           · rw [List.getElem?_set_ne (Ne.symm hy_eq)] at hnz
                                             exact hmk4 y hy hnz,
                                         fun idx hidx hor => by
                                           rw [List.getElem?_set_ne (by
                                             rw [hjm_idx]
                                             have := m7_p3_mask_lt_16 j (by omega); omega)]
                                           exact hout4 idx hidx hor, hm⟩
                                  · c0_hsteps!; exact hJ4i (matched, lm4, scr4) m4
                                      ⟨hlm4, hsc4, hmk4, hout4, hm4⟩)
                            · c0_hsteps!; exact hJ4 (matched, lm4, scr4) m4
                                ⟨hlm4, hsc4, hmk4, hout4, hm4⟩)
                      · -- Unmark `wf` literals (`k < fsz`)
                        c0_hsteps_nogrp
                        refine wp_loop_group (ts := [i32])
                          (fun rem5 (ku, ()) m5 => ∃ lm5 : List (BitVec 8),
                            let s5 : FullState :=
                              { s0 with core := { s0.core with lit_mark := lm5 }
                                        scratch := { s0.scratch with scratch_buf := scr4 } }
                            lm5.length = 2 * c.max_vars ∧ ku.toNat ≤ fsz.toNat ∧
                            rem5 = fsz.toNat - ku.toNat ∧
                            (∀ x < 2 * c.max_vars, lm5[x]?.getD 0#8 ≠ 0#8 →
                              ∃ t, ku.toNat ≤ t ∧ t < fsz.toNat ∧
                                (x ^^^ 1) = (s0.core.arena[wf.toNat + 3 + t]?.getD 0#32).toNat ∧
                                (x ^^^ 1) ≠ lit.toNat) ∧
                            (FullMem c s5 ⋆ R) m5)
                          ?_ ?_
                        · rintro L5 rem5 ⟨ku, ⟨⟩⟩ m5 hL5 ⟨lm5, hlm5, hku_le, rfl, hrem5, hm5⟩
                          c0_hsplit
                          · have hku_lt : ku.toNat < fsz.toNat := hc
                            have hwk_eq : (wf.setWidth 64 + 3#64 + ku.setWidth 64).toNat =
                                wf.toNat + 3 + ku.toNat := by
                              rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                                m6_zext32_toNat, BitVec.toNat_ofNat]
                              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                            have hwk : (wf.setWidth 64 + 3#64 + ku.setWidth 64).toNat <
                                s0.core.arena.length := by
                              rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                            let lu := s0.core.arena[(wf.setWidth 64 + 3#64 + ku.setWidth 64).toNat]'
                              hwk
                            have hlu_get : s0.core.arena[wf.toNat + 3 + ku.toNat]?.getD 0#32 =
                                lu := by
                              rw [List.getElem?_eq_getElem (by
                                  rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                              exact m6_getElem_congr hwk_eq.symm _ hwk
                            have hlu_mem : lu.toNat ∈ fullArenaClauseLitsCore s0.core wf.toNat := by
                              rw [mem_fullArenaClauseLitsCore_iff (by
                                rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                              exact ⟨ku.toNat, by omega,
                                congrArg BitVec.toNat (m6_getElem_congr hwk_eq.symm _ _)⟩
                            have hlu_lt : lu.toNat < 2 * s0.core.cur_vars :=
                              hdw0.2.1.arena.lits_lt wf.toNat hent_f.1 hent_f.2 _ hlu_mem
                            have hlun_lt : lu.toNat ^^^ 1 < 2 * s0.core.cur_vars := by
                              have := fullInv_var_xor1 lu.toNat; omega
                            have hlun_lm : ((lu ^^^ 1#32).setWidth 64).toNat < lm5.length := by
                              rw [hlm5, m6_zext32_toNat, BitVec.toNat_xor, BitVec.toNat_ofNat]
                              rw [show (1 : Nat) % 2 ^ 32 = 1 from rfl]; omega
                            have hlun_inv : ((lu ^^^ 1#32).setWidth 64).toNat ^^^ 1 = lu.toNat := by
                              have h := congrArg BitVec.toNat
                                (by rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] :
                                  (lu ^^^ 1#32) ^^^ 1#32 = lu)
                              rw [BitVec.toNat_xor, BitVec.toNat_ofNat,
                                show (1 : Nat) % 2 ^ 32 = 1 from rfl] at h
                              rw [m6_zext32_toNat]; exact h
                            have hku1 : (ku + 1#32).toNat = ku.toNat + 1 := by c0_bound
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [])
                              (fun _ m5' => ∃ lm5' : List (BitVec 8),
                                let s5' : FullState :=
                                  { s0 with core := { s0.core with lit_mark := lm5' }
                                            scratch := { s0.scratch with scratch_buf := scr4 } }
                                lm5'.length = 2 * c.max_vars ∧
                                (∀ x < 2 * c.max_vars, lm5'[x]?.getD 0#8 ≠ 0#8 →
                                  ∃ t, ku.toNat + 1 ≤ t ∧ t < fsz.toNat ∧
                                    (x ^^^ 1) = (s0.core.arena[wf.toNat + 3 + t]?.getD 0#32).toNat ∧
                                    (x ^^^ 1) ≠ lit.toNat) ∧
                                (FullMem c s5' ⋆ R) m5')
                              (fun _ _ m5' ⟨lm5', hlm5', hrem5', hm5'⟩ => by
                                c0_hsteps!
                                exact hL5 (fsz.toNat - (ku + 1#32).toNat)
                                  (ku + 1#32, ()) m5' (by omega)
                                  ⟨lm5', hlm5', by omega, rfl, fun y hy hnz => by
                                    obtain ⟨t, ht1, ht2, hyeq, hne⟩ := hrem5' y hy hnz
                                    exact ⟨t, by omega, ht2, hyeq, hne⟩, hm5'⟩)
                              (fun _ hJ5 => by
                                c0_hsplit
                                · c0_hsteps!
                                  refine hJ5 () _
                                    ⟨lm5.set ((lu ^^^ 1#32).setWidth 64).toNat 0#8, by simp [hlm5],
                                     m7_p3_lm_clear_step hlm5 (by rw [← hlm5]; exact hlun_lm)
                                       (fun y hy hnz => by
                                         obtain ⟨t, ht1, ht2, hyeq, hne⟩ := hrem5 y hy hnz
                                         rcases Nat.eq_or_lt_of_le ht1 with rfl | hgt
                                         · left
                                           have hbv : (BitVec.ofNat 32 y) ^^^ 1#32 = lu := by
                                             apply BitVec.eq_of_toNat_eq
                                             rw [BitVec.toNat_xor, BitVec.toNat_ofNat,
                                               Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
                                               show (1 : Nat) % 2 ^ 32 = 1 from rfl, hyeq, hlu_get]
                                           have hbv2 : BitVec.ofNat 32 y = lu ^^^ 1#32 := by
                                             rw [← hbv, BitVec.xor_assoc, BitVec.xor_self,
                                               BitVec.xor_zero]
                                           have hbv3 := congrArg BitVec.toNat hbv2
                                           rw [BitVec.toNat_ofNat,
                                             Nat.mod_eq_of_lt (by omega)] at hbv3
                                           rw [m6_zext32_toNat, hbv3]
                                         · right; exact ⟨t, by omega, ht2, hyeq, hne⟩), hm⟩
                                · c0_hsteps!
                                  refine hJ5 () m5
                                    ⟨lm5, hlm5, fun y hy hnz => by
                                      obtain ⟨t, ht1, ht2, hyeq, hne⟩ := hrem5 y hy hnz
                                      rcases Nat.eq_or_lt_of_le ht1 with rfl | hgt
                                      · have hlu_idx :
                                            ((s0.scratch.scratch_buf[(lit_off.toNat +
                                                found_i.toNat) % 2 ^ 32]'hfi_mod).toNat +
                                              BitVec.toNat (3 : BitVec 64) + ku.toNat) % 2 ^ 64 =
                                              (wf.setWidth 64 + 3#64 + ku.setWidth 64).toNat := by
                                          rw [hwf_c0, hwk_eq,
                                            show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                            Nat.mod_eq_of_lt (by omega)]
                                        have hlu_eq : lu = lit := by
                                          have h0 := hc
                                          rw [← h0]; exact m6_getElem_congr hlu_idx.symm _ _
                                        have hc0 : (y ^^^ 1) = lit.toNat := by
                                          rw [hyeq, hlu_get, hlu_eq]
                                        exact absurd hc0 hne
                                      · exact ⟨t, by omega, ht2, hyeq, hne⟩, hm5⟩)
                          · have hfsz_le_ku : fsz.toNat ≤ ku.toNat := by
                              have h0 : ¬(ku.toNat < (s0.core.arena[
                                  ((s0.scratch.scratch_buf[(lit_off.toNat + found_i.toNat) %
                                      2 ^ 32]'hfi_mod).toNat +
                                    BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                  rw [hfsz_c0_idx]; exact hwf2_ar)).toNat) := hc
                              rw [hfsz_c0] at h0; omega
                            have hclr5 : ∀ x < 2 * c.max_vars, lm5[x]?.getD 0#8 = 0#8 :=
                              fun x hx => Classical.byContradiction fun hnz => by
                                obtain ⟨t, ht1, ht2, _⟩ := hrem5 x hx hnz; omega
                            have hdw5 := m7_p3_fullDenseInvW_lm_scr hdw0 hlm5 hclr5 hsc4
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := []) (fun _ mf => mf = m5)
                              (fun _ _ mf hmf => by
                                subst mf
                                c0_hsteps_nogrp
                                refine wp_loop_group (ts := [i32])
                                  (fun rem6 (kc, ()) m6 => ∃ scr6 : List (BitVec 32),
                                    let s6 : FullState :=
                                      { s0 with core := { s0.core with lit_mark := lm5 }
                                                scratch :=
                                                  { s0.scratch with scratch_buf := scr6 } }
                                    scr6.length = c.scratch_cap ∧ kc.toNat ≤ 16 ∧
                                    rem6 = 16 - kc.toNat ∧
                                    (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
                                      scr6[i]? = s0.scratch.scratch_buf[i]?) ∧
                                    (FullMem c s6 ⋆ R) m6)
                                  ?_ ?_
                                · rintro L6 rem6 ⟨kc, ⟨⟩⟩ m6 hL6
                                    ⟨scr6, hsc6, hkc_le, rfl, hout6, hm6⟩
                                  c0_hsplit
                                  · have hkc_lt : kc.toNat < 16 := hc
                                    have hokc : ((opp_mask + kc).setWidth 64).toNat <
                                        scr6.length := by
                                      rw [hsc6, m6_zext32_toNat, BitVec.toNat_add,
                                        Nat.mod_eq_of_lt (by omega)]; omega
                                    have hokc_b : 1024 ≤ ((opp_mask + kc).setWidth 64).toNat ∧
                                        ((opp_mask + kc).setWidth 64).toNat < 1056 := by
                                      rw [m6_zext32_toNat, BitVec.toNat_add,
                                        Nat.mod_eq_of_lt (by omega)]; omega
                                    have hkc1 : (kc + 1#32).toNat = kc.toNat + 1 := by
                                      c0_bound
                                    c0_hsteps!
                                    exact hL6 (16 - (kc + 1#32).toNat)
                                      (kc + 1#32, ()) _ (by omega)
                                      ⟨scr6.set ((opp_mask + kc).setWidth 64).toNat 0#32,
                                       by simp [hsc6], by omega, rfl,
                                       fun idx hidx hor => by
                                         rw [List.getElem?_set_ne (by
                                           rw [m6_zext32_toNat, BitVec.toNat_add,
                                             Nat.mod_eq_of_lt (by omega)]; omega)]
                                         exact hout6 idx hidx hor, hm⟩
                                  · have hdw6 := m7_p3_fullDenseInvW_lm_scr hdw0 hlm5 hclr5 hsc6
                                    c0_hsteps!
                                    exact hQ false lm5 scr6 m6 hdw6 hsc6 hout6 hm6
                                · intro L6 hL6; c0_hsteps!
                                  exact hL6 16 (0#32, ()) m5
                                    ⟨scr4, hsc4, Nat.zero_le _, by simp, hout4, hm5⟩)
                              (fun _ hJfin => by
                                c0_hsplit
                                · c0_hsplit
                                  · have hfim : (lit_mask + (found_i >>> (5 : Nat))).toNat <
                                        scr4.length := by
                                      have h1 := m7_p3_mask_lt_16 found_i (by omega)
                                      rw [hsc4, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                                      omega
                                    have hfim_idx :
                                        ((lit_mask + (found_i >>> (5 : Nat))).setWidth 64).toNat =
                                          lit_mask.toNat + found_i.toNat / 32 := by
                                      have h1 := m7_p3_mask_lt_16 found_i (by omega)
                                      rw [m6_zext32_toNat, BitVec.toNat_add,
                                        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                        show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                                    have hfim_bd : lit_mask.toNat + found_i.toNat / 32 < 1056 := by
                                      have := m7_p3_mask_lt_16 found_i (by omega); omega
                                    have h1056 : 1056 < scr4.length := by rw [hsc4]; omega
                                    have h1057 : 1057 < scr4.length := by rw [hsc4]; omega
                                    c0_hsteps!
                                    refine hQ true lm5 ?_ m ?_ ?_ ?_ ?_
                                    rotate_left 4
                                    · exact hm
                                    · exact m7_p3_fullDenseInvW_lm_scr hdw0 hlm5 hclr5
                                        (by simp [hsc4])
                                    · simp [hsc4]
                                    · intro idx hidx hor
                                      rw [hfim_idx,
                                        List.getElem?_set_ne
                                          (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                                        List.getElem?_set_ne
                                          (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                                        List.getElem?_set_ne (by omega)]
                                      exact hout4 idx hidx hor
                                  · c0_hsteps!; exact hJfin () m5 rfl
                                · c0_hsteps!; exact hJfin () m5 rfl)
                        · intro L5 hL5; c0_hsteps!
                          exact hL5 fsz.toNat (0#32, ()) m4
                            ⟨lm4, hlm4, Nat.zero_le _, by simp, fun x hx hnz => by
                              obtain ⟨hm_mem, hm_ne⟩ := hmk4 x hx hnz
                              rw [mem_fullArenaClauseLitsCore_iff (by
                                rw [hdw0.1.core_ok.arena_len_arr]; omega)] at hm_mem
                              obtain ⟨t, ht, hxt⟩ := hm_mem
                              exact ⟨t, Nat.zero_le _, by omega, by
                                rw [List.getElem?_eq_getElem (by
                                  rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                                exact hxt.symm, hm_ne⟩, hm4⟩
                    · intro L4 hL4; c0_hsteps!
                      exact hL4 opp_n.toNat (0#32, 0#32, ()) m3
                        ⟨lm3, s0.scratch.scratch_buf, hlm3, hdw0.1.scratch_ok.scratch_buf_len,
                         Nat.zero_le _, by simp, hmk3, fun _ _ _ => rfl, hm3⟩
                · intro L3 hL3; c0_hsteps!
                  exact hL3 fsz.toNat (0#32, 0#32, ()) m2
                    ⟨lm2, hlm2, Nat.zero_le _, by simp, fun x hx hnz =>
                      absurd (hclr2 x hx) hnz, hm2⟩
          · intro L2 hL2; c0_hsteps!
            exact hL2 opp_n.toNat (0#32, ()) mb
              ⟨lm1, hlm1, Nat.zero_le _, by simp, fun x hx hnz => by
                obtain ⟨u, hu_lt, hwu, hxe⟩ := hmk1 x hx hnz
                exact ⟨u, Nat.zero_le _, by omega, hwu, hxe⟩, hm1⟩
        · -- Loop body (`i < lit_n`) for `wp_loop_break_group`
          rintro Bi Li rem_i ⟨i, ⟨⟩⟩ mi hBi hLi ⟨hmi, hi_le, rfl⟩
          subst mi
          c0_hsplit
          · have hi_lt : i.toNat < lit_n.toNat := hc
            have hli_sc : ((lit_off + i).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
              rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
            have hli_eq : ((lit_off + i).setWidth 64).toNat = lit_off.toNat + i.toNat := by
              rw [m6_zext32_toNat]; c0_bound
            let wi := s0.scratch.scratch_buf[((lit_off + i).setWidth 64).toNat]'hli_sc
            have hwi_get : s0.scratch.scratch_buf[lit_off.toNat + i.toNat]?.getD 0#32 = wi := by
              rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                Option.getD_some]
              exact m6_getElem_congr hli_eq.symm _ hli_sc
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32]) (fun _ mi' => mi' = m1)
              (fun _ _ mi' hmi' => by
                subst mi'; c0_hsteps!
                exact hLi (lit_n.toNat - (i + 1#32).toNat) (i + 1#32, ()) m1
                  (by omega) ⟨rfl, by omega, rfl⟩)
              (fun _ hJi => by
                c0_hstep; c0_hstep; c0_hsplit
                · have hwi_bin0 : (wi &&& 0x80000000#32) = 0#32 := hc
                  have hent_i := hp_ok i.toNat hi_lt
                  rw [hwi_get] at hent_i
                  unfold FullBveEntryOkW at hent_i
                  rw [ite_eq_right (fun h => h hwi_bin0)] at hent_i
                  have hwf_i := hdw0.2.1.arena.refs_wf wi.toNat hent_i.1
                  have hwi_bd : wi.toNat + 3 + fullArenaClauseSizeCore s0.core wi.toNat ≤
                      c.arena_cap := by
                    have := hwf_i.2.2.1; have := hwf_i.2.2.2.1; omega
                  have hsz_ge : 3 ≤ fullArenaClauseSizeCore s0.core wi.toNat := hwf_i.2.1
                  have hwi2_ar : (wi.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                    rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, m6_zext32_toNat,
                      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                  let sz := s0.core.arena[(wi.setWidth 64 + 2#64).toNat]'hwi2_ar
                  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core wi.toNat := by
                    unfold sz fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                      Option.getD_some]
                    exact congrArg BitVec.toNat (m6_getElem_congr (by
                      rw [BitVec.toNat_add, m6_zext32_toNat, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by omega)]) _ _)
                  c0_hsteps_nogrp
                  refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
                    (fun _ mb => mb = m1)
                    (fun rem_k (need, k, ()) mk => mk = m1 ∧ k.toNat ≤ sz.toNat ∧
                      rem_k = sz.toNat - k.toNat)
                    ?_ ?_ ?_
                  · rintro _ ⟨ok_b, need_b, _, ⟨⟩⟩ mb hmb
                    subst mb
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsteps!; exact hBi (i, i, ()) m1
                          ⟨rfl, Or.inr ⟨hi_lt, by rw [hwi_get]; exact hwi_bin0⟩⟩
                      · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl
                    · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl
                  · rintro Bk Lk rem_k ⟨need, k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                    subst mk
                    c0_hsplit
                    · have hk_lt : k.toNat < sz.toNat := hc
                      have hwk_eq : (wi.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                          wi.toNat + 3 + k.toNat := by
                        rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                          m6_zext32_toNat, BitVec.toNat_ofNat]
                        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      have hwk : (wi.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                          s0.core.arena.length := by
                        rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                      let l := s0.core.arena[(wi.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hwk
                      have hl_lt : l.toNat < 2 * s0.core.cur_vars := by
                        have hmem : l.toNat ∈ fullArenaClauseLitsCore s0.core wi.toNat := by
                          rw [mem_fullArenaClauseLitsCore_iff (by
                            rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                          exact ⟨k.toNat, by omega,
                            congrArg BitVec.toNat (m6_getElem_congr hwk_eq.symm _ _)⟩
                        exact hdw0.2.1.arena.lits_lt wi.toNat hent_i.1 hent_i.2 _ hmem
                      have hl_v : (l.setWidth 64).toNat < s0.core.vals.length := by
                        rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                      have hln_lm : ((l ^^^ 1#32).setWidth 64).toNat < lm1.length := by
                        rw [hlm1, m6_zext32_toNat]
                        change l.toNat ^^^ 1 < 2 * c.max_vars
                        have := fullInv_var_xor1 l.toNat; omega
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      c0_hsteps_nogrp
                      refine wp_join_state_pure (ts := [.bool, i32]) (α := BitVec 32)
                        (fun nd' => (true, nd', ())) (fun _ => True)
                        (fun _ nd' _ => by
                          c0_hsteps!
                          exact hLk (sz.toNat - (k + 1#32).toNat) (nd', k + 1#32, ())
                            m1 (by omega) ⟨rfl, by omega, rfl⟩)
                        (fun _ hJk => by
                          c0_hsplit
                          · c0_hsteps_nogrp
                            · c0_hsteps!; exact hBk (false, need, k, ()) m1 rfl
                            · refine wp_join_state_pure (ts := [.bool, i32])
                                (α := BitVec 32) (fun nd' => (true, nd', ()))
                                (fun _ => True)
                                (fun _ nd' _ => by c0_hsteps!; exact hJk nd' trivial)
                                (fun _ hJkn => by
                                  c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps!; exact hBk (false, need, k, ()) m1 rfl
                                    · c0_hsteps!; exact hJkn (need + 1#32) trivial
                                  · c0_hsteps!; exact hJkn need trivial)
                          · c0_hsteps!; exact hJk need trivial)
                    · c0_hsteps!; exact hBk (true, need, k, ()) m1 rfl
                  · intro _ Lk _ hLk; c0_hsteps!
                    exact hLk sz.toNat (0#32, 0#32, ()) m1 ⟨rfl, Nat.zero_le _, by simp⟩
                · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl)
          · c0_hsteps!; exact hBi (0xFFFFFFFF#32, i, ()) m1 ⟨rfl, Or.inl rfl⟩
        · intro _ Li _ hLi; c0_hsteps!
          exact hLi lit_n.toNat (0#32, ()) m1 ⟨rfl, Nat.zero_le _, by simp⟩
  · intro L1 hL1; c0_hsteps!
    exact hL1 opp_n.toNat (0#32, 0#32, ()) m0
      ⟨s0.core.lit_mark, hdw0.1.core_ok.lit_mark_len, Nat.zero_le _, by simp,
       Nat.zero_le _, fun _ => hdw0.2.2.1.2, fun x hx hnz =>
         absurd (hdw0.2.2.1.2 x hx) hnz, hm0⟩

end LeanQbe.T.Examples.Kissat.FullM7BveGates
