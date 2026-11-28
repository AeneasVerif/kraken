/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Walk.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Src.Walk

import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Walk WP Proofs — Part 2b (`Proof.Walk.Wp2b`)

Proves canonical WP correctness for literal flipping:
1. `full_walk_flip_m7_wp` (`fullWalkFlipM7Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk

open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Walk
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Walk.Spec

open scoped FullArenaTactics WalkMemTactics

/-! ## Shared Helpers -/

private theorem walk2_lengthsOk_set_sb {c : FullCfg} {s : FullState} {k : Nat} {v : BitVec 32}
    (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set k v } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    scratch_buf_len := by simp [hlen.scratch_ok.scratch_buf_len] }⟩

private theorem walk2_lengthsOk_set_sb2 {c : FullCfg} {s : FullState} {k1 k2 : Nat}
    {v1 v2 : BitVec 32} (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set k1 v1).set k2 v2 } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    scratch_buf_len := by simp [hlen.scratch_ok.scratch_buf_len] }⟩

private theorem walk2_lengthsOk_set_wks {c : FullCfg} {s : FullState} {k1 k2 k3 : Nat}
    {w1 w2 w3 : BitVec 32} (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        work_stk1 := s.scratch.work_stk1.set k1 w1
        work_stk2 := (s.scratch.work_stk2.set k2 w2).set k3 w3 } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    work_stk1_len := by simp [hlen.scratch_ok.work_stk1_len]
    work_stk2_len := by simp [hlen.scratch_ok.work_stk2_len] }⟩

private theorem walk2_lengthsOk_set_wv2 {c : FullCfg} {s : FullState} {k1 k2 : Nat}
    {v1 v2 : BitVec 8} (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        walk_vals := (s.scratch.walk_vals.set k1 v1).set k2 v2 } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    walk_vals_len := by simp [hlen.scratch_ok.walk_vals_len] }⟩

private theorem walkTblExpsOk_imm1080 {s : FullState} (hok : WalkTblExpsOk s)
    {d : BitVec 64} (hd : d.toNat / 4 = 2160)
    {hi_len : d.toNat / 4 + 1 < s.scratch.scratch_buf.length} :
    (pack64 s.scratch.scratch_buf[d.toNat / 4]
      s.scratch.scratch_buf[d.toNat / 4 + 1]).toNat ≤ 1080 := by
  simp only [hd]
  exact walkTblExpsOk_to_lt1080 hok (hi_len := by omega)

private theorem walkTblExpsOk_store_imm {s : FullState} {d v : BitVec 64}
    (hne : d.toNat / 4 ≠ 2160 ∧ d.toNat / 4 ≠ 2161 ∧
      d.toNat / 4 + 1 ≠ 2160 ∧ d.toNat / 4 + 1 ≠ 2161)
    (hok : WalkTblExpsOk s) :
    WalkTblExpsOk { s with scratch := { s.scratch with
      scratch_buf := (s.scratch.scratch_buf.set (d.toNat / 4) (v.setWidth 32)).set
        (d.toNat / 4 + 1) ((v >>> 32).setWidth 32) } } := by
  unfold WalkTblExpsOk at hok ⊢
  rcases hne with ⟨h0, h1, h2, h3⟩
  rw [List.getElem?_set_ne h2, List.getElem?_set_ne h0,
    List.getElem?_set_ne h3, List.getElem?_set_ne h1]
  exact hok

private theorem walkScrPrefixPres_set_ge2 {s : FullState} {k1 k2 : Nat}
    {v1 v2 : BitVec 32} (hk1 : 2200 ≤ k1) (hk2 : 2200 ≤ k2) :
    WalkScrPrefixPres s
      { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set k1 v1).set k2 v2 } } :=
  fun j hj => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem walk2_rem_eq {scap : Nat} {ncl : BitVec 64}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap) :
    (BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)).toNat =
      scap - (2200 + 5 * ncl.toNat) := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega)
  bv_omega

private theorem walk2_sat_idx {ncl x : BitVec 64} (hn : 2200 + 2 * ncl.toNat + x.toNat < 2 ^ 64) :
    ((2200#64 + (ncl <<< (1 : Nat))) + x).toNat = 2200 + 2 * ncl.toNat + x.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega); bv_omega

private theorem walk2_upos_idx {ncl x : BitVec 64}
    (hn : 2200 + 3 * ncl.toNat + x.toNat < 2 ^ 64) :
    ((2200#64 + (ncl <<< (1 : Nat)) + ncl) + x).toNat = 2200 + 3 * ncl.toNat + x.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega); bv_omega

private theorem walk2_uns_idx {ncl x : BitVec 64}
    (hn : 2200 + 4 * ncl.toNat + x.toNat < 2 ^ 64) :
    ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) + x).toNat = 2200 + 4 * ncl.toNat + x.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega); bv_omega

private theorem walk2_uns_sub1_idx {ncl cu : BitVec 64}
    (hn : 2200 + 4 * ncl.toNat + cu.toNat < 2 ^ 64) (hcu : 1 ≤ cu.toNat) :
    ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) + cu - 1#64).toNat =
      2200 + 4 * ncl.toNat + cu.toNat - 1 := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega); bv_omega

private theorem walk2_lim_avail {scap : Nat} {ncl : BitVec 64} {mark : BitVec 32}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hm : mark.toNat ≤
      (BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)).toNat) :
    mark.toNat +
      ((BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)) -
        mark.setWidth 64).toNat ≤ scap - (2200 + 5 * ncl.toNat) := by
  have hrem := walk2_rem_eq hsc h5
  have hz := bv32_lit_toNat_mod64 mark
  bv_omega

private theorem walk2_lim_trc {scap : Nat} {ncl : BitVec 64} {mark trc : BitVec 32}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hm : mark.toNat ≤
      (BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)).toNat)
    (ht : ¬ ((BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)) -
        mark.setWidth 64).toNat < trc.toNat) :
    mark.toNat + trc.toNat ≤ scap - (2200 + 5 * ncl.toNat) := by
  have hrem := walk2_rem_eq hsc h5
  have hz1 := bv32_lit_toNat_mod64 mark
  have hz2 := bv32_lit_toNat_mod64 trc
  bv_omega

private theorem walk2_lim_avail_exp {scap : Nat} {ncl : BitVec 64} {mark : BitVec 32}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hm : mark.toNat ≤ (2 ^ 64 - (BitVec.toNat (2200#64) + 2 * ncl.toNat + ncl.toNat +
        ncl.toNat + ncl.toNat) % 2 ^ 64 + scap) % 2 ^ 64) :
    mark.toNat +
      ((BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)) -
        mark.setWidth 64).toNat ≤ scap - (2200 + 5 * ncl.toNat) := by
  have h2200 : BitVec.toNat (2200#64) = 2200 := rfl
  rw [h2200] at hm
  have hrem := walk2_rem_eq hsc h5
  have hm' : mark.toNat ≤ scap - (2200 + 5 * ncl.toNat) := by omega
  have hz := bv32_lit_toNat_mod64 mark
  bv_omega

private theorem walk2_lim_trc_exp {scap : Nat} {ncl : BitVec 64} {mark : BitVec 32}
    {trc : Nat} (_hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hm : mark.toNat ≤ (2 ^ 64 - (BitVec.toNat (2200#64) + 2 * ncl.toNat + ncl.toNat +
        ncl.toNat + ncl.toNat) % 2 ^ 64 + scap) % 2 ^ 64)
    (ht : ¬ (2 ^ 64 - mark.toNat + (2 ^ 64 - (BitVec.toNat (2200#64) + 2 * ncl.toNat +
        ncl.toNat + ncl.toNat + ncl.toNat) % 2 ^ 64 + scap)) % 2 ^ 64 < trc) :
    mark.toNat + trc ≤ scap - (2200 + 5 * ncl.toNat) := by
  have h2200 : BitVec.toNat (2200#64) = 2200 := rfl
  rw [h2200] at hm ht
  have hm' : mark.toNat ≤ scap - (2200 + 5 * ncl.toNat) := by omega
  omega

private theorem bv32_xor1_toNat (x : BitVec 32) : x.toNat ^^^ 1 = (x ^^^ 1#32).toNat := by
  rw [BitVec.toNat_xor]; rfl

private theorem bv32_mask_lt (w : BitVec 32) : (w &&& 0x7FFFFFFF#32).toNat < 2 ^ 31 := by
  have h : (w &&& 0x7FFFFFFF#32).toNat ≤ (0x7FFFFFFF#32 : BitVec 32).toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  have h1 : (0x7FFFFFFF#32 : BitVec 32).toNat = 2147483647 := rfl
  omega


private theorem bv64_shl_one (x : BitVec 64) : x <<< (1#64 : BitVec 64) = x <<< (1 : Nat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]

private theorem bv64_pack_low32_and {hi lo : BitVec 64} {n : Nat}
    (hlo : lo.toNat ≤ n) (hn : n < 2 ^ 32) :
    (((hi <<< (32 : Nat)) ||| (lo &&& 0xFFFFFFFF#64)) &&& 0xFFFFFFFF#64).toNat ≤ n := by
  have hlt : lo.toNat < 2 ^ 32 := by omega
  have heq : ((hi <<< (32 : Nat)) ||| (lo &&& 0xFFFFFFFF#64)) &&& 0xFFFFFFFF#64 = lo := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi_lt
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    by_cases h32 : i < 32
    · have h1 : (0xFFFFFFFF#64 : BitVec 64).getLsbD i = true := by
        rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl,
          Nat.testBit_two_pow_sub_one]; simp [hi_lt, h32]
      have h2 : ¬ (32 ≤ i) := by omega
      simp [h1, h2]
    · have h1 : (0xFFFFFFFF#64 : BitVec 64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl,
          Nat.testBit_two_pow_sub_one]; simp [hi_lt, h32]
      have h2 : lo.getLsbD i = false := by
        rw [BitVec.getLsbD_eq_getElem, BitVec.getElem_eq_testBit_toNat]
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega)
            (by omega)))
        · exact hi_lt
      simp [h1, h2]
  rw [heq]; exact hlo

private theorem list_getElem?_set_ne_lt {xs : List (BitVec 32)} {i j : Nat} {v : BitVec 32}
    (hj : j < 2200) (hi : 2200 ≤ i) : (xs.set i v)[j]? = xs[j]? :=
  List.getElem?_set_ne (by omega)

private theorem walk2_sat_ge2200 (ncl x : BitVec 64)
    (h : 2200 + 2 * ncl.toNat + x.toNat < 2 ^ 64) :
    2200 ≤ ((2200#64 + (ncl <<< (1 : Nat))) + x).toNat := by
  rw [walk2_sat_idx h]; omega

private theorem walk2_upos_ge2200 (ncl x : BitVec 64)
    (h : 2200 + 3 * ncl.toNat + x.toNat < 2 ^ 64) :
    2200 ≤ ((2200#64 + (ncl <<< (1 : Nat)) + ncl) + x).toNat := by
  rw [walk2_upos_idx h]; omega

private theorem walk2_uns_ge2200 (ncl x : BitVec 64)
    (h : 2200 + 4 * ncl.toNat + x.toNat < 2 ^ 64) :
    2200 ≤ ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) + x).toNat := by
  rw [walk2_uns_idx h]; omega

/-! ## 2. `full_walk_flip_m7` -/

theorem full_walk_flip_m7_wp (Γ : Env) :
    ∀ a m Q X, flipSpec a m Q X →
      Func.wp Γ full_walk_flip_m7_body a m Q X := by
  intro a m Q X hs
  unfold flipSpec at hs
  have hs' := walk_fullContract_of_safetySlice hs
    (fun c (h, _) _ => h = c.hdr)
    (fun _ (_, _, ncl, _, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ WalkScrPrefixPres s s' ∧ (r &&& 0xFFFFFFFF#64).toNat ≤ ncl.toNat)
    (fun _ _ _ _ _ hh => hh) (fun _ _ _ _ _ _ hc _ ⟨he, hp, hle⟩ => ⟨hc, he, hp, hle⟩)
  rcases a with ⟨h, flip_lit, ncl, ulen, ⟨⟩⟩
  rcases hs' with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmaxv := c.hmaxv; have hscr := c.hscr
  unfold dimacsBound at hmaxv hscr
  unfold Func.wp full_walk_flip_m7_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun _ m1 => m = m1) ?_ ?_
  · rintro Jr0 ⟨⟩ _ rfl; rw [Blocks.get_here]
    refine wp_join_group (ts := [i64]) (fun (r, ()) m1 => m = m1 ∧ r.toNat ≤ ncl.toNat) ?_ ?_
    · rintro Jr ⟨r, ⟨⟩⟩ _ ⟨rfl, hr⟩; rw [Blocks.get_here]
      exact hQ (r, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, walkScrPrefixPres_refl s, by
        dsimp only
        have : (r &&& 0xFFFFFFFF#64).toNat ≤ r.toNat := by
          rw [BitVec.toNat_and]; exact Nat.and_le_left
        omega⟩ hm
    · intro Jr hJr; c0_hsteps_nogrp
      · exact hJr (ncl, ()) m ⟨rfl, Nat.le_refl _⟩
      · exact hJr (ulen, ()) m ⟨rfl, by c0_bound⟩
  · intro Jr0 hJr0
    c0_hsteps_nogrp
    · exact hJr0 () m rfl
    · exact hJr0 () m rfl
    · exact hJr0 () m rfl
    · exact hJr0 () m rfl
    · exact hJr0 () m rfl
    · exact hJr0 () m rfl
    have hcv_pos : 0 < s.core.cur_vars := by
        have hlt : s.core.cur_vars < 2 ^ 64 := by have := hlen.core_ok.cur_vars_le; omega
        have hne : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64 := by c0_bound
        exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
    have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    have hfl_lt : flip_lit.toNat < 2 * s.core.cur_vars := by
      have hz := bv32_lit_toNat_mod64 flip_lit; c0_bound
    have hnl_lt : (flip_lit ^^^ 1#32).toNat < 2 * s.core.cur_vars := bv32_lit_neg_lt hfl_lt
    have hncl_pos : 0 < ncl.toNat := by
      have hne : ncl ≠ 0#64 := by c0_bound
      exact Nat.pos_of_ne_zero fun h0 => hne (BitVec.eq_of_toNat_eq (by simp [h0]))
    have hncl_le : ncl.toNat ≤ c.scratch_cap := by c0_bound
    have h5ncl : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
      have hc1 : ¬ (BitVec.ofNat 64 c.scratch_cap).toNat < (2200#64 + 5#64 * ncl).toNat := by
        c0_bound
      have hbv : (2200#64 + 5#64 * ncl).toNat = 2200 + 5 * ncl.toNat := by bv_omega
      rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc1; omega
    have hwv_len := hlen.scratch_ok.walk_vals_len
    have htmk_len := hlen.scratch_ok.tarjan_mark_len
    have htrc_len := hlen.scratch_ok.tarjan_reach_len
    have hsb_len := hlen.scratch_ok.scratch_buf_len
    have hsat_eq : (2200#64 + (ncl <<< (1 : Nat))).toNat = 2200 + 2 * ncl.toNat := by
      rw [BitVec.toNat_add, bv64_shl1_toNat_lt (by omega)]; bv_omega
    have hwv1 : flip_lit.toNat < s.scratch.walk_vals.length := by rw [hwv_len]; omega
    have hwv2 : (flip_lit ^^^ 1#32).toNat <
        (s.scratch.walk_vals.set flip_lit.toNat 1#8).length := by
      rw [List.length_set, hwv_len]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun (cu, ()) m1 => m = m1 ∧ cu.toNat ≤ ncl.toNat) ?_ ?_
    · rintro Jcu ⟨cu, ⟨⟩⟩ _ ⟨rfl, hcu⟩; rw [Blocks.get_here]
      have hwv1' : (flip_lit.setWidth 64).toNat < s.scratch.walk_vals.length := by
        rw [bv32_lit_toNat_mod64]; exact hwv1
      have hwv2' : ((flip_lit ^^^ 1#32).setWidth 64).toNat <
          (s.scratch.walk_vals.set (flip_lit.setWidth 64).toNat 1#8).length := by
        rw [List.length_set, bv32_lit_toNat_mod64, hwv_len]; omega
      c0_hsteps_nogrp_nobound
      obtain ⟨st0, hcore0, hlen0, hext0, hpre0, hm0⟩ :
          ∃ st0 : FullState, PreservesCoreSlice FullState.core s st0 ∧ FullState.LengthsOk c st0 ∧
            FullExtScratchPres s st0 ∧ WalkScrPrefixPres s st0 ∧ (FullMem c st0 ⋆ R) m :=
        ⟨{ s with scratch := { s.scratch with
          walk_vals := (s.scratch.walk_vals.set (flip_lit.setWidth 64).toNat 1#8).set
            ((flip_lit ^^^ 1#32).setWidth 64).toNat 255#8 } },
          rfl, walk2_lengthsOk_set_wv2 hlen, ⟨rfl, rfl⟩, walkScrPrefixPres_refl s, hm⟩
      clear hm
      have hfl_tmk : flip_lit.toNat < st0.scratch.tarjan_mark.length := by
        rw [hlen0.scratch_ok.tarjan_mark_len]; omega
      have hfl_trc : flip_lit.toNat < st0.scratch.tarjan_reach.length := by
        rw [hlen0.scratch_ok.tarjan_reach_len]; omega
      have hnl_tmk : (flip_lit ^^^ 1#32).toNat < st0.scratch.tarjan_mark.length := by
        rw [hlen0.scratch_ok.tarjan_mark_len]; omega
      have hnl_trc : (flip_lit ^^^ 1#32).toNat < st0.scratch.tarjan_reach.length := by
        rw [hlen0.scratch_ok.tarjan_reach_len]; omega
      have hfl_tmk_sw : (flip_lit.setWidth 64).toNat < st0.scratch.tarjan_mark.length := by
        rw [bv32_lit_toNat_mod64]; exact hfl_tmk
      have hnl_tmk_sw : ((flip_lit ^^^ 1#32).setWidth 64).toNat <
          st0.scratch.tarjan_mark.length := by
        rw [bv32_lit_toNat_mod64]; exact hnl_tmk
      try c0_hsteps_nogrp_nobound
      refine wp_join_safety_slice (ts := [i64, i64]) (fullSafetySlice c) st0 R
        (fun _ => True) trivial (fun st1 (cu1, _, ()) => FullExtScratchPres s st1 ∧
          WalkScrPrefixPres s st1 ∧ st1.scratch.tarjan_mark = st0.scratch.tarjan_mark ∧
          st1.scratch.tarjan_reach = st0.scratch.tarjan_reach ∧ cu1.toNat ≤ ncl.toNat) ?_ ?_
      · rintro J1 st1 ⟨cu1, _, ⟨⟩⟩ m1 hcore1 hlen1 _
          ⟨hext1, hpre1, htmk1_eq, htrc1_eq, hcu1⟩ hm1
        rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hlen1 hm1
        have htrc1 := hlen1.scratch_ok.tarjan_reach_len
        have htmk1 := hlen1.scratch_ok.tarjan_mark_len
        have hnl_tmk1 : (flip_lit ^^^ 1#32).toNat < st1.scratch.tarjan_mark.length := by
          rw [htmk1]; omega
        have hnl_tmk1_sw : ((flip_lit ^^^ 1#32).setWidth 64).toNat <
            st1.scratch.tarjan_mark.length := by
          rw [bv32_lit_toNat_mod64]; exact hnl_tmk1
        have hnl_trc1 : (flip_lit ^^^ 1#32).toNat < st1.scratch.tarjan_reach.length := by
          rw [htrc1]; omega
        c0_hsteps_nogrp
        refine wp_join_safety_slice (ts := [i64, i64]) (fullSafetySlice c) st1 R
          (fun _ => True) trivial (fun st2 (cu2, _, ()) => FullExtScratchPres s st2 ∧
            WalkScrPrefixPres s st2 ∧ cu2.toNat ≤ ncl.toNat) ?_ ?_
        · rintro J2 st2 ⟨cu2, _, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hext2, hpre2, hcu2⟩ hm2
          rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
          have htrc2 := hlen2.scratch_ok.tarjan_reach_len
          have hfl_trc2 : flip_lit.toNat < st2.scratch.tarjan_reach.length := by
            rw [htrc2]; omega
          have hnl_trc2 : (flip_lit ^^^ 1#32).toNat < st2.scratch.tarjan_reach.length := by
            rw [htrc2]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3) ?_ ?_
          · rintro Jfs ⟨fs, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
            c0_hsteps
            exact hQ _ st2 m2 (hcore0.trans (hcore1.trans hcore2)) hlen2
              ⟨hext2, hpre2, bv64_pack_low32_and hcu2 (by omega)⟩ hm2
          · intro Jfs hJfs; c0_hsteps_nogrp <;> exact hJfs _ m2 rfl
        · intro J2 hJ2; c0_hsteps_nogrp
          · refine wp_join_group (ts := [i64]) (fun (lm, ()) m2 => m1 = m2 ∧
                (st1.scratch.tarjan_mark[(flip_lit ^^^ 1#32).toNat]'hnl_tmk1).toNat + lm.toNat ≤
                  c.scratch_cap - (2200 + 5 * ncl.toNat)) ?_ ?_
            · rintro Jlb ⟨lb, ⟨⟩⟩ _ ⟨rfl, hlb⟩; rw [Blocks.get_here]
              refine wp_loop_safety_slice (fullSafetySlice c) st1 R (fun _ => True) trivial
                (fun st2 (cu2, k, ()) => FullExtScratchPres s st2 ∧ WalkScrPrefixPres s st2 ∧
                  st2.scratch.tarjan_mark = st1.scratch.tarjan_mark ∧
                  cu2.toNat ≤ ncl.toNat ∧ k.toNat ≤ lb.toNat)
                (fun (_, k, ()) => lb.toNat - k.toNat) ?_ ?_
              · intro Jk hJk; c0_hsteps
                exact hJk st1 (cu1, 0#64, ()) m1 hm1 rfl hlen1
                  ⟨hext1, hpre1, rfl, hcu1, Nat.zero_le _⟩
              · rintro Jk st2 ⟨cu2, k, ⟨⟩⟩ m2 hcore2 hlen2 _
                  ⟨hext2, hpre2, htmk2_eq, hcu2, hk_le⟩ hmk hJk
                rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hmk hJk
                have hsb2 := hlen2.scratch_ok.scratch_buf_len
                have htmk2 := hlen2.scratch_ok.tarjan_mark_len
                have hnl_tmk2 : (flip_lit ^^^ 1#32).toNat < st2.scratch.tarjan_mark.length := by
                  rw [htmk2]; omega
                have hnl_tmk2_sw : ((flip_lit ^^^ 1#32).setWidth 64).toNat <
                    st2.scratch.tarjan_mark.length := by
                  rw [bv32_lit_toNat_mod64]; exact hnl_tmk2
                have htmk_eq2 : st2.scratch.tarjan_mark[(flip_lit ^^^ 1#32).toNat]'hnl_tmk2 =
                    st1.scratch.tarjan_mark[(flip_lit ^^^ 1#32).toNat]'hnl_tmk1 := by
                  simp [htmk2_eq]
                c0_hsteps_nogrp_nobound
                · have hk_lt : k.toNat < lb.toNat := by assumption
                  have hocc_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) +
                      (st2.scratch.tarjan_mark[(flip_lit ^^^ 1#32).toNat]'hnl_tmk2).setWidth 64 +
                      k).toNat < st2.scratch.scratch_buf.length := by
                    have hz := bv32_lit_toNat_mod64
                      (st2.scratch.tarjan_mark[(flip_lit ^^^ 1#32).toNat]'hnl_tmk2)
                    have hshl := bv64_shl1_toNat_lt (x := ncl) (by omega)
                    rw [htmk_eq2] at hz ⊢
                    rw [hsb2]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hshl] at hz ⊢
                    bv_omega
                  have hocc_lt_sw : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) +
                      (st2.scratch.tarjan_mark[((flip_lit ^^^ 1#32).setWidth 64
                        ).toNat]'hnl_tmk2_sw).setWidth 64 +
                      k).toNat < st2.scratch.scratch_buf.length := by
                    simpa only [bv32_lit_toNat_mod64] using hocc_lt
                  have hocc_lt_sw1 : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) +
                      (st1.scratch.tarjan_mark[((flip_lit ^^^ 1#32).setWidth 64
                        ).toNat]'hnl_tmk1_sw).setWidth 64 +
                      k).toNat < st2.scratch.scratch_buf.length := by
                    simpa only [htmk2_eq] using hocc_lt_sw
                  c0_hsteps_nogrp
                  refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) st2 R
                    (fun _ => True) trivial
                    (fun st3 (cu3, ()) => FullExtScratchPres s st3 ∧ WalkScrPrefixPres s st3 ∧
                      st3.scratch.tarjan_mark = st1.scratch.tarjan_mark ∧
                      cu3.toNat ≤ ncl.toNat) ?_ ?_
                  · rintro Jcu2 st3 ⟨cu3, ⟨⟩⟩ m3 hcore3 hlen3 _
                      ⟨hext3, hpre3, htmk3_eq, hcu3⟩ hm3
                    rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore3 hlen3 hm3
                    c0_hfast
                    exact hJk st3 (cu3, k + 1#64, ()) m3 hm3 (by
                      dsimp only; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
                      hcore3 hlen3 ⟨hext3, hpre3, htmk3_eq, hcu3,
                        by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega⟩
                  · intro Jcu2 hJcu2; dsimp only [fullSafetySlice] at hJcu2
                    c0_hfast_nogrp
                    · let cl := st2.scratch.scratch_buf[((2200#64 + (ncl <<< (1 : Nat)) + ncl +
                          ncl + ncl) + (st1.scratch.tarjan_mark[((flip_lit ^^^ 1#32).setWidth 64
                            ).toNat]'hnl_tmk1_sw).setWidth 64 + k).toNat]'hocc_lt_sw1
                      have hcl_lt : cl.toNat < ncl.toNat := by
                        have hz := bv32_lit_toNat_mod64 cl
                        dsimp only [cl] at hz ⊢
                        simp only [bv32_lit_toNat_mod64, ← bv32_xor1_toNat] at hz ⊢
                        c0_bound
                      have hsat_lt : ((2200#64 + (ncl <<< (1 : Nat))) + cl.setWidth 64).toNat <
                          st2.scratch.scratch_buf.length := by
                        have hz := bv32_lit_toNat_mod64 cl
                        rw [hsb2, walk2_sat_idx (by omega)]; omega
                      c0_hfast_nogrp
                      · have hupos_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl) +
                            cl.setWidth 64).toNat <
                            (st2.scratch.scratch_buf.set ((2200#64 + (ncl <<< (1 : Nat))) +
                              cl.setWidth 64).toNat (st2.scratch.scratch_buf[((2200#64 +
                                (ncl <<< (1 : Nat))) + cl.setWidth 64).toNat]'hsat_lt -
                                1#32)).length := by
                          have hz := bv32_lit_toNat_mod64 cl
                          rw [List.length_set, hsb2, walk2_upos_idx (by omega)]; omega
                        have huns_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) + cu2).toNat <
                            ((st2.scratch.scratch_buf.set ((2200#64 + (ncl <<< (1 : Nat))) +
                              cl.setWidth 64).toNat (st2.scratch.scratch_buf[((2200#64 +
                                (ncl <<< (1 : Nat))) + cl.setWidth 64).toNat]'hsat_lt -
                                1#32)).set ((2200#64 + (ncl <<< (1 : Nat)) + ncl) +
                              cl.setWidth 64).toNat (cu2.setWidth 32)).length := by
                          rw [List.length_set, List.length_set, hsb2, walk2_uns_idx (by omega)]
                          omega
                        c0_hfast <;> first
                          | ( refine hJcu2 _ (cu2 + 1#64, ()) _ (by assumption) ?_ ?_ ?_
                              · rfl
                              · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                                  scratch_buf_len := by simp [hsb2] }⟩
                              · refine ⟨⟨hext2.1, hext2.2⟩, fun j hj => ?_, htmk2_eq,
                                  by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega⟩
                                have hz := bv32_lit_toNat_mod64 cl
                                exact (list_getElem?_set_ne_lt hj
                                    (walk2_uns_ge2200 ncl cu2 (by omega))).trans
                                  ((list_getElem?_set_ne_lt hj
                                    (walk2_upos_ge2200 ncl (cl.setWidth 64) (by omega))).trans
                                  ((list_getElem?_set_ne_lt hj
                                    (walk2_sat_ge2200 ncl (cl.setWidth 64) (by omega))).trans
                                  (hpre2 j hj))) )
                          | ( refine hJcu2 _ (cu2, ()) _ (by assumption) ?_ ?_ ?_
                              · rfl
                              · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                                  scratch_buf_len := by simp [hsb2] }⟩
                              · refine ⟨⟨hext2.1, hext2.2⟩, fun j hj => ?_, htmk2_eq, hcu2⟩
                                have hz := bv32_lit_toNat_mod64 cl
                                exact (list_getElem?_set_ne_lt hj
                                  (walk2_sat_ge2200 ncl (cl.setWidth 64) (by omega))).trans
                                  (hpre2 j hj) )
                          | exact hJcu2 st2 (cu2, ()) m2 hmk rfl hlen2
                              ⟨hext2, hpre2, htmk2_eq, hcu2⟩
                      all_goals
                        exact hJcu2 st2 (cu2, ()) m2 hmk rfl hlen2 ⟨hext2, hpre2, htmk2_eq, hcu2⟩
                    · exact hJcu2 st2 (cu2, ()) m2 hmk rfl hlen2 ⟨hext2, hpre2, htmk2_eq, hcu2⟩
                · exact hJ2 st2 (cu2, _, ()) m2 hmk hcore2 hlen2 ⟨hext2, hpre2, hcu2⟩
            · intro Jlb hJlb; c0_hsteps_nogrp
              · exact hJlb _ m1 ⟨rfl, walk2_lim_avail_exp hscr h5ncl (by assumption)⟩
              · exact hJlb _ m1 ⟨rfl,
                  walk2_lim_trc_exp hscr h5ncl (by assumption) (by assumption)⟩
          · exact hJ2 st1 (cu1, _, ()) m1 hm1 rfl hlen1 ⟨hext1, hpre1, hcu1⟩
      · intro J1 hJ1; c0_hsteps_nogrp
        · refine wp_join_group (ts := [i64]) (fun (lm, ()) m1 =>
              m = m1 ∧ (st0.scratch.tarjan_mark[flip_lit.toNat]'hfl_tmk).toNat + lm.toNat ≤
                c.scratch_cap - (2200 + 5 * ncl.toNat)) ?_ ?_
          · rintro Jlm ⟨lm, ⟨⟩⟩ _ ⟨rfl, hlm⟩; rw [Blocks.get_here]
            refine wp_loop_safety_slice (fullSafetySlice c) st0 R (fun _ => True) trivial
              (fun st1 (cu1, k, ()) => FullExtScratchPres s st1 ∧ WalkScrPrefixPres s st1 ∧
                st1.scratch.tarjan_mark = st0.scratch.tarjan_mark ∧
                st1.scratch.tarjan_reach = st0.scratch.tarjan_reach ∧
                cu1.toNat ≤ ncl.toNat ∧ k.toNat ≤ lm.toNat)
              (fun (_, k, ()) => lm.toNat - k.toNat) ?_ ?_
            · intro Jk hJk; c0_hsteps
              exact hJk st0 (cu, 0#64, ()) m hm0 rfl hlen0
                ⟨hext0, hpre0, rfl, rfl, hcu, Nat.zero_le _⟩
            · rintro Jk st1 ⟨cu1, k, ⟨⟩⟩ m1 hcore1 hlen1 _
                ⟨hext1, hpre1, htmk1_eq, htrc1_eq, hcu1, hk_le⟩ hm1 hJk
              rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hlen1 hm1 hJk
              have hsb1 := hlen1.scratch_ok.scratch_buf_len
              have htmk1 := hlen1.scratch_ok.tarjan_mark_len
              have hfl_tmk1 : flip_lit.toNat < st1.scratch.tarjan_mark.length := by
                rw [htmk1]; omega
              have hfl_tmk1_sw : (flip_lit.setWidth 64).toNat <
                  st1.scratch.tarjan_mark.length := by
                rw [bv32_lit_toNat_mod64]; exact hfl_tmk1
              have htmk_eq1 : st1.scratch.tarjan_mark[flip_lit.toNat]'hfl_tmk1 =
                  st0.scratch.tarjan_mark[flip_lit.toNat]'hfl_tmk := by
                simp [htmk1_eq]
              c0_hsteps_nogrp_nobound
              · have hk_lt : k.toNat < lm.toNat := by assumption
                have hocc_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) +
                    (st1.scratch.tarjan_mark[flip_lit.toNat]'hfl_tmk1).setWidth 64 + k).toNat <
                    st1.scratch.scratch_buf.length := by
                  have hz := bv32_lit_toNat_mod64
                    (st1.scratch.tarjan_mark[flip_lit.toNat]'hfl_tmk1)
                  have hshl := bv64_shl1_toNat_lt (x := ncl) (by omega)
                  rw [htmk_eq1] at hz ⊢
                  rw [hsb1]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hshl] at hz ⊢
                  bv_omega
                have hocc_lt_sw : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) +
                    (st1.scratch.tarjan_mark[(flip_lit.setWidth 64).toNat]'hfl_tmk1_sw
                      ).setWidth 64 + k).toNat <
                    st1.scratch.scratch_buf.length := by
                  simpa only [bv32_lit_toNat_mod64] using hocc_lt
                have hocc_lt_sw0 : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) +
                    (st0.scratch.tarjan_mark[(flip_lit.setWidth 64).toNat]'hfl_tmk_sw
                      ).setWidth 64 + k).toNat <
                    st1.scratch.scratch_buf.length := by
                  simpa only [htmk1_eq] using hocc_lt_sw
                c0_hsteps_nogrp
                refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) st1 R
                  (fun _ => True) trivial
                  (fun st1' (cu1', ()) => FullExtScratchPres s st1' ∧ WalkScrPrefixPres s st1' ∧
                    st1'.scratch.tarjan_mark = st0.scratch.tarjan_mark ∧
                    st1'.scratch.tarjan_reach = st0.scratch.tarjan_reach ∧
                    cu1'.toNat ≤ ncl.toNat) ?_ ?_
                · rintro Jcu1 st1' ⟨cu1', ⟨⟩⟩ m1' hcore1' hlen1' _
                    ⟨hext1', hpre1', htmk1', htrc1', hcu1'⟩ hm1'
                  rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1' hlen1' hm1'
                  c0_hfast
                  exact hJk st1' (cu1', k + 1#64, ()) m1' hm1' (by
                    dsimp only; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
                    hcore1' hlen1' ⟨hext1', hpre1', htmk1', htrc1', hcu1',
                      by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega⟩
                · intro Jcu1 hJcu1; dsimp only [fullSafetySlice] at hJcu1
                  c0_hfast_nogrp
                  · let cl := st1.scratch.scratch_buf[((2200#64 + (ncl <<< (1 : Nat)) + ncl +
                        ncl + ncl) + (st0.scratch.tarjan_mark[(flip_lit.setWidth 64
                          ).toNat]'hfl_tmk_sw).setWidth 64 + k).toNat]'hocc_lt_sw0
                    have hcl_lt : cl.toNat < ncl.toNat := by
                      have hz := bv32_lit_toNat_mod64 cl; dsimp only [cl] at hz ⊢
                      simp only [bv32_lit_toNat_mod64, htmk1_eq] at *; c0_bound
                    have hsat_lt : ((2200#64 + (ncl <<< (1 : Nat))) + cl.setWidth 64).toNat <
                        st1.scratch.scratch_buf.length := by
                      have hz := bv32_lit_toNat_mod64 cl
                      rw [hsb1, walk2_sat_idx (by omega)]; omega
                    c0_hfast_nobound
                    · have hcu1_pos : 0 < cu1.toNat := by c0_bound
                      let sb1 := st1.scratch.scratch_buf.set ((2200#64 + (ncl <<< (1 : Nat))) +
                        cl.setWidth 64).toNat (st1.scratch.scratch_buf[((2200#64 +
                          (ncl <<< (1 : Nat))) + cl.setWidth 64).toNat]'hsat_lt +
                          (1 : BitVec 32))
                      have hupos_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl) +
                          cl.setWidth 64).toNat < sb1.length := by
                        have hz := bv32_lit_toNat_mod64 cl
                        rw [List.length_set, hsb1, walk2_upos_idx (by omega)]; omega
                      have huns_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) + cu1 -
                          1#64).toNat < sb1.length := by
                        rw [List.length_set, hsb1, walk2_uns_sub1_idx (by omega) (by omega)]; omega
                      c0_hfast_nobound
                      · let pos := sb1[((2200#64 + (ncl <<< (1 : Nat)) + ncl) +
                          cl.setWidth 64).toNat]'hupos_lt
                        let last_c := sb1[((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) + cu1 -
                          1#64).toNat]'huns_lt
                        have hpos_lt : pos.toNat < cu1.toNat := by
                          dsimp only [pos, sb1, cl]; c0_bound
                        have huns_p : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) +
                            pos.setWidth 64).toNat < sb1.length := by
                          have hz := bv32_lit_toNat_mod64 pos
                          rw [List.length_set, hsb1, walk2_uns_idx (by omega)]; omega
                        c0_hfast_nobound
                        · let sb2 := sb1.set ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) +
                            pos.setWidth 64).toNat last_c
                          have hlast_lt : last_c.toNat < ncl.toNat := by
                            dsimp only [last_c, sb1, cl]; c0_bound
                          have hlast_upos : ((2200#64 + (ncl <<< (1 : Nat)) + ncl) +
                              last_c.setWidth 64).toNat < sb2.length := by
                            have hz := bv32_lit_toNat_mod64 last_c
                            rw [List.length_set, List.length_set, hsb1, walk2_upos_idx (by omega)]
                            omega
                          let sb3 := sb2.set ((2200#64 + (ncl <<< (1 : Nat)) + ncl) +
                            last_c.setWidth 64).toNat pos
                          have hcl_upos3 : ((2200#64 + (ncl <<< (1 : Nat)) + ncl) +
                              cl.setWidth 64).toNat < sb3.length := by
                            have hz := bv32_lit_toNat_mod64 cl
                            rw [List.length_set, List.length_set, List.length_set, hsb1,
                              walk2_upos_idx (by omega)]; omega
                          c0_hfast_nobound
                          refine hJcu1 _ (cu1 - 1#64, ()) _ (by assumption) ?_ ?_ ?_
                          · rfl
                          · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                              scratch_buf_len := by simp [hsb1] }⟩
                          · refine ⟨⟨hext1.1, hext1.2⟩, fun j hj => ?_, htmk1_eq, htrc1_eq,
                              by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
                            have hz1 := bv32_lit_toNat_mod64 cl
                            have hz2 := bv32_lit_toNat_mod64 last_c
                            have hz3 := bv32_lit_toNat_mod64 pos
                            exact (list_getElem?_set_ne_lt hj
                                (walk2_upos_ge2200 ncl (cl.setWidth 64) (by omega))).trans
                              ((list_getElem?_set_ne_lt hj
                                (walk2_upos_ge2200 ncl (last_c.setWidth 64) (by omega))).trans
                              ((list_getElem?_set_ne_lt hj
                                (walk2_uns_ge2200 ncl (pos.setWidth 64) (by omega))).trans
                              ((list_getElem?_set_ne_lt hj
                                (walk2_sat_ge2200 ncl (cl.setWidth 64) (by omega))).trans
                              (hpre1 j hj))))
                        · let sb2 := sb1.set ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) +
                            pos.setWidth 64).toNat last_c
                          have hcl_upos2 : ((2200#64 + (ncl <<< (1 : Nat)) + ncl) +
                              cl.setWidth 64).toNat < sb2.length := by
                            have hz := bv32_lit_toNat_mod64 cl
                            rw [List.length_set, List.length_set, hsb1, walk2_upos_idx (by omega)]
                            omega
                          c0_hfast_nobound
                          refine hJcu1 _ (cu1 - 1#64, ()) _ (by assumption) ?_ ?_ ?_
                          · rfl
                          · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                              scratch_buf_len := by simp [hsb1] }⟩
                          · refine ⟨⟨hext1.1, hext1.2⟩, fun j hj => ?_, htmk1_eq, htrc1_eq,
                              by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
                            have hz1 := bv32_lit_toNat_mod64 cl
                            have hz3 := bv32_lit_toNat_mod64 pos
                            exact (list_getElem?_set_ne_lt hj
                                (walk2_upos_ge2200 ncl (cl.setWidth 64) (by omega))).trans
                              ((list_getElem?_set_ne_lt hj
                                (walk2_uns_ge2200 ncl (pos.setWidth 64) (by omega))).trans
                              ((list_getElem?_set_ne_lt hj
                                (walk2_sat_ge2200 ncl (cl.setWidth 64) (by omega))).trans
                              (hpre1 j hj)))
                      all_goals
                        refine hJcu1 _ (cu1, ()) _ (by assumption) ?_ ?_ ?_
                        · rfl
                        · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                            scratch_buf_len := by simp [hsb1] }⟩
                        · refine ⟨⟨hext1.1, hext1.2⟩, fun j hj => ?_, htmk1_eq, htrc1_eq, hcu1⟩
                          have hz1 := bv32_lit_toNat_mod64 cl
                          exact (list_getElem?_set_ne_lt hj
                            (walk2_sat_ge2200 ncl (cl.setWidth 64) (by omega))).trans (hpre1 j hj)
                    all_goals
                      refine hJcu1 _ (cu1, ()) _ (by assumption) ?_ ?_ ?_
                      · rfl
                      · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                          scratch_buf_len := by simp [hsb1] }⟩
                      · refine ⟨⟨hext1.1, hext1.2⟩, fun j hj => ?_, htmk1_eq, htrc1_eq, hcu1⟩
                        have hz1 := bv32_lit_toNat_mod64 cl
                        exact (list_getElem?_set_ne_lt hj
                          (walk2_sat_ge2200 ncl (cl.setWidth 64) (by omega))).trans (hpre1 j hj)
                  · exact hJcu1 st1 (cu1, ()) m1 hm1 rfl hlen1
                      ⟨hext1, hpre1, htmk1_eq, htrc1_eq, hcu1⟩
              · exact hJ1 st1 (cu1, _, ()) m1 hm1 hcore1 hlen1
                  ⟨hext1, hpre1, htmk1_eq, htrc1_eq, hcu1⟩
          · intro Jlm hJlm; c0_hsteps_nogrp
            · exact hJlm _ m ⟨rfl, walk2_lim_avail_exp hscr h5ncl (by assumption)⟩
            · exact hJlm _ m ⟨rfl, walk2_lim_trc_exp hscr h5ncl (by assumption) (by assumption)⟩
        · exact hJ1 st0 (cu, _, ()) m hm0 rfl hlen0 ⟨hext0, hpre0, rfl, rfl, hcu⟩
    · intro Jcu hJcu; c0_hsteps_nogrp
      · exact hJcu (ncl, ()) m ⟨rfl, Nat.le_refl _⟩
      · exact hJcu (ulen, ()) m ⟨rfl, by c0_bound⟩

end LeanQbe.T.Examples.Kissat.Proof.Walk
