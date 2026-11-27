/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Validate0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit

/-!
# Node Validator WP Proof (`Bitblast.Proof.ValidateNode`)

Proves `bv_validate_node_wp` (`Γ`-parametric `Func.wp` soundness for `bv_validate_node`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.Examples.Bitblast.Src.Validate
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

private theorem bv32_lit_23 : (23 : BitVec 32).toNat = 23 := rfl

local macro "vn_read_with" hRead:ident progBytes:ident R:ident hfit:ident hm:ident
    hok:ident : tactic =>
  `(tactic| (
    c0_call $hRead
    refine ⟨$progBytes, $R, $hfit, ($hok).2, $hm, ?_⟩
    dsimp only
    rw [($hok).1]
    c0_hstraight))

local macro "vn_hc" hc:ident : tactic =>
  `(tactic| (
    have htmp_ := $hc
    try (simp only [bv_c0, beq_iff_eq, BitVec.toNat_eq,
      bv32_lit_0, bv32_lit_1, bv32_lit_2, bv32_lit_9, bv32_lit_16, bv32_lit_17,
      bv32_lit_18, bv32_lit_21, bv32_lit_22, bv32_lit_23, bv32_lit_24, bv32_lit_25,
      bv32_lit_26, bv32_lit_30, bv32_lit_32] at htmp_)
    omega))

local macro "vn_ite_t" hQ:ident hc:ident : tactic =>
  `(tactic| (
    have hQt_ := $hQ; rw [bv_ite_t (by vn_hc $hc)] at hQt_; exact hQt_))

local macro "vn_guard_a" hQ:ident hc:ident ha:ident ty:term : tactic =>
  `(tactic| (
    c0_hstraight; c0_hsplit
    · vn_ite_t $hQ $hc
    have $ha : $ty := by vn_hc $hc
    clear $hc
    have hQt_ := $hQ; rw [bv_ite_f (by omega)] at hQt_; clear $hQ; have $hQ := hQt_; clear hQt_
    c0_hstraight))

local macro "vn_guard_ab" hQ:ident hc:ident ha:ident hb:ident
    tyA:term "," tyB:term : tactic =>
  `(tactic| (
    c0_hstraight; c0_hsplit
    · have hQt_ := $hQ
      rw [bv_ite_t (by simp only [Bool.or_eq_true, decide_eq_true_eq]; left; vn_hc $hc)] at hQt_
      exact hQt_
    have $ha : $tyA := by vn_hc $hc
    clear $hc; c0_hstraight; c0_hsplit
    · have hQt_ := $hQ
      rw [bv_ite_t (by
        simp only [Bool.or_eq_true, decide_eq_true_eq]; right; vn_hc $hc)] at hQt_
      exact hQt_
    have $hb : $tyB := by vn_hc $hc
    clear $hc
    have hQt_ := $hQ; rw [bv_ite_f (by (try simp); omega)] at hQt_
    clear $hQ; have $hQ := hQt_; clear hQt_
    c0_hstraight))

local macro "vn_rd1" hRead:ident progBytes:ident R:ident hfit:ident hnw:ident hlen':ident
    hm:ident nVars:ident nCwords:ident hlt:ident child:ident ho:ident : tactic =>
  `(tactic| (
    have hc0_ := bv_child_word0_ok $hfit $hnw $hlen' $hlt
    vn_read_with $hRead $progBytes $R $hfit $hm hc0_
    have $ho : u32At $progBytes (nodesOff ($nVars).toNat ($nCwords).toNat + 5 * $child) <
        2 ^ 32 := u32At_lt ..
    clear hc0_))

local macro "vn_rd2" hRead:ident progBytes:ident R:ident hfit:ident hnw:ident hlen':ident
    hm:ident nVars:ident nCwords:ident hlt:ident child:ident ho:ident hw:ident : tactic =>
  `(tactic| (
    have hc0_ := bv_child_word0_ok $hfit $hnw $hlen' $hlt
    have hc1_ := bv_child_word1_ok $hfit $hnw $hlen' $hlt
    vn_read_with $hRead $progBytes $R $hfit $hm hc0_
    vn_read_with $hRead $progBytes $R $hfit $hm hc1_
    have $ho : u32At $progBytes (nodesOff ($nVars).toNat ($nCwords).toNat + 5 * $child) <
        2 ^ 32 := u32At_lt ..
    have $hw : u32At $progBytes (nodesOff ($nVars).toNat ($nCwords).toNat + 5 * $child + 1) <
        2 ^ 32 := u32At_lt ..
    clear hc0_ hc1_))

open Lean.Parser.Tactic in
local macro "vn_fin" hQ:ident _hc:ident m:ident Q:ident "[" lts:simpLemma,* "]" : tactic =>
  `(tactic| (
    c0_hsteps <;> first
      | (change $Q (false, ()) $m
         have hQf_ := $hQ
         rw [decide_eq_false] at hQf_
         · exact hQf_
         · clear hQf_ $hQ
           try simp only [bv_c0, beq_iff_eq, BitVec.toNat_eq, bv32_lit_22, $lts,*] at *
           omega)
      | (have hQt_ := $hQ
         rw [decide_eq_true] at hQt_
         · exact hQt_
         · clear hQt_ $hQ
           try simp only [bv_c0, beq_iff_eq, BitVec.toNat_eq, bv32_lit_22, $lts,*] at *
           omega)))

public section

theorem bv_validate_node_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X →
      Γ "bv_read_u32" [i64, i64] [i32] xs m Q X) :
    ∀ xs m Q X, bvValidateNodeSpec xs m Q X → Func.wp Γ bv_validate_node_body xs m Q X := by
  rintro ⟨progPtr, nodesW, nVars, nCwords, idx, ⟨⟩⟩ m Q X
    ⟨progBytes, R, hfit, hnw, hlen, hm, hQ⟩
  c0_hstraight
  have hlen' : 4 * (nodesOff nVars.toNat nCwords.toNat + 5 * (idx.toNat + 1)) ≤
      progBytes.length := hnw ▸ hlen
  have hk0 := bv_node_word0_ok hfit hnw hlen'
  have hk1 := bv_node_word_ok 1 1 rfl (by decide) hfit hnw hlen'
  have hk2 := bv_node_word_ok 2 2 rfl (by decide) hfit hnw hlen'
  have hk3 := bv_node_word_ok 3 3 rfl (by decide) hfit hnw hlen'
  have hk4 := bv_node_word_ok 4 4 rfl (by decide) hfit hnw hlen'
  vn_read_with hRead progBytes R hfit hm hk0
  vn_read_with hRead progBytes R hfit hm hk1
  vn_read_with hRead progBytes R hfit hm hk2
  vn_read_with hRead progBytes R hfit hm hk3
  vn_read_with hRead progBytes R hfit hm hk4
  clear hk0 hk1 hk2 hk3 hk4
  generalize hop_eq : u32At progBytes (nodesOff nVars.toNat nCwords.toNat + 5 * idx.toNat) = op
  generalize hw_eq : u32At progBytes (nodesOff nVars.toNat nCwords.toNat + 5 * idx.toNat + 1) = w
  generalize ha_eq : u32At progBytes (nodesOff nVars.toNat nCwords.toNat + 5 * idx.toNat + 2) = a
  generalize hb_eq : u32At progBytes (nodesOff nVars.toNat nCwords.toNat + 5 * idx.toNat + 3) = b
  generalize hc_eq : u32At progBytes (nodesOff nVars.toNat nCwords.toNat + 5 * idx.toNat + 4) = c
  have hop_lt : op < u32Bound := hop_eq ▸ u32At_lt ..
  have hw_lt : w < u32Bound := hw_eq ▸ u32At_lt ..
  have ha_lt : a < u32Bound := ha_eq ▸ u32At_lt ..
  have hb_lt : b < u32Bound := hb_eq ▸ u32At_lt ..
  have hc_lt : c < u32Bound := hc_eq ▸ u32At_lt ..
  unfold u32Bound at hop_lt hw_lt ha_lt hb_lt hc_lt
  c0_hsplit
  · rw [validNodeAt_ge32 (by rw [hop_eq]; vn_hc hc)] at hQ; exact hQ
  have hop_lt32 : op < 32 := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop0 : op = 0 := by vn_hc hc
    clear hc; rw [validNodeAt_var (hop_eq.trans hop0)] at hQ; dsimp only at hQ
    rw [ha_eq, hw_eq] at hQ; vn_guard_a hQ hc ha_nv (a < nVars.toNat)
    have hvw := bv_var_width_idx_ok hlen' ha_nv
    vn_read_with hRead progBytes R hfit hm hvw
    have hvw_lt : u32At progBytes (8 + 2 * a + 1) < 2 ^ 32 := u32At_lt ..
    clear hvw hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    exact bv_bool_q (bv_node_bool_iff (by
      simp only [bv_c0, Nat.mod_eq_of_lt hw_lt, Nat.mod_eq_of_lt hvw_lt,
        beq_iff_eq, BitVec.toNat_eq])) hQ
  have hop_gt0 : 0 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop1 : op = 1 := by vn_hc hc
    clear hc; rw [validNodeAt_const (hop_eq.trans hop1)] at hQ; dsimp only at hQ
    rw [hw_eq, ha_eq] at hQ
    have hnw_eq : (((BitVec.ofNat 32 w).setWidth 64 + 31) >>> (5 : Nat)).toNat =
        (w + 31) / 32 := by
      clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq; c0_bv_omega [hw_lt]
    clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    have hn_is : nCwords.toNat < 2 ^ 32 := nCwords.isLt
    c0_hsteps
    · rw [bv_ite_t (by clear hQ; c0_bv_omega [hw_lt, hnw_eq])] at hQ
      rw [decide_eq_false] at hQ; exact hQ; clear hQ; c0_bv_omega [ha_lt]
    · rw [bv_ite_t (by clear hQ; c0_bv_omega [hw_lt, hnw_eq])] at hQ
      rw [decide_eq_false] at hQ; exact hQ; clear hQ; c0_bv_omega [hw_lt, ha_lt, hnw_eq, hn_is]
    · rw [bv_ite_t (by clear hQ; c0_bv_omega [hw_lt, hnw_eq])] at hQ
      rw [decide_eq_true] at hQ; exact hQ; clear hQ; c0_bv_omega [hw_lt, ha_lt, hnw_eq, hn_is]
    · rw [bv_ite_f (by clear hQ; c0_bv_omega [hw_lt, hnw_eq])] at hQ; exact hQ
  have hop_gt1 : 1 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop2 : op = 2 := by vn_hc hc
    clear hc; rw [validNodeAt_extract (hop_eq.trans hop2)] at hQ; dsimp only at hQ
    rw [hb_eq] at hQ; vn_guard_a hQ hc hb_lti (b < idx.toNat)
    vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords hb_lti b hob_lt
    unfold opEq at hQ; exact bv_bool_q (bv32_ult_22 _ hob_lt) hQ
  have hop_gt2 : 2 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop9 : op ≤ opUmod := by unfold opUmod; vn_hc hc
    clear hc; rw [validNodeAt_binop (hop_eq.symm ▸ hop_gt2) (hop_eq.symm ▸ hop9)] at hQ
    dsimp only at hQ; rw [hw_eq, ha_eq, hb_eq] at hQ
    vn_guard_ab hQ hc ha_lti hb_lti (a < idx.toNat), (b < idx.toNat)
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa hwa
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords hb_lti b hob hwb
    unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    vn_fin hQ hc m Q [Nat.mod_eq_of_lt hw_lt, Nat.mod_eq_of_lt hoa, Nat.mod_eq_of_lt hwa,
      Nat.mod_eq_of_lt hob, Nat.mod_eq_of_lt hwb]
  have hop_gt9 : 9 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop16 : op ≤ opCpop := by unfold opCpop; vn_hc hc
    clear hc; rw [validNodeAt_unop (by unfold opUmod; exact hop_eq.symm ▸ hop_gt9)
      (hop_eq.symm ▸ hop16)] at hQ
    dsimp only at hQ; rw [hw_eq, ha_eq] at hQ; vn_guard_a hQ hc ha_lti (a < idx.toNat)
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa hwa
    unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    vn_fin hQ hc m Q [Nat.mod_eq_of_lt hw_lt, Nat.mod_eq_of_lt hoa, Nat.mod_eq_of_lt hwa]
  have hop_gt16 : 16 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop17 : op = opAppend := by unfold opAppend; vn_hc hc
    clear hc; rw [validNodeAt_append (hop_eq.trans hop17)] at hQ
    dsimp only at hQ; rw [hw_eq, ha_eq, hb_eq] at hQ
    vn_guard_ab hQ hc ha_lti hb_lti (a < idx.toNat), (b < idx.toNat)
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa hwa
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords hb_lti b hob hwb
    unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    vn_fin hQ hc m Q [Nat.mod_eq_of_lt hw_lt, Nat.mod_eq_of_lt hoa, Nat.mod_eq_of_lt hwa,
      Nat.mod_eq_of_lt hob, Nat.mod_eq_of_lt hwb]
  have hop_gt17 : 17 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop18 : op = opReplicate := by unfold opReplicate; vn_hc hc
    clear hc; rw [validNodeAt_rep (hop_eq.trans hop18)] at hQ
    dsimp only at hQ; rw [hw_eq, ha_eq, hb_eq] at hQ; vn_guard_a hQ hc ha_lti (a < idx.toNat)
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa hwa
    unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    have hmul_lt : u32At progBytes (nodesOff nVars.toNat nCwords.toNat + 5 * a + 1) * b <
        2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_pred_of_lt hwa) (Nat.le_pred_of_lt hb_lt))
        (by decide)
    have hmul64 :
        (BitVec.ofNat 32
          (u32At progBytes (nodesOff nVars.toNat nCwords.toNat + 5 * a + 1))).setWidth 64 *
            (BitVec.ofNat 32 b).setWidth 64 =
        BitVec.ofNat 64
          (u32At progBytes (nodesOff nVars.toNat nCwords.toNat + 5 * a + 1) * b) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmul_lt]
    c0_hsteps <;> first
      | (change Q (false, ()) m; rw [decide_eq_false] at hQ; exact hQ
         clear hQ; try rw [hmul64] at hc
         try (simp only [bv_c0, BitVec.toNat_eq, bv32_lit_22, Nat.mod_eq_of_lt hoa,
           Nat.mod_eq_of_lt hw_lt, Nat.mod_eq_of_lt hmul_lt] at hc)
         omega)
      | (rw [decide_eq_true] at hQ; exact hQ
         clear hQ; rw [hmul64] at hc
         simp only [bv_c0, BitVec.toNat_eq, Nat.mod_eq_of_lt hw_lt, Nat.mod_eq_of_lt hmul_lt] at hc
         rename_i h1_
         simp only [bv_c0, bv32_lit_22, Nat.mod_eq_of_lt hoa] at h1_
         omega)
  have hop_gt18 : 18 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop21 : op ≤ opAshr := by unfold opAshr; vn_hc hc
    clear hc; rw [validNodeAt_shift (by unfold opReplicate; exact hop_eq.symm ▸ hop_gt18)
      (hop_eq.symm ▸ hop21)] at hQ
    dsimp only at hQ; rw [hw_eq, ha_eq, hb_eq] at hQ
    vn_guard_ab hQ hc ha_lti hb_lti (a < idx.toNat), (b < idx.toNat)
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa hwa
    vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords hb_lti b hob
    unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    vn_fin hQ hc m Q [Nat.mod_eq_of_lt hw_lt, Nat.mod_eq_of_lt hoa, Nat.mod_eq_of_lt hwa,
      Nat.mod_eq_of_lt hob]
  have hop_gt21 : 21 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · rw [validNodeAt_w_ne1 (by unfold opAshr; exact hop_eq.symm ▸ hop_gt21)
      (hop_eq.symm ▸ hop_lt32) (by rw [hw_eq]; vn_hc hc)] at hQ
    exact hQ
  have hw1 : w = 1 := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop23 : op ≤ opUlt := by unfold opUlt; vn_hc hc
    clear hc; rw [validNodeAt_cmp (by unfold opAshr; exact hop_eq.symm ▸ hop_gt21)
      (hop_eq.symm ▸ hop23) (hw_eq.trans hw1)] at hQ
    dsimp only at hQ; rw [ha_eq, hb_eq] at hQ
    vn_guard_ab hQ hc ha_lti hb_lti (a < idx.toNat), (b < idx.toNat)
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa hwa
    vn_rd2 hRead progBytes R hfit hnw hlen' hm nVars nCwords hb_lti b hob hwb
    unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    vn_fin hQ hc m Q [Nat.mod_eq_of_lt hoa, Nat.mod_eq_of_lt hwa, Nat.mod_eq_of_lt hob,
      Nat.mod_eq_of_lt hwb]
  have hop_gt23 : 23 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop24 : op = opGetLsbD := by unfold opGetLsbD; vn_hc hc
    clear hc; rw [validNodeAt_getlsbd (hop_eq.trans hop24) (hw_eq.trans hw1)] at hQ
    dsimp only at hQ; rw [ha_eq] at hQ; vn_guard_a hQ hc ha_lti (a < idx.toNat)
    vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa
    unfold opEq at hQ; exact bv_bool_q (bv32_ult_22 _ hoa) hQ
  have hop_ne24 : op ≠ 24 := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop25 : op = opBConst := by unfold opBConst; vn_hc hc
    clear hc; rw [validNodeAt_bconst (hop_eq.trans hop25) (hw_eq.trans hw1)] at hQ
    dsimp only at hQ; rw [ha_eq] at hQ; c0_hstraight
    exact bv_bool_q (bv_node_bool_iff (by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
        bv32_lit_2, decide_eq_true_eq])) hQ
  have hop_ne25 : op ≠ 25 := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop26 : op = opBNot := by unfold opBNot; vn_hc hc
    clear hc; rw [validNodeAt_bnot (hop_eq.trans hop26) (hw_eq.trans hw1)] at hQ
    dsimp only at hQ; rw [ha_eq] at hQ; vn_guard_a hQ hc ha_lti (a < idx.toNat)
    vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa
    unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    exact bv_bool_q (bv_node_bool_iff (by
      simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoa,
        bv32_lit_22, decide_eq_true_eq])) hQ
  have hop_gt26 : 26 < op := by vn_hc hc
  clear hc; c0_hstraight
  c0_hsplit
  · have hop30 : op ≤ opGateOr := by unfold opGateOr; vn_hc hc
    clear hc; rw [validNodeAt_gate (by unfold opBNot; exact hop_eq.symm ▸ hop_gt26)
      (hop_eq.symm ▸ hop30) (hw_eq.trans hw1)] at hQ
    dsimp only at hQ; rw [ha_eq, hb_eq] at hQ
    vn_guard_ab hQ hc ha_lti hb_lti (a < idx.toNat), (b < idx.toNat)
    vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa
    vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords hb_lti b hob
    unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
    vn_fin hQ hc m Q [Nat.mod_eq_of_lt hoa, Nat.mod_eq_of_lt hob]
  · have hop_gt30 : opGateOr < op := by unfold opGateOr; vn_hc hc
    clear hc; rw [validNodeAt_ite (hop_eq.symm ▸ hop_gt30) (hop_eq.symm ▸ hop_lt32)
      (hw_eq.trans hw1)] at hQ
    dsimp only at hQ; rw [ha_eq, hb_eq, hc_eq] at hQ; c0_hstraight; c0_hsplit
    · rw [bv_ite_t (by
        simp only [Bool.or_eq_true, decide_eq_true_eq]; left; left; vn_hc hc)] at hQ
      exact hQ
    · have ha_lti : a < idx.toNat := by vn_hc hc
      clear hc; c0_hstraight; c0_hsplit
      · rw [bv_ite_t (by
          simp only [Bool.or_eq_true, decide_eq_true_eq]; left; right; vn_hc hc)] at hQ
        exact hQ
      · have hb_lti : b < idx.toNat := by vn_hc hc
        clear hc; c0_hstraight; c0_hsplit
        · rw [bv_ite_t (by
            simp only [Bool.or_eq_true, decide_eq_true_eq]; right; vn_hc hc)] at hQ
          exact hQ
        · have hc_lti : c < idx.toNat := by vn_hc hc
          clear hc; rw [bv_ite_f (by simp; omega)] at hQ; c0_hstraight
          vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords ha_lti a hoa
          vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords hb_lti b hob
          vn_rd1 hRead progBytes R hfit hnw hlen' hm nVars nCwords hc_lti c hoc
          unfold opEq at hQ; clear hfit hnw hlen hlen' hm hop_eq hw_eq ha_eq hb_eq hc_eq
          vn_fin hQ hc m Q [Nat.mod_eq_of_lt hoa, Nat.mod_eq_of_lt hob, Nat.mod_eq_of_lt hoc]

end

end LeanQbe.T.Examples.Bitblast.Proof
