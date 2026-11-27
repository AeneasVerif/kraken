/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Src.Validate
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Bytes

/-!
# Validator Base Helpers, `bv_read_u32_wp` & `bv_count_atoms_wp` (`Bitblast.Proof.Validate0`)

Proves byte-word conversion helpers, `bv_read_u32_wp`, `bv_count_atoms_wp`, and unfolded
`validNodeAt_*` equations used by `Bitblast.Proof.ValidateNode` and `Bitblast.Proof.Validate`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Validate
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

/-! ## 1. Pure Word & Byte Helpers -/

private theorem nat_testBit_eq_mod2 (n i : Nat) : n.testBit i = ((n / 2 ^ i) % 2 != 0) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod]

private theorem nat_or_shiftLeft (x y k : Nat) (hx : x < 2 ^ k) :
    x ||| (y <<< k) = x + y * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < k
  · have hge : ¬ (k ≤ i) := by omega
    simp only [hge, decide_false, Bool.false_and, Bool.or_false]
    have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have hmul : y * 2 ^ k = y * 2 ^ (k - i) * 2 ^ i := by rw [hpow]; ac_rfl
    have hx1 : (x + y * 2 ^ k) / 2 ^ i = x / 2 ^ i + y * 2 ^ (k - i) := by
      rw [hmul]; exact Nat.add_mul_div_right x (y * 2 ^ (k - i)) (Nat.pow_pos (by decide))
    have hk_sub : k - i = (k - i - 1) + 1 := by omega
    have hdiv2 : (x / 2 ^ i + y * 2 ^ (k - i)) % 2 = (x / 2 ^ i) % 2 := by
      rw [hk_sub, Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
    rw [nat_testBit_eq_mod2, nat_testBit_eq_mod2, hx1, hdiv2]
  · have hge : k ≤ i := by omega
    have hx_div : x / 2 ^ i = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hge))
    have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    have htot_div : (x + y * 2 ^ k) / 2 ^ i = y / 2 ^ (i - k) := by
      rw [hpow, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_right x y (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hx, Nat.zero_add]
    simp only [hge, decide_true, Bool.true_and]
    rw [nat_testBit_eq_mod2 x i, hx_div]
    simp only [Nat.zero_mod, bne_self_eq_false, Bool.false_or]
    rw [nat_testBit_eq_mod2, nat_testBit_eq_mod2, htot_div]

private theorem u32OfBytesLE_bv32 (b0 b1 b2 b3 : UInt8) :
    (BitVec.ofNat 8 b0.toNat).setWidth 32 |||
      ((BitVec.ofNat 8 b1.toNat).setWidth 32 <<< (8 : Nat)) |||
      ((BitVec.ofNat 8 b2.toNat).setWidth 32 <<< (16 : Nat)) |||
      ((BitVec.ofNat 8 b3.toNat).setWidth 32 <<< (24 : Nat)) =
      BitVec.ofNat 32 (u32OfBytesLE b0 b1 b2 b3) := by
  have hb0 := b0.toNat_lt
  have hb1 := b1.toNat_lt
  have hb2 := b2.toNat_lt
  have hb3 := b3.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : b0.toNat < 2 ^ 8),
    Nat.mod_eq_of_lt (by omega : b1.toNat < 2 ^ 8),
    Nat.mod_eq_of_lt (by omega : b2.toNat < 2 ^ 8),
    Nat.mod_eq_of_lt (by omega : b3.toNat < 2 ^ 8),
    Nat.mod_eq_of_lt (by omega : b0.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b1.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b2.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b3.toNat < 2 ^ 32)]
  have hm1 : b1.toNat <<< 8 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; omega
  have hm2 : b2.toNat <<< 16 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; omega
  have hm3 : b3.toNat <<< 24 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; omega
  rw [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2, Nat.mod_eq_of_lt hm3]
  have step1 : b0.toNat ||| (b1.toNat <<< 8) = b0.toNat + b1.toNat * 2 ^ 8 :=
    nat_or_shiftLeft b0.toNat b1.toNat 8 (by omega)
  have step2 : (b0.toNat + b1.toNat * 2 ^ 8) ||| (b2.toNat <<< 16) =
      b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 :=
    nat_or_shiftLeft _ b2.toNat 16 (by omega)
  have step3 : (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) ||| (b3.toNat <<< 24) =
      b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 :=
    nat_or_shiftLeft _ b3.toNat 24 (by omega)
  rw [step1, step2, step3]
  unfold u32OfBytesLE
  omega

@[local c0_load] private theorem c0_load_bytes_base {base : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i8 base = some (BitVec.ofNat 8 (bs[0]'hi).toNat) := by
  simpa using load_bytes_at hi hlen hm

@[local c0_load] private theorem c0_load_bytes_off {base off : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : off.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i8 (base + off) = some (BitVec.ofNat 8 (bs[off.toNat]'hi).toNat) := by
  have heq : BitVec.ofNat 64 off.toNat = off := BitVec.eq_of_toNat_eq (by simp)
  simpa [heq] using load_bytes_at (i := off.toNat) hi hlen hm

@[local c0_load] private theorem c0_load_bytes_shl2_add {base idx k : BitVec 64} {sh : Nat}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hsh : sh = 2) (hk : k.toNat < 4) (hi : 4 * (idx.toNat + 1) ≤ bs.length)
    (hlen : bs.length ≤ 2 ^ 64) (hm : (bytes base bs ⋆ R) m) :
    loadVal m i8 (base + (idx <<< sh) + k) =
      some (BitVec.ofNat 8 (bs[4 * idx.toNat + k.toNat]'(by omega)).toNat) := by
  subst hsh
  have heq : base + (idx <<< (2 : Nat)) + k =
      base + BitVec.ofNat 64 (4 * idx.toNat + k.toNat) := by
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hi64 : 4 * idx.toNat + k.toNat < 2 ^ 64 := by omega
    rw [Nat.mul_comm _ 4, Nat.mod_eq_of_lt (by omega : 4 * idx.toNat < 2 ^ 64),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
  rw [heq]
  exact load_bytes_at (i := 4 * idx.toNat + k.toNat) (by omega) hlen hm

@[local c0_load] private theorem c0_load_bytes_shl2_base {base idx : BitVec 64} {sh : Nat}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hsh : sh = 2) (hi : 4 * (idx.toNat + 1) ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i8 (base + (idx <<< sh)) =
      some (BitVec.ofNat 8 (bs[4 * idx.toNat]'(by omega)).toNat) := by
  have h := c0_load_bytes_shl2_add (base := base) (idx := idx) (k := 0#64) hsh (by decide)
    hi hlen hm
  simpa using h

@[local c0_load] private theorem c0_load_bytes_off_add {base off k : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hi : off.toNat + k.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i8 (base + off + k) =
      some (BitVec.ofNat 8 (bs[off.toNat + k.toNat]'hi).toNat) := by
  have heq : base + off + k = base + BitVec.ofNat 64 (off.toNat + k.toNat) := by
    rw [BitVec.add_assoc]
    have hk : off + k = BitVec.ofNat 64 (off.toNat + k.toNat) :=
      BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add])
    rw [hk]
  rw [heq]
  exact load_bytes_at (i := off.toNat + k.toNat) hi hlen hm

private theorem u32At_eq_of_lt (bs : List UInt8) (idx : Nat)
    (h : 4 * (idx + 1) ≤ bs.length) :
    u32At bs idx =
      u32OfBytesLE (bs[4 * idx]'(by omega)) (bs[4 * idx + 1]'(by omega))
        (bs[4 * idx + 2]'(by omega)) (bs[4 * idx + 3]'(by omega)) := by
  unfold u32At
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega : 4 * idx < bs.length),
    List.getElem?_eq_getElem (by omega : 4 * idx + 1 < bs.length),
    List.getElem?_eq_getElem (by omega : 4 * idx + 2 < bs.length),
    List.getElem?_eq_getElem (by omega : 4 * idx + 3 < bs.length),
    Option.getD_some]

private theorem countAtoms_zero_mono {bs : List UInt8} {k n : Nat} (hle : k ≤ n)
    (hk : countAtoms bs k = 0) : countAtoms bs n = 0 := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; exact hk
  | succ m ih =>
    by_cases hkm : k = m + 1
    · subst hkm; exact hk
    · have hm := ih (by omega)
      unfold countAtoms
      simp [hm]

private theorem c0_read_u32_idx_norm {k : Nat} (hk : k < 2 ^ 32) :
    ((8 : BitVec 64) + ((BitVec.ofNat 32 k).setWidth 64 <<< (1 : Nat)) + 1).toNat =
      8 + 2 * k + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [h1, h8, Nat.pow_one]
  omega

private theorem countAtoms_succ_eq (bs : List UInt8) (k : Nat) :
    countAtoms bs (k + 1) =
      (let prev := countAtoms bs k
      let vw := u32At bs (8 + 2 * k + 1)
      if (prev == 0 || decide (vw ≥ bvDimacsBound) ||
          decide (prev > bvDimacsBound - 1 - vw)) = true
      then 0 else prev + vw) := rfl

private theorem countAtoms_succ_zero {bs : List UInt8} {k : Nat}
    (_hk : countAtoms bs k ≠ 0)
    (hbad : u32At bs (8 + 2 * k + 1) ≥ bvDimacsBound ∨
      countAtoms bs k > bvDimacsBound - 1 - u32At bs (8 + 2 * k + 1)) :
    countAtoms bs (k + 1) = 0 := by
  rw [countAtoms_succ_eq]
  dsimp only
  split
  · rfl
  · exfalso
    rename_i h
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases hbad with hb | hb
    · exact h (Or.inl (Or.inr hb))
    · exact h (Or.inr hb)

private theorem countAtoms_succ_ok {bs : List UInt8} {k : Nat}
    (_hk : countAtoms bs k ≠ 0)
    (h1 : u32At bs (8 + 2 * k + 1) < bvDimacsBound)
    (h2 : countAtoms bs k ≤ bvDimacsBound - 1 - u32At bs (8 + 2 * k + 1)) :
    countAtoms bs (k + 1) = countAtoms bs k + u32At bs (8 + 2 * k + 1) := by
  rw [countAtoms_succ_eq]
  dsimp only
  split
  · exfalso
    rename_i h
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with (h0 | h3) | h4 <;> omega
  · rfl

/-! ## 2. Canonical WP Theorems: `bv_read_u32_wp` & `bv_count_atoms_wp` -/

public section

theorem bv_read_u32_wp (Γ : Env) :
    ∀ xs m Q X, bvReadU32Spec xs m Q X → Func.wp Γ bv_read_u32_body xs m Q X := by
  rintro ⟨progPtr, idx, ⟨⟩⟩ m Q X ⟨progBytes, R, hfit, hlen, hm, hQ⟩
  c0_hsteps!
  have hres := u32OfBytesLE_bv32 (progBytes[4 * idx.toNat]'(by omega))
    (progBytes[4 * idx.toNat + 1]'(by omega)) (progBytes[4 * idx.toNat + 2]'(by omega))
    (progBytes[4 * idx.toNat + 3]'(by omega))
  rw [← u32At_eq_of_lt progBytes idx.toNat hlen] at hres
  simp only [BitVec.toNat_ofNat,
    show (OfNat.ofNat 0 : Nat) % 2 ^ 64 = 0 from rfl,
    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 3 < 2 ^ 64),
    Nat.add_zero]
  rw [hres]
  exact hQ

private theorem bv64_dimacs_sub_eq {w : Nat} (hw : w < bvDimacsBound) :
    ((268435456 : BitVec 64) - 1 - (BitVec.ofNat 32 w).setWidth 64) =
      BitVec.ofNat 64 (bvDimacsBound - 1 - w) := by
  unfold bvDimacsBound at hw ⊢
  apply BitVec.eq_of_toNat_eq
  have h1 : (268435456 : BitVec 64) - 1 = BitVec.ofNat 64 268435455 := by decide
  rw [h1, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : w < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : w < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 268435455 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 268435455 - w < 2 ^ 64)]
  omega

theorem bv_count_atoms_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X →
      Γ "bv_read_u32" [i64, i64] [i32] xs m Q X) :
    ∀ xs m Q X, bvCountAtomsSpec xs m Q X → Func.wp Γ bv_count_atoms_body xs m Q X := by
  rintro ⟨progPtr, nVars, ⟨⟩⟩ m Q X ⟨progBytes, R, hfit, hlen, hm, hQ⟩
  c0_hsteps_nogrp
  refine wp_while_state (α := Nat)
    (fun k => (BitVec.ofNat 64 (countAtoms progBytes k), BitVec.ofNat 32 k, ()))
    (fun k => nVars.toNat - k)
    (fun k ml => ml = m ∧ k ≤ nVars.toNat ∧ countAtoms progBytes k ≠ 0) ?_ ?_
  · intro J hJ
    c0_hsteps
    exact hJ 0 m ⟨rfl, Nat.zero_le _, by unfold countAtoms; omega⟩
  · intro J k ml ⟨hml, hk_le, hk_ne⟩ ih
    subst hml
    c0_hstraight
    c0_hsplit
    · have hk_lt : k < nVars.toNat := by c0_bound
      have hk32 : k < 2 ^ 32 := by omega
      c0_hstraight
      c0_call hRead
      refine ⟨progBytes, R, hfit, ?_, hm, ?_⟩
      · rw [c0_read_u32_idx_norm hk32]; omega
      · rw [c0_read_u32_idx_norm hk32]
        have hlt1 := countAtoms_lt progBytes k
        have hlt2 := u32At_lt progBytes (8 + 2 * k + 1)
        unfold u32Bound at hlt2
        have hlt1_64 : countAtoms progBytes k < 2 ^ 64 := by
          unfold bvDimacsBound at hlt1; omega
        have h268 : (268435456 : BitVec 64).toNat = 268435456 := rfl
        c0_hstraight
        c0_hsplit
        · have hw : u32At progBytes (8 + 2 * k + 1) ≥ bvDimacsBound := by
            unfold bvDimacsBound
            simp only [bv_c0, h268, Nat.mod_eq_of_lt hlt2] at hc
            omega
          have hk1_zero := countAtoms_succ_zero hk_ne (Or.inl hw)
          rw [countAtoms_zero_mono (by omega : k + 1 ≤ nVars.toNat) hk1_zero] at hQ
          exact hQ
        · have hw_lt : u32At progBytes (8 + 2 * k + 1) < bvDimacsBound := by
            unfold bvDimacsBound
            simp only [bv_c0, h268, Nat.mod_eq_of_lt hlt2] at hc
            omega
          clear hc
          have hsub := bv64_dimacs_sub_eq hw_lt
          have hsub_lt : bvDimacsBound - 1 - u32At progBytes (8 + 2 * k + 1) < 2 ^ 64 := by
            unfold bvDimacsBound at hw_lt ⊢; omega
          c0_hstraight
          refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
          · rw [hsub] at hc
            simp only [Arg.val, BitVec.ult, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt hlt1_64, decide_eq_true_eq] at hc
            have hk1_zero := countAtoms_succ_zero hk_ne (Or.inr hc)
            rw [countAtoms_zero_mono (by omega : k + 1 ≤ nVars.toNat) hk1_zero] at hQ
            c0_hstraight
            exact hQ
          · c0_hstraight
            rw [hsub] at hc
            simp only [Arg.val, BitVec.ult, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt hlt1_64, decide_eq_false_iff_not] at hc
            have hle : countAtoms progBytes k ≤
                bvDimacsBound - 1 - u32At progBytes (8 + 2 * k + 1) :=
              Nat.le_of_not_lt hc
            clear hc
            have hk1_eq := countAtoms_succ_ok hk_ne hw_lt hle
            have hk1_ne : countAtoms progBytes (k + 1) ≠ 0 := by
              rw [hk1_eq]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hk_ne)
                (Nat.le_add_right ..))
            have hlt2_64 : u32At progBytes (8 + 2 * k + 1) < 2 ^ 64 :=
              Nat.lt_trans hlt2 (by decide)
            have hsum_lt : countAtoms progBytes k + u32At progBytes (8 + 2 * k + 1) < 2 ^ 64 := by
              unfold bvDimacsBound at hlt1 hw_lt
              exact Nat.lt_trans (Nat.add_lt_add hlt1 hw_lt) (by decide)
            have heq_end : BitVec.ofNat 64 (countAtoms progBytes k) +
                (BitVec.ofNat 32 (u32At progBytes (8 + 2 * k + 1))).setWidth 64 =
                BitVec.ofNat 64 (countAtoms progBytes (k + 1)) := by
              rw [hk1_eq]; apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt1_64,
                Nat.mod_eq_of_lt hlt2_64, Nat.mod_eq_of_lt hsum_lt]
            have heq_k : BitVec.ofNat 32 k + (1 : BitVec 32) = BitVec.ofNat 32 (k + 1) := by
              apply BitVec.eq_of_toNat_eq
              have hk1 : k + 1 < 2 ^ 32 := Nat.lt_of_le_of_lt hk_lt nVars.isLt
              have h1_32 : (1 : BitVec 32).toNat = 1 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1_32,
                Nat.mod_eq_of_lt hk32, Nat.mod_eq_of_lt hk1]
            rw [heq_end, heq_k]
            exact ih (k + 1) ml (Nat.sub_lt_sub_left hk_lt (Nat.lt_succ_self k))
              ⟨rfl, hk_lt, hk1_ne⟩
    · have hk32 : k < 2 ^ 32 := Nat.lt_of_le_of_lt hk_le nVars.isLt
      rw [Nat.mod_eq_of_lt hk32] at hc
      have hk_eq : k = nVars.toNat := Nat.le_antisymm hk_le (Nat.le_of_not_lt hc)
      subst hk_eq
      simp only [wp]
      exact hQ

/-! ## 3. Shared Helpers & `validNodeAt` Equations for `ValidateNode` -/

theorem bv_node_word0_ok {nodesW : BitVec 64} {nVars nCwords idx : BitVec 32}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    (hfit : progPtr.toNat + progBytes.length < 2 ^ 64)
    (hnw : nodesW.toNat = nodesOff nVars.toNat nCwords.toNat)
    (hlen : 4 * (nodesOff nVars.toNat nCwords.toNat + 5 * (idx.toNat + 1)) ≤ progBytes.length) :
    (nodesW + idx.setWidth 64 * 5).toNat =
        nodesOff nVars.toNat nCwords.toNat + 5 * idx.toNat ∧
      4 * ((nodesW + idx.setWidth 64 * 5).toNat + 1) ≤ progBytes.length := by
  have hi := idx.isLt
  constructor <;> c0_bv_omega [hfit, hnw, hlen, hi]

theorem bv_node_word_ok {nodesW : BitVec 64} {nVars nCwords idx : BitVec 32}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    (kv : BitVec 64) (k : Nat) (hkv : kv.toNat = k) (hk : k < 5)
    (hfit : progPtr.toNat + progBytes.length < 2 ^ 64)
    (hnw : nodesW.toNat = nodesOff nVars.toNat nCwords.toNat)
    (hlen : 4 * (nodesOff nVars.toNat nCwords.toNat + 5 * (idx.toNat + 1)) ≤ progBytes.length) :
    (nodesW + idx.setWidth 64 * 5 + kv).toNat =
        nodesOff nVars.toNat nCwords.toNat + 5 * idx.toNat + k ∧
      4 * ((nodesW + idx.setWidth 64 * 5 + kv).toNat + 1) ≤ progBytes.length := by
  have hi := idx.isLt
  constructor <;> c0_bv_omega [hfit, hnw, hlen, hi, hkv, hk]

theorem bv_ite_t {P : Prop} [Decidable P] {α : Type} {a b : α} (h : P) :
    (if P then a else b) = a := by
  split
  · rfl
  · contradiction

theorem bv_ite_f {P : Prop} [Decidable P] {α : Type} {a b : α} (h : ¬ P) :
    (if P then a else b) = b := by
  split
  · contradiction
  · rfl

theorem bv_child_word0_ok {nodesW : BitVec 64} {nVars nCwords idx : BitVec 32}
    {progPtr : BitVec 64} {progBytes : List UInt8} {a : Nat}
    (hfit : progPtr.toNat + progBytes.length < 2 ^ 64)
    (hnw : nodesW.toNat = nodesOff nVars.toNat nCwords.toNat)
    (hlen : 4 * (nodesOff nVars.toNat nCwords.toNat + 5 * (idx.toNat + 1)) ≤ progBytes.length)
    (ha : a < idx.toNat) :
    (nodesW + (BitVec.ofNat 32 a).setWidth 64 * 5).toNat =
        nodesOff nVars.toNat nCwords.toNat + 5 * a ∧
      4 * ((nodesW + (BitVec.ofNat 32 a).setWidth 64 * 5).toNat + 1) ≤ progBytes.length := by
  have hi := idx.isLt
  have h5a : (BitVec.ofNat 32 a).setWidth 64 * 5 = BitVec.ofNat 64 (5 * a) := by
    apply BitVec.eq_of_toNat_eq
    c0_bv_omega [hi, ha]
  rw [h5a]
  constructor <;> c0_bv_omega [hfit, hnw, hlen, hi, ha]

theorem bv_child_word1_ok {nodesW : BitVec 64} {nVars nCwords idx : BitVec 32}
    {progPtr : BitVec 64} {progBytes : List UInt8} {a : Nat}
    (hfit : progPtr.toNat + progBytes.length < 2 ^ 64)
    (hnw : nodesW.toNat = nodesOff nVars.toNat nCwords.toNat)
    (hlen : 4 * (nodesOff nVars.toNat nCwords.toNat + 5 * (idx.toNat + 1)) ≤ progBytes.length)
    (ha : a < idx.toNat) :
    (nodesW + (BitVec.ofNat 32 a).setWidth 64 * 5 + (1 : BitVec 64)).toNat =
        nodesOff nVars.toNat nCwords.toNat + 5 * a + 1 ∧
      4 * ((nodesW + (BitVec.ofNat 32 a).setWidth 64 * 5 + (1 : BitVec 64)).toNat + 1) ≤
        progBytes.length := by
  have h0 := (bv_child_word0_ok hfit hnw hlen ha).1
  have hfit0 : nodesW.toNat + 5 * a < 2 ^ 64 := by omega
  have hw0 : (nodesW + (BitVec.ofNat 32 a).setWidth 64 * 5).toNat + 1 ≤
      nodesOff nVars.toNat nCwords.toNat + 5 * idx.toNat := by omega
  rw [BitVec.toNat_add, h0]
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [h1, Nat.mod_eq_of_lt (by omega : nodesOff nVars.toNat nCwords.toNat + 5 * a + 1 < 2 ^ 64)]
  omega

theorem bv_var_width_idx_ok {nVars nCwords idx : BitVec 32}
    {progBytes : List UInt8} {a : Nat}
    (hlen : 4 * (nodesOff nVars.toNat nCwords.toNat + 5 * (idx.toNat + 1)) ≤ progBytes.length)
    (ha : a < nVars.toNat) :
    ((8 : BitVec 64) + ((BitVec.ofNat 32 a).setWidth 64 <<< (1 : Nat)) +
        (1 : BitVec 64)).toNat = 8 + 2 * a + 1 ∧
      4 * (((8 : BitVec 64) + ((BitVec.ofNat 32 a).setWidth 64 <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat + 1) ≤ progBytes.length := by
  have hn := nVars.isLt
  have hnoff : nodesOff nVars.toNat nCwords.toNat = 8 + 2 * nVars.toNat + nCwords.toNat := rfl
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  constructor <;> c0_bv_omega [hlen, hn, ha, hnoff, h8, h1]

theorem bv_node_bool_iff {p q : Bool} (h : p = true ↔ q = true) :
    p = q := Bool.eq_iff_iff.mpr h

theorem bv_bool_q {Q : Post [Ty.bool]} {m : Mem 64} {a b : Bool}
    (h : a = b) (hb : Q (b, ()) m) : Q (a, ()) m := h ▸ hb

theorem bv32_lit_0 : (0 : BitVec 32).toNat = 0 := rfl
theorem bv32_lit_1 : (1 : BitVec 32).toNat = 1 := rfl
theorem bv32_lit_2 : (2 : BitVec 32).toNat = 2 := rfl
theorem bv32_lit_9 : (9 : BitVec 32).toNat = 9 := rfl
theorem bv32_lit_16 : (16 : BitVec 32).toNat = 16 := rfl
theorem bv32_lit_17 : (17 : BitVec 32).toNat = 17 := rfl
theorem bv32_lit_18 : (18 : BitVec 32).toNat = 18 := rfl
theorem bv32_lit_21 : (21 : BitVec 32).toNat = 21 := rfl
theorem bv32_lit_22 : (22 : BitVec 32).toNat = 22 := rfl
theorem bv32_lit_24 : (24 : BitVec 32).toNat = 24 := rfl
theorem bv32_lit_25 : (25 : BitVec 32).toNat = 25 := rfl
theorem bv32_lit_26 : (26 : BitVec 32).toNat = 26 := rfl
theorem bv32_lit_30 : (30 : BitVec 32).toNat = 30 := rfl
theorem bv32_lit_32 : (32 : BitVec 32).toNat = 32 := rfl

theorem bv32_ult_22 (x : Nat) (hx : x < 2 ^ 32) :
    ((BitVec.ofNat 32 x).ult 22) = decide (x < 22) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, bv32_lit_22]

theorem validNodeAt_ge32 {bs : List UInt8} {nVars nCwords idx : Nat}
    (hge : u32At bs (nodesOff nVars nCwords + 5 * idx) ≥ 32) :
    validNodeAt bs nVars nCwords idx = false := by
  unfold validNodeAt; dsimp only; exact bv_ite_t hge

theorem validNodeAt_var {bs : List UInt8} {nVars nCwords idx : Nat}
    (h0 : u32At bs (nodesOff nVars nCwords + 5 * idx) = opVar) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let w := u32At bs (nw0 + 5 * idx + 1)
      let a := u32At bs (nw0 + 5 * idx + 2)
      if a ≥ nVars then false else u32At bs (8 + 2 * a + 1) == w := by
  unfold validNodeAt opVar at *; dsimp only
  rw [bv_ite_f (by omega), bv_ite_t (by simp [h0])]

theorem validNodeAt_const {bs : List UInt8} {nVars nCwords idx : Nat}
    (h1 : u32At bs (nodesOff nVars nCwords + 5 * idx) = opConst) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let w := u32At bs (nw0 + 5 * idx + 1)
      let a := u32At bs (nw0 + 5 * idx + 2)
      let nw := (w + 31) / 32
      if nw > 0 then decide (a ≤ nCwords ∧ nw ≤ nCwords - a) else true := by
  unfold validNodeAt opVar opConst at *; dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp [h1]), bv_ite_t (by simp [h1])]

theorem validNodeAt_extract {bs : List UInt8} {nVars nCwords idx : Nat}
    (h2 : u32At bs (nodesOff nVars nCwords + 5 * idx) = opExtract) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let b := u32At bs (nw0 + 5 * idx + 3)
      if b ≥ idx then false else decide (u32At bs (nw0 + 5 * b) < opEq) := by
  unfold validNodeAt opVar opConst opExtract at *; dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp [h2]), bv_ite_f (by simp [h2]),
    bv_ite_t (by simp [h2])]

theorem validNodeAt_binop {bs : List UInt8} {nVars nCwords idx : Nat}
    (hgt : 2 < u32At bs (nodesOff nVars nCwords + 5 * idx))
    (hle : u32At bs (nodesOff nVars nCwords + 5 * idx) ≤ opUmod) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let w := u32At bs (nw0 + 5 * idx + 1)
      let a := u32At bs (nw0 + 5 * idx + 2)
      let b := u32At bs (nw0 + 5 * idx + 3)
      if a ≥ idx || b ≥ idx then false
      else
        let ab := nw0 + 5 * a
        let bb := nw0 + 5 * b
        decide (u32At bs ab < opEq ∧ u32At bs bb < opEq ∧
          u32At bs (ab + 1) = w ∧ u32At bs (bb + 1) = w) := by
  unfold validNodeAt opVar opConst opExtract opUmod at *; dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp; omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_t hle]

theorem validNodeAt_unop {bs : List UInt8} {nVars nCwords idx : Nat}
    (hgt : opUmod < u32At bs (nodesOff nVars nCwords + 5 * idx))
    (hle : u32At bs (nodesOff nVars nCwords + 5 * idx) ≤ opCpop) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let w := u32At bs (nw0 + 5 * idx + 1)
      let a := u32At bs (nw0 + 5 * idx + 2)
      if a ≥ idx then false
      else
        let ab := nw0 + 5 * a
        decide (u32At bs ab < opEq ∧ u32At bs (ab + 1) = w) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop at *; dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp; omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_f (by omega), bv_ite_t hle]

theorem validNodeAt_append {bs : List UInt8} {nVars nCwords idx : Nat}
    (h17 : u32At bs (nodesOff nVars nCwords + 5 * idx) = opAppend) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let w := u32At bs (nw0 + 5 * idx + 1)
      let a := u32At bs (nw0 + 5 * idx + 2)
      let b := u32At bs (nw0 + 5 * idx + 3)
      if a ≥ idx || b ≥ idx then false
      else
        let ab := nw0 + 5 * a
        let bb := nw0 + 5 * b
        decide (u32At bs ab < opEq ∧ u32At bs bb < opEq ∧
          u32At bs (ab + 1) + u32At bs (bb + 1) = w) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend at *; dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp [h17]), bv_ite_f (by simp [h17]),
    bv_ite_f (by simp [h17]), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_t (by simp [h17])]

theorem validNodeAt_rep {bs : List UInt8} {nVars nCwords idx : Nat}
    (h18 : u32At bs (nodesOff nVars nCwords + 5 * idx) = opReplicate) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let w := u32At bs (nw0 + 5 * idx + 1)
      let a := u32At bs (nw0 + 5 * idx + 2)
      let b := u32At bs (nw0 + 5 * idx + 3)
      if a ≥ idx then false
      else
        let ab := nw0 + 5 * a
        decide (u32At bs ab < opEq ∧ u32At bs (ab + 1) * b = w) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate at *; dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp [h18]), bv_ite_f (by simp [h18]),
    bv_ite_f (by simp [h18]), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp [h18]), bv_ite_t (by simp [h18])]

theorem validNodeAt_shift {bs : List UInt8} {nVars nCwords idx : Nat}
    (hgt : opReplicate < u32At bs (nodesOff nVars nCwords + 5 * idx))
    (hle : u32At bs (nodesOff nVars nCwords + 5 * idx) ≤ opAshr) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let w := u32At bs (nw0 + 5 * idx + 1)
      let a := u32At bs (nw0 + 5 * idx + 2)
      let b := u32At bs (nw0 + 5 * idx + 3)
      if a ≥ idx || b ≥ idx then false
      else
        let ab := nw0 + 5 * a
        let bb := nw0 + 5 * b
        decide (u32At bs ab < opEq ∧ u32At bs bb < opEq ∧ u32At bs (ab + 1) = w) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate opAshr at *
  dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp; omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp; omega), bv_ite_f (by simp; omega), bv_ite_t hle]

theorem validNodeAt_w_ne1 {bs : List UInt8} {nVars nCwords idx : Nat}
    (hgt : opAshr < u32At bs (nodesOff nVars nCwords + 5 * idx))
    (hlt : u32At bs (nodesOff nVars nCwords + 5 * idx) < 32)
    (hne : u32At bs (nodesOff nVars nCwords + 5 * idx + 1) ≠ 1) :
    validNodeAt bs nVars nCwords idx = false := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate opAshr at *
  dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp; omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp; omega), bv_ite_f (by simp; omega), bv_ite_f (by omega), bv_ite_t hne]

theorem validNodeAt_cmp {bs : List UInt8} {nVars nCwords idx : Nat}
    (hgt : opAshr < u32At bs (nodesOff nVars nCwords + 5 * idx))
    (hle : u32At bs (nodesOff nVars nCwords + 5 * idx) ≤ opUlt)
    (hw : u32At bs (nodesOff nVars nCwords + 5 * idx + 1) = 1) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let a := u32At bs (nw0 + 5 * idx + 2)
      let b := u32At bs (nw0 + 5 * idx + 3)
      if a ≥ idx || b ≥ idx then false
      else
        let ab := nw0 + 5 * a
        let bb := nw0 + 5 * b
        decide (u32At bs ab < opEq ∧ u32At bs bb < opEq ∧
          u32At bs (ab + 1) = u32At bs (bb + 1)) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate opAshr
    opUlt at *
  dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp; omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp; omega), bv_ite_f (by simp; omega), bv_ite_f (by omega),
    bv_ite_f (by simp [hw]), bv_ite_t hle]

theorem validNodeAt_getlsbd {bs : List UInt8} {nVars nCwords idx : Nat}
    (h24 : u32At bs (nodesOff nVars nCwords + 5 * idx) = opGetLsbD)
    (hw : u32At bs (nodesOff nVars nCwords + 5 * idx + 1) = 1) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let a := u32At bs (nw0 + 5 * idx + 2)
      if a ≥ idx then false
      else decide (u32At bs (nw0 + 5 * a) < opEq) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate opAshr
    opUlt opGetLsbD at *
  dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp [h24]), bv_ite_f (by simp [h24]),
    bv_ite_f (by simp [h24]), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp [h24]), bv_ite_f (by simp [h24]), bv_ite_f (by omega),
    bv_ite_f (by simp [hw]), bv_ite_f (by omega), bv_ite_t (by simp [h24])]

theorem validNodeAt_bconst {bs : List UInt8} {nVars nCwords idx : Nat}
    (h25 : u32At bs (nodesOff nVars nCwords + 5 * idx) = opBConst)
    (hw : u32At bs (nodesOff nVars nCwords + 5 * idx + 1) = 1) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let a := u32At bs (nw0 + 5 * idx + 2)
      decide (a < 2) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate opAshr
    opUlt opGetLsbD opBConst at *
  dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp [h25]), bv_ite_f (by simp [h25]),
    bv_ite_f (by simp [h25]), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp [h25]), bv_ite_f (by simp [h25]), bv_ite_f (by omega),
    bv_ite_f (by simp [hw]), bv_ite_f (by omega), bv_ite_f (by simp [h25]),
    bv_ite_t (by simp [h25])]

theorem validNodeAt_bnot {bs : List UInt8} {nVars nCwords idx : Nat}
    (h26 : u32At bs (nodesOff nVars nCwords + 5 * idx) = opBNot)
    (hw : u32At bs (nodesOff nVars nCwords + 5 * idx + 1) = 1) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let a := u32At bs (nw0 + 5 * idx + 2)
      if a ≥ idx then false
      else decide (u32At bs (nw0 + 5 * a) ≥ opEq) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate opAshr
    opUlt opGetLsbD opBConst opBNot at *
  dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp [h26]), bv_ite_f (by simp [h26]),
    bv_ite_f (by simp [h26]), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp [h26]), bv_ite_f (by simp [h26]), bv_ite_f (by omega),
    bv_ite_f (by simp [hw]), bv_ite_f (by omega), bv_ite_f (by simp [h26]),
    bv_ite_f (by simp [h26]), bv_ite_t (by simp [h26])]

theorem validNodeAt_gate {bs : List UInt8} {nVars nCwords idx : Nat}
    (hgt : opBNot < u32At bs (nodesOff nVars nCwords + 5 * idx))
    (hle : u32At bs (nodesOff nVars nCwords + 5 * idx) ≤ opGateOr)
    (hw : u32At bs (nodesOff nVars nCwords + 5 * idx + 1) = 1) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let a := u32At bs (nw0 + 5 * idx + 2)
      let b := u32At bs (nw0 + 5 * idx + 3)
      if a ≥ idx || b ≥ idx then false
      else decide (u32At bs (nw0 + 5 * a) ≥ opEq ∧ u32At bs (nw0 + 5 * b) ≥ opEq) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate opAshr
    opUlt opGetLsbD opBConst opBNot opGateOr at *
  dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp; omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp; omega), bv_ite_f (by simp; omega), bv_ite_f (by omega),
    bv_ite_f (by simp [hw]), bv_ite_f (by omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_f (by simp; omega), bv_ite_t hle]

theorem validNodeAt_ite {bs : List UInt8} {nVars nCwords idx : Nat}
    (hgt : opGateOr < u32At bs (nodesOff nVars nCwords + 5 * idx))
    (hlt : u32At bs (nodesOff nVars nCwords + 5 * idx) < 32)
    (hw : u32At bs (nodesOff nVars nCwords + 5 * idx + 1) = 1) :
    validNodeAt bs nVars nCwords idx =
      let nw0 := nodesOff nVars nCwords
      let a := u32At bs (nw0 + 5 * idx + 2)
      let b := u32At bs (nw0 + 5 * idx + 3)
      let c := u32At bs (nw0 + 5 * idx + 4)
      if a ≥ idx || b ≥ idx || c ≥ idx then false
      else decide (u32At bs (nw0 + 5 * a) ≥ opEq ∧ u32At bs (nw0 + 5 * b) ≥ opEq ∧
        u32At bs (nw0 + 5 * c) ≥ opEq) := by
  unfold validNodeAt opVar opConst opExtract opUmod opCpop opAppend opReplicate opAshr
    opUlt opGetLsbD opBConst opBNot opGateOr at *
  dsimp only
  rw [bv_ite_f (by omega), bv_ite_f (by simp; omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_f (by omega), bv_ite_f (by omega),
    bv_ite_f (by simp; omega), bv_ite_f (by simp; omega), bv_ite_f (by omega),
    bv_ite_f (by simp [hw]), bv_ite_f (by omega), bv_ite_f (by simp; omega),
    bv_ite_f (by simp; omega), bv_ite_f (by simp; omega), bv_ite_f (by omega)]

end

end LeanQbe.T.Examples.Bitblast.Proof
