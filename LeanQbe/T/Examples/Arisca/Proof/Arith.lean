/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Arena
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import LeanQbe.T.Logic.Arith

/-!
# ARiSCA Header Primitives & 128-bit Modular Arithmetic (`Arisca.Proof.Arith`)

WP specifications and proofs for all `10` functions of `LeanQbe.T.Examples.Arisca.Src.Header`:
- Memory/word/allocator primitives: `ar_rd32`, `ar_next_word`, `ar_aalloc`
- Exact `128`-bit multiplier & masked `n_out`-bit modular arithmetic:
  `u64_mul128`, `ar_cmul`, `ar_cadd`, `ar_csub`, `ar_cneg`, `ar_cfrom_small`, `ar_cpow2`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header

/-! ## 1. Pure Definitions (`u32LE`, `wordAt`, `MasksOk`, `coeff128`) & Specs -/

@[expose] public section

/-- Little-endian 32-bit unsigned value of `4` bytes. -/
def u32LE (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat

/-- Little-endian `u32` word `idx` of byte list `bs`. -/
def wordAt (bs : List UInt8) (idx : Nat) : Nat :=
  u32LE (bs.getD (4 * idx) 0) (bs.getD (4 * idx + 1) 0)
    (bs.getD (4 * idx + 2) 0) (bs.getD (4 * idx + 3) 0)

/-- Low `k` bits set in a `64`-bit word (`min k 64` ones). -/
def maskVal64 (k : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ min k 64 - 1)

/-- Canonical `mlo`/`mhi` bitmasks matching `1 ≤ n_out ≤ 128`. -/
def MasksOk (n_out : Nat) (mlo mhi : BitVec 64) : Prop :=
  1 ≤ n_out ∧ n_out ≤ 128 ∧ mlo = maskVal64 n_out ∧ mhi = maskVal64 (n_out - 64)

/-- `(lo, hi)` interpreted modulo `2 ^ n_out` as `BitVec n_out`. -/
def coeff128 (n_out : Nat) (lo hi : BitVec 64) : BitVec n_out :=
  BitVec.ofNat n_out (lo.toNat + 2 ^ 64 * hi.toNat)

/-- WP specification for `ar_rd32(p)`. -/
def arRd32Spec : Spec [i64] [i32] :=
  fun ⟨p, ⟨⟩⟩ m Q _ =>
    ∃ (base : BitVec 64) (bs : List UInt8) (off : Nat) (R : Mem 64 → Prop),
      p = base + BitVec.ofNat 64 off ∧
      off + 4 ≤ bs.length ∧
      bs.length ≤ 2 ^ 64 ∧
      (bytes base bs ⋆ R) m ∧
      Q (BitVec.ofNat 32 (u32LE (bs.getD off 0) (bs.getD (off + 1) 0)
        (bs.getD (off + 2) 0) (bs.getD (off + 3) 0)), ⟨⟩) m

/-- WP specification for `ar_next_word(cx)`. -/
def arNextWordSpec : Spec [i64] [.bool, i32] :=
  fun ⟨cx, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (artBytes : List UInt8) (R : Mem 64 → Prop),
      s.art.toNat + artBytes.length < 2 ^ 64 ∧
      4 * s.nw.toNat ≤ artBytes.length ∧
      (arCtxMem cx s ⋆ bytes s.art artBytes ⋆ R) m ∧
      (∀ (ok : Bool) (v : BitVec 32) (s' : ArCtxState) (m' : Mem 64),
        (if s.pos.toNat < s.nw.toNat then
          ok = true ∧ v = BitVec.ofNat 32 (wordAt artBytes s.pos.toNat) ∧
          s' = { s with pos := s.pos + 1 }
        else
          ok = false ∧ v = 0#32 ∧ s' = s) →
        (arCtxMem cx s' ⋆ bytes s.art artBytes ⋆ R) m' →
        Q (ok, v, ⟨⟩) m')

/-- WP specification for `ar_aalloc(cx, nbytes)`. -/
def arAallocSpec : Spec [i64, i64] [i64] :=
  fun ⟨cx, nbytes, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (R : Mem 64 → Prop),
      0 < s.w.toNat ∧
      s.top.toNat ≤ s.wlen.toNat ∧
      s.w.toNat + s.wlen.toNat < 2 ^ 64 ∧
      (arCtxMem cx s ⋆ region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R) m ∧
      (∀ (ret : BitVec 64) (s' : ArCtxState) (m' : Mem 64),
        let pad := (8 - s.top.toNat % 8) % 8
        let t := s.top.toNat + pad
        ((ret = 0#64 ∧ s' = s ∧
           (arCtxMem cx s ⋆ region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R) m') ∨
         (ret ≠ 0#64 ∧ t + nbytes.toNat ≤ s.wlen.toNat ∧
           ret = s.w + BitVec.ofNat 64 t ∧
           s' = { s with top := BitVec.ofNat 64 (t + nbytes.toNat) } ∧
           (arCtxMem cx s' ⋆
             region (s.w + s.top) pad ⋆
             region ret nbytes.toNat ⋆
             region (s.w + BitVec.ofNat 64 (t + nbytes.toNat))
               (s.wlen.toNat - (t + nbytes.toNat)) ⋆ R) m')) →
        Q (ret, ⟨⟩) m')

/-- WP specification for `u64_mul128(a, b)`. -/
def u64Mul128Spec : Spec [i64, i64] [i64, i64] :=
  fun ⟨a, b, ⟨⟩⟩ m Q _ =>
    ∀ lo hi : BitVec 64,
      lo.toNat + 2 ^ 64 * hi.toNat = a.toNat * b.toNat →
      Q (lo, hi, ⟨⟩) m

/-- WP specification for `ar_cmul(cx, al, ah, bl, bh)`. -/
def arCmulSpec : Spec [i64, i64, i64, i64, i64] [i64, i64] :=
  fun ⟨cx, al, ah, bl, bh, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (R : Mem 64 → Prop),
      MasksOk s.modW s.mlo s.mhi ∧
      (arCtxMem cx s ⋆ R) m ∧
      (∀ lo hi : BitVec 64,
        coeff128 s.modW lo hi =
          coeff128 s.modW al ah * coeff128 s.modW bl bh →
        Q (lo, hi, ⟨⟩) m)

/-- WP specification for `ar_cadd(cx, al, ah, bl, bh)`. -/
def arCaddSpec : Spec [i64, i64, i64, i64, i64] [i64, i64] :=
  fun ⟨cx, al, ah, bl, bh, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (R : Mem 64 → Prop),
      MasksOk s.modW s.mlo s.mhi ∧
      (arCtxMem cx s ⋆ R) m ∧
      (∀ lo hi : BitVec 64,
        coeff128 s.modW lo hi =
          coeff128 s.modW al ah + coeff128 s.modW bl bh →
        Q (lo, hi, ⟨⟩) m)

/-- WP specification for `ar_csub(cx, al, ah, bl, bh)`. -/
def arCsubSpec : Spec [i64, i64, i64, i64, i64] [i64, i64] :=
  fun ⟨cx, al, ah, bl, bh, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (R : Mem 64 → Prop),
      MasksOk s.modW s.mlo s.mhi ∧
      (arCtxMem cx s ⋆ R) m ∧
      (∀ lo hi : BitVec 64,
        coeff128 s.modW lo hi =
          coeff128 s.modW al ah - coeff128 s.modW bl bh →
        Q (lo, hi, ⟨⟩) m)

/-- WP specification for `ar_cneg(cx, al, ah)`. -/
def arCnegSpec : Spec [i64, i64, i64] [i64, i64] :=
  fun ⟨cx, al, ah, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (R : Mem 64 → Prop),
      MasksOk s.modW s.mlo s.mhi ∧
      (arCtxMem cx s ⋆ R) m ∧
      (∀ lo hi : BitVec 64,
        coeff128 s.modW lo hi = -coeff128 s.modW al ah →
        Q (lo, hi, ⟨⟩) m)

/-- WP specification for `ar_cfrom_small(cx, v)`. -/
def arCfromSmallSpec : Spec [i64, i64] [i64, i64] :=
  fun ⟨cx, v, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (R : Mem 64 → Prop),
      MasksOk s.modW s.mlo s.mhi ∧
      (arCtxMem cx s ⋆ R) m ∧
      (∀ lo hi : BitVec 64,
        coeff128 s.modW lo hi = BitVec.ofInt s.modW v.toInt →
        Q (lo, hi, ⟨⟩) m)

/-- WP specification for `ar_cpow2(cx, e)`. -/
def arCpow2Spec : Spec [i64, i32] [i64, i64] :=
  fun ⟨cx, e, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (R : Mem 64 → Prop),
      MasksOk s.modW s.mlo s.mhi ∧
      (arCtxMem cx s ⋆ R) m ∧
      (∀ lo hi : BitVec 64,
        coeff128 s.modW lo hi =
          (if e.toNat < 128 then BitVec.ofNat s.modW (2 ^ e.toNat) else 0#(s.modW)) →
        Q (lo, hi, ⟨⟩) m)

end

/-! ## 2. Pure Mask & 128-bit Modular Lemmas -/

public section

theorem MasksOk.of_set_masks (n_out : BitVec 32) (hn1 : 1 ≤ n_out.toNat) (hn2 : n_out.toNat ≤ 128) :
    let mlo := if n_out.toNat ≥ 64 then ~~~0#64 else (1#64 <<< (n_out.setWidth 64)) - 1#64
    let mhi := if n_out.toNat ≥ 64 then
        (if n_out = 128#32 then ~~~0#64 else (1#64 <<< ((n_out - 64#32).setWidth 64)) - 1#64)
      else 0#64
    MasksOk n_out.toNat mlo mhi := by
  refine ⟨hn1, hn2, ?_, ?_⟩
  · by_cases h64 : n_out.toNat ≥ 64
    · simp only [h64, ↓reduceIte, maskVal64, Nat.min_eq_right h64]
      apply BitVec.eq_of_toNat_eq; decide
    · have hlt : n_out.toNat < 64 := by omega
      simp only [h64, ↓reduceIte, maskVal64, Nat.min_eq_left (by omega : n_out.toNat ≤ 64)]
      apply BitVec.eq_of_toNat_eq
      have hsh : (1#64 <<< n_out.setWidth 64).toNat = 2 ^ n_out.toNat := by
        rw [bv_c0_toNat_shiftLeft_bv, BitVec.toNat_setWidth,
          show (1#64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : n_out.toNat < 2 ^ 64),
          Nat.one_mul,
          Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hlt)]
      have hpos : (1#64).toNat ≤ (1#64 <<< n_out.setWidth 64).toNat := by
        rw [show (1#64).toNat = 1 from rfl, hsh]; exact Nat.one_le_pow _ _ (by decide)
      have hsublt : 2 ^ n_out.toNat - 1 < 2 ^ 64 := by
        have h1 : 2 ^ n_out.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hlt
        omega
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hpos), hsh, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt hsublt).symm
  · by_cases h64 : n_out.toNat ≥ 64
    · simp only [h64, ↓reduceIte, maskVal64]
      by_cases h128 : n_out = 128#32
      · subst h128; apply BitVec.eq_of_toNat_eq; decide
      · have hne : n_out.toNat ≠ 128 := fun h => h128 (BitVec.eq_of_toNat_eq (by simpa using h))
        have hlt : n_out.toNat - 64 < 64 := by omega
        simp only [h128, ↓reduceIte, Nat.min_eq_left (by omega : n_out.toNat - 64 ≤ 64)]
        apply BitVec.eq_of_toNat_eq
        have hsub : (n_out - 64#32).toNat = n_out.toNat - 64 := by c0_bv_omega [h64]
        have hsh : (1#64 <<< (n_out - 64#32).setWidth 64).toNat = 2 ^ (n_out.toNat - 64) := by
          rw [bv_c0_toNat_shiftLeft_bv, BitVec.toNat_setWidth, hsub,
            show (1#64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : n_out.toNat - 64 < 2 ^ 64),
            Nat.one_mul,
            Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hlt)]
        have hpos : (1#64).toNat ≤ (1#64 <<< (n_out - 64#32).setWidth 64).toNat := by
          rw [show (1#64).toNat = 1 from rfl, hsh]; exact Nat.one_le_pow _ _ (by decide)
        have hsublt : 2 ^ (n_out.toNat - 64) - 1 < 2 ^ 64 := by
          have h1 : 2 ^ (n_out.toNat - 64) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hlt
          omega
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hpos), hsh, BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt hsublt).symm
    · have h0 : n_out.toNat - 64 = 0 := by omega
      simp [h64, maskVal64, h0]

private theorem and_maskVal64_toNat (x : BitVec 64) (k : Nat) :
    (x &&& maskVal64 k).toNat = x.toNat % 2 ^ min k 64 := by
  have hk : min k 64 ≤ 64 := Nat.min_le_right k 64
  have hpow : 2 ^ min k 64 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  have hpowpos : 0 < 2 ^ min k 64 := Nat.pow_pos (by decide)
  have hlt : 2 ^ min k 64 - 1 < 2 ^ 64 := by omega
  rw [BitVec.toNat_and, maskVal64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat (min k 64)

theorem coeff128_mask {n_out : Nat} {mlo mhi : BitVec 64} (hm : MasksOk n_out mlo mhi)
    (lo hi : BitVec 64) :
    coeff128 n_out (lo &&& mlo) (hi &&& mhi) = coeff128 n_out lo hi := by
  rcases hm with ⟨_, hn2, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [coeff128, BitVec.toNat_ofNat, and_maskVal64_toNat]
  by_cases h64 : n_out ≤ 64
  · have hmin1 : min n_out 64 = n_out := Nat.min_eq_left h64
    have hsub : n_out - 64 = 0 := by omega
    rw [hmin1, hsub]
    have hmod0 : hi.toNat % 2 ^ min 0 64 = 0 := by show hi.toNat % 1 = 0; exact Nat.mod_one _
    rw [hmod0, Nat.mul_zero, Nat.add_zero, Nat.mod_mod]
    have hpow : 2 ^ n_out ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 h64
    rcases hpow with ⟨q, hq⟩
    rw [hq, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  · have hmin1 : min n_out 64 = 64 := Nat.min_eq_right (by omega)
    have hmin2 : min (n_out - 64) 64 = n_out - 64 := Nat.min_eq_left (by omega)
    rw [hmin1, hmin2, Nat.mod_eq_of_lt lo.isLt]
    have hsplit : 2 ^ n_out = 2 ^ 64 * 2 ^ (n_out - 64) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    rw [hsplit]
    rw [Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_mod, ← Nat.mul_mod_mul_left, ← Nat.add_mod]

theorem coeff128_eq_of_mod128 {n_out : Nat} (hn : n_out ≤ 128) (a b : Nat)
    (h : a % 2 ^ 128 = b % 2 ^ 128) : BitVec.ofNat n_out a = BitVec.ofNat n_out b := by
  apply BitVec.eq_of_toNat_eq
  have hdvd : 2 ^ n_out ∣ 2 ^ 128 := Nat.pow_dvd_pow 2 hn
  calc
    (BitVec.ofNat n_out a).toNat = a % 2 ^ n_out := @BitVec.toNat_ofNat a n_out
    _ = (a % 2 ^ 128) % 2 ^ n_out := (Nat.mod_mod_of_dvd a hdvd).symm
    _ = (b % 2 ^ 128) % 2 ^ n_out := by rw [h]
    _ = b % 2 ^ n_out := Nat.mod_mod_of_dvd b hdvd
    _ = (BitVec.ofNat n_out b).toNat := (@BitVec.toNat_ofNat b n_out).symm

theorem coeff128_zero (n_out : Nat) : coeff128 n_out 0#64 0#64 = 0#n_out := by
  apply BitVec.eq_of_toNat_eq; simp [coeff128]

theorem coeff128_one (n_out : Nat) : coeff128 n_out 1#64 0#64 = 1#n_out := by
  apply BitVec.eq_of_toNat_eq; simp [coeff128]

/-! ## 3. WP Proofs for `ar_rd32`, `ar_next_word`, & `ar_aalloc` -/

private theorem u32LE_bv32 (b0 b1 b2 b3 : UInt8) :
    (BitVec.ofNat 8 b0.toNat).setWidth 32 |||
      ((BitVec.ofNat 8 b1.toNat).setWidth 32 <<< (8 : Nat)) |||
      ((BitVec.ofNat 8 b2.toNat).setWidth 32 <<< (16 : Nat)) |||
      ((BitVec.ofNat 8 b3.toNat).setWidth 32 <<< (24 : Nat)) =
      BitVec.ofNat 32 (u32LE b0 b1 b2 b3) := by
  have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt
  have hb2 := b2.toNat_lt; have hb3 := b3.toNat_lt
  have hdisj : ∀ (x y k : Nat), x < 2 ^ k → x ||| (y <<< k) = x + y * 2 ^ k := by
    intro x y k hx
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hi : i < k
    · have hge : ¬ (k ≤ i) := by omega
      simp only [hge, decide_false, Bool.false_and, Bool.or_false]
      have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      have hmul : y * 2 ^ k = y * 2 ^ (k - i) * 2 ^ i := by rw [hpow]; ac_rfl
      have hx1 : (x + y * 2 ^ k) / 2 ^ i = x / 2 ^ i + y * 2 ^ (k - i) := by
        rw [hmul]; exact Nat.add_mul_div_right x (y * 2 ^ (k - i)) (Nat.pow_pos (by decide))
      have hk_sub : k - i = (k - i - 1) + 1 := by omega
      have hdiv2 : (x / 2 ^ i + y * 2 ^ (k - i)) % 2 = (x / 2 ^ i) % 2 := by
        rw [hk_sub, Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod,
        hx1, hdiv2]
    · have hge : k ≤ i := by omega
      have hx_div : x / 2 ^ i = 0 :=
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hge))
      have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
      have htot_div : (x + y * 2 ^ k) / 2 ^ i = y / 2 ^ (i - k) := by
        rw [hpow, ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_right x y (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hx, Nat.zero_add]
      simp only [hge, decide_true, Bool.true_and, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.and_comm 1, Nat.and_one_is_mod, hx_div, Nat.zero_mod, bne_self_eq_false,
        Bool.false_or, htot_div]
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
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega : b1.toNat <<< 8 < 2 ^ 32),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega : b2.toNat <<< 16 < 2 ^ 32),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega : b3.toNat <<< 24 < 2 ^ 32)]
  rw [hdisj b0.toNat b1.toNat 8 (by omega),
      hdisj _ b2.toNat 16 (by omega),
      hdisj _ b3.toNat 24 (by omega)]
  unfold u32LE; omega

theorem ar_rd32_wp (Γ : Env) :
    ∀ xs m Q X, arRd32Spec xs m Q X → Func.wp Γ ar_rd32_body xs m Q X := by
  rintro ⟨p, ⟨⟩⟩ m Q X ⟨base, bs, off, R, rfl, hfit, hlen, hm, hQ⟩
  c0_hstraight
  refine head_wp_load (addr := base + BitVec.ofNat 64 off)
    (v := BitVec.ofNat 8 (bs[off]'(by omega)).toNat) ?_
      (load_bytes_at (i := off) (by omega) hlen hm) ?_
  · dsimp only [Arg.val]; exact BitVec.add_zero _
  c0_hstraight
  refine head_wp_load (addr := base + BitVec.ofNat 64 (off + 1))
    (v := BitVec.ofNat 8 (bs[off + 1]'(by omega)).toNat) ?_
    (load_bytes_at (i := off + 1) (by omega) hlen hm) ?_
  · dsimp only [Arg.val]; rw [BitVec.add_assoc]
    exact congrArg (base + ·) (BitVec.eq_of_toNat_eq (by c0_bv_omega [hfit, hlen]))
  c0_hstraight
  refine head_wp_load (addr := base + BitVec.ofNat 64 (off + 2))
    (v := BitVec.ofNat 8 (bs[off + 2]'(by omega)).toNat) ?_
    (load_bytes_at (i := off + 2) (by omega) hlen hm) ?_
  · dsimp only [Arg.val]; rw [BitVec.add_assoc]
    exact congrArg (base + ·) (BitVec.eq_of_toNat_eq (by c0_bv_omega [hfit, hlen]))
  c0_hstraight
  refine head_wp_load (addr := base + BitVec.ofNat 64 (off + 3))
    (v := BitVec.ofNat 8 (bs[off + 3]'(by omega)).toNat) ?_
    (load_bytes_at (i := off + 3) (by omega) hlen hm) ?_
  · dsimp only [Arg.val]; rw [BitVec.add_assoc]
    exact congrArg (base + ·) (BitVec.eq_of_toNat_eq (by c0_bv_omega [hfit, hlen]))
  c0_hstraight
  have hg0 : bs[off]'(by omega) = bs.getD off 0 := by
    simp [List.getD_eq_getElem?_getD, (by omega : off < bs.length)]
  have hg1 : bs[off + 1]'(by omega) = bs.getD (off + 1) 0 := by
    simp [List.getD_eq_getElem?_getD, (by omega : off + 1 < bs.length)]
  have hg2 : bs[off + 2]'(by omega) = bs.getD (off + 2) 0 := by
    simp [List.getD_eq_getElem?_getD, (by omega : off + 2 < bs.length)]
  have hg3 : bs[off + 3]'(by omega) = bs.getD (off + 3) 0 := by
    simp [List.getD_eq_getElem?_getD, (by omega : off + 3 < bs.length)]
  rw [hg0, hg1, hg2, hg3, u32LE_bv32]
  exact hQ

theorem ar_next_word_wp (Γ : Env)
    (hRd : ∀ xs m Q X, arRd32Spec xs m Q X → Γ "ar_rd32" [i64] [i32] xs m Q X) :
    ∀ xs m Q X, arNextWordSpec xs m Q X → Func.wp Γ ar_next_word_body xs m Q X := by
  rintro ⟨cx, ⟨⟩⟩ m Q X ⟨s, artBytes, R, hart, hnw, hm, hQ⟩
  c0_hstraight
  c0_hsplit
  · c0_hstraight
    have hge : ¬ s.pos.toNat < s.nw.toNat := by c0_bv_omega [hc]
    exact hQ false 0#32 s m (by simp [hge]) hm
  · have hlt : s.pos.toNat < s.nw.toNat := by c0_bv_omega [hc]
    clear hc
    c0_hstraight
    have hp : s.art + 4 * s.pos = s.art + BitVec.ofNat 64 (4 * s.pos.toNat) :=
      congrArg (s.art + ·) (BitVec.eq_of_toNat_eq (by c0_bv_omega [hart, hnw, hlt]))
    refine wp_call_of_spec _ _ (hRd _ _ _ _ ⟨s.art, artBytes, 4 * s.pos.toNat,
        (arCtxMem cx s ⋆ R), hp, by omega, by omega, by c0_frame, ?_⟩)
    c0_hstraight
    have hw : u32LE (artBytes.getD (4 * s.pos.toNat) 0)
        (artBytes.getD (4 * s.pos.toNat + 1) 0)
        (artBytes.getD (4 * s.pos.toNat + 2) 0)
        (artBytes.getD (4 * s.pos.toNat + 3) 0) = wordAt artBytes s.pos.toNat := rfl
    rw [hw]
    exact hQ true (BitVec.ofNat 32 (wordAt artBytes s.pos.toNat))
      { s with pos := s.pos + 1 } _ (by simp [hlt]) (by c0_frame)

theorem ar_aalloc_wp (Γ : Env) :
    ∀ xs m Q X, arAallocSpec xs m Q X → Func.wp Γ ar_aalloc_body xs m Q X := by
  rintro ⟨cx, nbytes, ⟨⟩⟩ m Q X ⟨s, R, hwpos, htop, hfit, hm, hQ⟩
  c0_hstraight
  c0_hsplit
  · exact absurd (by c0_bv_omega [hc] : s.wlen.toNat < s.top.toNat) (by omega)
  · clear hc
    c0_hstraight
    c0_hsplit
    · c0_hstraight; exact hQ 0#64 s m (Or.inl ⟨rfl, rfl, hm⟩)
    · have hpad_nat :
          ((8 - (s.top &&& 7)) &&& 7 : BitVec 64).toNat = (8 - s.top.toNat % 8) % 8 := by
        have h1 : (s.top &&& 7 : BitVec 64).toNat = s.top.toNat % 8 := by
          rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 7 from rfl]
          exact Nat.and_two_pow_sub_one_eq_mod s.top.toNat 3
        have h2 : (8 - (s.top &&& 7) : BitVec 64).toNat = 8 - s.top.toNat % 8 := by
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1]; show _ ≤ 8; omega)), h1]
          rfl
        rw [BitVec.toNat_and, h2, show (7 : BitVec 64).toNat = 7 from rfl]
        exact Nat.and_two_pow_sub_one_eq_mod _ 3
      have hpad_le : (8 - s.top.toNat % 8) % 8 ≤ s.wlen.toNat - s.top.toNat := by
        c0_bv_omega [hc, hpad_nat, htop]
      clear hc
      c0_hstraight
      c0_hsplit
      · c0_hstraight; exact hQ 0#64 s m (Or.inl ⟨rfl, rfl, hm⟩)
      · have hfit_bytes :
            (8 - s.top.toNat % 8) % 8 + nbytes.toNat ≤ s.wlen.toNat - s.top.toNat := by
          c0_bv_omega [hc, hpad_nat, htop, hpad_le]
        clear hc
        c0_hstraight
        let pad := (8 - s.top.toNat % 8) % 8
        let t := s.top.toNat + pad
        have hsplit1 : region (s.w + s.top) (s.wlen.toNat - s.top.toNat) =
            (region (s.w + s.top) pad ⋆
             region (s.w + BitVec.ofNat 64 t) (s.wlen.toNat - t)) := by
          have heq : s.wlen.toNat - s.top.toNat = pad + (s.wlen.toNat - t) := by omega
          rw [heq, region_split (by omega), BitVec.add_assoc]
          congr 2; apply BitVec.eq_of_toNat_eq; c0_bv_omega [htop, hfit, hpad_le]
        have hsplit2 : region (s.w + BitVec.ofNat 64 t) (s.wlen.toNat - t) =
            (region (s.w + BitVec.ofNat 64 t) nbytes.toNat ⋆
             region (s.w + BitVec.ofNat 64 (t + nbytes.toNat))
               (s.wlen.toNat - (t + nbytes.toNat))) := by
          have heq : s.wlen.toNat - t = nbytes.toNat + (s.wlen.toNat - (t + nbytes.toNat)) := by
            omega
          rw [heq, region_split (by omega), ptr_add_ofNat]
        have hadr1 : s.top + ((8 - (s.top &&& 7)) &&& 7) = BitVec.ofNat 64 t := by
          apply BitVec.eq_of_toNat_eq; c0_bv_omega [hpad_nat, htop, hfit, hpad_le]
        have htop_eq : s.top + ((8 - (s.top &&& 7)) &&& 7) + nbytes =
            BitVec.ofNat 64 (t + nbytes.toNat) := by
          apply BitVec.eq_of_toNat_eq; c0_bv_omega [hpad_nat, htop, hfit, hpad_le, hfit_bytes]
        have hret_eq : s.w + (s.top + ((8 - (s.top &&& 7)) &&& 7)) =
            s.w + BitVec.ofNat 64 t := by
          rw [hadr1]
        have hret_ne : s.w + BitVec.ofNat 64 t ≠ 0#64 := by
          intro h0; have := congrArg BitVec.toNat h0; c0_bv_omega [hwpos, htop, hfit, hpad_le]
        have hm'' : (arCtxMem cx { s with top := BitVec.ofNat 64 (t + nbytes.toNat) } ⋆
            region (s.w + s.top) pad ⋆
            region (s.w + BitVec.ofNat 64 t) nbytes.toNat ⋆
            region (s.w + BitVec.ofNat 64 (t + nbytes.toNat))
              (s.wlen.toNat - (t + nbytes.toNat)) ⋆ R) m := by
          rw [htop_eq] at hm
          rw [hsplit1, hsplit2] at hm
          c0_frame
        rw [hret_eq]
        exact hQ (s.w + BitVec.ofNat 64 t) { s with top := BitVec.ofNat 64 (t + nbytes.toNat) } m
          (Or.inr ⟨hret_ne, by omega, rfl, rfl, hm''⟩)

/-! ## 4. WP Proofs for 128-bit Arithmetic (`u64_mul128` & `ar_c*`) -/

private theorem bv64_and_lo32 (x : BitVec 64) : (x &&& 0xFFFFFFFF#64).toNat = x.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and, show (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32

private theorem bv64_ushr32 (x : BitVec 64) : (x >>> (32 : Nat)).toNat = x.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv_eq_sub_of_add_eq {w : Nat} {a b c : BitVec w} (h : a + b = c) : a = c - b := by
  calc
    a = a + b - b := (BitVec.add_sub_cancel a b).symm
    _ = c - b := by rw [h]

private theorem bv_eq_neg_of_add_eq_zero {w : Nat} {a b : BitVec w} (h : a + b = 0#w) : a = -b := by
  rw [bv_eq_sub_of_add_eq h, BitVec.zero_sub]

private theorem nat_or_shl32 (a c : Nat) (ha : a < 2 ^ 32) : a ||| (c <<< 32) = a + (c <<< 32) := by
  rw [Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  by_cases hi : i < 32
  · have hpow : 2 ^ 32 = (2 * 2 ^ (32 - i - 1)) * 2 ^ i := by
      have h1 : 2 * 2 ^ (32 - i - 1) = 2 ^ (32 - i) := by
        rw [← Nat.pow_succ', Nat.succ_eq_add_one, show 32 - i - 1 + 1 = 32 - i by omega]
      rw [h1, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hmul : c * 2 ^ 32 = (2 * (c * 2 ^ (32 - i - 1))) * 2 ^ i := by
      rw [hpow]; simp only [Nat.mul_assoc, Nat.mul_left_comm]
    have hpowPos : 0 < 2 ^ i := Nat.pow_pos (by decide)
    have h0 : (c * 2 ^ 32).testBit i = false := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hmul, Nat.mul_div_left _ hpowPos,
        Nat.and_comm 1, Nat.and_one_is_mod, Nat.mul_mod_right]; decide
    have ha1 : (a + c * 2 ^ 32) / 2 ^ i % 2 = a / 2 ^ i % 2 := by
      rw [hmul, Nat.add_mul_div_right _ _ hpowPos, Nat.mul_comm 2, Nat.add_mul_mod_self_right]
    rw [h0, Bool.or_false]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod, ha1]
  · have hge : 32 ≤ i := by omega
    have hpow : 2 ^ i = 2 ^ 32 * 2 ^ (i - 32) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    have ha0 : a.testBit i = false := by
      have hlti : a < 2 ^ i := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hge)
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlti]; decide
    have hc1 : (a + c * 2 ^ 32) / 2 ^ i = c / 2 ^ (i - 32) := by
      rw [hpow, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 32), Nat.div_eq_of_lt ha, Nat.zero_add]
    have hc2 : (c * 2 ^ 32) / 2 ^ i = c / 2 ^ (i - 32) := by
      rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_div_left c (by decide : 0 < 2 ^ 32)]
    rw [ha0, Bool.false_or]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hc1, hc2]

private theorem or_shl32_eq (x y : BitVec 64) :
    ((x &&& 0xFFFFFFFF#64) ||| (y <<< (32 : Nat))).toNat =
      x.toNat % 2 ^ 32 + 2 ^ 32 * (y.toNat % 2 ^ 32) := by
  have hx := bv64_and_lo32 x
  have hy_sh : (y <<< (32 : Nat)).toNat = (y.toNat % 2 ^ 32) <<< 32 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have hpow : (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 := by decide
    rw [hpow, Nat.mul_comm y.toNat (2 ^ 32), Nat.mul_mod_mul_left, Nat.mul_comm (2 ^ 32)]
  have hlt : (x &&& 0xFFFFFFFF#64).toNat < 2 ^ 32 := hx ▸ Nat.mod_lt _ (by decide)
  rw [BitVec.toNat_or, hy_sh, nat_or_shl32 _ _ hlt, Nat.shiftLeft_eq, Nat.mul_comm _ (2 ^ 32), hx]

theorem u64_mul128_wp (Γ : Env) :
    ∀ xs m Q X, u64Mul128Spec xs m Q X → Func.wp Γ u64_mul128_body xs m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  c0_hstraight
  refine hQ _ _ ?_
  let a0 := a &&& 0xFFFFFFFF#64
  let a1 := a >>> (32 : Nat)
  let b0 := b &&& 0xFFFFFFFF#64
  let b1 := b >>> (32 : Nat)
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := (p00 >>> (32 : Nat)) + (p01 &&& 0xFFFFFFFF#64) + (p10 &&& 0xFFFFFFFF#64)
  change ((p00 &&& 0xFFFFFFFF#64) ||| (mid <<< (32 : Nat))).toNat +
      2 ^ 64 * (p11 + (p01 >>> (32 : Nat)) + (p10 >>> (32 : Nat)) + (mid >>> (32 : Nat))).toNat =
    a.toNat * b.toNat
  have ha0 : a0.toNat = a.toNat % 2 ^ 32 := bv64_and_lo32 a
  have ha1 : a1.toNat = a.toNat / 2 ^ 32 := bv64_ushr32 a
  have hb0 : b0.toNat = b.toNat % 2 ^ 32 := bv64_and_lo32 b
  have hb1 : b1.toNat = b.toNat / 2 ^ 32 := bv64_ushr32 b
  have ha0lt : a0.toNat < 2 ^ 32 := ha0 ▸ Nat.mod_lt _ (by decide)
  have ha1lt : a1.toNat < 2 ^ 32 := by rw [ha1]; have := a.isLt; omega
  have hb0lt : b0.toNat < 2 ^ 32 := hb0 ▸ Nat.mod_lt _ (by decide)
  have hb1lt : b1.toNat < 2 ^ 32 := by rw [hb1]; have := b.isLt; omega
  have hp00 : p00.toNat = a0.toNat * b0.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (Nat.mul_lt_mul'' ha0lt hb0lt)]
  have hp01 : p01.toNat = a0.toNat * b1.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (Nat.mul_lt_mul'' ha0lt hb1lt)]
  have hp10 : p10.toNat = a1.toNat * b0.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (Nat.mul_lt_mul'' ha1lt hb0lt)]
  have hp11 : p11.toNat = a1.toNat * b1.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (Nat.mul_lt_mul'' ha1lt hb1lt)]
  have hmid : mid.toNat = p00.toNat / 2 ^ 32 + p01.toNat % 2 ^ 32 + p10.toNat % 2 ^ 32 := by
    have hlt : p00.toNat / 2 ^ 32 + p01.toNat % 2 ^ 32 + p10.toNat % 2 ^ 32 < 2 ^ 64 := by
      have : p00.toNat / 2 ^ 32 < 2 ^ 32 := by
        have := Nat.mul_lt_mul'' ha0lt hb0lt; rw [← hp00] at this; omega
      have := Nat.mod_lt p01.toNat (by decide : 0 < 2 ^ 32)
      have := Nat.mod_lt p10.toNat (by decide : 0 < 2 ^ 32)
      omega
    simp only [mid, BitVec.toNat_add, bv64_ushr32, bv64_and_lo32]
    rw [Nat.mod_eq_of_lt (by omega : p00.toNat / 2 ^ 32 + p01.toNat % 2 ^ 32 < 2 ^ 64),
      Nat.mod_eq_of_lt hlt]
  have hhi_lt :
      p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + mid.toNat / 2 ^ 32 < 2 ^ 64 := by
    have h11 : p11.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      rw [hp11]; exact Nat.mul_le_mul (by omega) (by omega)
    have h00 : p00.toNat / 2 ^ 32 ≤ 2 ^ 32 - 2 := by
      have : p00.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
        rw [hp00]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    have h01 : p01.toNat / 2 ^ 32 ≤ 2 ^ 32 - 2 := by
      have : p01.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
        rw [hp01]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    have h10 : p10.toNat / 2 ^ 32 ≤ 2 ^ 32 - 2 := by
      have : p10.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
        rw [hp10]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    have hm : mid.toNat / 2 ^ 32 ≤ 2 := by
      have := Nat.mod_lt p01.toNat (by decide : 0 < 2 ^ 32)
      have := Nat.mod_lt p10.toNat (by decide : 0 < 2 ^ 32)
      rw [hmid]; omega
    omega
  have hlo : ((p00 &&& 0xFFFFFFFF#64) ||| (mid <<< (32 : Nat))).toNat =
      p00.toNat % 2 ^ 32 + 2 ^ 32 * (mid.toNat % 2 ^ 32) := or_shl32_eq p00 mid
  have hhi : (p11 + (p01 >>> (32 : Nat)) + (p10 >>> (32 : Nat)) + (mid >>> (32 : Nat))).toNat =
      p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + mid.toNat / 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, bv64_ushr32, bv64_ushr32, bv64_ushr32,
      Nat.mod_eq_of_lt (by omega : p11.toNat + p01.toNat / 2 ^ 32 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 < 2 ^ 64),
      Nat.mod_eq_of_lt hhi_lt]
  have ha_eq : a.toNat = a0.toNat + 2 ^ 32 * a1.toNat := by rw [ha0, ha1]; omega
  have hb_eq : b.toNat = b0.toNat + 2 ^ 32 * b1.toNat := by rw [hb0, hb1]; omega
  rw [hlo, hhi]
  have hmid_split : mid.toNat = mid.toNat % 2 ^ 32 + 2 ^ 32 * (mid.toNat / 2 ^ 32) := by omega
  have hp00_split : p00.toNat = p00.toNat % 2 ^ 32 + 2 ^ 32 * (p00.toNat / 2 ^ 32) := by omega
  have hp01_split : p01.toNat = p01.toNat % 2 ^ 32 + 2 ^ 32 * (p01.toNat / 2 ^ 32) := by omega
  have hp10_split : p10.toNat = p10.toNat % 2 ^ 32 + 2 ^ 32 * (p10.toNat / 2 ^ 32) := by omega
  have hpow64 : (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 := by decide
  rw [ha_eq, hb_eq]
  calc
    p00.toNat % 2 ^ 32 + 2 ^ 32 * (mid.toNat % 2 ^ 32) +
        2 ^ 64 * (p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + mid.toNat / 2 ^ 32)
      = p00.toNat % 2 ^ 32 + 2 ^ 32 * (mid.toNat % 2 ^ 32 + 2 ^ 32 * (mid.toNat / 2 ^ 32)) +
        2 ^ 64 * (p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32) := by
        rw [hpow64]; simp only [Nat.mul_add, Nat.mul_assoc]; ac_rfl
    _ = p00.toNat % 2 ^ 32 + 2 ^ 32 * mid.toNat +
        2 ^ 64 * (p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32) := by
        rw [← hmid_split]
    _ = (p00.toNat % 2 ^ 32 + 2 ^ 32 * (p00.toNat / 2 ^ 32)) +
        2 ^ 32 * ((p01.toNat % 2 ^ 32 + 2 ^ 32 * (p01.toNat / 2 ^ 32)) +
          (p10.toNat % 2 ^ 32 + 2 ^ 32 * (p10.toNat / 2 ^ 32))) +
        2 ^ 64 * p11.toNat := by
        rw [hmid, hpow64]; simp only [Nat.mul_add, Nat.mul_assoc]; ac_rfl
    _ = p00.toNat + 2 ^ 32 * (p01.toNat + p10.toNat) + 2 ^ 64 * p11.toNat := by
        rw [← hp00_split, ← hp01_split, ← hp10_split]
    _ = (a0.toNat + 2 ^ 32 * a1.toNat) * (b0.toNat + 2 ^ 32 * b1.toNat) := by
        rw [hp00, hp01, hp10, hp11, hpow64]
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]; ac_rfl

theorem ar_cmul_wp (Γ : Env)
    (hMul : ∀ xs m Q X, u64Mul128Spec xs m Q X → Γ "u64_mul128" [i64, i64] [i64, i64] xs m Q X) :
    ∀ xs m Q X, arCmulSpec xs m Q X → Func.wp Γ ar_cmul_body xs m Q X := by
  rintro ⟨cx, al, ah, bl, bh, ⟨⟩⟩ m Q X ⟨s, R, hmasks, hm, hQ⟩
  c0_hsteps
  refine wp_call_of_spec _ _ (hMul _ _ _ _ (fun l h hm128 => ?_))
  c0_hsteps
  refine hQ _ _ ?_
  rw [coeff128_mask hmasks]
  have hmul : coeff128 s.modW l (h + al * bh + ah * bl) =
      coeff128 s.modW al ah * coeff128 s.modW bl bh := by
    have hmul_eq : coeff128 s.modW al ah * coeff128 s.modW bl bh =
        BitVec.ofNat s.modW
          ((al.toNat + 2 ^ 64 * ah.toNat) * (bl.toNat + 2 ^ 64 * bh.toNat)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [coeff128, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mod_mul_mod]
    rw [hmul_eq]
    apply coeff128_eq_of_mod128 hmasks.2.1
    have hpow : (2 ^ 128 : Nat) = 2 ^ 64 * 2 ^ 64 := by decide
    have hh : (h + al * bh + ah * bl).toNat =
        (h.toNat + al.toNat * bh.toNat + ah.toNat * bl.toNat) % 2 ^ 64 := by
      simp [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod]
    rw [hh, hpow]
    have hm1 :
        (l.toNat + 2 ^ 64 * ((h.toNat + al.toNat * bh.toNat + ah.toNat * bl.toNat) % 2 ^ 64)) %
        (2 ^ 64 * 2 ^ 64) =
        (l.toNat + 2 ^ 64 * (h.toNat + al.toNat * bh.toNat + ah.toNat * bl.toNat)) %
          (2 ^ 64 * 2 ^ 64) := by
      rw [Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_mod, ← Nat.mul_mod_mul_left, ← Nat.add_mod]
    rw [hm1, ← hpow]
    have hrhs : (al.toNat + 2 ^ 64 * ah.toNat) * (bl.toNat + 2 ^ 64 * bh.toNat) =
        (al.toNat * bl.toNat + 2 ^ 64 * (al.toNat * bh.toNat + ah.toNat * bl.toNat)) +
          2 ^ 128 * (ah.toNat * bh.toNat) := by
      rw [hpow]; simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]; ac_rfl
    change l.toNat + 2 ^ 64 * h.toNat = al.toNat * bl.toNat at hm128
    rw [hrhs, Nat.add_mul_mod_self_left, ← hm128]
    congr 1; simp only [Nat.mul_add]; ac_rfl
  exact hmul

private theorem mod_pow128_mul64 (a b : Nat) :
    (a + 2 ^ 64 * (b % 2 ^ 64)) % 2 ^ 128 = (a + 2 ^ 64 * b) % 2 ^ 128 := by
  have hpow : (2 ^ 128 : Nat) = 2 ^ 64 * 2 ^ 64 := by decide
  rw [hpow, Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_mod, ← Nat.mul_mod_mul_left, ← Nat.add_mod]

private theorem coeff128_add_of_nat (n : Nat) (a b c d : BitVec 64) :
    coeff128 n a b + coeff128 n c d =
      BitVec.ofNat n ((a.toNat + 2 ^ 64 * b.toNat) + (c.toNat + 2 ^ 64 * d.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [coeff128, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]

private theorem bv64_sub_add2 (a b : BitVec 64) : ((a - b - 1) + b + 1#64) = a := by bv_omega
private theorem bv64_sub_zero_add (a b : BitVec 64) : ((a - b - 0) + b) = a := by bv_omega
private theorem bv64_not_add_one_zero (a : BitVec 64) (h : (~~~a) + 1 = 0#64) : a = 0#64 := by
  bv_omega

private theorem nat_sum_carry (a b kc kd k : Nat) (h : k ≤ a + b) :
    (a + b - k) + (kc + kd + k) = (a + kc) + (b + kd) := by omega

private theorem nat_sum_nocarry (a b kc kd : Nat) :
    (a + b) + (kc + kd) = (a + kc) + (b + kd) := by omega

private theorem nat_sub_borrow (a b kc kd k : Nat) (_h : a < b) (_hb : b ≤ k) :
    (k + a - b) + kc + (b + kd) = a + (kc + kd + k) := by omega

private theorem nat_sub_noborrow (a b kc kd : Nat) (h : b ≤ a) :
    (a - b) + kc + (b + kd) = a + (kc + kd) := by omega

theorem ar_cadd_wp (Γ : Env) :
    ∀ xs m Q X, arCaddSpec xs m Q X → Func.wp Γ ar_cadd_body xs m Q X := by
  rintro ⟨cx, al, ah, bl, bh, ⟨⟩⟩ m Q X ⟨s, R, hmasks, hm, hQ⟩
  c0_hsteps
  · try clear J hJ
    refine hQ _ _ ?_
    rw [coeff128_mask hmasks, coeff128_add_of_nat]
    apply coeff128_eq_of_mod128 hmasks.2.1
    have hlt : al.toNat + bl.toNat ≥ 2 ^ 64 := by
      have h1 : (al + bl).toNat < al.toNat := hc
      rw [BitVec.toNat_add] at h1; omega
    have hl : (al + bl).toNat = al.toNat + bl.toNat - 2 ^ 64 := by
      rw [BitVec.toNat_add]; omega
    have hh : (ah + bh + 1).toNat = (ah.toNat + bh.toNat + 1) % 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
        Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have heq : (al.toNat + bl.toNat - 2 ^ 64) + 2 ^ 64 * (ah.toNat + bh.toNat + 1) =
        (al.toNat + 2 ^ 64 * ah.toNat) + (bl.toNat + 2 ^ 64 * bh.toNat) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      exact nat_sum_carry al.toNat bl.toNat (2 ^ 64 * ah.toNat) (2 ^ 64 * bh.toNat) (2 ^ 64) hlt
    rw [hh, mod_pow128_mul64, hl, heq]
  · try clear J hJ
    refine hQ _ _ ?_
    rw [coeff128_mask hmasks, coeff128_add_of_nat]
    apply coeff128_eq_of_mod128 hmasks.2.1
    have hlt : al.toNat + bl.toNat < 2 ^ 64 := by
      have h1 : al.toNat ≤ (al + bl).toNat := BitVec.not_lt.mp hc
      rw [BitVec.toNat_add] at h1; omega
    have hl : (al + bl).toNat = al.toNat + bl.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt]
    have hh : (ah + bh + 0).toNat = (ah.toNat + bh.toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, show (0 : BitVec 64).toNat = 0 from rfl,
        Nat.add_zero, Nat.mod_mod]
    have heq : (al.toNat + bl.toNat) + 2 ^ 64 * (ah.toNat + bh.toNat) =
        (al.toNat + 2 ^ 64 * ah.toNat) + (bl.toNat + 2 ^ 64 * bh.toNat) := by
      rw [Nat.mul_add]
      exact nat_sum_nocarry al.toNat bl.toNat (2 ^ 64 * ah.toNat) (2 ^ 64 * bh.toNat)
    rw [hh, mod_pow128_mul64, hl, heq]

theorem ar_csub_wp (Γ : Env) :
    ∀ xs m Q X, arCsubSpec xs m Q X → Func.wp Γ ar_csub_body xs m Q X := by
  rintro ⟨cx, al, ah, bl, bh, ⟨⟩⟩ m Q X ⟨s, R, hmasks, hm, hQ⟩
  c0_hsteps
  · try clear J hJ
    refine hQ _ _ ?_
    rw [coeff128_mask hmasks]
    apply bv_eq_sub_of_add_eq
    rw [coeff128_add_of_nat]
    apply coeff128_eq_of_mod128 hmasks.2.1
    have hlt : al.toNat < bl.toNat := hc
    have hl : (al - bl).toNat = 2 ^ 64 + al.toNat - bl.toNat := by
      rw [BitVec.toNat_sub]; have := al.isLt; have := bl.isLt; omega
    have hbmod : ((ah - bh - 1).toNat + bh.toNat + 1) % 2 ^ 64 = ah.toNat := by
      have h1 := congrArg BitVec.toNat (bv64_sub_add2 ah bh)
      rw [BitVec.toNat_add, BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
        Nat.add_mod, Nat.mod_mod, ← Nat.add_mod] at h1
      exact h1
    have hstep1 :
        ((al - bl).toNat + 2 ^ 64 * (ah - bh - 1).toNat + (bl.toNat + 2 ^ 64 * bh.toNat)) =
        al.toNat + 2 ^ 64 * ((ah - bh - 1).toNat + bh.toNat + 1) := by
      rw [hl, Nat.mul_add, Nat.mul_add, Nat.mul_one]
      exact nat_sub_borrow al.toNat bl.toNat (2 ^ 64 * (ah - bh - 1).toNat)
        (2 ^ 64 * bh.toNat) (2 ^ 64) hlt (by have := bl.isLt; omega)
    rw [hstep1, ← mod_pow128_mul64, hbmod]
  · try clear J hJ
    refine hQ _ _ ?_
    rw [coeff128_mask hmasks]
    apply bv_eq_sub_of_add_eq
    rw [coeff128_add_of_nat]
    apply coeff128_eq_of_mod128 hmasks.2.1
    have hle : bl.toNat ≤ al.toNat := BitVec.not_lt.mp hc
    have hl : (al - bl).toNat = al.toNat - bl.toNat := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
    have hbmod : ((ah - bh - 0).toNat + bh.toNat) % 2 ^ 64 = ah.toNat := by
      simpa [BitVec.toNat_add] using congrArg BitVec.toNat (bv64_sub_zero_add ah bh)
    have hstep1 :
        ((al - bl).toNat + 2 ^ 64 * (ah - bh - 0).toNat + (bl.toNat + 2 ^ 64 * bh.toNat)) =
        al.toNat + 2 ^ 64 * ((ah - bh - 0).toNat + bh.toNat) := by
      rw [hl, Nat.mul_add]
      exact nat_sub_noborrow al.toNat bl.toNat (2 ^ 64 * (ah - bh - 0).toNat)
        (2 ^ 64 * bh.toNat) hle
    rw [hstep1, ← mod_pow128_mul64, hbmod]

theorem ar_cneg_wp (Γ : Env) :
    ∀ xs m Q X, arCnegSpec xs m Q X → Func.wp Γ ar_cneg_body xs m Q X := by
  rintro ⟨cx, al, ah, ⟨⟩⟩ m Q X ⟨s, R, hmasks, hm, hQ⟩
  c0_hsteps
  · try clear J hJ
    refine hQ _ _ ?_
    rw [coeff128_mask hmasks]
    apply bv_eq_neg_of_add_eq_zero
    rw [coeff128_add_of_nat]
    apply coeff128_eq_of_mod128 hmasks.2.1
    have hal0 : al = 0#64 := bv64_not_add_one_zero al hc
    subst hal0
    have hlo0 : ((~~~0#64 : BitVec 64) + 1).toNat = 0 := by decide
    have hbmod : (((~~~ah) + 1).toNat + ah.toNat) % 2 ^ 64 = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_not, show (1 : BitVec 64).toNat = 1 from rfl]
      have ha := ah.isLt
      by_cases ha0 : ah.toNat = 0
      · simp [ha0]
      · have hlt1 : 2 ^ 64 - 1 - ah.toNat + 1 < 2 ^ 64 := by omega
        have hlt2 : 2 ^ 64 - 1 - ah.toNat + 1 + ah.toNat = 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hlt1, hlt2, Nat.mod_self]
    have hstep :
        0 + 2 ^ 64 * ((~~~ah) + 1).toNat + (0 + 2 ^ 64 * ah.toNat) =
        0 + 2 ^ 64 * (((~~~ah) + 1).toNat + ah.toNat) := by
      rw [Nat.mul_add]; omega
    rw [hlo0, show (0#64 : BitVec 64).toNat = 0 from rfl, hstep, ← mod_pow128_mul64, hbmod]
  · try clear J hJ
    refine hQ _ _ ?_
    rw [coeff128_mask hmasks]
    apply bv_eq_neg_of_add_eq_zero
    rw [coeff128_add_of_nat]
    apply coeff128_eq_of_mod128 hmasks.2.1
    have hnz : al.toNat ≠ 0 := by
      intro hz
      have hal0 : al = 0#64 := BitVec.eq_of_toNat_eq hz
      apply hc; subst hal0; decide
    have hl0 : ((~~~al) + 1).toNat + al.toNat = 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_not, show (1 : BitVec 64).toNat = 1 from rfl]
      have ha := al.isLt
      have hlt1 : 2 ^ 64 - 1 - al.toNat + 1 < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hlt1]; omega
    have hh0 : ((~~~ah) + 0).toNat + ah.toNat = 2 ^ 64 - 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_not, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
      have ha := ah.isLt
      have hlt1 : 2 ^ 64 - 1 - ah.toNat < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hlt1]; omega
    have hsum_nat : ∀ a1 a2 kc kd : Nat, (a1 + kc) + (a2 + kd) = (a1 + a2) + (kc + kd) := by
      intros; omega
    have htot :
        ((~~~al) + 1).toNat + 2 ^ 64 * ((~~~ah) + 0).toNat + (al.toNat + 2 ^ 64 * ah.toNat) =
        2 ^ 128 := by
      rw [hsum_nat, ← Nat.mul_add, hl0, hh0]
    rw [htot]

private theorem nat_add_sub_mid (x M K : Nat) (hx : x ≤ K) : x + M + (K - x) = M + K := by omega

private theorem pow64_mul_pred_add : 2 ^ 64 * (2 ^ 64 - 1) + 2 ^ 64 = 2 ^ 128 := by
  have h1 : 2 ^ 64 * (2 ^ 64 - 1) + 2 ^ 64 = 2 ^ 64 * ((2 ^ 64 - 1) + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [h1, Nat.sub_add_cancel (Nat.pow_pos (by decide : 0 < 2)), ← Nat.pow_add]

private theorem not_zero_bv64_toNat : (~~~0 : BitVec 64).toNat = 2 ^ 64 - 1 := by
  rw [BitVec.toNat_not, show (0 : BitVec 64).toNat = 0 from rfl, Nat.sub_zero]

private theorem coeff128_from_small_neg (n : Nat) (hn2 : n ≤ 128) (v : BitVec 64)
    (hmsb : 2 ^ 63 ≤ v.toNat) : coeff128 n v (~~~0) = BitVec.ofInt n v.toInt := by
  have hadd_eq : coeff128 n v (~~~0) + BitVec.ofNat n (2 ^ 64 - v.toNat) = 0#n := by
    apply BitVec.eq_of_toNat_eq
    have hvlt := v.isLt
    have htot : (v.toNat + 2 ^ 64 * (~~~0 : BitVec 64).toNat) + (2 ^ 64 - v.toNat) =
        2 ^ n * 2 ^ (128 - n) := by
      rw [not_zero_bv64_toNat,
        nat_add_sub_mid v.toNat (2 ^ 64 * (2 ^ 64 - 1)) (2 ^ 64) (Nat.le_of_lt hvlt),
        pow64_mul_pred_add, ← Nat.pow_add, Nat.add_sub_cancel' hn2]
    dsimp only [coeff128]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      ← Nat.add_mod, htot, Nat.mul_mod_right]
    exact (Nat.zero_mod _).symm
  have hneg := bv_eq_neg_of_add_eq_zero hadd_eq
  have hvint : v.toInt = (v.toNat : Int) - ((2 ^ 64 : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    by_cases h : 2 * v.toNat < 2 ^ 64
    · omega
    · simp only [h, ↓reduceIte]
  rw [hneg, hvint]
  have : (v.toNat : Int) - ((2 ^ 64 : Nat) : Int) = -((2 ^ 64 - v.toNat : Nat) : Int) := by
    have := v.isLt; omega
  rw [this, BitVec.ofInt_neg, BitVec.ofInt_natCast]

private theorem coeff128_from_small_pos (n : Nat) (v : BitVec 64) (hmsb : v.toNat < 2 ^ 63) :
    coeff128 n v 0 = BitVec.ofInt n v.toInt := by
  have hvint : v.toInt = (v.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    by_cases h : 2 * v.toNat < 2 ^ 64
    · simp only [h, ↓reduceIte]
    · omega
  rw [hvint, BitVec.ofInt_natCast]
  rw [coeff128, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]

private theorem coeff128_pow2_lo (n : Nat) (e : BitVec 32) (hlt : e.toNat < 64) :
    coeff128 n ((1 : BitVec 64) <<< ((BitVec.setWidth 64 e).toNat % 64)) 0 =
      BitVec.ofNat n (2 ^ e.toNat) := by
  have h1 : ((1 : BitVec 64) <<< ((BitVec.setWidth 64 e).toNat % 64)).toNat = 2 ^ e.toNat := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : e.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt hlt, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hlt)]
  rw [coeff128, h1, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]

private theorem coeff128_pow2_hi (n : Nat) (e : BitVec 32) (hge64 : 64 ≤ e.toNat)
    (hlt128 : e.toNat < 128) :
    coeff128 n 0 ((1 : BitVec 64) <<< ((BitVec.setWidth 64 (e - 64)).toNat % 64)) =
      BitVec.ofNat n (2 ^ e.toNat) := by
  have hsub : (e - 64).toNat = e.toNat - 64 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hge64)
  have hlt2 : e.toNat - 64 < 64 := by omega
  have h1 : ((1 : BitVec 64) <<< ((BitVec.setWidth 64 (e - 64)).toNat % 64)).toNat =
      2 ^ (e.toNat - 64) := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, hsub,
      show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : e.toNat - 64 < 2 ^ 64),
      Nat.mod_eq_of_lt hlt2, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hlt2)]
  rw [coeff128, h1, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add,
    ← Nat.pow_add, Nat.add_sub_cancel' hge64]

theorem ar_cfrom_small_wp (Γ : Env) :
    ∀ xs m Q X, arCfromSmallSpec xs m Q X → Func.wp Γ ar_cfrom_small_body xs m Q X := by
  rintro ⟨cx, v, ⟨⟩⟩ m Q X ⟨s, R, hmasks, hm, hQ⟩
  c0_hsteps
  · refine hQ _ _ ?_
    rw [coeff128_mask hmasks]
    have hmsb : 2 ^ 63 ≤ v.toNat := by
      have hnz : (v >>> (63 : Nat)).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hnz
      omega
    exact coeff128_from_small_neg s.modW hmasks.2.1 v hmsb
  · refine hQ _ _ ?_
    rw [coeff128_mask hmasks]
    have hmsb : v.toNat < 2 ^ 63 := by
      have hz : (v >>> (63 : Nat)).toNat = 0 := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hz
      omega
    exact coeff128_from_small_pos s.modW v hmsb

theorem ar_cpow2_wp (Γ : Env) :
    ∀ xs m Q X, arCpow2Spec xs m Q X → Func.wp Γ ar_cpow2_body xs m Q X := by
  rintro ⟨cx, e, ⟨⟩⟩ m Q X ⟨s, R, hmasks, hm, hQ⟩
  c0_hsteps
  · refine hQ _ _ ?_
    have hlt : e.toNat < 64 := hc
    have hlt128 : e.toNat < 128 := by omega
    rw [coeff128_mask hmasks]
    simp only [hlt128, ↓reduceIte]
    exact coeff128_pow2_lo s.modW e hlt
  · refine hQ _ _ ?_
    have hge64 : 64 ≤ e.toNat := Nat.not_lt.mp (by simpa using ‹¬ e.toNat < BitVec.toNat 64›)
    have hlt128 : e.toNat < 128 := hc
    rw [coeff128_mask hmasks]
    simp only [hlt128, ↓reduceIte]
    exact coeff128_pow2_hi s.modW e hge64 hlt128
  · refine hQ _ _ ?_
    have hge128 : ¬ e.toNat < 128 := hc
    rw [coeff128_mask hmasks]
    simp only [hge128, ↓reduceIte]
    exact coeff128_zero _

end

end LeanQbe.T.Examples.Arisca.Proof
