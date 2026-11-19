module

public import LeanQbe.T.OpsLemmas
import all Kraken.Mem

/-!
# Bit-vector and address arithmetic for `LeanQbe.T` proofs (`T4`)

Port of `LeanQbe/Logic/BitVec.lean` for 64-bit pointers (`BitVec 64`) and `Nat`/`UInt8` helpers.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Sign, mask, truncation -/

theorem sar63 (lit : BitVec 64) : lit.sshiftRight 63 = if lit.slt 0 then -1 else 0 := by grind

theorem negif (b : BitVec 64) (c : Bool) :
    (b ^^^ (if c then -1 else 0)) - (if c then -1 else 0) = if c then -b else b := by
  cases c <;> simp [BitVec.neg_eq_not_add, BitVec.sub_eq_add_neg]
  exact BitVec.xor_allOnes

theorem ofInt_take_toNat (v : BitVec 64) {w : Nat} :
    BitVec.ofInt 64 ((v.toNat : Int).take w) = (v.setWidth w).setWidth 64 := by grind

/-! ## Address arithmetic -/

theorem ptr4 (p : BitVec 64) (i : Nat) :
    p + BitVec.ofNat 64 (4 * i) + 4 = p + BitVec.ofNat 64 (4 * (i + 1)) := by grind

theorem ptr4_sub (p : BitVec 64) (i : Nat) :
    p + BitVec.ofNat 64 (4 * (i + 1)) - 4 = p + BitVec.ofNat 64 (4 * i) := by grind

theorem shl_two (x : BitVec 64) : x <<< 2 = BitVec.ofNat 64 (4 * x.toNat) := by grind

@[simp] theorem shl_three (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft]; omega

theorem ptr_add_ofNat (base : BitVec 64) (a b : Nat) :
    base + BitVec.ofNat 64 a + BitVec.ofNat 64 b = base + BitVec.ofNat 64 (a + b) := by grind

theorem ptr_step_1 (base : BitVec 64) (i : Nat) :
    base + BitVec.ofNat 64 i + 1 = base + BitVec.ofNat 64 (i + 1) :=
  ptr_add_ofNat base i 1

theorem cursor_eq_iff {base : BitVec 64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 j ↔ i = j := by grind

/-! ## `BitVec.ofNat 64` and `Nat` -/

theorem bv64_u8_eq {b k : UInt8} :
    BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 k.toNat ↔ b = k := by grind

theorem u8_le_iff_toNat {a b : UInt8} : a ≤ b ↔ a.toNat ≤ b.toNat :=
  UInt8.le_iff_toBitVec_le.trans BitVec.le_def

theorem u8_sub_ult_eq (lo len : Nat) (hlen : 0 < len) (h : lo + len ≤ 256) (b : UInt8) :
    (BitVec.ofNat 64 b.toNat - BitVec.ofNat 64 lo).ult (BitVec.ofNat 64 len) =
      (decide (lo ≤ b.toNat) && decide (b.toNat ≤ lo + len - 1)) := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  have ha : b.toNat < 2 ^ 64 := Nat.lt_trans hb (by decide)
  have hlo : lo < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  by_cases hle : lo ≤ b.toNat
  · have hsub : BitVec.ofNat 64 b.toNat - BitVec.ofNat 64 lo = BitVec.ofNat 64 (b.toNat - lo) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hlo]; omega),
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b.toNat - lo < 2 ^ 64),
      Nat.mod_eq_of_lt hlen64]
    by_cases hhi : b.toNat ≤ lo + len - 1 <;> simp [hle, hhi] <;> omega
  · simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hlen64]
    rw [Nat.mod_eq_of_lt (by omega : 2 ^ 64 - lo + b.toNat < 2 ^ 64)]
    have hf : decide (2 ^ 64 - lo + b.toNat < len) = false := decide_eq_false (by omega)
    simp [hle, hf]

theorem bv_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by grind

theorem bv_add_ofNat_toNat {a : BitVec 64} {n : Nat} (h : a.toNat + n < 2 ^ 64) :
    (a + BitVec.ofNat 64 n).toNat = a.toNat + n := by grind

theorem bv_sub_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by grind

theorem bv_shl_ofNat {a k : Nat} (ha : a < 2 ^ 64) (_hk : k < 64) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a <<< k) := by grind

theorem bv_shr_ofNat {a k : Nat} (ha : a < 2 ^ 64) (_hk : k < 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a >>> k) :=
  BitVec.eq_of_toNat_eq (by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)])

theorem bv_shr_one {u : Nat} (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u >>> (1 : Nat) = BitVec.ofNat 64 (u / 2) := by grind

theorem bv_and_pow2_sub_one {a k : Nat} (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ k - 1) = BitVec.ofNat 64 (a % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a _) ha)]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · simp [hi, Bool.and_comm]
  · have hai : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, hai]

theorem bv_and_one {u : Nat} (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u &&& (1 : BitVec 64) = BitVec.ofNat 64 (u % 2) :=
  bv_and_pow2_sub_one (k := 1) hu

theorem bv_align_pow2 {x k : Nat} (hk : k < 64) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& (-(BitVec.ofNat 64 (2 ^ k))) = BitVec.ofNat 64 ((x / 2 ^ k) * 2 ^ k) := by
  have hp : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have hpow_pos : 0 < 2 ^ k := @Nat.two_pow_pos k
  have hlt : (x / 2 ^ k) * 2 ^ k < 2 ^ 64 := by
    have := Nat.div_mul_le_self x (2 ^ k); omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hlt]
  have hm : (2 ^ 64 - 2 ^ k) % 2 ^ 64 = 2 ^ 64 - 2 ^ k := by omega
  have hsh : (x >>> k) <<< k = x &&& (2 ^ 64 - 2 ^ k) := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and]
    by_cases hik : k ≤ i <;> by_cases hi64 : i < 64
    · have ht1 : (2 ^ 64 - 2 ^ k).testBit i = true := by
        have hsub : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) <<< k := by
          rw [Nat.shiftLeft_eq, Nat.mul_sub_right_distrib, Nat.one_mul, ← Nat.pow_add,
            Nat.sub_add_cancel (by omega)]
        rw [hsub, Nat.testBit_shiftLeft]
        simp [hik, Nat.testBit_two_pow_sub_one, show i - k < 64 - k by omega]
      simp [hik, ht1, Nat.add_sub_cancel' hik]
    · have hx0 : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hik, Nat.add_sub_cancel' hik, hx0]
    · have ht0 : (2 ^ 64 - 2 ^ k).testBit i = false := by
        have hsub : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) <<< k := by
          rw [Nat.shiftLeft_eq, Nat.mul_sub_right_distrib, Nat.one_mul, ← Nat.pow_add,
            Nat.sub_add_cancel (by omega)]
        rw [hsub, Nat.testBit_shiftLeft]
        simp [hik]
      simp [hik, ht0]
    · have hx0 : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hik, hx0]
  rw [hm, ← hsh, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

theorem bv_ult_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv_ule_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = decide (a ≤ b) := by
  simp [BitVec.ule, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv_eq_zero_iff {v : Nat} (hv : v < 2 ^ 64) :
    BitVec.ofNat 64 v = (0 : BitVec 64) ↔ v = 0 := by grind

/-! ## Comparisons under `jnz` -/

theorem ult_branch {a b : Nat} {P Q : Prop} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ht : a < b → P) (hf : ¬ a < b → Q) :
    ((BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true → P) ∧
    ((BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false → Q) :=
  ⟨fun h => ht (by simpa [bv_ult_eq ha hb] using h),
   fun h => hf (by simpa [bv_ult_eq ha hb] using h)⟩

theorem ule_branch {a b : Nat} {P Q : Prop} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ht : a ≤ b → P) (hf : ¬ a ≤ b → Q) :
    ((BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true → P) ∧
    ((BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = false → Q) :=
  ⟨fun h => ht (by simpa [bv_ule_eq ha hb] using h),
   fun h => hf (by simpa [bv_ule_eq ha hb] using h)⟩

theorem bv_eq_zero_branch {v : Nat} {P Q : Prop} (hv : v < 2 ^ 64)
    (hz : v = 0 → P) (hnz : v ≠ 0 → Q) :
    (BitVec.ofNat 64 v = (0 : BitVec 64) → P) ∧
    (BitVec.ofNat 64 v ≠ (0 : BitVec 64) → Q) := by grind

@[simp] theorem setWidth64_ofNat8 (b : UInt8) :
    (BitVec.ofNat 8 b.toNat).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.toNat_lt
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]

theorem bv_odd_branch {u : Nat} {P Q : Prop} (hu : u < 2 ^ 64)
    (hodd : (u % 2 != 0) = true → P) (heven : (u % 2 != 0) = false → Q) :
    (BitVec.ofNat 64 u &&& (1 : BitVec 64) ≠ 0 → P) ∧
    (BitVec.ofNat 64 u &&& (1 : BitVec 64) = 0 → Q) := by grind

theorem u8_eq_branch {b : UInt8} {n : Nat} [OfNat (BitVec 64) n] [OfNat UInt8 n]
    {P Q : Prop}
    (ht : (b == OfNat.ofNat n) = true → P)
    (hf : (b == OfNat.ofNat n) = false → Q)
    (hk : (OfNat.ofNat n : BitVec 64) = BitVec.ofNat 64 (OfNat.ofNat n : UInt8).toNat := by rfl) :
    (BitVec.ofNat 64 b.toNat = OfNat.ofNat n → P) ∧
    (BitVec.ofNat 64 b.toNat ≠ OfNat.ofNat n → Q) := by
  rw [hk, bv64_u8_eq]
  grind

theorem cursor_eof_branch {base : BitVec 64} {i n : Nat} {P Q : Prop}
    (hi : i ≤ n) (hn : n < 2 ^ 64)
    (heof : i = n → P) (hneof : i < n → Q) :
    (base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 n → P) ∧
    (base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 n → Q) := by grind

end LeanQbe.T
