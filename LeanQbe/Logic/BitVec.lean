module

public import LeanQbe.Ops
import all Kraken.Mem

/-!
# Bit-vector and address arithmetic for user proofs

Facts about `Val = BitVec 64` that proofs of QBE programs keep needing. None of them mentions memory.

* Sign and mask idioms: `sar63`, `negif`; truncation: `ofInt_take_toNat`.
* Address arithmetic: `ptr4`, `ptr4_sub`, `shl_two`, `ptr_add_ofNat`, `ptr_step_1`, `cursor_eq_iff`.
* `BitVec.ofNat 64` against the operations of `Nat`: `bv_add_ofNat`, `bv_add_ofNat_toNat`, `bv_sub_ofNat`,
  `bv_shl_ofNat`, `bv_shr_ofNat`, `bv_and_pow2_sub_one`, `bv_align_pow2`, `bv_ult_eq`, `bv_ule_eq`,
  `bv_eq_zero_iff`, …
* Bytes (`UInt8`) as values: `bv64_u8_eq`, `u8_le_iff_toNat`, and the range test `lo ≤ b ≤ lo + len - 1`
  done as one unsigned comparison (`u8_sub_ult_eq`).
* A comparison under `jnz`, in the shape `wp_unfold` leaves (two implications): `ult_branch`,
  `ule_branch`, `bv_eq_zero_branch`, `bv_odd_branch`, `cursor_eof_branch`; the `or` of two comparison
  results (`boolVal_or`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-! ## Sign, mask, truncation -/

theorem sar63 (lit : Val) : lit.sshiftRight 63 = if lit.slt 0 then -1 else 0 := by grind

theorem negif (b : Val) (c : Bool) :
    (b ^^^ (if c then -1 else 0)) - (if c then -1 else 0) = if c then -b else b := by
  cases c <;> simp [BitVec.neg_eq_not_add, BitVec.sub_eq_add_neg]
  exact BitVec.xor_allOnes

theorem ofInt_take_toNat (v : Val) {w : Nat} :
    BitVec.ofInt 64 ((v.toNat : Int).take w) = (v.setWidth w).setWidth 64 := by grind

/-! ## Address arithmetic -/

theorem ptr4 (p : Val) (i : Nat) :
    p + BitVec.ofNat 64 (4 * i) + 4 = p + BitVec.ofNat 64 (4 * (i + 1)) := by grind

theorem ptr4_sub (p : Val) (i : Nat) :
    p + BitVec.ofNat 64 (4 * (i + 1)) - 4 = p + BitVec.ofNat 64 (4 * i) := by grind

theorem shl_two (x : Val) : x <<< 2 = BitVec.ofNat 64 (4 * x.toNat) := by grind

theorem ptr_add_ofNat (base : Val) (a b : Nat) :
    base + BitVec.ofNat 64 a + BitVec.ofNat 64 b = base + BitVec.ofNat 64 (a + b) := by grind

theorem ptr_step_1 (base : Val) (i : Nat) :
    base + BitVec.ofNat 64 i + 1 = base + BitVec.ofNat 64 (i + 1) :=
  ptr_add_ofNat base i 1

theorem cursor_eq_iff {base : Val} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 j ↔ i = j := by grind

/-! ## `BitVec.ofNat 64` and `Nat` -/

theorem bv64_u8_eq {b k : UInt8} :
    BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 k.toNat ↔ b = k := by grind

theorem u8_le_iff_toNat {a b : UInt8} : a ≤ b ↔ a.toNat ≤ b.toNat :=
  UInt8.le_iff_toBitVec_le.trans BitVec.le_def

theorem u8_sub_ult_eq (lo len : Nat) (hlen : 0 < len) (h : lo + len ≤ 256) (b : UInt8) :
    (BitVec.ofNat 64 b.toNat - BitVec.ofNat 64 lo).ult (BitVec.ofNat 64 len) =
      (decide (lo ≤ b.toNat) && decide (b.toNat ≤ lo + len - 1)) := by grind

theorem bv_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by grind

theorem bv_add_ofNat_toNat {a : Val} {n : Nat} (h : a.toNat + n < 2 ^ 64) :
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
    BitVec.ofNat 64 u &&& (1 : Val) = BitVec.ofNat 64 (u % 2) :=
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
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by grind

theorem bv_ule_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = decide (a ≤ b) := by grind

theorem bv_eq_zero_iff {v : Nat} (hv : v < 2 ^ 64) :
    BitVec.ofNat 64 v = (0 : Val) ↔ v = 0 := by grind

/-! ## Comparisons under `jnz` -/

theorem boolVal_or (a b : Bool) : boolVal a ||| boolVal b = boolVal (a || b) := by
  cases a <;> cases b <;> decide

theorem ult_branch {a b : Nat} {P Q : Prop} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ht : a < b → P) (hf : ¬ a < b → Q) :
    ((BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true → P) ∧
    ((BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false → Q) := by grind

theorem ule_branch {a b : Nat} {P Q : Prop} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ht : a ≤ b → P) (hf : ¬ a ≤ b → Q) :
    ((BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true → P) ∧
    ((BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = false → Q) := by grind

theorem bv_eq_zero_branch {v : Nat} {P Q : Prop} (hv : v < 2 ^ 64)
    (hz : v = 0 → P) (hnz : v ≠ 0 → Q) :
    (BitVec.ofNat 64 v = (0 : Val) → P) ∧ (BitVec.ofNat 64 v ≠ (0 : Val) → Q) := by grind

theorem bv_odd_branch {u : Nat} {P Q : Prop} (hu : u < 2 ^ 64)
    (hodd : (u % 2 != 0) = true → P) (heven : (u % 2 != 0) = false → Q) :
    (BitVec.ofNat 64 u &&& (1 : Val) ≠ 0 → P) ∧
    (¬ BitVec.ofNat 64 u &&& (1 : Val) ≠ 0 → Q) := by grind

theorem cursor_eof_branch {base : Val} {i n : Nat} {P Q : Prop}
    (hi : i ≤ n) (hn : n < 2 ^ 64)
    (heof : i = n → P) (hneof : i < n → Q) :
    (base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 n → P) ∧
    (base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 n → Q) := by grind

end LeanQbe
