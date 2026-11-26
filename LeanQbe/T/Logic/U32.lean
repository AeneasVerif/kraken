module

public meta import Lean.Elab.Tactic

set_option autoImplicit false

/-!
Separation-free arithmetic, bit-twiddling, and `UInt8`/`UInt32`/`UInt64`/`BitVec` lemmas
and `u32_omega` automation.

This is a strictly separation-free leaf module (`Init` + `Lean.Elab.Tactic` only; no
`Kraken.Mem`, no `Kraken.Separation`, no `ProofKit`), safe to import at the bottom of
compiler, codec, and SAT solver proofs without pulling in memory-model dependencies.
-/

public section

namespace LeanQbe.T

/-! ## `Nat` case-split, size, & bitwise helpers -/

theorem nat_cases_le_step {n k : Nat} (h : n ≤ k + 1) : n ≤ k ∨ n = k + 1 := by
  omega

theorem nat_cases_le_zero {n : Nat} (h : n ≤ 0) : n = 0 := by
  omega

theorem u8_size_eq : UInt8.size = 256 := rfl
theorem u32_size_eq : UInt32.size = 4294967296 := rfl
theorem u64_size_eq : UInt64.size = 18446744073709551616 := rfl

private theorem pow2_8_eq : (2 : Nat) ^ 8 = 256 := rfl
private theorem pow2_32_eq : (2 : Nat) ^ 32 = 4294967296 := rfl
private theorem pow2_64_eq : (2 : Nat) ^ 64 = 18446744073709551616 := rfl

private theorem nat_testBit_two_mul (k j : Nat) :
    (2 * k).testBit j = if j = 0 then false else k.testBit (j - 1) := by
  have h := Nat.testBit_two_pow_mul_add k (b := 0) (i := 1) (by omega) j
  by_cases hj : j = 0
  · subst hj; simp at h ⊢
  · have hj' : ¬ (j < 1) := by omega
    simp [hj, hj'] at h ⊢; exact h

private theorem nat_testBit_two_mul_add1 (k j : Nat) :
    (2 * k + 1).testBit j = if j = 0 then true else k.testBit (j - 1) := by
  have h := Nat.testBit_two_pow_mul_add k (b := 1) (i := 1) (by omega) j
  by_cases hj : j = 0
  · subst hj; simp at h ⊢
  · have hj' : ¬ (j < 1) := by omega
    simp [hj, hj'] at h ⊢; exact h

private theorem nat_testBit_one_eq (j : Nat) :
    (1 : Nat).testBit j = if j = 0 then true else false := by
  have h := nat_testBit_two_mul_add1 0 j
  simpa using h

private theorem nat_even_or_one (a : Nat) (ha : a % 2 = 0) : a ||| 1 = a + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, nat_testBit_two_mul, nat_testBit_one_eq, nat_testBit_two_mul_add1]
  by_cases hj : j = 0 <;> simp [hj]

private theorem nat_even_xor_one (a : Nat) (ha : a % 2 = 0) : a ^^^ 1 = a + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, nat_testBit_two_mul, nat_testBit_one_eq, nat_testBit_two_mul_add1]
  by_cases hj : j = 0 <;> simp [hj]

private theorem nat_odd_xor_one (a : Nat) (ha : a % 2 = 1) : a ^^^ 1 = a - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  apply Nat.eq_of_testBit_eq
  intro j
  have hsub : 2 * k + 1 - 1 = 2 * k := by omega
  rw [hsub, Nat.testBit_xor, nat_testBit_two_mul_add1, nat_testBit_one_eq, nat_testBit_two_mul]
  by_cases hj : j = 0 <;> simp [hj]

/-! ## `UInt8` basic algebra -/

theorem u8_ext {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  UInt8.toNat_inj.mp h

theorem u8_eq_iff (a b : UInt8) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, u8_ext⟩

theorem u8_ne_iff (a b : UInt8) : a ≠ b ↔ a.toNat ≠ b.toNat :=
  not_congr (u8_eq_iff a b)

theorem u8_toNat_lt (a : UInt8) : a.toNat < 256 :=
  a.toBitVec.isLt

theorem u8_ofNat_toNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  change (BitVec.ofNat 8 n).toNat = n % 256
  rw [BitVec.toNat_ofNat, pow2_8_eq]

theorem u8_ofNat_lit_toNat (n : Nat) (h : n < 256 := by omega) :
    (OfNat.ofNat n : UInt8).toNat = n := by
  change (UInt8.ofNat n).toNat = n
  rw [u8_ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem u8_ofNat_toNat_lt {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  rw [u8_ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem u8_ofNat_eq {n m : Nat} (h : n % 256 = m % 256) : UInt8.ofNat n = UInt8.ofNat m :=
  u8_ext (by rw [u8_ofNat_toNat, u8_ofNat_toNat, h])

theorem u8_toNat_sub_of_le_toNat {a b : UInt8} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  UInt8.toNat_sub_of_le a b (UInt8.le_iff_toNat_le.mpr h)

theorem u8_toNat_sub_of_eq {a b : UInt8} (h : a.toNat = b.toNat) : (a - b).toNat = 0 := by
  rw [u8_toNat_sub_of_le_toNat (Nat.le_of_eq h.symm), h, Nat.sub_self]

theorem u8_eq_ofNat_of_le_ne {a : UInt8} {k : Nat} (hle : a.toNat ≤ k)
    (hne : a ≠ UInt8.ofNat k) (hk : k < 256) : a.toNat ≤ k - 1 := by
  have hneNat : a.toNat ≠ (UInt8.ofNat k).toNat := (u8_ne_iff _ _).mp hne
  rw [u8_ofNat_toNat_lt hk] at hneNat
  omega

theorem u8_cases_le {a : UInt8} {k : Nat} (h : a.toNat ≤ k + 1) (hk : k + 1 < 256) :
    a.toNat ≤ k ∨ a = UInt8.ofNat (k + 1) := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · exact Or.inl (Nat.le_of_lt_succ hlt)
  · exact Or.inr (u8_ext (by rw [heq, u8_ofNat_toNat_lt hk]))

/-! ## `UInt32` basic algebra, wraparound, and packing -/

theorem u32_ext {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.toNat_inj.mp h

theorem u32_eq_iff (a b : UInt32) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, u32_ext⟩

theorem u32_ne_iff (a b : UInt32) : a ≠ b ↔ a.toNat ≠ b.toNat :=
  not_congr (u32_eq_iff a b)

theorem u32_toNat_lt (a : UInt32) : a.toNat < 4294967296 :=
  a.toBitVec.isLt

theorem u32_ofNat_toNat (n : Nat) : (UInt32.ofNat n).toNat = n % 4294967296 := by
  change (BitVec.ofNat 32 n).toNat = n % 4294967296
  rw [BitVec.toNat_ofNat, pow2_32_eq]

theorem u32_ofNat_lit_toNat (n : Nat) (h : n < 4294967296 := by omega) :
    (OfNat.ofNat n : UInt32).toNat = n := by
  change (UInt32.ofNat n).toNat = n
  rw [u32_ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem u32_ofNat_toNat_lt {n : Nat} (h : n < 4294967296) : (UInt32.ofNat n).toNat = n := by
  rw [u32_ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem u32_ofNat_eq {n m : Nat} (h : n % 4294967296 = m % 4294967296) :
    UInt32.ofNat n = UInt32.ofNat m :=
  u32_ext (by rw [u32_ofNat_toNat, u32_ofNat_toNat, h])

theorem u32_eq_zero_of_toNat_eq_zero {a : UInt32} (h : a.toNat = 0) : a = 0 :=
  u32_ext (by simpa using h)

theorem u32_ne_zero_of_toNat_pos {a : UInt32} (h : 0 < a.toNat) : a ≠ 0 := by
  intro h0
  subst h0
  simp at h

theorem u32_toNat_pos_of_ne_zero {a : UInt32} (h : a ≠ 0) : 0 < a.toNat := by
  have ha : a.toNat ≠ 0 := fun hz => h (u32_eq_zero_of_toNat_eq_zero hz)
  omega

theorem u32_add_zero (a : UInt32) : a + 0 = a :=
  UInt32.add_zero a

theorem u32_add_assoc (a b c : UInt32) : a + b + c = a + (b + c) :=
  UInt32.add_assoc a b c

theorem u32_add_ofNat_lt {a : UInt32} {k : Nat} (h : a.toNat + k < 4294967296) :
    (a + UInt32.ofNat k).toNat = a.toNat + k := by
  rw [UInt32.toNat_add, u32_ofNat_toNat, pow2_32_eq]
  have ha := u32_toNat_lt a
  omega

theorem u32_add1_toNat {a : UInt32} (h : a.toNat + 1 < 4294967296) :
    (a + 1).toNat = a.toNat + 1 := by
  change (a + UInt32.ofNat 1).toNat = a.toNat + 1
  exact u32_add_ofNat_lt h

theorem u32_ofNat_add_eq (n m : Nat) :
    UInt32.ofNat (n + m) = UInt32.ofNat n + UInt32.ofNat m :=
  u32_ext (by
    rw [u32_ofNat_toNat, UInt32.toNat_add, u32_ofNat_toNat, u32_ofNat_toNat, pow2_32_eq,
      Nat.add_mod])

theorem u32_succ_add_ofNat (a : UInt32) (n : Nat) :
    a + UInt32.ofNat (n + 1) = (a + UInt32.ofNat n) + 1 := by
  rw [show UInt32.ofNat (n + 1) = UInt32.ofNat n + 1 from u32_ofNat_add_eq n 1,
    UInt32.add_assoc]

theorem u32_eq_add_of_toNat {a b : UInt32} (h : a.toNat = b.toNat + 1) : a = b + 1 := by
  have hb : b.toNat + 1 < 4294967296 := h ▸ a.toBitVec.isLt
  exact u32_ext (by rw [h, u32_add1_toNat hb])

theorem u32_ofNat_succ_add (a : UInt32) (k : Nat) :
    a + UInt32.ofNat k + 1 = a + UInt32.ofNat (k + 1) :=
  (u32_succ_add_ofNat a k).symm

theorem u32_ofNat_succ_sub_one (k : Nat) : UInt32.ofNat (k + 1) - 1 = UInt32.ofNat k :=
  u32_ext (by
    rw [UInt32.toNat_sub, u32_ofNat_toNat, u32_ofNat_toNat, pow2_32_eq]
    have h1 : (1 : UInt32).toNat = 1 := rfl
    rw [h1]
    omega)

theorem u32_toNat_sub_of_le_toNat {a b : UInt32} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  UInt32.toNat_sub_of_le a b (UInt32.le_iff_toNat_le.mpr h)

theorem u32_toNat_sub_of_eq {a b : UInt32} (h : a.toNat = b.toNat) : (a - b).toNat = 0 := by
  rw [u32_toNat_sub_of_le_toNat (Nat.le_of_eq h.symm), h, Nat.sub_self]

theorem u32_sub1_toNat {a : UInt32} (h : 0 < a.toNat) : (a - 1).toNat = a.toNat - 1 :=
  u32_toNat_sub_of_le_toNat (Nat.succ_le_of_lt h)

theorem u32_sub_ofNat {a : UInt32} {k : Nat} (h : k ≤ a.toNat) (hk : k < 4294967296) :
    (a - UInt32.ofNat k).toNat = a.toNat - k := by
  have hk' : (UInt32.ofNat k).toNat ≤ a.toNat := by
    rw [u32_ofNat_toNat_lt hk]
    exact h
  rw [u32_toNat_sub_of_le_toNat hk', u32_ofNat_toNat_lt hk]

theorem u32_sub_ofNat_toNat (n k : Nat) (h : k ≤ n) (hn : n < 4294967296) :
    (UInt32.ofNat n - UInt32.ofNat k).toNat = n - k := by
  rw [u32_sub_ofNat, u32_ofNat_toNat_lt hn]
  · rw [u32_ofNat_toNat_lt hn]; exact h
  · omega

theorem u32_sub1_ge {a : UInt32} {n : Nat} (h : n + 1 ≤ a.toNat) : n ≤ (a - 1).toNat := by
  rw [u32_sub1_toNat (by omega)]
  omega

theorem u32_sub_sub_ofNat (a : UInt32) (n : Nat) :
    a - UInt32.ofNat n - 1 = a - UInt32.ofNat (n + 1) := by
  apply u32_ext
  have ha := u32_toNat_lt a
  have h1 : (1 : UInt32).toNat = 1 := rfl
  rw [UInt32.toNat_sub, UInt32.toNat_sub, UInt32.toNat_sub, u32_ofNat_toNat,
    u32_ofNat_toNat, pow2_32_eq, h1]
  omega

theorem u32_sub1_sub (a b : UInt32) : a - 1 - b = a - (b + 1) := by
  apply u32_ext
  have ha := u32_toNat_lt a
  have hb := u32_toNat_lt b
  have h1 : (1 : UInt32).toNat = 1 := rfl
  rw [UInt32.toNat_sub, UInt32.toNat_sub, UInt32.toNat_sub, UInt32.toNat_add, pow2_32_eq, h1]
  omega

theorem u32_cnt_sub1_add {cnt : UInt32} (h : 0 < cnt.toNat) :
    cnt - 1 + 1 = cnt := by
  apply u32_ext
  have h1 : (cnt - 1).toNat = cnt.toNat - 1 := u32_sub1_toNat h
  have hlt : (cnt - 1).toNat + 1 < 4294967296 := by
    have := u32_toNat_lt cnt
    omega
  rw [u32_add1_toNat hlt, h1]
  omega

theorem u32_cnt_sub1_lt {cnt : UInt32} (h : 0 < cnt.toNat) : (cnt - 1).toNat < cnt.toNat := by
  rw [u32_sub1_toNat h]
  omega

theorem u32_sub1_lt {cnt : UInt32} (h : cnt ≠ 0) : (cnt - 1).toNat < cnt.toNat :=
  u32_cnt_sub1_lt (u32_toNat_pos_of_ne_zero h)

theorem u32Sub1Lt {cnt : UInt32} (h : cnt ≠ 0) : (cnt - 1).toNat < cnt.toNat :=
  u32_sub1_lt h

private theorem nat_pack4_shift (b0 b1 b2 b3 : UInt8) :
    b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 < 4294967296 := by
  have := u8_toNat_lt b0
  have := u8_toNat_lt b1
  have := u8_toNat_lt b2
  have := u8_toNat_lt b3
  omega

private theorem bv32_pack_getLsbD (b0 b1 b2 b3 : UInt8) (j : Nat) (hj : j < 32) :
    (BitVec.setWidth 32 b0.toBitVec |||
      (BitVec.setWidth 32 b1.toBitVec <<< (8 : Nat)) |||
      (BitVec.setWidth 32 b2.toBitVec <<< (16 : Nat)) |||
      (BitVec.setWidth 32 b3.toBitVec <<< (24 : Nat))).getLsbD j =
      if j < 8 then b0.toBitVec.getLsbD j
      else if j < 16 then b1.toBitVec.getLsbD (j - 8)
      else if j < 24 then b2.toBitVec.getLsbD (j - 16)
      else b3.toBitVec.getLsbD (j - 24) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hj,
    decide_true, Bool.true_and]
  by_cases h8 : j < 8
  · have h16 : j < 16 := by omega
    have h24 : j < 24 := by omega
    simp [h8, h16, h24]
  · by_cases h16 : j < 16
    · have h24 : j < 24 := by omega
      have hb0 : b0.toBitVec.getLsbD j = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [h8, h16, h24, hb0, show j - 8 < 32 by omega]
    · by_cases h24 : j < 24
      · have hb0 : b0.toBitVec.getLsbD j = false := BitVec.getLsbD_of_ge _ _ (by omega)
        have hb1 : b1.toBitVec.getLsbD (j - 8) = false := BitVec.getLsbD_of_ge _ _ (by omega)
        simp [h8, h16, h24, hb0, hb1, show j - 8 < 32 by omega, show j - 16 < 32 by omega]
      · have hb0 : b0.toBitVec.getLsbD j = false := BitVec.getLsbD_of_ge _ _ (by omega)
        have hb1 : b1.toBitVec.getLsbD (j - 8) = false := BitVec.getLsbD_of_ge _ _ (by omega)
        have hb2 : b2.toBitVec.getLsbD (j - 16) = false := BitVec.getLsbD_of_ge _ _ (by omega)
        simp [h8, h16, h24, hb0, hb1, hb2, show j - 8 < 32 by omega,
          show j - 16 < 32 by omega, show j - 24 < 32 by omega]

private theorem u32_pack_toBitVec (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
      (b3.toUInt32 <<< 24)).toBitVec =
    (BitVec.setWidth 32 b0.toBitVec |||
      (BitVec.setWidth 32 b1.toBitVec <<< (8 : Nat)) |||
      (BitVec.setWidth 32 b2.toBitVec <<< (16 : Nat)) |||
      (BitVec.setWidth 32 b3.toBitVec <<< (24 : Nat))) := by
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32]
  rfl

private theorem bv32_shiftRight_nat (x : BitVec 32) (n : UInt32) (hn : n.toBitVec.toNat < 32)
    (k : Nat) (hk : n.toBitVec.toNat = k) :
    x >>> (n.toBitVec % 32) = x >>> k := by
  subst hk
  change BitVec.ushiftRight x (n.toBitVec % 32).toNat = BitVec.ushiftRight x n.toBitVec.toNat
  congr 1
  rw [BitVec.toNat_umod, show (32 : BitVec 32).toNat = 32 from rfl, Nat.mod_eq_of_lt hn]

theorem u32_pack_unpack_bytes (b0 b1 b2 b3 : UInt8) :
    let w : UInt32 :=
      b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    w.toUInt8 = b0 ∧
      (w >>> 8).toUInt8 = b1 ∧
      (w >>> 16).toUInt8 = b2 ∧
      (w >>> 24).toUInt8 = b3 := by
  intro w
  have hw : w.toBitVec =
      BitVec.setWidth 32 b0.toBitVec |||
      (BitVec.setWidth 32 b1.toBitVec <<< (8 : Nat)) |||
      (BitVec.setWidth 32 b2.toBitVec <<< (16 : Nat)) |||
      (BitVec.setWidth 32 b3.toBitVec <<< (24 : Nat)) :=
    u32_pack_toBitVec b0 b1 b2 b3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toBitVec_inj.mp <;> apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi
  · simp only [UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, show i < 8 from hi,
      decide_true, Bool.true_and, hw]
    rw [bv32_pack_getLsbD b0 b1 b2 b3 i (by omega)]
    simp [hi]
  · simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, BitVec.getLsbD_setWidth,
      show i < 8 from hi, decide_true, Bool.true_and]
    rw [bv32_shiftRight_nat w.toBitVec 8 (by decide) 8 rfl, BitVec.getLsbD_ushiftRight,
      hw, bv32_pack_getLsbD b0 b1 b2 b3 (8 + i) (by omega)]
    simp [show ¬ (8 + i < 8) by omega, show 8 + i < 16 by omega, show 8 + i - 8 = i by omega]
  · simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, BitVec.getLsbD_setWidth,
      show i < 8 from hi, decide_true, Bool.true_and]
    rw [bv32_shiftRight_nat w.toBitVec 16 (by decide) 16 rfl, BitVec.getLsbD_ushiftRight,
      hw, bv32_pack_getLsbD b0 b1 b2 b3 (16 + i) (by omega)]
    simp [show ¬ (16 + i < 8) by omega, show ¬ (16 + i < 16) by omega,
      show 16 + i < 24 by omega, show 16 + i - 16 = i by omega]
  · simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, BitVec.getLsbD_setWidth,
      show i < 8 from hi, decide_true, Bool.true_and]
    rw [bv32_shiftRight_nat w.toBitVec 24 (by decide) 24 rfl, BitVec.getLsbD_ushiftRight,
      hw, bv32_pack_getLsbD b0 b1 b2 b3 (24 + i) (by omega)]
    simp [show ¬ (24 + i < 8) by omega, show ¬ (24 + i < 16) by omega,
      show ¬ (24 + i < 24) by omega, show 24 + i - 24 = i by omega]

theorem u32_of_u8_pack (w : UInt32) :
    w =
      w.toUInt8.toUInt32 |||
      ((w >>> 8).toUInt8.toUInt32 <<< 8) |||
      ((w >>> 16).toUInt8.toUInt32 <<< 16) |||
      ((w >>> 24).toUInt8.toUInt32 <<< 24) := by
  apply UInt32.toBitVec_inj.mp
  rw [u32_pack_toBitVec]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bv32_pack_getLsbD _ _ _ _ i hi]
  simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, BitVec.getLsbD_setWidth]
  rw [bv32_shiftRight_nat w.toBitVec 8 (by decide) 8 rfl,
    bv32_shiftRight_nat w.toBitVec 16 (by decide) 16 rfl,
    bv32_shiftRight_nat w.toBitVec 24 (by decide) 24 rfl,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  by_cases h8 : i < 8
  · simp [h8]
  · by_cases h16 : i < 16
    · simp [h8, h16, show i - 8 < 8 by omega, show 8 + (i - 8) = i by omega]
    · by_cases h24 : i < 24
      · simp [h8, h16, h24, show i - 16 < 8 by omega, show 16 + (i - 16) = i by omega]
      · simp [h8, h16, h24, show i - 24 < 8 by omega, show 24 + (i - 24) = i by omega]

/-! ## `UInt64` basic algebra and `UInt32` packing -/

theorem u64_ext {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.toNat_inj.mp h

theorem u64_eq_iff (a b : UInt64) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, u64_ext⟩

theorem u64_ne_iff (a b : UInt64) : a ≠ b ↔ a.toNat ≠ b.toNat :=
  not_congr (u64_eq_iff a b)

theorem u64_toNat_lt (a : UInt64) : a.toNat < 18446744073709551616 :=
  a.toBitVec.isLt

theorem u64_ofNat_toNat (n : Nat) : (UInt64.ofNat n).toNat = n % 18446744073709551616 := by
  change (BitVec.ofNat 64 n).toNat = n % 18446744073709551616
  rw [BitVec.toNat_ofNat, pow2_64_eq]

theorem u64_ofNat_lit_toNat (n : Nat) (h : n < 18446744073709551616 := by omega) :
    (OfNat.ofNat n : UInt64).toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [u64_ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem u64_ofNat_toNat_lt {n : Nat} (h : n < 18446744073709551616) :
    (UInt64.ofNat n).toNat = n := by
  rw [u64_ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem u64_ofNat_eq {n m : Nat}
    (h : n % 18446744073709551616 = m % 18446744073709551616) :
    UInt64.ofNat n = UInt64.ofNat m :=
  u64_ext (by rw [u64_ofNat_toNat, u64_ofNat_toNat, h])

theorem u64_toNat_sub_of_le_toNat {a b : UInt64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le a b (UInt64.le_iff_toNat_le.mpr h)

theorem u64_toNat_sub_of_eq {a b : UInt64} (h : a.toNat = b.toNat) : (a - b).toNat = 0 := by
  rw [u64_toNat_sub_of_le_toNat (Nat.le_of_eq h.symm), h, Nat.sub_self]

private theorem u64_pack_toBitVec (lo hi : UInt32) :
    (lo.toUInt64 ||| (hi.toUInt64 <<< 32)).toBitVec =
      (BitVec.setWidth 64 lo.toBitVec ||| (BitVec.setWidth 64 hi.toBitVec <<< (32 : Nat))) := by
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64]
  rfl

private theorem bv64_pack_getLsbD (lo hi : UInt32) (j : Nat) (hj : j < 64) :
    (BitVec.setWidth 64 lo.toBitVec |||
      (BitVec.setWidth 64 hi.toBitVec <<< (32 : Nat))).getLsbD j =
      if j < 32 then lo.toBitVec.getLsbD j else hi.toBitVec.getLsbD (j - 32) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hj,
    decide_true, Bool.true_and]
  by_cases h32 : j < 32
  · simp [h32]
  · have hlo : lo.toBitVec.getLsbD j = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [h32, hlo, show j - 32 < 64 by omega]

private theorem bv64_shiftRight_nat (x : BitVec 64) (n : UInt64) (hn : n.toBitVec.toNat < 64)
    (k : Nat) (hk : n.toBitVec.toNat = k) :
    x >>> (n.toBitVec % 64) = x >>> k := by
  subst hk
  change BitVec.ushiftRight x (n.toBitVec % 64).toNat = BitVec.ushiftRight x n.toBitVec.toNat
  congr 1
  rw [BitVec.toNat_umod, show (64 : BitVec 64).toNat = 64 from rfl, Nat.mod_eq_of_lt hn]

theorem u64_pack_unpack_u32 (lo hi : UInt32) :
    let w : UInt64 := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
    w.toUInt32 = lo ∧ (w >>> 32).toUInt32 = hi := by
  intro w
  have hw := u64_pack_toBitVec lo hi
  refine ⟨?_, ?_⟩ <;> apply UInt32.toBitVec_inj.mp <;> apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi32
  · simp only [UInt64.toBitVec_toUInt32, BitVec.getLsbD_setWidth, show i < 32 from hi32,
      decide_true, Bool.true_and]
    change w.toBitVec.getLsbD i = lo.toBitVec.getLsbD i
    rw [hw, bv64_pack_getLsbD lo hi i (by omega)]
    simp [hi32]
  · simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight, BitVec.getLsbD_setWidth,
      show i < 32 from hi32, decide_true, Bool.true_and]
    rw [bv64_shiftRight_nat w.toBitVec 32 (by decide) 32 rfl, BitVec.getLsbD_ushiftRight,
      hw, bv64_pack_getLsbD lo hi (32 + i) (by omega)]
    simp [show ¬ (32 + i < 32) by omega, show 32 + i - 32 = i by omega]

theorem u64_of_u32_pack (w : UInt64) :
    w = w.toUInt32.toUInt64 ||| ((w >>> 32).toUInt32.toUInt64 <<< 32) := by
  apply UInt64.toBitVec_inj.mp
  rw [u64_pack_toBitVec]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bv64_pack_getLsbD _ _ i hi]
  simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight, BitVec.getLsbD_setWidth]
  rw [bv64_shiftRight_nat w.toBitVec 32 (by decide) 32 rfl, BitVec.getLsbD_ushiftRight]
  by_cases h32 : i < 32
  · simp [h32]
  · simp [h32, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]

/-! ## `BitVec` bounds, `ofNat`, `setWidth`, `truncate`, `signExtend` -/

theorem bv8_toNat_lt (x : BitVec 8) : x.toNat < 256 := x.isLt
theorem bv32_toNat_lt (x : BitVec 32) : x.toNat < 4294967296 := x.isLt
theorem bv64_toNat_lt (x : BitVec 64) : x.toNat < 18446744073709551616 := x.isLt
theorem bv32_toNat_le (x : BitVec 32) : x.toNat ≤ 4294967295 := Nat.lt_succ_iff.mp x.isLt

theorem bv8_ofNat_toNat (n : Nat) (h : n < 256) : (BitVec.ofNat 8 n).toNat = n := by
  rw [BitVec.toNat_ofNat, pow2_8_eq, Nat.mod_eq_of_lt h]

theorem bv32_ofNat_toNat (n : Nat) (h : n < 4294967296) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, pow2_32_eq, Nat.mod_eq_of_lt h]

theorem bv64_ofNat_toNat_lt (n : Nat) (h : n < 18446744073709551616) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, pow2_64_eq, Nat.mod_eq_of_lt h]

theorem bv_ofNat_toNat_eq {w : Nat} (n : Nat) (h : n < 2 ^ w) :
    (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv32_one_toNat : (1 : BitVec 32).toNat = 1 := rfl
theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl

theorem bv_toNat_setWidth_of_le {w v : Nat} (h : w ≤ v) (x : BitVec w) :
    (BitVec.setWidth v x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h))

theorem bv_toNat_setWidth_of_ble {w v : Nat} (x : BitVec w) (h : Nat.ble w v = true) :
    (BitVec.setWidth v x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (Nat.le_of_ble_eq_true h) x

theorem bv_toNat_truncate {w v : Nat} (x : BitVec w) :
    (BitVec.truncate v x).toNat = x.toNat % 2 ^ v :=
  BitVec.toNat_setWidth v x

theorem bv_zext_self {w : Nat} (x : BitVec w) : BitVec.setWidth w x = x :=
  BitVec.setWidth_eq x

theorem bv_zext1_32 (x : BitVec 1) : (BitVec.setWidth 32 x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (by omega) x

theorem bv_zext1_64 (x : BitVec 1) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (by omega) x

theorem bv_zext8_16 (x : BitVec 8) : (BitVec.setWidth 16 x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (by omega) x

theorem bv_zext8_32 (x : BitVec 8) : (BitVec.setWidth 32 x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (by omega) x

theorem bv_zext8_64 (x : BitVec 8) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (by omega) x

theorem bv_zext16_32 (x : BitVec 16) : (BitVec.setWidth 32 x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (by omega) x

theorem bv_zext16_64 (x : BitVec 16) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (by omega) x

theorem bv_zext32_64 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  bv_toNat_setWidth_of_le (by omega) x

theorem bv32_setWidth64_eq (x : BitVec 32) :
    BitVec.setWidth 64 x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_zext32_64, bv64_ofNat_toNat_lt _ (Nat.lt_trans x.isLt (by omega))]

theorem bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat :=
  bv_zext32_64 x

theorem bv32_setWidth64_setWidth32 (x : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv_zext32_64, pow2_32_eq, Nat.mod_eq_of_lt x.isLt]

theorem bv32_setWidth64_truncate32 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.setWidth 64 x) = x :=
  bv32_setWidth64_setWidth32 x

theorem bv32_setWidth64_add_of_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 4294967296) :
    BitVec.setWidth 64 (x + y) = BitVec.setWidth 64 x + BitVec.setWidth 64 y := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_zext32_64, BitVec.toNat_add, pow2_32_eq, Nat.mod_eq_of_lt h,
    BitVec.toNat_add, bv_zext32_64, bv_zext32_64, pow2_64_eq,
    Nat.mod_eq_of_lt (Nat.lt_trans h (by omega))]

theorem bv32_setWidth64_sub_of_le {x y : BitVec 32} (h : y.toNat ≤ x.toNat) :
    BitVec.setWidth 64 (x - y) = BitVec.setWidth 64 x - BitVec.setWidth 64 y := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_zext32_64, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h),
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [bv_zext32_64, bv_zext32_64]; exact h)),
    bv_zext32_64, bv_zext32_64]

theorem bv64_setWidth32_setWidth64_of_lt {x : BitVec 64} (h : x.toNat < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_zext32_64, BitVec.toNat_setWidth, pow2_32_eq, Nat.mod_eq_of_lt h]

theorem bv64_truncate32_setWidth64_of_lt {x : BitVec 64} (h : x.toNat < 4294967296) :
    BitVec.setWidth 64 (BitVec.truncate 32 x) = x :=
  bv64_setWidth32_setWidth64_of_lt h

theorem bv64_setWidth32_ofNat (n : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (n % 2 ^ 64) % 2 ^ 32 = n % 2 ^ 32
  exact Nat.mod_mod_of_dvd n ⟨2 ^ 32, by decide⟩

theorem bv64_trunc32_ofNat (n : Nat) :
    BitVec.truncate 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n :=
  bv64_setWidth32_ofNat n

theorem bv64_add_truncate32 (a b : BitVec 64) :
    BitVec.truncate 32 (a + b) = BitVec.truncate 32 a + BitVec.truncate 32 b := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_add]

theorem bv64_add_setWidth32 (a b : BitVec 64) :
    BitVec.setWidth 32 (a + b) = BitVec.setWidth 32 a + BitVec.setWidth 32 b :=
  bv64_add_truncate32 a b

theorem bv32_trunc_add (a b : BitVec 32) :
    BitVec.truncate 32 (BitVec.setWidth 64 a + BitVec.setWidth 64 b) = a + b := by
  rw [bv64_add_truncate32, bv32_setWidth64_truncate32, bv32_setWidth64_truncate32]

theorem bv_msb_false_of_toNat_lt {w : Nat} (x : BitVec w) (hlt : x.toNat < 2 ^ (w - 1)) :
    x.msb = false := by
  cases w with
  | zero => exact Subsingleton.elim x 0 ▸ rfl
  | succ w' =>
    rw [BitVec.msb_eq_toInt, decide_eq_false_iff_not]
    have h2 : 2 * x.toNat < 2 ^ (w' + 1) := by
      have hsub : w' + 1 - 1 = w' := by omega
      rw [hsub] at hlt
      rw [Nat.pow_succ]
      omega
    have htoInt : x.toInt = (x.toNat : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]
      simp [h2]
    omega

theorem bv_toNat_signExtend_of_lt {w v : Nat} (hw : w ≤ v) (x : BitVec w)
    (hlt : x.toNat < 2 ^ (w - 1)) : (BitVec.signExtend v x).toNat = x.toNat := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (bv_msb_false_of_toNat_lt x hlt)]
  exact bv_toNat_setWidth_of_le hw x

theorem bv_toNat_signExtend_of_lt_le {w v : Nat} (x : BitVec w)
    (hw : w ≤ v) (hlt : x.toNat < 2 ^ (w - 1)) : (BitVec.signExtend v x).toNat = x.toNat :=
  bv_toNat_signExtend_of_lt hw x hlt

theorem bv_toNat_signExtend_of_eq_lt {w v : Nat} (hv : w = v) (x : BitVec w) :
    (BitVec.signExtend v x).toNat = x.toNat := by
  subst hv
  rw [BitVec.signExtend_eq]

theorem bv_toNat_signExtend_of_eq_ble {w v : Nat} (x : BitVec w) (hw : Nat.ble w v = true)
    (hlt : x.toNat < 2 ^ (w - 1)) : (BitVec.signExtend v x).toNat = x.toNat :=
  bv_toNat_signExtend_of_lt (Nat.le_of_ble_eq_true hw) x hlt

/-! ## `BitVec` addition, subtraction, equality, and comparison -/

theorem bv_toNat_add_lt {w : Nat} (a b : BitVec w) (h : a.toNat + b.toNat < 2 ^ w) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv32_add_toNat {a b : BitVec 32} (h : a.toNat + b.toNat < 4294967296) :
    (a + b).toNat = a.toNat + b.toNat :=
  bv_toNat_add_lt a b h

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 18446744073709551616) :
    (a + b).toNat = a.toNat + b.toNat :=
  bv_toNat_add_lt a b h

theorem bv32_add_no_ovf {a b : BitVec 32} (ha : a.toNat < 2147483648)
    (hb : b.toNat < 2147483648) : (a + b).toNat = a.toNat + b.toNat :=
  bv32_add_toNat (by omega)

theorem bv64_add_no_ovf {a b : BitVec 64} (ha : a.toNat < 9223372036854775808)
    (hb : b.toNat < 9223372036854775808) : (a + b).toNat = a.toNat + b.toNat :=
  bv64_add_toNat (by omega)

theorem bv32_add_small_eq (x : BitVec 32) (n : Nat) (h : x.toNat + n < 4294967296) :
    x + BitVec.ofNat 32 n = BitVec.ofNat 32 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32_add_toNat (by rw [bv32_ofNat_toNat _ (by omega)]; exact h),
    bv32_ofNat_toNat _ (by omega), bv32_ofNat_toNat _ h]

theorem bv64_add_small_eq (x : BitVec 64) (n : Nat) (h : x.toNat + n < 18446744073709551616) :
    x + BitVec.ofNat 64 n = BitVec.ofNat 64 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_add_toNat (by rw [bv64_ofNat_toNat_lt _ (by omega)]; exact h),
    bv64_ofNat_toNat_lt _ (by omega), bv64_ofNat_toNat_lt _ h]

theorem bv32_add_small {x : BitVec 32} {n : Nat} (h : x.toNat + n < 4294967296) :
    (x + BitVec.ofNat 32 n).toNat = x.toNat + n := by
  rw [bv32_add_small_eq x n h, bv32_ofNat_toNat _ h]

theorem bv64_add_small {x : BitVec 64} {n : Nat} (h : x.toNat + n < 18446744073709551616) :
    (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [bv64_add_small_eq x n h, bv64_ofNat_toNat_lt _ h]

theorem bv32_add1_toNat {a : BitVec 32} (h : a.toNat + 1 < 4294967296) :
    (a + 1).toNat = a.toNat + 1 :=
  bv32_add_small h

theorem bv64_add1_toNat {a : BitVec 64} (h : a.toNat + 1 < 18446744073709551616) :
    (a + 1).toNat = a.toNat + 1 :=
  bv64_add_small h

theorem bv32_add1_lt {a : BitVec 32} (h : a.toNat + 1 < 4294967296) :
    (a + 1#32).toNat = a.toNat + 1 :=
  bv32_add1_toNat h

theorem bv64_add1_lt {a : BitVec 64} (h : a.toNat + 1 < 18446744073709551616) :
    (a + 1#64).toNat = a.toNat + 1 :=
  bv64_add1_toNat h

theorem bv32_add1_no_ovf {a : BitVec 32} (h : a.toNat < 4294967295) :
    (a + 1).toNat = a.toNat + 1 :=
  bv32_add1_toNat (by omega)

theorem bv64_add1_no_ovf {a : BitVec 64} (h : a.toNat < 18446744073709551615) :
    (a + 1).toNat = a.toNat + 1 :=
  bv64_add1_toNat (by omega)

theorem bv32_add1_ofNat_toNat (n : Nat) (h : n + 1 < 4294967296) :
    (BitVec.ofNat 32 n + 1).toNat = n + 1 := by
  rw [bv32_add1_toNat (by rw [bv32_ofNat_toNat _ (by omega)]; exact h),
    bv32_ofNat_toNat _ (by omega)]

theorem bv64_add1_ofNat_toNat (n : Nat) (h : n + 1 < 18446744073709551616) :
    (BitVec.ofNat 64 n + 1).toNat = n + 1 := by
  rw [bv64_add1_toNat (by rw [bv64_ofNat_toNat_lt _ (by omega)]; exact h),
    bv64_ofNat_toNat_lt _ (by omega)]

theorem bv_toNat_sub_le {w : Nat} {a b : BitVec w} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem bv_toNat_sub_of_eq {w : Nat} {a b : BitVec w} (h : a.toNat = b.toNat) :
    (a - b).toNat = 0 := by
  rw [bv_toNat_sub_le (Nat.le_of_eq h.symm), h, Nat.sub_self]

theorem bv32_sub_toNat {a b : BitVec 32} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  bv_toNat_sub_le h

theorem bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  bv_toNat_sub_le h

theorem bv32_sub_ofNat_toNat {a : BitVec 32} {n : Nat} (h : n ≤ a.toNat)
    (hn : n < 4294967296) : (a - BitVec.ofNat 32 n).toNat = a.toNat - n := by
  rw [bv32_sub_toNat (by rw [bv32_ofNat_toNat _ hn]; exact h), bv32_ofNat_toNat _ hn]

theorem bv64_sub_ofNat_toNat {a : BitVec 64} {n : Nat} (h : n ≤ a.toNat)
    (hn : n < 18446744073709551616) : (a - BitVec.ofNat 64 n).toNat = a.toNat - n := by
  rw [bv64_sub_toNat (by rw [bv64_ofNat_toNat_lt _ hn]; exact h), bv64_ofNat_toNat_lt _ hn]

theorem bv32_sub1_toNat {a : BitVec 32} (h : 0 < a.toNat) : (a - 1).toNat = a.toNat - 1 := by
  change (a - BitVec.ofNat 32 1).toNat = a.toNat - 1
  exact bv32_sub_ofNat_toNat (n := 1) (Nat.succ_le_of_lt h) (by omega)

theorem bv64_sub1_toNat {a : BitVec 64} (h : 0 < a.toNat) : (a - 1).toNat = a.toNat - 1 := by
  change (a - BitVec.ofNat 64 1).toNat = a.toNat - 1
  exact bv64_sub_ofNat_toNat (n := 1) (Nat.succ_le_of_lt h) (by omega)

theorem bv64_sub_small_eq (x : BitVec 64) (n : Nat) (h : n ≤ x.toNat) :
    x - BitVec.ofNat 64 n = BitVec.ofNat 64 (x.toNat - n) := by
  have hn : n < 18446744073709551616 := Nat.lt_of_le_of_lt h x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [bv64_sub_ofNat_toNat h hn, bv64_ofNat_toNat_lt _ (by have := x.isLt; omega)]

theorem bv64_sub_sub1_idx (x y : BitVec 64) (hy : 0 < y.toNat) (h : y.toNat ≤ x.toNat) :
    x - y = (x - 1) - (y - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_sub_toNat h,
    bv64_sub_toNat (by rw [bv64_sub1_toNat hy, bv64_sub1_toNat (by omega)]; omega),
    bv64_sub1_toNat hy, bv64_sub1_toNat (by omega)]
  omega

theorem bv32_eq_zero_of_not_pos {x : BitVec 32} (h : ¬ 0 < x.toNat) : x = 0 :=
  BitVec.eq_of_toNat_eq (by change x.toNat = 0; omega)

theorem bv64_eq_zero_of_not_pos {x : BitVec 64} (h : ¬ 0 < x.toNat) : x = 0 :=
  BitVec.eq_of_toNat_eq (by change x.toNat = 0; omega)

theorem bv32_eq_nat {x : BitVec 32} {n : Nat} (hn : n < 4294967296) :
    x = BitVec.ofNat 32 n ↔ x.toNat = n :=
  ⟨fun h => h ▸ bv32_ofNat_toNat n hn,
   fun h => BitVec.eq_of_toNat_eq (h.trans (bv32_ofNat_toNat n hn).symm)⟩

theorem bv64_eq_nat {x : BitVec 64} {n : Nat} (hn : n < 18446744073709551616) :
    x = BitVec.ofNat 64 n ↔ x.toNat = n :=
  ⟨fun h => h ▸ bv64_ofNat_toNat_lt n hn,
   fun h => BitVec.eq_of_toNat_eq (h.trans (bv64_ofNat_toNat_lt n hn).symm)⟩

theorem bv32_ne_nat {x : BitVec 32} {n : Nat} (hn : n < 4294967296) :
    x ≠ BitVec.ofNat 32 n ↔ x.toNat ≠ n :=
  not_congr (bv32_eq_nat hn)

theorem bv64_ne_nat {x : BitVec 64} {n : Nat} (hn : n < 18446744073709551616) :
    x ≠ BitVec.ofNat 64 n ↔ x.toNat ≠ n :=
  not_congr (bv64_eq_nat hn)

theorem bv32_beq_nat_eq (x : BitVec 32) (n : Nat) (hn : n < 4294967296) :
    (x == BitVec.ofNat 32 n) = decide (x.toNat = n) := by
  by_cases h : x.toNat = n
  · have hx : x = BitVec.ofNat 32 n := (bv32_eq_nat hn).mpr h
    rw [hx, beq_self_eq_true, bv32_ofNat_toNat n hn, decide_eq_true rfl]
  · have hx : x ≠ BitVec.ofNat 32 n := (bv32_ne_nat hn).mpr h
    have hb : (x == BitVec.ofNat 32 n) = false := beq_false_of_ne hx
    rw [hb, decide_eq_false h]

theorem bv32_ult_eq (a b : BitVec 32) : BitVec.ult a b = decide (a.toNat < b.toNat) := rfl
theorem bv64_ult_eq (a b : BitVec 64) : BitVec.ult a b = decide (a.toNat < b.toNat) := rfl
theorem bv32_ule_eq (a b : BitVec 32) : BitVec.ule a b = decide (a.toNat ≤ b.toNat) := rfl
theorem bv64_ule_eq (a b : BitVec 64) : BitVec.ule a b = decide (a.toNat ≤ b.toNat) := rfl

theorem bv64_fit_of_not_ugt {x : BitVec 64}
    (h : BitVec.ult (BitVec.ofNat 64 4294967295) x = false) :
    x.toNat < 4294967296 := by
  rw [bv64_ult_eq, decide_eq_false_iff_not, bv64_ofNat_toNat_lt _ (by omega)] at h
  omega

/-! ## `BitVec` shift and multiplication lemmas (`<<<`, `>>>`, `setWidth`) -/

theorem bv_toNat_shl_nat {w : Nat} (x : BitVec w) (k : Nat) :
    (x <<< k).toNat = (x.toNat * 2 ^ k) % 2 ^ w := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem bv_toNat_shl_bv {w : Nat} (x s : BitVec w) :
    (x <<< s).toNat = (x.toNat * 2 ^ s.toNat) % 2 ^ w := by
  change (x <<< s.toNat).toNat = _
  exact bv_toNat_shl_nat x s.toNat

theorem bv_toNat_ushiftRight_nat {w : Nat} (x : BitVec w) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv_toNat_ushiftRight_bv {w : Nat} (x s : BitVec w) :
    (x >>> s).toNat = x.toNat / 2 ^ s.toNat := by
  change (x >>> s.toNat).toNat = _
  exact bv_toNat_ushiftRight_nat x s.toNat

theorem bv32_lshr1_nat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  rw [bv_toNat_ushiftRight_nat]

theorem bv64_lshr1_nat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  rw [bv_toNat_ushiftRight_nat]

theorem bv32_lshr1_bv (x : BitVec 32) : (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := by
  rw [bv_toNat_ushiftRight_bv, bv32_one_toNat]

theorem bv64_lshr1_bv (x : BitVec 64) : (x >>> (1 : BitVec 64)).toNat = x.toNat / 2 := by
  rw [bv_toNat_ushiftRight_bv, bv64_one_toNat]

theorem bv64_zext32_ushr1 (x : BitVec 32) :
    (BitVec.setWidth 64 x >>> (1 : BitVec 64)).toNat = x.toNat / 2 := by
  rw [bv64_lshr1_bv, bv_zext32_64]

theorem bv32_shl1_nat (x : BitVec 32) (h : 2 * x.toNat < 4294967296) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [bv_toNat_shl_nat]
  change (x.toNat * 2) % 4294967296 = 2 * x.toNat
  omega

theorem bv64_shl1_nat (x : BitVec 64) (h : 2 * x.toNat < 18446744073709551616) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [bv_toNat_shl_nat]
  change (x.toNat * 2) % 18446744073709551616 = 2 * x.toNat
  omega

theorem bv32_shl1_bv (x : BitVec 32) (h : 2 * x.toNat < 4294967296) :
    (x <<< (1 : BitVec 32)).toNat = 2 * x.toNat := by
  change (x <<< (1 : BitVec 32).toNat).toNat = _
  rw [bv32_one_toNat]
  exact bv32_shl1_nat x h

theorem bv64_shl1_bv (x : BitVec 64) (h : 2 * x.toNat < 18446744073709551616) :
    (x <<< (1 : BitVec 64)).toNat = 2 * x.toNat := by
  change (x <<< (1 : BitVec 64).toNat).toNat = _
  rw [bv64_one_toNat]
  exact bv64_shl1_nat x h

theorem bv64_shl2_nat (x : BitVec 64) (h : 4 * x.toNat < 18446744073709551616) :
    (x <<< (2 : Nat)).toNat = 4 * x.toNat := by
  rw [bv_toNat_shl_nat]
  change (x.toNat * 4) % 18446744073709551616 = 4 * x.toNat
  omega

theorem bv64_shl2_bv (x : BitVec 64) (h : 4 * x.toNat < 18446744073709551616) :
    (x <<< (2 : BitVec 64)).toNat = 4 * x.toNat := by
  change (x <<< (2 : BitVec 64).toNat).toNat = _
  rw [bv64_two_toNat]
  exact bv64_shl2_nat x h

theorem bv64_shl3_nat (x : BitVec 64) (h : 8 * x.toNat < 18446744073709551616) :
    (x <<< (3 : Nat)).toNat = 8 * x.toNat := by
  rw [bv_toNat_shl_nat]
  change (x.toNat * 8) % 18446744073709551616 = 8 * x.toNat
  omega

theorem bv64_shl3_bv (x : BitVec 64) (h : 8 * x.toNat < 18446744073709551616) :
    (x <<< (3 : BitVec 64)).toNat = 8 * x.toNat := by
  change (x <<< (3 : BitVec 64).toNat).toNat = _
  rw [bv64_three_toNat]
  exact bv64_shl3_nat x h

theorem bv32_toNat_shl_of_lt (x : BitVec 32) (k : Nat) (h : x.toNat * 2 ^ k < 4294967296) :
    (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [bv_toNat_shl_nat, pow2_32_eq]
  exact Nat.mod_eq_of_lt h

theorem bv64_toNat_shl_of_lt (x : BitVec 64) (k : Nat)
    (h : x.toNat * 2 ^ k < 18446744073709551616) :
    (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [bv_toNat_shl_nat, pow2_64_eq]
  exact Nat.mod_eq_of_lt h

theorem bv64_shl3_eq_mul8 (x : BitVec 64) : x <<< (3 : BitVec 64) = x * 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_toNat_shl_bv, bv64_three_toNat, BitVec.toNat_mul]
  change (x.toNat * 8) % 2 ^ 64 = (x.toNat * (8 % 2 ^ 64)) % 2 ^ 64
  rfl

theorem bv64_mul8_eq_ofNat (x : BitVec 64) : x * 8 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (x.toNat * 8) % 2 ^ 64 = (8 * x.toNat) % 2 ^ 64
  rw [Nat.mul_comm]

theorem bv64_shl3_eq_ofNat (x : BitVec 64) :
    x <<< (3 : BitVec 64) = BitVec.ofNat 64 (8 * x.toNat) := by
  rw [bv64_shl3_eq_mul8, bv64_mul8_eq_ofNat]

theorem bv64_add_mul8_eq (base idx : BitVec 64) :
    base + idx * 8 = base + BitVec.ofNat 64 (8 * idx.toNat) := by
  rw [bv64_mul8_eq_ofNat]

theorem bv64_add_shl3_eq (base idx : BitVec 64) :
    base + (idx <<< (3 : BitVec 64)) = base + BitVec.ofNat 64 (8 * idx.toNat) := by
  rw [bv64_shl3_eq_ofNat]

theorem bv64_lit2 (x : BitVec 64) :
    x <<< (1 : BitVec 64) = BitVec.ofNat 64 (2 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_toNat_shl_bv, bv64_one_toNat, BitVec.toNat_ofNat]
  change (x.toNat * 2) % 2 ^ 64 = (2 * x.toNat) % 2 ^ 64
  rw [Nat.mul_comm]

theorem bv64_lit2p1 (x : BitVec 64) :
    (x <<< (1 : BitVec 64)) ||| (1 : BitVec 64) = BitVec.ofNat 64 (2 * x.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, bv_toNat_shl_bv, bv64_one_toNat, BitVec.toNat_ofNat]
  change ((x.toNat * 2) % 2 ^ 64 ||| 1) = (2 * x.toNat + 1) % 2 ^ 64
  have heven : ((x.toNat * 2) % 2 ^ 64) % 2 = 0 := by
    rw [pow2_64_eq]; omega
  rw [nat_even_or_one _ heven, pow2_64_eq]
  omega

theorem bv32_mul4_eq (x : BitVec 32) : x * 4 = BitVec.ofNat 32 (4 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (x.toNat * 4) % 2 ^ 32 = (4 * x.toNat) % 2 ^ 32
  rw [Nat.mul_comm]

theorem bv64_mul4_eq (x : BitVec 64) : x * 4 = BitVec.ofNat 64 (4 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (x.toNat * 4) % 2 ^ 64 = (4 * x.toNat) % 2 ^ 64
  rw [Nat.mul_comm]

theorem bv32_mul4_nat (x : BitVec 32) (h : 4 * x.toNat < 4294967296) :
    (x * 4).toNat = 4 * x.toNat := by
  rw [bv32_mul4_eq, bv32_ofNat_toNat _ h]

theorem bv64_mul4_nat (x : BitVec 64) (h : 4 * x.toNat < 18446744073709551616) :
    (x * 4).toNat = 4 * x.toNat := by
  rw [bv64_mul4_eq, bv64_ofNat_toNat_lt _ h]

theorem bv32_mul16_eq (x : BitVec 32) : x * 16 = BitVec.ofNat 32 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (x.toNat * 16) % 2 ^ 32 = (16 * x.toNat) % 2 ^ 32
  rw [Nat.mul_comm]

theorem bv64_mul16_eq (x : BitVec 64) : x * 16 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (x.toNat * 16) % 2 ^ 64 = (16 * x.toNat) % 2 ^ 64
  rw [Nat.mul_comm]

theorem bv32_mul16_nat (x : BitVec 32) (h : 16 * x.toNat < 4294967296) :
    (x * 16).toNat = 16 * x.toNat := by
  rw [bv32_mul16_eq, bv32_ofNat_toNat _ h]

theorem bv64_mul16_nat (x : BitVec 64) (h : 16 * x.toNat < 18446744073709551616) :
    (x * 16).toNat = 16 * x.toNat := by
  rw [bv64_mul16_eq, bv64_ofNat_toNat_lt _ h]

theorem bv_shl_sext1 (b : BitVec 8) (h : b.toNat < 64) :
    ((BitVec.signExtend 64 b <<< (1 : BitVec 64)).toNat) = 2 * b.toNat := by
  have hb : (BitVec.signExtend 64 b).toNat = b.toNat :=
    bv_toNat_signExtend_of_lt (by omega) b (by change b.toNat < 2 ^ 7; omega)
  rw [bv64_shl1_bv _ (by rw [hb]; omega), hb]

theorem bv_shr_sext2 (b : BitVec 8) (h : b.toNat < 128) :
    ((BitVec.signExtend 64 b >>> (2 : BitVec 64)).toNat) = b.toNat / 4 := by
  have hb : (BitVec.signExtend 64 b).toNat = b.toNat :=
    bv_toNat_signExtend_of_lt (by omega) b (by change b.toNat < 2 ^ 7; omega)
  rw [bv_toNat_ushiftRight_bv, bv64_two_toNat, hb]

theorem bv_shr_sext6 (b : BitVec 8) (h : b.toNat < 128) :
    ((BitVec.signExtend 64 b >>> (6 : BitVec 64)).toNat) = b.toNat / 64 := by
  have hb : (BitVec.signExtend 64 b).toNat = b.toNat :=
    bv_toNat_signExtend_of_lt (by omega) b (by change b.toNat < 2 ^ 7; omega)
  rw [bv_toNat_ushiftRight_bv]
  have h6 : (6 : BitVec 64).toNat = 6 := rfl
  rw [h6, hb]

theorem ptr_add_nat_bv64 (base : BitVec 64) (n : Nat) (k : BitVec 64)
    (hk : k.toNat = n) (hn : n < 18446744073709551616) :
    base + k = base + BitVec.ofNat 64 n := by
  congr 1
  exact (bv64_eq_nat hn).mpr hk

/-! ## Bitwise lemmas (`&&&`, `|||`, `^^^`) -/

theorem bv_toNat_and_one_of_le {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]
  have h1 : (1 : BitVec w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  rw [h1, Nat.and_one_is_mod]

theorem bv8_toNat_and_one (x : BitVec 8) : (x &&& 1).toNat = x.toNat % 2 :=
  bv_toNat_and_one_of_le (by omega) x

theorem bv16_toNat_and_one (x : BitVec 16) : (x &&& 1).toNat = x.toNat % 2 :=
  bv_toNat_and_one_of_le (by omega) x

theorem bv32_toNat_and_one (x : BitVec 32) : (x &&& 1).toNat = x.toNat % 2 :=
  bv_toNat_and_one_of_le (by omega) x

theorem bv64_toNat_and_one (x : BitVec 64) : (x &&& 1).toNat = x.toNat % 2 :=
  bv_toNat_and_one_of_le (by omega) x

theorem bv32_and1_ofNat (x : BitVec 32) :
    x &&& (1 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32_toNat_and_one, bv32_ofNat_toNat _ (by omega)]

theorem bv64_and1_ofNat (x : BitVec 64) :
    x &&& (1 : BitVec 64) = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_toNat_and_one, bv64_ofNat_toNat_lt _ (by omega)]

theorem bv32_and1_eq_zero_of_mod8 (x : BitVec 32) (h : x.toNat % 8 = 0) :
    x &&& (1 : BitVec 32) = 0 := by
  rw [bv32_and1_ofNat, show x.toNat % 2 = 0 by omega]; rfl

theorem bv64_and1_eq_zero_of_mod8 (x : BitVec 64) (h : x.toNat % 8 = 0) :
    x &&& (1 : BitVec 64) = 0 := by
  rw [bv64_and1_ofNat, show x.toNat % 2 = 0 by omega]; rfl

theorem bv64_and1_ne_zero_iff (x : BitVec 64) :
    x &&& (1 : BitVec 64) ≠ 0 ↔ x.toNat % 2 = 1 := by
  rw [bv64_and1_ofNat]
  change BitVec.ofNat 64 (x.toNat % 2) ≠ BitVec.ofNat 64 0 ↔ _
  rw [bv64_ne_nat (by omega), bv64_ofNat_toNat_lt _ (by omega)]
  omega

theorem bv_toNat_shl1_or_one_of_le {w : Nat} (hw : 1 ≤ w) (x : BitVec w)
    (h : 2 * x.toNat + 1 < 2 ^ w) :
    ((x <<< 1) ||| 1).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_or, bv_toNat_shl_nat]
  have h1 : (1 : BitVec w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  have hp2 : (2 : Nat) ^ 1 = 2 := rfl
  rw [h1, hp2, Nat.mod_eq_of_lt (by omega)]
  have heven : (x.toNat * 2) % 2 = 0 := by omega
  rw [nat_even_or_one _ heven]
  omega

theorem bv32_shl1_or_one_toNat (x : BitVec 32) (h : 2 * x.toNat + 1 < 4294967296) :
    ((x <<< 1) ||| 1).toNat = 2 * x.toNat + 1 :=
  bv_toNat_shl1_or_one_of_le (by omega) x h

theorem bv64_shl1_or_one_toNat (x : BitVec 64) (h : 2 * x.toNat + 1 < 18446744073709551616) :
    ((x <<< 1) ||| 1).toNat = 2 * x.toNat + 1 :=
  bv_toNat_shl1_or_one_of_le (by omega) x h

theorem bv32_shl1_or_one_eq (x : BitVec 32) :
    ((x <<< (1 : BitVec 32)) ||| 1) = BitVec.ofNat 32 (2 * x.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, bv_toNat_shl_bv, bv32_one_toNat, BitVec.toNat_ofNat]
  change ((x.toNat * 2) % 2 ^ 32 ||| 1) = (2 * x.toNat + 1) % 2 ^ 32
  have heven : ((x.toNat * 2) % 2 ^ 32) % 2 = 0 := by
    rw [pow2_32_eq]; omega
  rw [nat_even_or_one _ heven, pow2_32_eq]
  omega

theorem bv64_shl1_or_one_eq (x : BitVec 64) :
    ((x <<< (1 : BitVec 64)) ||| 1) = BitVec.ofNat 64 (2 * x.toNat + 1) :=
  bv64_lit2p1 x

theorem bv32_shl1_or_one_ushiftRight1 (x : BitVec 32) (h : 2 * x.toNat + 1 < 4294967296) :
    ((x <<< (1 : BitVec 32)) ||| 1) >>> (1 : BitVec 32) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32_lshr1_bv, bv32_shl1_or_one_eq, bv32_ofNat_toNat _ h]
  omega

theorem bv64_shl1_or_one_ushiftRight1 (x : BitVec 64)
    (h : 2 * x.toNat + 1 < 18446744073709551616) :
    ((x <<< (1 : BitVec 64)) ||| 1) >>> (1 : BitVec 64) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_lshr1_bv, bv64_shl1_or_one_eq, bv64_ofNat_toNat_lt _ h]
  omega

theorem bv32_zext64_shl1_or_one_toNat (x : BitVec 32) (h : 2 * x.toNat + 1 < 4294967296) :
    (BitVec.setWidth 64 ((x <<< (1 : BitVec 32)) ||| 1)).toNat = 2 * x.toNat + 1 := by
  rw [bv_zext32_64, bv32_shl1_or_one_eq, bv32_ofNat_toNat _ h]

theorem bv32_or1_of_even (x : BitVec 32) (h : x.toNat % 2 = 0) :
    (x ||| 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_or, bv32_one_toNat, nat_even_or_one _ h]

theorem bv64_or1_of_even (x : BitVec 64) (h : x.toNat % 2 = 0) :
    (x ||| 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_or, bv64_one_toNat, nat_even_or_one _ h]

theorem bv32_lit_even (x : BitVec 32) (h : x.toNat % 2 = 0) :
    (x &&& 1 : BitVec 32) = 0 := by
  rw [bv32_and1_ofNat, h]; rfl

theorem bv32_lit_odd (x : BitVec 32) (h : x.toNat % 2 = 1) :
    (x &&& 1 : BitVec 32) = 1 := by
  rw [bv32_and1_ofNat, h]; rfl

theorem bv32_and_pow2_sub_one (x : BitVec 32) (k : Nat) (hk : k ≤ 32) :
    (x &&& BitVec.ofNat 32 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  have hm : 2 ^ k - 1 < 2 ^ 32 := by
    have : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hk
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.and_two_pow_sub_one_eq_mod]

theorem bv64_and_pow2_sub_one (x : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  have hm : 2 ^ k - 1 < 2 ^ 64 := by
    have : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.and_two_pow_sub_one_eq_mod]

theorem bv32_and_mask31_eq (x : BitVec 32) :
    (x &&& 2147483647#32).toNat = x.toNat % 2147483648 := by
  have h := bv32_and_pow2_sub_one x 31 (by omega)
  simpa using h

theorem bv32_and_msb31_eq_zero_of_lt (x : BitVec 32) (h : x.toNat < 2147483648) :
    x &&& (2147483648#32 : BitVec 32) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have hz : (0 : BitVec 32).toNat = 0 := rfl
  rw [hz]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i < 31
  · have hmask : (2147483648#32 : BitVec 32).toNat.testBit i = false := by
      have hm : (2147483648#32 : BitVec 32).toNat = 2 ^ 31 := rfl
      rw [hm, Nat.testBit_two_pow, decide_eq_false (by omega)]
    rw [hmask, Bool.and_false]
  · have hpow : 2 ^ 31 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    have hx : x.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (by simpa using hpow))
    rw [hx, Bool.false_and]

theorem bv32_tag_bin_flag (x : BitVec 32) :
    (x ||| (2147483648#32 : BitVec 32)) &&& 2147483648#32 ≠ 0 := by
  intro heq
  have hbit := congrArg (fun v : BitVec 32 => v.toNat.testBit 31) heq
  simp only [BitVec.toNat_and, BitVec.toNat_or] at hbit
  have hmask : (2147483648#32 : BitVec 32).toNat.testBit 31 = true := by decide
  rw [Nat.testBit_and, Nat.testBit_or, hmask] at hbit
  simp at hbit

theorem bv32_tag_bin_mask (x : BitVec 32) (h : x.toNat < 2147483648) :
    (x ||| (2147483648#32 : BitVec 32)) &&& 2147483647#32 = x := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [BitVec.toNat_and, BitVec.toNat_or, Nat.testBit_and, Nat.testBit_or]
  by_cases hi : i < 31
  · have hm31 : (2147483648#32 : BitVec 32).toNat.testBit i = false := by
      have hm : (2147483648#32 : BitVec 32).toNat = 2 ^ 31 := rfl
      rw [hm, Nat.testBit_two_pow, decide_eq_false (by omega)]
    have hm30 : (2147483647#32 : BitVec 32).toNat.testBit i = true := by
      have hm : (2147483647#32 : BitVec 32).toNat = 2 ^ 31 - 1 := rfl
      rw [hm, Nat.testBit_two_pow_sub_one, decide_eq_true hi]
    rw [hm31, hm30, Bool.or_false, Bool.and_true]
  · have hpow : 2 ^ 31 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    have hx : x.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (by simpa using hpow))
    have hm30 : (2147483647#32 : BitVec 32).toNat.testBit i = false := by
      have hm : (2147483647#32 : BitVec 32).toNat = 2 ^ 31 - 1 := rfl
      rw [hm, Nat.testBit_two_pow_sub_one, decide_eq_false (by omega)]
    rw [hx, hm30, Bool.and_false]

theorem bv32_tag_bin_ne_sent (x : BitVec 32) (h : x.toNat < 2147483647) :
    (x ||| (2147483648#32 : BitVec 32)) ≠ 4294967295#32 := by
  intro heq
  have h1 := bv32_tag_bin_mask x (by omega)
  rw [heq] at h1
  have hval : (4294967295#32 &&& 2147483647#32 : BitVec 32).toNat = 2147483647 := rfl
  have hx := congrArg BitVec.toNat h1
  rw [hval] at hx
  omega

theorem bv32_mask_flag0 (x : BitVec 32) (h : x.toNat < 2147483648) :
    x &&& 2147483647#32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32_and_mask31_eq]
  exact Nat.mod_eq_of_lt h

theorem bv32_mask_ne_sent (x : BitVec 32) :
    x &&& 2147483647#32 ≠ 4294967295#32 := by
  intro heq
  have hlt : (x &&& 2147483647#32).toNat < 2147483648 := by
    rw [bv32_and_mask31_eq]
    exact Nat.mod_lt _ (by omega)
  rw [heq] at hlt
  have hv : (4294967295#32 : BitVec 32).toNat = 4294967295 := rfl
  omega

theorem bv32_lshr1_shl1_or_lt2 (x : BitVec 32) (b : Nat) (hb : b < 2)
    (hx : 2 * x.toNat + b < 4294967296) :
    ((x <<< (1 : BitVec 32)) ||| BitVec.ofNat 32 b) >>> (1 : BitVec 32) = x := by
  have hcases : b = 0 ∨ b = 1 := by omega
  rcases hcases with rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    rw [bv32_lshr1_bv, BitVec.toNat_or, BitVec.toNat_ofNat, Nat.zero_mod, Nat.or_zero,
      bv_toNat_shl_bv, bv32_one_toNat, pow2_32_eq]
    change (x.toNat * 2) % 4294967296 / 2 = x.toNat
    omega
  · simpa using bv32_shl1_or_one_ushiftRight1 x hx

theorem bv_toNat_xor_one_of_le {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    (x ^^^ 1).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 := by
  rw [BitVec.toNat_xor]
  have h1 : (1 : BitVec w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  rw [h1]
  by_cases hp : x.toNat % 2 = 0
  · simp only [hp, ite_true]
    exact nat_even_xor_one _ hp
  · have ho : x.toNat % 2 = 1 := by omega
    simp only [hp, ite_false]
    exact nat_odd_xor_one _ ho

theorem bv8_toNat_xor_one (x : BitVec 8) :
    (x ^^^ 1).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_toNat_xor_one_of_le (by omega) x

theorem bv32_toNat_xor_one (x : BitVec 32) :
    (x ^^^ 1).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_toNat_xor_one_of_le (by omega) x

theorem bv64_toNat_xor_one (x : BitVec 64) :
    (x ^^^ 1).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_toNat_xor_one_of_le (by omega) x

theorem bv_toNat_xor_one_ushiftRight {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    (x ^^^ 1).toNat / 2 = x.toNat / 2 := by
  rw [bv_toNat_xor_one_of_le hw x]
  split <;> omega

theorem bv32_xor1_div2 (x : BitVec 32) : (x ^^^ 1).toNat / 2 = x.toNat / 2 :=
  bv_toNat_xor_one_ushiftRight (by omega) x

theorem bv64_xor1_div2 (x : BitVec 64) : (x ^^^ 1).toNat / 2 = x.toNat / 2 :=
  bv_toNat_xor_one_ushiftRight (by omega) x

theorem bv32_xor1_lt (x : BitVec 32) (n : Nat) (hx : x.toNat < n) (hn : n % 2 = 0) :
    (x ^^^ 1).toNat < n := by
  rw [bv32_toNat_xor_one]
  split <;> omega

theorem bv32_xor1_self (x : BitVec 32) : (x ^^^ 1) ^^^ 1 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32_toNat_xor_one, bv32_toNat_xor_one]
  split <;> split <;> omega

theorem bv8_bit_zero_of_and_fe (x : BitVec 8) :
    ((x &&& (254#8 : BitVec 8)).toNat % 2 = 0) := by
  have hz : (x &&& 254#8) &&& (1#8 : BitVec 8) = 0 := by
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : BitVec 8).toNat = 0 := rfl
    rw [h0]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [BitVec.toNat_and, Nat.testBit_and, Nat.zero_testBit]
    cases i with
    | zero =>
      have hm : (254#8 : BitVec 8).toNat.testBit 0 = false := rfl
      rw [hm]
      simp
    | succ i' =>
      have h1 : (1#8 : BitVec 8).toNat.testBit (i' + 1) = false := by
        rw [show (1#8 : BitVec 8).toNat = 1 from rfl, nat_testBit_one_eq]
        simp
      rw [h1]
      simp
  have hmod := congrArg BitVec.toNat hz
  change ((x &&& 254#8) &&& (1 : BitVec 8)).toNat = (0 : BitVec 8).toNat at hmod
  rw [bv8_toNat_and_one] at hmod
  exact hmod

theorem bv8_clear_bit1_of_zero (x : BitVec 8) : (x &&& (254#8 : BitVec 8)) &&& 1#8 = 0 := by
  apply BitVec.eq_of_toNat_eq
  change ((x &&& 254#8) &&& (1 : BitVec 8)).toNat = 0
  rw [bv8_toNat_and_one]
  exact bv8_bit_zero_of_and_fe x

theorem bv8_clear_bit2_of_zero (x : BitVec 8) : (x &&& (253#8 : BitVec 8)) &&& 2#8 = 0 := by
  apply BitVec.eq_of_toNat_eq
  have h0 : (0 : BitVec 8).toNat = 0 := rfl
  rw [h0]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [BitVec.toNat_and, Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i = 1
  · subst hi
    have hm : (253#8 : BitVec 8).toNat.testBit 1 = false := rfl
    rw [hm]
    simp
  · have h2 : (2#8 : BitVec 8).toNat.testBit i = false := by
      have hm : (2#8 : BitVec 8).toNat = 2 ^ 1 := rfl
      rw [hm, Nat.testBit_two_pow, decide_eq_false (Ne.symm hi)]
    rw [h2]
    simp

/-! ## `u32_omega` automation (and scoped `U32.c0_bv32_omega`) -/

section Simprocs
open Lean Meta Elab Tactic Simp

/-- Normalize concrete powers `2 ^ k` (`k ≤ 64`) in `u32_omega`. -/
dsimproc u32PowSimproc ((2 : Nat) ^ _) := fun e => do
  let_expr HPow.hPow _ _ _ _ a b := e | return .continue
  let some 2 := a.nat? | return .continue
  let some k := b.nat? | return .continue
  if k > 64 then return .continue
  return .done (mkNatLit (2 ^ k))

/-- Simplify `(BitVec.ofNat w n).toNat` for concrete `w, n` when `n < 2^w`. -/
simproc u32BvOfNatSimproc (BitVec.toNat (BitVec.ofNat _ _)) := fun e => do
  let_expr BitVec.toNat wExpr inner := e | return .continue
  let_expr BitVec.ofNat _ nExpr := inner | return .continue
  let some w := wExpr.nat? | return .continue
  let some n := nExpr.nat? | return .continue
  if w ≤ 64 && n < 2 ^ w then
    let powExpr ← mkAppM ``Nat.pow #[mkNatLit 2, wExpr]
    let ltPrf ← mkDecideProof (← mkAppM ``LT.lt #[nExpr, powExpr])
    let prf ← mkAppM ``bv_ofNat_toNat_eq #[nExpr, ltPrf]
    return .done { expr := nExpr, proof? := some prf }
  return .continue

private meta def addIntBounds : TacticM Unit := do
  withMainContext do
    let lctx ← getLCtx
    let target ← getMainTarget
    let seen : Std.HashSet Expr := {}
    let acc : Array Expr := #[]
    let rec collect (e : Expr) (s : Std.HashSet Expr × Array Expr) :
        Std.HashSet Expr × Array Expr :=
      if s.1.contains e then s else
      let s := (s.1.insert e, s.2.push e)
      match e with
      | .app f a => collect a (collect f s)
      | .lam _ d b _ => collect b (collect d s)
      | .forallE _ d b _ => collect b (collect d s)
      | .letE _ t v b _ => collect b (collect v (collect t s))
      | .mdata _ b => collect b s
      | .proj _ _ b => collect b s
      | _ => s
    let mut state := collect target (seen, acc)
    for decl in lctx do
      if !decl.isImplementationDetail then
        state := collect decl.type state
    let mut idx : Nat := 0
    for e in state.2 do
      let ty ← inferType e
      let tyWhnf ← whnf ty
      let bound? : Option (Name × Expr) :=
        if tyWhnf.isConstOf ``UInt8 then
          some (``u8_toNat_lt, e)
        else if tyWhnf.isConstOf ``UInt32 then
          some (``u32_toNat_lt, e)
        else if tyWhnf.isConstOf ``UInt64 then
          some (``u64_toNat_lt, e)
        else if tyWhnf.isAppOfArity ``BitVec 1 then
          match tyWhnf.appArg!.nat? with
          | some 8 => some (``bv8_toNat_lt, e)
          | some 32 => some (``bv32_toNat_lt, e)
          | some 64 => some (``bv64_toNat_lt, e)
          | _ => none
        else
          none
      if let some (lemName, arg) := bound? then
        let prf ← mkAppM lemName #[arg]
        let prop ← inferType prf
        let n := Name.mkSimple s!"_u32_bound_{idx}"
        idx := idx + 1
        let mvarId ← getMainGoal
        let (_, mvarId') ← mvarId.note n prop prf
        replaceMainGoal [mvarId']

end Simprocs

syntax "u32_omega" : tactic
syntax "u32_omega" " [" "*" "]" : tactic
syntax "u32_omega" " [" term,+ "]" : tactic

private meta def runU32OmegaCore : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    try simp only [
      u32PowSimproc, u32BvOfNatSimproc,
      u32_size_eq, u8_size_eq, u64_size_eq,
      u8_eq_iff, u32_eq_iff, u64_eq_iff,
      u8_ne_iff, u32_ne_iff, u64_ne_iff,
      UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le,
      UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
      UInt8.toNat_ofNat, UInt32.toNat_ofNat, UInt64.toNat_ofNat,
      UInt8.toNat_toUInt32, UInt32.toNat_toUInt64,
      UInt32.toNat_toUInt8, UInt64.toNat_toUInt32,
      BitVec.lt_def, BitVec.le_def,
      BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      bv32_one_toNat, bv64_one_toNat, bv64_two_toNat, bv64_three_toNat] at *))
  addIntBounds
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals (try omega)))

elab "u32_omega" : tactic => runU32OmegaCore
elab "u32_omega" " [" "*" "]" : tactic => runU32OmegaCore
elab "u32_omega" " [" ts:term,+ "]" : tactic => do
  for t in ts.getElems do
    let hId := Lean.mkIdent (Lean.Name.mkSimple "_u32_extra")
    Lean.Elab.Tactic.evalTactic (← `(tactic| have $hId := $t))
  runU32OmegaCore

namespace U32

scoped syntax "c0_bv32_omega" : tactic
scoped syntax "c0_bv32_omega" " [" "*" "]" : tactic
scoped syntax "c0_bv32_omega" " [" term,+ "]" : tactic

macro_rules
  | `(tactic| c0_bv32_omega) => `(tactic| u32_omega)
  | `(tactic| c0_bv32_omega [*]) => `(tactic| u32_omega [*])
  | `(tactic| c0_bv32_omega [$ts,*]) => `(tactic| u32_omega [$ts,*])

end U32

end LeanQbe.T
