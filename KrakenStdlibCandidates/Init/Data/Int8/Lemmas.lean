prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.Int.Bitwise.Lemmas
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
import KrakenStdlibCandidates.Init.Data.UInt8.Lemmas

/-!
# Grind homomorphism lemmas for Int8.
-/

attribute [grind_homo] Int8.toBitVec_add
attribute [grind_homo] Int8.toBitVec_sub
attribute [grind_homo] Int8.toBitVec_mul
attribute [grind_homo] Int8.toBitVec_div
attribute [grind_homo] Int8.toBitVec_mod
attribute [grind_homo] Int8.toBitVec_and
attribute [grind_homo] Int8.toBitVec_or
attribute [grind_homo] Int8.toBitVec_xor
attribute [grind_homo] Int8.toBitVec_shiftLeft
attribute [grind_homo] Int8.toBitVec_shiftRight
attribute [grind_homo] Int8.toBitVec_toInt16
attribute [grind_homo] Int8.toBitVec_toInt32
attribute [grind_homo] Int8.toBitVec_toInt64
attribute [grind_homo] Int8.toBitVec_toISize
attribute [grind_homo] Int8.toBitVec_toUInt8
attribute [grind_homo] Int8.eq_iff_toBitVec_eq
attribute [grind_homo] Int8.toBitVec_zero
attribute [grind_homo] Int8.toBitVec_one
attribute [grind_homo] Int8.toBitVec_not
attribute [grind_homo] Int8.toBitVec_neg
attribute [grind_homo] Int8.toBitVec_ofNat

namespace Int8

@[grind_homo] theorem toInt_eq_toBitVec_signed (x : Int8) : x.toInt = x.toBitVec.signed := rfl


@[grind_homo_pred]
theorem toBitVec_le (a b : Int8) : a ≤ b ↔ (a.toBitVec.sle b.toBitVec = true) := Iff.rfl

@[grind_homo_pred]
theorem toBitVec_lt (a b : Int8) : a < b ↔ (a.toBitVec.slt b.toBitVec = true) := Iff.rfl

theorem toBitVec_injective : Function.Injective Int8.toBitVec := fun ⟨_⟩ ⟨_⟩ h => by congr; exact UInt8.toBitVec_injective h
attribute [grind inj] toBitVec_injective

@[grind_homo] theorem toBitVec_ofUInt8 (a : UInt8) : (Int8.ofUInt8 a).toBitVec = a.toBitVec := rfl

@[grind_homo] theorem toInt32_toInt8 (x : Int8) : x.toInt32.toInt8 = x := by
  rw [Int8.eq_iff_toBitVec_eq]
  rw [Int32.toBitVec_toInt8]
  rw [Int8.toBitVec_toInt32]
  grind

@[grind_homo_pred] theorem toInt_range (x : Int8) :
  -(2^7) ≤ x.toInt ∧ x.toInt < 2^7 := ⟨Int8.le_toInt x, Int8.toInt_lt x⟩

@[grind_homo] theorem testBit_toBitVec (x : Int8) (i : Nat) :
  x.toInt.testBit i = if i < 8 then x.toBitVec.getLsbD i else x.toBitVec.getLsbD 7 :=
  BitVec.testBit_toInt (by decide) x.toBitVec i

theorem toInt_toInt16_mul (x y : Int8) : (x.toInt16 * y.toInt16).toInt = x.toInt * y.toInt := by
  have hx := Int8.le_toInt x
  have hx2 := Int8.toInt_lt x
  have hy := Int8.le_toInt y
  have hy2 := Int8.toInt_lt y
  have hx_abs : x.toInt.natAbs ≤ 2^7 := by omega
  have hy_abs : y.toInt.natAbs ≤ 2^7 := by omega
  have h_upper : x.toInt * y.toInt ≤ 2^7 * 2^7 := Int.mul_le_mul_of_natAbs_le hx_abs hy_abs
  have h_neg : (-x.toInt).natAbs ≤ 2^7 := by
    rwa [← Int.natAbs_neg] at hx_abs
  have h_lower : -(x.toInt * y.toInt) ≤ 2^7 * 2^7 := by
    have h := Int.mul_le_mul_of_natAbs_le h_neg hy_abs
    rwa [Int.neg_mul] at h
  rw [Int16.toInt_mul, Int8.toInt_toInt16, Int8.toInt_toInt16]
  have h_range1 : -(2^15) ≤ x.toInt * y.toInt := by omega
  have h_range2 : x.toInt * y.toInt < 2^15 := by omega
  exact Int.bmod_eq_of_le h_range1 h_range2

theorem mul_range (x y : Int8) :
    -(2^14) + 2^7 ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ 2^14 := by
  have hx_abs : x.toInt.natAbs ≤ 2^7 := by
    have h1 := Int8.le_toInt x
    have h2 := Int8.toInt_lt x
    omega
  have hy_abs : y.toInt.natAbs ≤ 2^7 := by
    have h1 := Int8.le_toInt y
    have h2 := Int8.toInt_lt y
    omega
  have h_upper : x.toInt * y.toInt ≤ 2^7 * 2^7 := Int.mul_le_mul_of_natAbs_le hx_abs hy_abs
  constructor
  · by_cases h1 : 0 ≤ x.toInt
    · have hx1 : (-x.toInt).natAbs ≤ 127 := by
        have h := Int8.toInt_lt x
        omega
      have hy1 : y.toInt.natAbs ≤ 128 := by
        have h := Int8.le_toInt y
        have h2 := Int8.toInt_lt y
        omega
      have h_neg := Int.mul_le_mul_of_natAbs_le hx1 hy1
      rw [Int.neg_mul] at h_neg
      omega
    · by_cases h2 : 0 ≤ y.toInt
      · have hx2 : x.toInt.natAbs ≤ 128 := by
          have h := Int8.le_toInt x
          omega
        have hy2 : (-y.toInt).natAbs ≤ 127 := by
          have h := Int8.toInt_lt y
          omega
        have h_neg := Int.mul_le_mul_of_natAbs_le hx2 hy2
        rw [Int.mul_neg] at h_neg
        omega
      · have : 0 ≤ x.toInt * y.toInt := by
          have hx_neg : x.toInt ≤ 0 := by omega
          have hy_neg : y.toInt ≤ 0 := by omega
          exact Int.mul_nonneg_of_nonpos_of_nonpos hx_neg hy_neg
        omega
  · omega

end Int8

