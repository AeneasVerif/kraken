prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.Int.Bitwise.Lemmas
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
import KrakenStdlibCandidates.Init.Data.UInt32.Lemmas


/-!
# Grind homomorphism lemmas for Int32.
-/

attribute [grind_homo] Int32.toBitVec_add
attribute [grind_homo] Int32.toBitVec_sub
attribute [grind_homo] Int32.toBitVec_mul
attribute [grind_homo] Int32.toBitVec_div
attribute [grind_homo] Int32.toBitVec_mod
attribute [grind_homo] Int32.toBitVec_and
attribute [grind_homo] Int32.toBitVec_or
attribute [grind_homo] Int32.toBitVec_xor
attribute [grind_homo] Int32.toBitVec_shiftLeft
attribute [grind_homo] Int32.toBitVec_shiftRight
attribute [grind_homo] Int32.toBitVec_toInt8
attribute [grind_homo] Int32.toBitVec_toInt16
attribute [grind_homo] Int32.toBitVec_toInt64
attribute [grind_homo] Int32.toBitVec_toISize
attribute [grind_homo] Int32.toBitVec_toUInt32
attribute [grind_homo] Int32.eq_iff_toBitVec_eq
attribute [grind_homo] Int32.toBitVec_zero
attribute [grind_homo] Int32.toBitVec_one
attribute [grind_homo] Int32.toBitVec_not
attribute [grind_homo] Int32.toBitVec_neg
attribute [grind_homo] Int32.toBitVec_ofNat


namespace Int32

@[grind_homo_pred]
theorem toBitVec_le (a b : Int32) : Int32.le a b ↔ (a.toBitVec.sle b.toBitVec = true) := Iff.rfl

@[grind_homo_pred]
theorem toBitVec_lt (a b : Int32) : Int32.lt a b ↔ (a.toBitVec.slt b.toBitVec = true) := Iff.rfl

theorem toBitVec_injective : Function.Injective Int32.toBitVec := fun ⟨_⟩ ⟨_⟩ h => by congr; exact UInt32.toBitVec_injective h
attribute [grind inj] toBitVec_injective

@[grind_homo] theorem toBitVec_ofUInt32 (a : UInt32) : (Int32.ofUInt32 a).toBitVec = a.toBitVec := rfl

@[grind_homo_pred] theorem toInt_range (x : Int32) :
  -(2^31) ≤ x.toInt ∧ x.toInt < 2^31 := ⟨Int32.le_toInt x, Int32.toInt_lt x⟩

@[grind_homo] theorem testBit_toBitVec (x : Int32) (i : Nat) :
  x.toInt.testBit i = if i < 32 then x.toBitVec.getLsbD i else x.toBitVec.getLsbD 31 :=
  BitVec.testBit_toInt (by decide) x.toBitVec i

theorem toInt_toInt64_mul (x y : Int32) : (x.toInt64 * y.toInt64).toInt = x.toInt * y.toInt := by
  have hx := Int32.le_toInt x
  have hx2 := Int32.toInt_lt x
  have hy := Int32.le_toInt y
  have hy2 := Int32.toInt_lt y
  have hx_abs : x.toInt.natAbs ≤ 2^31 := by omega
  have hy_abs : y.toInt.natAbs ≤ 2^31 := by omega
  have h_upper : x.toInt * y.toInt ≤ 2^31 * 2^31 := Int.mul_le_mul_of_natAbs_le hx_abs hy_abs
  have h_neg : (-x.toInt).natAbs ≤ 2^31 := by
    rwa [← Int.natAbs_neg] at hx_abs
  have h_lower : -(x.toInt * y.toInt) ≤ 2^31 * 2^31 := by
    have h := Int.mul_le_mul_of_natAbs_le h_neg hy_abs
    rwa [Int.neg_mul] at h
  rw [Int64.toInt_mul, Int32.toInt_toInt64, Int32.toInt_toInt64]
  have h_range1 : -(2^63) ≤ x.toInt * y.toInt := by omega
  have h_range2 : x.toInt * y.toInt < 2^63 := by omega
  exact Int.bmod_eq_of_le h_range1 h_range2

theorem mul_range (x y : Int32) : -(2^62) + 2^31 ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ 2^62 := by
  have hx := Int32.le_toInt x
  have hx2 := Int32.toInt_lt x
  have hy := Int32.le_toInt y
  have hy2 := Int32.toInt_lt y
  have hx_abs : x.toInt.natAbs ≤ 2^31 := by omega
  have hy_abs : y.toInt.natAbs ≤ 2^31 := by omega
  have h_upper : x.toInt * y.toInt ≤ 2^31 * 2^31 := Int.mul_le_mul_of_natAbs_le hx_abs hy_abs
  constructor
  · have hx_cases : 0 ≤ x.toInt ∨ x.toInt < 0 := by omega
    have hy_cases : 0 ≤ y.toInt ∨ y.toInt < 0 := by omega
    rcases hx_cases with hx_pos | hx_neg
    · rcases hy_cases with hy_pos | hy_neg
      · have h := Int.mul_nonneg hx_pos hy_pos
        omega
      · have h1 : x.toInt ≤ 2^31 - 1 := by omega
        have h2 : -y.toInt ≤ 2^31 := by omega
        have h3 : 0 ≤ -y.toInt := by omega
        have h4 : 0 ≤ (2^31 - 1 : Int) := by decide
        have h_mul := Int.mul_le_mul h1 h2 h3 h4
        rw [Int.mul_neg] at h_mul
        omega
    · rcases hy_cases with hy_pos | hy_neg
      · have h1 : -x.toInt ≤ 2^31 := by omega
        have h2 : y.toInt ≤ 2^31 - 1 := by omega
        have h3 : 0 ≤ y.toInt := by omega
        have h4 : 0 ≤ (2^31 : Int) := by decide
        have h_mul := Int.mul_le_mul h1 h2 h3 h4
        rw [Int.neg_mul] at h_mul
        omega
      · have h_mul := Int.mul_nonneg (by omega : 0 ≤ -x.toInt) (by omega : 0 ≤ -y.toInt)
        rw [Int.neg_mul_neg] at h_mul
        omega
  · omega

end Int32

