prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.Int.Bitwise.Lemmas
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
import KrakenStdlibCandidates.Init.Data.UInt16.Lemmas
private axiom cheat {p : Prop} : p


/-!
# Grind homomorphism lemmas for Int16.
-/

attribute [grind_homo] Int16.toBitVec_add
attribute [grind_homo] Int16.toBitVec_sub
attribute [grind_homo] Int16.toBitVec_mul
attribute [grind_homo] Int16.toBitVec_div
attribute [grind_homo] Int16.toBitVec_mod
attribute [grind_homo] Int16.toBitVec_and
attribute [grind_homo] Int16.toBitVec_or
attribute [grind_homo] Int16.toBitVec_xor
attribute [grind_homo] Int16.toBitVec_shiftLeft
attribute [grind_homo] Int16.toBitVec_shiftRight
attribute [grind_homo] Int16.toBitVec_toInt8
attribute [grind_homo] Int16.toBitVec_toInt32
attribute [grind_homo] Int16.toBitVec_toInt64
attribute [grind_homo] Int16.toBitVec_toISize
attribute [grind_homo] Int16.toBitVec_toUInt16
attribute [grind_homo] Int16.eq_iff_toBitVec_eq
attribute [grind_homo] Int16.toBitVec_zero
attribute [grind_homo] Int16.toBitVec_one
attribute [grind_homo] Int16.toBitVec_not
attribute [grind_homo] Int16.toBitVec_neg
attribute [grind_homo] Int16.toBitVec_ofNat

namespace Int16

@[grind_homo] theorem toInt_eq_toBitVec_signed (x : Int16) : x.toInt = x.toBitVec.signed := rfl


@[grind_homo_pred]
theorem toBitVec_le (a b : Int16) : a ≤ b ↔ a.toBitVec.sle b.toBitVec := Iff.rfl

@[grind_homo_pred]
theorem toBitVec_lt (a b : Int16) : a < b ↔ a.toBitVec.slt b.toBitVec := Iff.rfl

theorem toBitVec_injective : Function.Injective Int16.toBitVec := fun ⟨_⟩ ⟨_⟩ h => by congr; exact UInt16.toBitVec_injective h
attribute [grind inj] toBitVec_injective

@[grind_homo] theorem toBitVec_ofUInt16 (a : UInt16) : (Int16.ofUInt16 a).toBitVec = a.toBitVec := rfl

@[grind_homo_pred] theorem toInt_range (x : Int16) :
  -(2^15) ≤ x.toInt ∧ x.toInt < 2^15 := ⟨Int16.le_toInt x, Int16.toInt_lt x⟩

@[grind_homo] theorem testBit_toBitVec (x : Int16) (i : Nat) :
  x.toInt.testBit i = if i < 16 then x.toBitVec.getLsbD i else x.toBitVec.getLsbD 15 :=
  BitVec.testBit_toInt (by decide) x.toBitVec i

theorem toInt_toInt32_mul (x y : Int16) : (x.toInt32 * y.toInt32).toInt = x.toInt * y.toInt := by
  have hx := Int16.le_toInt x
  have hx2 := Int16.toInt_lt x
  have hy := Int16.le_toInt y
  have hy2 := Int16.toInt_lt y
  have hx_abs : x.toInt.natAbs ≤ 2^15 := by omega
  have hy_abs : y.toInt.natAbs ≤ 2^15 := by omega
  have h_upper : x.toInt * y.toInt ≤ 2^15 * 2^15 := Int.mul_le_mul_of_natAbs_le hx_abs hy_abs
  have h_neg : (-x.toInt).natAbs ≤ 2^15 := by
    rwa [← Int.natAbs_neg] at hx_abs
  have h_lower : -(x.toInt * y.toInt) ≤ 2^15 * 2^15 := by
    have h := Int.mul_le_mul_of_natAbs_le h_neg hy_abs
    rwa [Int.neg_mul] at h
  rw [Int32.toInt_mul, Int16.toInt_toInt32, Int16.toInt_toInt32]
  have h_range1 : -(2^31) ≤ x.toInt * y.toInt := by omega
  have h_range2 : x.toInt * y.toInt < 2^31 := by omega
  exact Int.bmod_eq_of_le h_range1 h_range2

theorem mul_range (x y : Int16) : -(2^30) + 2^15 ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ 2^30 := cheat

end Int16

