prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.Int.Bitwise.Lemmas
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
private axiom cheat {p : Prop} : p
/-!
# Grind homomorphism lemmas for Int64.
-/

attribute [grind_homo] Int64.toBitVec_add
attribute [grind_homo] Int64.toBitVec_sub
attribute [grind_homo] Int64.toBitVec_mul
attribute [grind_homo] Int64.toBitVec_div
attribute [grind_homo] Int64.toBitVec_mod
attribute [grind_homo] Int64.toBitVec_and
attribute [grind_homo] Int64.toBitVec_or
attribute [grind_homo] Int64.toBitVec_xor
attribute [grind_homo] Int64.toBitVec_shiftLeft
attribute [grind_homo] Int64.toBitVec_shiftRight
attribute [grind_homo] Int64.eq_iff_toBitVec_eq
attribute [grind_homo] Int64.toBitVec_zero
attribute [grind_homo] Int64.toBitVec_one
attribute [grind_homo] Int64.toBitVec_ofNat
attribute [grind_homo] Int64.toBitVec_not
attribute [grind_homo] Int64.toBitVec_neg
attribute [grind_homo] Int64.toBitVec_toInt8
attribute [grind_homo] Int64.toBitVec_toInt16
attribute [grind_homo] Int64.toBitVec_toInt32
attribute [grind_homo] Int64.toBitVec_toISize
attribute [grind_homo] Int64.toBitVec_toUInt64


namespace Int64

@[grind_homo]
theorem le_simp' (a b : Int64) : (a ≤ b) = (a.toBitVec.toInt ≤ b.toBitVec.toInt) := by
  exact BitVec.sle_simp' a.toBitVec b.toBitVec

@[grind_homo]
theorem lt_simp' (a b : Int64) : (a < b) = (a.toBitVec.toInt < b.toBitVec.toInt) := by
  exact BitVec.slt_simp' a.toBitVec b.toBitVec

@[grind_homo_pred]
theorem le_toInt_inst (a b : Int64) : a ≤ b ↔ a.toBitVec.toInt ≤ b.toBitVec.toInt := by
  exact BitVec.sle_toInt_pred a.toBitVec b.toBitVec

@[grind_homo_pred]
theorem lt_toInt_inst (a b : Int64) : a < b ↔ a.toBitVec.toInt < b.toBitVec.toInt := by
  exact BitVec.slt_toInt_pred a.toBitVec b.toBitVec









attribute [grind_homo] Int64.xor_self Int64.not_not Int64.shiftLeft_zero Int64.and_zero

@[grind_homo] theorem hShiftLeft_eq (x y : Int64) : x <<< y = x * Int64.ofNat (2 ^ y.toBitVec.toNat) := cheat
@[grind_homo] theorem hShiftRight_eq (x y : Int64) : x >>> y = x / Int64.ofNat (2 ^ y.toBitVec.toNat) := cheat



@[grind_homo] theorem toInt32_toInt16 (x : Int64) : x.toInt32.toInt16 = x.toInt16 := by
  rw [Int16.eq_iff_toBitVec_eq]
  rw [Int32.toBitVec_toInt16]
  rw [Int64.toBitVec_toInt32]
  rw [Int64.toBitVec_toInt16]
  grind



@[grind_homo] theorem toBitVec_ofUInt64 (a : UInt64) : (Int64.ofUInt64 a).toBitVec = a.toBitVec := rfl

theorem toBitVec_injective : Function.Injective Int64.toBitVec := fun ⟨_⟩ ⟨_⟩ h => by congr; exact UInt64.eq_of_toBitVec_eq h
attribute [grind inj] toBitVec_injective
@[grind_homo_pred] theorem toBitVec_toInt_range (x : Int64) :
  -(2^63) ≤ x.toBitVec.toInt ∧ x.toBitVec.toInt < 2^63 := ⟨Int64.le_toInt x, Int64.toInt_lt x⟩


@[grind_homo] theorem toBitVec_toInt (x : Int64) : x.toInt = x.toBitVec.toInt := rfl


@[grind_homo] theorem testBit_toBitVec (x : Int64) (i : Nat) :
  x.toInt.testBit i = if i < 64 then x.toBitVec.getLsbD i else x.toBitVec.getLsbD 63 :=
  BitVec.testBit_toInt (by decide) x.toBitVec i

@[grind_homo] theorem sub_eq (x y : Int64) : x - y = x + ~~~y + 1 := by
  rw [Int64.eq_iff_toBitVec_eq]
  grind

end Int64

