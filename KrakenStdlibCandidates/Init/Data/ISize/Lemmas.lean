prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.Int.Bitwise.Lemmas
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
import KrakenStdlibCandidates.Init.Data.USize.Lemmas


/-!
# Grind homomorphism lemmas for ISize.
-/

attribute [grind_homo] ISize.toBitVec_add
attribute [grind_homo] ISize.toBitVec_sub
attribute [grind_homo] ISize.toBitVec_mul
attribute [grind_homo] ISize.toBitVec_div
attribute [grind_homo] ISize.toBitVec_mod
attribute [grind_homo] ISize.toBitVec_and
attribute [grind_homo] ISize.toBitVec_or
attribute [grind_homo] ISize.toBitVec_xor
attribute [grind_homo] ISize.toBitVec_shiftLeft
attribute [grind_homo] ISize.toBitVec_shiftRight
attribute [grind_homo] ISize.toBitVec_toInt8
attribute [grind_homo] ISize.toBitVec_toInt16
attribute [grind_homo] ISize.toBitVec_toInt32
attribute [grind_homo] ISize.toBitVec_toInt64
attribute [grind_homo] ISize.toBitVec_toUSize
attribute [grind_homo] ISize.eq_iff_toBitVec_eq
attribute [grind_homo] ISize.toBitVec_zero
attribute [grind_homo] ISize.toBitVec_one
attribute [grind_homo] ISize.toBitVec_not
attribute [grind_homo] ISize.toBitVec_neg
attribute [grind_homo] ISize.toBitVec_ofNat


namespace ISize

@[grind_homo] theorem toInt_eq_toBitVec_signed (x : ISize) : x.toInt = x.toBitVec.signed := rfl

@[grind_homo_pred]
theorem toBitVec_le (a b : ISize) : ISize.le a b ↔ (a.toBitVec.sle b.toBitVec = true) := Iff.rfl

@[grind_homo_pred]
theorem toBitVec_lt (a b : ISize) : ISize.lt a b ↔ (a.toBitVec.slt b.toBitVec = true) := Iff.rfl

theorem toBitVec_injective : Function.Injective ISize.toBitVec := fun ⟨_⟩ ⟨_⟩ h => by congr; exact USize.toBitVec_injective h
attribute [grind inj] toBitVec_injective

@[grind_homo] theorem toBitVec_ofUSize (a : USize) : (ISize.ofUSize a).toBitVec = a.toBitVec := rfl

@[grind_homo] theorem testBit_toBitVec (x : ISize) (i : Nat) :
  x.toInt.testBit i = if i < System.Platform.numBits then x.toBitVec.getLsbD i else x.toBitVec.getLsbD (System.Platform.numBits - 1) :=
  BitVec.testBit_toInt System.Platform.numBits_pos x.toBitVec i

end ISize

