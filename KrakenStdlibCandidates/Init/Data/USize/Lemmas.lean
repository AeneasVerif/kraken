prelude
import Init.Data.UInt
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas


/-!
# Grind homomorphism lemmas for USize.
-/

attribute [grind_homo] USize.toBitVec_add
attribute [grind_homo] USize.toBitVec_sub
attribute [grind_homo] USize.toBitVec_mul
attribute [grind_homo] USize.toBitVec_div
attribute [grind_homo] USize.toBitVec_mod
attribute [grind_homo] USize.toBitVec_and
attribute [grind_homo] USize.toBitVec_or
attribute [grind_homo] USize.toBitVec_xor
attribute [grind_homo] USize.toBitVec_shiftLeft
attribute [grind_homo] USize.toBitVec_shiftRight
attribute [grind_homo] USize.toBitVec_ofNat
attribute [grind_homo] USize.toBitVec_ofNat'
attribute [grind_homo] USize.toBitVec_toUInt8
attribute [grind_homo] USize.toBitVec_toUInt16
attribute [grind_homo] USize.toBitVec_toUInt32
attribute [grind_homo] USize.toBitVec_toUInt64
attribute [grind_homo] USize.toBitVec_toISize
attribute [grind_homo] USize.eq_iff_toBitVec_eq
attribute [grind_homo] USize.toBitVec_zero
attribute [grind_homo] USize.toBitVec_one
attribute [grind_homo] USize.toBitVec_not
attribute [grind_homo] USize.toBitVec_neg


@[grind_homo] theorem USize.toBitVec_toNat (n : USize) : n.toNat = n.toBitVec.toNat := rfl

@[grind_homo_pred] theorem USize.toBitVec_le (a b : USize) : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := Iff.rfl
@[grind_homo_pred] theorem USize.toBitVec_lt (a b : USize) : a < b ↔ a.toBitVec < b.toBitVec := Iff.rfl

namespace USize

theorem toBitVec_injective : Function.Injective USize.toBitVec := fun ⟨_⟩ ⟨_⟩ h => by congr
attribute [grind inj] toBitVec_injective

end USize


