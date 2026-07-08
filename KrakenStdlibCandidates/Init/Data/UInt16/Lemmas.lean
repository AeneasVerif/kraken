prelude
import Init.Data.UInt
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
import KrakenStdlibCandidates.Init.Data.UInt32.Lemmas


/-!
# Grind homomorphism lemmas for UInt16.
-/

attribute [grind_homo] UInt16.toBitVec_add
attribute [grind_homo] UInt16.toBitVec_sub
attribute [grind_homo] UInt16.toBitVec_mul
attribute [grind_homo] UInt16.toBitVec_div
attribute [grind_homo] UInt16.toBitVec_mod
attribute [grind_homo] UInt16.toBitVec_and
attribute [grind_homo] UInt16.toBitVec_or
attribute [grind_homo] UInt16.toBitVec_xor
attribute [grind_homo] UInt16.toBitVec_shiftLeft
attribute [grind_homo] UInt16.toBitVec_shiftRight
attribute [grind_homo] UInt16.toBitVec_ofNat
attribute [grind_homo] UInt16.toBitVec_ofNat'
attribute [grind_homo] UInt16.toBitVec_toUInt8
attribute [grind_homo] UInt16.toBitVec_toUInt32
attribute [grind_homo] UInt16.toBitVec_toUInt64
attribute [grind_homo] UInt16.toBitVec_toUSize
attribute [grind_homo] UInt16.toBitVec_toInt16
attribute [grind_homo] UInt16.eq_iff_toBitVec_eq
attribute [grind_homo] UInt16.toBitVec_zero
attribute [grind_homo] UInt16.toBitVec_one
attribute [grind_homo] UInt16.toBitVec_not
attribute [grind_homo] UInt16.toBitVec_neg


@[grind_homo] theorem UInt16.toBitVec_toNat (n : UInt16) : n.toNat = n.toBitVec.toNat := rfl
attribute [grind_homo] UInt16.toNat_toUInt32 UInt16.toNat_toUInt64
@[grind_homo] theorem UInt16.toBitVec_toNat_toUInt32 (x : UInt16) : x.toUInt32.toBitVec.toNat = x.toBitVec.toNat := rfl
@[grind_homo] theorem UInt16.toBitVec_toNat_toUInt64 (x : UInt16) : x.toUInt64.toBitVec.toNat = x.toBitVec.toNat := rfl

@[grind_homo_pred] theorem UInt16.toNat_le_max (x : UInt16) : x.toNat ≤ 65535 := by
  have : x.toNat < 65536 := x.toBitVec.isLt
  omega

@[grind_homo] theorem UInt16.toNat_add_upcast32 (x y : UInt16) : (x.toUInt32 + y.toUInt32).toNat = x.toNat + y.toNat := by
  have hx : x.toNat < 65536 := x.toBitVec.isLt
  have hy : y.toNat < 65536 := y.toBitVec.isLt
  rw [UInt32.toBitVec_toNat, UInt32.toBitVec_add, BitVec.toNat_add]
  rw [UInt16.toBitVec_toNat_toUInt32, UInt16.toBitVec_toNat_toUInt32]
  rw [← UInt16.toBitVec_toNat, ← UInt16.toBitVec_toNat]
  change (x.toNat + y.toNat) % 4294967296 = x.toNat + y.toNat
  omega

@[grind_homo] theorem UInt16.toNat_mul_upcast32 (x y : UInt16) : (x.toUInt32 * y.toUInt32).toNat = x.toNat * y.toNat := by
  have hx : x.toNat ≤ 65535 := UInt16.toNat_le_max x
  have hy : y.toNat ≤ 65535 := UInt16.toNat_le_max y
  have h_mul : x.toNat * y.toNat ≤ 65535 * 65535 := Nat.mul_le_mul hx hy
  rw [UInt32.toBitVec_toNat, UInt32.toBitVec_mul, BitVec.toNat_mul]
  rw [UInt16.toBitVec_toNat_toUInt32, UInt16.toBitVec_toNat_toUInt32]
  rw [← UInt16.toBitVec_toNat, ← UInt16.toBitVec_toNat]
  change (x.toNat * y.toNat) % 4294967296 = x.toNat * y.toNat
  apply Nat.mod_eq_of_lt
  have h_lt : 65535 * 65535 < 4294967296 := by decide
  exact Nat.lt_of_le_of_lt h_mul h_lt


@[grind_homo_pred] theorem UInt16.toBitVec_le (a b : UInt16) : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := Iff.rfl
@[grind_homo_pred] theorem UInt16.toBitVec_lt (a b : UInt16) : a < b ↔ a.toBitVec < b.toBitVec := Iff.rfl

namespace UInt16
theorem toBitVec_injective : Function.Injective UInt16.toBitVec := fun _ _ => UInt16.eq_of_toBitVec_eq
attribute [grind inj] toBitVec_injective
end UInt16
