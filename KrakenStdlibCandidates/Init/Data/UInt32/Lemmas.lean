prelude
import Init.Data.UInt
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
import KrakenStdlibCandidates.Init.Data.UInt64.Lemmas


/-!
# Grind homomorphism lemmas for UInt32.
-/

attribute [grind_homo] UInt32.toBitVec_add
attribute [grind_homo] UInt32.toBitVec_sub
attribute [grind_homo] UInt32.toBitVec_mul
attribute [grind_homo] UInt32.toBitVec_div
attribute [grind_homo] UInt32.toBitVec_mod
attribute [grind_homo] UInt32.toBitVec_and
attribute [grind_homo] UInt32.toBitVec_or
attribute [grind_homo] UInt32.toBitVec_xor
attribute [grind_homo] UInt32.toBitVec_shiftLeft
attribute [grind_homo] UInt32.toBitVec_shiftRight
attribute [grind_homo] UInt32.toBitVec_ofNat
attribute [grind_homo] UInt32.toBitVec_ofNat'
attribute [grind_homo] UInt32.toBitVec_toUInt8
attribute [grind_homo] UInt32.toBitVec_toUInt16
attribute [grind_homo] UInt32.toBitVec_toUInt64
attribute [grind_homo] UInt32.toBitVec_toUSize
attribute [grind_homo] UInt32.toBitVec_toInt32
attribute [grind_homo] UInt32.eq_iff_toBitVec_eq
attribute [grind_homo] UInt32.toBitVec_zero
attribute [grind_homo] UInt32.toBitVec_one
attribute [grind_homo] UInt32.toBitVec_not
attribute [grind_homo] UInt32.toBitVec_neg


@[grind_homo] theorem UInt32.toBitVec_toNat (n : UInt32) : n.toNat = n.toBitVec.toNat := rfl
attribute [grind_homo] UInt32.toNat_toUInt64
@[grind_homo] theorem UInt32.toBitVec_toNat_toUInt64 (x : UInt32) : x.toUInt64.toBitVec.toNat = x.toBitVec.toNat := rfl

@[grind_homo_pred] theorem UInt32.toNat_le_max (x : UInt32) : x.toNat ≤ 4294967295 := by
  have : x.toNat < 4294967296 := x.toBitVec.isLt
  omega

@[grind_homo] theorem UInt32.toNat_add_upcast64 (x y : UInt32) : (x.toUInt64 + y.toUInt64).toNat = x.toNat + y.toNat := by
  have hx : x.toNat < 4294967296 := x.toBitVec.isLt
  have hy : y.toNat < 4294967296 := y.toBitVec.isLt
  rw [UInt64.toBitVec_toNat, UInt64.toBitVec_add, BitVec.toNat_add]
  rw [UInt32.toBitVec_toNat_toUInt64, UInt32.toBitVec_toNat_toUInt64]
  rw [← UInt32.toBitVec_toNat, ← UInt32.toBitVec_toNat]
  change (x.toNat + y.toNat) % 18446744073709551616 = x.toNat + y.toNat
  omega

@[grind_homo] theorem UInt32.toNat_mul_upcast64 (x y : UInt32) : (x.toUInt64 * y.toUInt64).toNat = x.toNat * y.toNat := by
  have hx : x.toNat ≤ 4294967295 := UInt32.toNat_le_max x
  have hy : y.toNat ≤ 4294967295 := UInt32.toNat_le_max y
  have h_mul : x.toNat * y.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul hx hy
  rw [UInt64.toBitVec_toNat, UInt64.toBitVec_mul, BitVec.toNat_mul]
  rw [UInt32.toBitVec_toNat_toUInt64, UInt32.toBitVec_toNat_toUInt64]
  rw [← UInt32.toBitVec_toNat, ← UInt32.toBitVec_toNat]
  change (x.toNat * y.toNat) % 18446744073709551616 = x.toNat * y.toNat
  apply Nat.mod_eq_of_lt
  have h_lt : 4294967295 * 4294967295 < 18446744073709551616 := by decide
  exact Nat.lt_of_le_of_lt h_mul h_lt


@[grind_homo_pred] theorem UInt32.toBitVec_le (a b : UInt32) : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := Iff.rfl
@[grind_homo_pred] theorem UInt32.toBitVec_lt (a b : UInt32) : a < b ↔ a.toBitVec < b.toBitVec := Iff.rfl

namespace UInt32
theorem toBitVec_injective : Function.Injective UInt32.toBitVec := fun _ _ => UInt32.eq_of_toBitVec_eq
attribute [grind inj] toBitVec_injective
end UInt32
