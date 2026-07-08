prelude
import Init.Data.UInt
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
import KrakenStdlibCandidates.Init.Data.UInt16.Lemmas


/-!
# Grind homomorphism lemmas for UInt8.
-/

attribute [grind_homo] UInt8.toBitVec_add
attribute [grind_homo] UInt8.toBitVec_sub
attribute [grind_homo] UInt8.toBitVec_mul
attribute [grind_homo] UInt8.toBitVec_div
attribute [grind_homo] UInt8.toBitVec_mod
attribute [grind_homo] UInt8.toBitVec_and
attribute [grind_homo] UInt8.toBitVec_or
attribute [grind_homo] UInt8.toBitVec_xor
attribute [grind_homo] UInt8.toBitVec_shiftLeft
attribute [grind_homo] UInt8.toBitVec_shiftRight
attribute [grind_homo] UInt8.toBitVec_ofNat
attribute [grind_homo] UInt8.toBitVec_ofNat'
attribute [grind_homo] UInt8.toBitVec_toUInt16
attribute [grind_homo] UInt8.toBitVec_toUInt32
attribute [grind_homo] UInt8.toBitVec_toUInt64
attribute [grind_homo] UInt8.toBitVec_toUSize
attribute [grind_homo] UInt8.toBitVec_toInt8
attribute [grind_homo] UInt8.eq_iff_toBitVec_eq
attribute [grind_homo] UInt8.toBitVec_zero
attribute [grind_homo] UInt8.toBitVec_one
attribute [grind_homo] UInt8.toBitVec_not
attribute [grind_homo] UInt8.toBitVec_neg


@[grind_homo] theorem UInt8.toBitVec_toNat (n : UInt8) : n.toNat = n.toBitVec.toNat := rfl
attribute [grind_homo] UInt8.toNat_toUInt16 UInt8.toNat_toUInt32 UInt8.toNat_toUInt64
@[grind_homo] theorem UInt8.toBitVec_toNat_toUInt16 (x : UInt8) : x.toUInt16.toBitVec.toNat = x.toBitVec.toNat := rfl
@[grind_homo] theorem UInt8.toBitVec_toNat_toUInt32 (x : UInt8) : x.toUInt32.toBitVec.toNat = x.toBitVec.toNat := rfl
@[grind_homo] theorem UInt8.toBitVec_toNat_toUInt64 (x : UInt8) : x.toUInt64.toBitVec.toNat = x.toBitVec.toNat := rfl

@[grind_homo_pred] theorem UInt8.toNat_le_max (x : UInt8) : x.toNat ≤ 255 := by
  have : x.toNat < 256 := x.toBitVec.isLt
  omega

@[grind_homo] theorem UInt8.toNat_add_upcast16 (x y : UInt8) : (x.toUInt16 + y.toUInt16).toNat = x.toNat + y.toNat := by
  have hx : x.toNat < 256 := x.toBitVec.isLt
  have hy : y.toNat < 256 := y.toBitVec.isLt
  rw [UInt16.toBitVec_toNat, UInt16.toBitVec_add, BitVec.toNat_add]
  rw [UInt8.toBitVec_toNat_toUInt16, UInt8.toBitVec_toNat_toUInt16]
  rw [← UInt8.toBitVec_toNat, ← UInt8.toBitVec_toNat]
  change (x.toNat + y.toNat) % 65536 = x.toNat + y.toNat
  omega

@[grind_homo] theorem UInt8.toNat_mul_upcast16 (x y : UInt8) : (x.toUInt16 * y.toUInt16).toNat = x.toNat * y.toNat := by
  have hx : x.toNat ≤ 255 := UInt8.toNat_le_max x
  have hy : y.toNat ≤ 255 := UInt8.toNat_le_max y
  have h_mul : x.toNat * y.toNat ≤ 255 * 255 := Nat.mul_le_mul hx hy
  rw [UInt16.toBitVec_toNat, UInt16.toBitVec_mul, BitVec.toNat_mul]
  rw [UInt8.toBitVec_toNat_toUInt16, UInt8.toBitVec_toNat_toUInt16]
  rw [← UInt8.toBitVec_toNat, ← UInt8.toBitVec_toNat]
  change (x.toNat * y.toNat) % 65536 = x.toNat * y.toNat
  apply Nat.mod_eq_of_lt
  have h_lt : 255 * 255 < 65536 := by decide
  exact Nat.lt_of_le_of_lt h_mul h_lt


@[grind_homo_pred] theorem UInt8.toBitVec_le (a b : UInt8) : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := Iff.rfl
@[grind_homo_pred] theorem UInt8.toBitVec_lt (a b : UInt8) : a < b ↔ a.toBitVec < b.toBitVec := Iff.rfl

namespace UInt8
theorem toBitVec_injective : Function.Injective UInt8.toBitVec := fun _ _ => UInt8.eq_of_toBitVec_eq
attribute [grind inj] toBitVec_injective
end UInt8

@[ext] theorem UInt8.ext (a b : UInt8) : a.toBitVec = b.toBitVec → a = b := UInt8.eq_of_toBitVec_eq

instance : Std.Commutative (α := UInt8) (· + ·) := ⟨UInt8.add_comm⟩
instance : Std.Associative (α := UInt8) (· + ·) := ⟨UInt8.add_assoc⟩
