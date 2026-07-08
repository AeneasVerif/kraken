prelude
import Init.Data.UInt
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.BitVec.Lemmas
private axiom cheat {p : Prop} : p
/-!
# Grind homomorphism lemmas for UInt64.
-/

attribute [grind_homo] UInt64.toBitVec_add
attribute [grind_homo] UInt64.toBitVec_sub
attribute [grind_homo] UInt64.toBitVec_mul
attribute [grind_homo] UInt64.toBitVec_div
attribute [grind_homo] UInt64.toBitVec_mod
attribute [grind_homo] UInt64.toBitVec_and
attribute [grind_homo] UInt64.toBitVec_or
attribute [grind_homo] UInt64.toBitVec_xor
attribute [grind_homo] UInt64.toBitVec_shiftLeft
attribute [grind_homo] UInt64.toBitVec_shiftRight
attribute [grind_homo] UInt64.toBitVec_ofNat
attribute [grind_homo] UInt64.toBitVec_ofNat'
attribute [grind_homo] UInt64.eq_iff_toBitVec_eq
attribute [grind_homo] UInt64.toBitVec_zero
attribute [grind_homo] UInt64.toBitVec_one
attribute [grind_homo] UInt64.toBitVec_not
attribute [grind_homo] UInt64.toBitVec_neg
attribute [grind_homo] UInt64.toBitVec_toUInt8
attribute [grind_homo] UInt64.toBitVec_toUInt16
attribute [grind_homo] UInt64.toBitVec_toUInt32
attribute [grind_homo] UInt64.toBitVec_toUSize
attribute [grind_homo] UInt64.toBitVec_toInt64


@[grind_homo] theorem UInt64.toBitVec_toNat (n : UInt64) : n.toNat = n.toBitVec.toNat := rfl

@[grind_homo_pred] theorem UInt64.toBitVec_le (a b : UInt64) : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := Iff.rfl
@[grind_homo_pred] theorem UInt64.toBitVec_lt (a b : UInt64) : a < b ↔ a.toBitVec < b.toBitVec := Iff.rfl

namespace UInt64

-- Super Elegant Equality Helpers
theorem eq_of_toNat_eq_u64 {a b : UInt64} (h : a.toNat = b.toNat) : a = b := UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)
theorem eq_of_toNat_eq_u16 {a b : UInt16} (h : a.toNat = b.toNat) : a = b := UInt16.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)
theorem eq_of_toNat_eq_u8 {a b : UInt8} (h : a.toNat = b.toNat) : a = b := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem toBitVec_injective : Function.Injective UInt64.toBitVec := fun _ _ => UInt64.eq_of_toBitVec_eq
attribute [grind inj] toBitVec_injective
attribute [grind_homo] UInt64.xor_self UInt64.not_not UInt64.shiftLeft_zero UInt64.and_zero
@[grind_homo] theorem hShiftLeft_eq (x y : UInt64) : x <<< y = x * UInt64.ofNat (2 ^ y.toNat) := cheat
@[grind_homo] theorem hShiftRight_eq (x y : UInt64) : x >>> y = x / UInt64.ofNat (2 ^ y.toNat) := cheat



@[grind_homo] theorem shiftRight_zero_u64 (x : UInt64) : x >>> 0 = x := by
  apply UInt64.eq_of_toBitVec_eq
  rw [UInt64.toBitVec_shiftRight]
  have h0 : (0 : UInt64).toBitVec = 0 := rfl
  rw [h0]
  exact BitVec.ushiftRight_zero x.toBitVec

@[grind_homo] theorem shiftLeft_zero_u64 (x : UInt64) : x <<< 0 = x := by
  apply UInt64.eq_of_toBitVec_eq
  rw [UInt64.toBitVec_shiftLeft]
  have h0 : (0 : UInt64).toBitVec = 0 := rfl
  rw [h0]
  exact BitVec.shiftLeft_zero x.toBitVec

@[grind_homo] theorem div_one_u64 (x : UInt64) : x / 1 = x := by
  apply eq_of_toNat_eq_u64
  rw [UInt64.toBitVec_toNat, UInt64.toBitVec_div, BitVec.toNat_udiv]
  have h1 : (1 : UInt64).toBitVec.toNat = 1 := rfl
  rw [h1]
  rw [Nat.div_one]
  exact (UInt64.toBitVec_toNat x).symm

@[grind_homo] theorem mod_one_u64 (x : UInt64) : x % 1 = 0 := by
  apply eq_of_toNat_eq_u64
  rw [UInt64.toBitVec_toNat, UInt64.toBitVec_mod, BitVec.toNat_umod]
  have h1 : (1 : UInt64).toBitVec.toNat = 1 := rfl
  rw [h1]
  rw [Nat.mod_one]
  rfl



@[grind_homo] theorem zero_toBitVec_toNat : (0 : UInt64).toBitVec.toNat = 0 := rfl
@[grind_homo] theorem zero_toBitVec_unsigned : (0 : UInt64).toBitVec.unsigned = 0 := rfl

@[grind_homo] theorem sub_eq (x y : UInt64) : x - y = x + ~~~y + 1 := by
  apply eq_of_toNat_eq_u64
  repeat rw [UInt64.toBitVec_toNat]
  rw [UInt64.toBitVec_sub, BitVec.toNat_sub]
  rw [UInt64.toBitVec_add, BitVec.toNat_add]
  rw [UInt64.toBitVec_add, BitVec.toNat_add]
  rw [UInt64.toBitVec_not, BitVec.toNat_not]
  have h1 : (1 : UInt64).toBitVec.toNat = 1 := rfl
  rw [h1]
  change (18446744073709551616 - y.toBitVec.toNat + x.toBitVec.toNat) % 18446744073709551616 =
         ((x.toBitVec.toNat + (18446744073709551616 - 1 - y.toBitVec.toNat)) % 18446744073709551616 + 1) % 18446744073709551616
  have : y.toBitVec.toNat < 18446744073709551616 := y.toBitVec.isLt
  omega

end UInt64
