prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Lean
import KrakenStdlibCandidates.Init.Data.Nat.Bitwise.Lemmas
import KrakenStdlibCandidates.Init.Data.Int.Bitwise.Lemmas


/-!
# Grind homomorphism lemmas for BitVec.
-/

open Lean Meta
set_option autoImplicit true

namespace BitVec

@[grind_homo] theorem toNat_setWidth_8_16 (x : BitVec 8) : (BitVec.setWidth 16 x).toNat = x.toNat := by
  apply BitVec.toNat_setWidth'
  decide

@[grind_homo] theorem toNat_setWidth_16_32 (x : BitVec 16) : (BitVec.setWidth 32 x).toNat = x.toNat := by
  apply BitVec.toNat_setWidth'
  decide

@[grind_homo] theorem toNat_setWidth_32_64 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  apply BitVec.toNat_setWidth'
  decide

@[grind_homo] theorem toNat_setWidth_64_64 (x : BitVec 64) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  apply BitVec.toNat_setWidth'
  decide

@[grind_homo] theorem setWidth_same_eq {w : Nat} (x : BitVec w) : BitVec.setWidth w x = x := by
  ext i hi; grind

@[grind_homo] theorem setWidth_64_eq (x : BitVec 64) : BitVec.setWidth 64 x = x := by
  ext i hi; grind

@[grind_homo] theorem toNat_setWidth_same {w : Nat} (x : BitVec w) : (BitVec.setWidth w x).toNat = x.toNat := by
  rw [setWidth_same_eq]

attribute [grind_homo] BitVec.toNat_and
attribute [grind_homo] BitVec.toNat_or
attribute [grind_homo] BitVec.toNat_xor
attribute [grind_homo] BitVec.toNat_shiftLeft
attribute [grind_homo] BitVec.toNat_ushiftRight
attribute [grind_homo] BitVec.toNat_add

@[grind_homo] theorem BitVec.toNat_sub_sub_liveverif (j i count : BitVec 32)
    (h : i.unsigned + count.unsigned ≤ j.unsigned) :
    (j - i - count).toNat = j.toNat - i.toNat - count.toNat := by
  have h_nat : i.toNat + count.toNat ≤ j.toNat := by
    change (i.toNat : Int) + (count.toNat : Int) ≤ (j.toNat : Int) at h
    omega
  have h1 : i.toNat ≤ j.toNat := by omega
  have h2 : count.toNat ≤ (j - i).toNat := by
    rw [BitVec.toNat_sub_of_le h1]
    omega
  rw [BitVec.toNat_sub_of_le h2, BitVec.toNat_sub_of_le h1]

@[grind_homo] theorem BitVec.add_sub_cancel_liveverif (i j count : BitVec 32)
    (h : i.unsigned + count.unsigned ≤ j.unsigned) :
    i.toNat + count.toNat + (j - i).toNat = count.toNat + j.toNat := by
  have h1 : i.toNat ≤ j.toNat := by
    change (i.toNat : Int) + (count.toNat : Int) ≤ (j.toNat : Int) at h
    omega
  rw [BitVec.toNat_sub_of_le h1]
  omega

@[grind_homo] theorem BitVec.add_sub_sub_cancel_liveverif (i j count : BitVec 32)
    (h : i.unsigned + count.unsigned ≤ j.unsigned) :
    i.toNat + count.toNat + (j - i - count).toNat = j.toNat := by
  rw [BitVec.toNat_sub_sub_liveverif j i count h]
  have h1 : i.toNat + count.toNat ≤ j.toNat := by
    change (i.toNat : Int) + (count.toNat : Int) ≤ (j.toNat : Int) at h
    omega
  omega

attribute [grind_homo] BitVec.toNat_mul
attribute [grind_homo] BitVec.toNat_udiv
attribute [grind_homo] BitVec.toNat_umod
attribute [grind_homo] BitVec.toNat_neg
attribute [grind_homo] BitVec.toNat_ofNat
attribute [grind_homo] BitVec.ofNat_toNat
attribute [grind_homo] UInt64.toBitVec_ofBitVec
attribute [simp, grind_homo] BitVec.xor_allOnes
attribute [simp, grind_homo] BitVec.allOnes_and
attribute [simp, grind_homo] BitVec.and_allOnes
attribute [simp, grind_homo] BitVec.not_zero
attribute [simp, grind_homo] BitVec.zero_and
attribute [simp, grind_homo] BitVec.and_zero
attribute [simp, grind_homo] BitVec.zero_or
attribute [simp, grind_homo] BitVec.or_zero
attribute [simp, grind_homo] BitVec.zero_xor
attribute [simp, grind_homo] BitVec.xor_zero
attribute [simp, grind_homo] BitVec.xor_self



@[grind_homo_pred] theorem BitVec.toNat_le {w : Nat} (a b : BitVec w) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl
@[grind_homo_pred] theorem BitVec.toNat_lt {w : Nat} (a b : BitVec w) : a < b ↔ a.toNat < b.toNat := Iff.rfl
@[grind_homo_pred] theorem BitVec.toNat_eq {w : Nat} (a b : BitVec w) : a = b ↔ a.toNat = b.toNat := ⟨fun h => by subst h; rfl, BitVec.eq_of_toNat_eq⟩






theorem add_left_comm {w : Nat} (a b c : BitVec w) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

instance {w : Nat} : Std.Commutative (α := BitVec w) (· + ·) := ⟨BitVec.add_comm⟩
instance {w : Nat} : Std.Associative (α := BitVec w) (· + ·) := ⟨BitVec.add_assoc⟩



theorem toNat_injective' {w : Nat} : Function.Injective (BitVec.toNat : BitVec w → Nat) := fun _ _ => BitVec.eq_of_toNat_eq
attribute [grind inj] toNat_injective'

@[grind_homo] theorem unsigned_and {w : Nat} (a b : BitVec w) : (a &&& b).unsigned = a.unsigned &&& b.unsigned := by
  exact congrArg Int.ofNat (toNat_and a b)
theorem toNat_and_le_right {w : Nat} (x y : BitVec w) : (x &&& y).toNat ≤ y.toNat := by


  rw [toNat_and]
  apply Nat.and_le_right

theorem toNat_ushiftRight_le {w : Nat} (x : BitVec w) (n : Nat) : (x >>> n).toNat ≤ x.toNat := by
  rw [toNat_ushiftRight]
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_le_self

@[grind_homo_pred] theorem unsigned_range (x : BitVec w) : 0 <= x.unsigned ∧ x.unsigned < 2^w :=
  by have := x.isLt; dsimp only [unsigned]; lia

@[grind_homo_pred] theorem toNat_range {w : Nat} (x : BitVec w) : x.toNat < 2^w :=
  x.isLt


@[grind_homo] theorem unsigned_ofNat_toNat {w : Nat} (x : BitVec w) :
    (BitVec.ofNat w x.toNat).unsigned = x.unsigned := by
  rcases x with ⟨⟨val, isLt⟩⟩
  dsimp [BitVec.ofNat, unsigned, Fin.ofNat]
  have h1 : 0 ≤ (val : Int) := by omega
  have h_cast : (2^w : Int) = ((2^w : Nat) : Int) := rfl
  have h2 : (val : Int) < (2^w : Int) := by rw [h_cast]; omega
  rw [Int.emod_eq_of_lt h1 h2]

@[grind_homo] theorem UInt64.unsigned_ofNat_toNat (x : UInt64) :
    (BitVec.ofNat 64 x.toNat).unsigned = x.toBitVec.unsigned :=
  show (BitVec.ofNat 64 x.toBitVec.toNat).unsigned = _ from
  BitVec.unsigned_ofNat_toNat x.toBitVec

@[grind_homo] theorem UInt64.ofNat_toNat (x : UInt64) :
    BitVec.ofNat 64 x.toNat = x.toBitVec := by
  change BitVec.ofNat 64 (BitVec.toNat x.toBitVec) = x.toBitVec
  exact BitVec.ofNat_toNat 64 x.toBitVec


@[grind_homo] theorem unsigned_add (x y : BitVec w) :
  (x + y).unsigned = (x.unsigned + y.unsigned) % (2 ^ w) := by
  dsimp only [unsigned]; simp

theorem unsigned_add_eval (x y : BitVec w) :
    (x + y).unsigned = if x.unsigned + y.unsigned < (2^w : Int) then x.unsigned + y.unsigned else x.unsigned + y.unsigned - (2^w : Int) := by
  have := x.unsigned_range
  have := y.unsigned_range
  rw [unsigned_add]
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · have h_eq : (x.unsigned + y.unsigned) % (2^w : Int) = ((2^w : Int) + (x.unsigned + y.unsigned - 2^w)) % (2^w : Int) := by
      congr 1; omega
    rw [h_eq, Int.add_emod_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)

@[grind_homo] theorem unsigned_mul (x y : BitVec w) :
  (x * y).unsigned = (x.unsigned * y.unsigned) % (2 ^ w) := by
  dsimp only [unsigned]; simp

@[grind_homo] theorem unsigned_sub (x y : BitVec w) :
    (x - y).unsigned = (x.unsigned - y.unsigned) % (2 ^ w) := by
  dsimp only [unsigned]
  rw [BitVec.toNat_sub]
  simp only [Int.ofNat_eq_natCast]
  rw [Int.natCast_emod, Int.natCast_add, Int.natCast_sub (by omega)]
  rw [Int.natCast_pow, Int.cast_ofNat_Int]
  have h_rearrange : (2 ^ w - ↑y.toNat + ↑x.toNat : Int) = 2 ^ w + (↑x.toNat - ↑y.toNat) := by
    omega
  rw [h_rearrange, Int.add_emod_left]

theorem unsigned_sub_eval (x y : BitVec w) :
    (x - y).unsigned = if y.unsigned ≤ x.unsigned then x.unsigned - y.unsigned else x.unsigned + (2^w : Int) - y.unsigned := by
  have hx := x.unsigned_range
  have hy := y.unsigned_range
  rw [unsigned_sub]
  split <;> rename_i h
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [← Int.add_emod_left]
    have h_eq : ((2^w : Int) + (x.unsigned - y.unsigned)) = x.unsigned + (2^w : Int) - y.unsigned := by omega
    rw [h_eq]
    exact Int.emod_eq_of_lt (by omega) (by omega)

@[grind_homo] theorem unsigned_inj {w : Nat} {x y : BitVec w} (h : x.unsigned = y.unsigned) :
  x = y := by
  dsimp only [unsigned] at h
  apply eq_of_toNat_eq
  injection h

@[grind_homo] theorem unsigned_inj_iff {w : Nat} {x y : BitVec w} :
  x = y ↔ x.unsigned = y.unsigned := by
  constructor
  · intro h; rw [h]
  · apply unsigned_inj

@[grind_homo] theorem unsigned_lt {w : Nat} (x y : BitVec w) :
  (x < y) = (x.toNat < y.toNat ∧ x.unsigned < y.unsigned) := by
  apply propext
  dsimp only [unsigned, LT.lt]
  constructor
  · intro h
    exact ⟨h, Int.ofNat_lt.mpr h⟩
  · intro h
    exact h.1

@[grind_homo] theorem unsigned_le {w : Nat} (x y : BitVec w) :
  (x ≤ y) = (x.toNat ≤ y.toNat ∧ x.unsigned ≤ y.unsigned) := by
  apply propext
  dsimp only [unsigned, LE.le]
  constructor
  · intro h
    exact ⟨h, Int.ofNat_le.mpr h⟩
  · intro h
    exact h.1

@[grind_homo] theorem unsigned_ite {w : Nat} (c : Prop) [Decidable c] (x y : BitVec w) :
  (if c then x else y).unsigned = if c then x.unsigned else y.unsigned := by
  split <;> rfl

@[grind_homo] theorem signed_ite {w : Nat} (c : Prop) [Decidable c] (x y : BitVec w) :
  (if c then x else y).signed = if c then x.signed else y.signed := by
  split <;> rfl


 @[grind_homo] theorem toNat_eq_unsigned {w : Nat} (x : BitVec w) :
  x.toNat = x.unsigned := by
  rfl
theorem ofNat_max_eq_allOnes {w : Nat} : BitVec.ofNat w (2^w - 1) = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.allOnes]

-- Zmod.unsigned_of_Z / bits.unsigned_of_Z equivalents
@[grind_homo] theorem unsigned_ofNat (w n : Nat) :
  (BitVec.ofNat w n).unsigned = n % (2 ^ w) := by dsimp only [unsigned]; simp

@[grind_homo] theorem signed_ofNat (w n : Nat) :
  (BitVec.ofNat w n).signed = (Int.ofNat n).bmod (2 ^ w) := by
  have h : (BitVec.ofNat w n) = OfNat.ofNat n := rfl
  rw [h]
  exact BitVec.toInt_ofNat n

@[grind_homo] theorem unsigned_ofInt (w : Nat) (i : Int) :
  (BitVec.ofInt w i).unsigned = i % (2 ^ w) := by
  dsimp only [unsigned]
  rw [BitVec.toNat_ofInt]
  apply Int.toNat_of_nonneg
  apply Int.emod_nonneg
  apply Int.ne_of_gt
  apply Int.natCast_pos.mpr
  apply Nat.two_pow_pos

@[grind_homo] theorem signed_ofInt (w : Nat) (i : Int) :
  (BitVec.ofInt w i).signed = i.bmod (2 ^ w) := by exact toInt_ofInt i

@[grind_homo] theorem ofInt_signed {w : Nat} (a : BitVec w) :
    BitVec.ofInt w a.signed = a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.signed]

@[grind_homo] theorem unsigned_instOfNat (w n : Nat) :
  (@OfNat.ofNat _ _ (@BitVec.instOfNat w n)).unsigned = n % (2 ^ w) :=
    by apply unsigned_ofNat

@[grind_homo] theorem signed_instOfNat (w n : Nat) :
  (@OfNat.ofNat _ _ (@BitVec.instOfNat w n)).signed = (Int.ofNat n).bmod (2 ^ w) :=
    by apply signed_ofNat

-- Zmod.unsigned_0_iff
@[grind_homo] theorem unsigned_zero_iff {w : Nat} {x : BitVec w} :
  x = 0#w ↔ x.unsigned = 0 := by
  dsimp only [unsigned]
  constructor
  · intro h; simp [h]
  · intros h; apply eq_of_toNat_eq; rw [toNat_zero]; lia

-- Zmod.unsigned_0
@[grind_homo] theorem unsigned_zero {w : Nat} :
  (0#w).unsigned = 0 := by rw [← unsigned_zero_iff]

@[grind_homo] theorem signed_zero {w : Nat} :
  (0#w).signed = 0 := by
  dsimp only [signed, BitVec.toInt]
  simp

-- Zmod.unsigned_nz
@[grind_homo] theorem unsigned_ne_zero {w : Nat} {x : BitVec w} (h : x ≠ 0#w) :
  x.unsigned ≠ 0 := by have := @unsigned_zero_iff _ x; lia

@[grind_homo] theorem unsigned_neg {w : Nat} (x : BitVec w) :
  (-x).unsigned = (-x.unsigned) % (2 ^ w) := by
  rw [←BitVec.zero_sub,unsigned_sub,unsigned_zero]; lia

-- bits.unsigned_width0
@[grind_homo] theorem unsigned_width0 (a : BitVec 0) :
  a.unsigned = 0 := by
  dsimp only [unsigned]; simp [toNat_zero_length]

-- bits.unsigned_firstn
@[grind_homo] theorem unsigned_truncate {m : Nat} (n : Nat) (a : BitVec m) :
  (BitVec.truncate n a).unsigned = a.unsigned % (2 ^ n) := by
  dsimp only [unsigned]; simp

@[grind_homo] theorem truncate_truncate_16_32 (a : BitVec 32) :
    (a.truncate 16).truncate 8 = a.truncate 8 := by
  apply unsigned_inj
  rw [unsigned_truncate, unsigned_truncate, unsigned_truncate]
  have h_eq : (a.toNat % 2^16 % 2^8 : Nat) = a.toNat % 2^8 := Nat.mod_mod_of_dvd a.toNat (by decide)
  exact congrArg Int.ofNat h_eq

@[grind_homo] theorem truncate_truncate_8_32 (a : BitVec 32) :
    (a.truncate 8).truncate 8 = a.truncate 8 := by
  apply unsigned_inj
  rw [unsigned_truncate, unsigned_truncate]
  have h_eq : (a.toNat % 2^8 % 2^8 : Nat) = a.toNat % 2^8 := Nat.mod_mod a.toNat (2^8)
  exact congrArg Int.ofNat h_eq

theorem unsigned_truncate_small (x : BitVec w) (h : x.unsigned < 2^n) : (x.truncate n).unsigned = x.unsigned := by
  have := x.unsigned_range
  rw [unsigned_truncate,Int.emod_eq_of_lt] <;> lia

-- bits.unsigned_slice
@[grind_homo] theorem unsigned_extractLsb' {w : Nat} (start len : Nat) (a : BitVec w) :
  (BitVec.extractLsb' start len a).unsigned = (a.unsigned / (2 ^ start)) % (2 ^ len) := by
  dsimp only [unsigned]; rw [extractLsb'_toNat]
  simp [Nat.shiftRight_eq_div_pow]

-- bits.unsigned_not'
@[grind_homo] theorem unsigned_not' {n : Nat} (x : BitVec n) :
  (~~~x).unsigned = (2 ^ n - 1) - x.unsigned := by
  dsimp only [unsigned]; rw [toNat_not]; have := x.isLt; lia

-- bits.unsigned_slu / Zmod.unsigned_slu
-- Logical shift left. Assuming shift amount is Nat.
@[grind_homo] theorem unsigned_shiftLeft {n : Nat} (x : BitVec n) (y : Nat) :
  (x <<< y).unsigned = (x.unsigned * (2 ^ y)) % (2 ^ n) := by
  dsimp only [unsigned]; rw [toNat_shiftLeft]; simp [Nat.shiftLeft_eq]

-- bits.unsigned_skipn / Zmod.unsigned_sru
@[grind_homo] theorem unsigned_ushiftRight {m : Nat} (a : BitVec m) (n : Nat) :
  (a >>> n).unsigned = a.unsigned / (2 ^ n) := by
  dsimp only [unsigned]; rw [toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]

attribute [grind_homo] BitVec.toNat_append unsigned_append


-- bits.unsigned_srs
@[grind_homo] theorem unsigned_sshiftRight {n : Nat} (x : BitVec n) (y : Nat) :
  (x.sshiftRight y).unsigned = (x.signed / (2 ^ y)) % (2 ^ n) := by
  dsimp only [sshiftRight, signed]; rw [unsigned_ofInt]; simp [Int.shiftRight_eq_div_pow]

@[grind_homo] theorem signed_sshiftRight {n : Nat} (x : BitVec n) (y : Nat) :
  (x.sshiftRight y).signed = (x.signed / (2 ^ y)).bmod (2 ^ n) := by
  dsimp only [sshiftRight]; rw [signed_ofInt]; simp [Int.shiftRight_eq_div_pow]

@[grind_homo] theorem unsigned_cast {n m : Nat} (h : n = m) (a : BitVec n) :
  (BitVec.cast h a).unsigned = a.unsigned := by
  dsimp only [unsigned]; rw [toNat_cast]

-- Zmod.unsigned_udiv / Zmod.unsigned_udiv_nonneg
@[grind_homo] theorem unsigned_udiv {w : Nat} (x y : BitVec w) :
  (x / y).unsigned = x.unsigned / y.unsigned := by
  dsimp only [unsigned]; rw [toNat_udiv]
  change ((x.toNat / y.toNat : Nat) : Int) = (x.toNat : Int) / (y.toNat : Int)
  omega

-- Zmod.unsigned_umod
@[grind_homo] theorem unsigned_umod {w : Nat} (x y : BitVec w) :
  (x % y).unsigned = x.unsigned % y.unsigned := by
  dsimp only [unsigned]; simp [toNat_umod]

-- Zmod.unsigned_pos
@[grind_homo] theorem unsigned_nonnegative {w : Nat} {x : BitVec w} (h : 0 ≤ x.signed) :
  x.unsigned = x.toInt := by
  dsimp only [unsigned]
  have := BitVec.toInt_pos_iff.mp h
  rw [toInt_eq_toNat_cond]
  lia

@[grind_homo] theorem unsigned_negative {w : Nat} {x : BitVec w} :
  x.signed < 0 → x.unsigned = (2 ^ w) + x.signed := by
  dsimp only [unsigned, signed, BitVec.toInt]; lia

-- Zmod.signed_eq_unsigned_iff
@[grind_homo] theorem signed_eq_unsigned_iff {w : Nat} (x : BitVec w) :
    x.signed = x.unsigned ↔ 2 * x.unsigned < (2 ^ w) := by
  have := @unsigned_negative _ x
  have := @unsigned_nonnegative _ x
  grind only [usr le_two_mul_toInt, usr two_mul_toInt_lt]

-- bits.unsigned_pow_nonneg_r
@[grind_homo] theorem unsigned_pow {n : Nat} (x : BitVec n) (z : Nat) :
  (x.pow z).unsigned = (x.unsigned ^ z) % (2 ^ n) := by
  induction z <;> simp_all [BitVec.pow, unsigned_ofNat, unsigned_mul, Int.pow_succ, Int.mul_comm, Int.mul_emod]

theorem unsigned_or' {w : Nat} (x y : BitVec w) :
  (x ||| y).unsigned = x.unsigned ||| y.unsigned := by
  exact congrArg Int.ofNat (toNat_or x y)

@[grind_homo] theorem unsigned_or {w : Nat} (x y : BitVec w) :
  (x ||| y).unsigned = (x.unsigned + y.unsigned) - (x.unsigned &&& y.unsigned) := by
  rw [unsigned_or', Int.lor_eq_add_sub_land]

@[grind_homo] theorem unsigned_xor' {w : Nat} (x y : BitVec w) :
  (x ^^^ y).unsigned = x.unsigned ^^^ y.unsigned := by
  exact congrArg Int.ofNat (toNat_xor x y)

@[grind_homo] theorem unsigned_xor {w : Nat} (x y : BitVec w) :
  (x ^^^ y).unsigned = (x.unsigned + y.unsigned) - 2 * (x.unsigned &&& y.unsigned) := by
  rw [unsigned_xor', Int.xor_eq_add_sub_land]

@[grind_homo] theorem unsigned_and_mask {w : Nat} (x y : BitVec w) (n : Nat) (h : y.unsigned = 2^n - 1) :
  (x &&& y).unsigned = x.unsigned % (2 ^ n) := by
  dsimp only [unsigned] at h ⊢
  change ↑y.toNat = (2^n : Int) - 1 at h
  rw [BitVec.toNat_and]
  have h2 : y.toNat = 2^n - 1 := by
    have h_cast : (2^n : Int) = ((2^n : Nat) : Int) := rfl
    rw [h_cast] at h; omega
  rw [h2]
  change Int.ofNat (x.toNat &&& (2^n - 1)) = Int.ofNat (x.toNat % 2^n)
  rw [Nat.and_two_pow_sub_one_eq_mod]

@[grind_homo] theorem unsigned_and_inv_mask {w : Nat} (x y : BitVec w) (n : Nat) (h : y.unsigned = 2^n - 1) :
  (x &&& ~~~y).unsigned = x.unsigned - x.unsigned % (2 ^ n) := by
  have h_nat : y.toNat = 2^n - 1 := by
    have h1 : (2^n : Int) = ((2^n : Nat) : Int) := rfl
    have h2 : 1 ≤ 2^n := Nat.two_pow_pos n
    have eq : ((2^n : Nat) : Int) - 1 = (((2^n - 1) : Nat) : Int) := by omega
    rw [h1, eq] at h; exact Int.ofNat_inj.mp h
  have h_shift : x &&& ~~~y = (x >>> n) <<< n := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    have hy : y.getLsbD i = decide (i < n) :=
      by rw [← BitVec.testBit_toNat, h_nat, Nat.testBit_two_pow_sub_one]
    rw [hy]; cases Nat.lt_or_ge i n <;> simp [*]
    have eq : n + (i - n) = i := by omega
    simp [Nat.not_lt_of_ge (by assumption), Bool.and_comm]
  rw [h_shift, unsigned_shiftLeft, unsigned_ushiftRight]
  have h_sub : x.unsigned / (2^n : Int) * (2^n : Int) = x.unsigned - x.unsigned % (2^n : Int) := by
    have := Int.mul_ediv_add_emod x.unsigned (2^n : Int)
    rw [Int.mul_comm]; omega
  have h_mul : 0 ≤ x.unsigned / (2^n : Int) * (2^n : Int) := by
    have := x.unsigned_range
    apply Int.mul_nonneg (Int.ediv_nonneg this.1 (by omega)) (by omega)
  rw [h_sub] at h_mul ⊢
  have h_pos : (0:Int) < 2^n := by exact Int.natCast_pos.mpr (Nat.two_pow_pos n)
  apply Int.emod_eq_of_lt h_mul (by
  have := Int.emod_lt_of_pos x.unsigned h_pos; have := x.unsigned_range; omega)

@[grind_homo] theorem unsigned_setWidth {w : Nat} (n : Nat) (a : BitVec w) :
  (a.setWidth n).unsigned = a.unsigned % (2 ^ n) := by
  dsimp only [BitVec.setWidth, BitVec.unsigned]
  split
  · rename_i h
    change (a.toNat : Int) = (a.toNat : Int) % (2 ^ n : Int)
    rw [Int.emod_eq_of_lt (by omega)]
    have := a.isLt
    have : 2^w ≤ 2^n := Nat.pow_le_pow_right (by decide) h
    exact_mod_cast (by omega : a.toNat < 2^n)
  · rw [BitVec.toNat_ofNat]
    rfl

@[grind_homo] theorem unsigned_zeroExtend {w : Nat} (n : Nat) (a : BitVec w) :
  (a.zeroExtend n).unsigned = a.unsigned % (2 ^ n) := by
  rw [BitVec.zeroExtend]
  exact unsigned_setWidth n a

@[grind_homo] theorem unsigned_rotateLeft {w : Nat} (a : BitVec w) (n : Nat) :
  (a.rotateLeft n).unsigned = (a.unsigned * (2 ^ (n % w)) + a.unsigned / (2 ^ (w - (n % w)))) % (2 ^ w) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw_pos
  · simp [unsigned_width0 a, unsigned_width0 (a.rotateLeft n)]
  · simp [BitVec.unsigned, BitVec.toNat_rotateLeft, Nat.rotateLeft_nat_eq w a.toNat n hw_pos a.isLt]

@[grind_homo] theorem unsigned_rotateRight {w : Nat} (a : BitVec w) (n : Nat) :
  (a.rotateRight n).unsigned = (a.unsigned / (2 ^ (n % w)) + a.unsigned * (2 ^ (w - (n % w)))) % (2 ^ w) := by
  rcases Nat.eq_zero_or_pos w with rfl | hwpos; · simp [unsigned_width0]
  have hk : n % w ≤ w := Nat.le_of_lt (Nat.mod_lt _ hwpos)
  have b_lt_pow (A w k : Nat) (hA : A < 2^w) (hk : k ≤ w) : A / 2^k < 2^(w-k) := by
    have h_pow : 2^w = 2^k * 2^(w-k) := by rw [← Nat.pow_add]; congr 1; omega
    rw [h_pow] at hA; exact Nat.div_lt_of_lt_mul hA
  have Y_eq_shift (A w k : Nat) (hk : k ≤ w) : A * 2 ^ (w - k) % 2 ^ w = (A % 2 ^ k) * 2 ^ (w - k) := by
    rw [show 2^w = 2^k * 2^(w-k)
      by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_right]
  have h_rot (A w k : Nat) (hA : A < 2^w) (hkw : k ≤ w) : (A % 2^k) * 2^(w-k) + A / 2^k = (A / 2^k + A * 2^(w-k)) % 2^w := by
    have h_pow : 2^w = 2^k * 2^(w-k) := by rw [← Nat.pow_add]; congr 1; omega
    have h2 : A * 2^(w-k) = (2^k * (A / 2^k) + A % 2^k) * 2^(w-k) :=
      congrArg (· * 2^(w-k)) (Nat.div_add_mod A (2^k)).symm
    have h_RHS : A / 2^k + A * 2^(w-k) = A / 2^k + (A % 2^k) * 2^(w-k) + A / 2^k * 2^w := by
      rw [h2, Nat.add_mul, Nat.mul_comm (2^k), Nat.mul_assoc, ←h_pow]; omega
    rw [h_RHS, Nat.mul_comm _ (2^w),  Nat.add_mul_mod_self_left]
    have h_lt : A / 2^k + (A % 2^k) * 2^(w-k) < 2^w := by
      have h_Y : 1 + A % 2^k ≤ 2^k :=
        by have := Nat.mod_lt A (Nat.two_pow_pos k); omega
      have h_X : A / 2^k < 2^(w-k) := Nat.div_lt_of_lt_mul (
        by rw [← h_pow]; exact hA)
      calc A / 2^k + (A % 2^k) * 2^(w-k)
        _ < 2^(w-k) + (A % 2^k) * 2^(w-k) := by omega
        _ = (1 + A % 2^k) * 2^(w-k) := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ 2^k * 2^(w-k) := Nat.mul_le_mul_right _ h_Y
        _ = 2^w := h_pow.symm
    rw [Nat.mod_eq_of_lt h_lt, Nat.add_comm]
  have h_lor := Nat.shiftLeft_add_eq_or_of_lt (b_lt_pow a.toNat w (n % w) a.isLt hk) (a.toNat % 2^(n % w))
  rw [Nat.shiftLeft_eq] at h_lor
  dsimp only [unsigned]; rw [toNat_rotateRight,  Nat.shiftLeft_eq,  Nat.shiftRight_eq_div_pow, Y_eq_shift _ w (n % w) hk,  Nat.or_comm,  ← h_lor,  h_rot a.toNat w (n % w) a.isLt hk]; simp

@[grind_homo] theorem unsigned_ofBool (b : Bool) :
  (BitVec.ofBool b).unsigned = if b then 1 else 0 := by
  cases b <;> rfl

-- bits.signed_range'
@[grind_homo] theorem signed_range' {w : Nat} (x : BitVec w) (_ : 1 ≤ w) :
  -(2 ^ (w - 1)) ≤ x.signed ∧ x.signed < (2 ^ (w - 1)) := by
  dsimp only [signed]
  constructor
  · apply le_toInt
  · apply toInt_lt

-- bits.signed_range
@[grind_homo_pred] theorem signed_range {w : Nat} (x : BitVec w) :
  -(2 ^ w) ≤ 2 * x.signed ∧ 2 * x.signed < (2 ^ w) := by
  dsimp only [signed]
  constructor
  · apply le_two_mul_toInt
  · apply two_mul_toInt_lt


-- Zmod.signed_inj / Zmod.signed_inj_iff
@[grind_homo] theorem signed_inj_iff {w : Nat} {x y : BitVec w} :
  x = y ↔ x.signed = y.signed := by
  dsimp only [signed]; symm; apply toInt_inj

-- Zmod.signed_0_iff
@[grind_homo] theorem signed_zero_iff {w : Nat} {x : BitVec w} :
  x = 0#w ↔ x.unsigned = 0 := by
  dsimp only [unsigned]
  constructor
  · intro h; rw [h]; rw [toNat_zero]; rfl
  · intros h; apply eq_of_toNat_eq; rw [toNat_zero]; lia

-- Zmod.signed_opp / bits.signed_opp
@[grind_homo] theorem signed_neg_bmod {w : Nat} (x : BitVec w) :
  (-x).signed = (-x.signed).bmod (2 ^ w) := by
  dsimp only [signed]
  rw [toInt_neg]

-- Zmod.signed_add / bits.signed_add
@[grind_homo] theorem signed_add_bmod {w : Nat} (x y : BitVec w) :
  (x + y).signed = (x.signed + y.signed).bmod (2 ^ w) := by
  dsimp only [signed]
  rw [toInt_add]

@[grind_homo] theorem signed_cast {n m : Nat} (h : n = m) (a : BitVec n) :
  (BitVec.cast h a).signed = a.signed := by
  subst h; rfl

-- bits.signed_width0
@[grind_homo] theorem signed_width0 (a : BitVec 0) :
  a.signed = 0 := by
  dsimp only [signed]; rw [toInt_zero_length]

-- Zmod.signed_sub / bits.signed_sub
@[grind_homo] theorem signed_sub_bmod {w : Nat} (x y : BitVec w) :
  (x - y).signed = (x.signed - y.signed).bmod (2 ^ w) := by
  simp only [signed, toInt_sub]

-- Zmod.signed_srs / bits.signed_srs
@[grind_homo] theorem signed_sshiftRight_eq {w : Nat} (x : BitVec w) (n : Nat) :
  (x.sshiftRight n).signed = x.signed >>> n := by
  dsimp only [signed]; rw [toInt_sshiftRight]

-- Zmod.signed_mul / bits.signed_mul
@[grind_homo] theorem signed_mul_bmod {w : Nat} (x y : BitVec w) :
  (x * y).signed = (x.signed * y.signed).bmod (2 ^ w) := by
  dsimp only [signed]; rw [toInt_mul]

-- Zmod.signed_small_iff / bits.signed_small_iff
@[grind_homo] theorem signed_eq_unsigned_iff' {w : Nat} (x : BitVec w) :
  x.signed = x.unsigned ↔ 2 * x.unsigned < (2 ^ w) :=
    by exact signed_eq_unsigned_iff x

-- Zmod.signed_large / bits.signed_large
@[grind_homo] theorem signed_large {w : Nat} (x : BitVec w) (h : (2 ^ w) ≤ 2 * x.unsigned) :
  x.signed = x.unsigned - (2 ^ w) := by
  dsimp only [unsigned] at h ⊢; simp [BitVec.toInt_eq_toNat_cond]; lia

-- bits.signed_neg_iff / Zmod.signed_neg_iff
@[grind_homo] theorem signed_negative_iff {w : Nat} (x : BitVec w) :
  x.signed < 0 ↔ (2 ^ w) ≤ 2 * x.unsigned := by
  have := @unsigned_negative _ x
  have := @unsigned_nonnegative _ x
  grind only [usr le_two_mul_toInt, usr two_mul_toInt_lt]

-- bits.signed_pos_iff / Zmod.signed_pos_iff
@[grind_homo] theorem signed_positive_iff {w : Nat} (x : BitVec w) :
  0 < x.signed ↔ 0 < 2 * x.unsigned ∧ 2 * x.unsigned < (2 ^ w) := by
  have := x.unsigned_negative
  have := x.unsigned_nonnegative
  grind only [usr le_two_mul_toInt, usr two_mul_toInt_lt]

-- bits.signed_nonneg_iff / Zmod.signed_nonneg_iff
@[grind_homo] theorem signed_nonneg_iff {w : Nat} (x : BitVec w) :
  0 ≤ x.signed ↔ 2 * x.unsigned < (2 ^ w) := by
  have := @unsigned_negative _ x
  have := @unsigned_nonnegative _ x
  grind only [usr le_two_mul_toInt, usr two_mul_toInt_lt]

@[grind_homo] theorem signed_sdiv {w : Nat} (x y : BitVec w) :
  (x.sdiv y).signed = (x.signed.tdiv y.signed).bmod (2 ^ w) := by
  dsimp only [signed]; rw [toInt_sdiv]

@[grind_homo] theorem signed_srem {w : Nat} (x y : BitVec w) :
  (x.srem y).signed = x.signed.tmod y.signed := by
  dsimp only [signed]; rw [toInt_srem]

@[grind_homo] theorem signed_smod {w : Nat} (x y : BitVec w) :
  (x.smod y).signed = x.signed.fmod y.signed := by
  dsimp only [signed]; rw [toInt_smod]

@[grind_homo] theorem signed_pow_bmod {w : Nat} (x : BitVec w) (z : Nat) :
  (x.pow z).signed = (x.signed ^ z).bmod (2 ^ w) := by
  induction z <;> simp [*, BitVec.pow, signed_ofNat, Int.pow_succ, Int.mul_comm]

theorem ofNat_sub_two_pow {w : Nat} (y : BitVec w) : (↑y.toNat - ↑(2 ^ w) : Int) = Int.negSucc (2 ^ w - y.toNat - 1) := by
  rw [Int.negSucc_eq]
  have h1 : (↑y.toNat + ↑(2 ^ w - y.toNat - 1) + 1 : Int) = ↑(2 ^ w) :=
    congrArg (fun (x : Nat) => (x : Int)) (show y.toNat + (2 ^ w - y.toNat - 1) + 1 = 2 ^ w
      by omega)
  omega

theorem xor_and_not {w : Nat} (x y : BitVec w) : x ^^^ (x &&& ~~~y) = x &&& y := by
  ext i
  grind

theorem xor_not_not {w : Nat} (x y : BitVec w) : ~~~x ^^^ ~~~y = x ^^^ y := by
  ext i
  grind

theorem signed_eq_msb {w : Nat} (x : BitVec w) :
  x.signed = if x.msb then (x.toNat : Int) - 2^w else (x.toNat : Int) := by
  dsimp only [signed, BitVec.toInt]
  have h1 := x.isLt
  have h2 := BitVec.msb_eq_decide x
  cases w with
  | zero => simp_all
  | succ w =>
    have h3 : 2^(w+1) = 2 * 2^w := by rw [Nat.pow_succ, Nat.mul_comm]
    simp_all; split <;> split <;> simp_all <;> omega

@[grind_homo] theorem signed_and {w : Nat} (x y : BitVec w) : (x &&& y).signed = x.signed &&& y.signed := by
  rw [signed_eq_msb x, signed_eq_msb y, signed_eq_msb]
  have h_and : (x &&& y).msb = (x.msb && y.msb) := by simp [BitVec.msb]
  rw [h_and]
  cases hx : x.msb <;> cases hy : y.msb <;> simp
  · rfl
  · have h_not_y : 2 ^ w - y.toNat - 1 = (~~~y).toNat :=
      by rw [BitVec.toNat_not]; omega
    have h_eq : x.toNat ^^^ (x.toNat &&& (~~~y).toNat) = (x &&& y).toNat :=
      by rw [← BitVec.toNat_and, ← BitVec.toNat_xor, xor_and_not]
    rw [ofNat_sub_two_pow,   h_not_y,   Int.land_ofNat_negSucc,   h_eq,   ← BitVec.toNat_and]
  · have h_not_x : 2 ^ w - x.toNat - 1 = (~~~x).toNat :=
      by rw [BitVec.toNat_not]; omega
    have h_eq : y.toNat ^^^ ((~~~x).toNat &&& y.toNat) = (x &&& y).toNat :=
      by rw [← BitVec.toNat_and,  ← BitVec.toNat_xor, BitVec.and_comm _ y,  xor_and_not,  BitVec.and_comm y x]
    rw [ofNat_sub_two_pow,   h_not_x,   Int.land_negSucc_ofNat,   h_eq,   ← BitVec.toNat_and]
  · have h_not_x : 2 ^ w - x.toNat - 1 = (~~~x).toNat :=
      by rw [BitVec.toNat_not]; omega
    have h_not_y : 2 ^ w - y.toNat - 1 = (~~~y).toNat :=
      by rw [BitVec.toNat_not]; omega
    have h_not_xy : 2 ^ w - (x &&& y).toNat - 1 = (~~~(x &&& y)).toNat :=
      by rw [BitVec.toNat_not]; omega
    rw [ofNat_sub_two_pow,   ofNat_sub_two_pow y,   ← BitVec.toNat_and,   ofNat_sub_two_pow (x &&& y),   h_not_x,   h_not_y,   h_not_xy,   Int.land_negSucc_negSucc,   ← BitVec.toNat_or,   ← BitVec.not_and]

@[grind_homo] theorem signed_or {w : Nat} (x y : BitVec w) : (x ||| y).signed = x.signed ||| y.signed := by
  have h_not := fun (z : BitVec w) => show 2^w - z.toNat - 1 = (~~~z).toNat
    by rw [BitVec.toNat_not]; omega
  rw [signed_eq_msb x, signed_eq_msb y, signed_eq_msb]
  have h_or : (x ||| y).msb = (x.msb || y.msb) := by simp [BitVec.msb]
  rw [h_or]
  cases hx : x.msb <;> cases hy : y.msb <;> simp
  · rfl
  · rw [ofNat_sub_two_pow,   ← BitVec.toNat_or,   ofNat_sub_two_pow (x ||| y),   h_not y,   h_not (x ||| y),   Int.lor_ofNat_negSucc,   ← toNat_and,   ← toNat_xor]
    have h_eq : ~~~y ^^^ (x &&& ~~~y) = ~~~(x ||| y) := by
      ext i
      grind
    rw [h_eq]
  · rw [ofNat_sub_two_pow,   ← BitVec.toNat_or,   ofNat_sub_two_pow (x ||| y),   h_not x,   h_not (x ||| y),   Int.lor_negSucc_ofNat,   ← toNat_and,   ← toNat_xor]
    have h_eq : ~~~x ^^^ (~~~x &&& y) = ~~~(x ||| y) := by
      ext i
      grind
    rw [h_eq]
  · rw [ofNat_sub_two_pow,   ofNat_sub_two_pow y,   ← BitVec.toNat_or,   ofNat_sub_two_pow (x ||| y),   h_not x,   h_not y,   h_not (x ||| y),   Int.lor_negSucc_negSucc,   ← toNat_and,   ← BitVec.not_or]

@[grind_homo] theorem signed_xor {w : Nat} (x y : BitVec w) : (x ^^^ y).signed = x.signed ^^^ y.signed := by
  have h_not := fun (z : BitVec w) => show 2^w - z.toNat - 1 = (~~~z).toNat
    by rw [BitVec.toNat_not]; omega
  rw [signed_eq_msb x, signed_eq_msb y, signed_eq_msb]
  have h_xor : (x ^^^ y).msb = xor x.msb y.msb := by simp [BitVec.msb]
  rw [h_xor]
  cases hx : x.msb <;> cases hy : y.msb <;> simp
  · rfl
  · rw [ofNat_sub_two_pow]
    change (↑(x ^^^ y).toNat - 2 ^ w : Int) = ↑x.toNat ^^^ Int.negSucc (2 ^ w - y.toNat - 1)
    rw [ofNat_sub_two_pow]
    rw [h_not y, h_not,   Int.lxor_ofNat_negSucc,   ← toNat_xor,   BitVec.not_xor_right]
  · rw [ofNat_sub_two_pow]
    change (↑(x ^^^ y).toNat - 2 ^ w : Int) = Int.negSucc (2 ^ w - x.toNat - 1) ^^^ ↑y.toNat
    rw [ofNat_sub_two_pow]
    rw [h_not x, h_not,   Int.lxor_negSucc_ofNat,   ← toNat_xor,   BitVec.not_xor_left]
  · rw [ofNat_sub_two_pow,   ofNat_sub_two_pow y]
    rw [h_not,   h_not y,   Int.lxor_negSucc_negSucc,   ← toNat_xor (~~~x) (~~~y),   xor_not_not,   toNat_xor]

theorem toNat_add_cases {w : Nat} (x y : BitVec w) :
  (x + y).toNat = x.toNat + y.toNat ∨ (x + y).toNat = x.toNat + y.toNat - 2^w := by
  have hx := x.isLt; have hy := y.isLt
  rw [toNat_add, Nat.add_mod_eq_sub, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  split <;> omega

theorem unsigned_add_cases {w : Nat} (x y : BitVec w) :
  (x + y).unsigned = x.unsigned + y.unsigned ∨ (x + y).unsigned = x.unsigned + y.unsigned - (2^w : Int) := by
  change ((x + y).toNat : Int) = (x.toNat : Int) + (y.toNat : Int) ∨ ((x + y).toNat : Int) = (x.toNat : Int) + (y.toNat : Int) - (2^w : Int)
  have hx := x.isLt; have hy := y.isLt
  by_cases hle : 2^w ≤ x.toNat + y.toNat
  · right
    have h1 : (x + y).toNat = x.toNat + y.toNat - 2^w := by
      rw [BitVec.toNat_add, Nat.add_mod_eq_sub, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
      split <;> omega
    rw [h1, Int.ofNat_sub hle]
    push_cast
    rfl
  · left
    have h1 : (x + y).toNat = x.toNat + y.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    push_cast
    rfl

@[grind_homo] theorem signed_not {w : Nat} (x : BitVec w) :
  (~~~x).signed = (~~~x.signed).bmod (2 ^ w) := by
  simp only [signed]
  rw [toInt_not, Int.lnot_def]
  have : 0 < 2 ^ w := Nat.two_pow_pos w
  have h_eq : (2 ^ w - 1 - (x.toNat : Int)) % (2 ^ w : Nat) = (-x.toInt - 1) % (2 ^ w : Nat) := by
    have h_arith : (2 ^ w - 1 - (x.toNat : Int)) = ↑(2 ^ w) + (-x.toNat - 1) := by omega
    rw [h_arith]
    rw [Int.add_emod]
    have h_self : ((2 ^ w : Int) % (2 ^ w : Nat)) = 0 := by exact Int.emod_self
    rw [h_self, Int.zero_add, Int.emod_emod]
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · rfl
    · have h_helper (A C : Int) : (-(A - C) - 1) % C = (-A - 1) % C := by
        have h_arith : -(A - C) - 1 = C + (-A - 1) := by omega
        rw [h_arith, Int.add_emod]
        have h_self : C % C = 0 := by exact Int.emod_self
        rw [h_self, Int.zero_add, Int.emod_emod]
      exact (h_helper ↑x.toNat ↑(2 ^ w)).symm
  rw [← Int.emod_bmod (2 ^ w - 1 - (x.toNat : Int)) (2 ^ w)]
  rw [h_eq]
  rw [Int.emod_bmod]

theorem bmod_mul_mod_l_helper (x : Int) (n : Int) (y : Int) (hn : 0 ≤ n) :
  (x.bmod n.natAbs * y) % n = (x * y) % n := by
  rw [← Int.mod_mul_mod_l]
  have h_nat : (n.natAbs : Int) = n := Int.natAbs_of_nonneg hn
  rw [← h_nat]
  dsimp
  rw [Int.bmod_emod]
  rw [h_nat, Int.mod_mul_mod_l]

@[grind_homo] theorem signed_shiftLeft {w : Nat} (x : BitVec w) (n : Nat) :
  (x <<< n).signed = (x.signed <<< n).bmod (2 ^ w) := by
  dsimp only [signed]
  rw [toInt_shiftLeft, Int.shiftLeft_eq, Nat.shiftLeft_eq, BitVec.toInt_eq_toNat_bmod]
  have bmod_eq_of_emod_eq {x y : Int} {m : Nat} (h : x % (m : Int) = y % (m : Int)) : x.bmod m = y.bmod m := by
    dsimp [Int.bmod]
    rw [h]
  apply bmod_eq_of_emod_eq
  rw [Int.natCast_mul, Int.natCast_pow]
  have h_two : (Nat.cast 2 : Int) = 2 := by rfl
  rw [h_two]
  have h_div : (Nat.cast (2 ^ w) : Int) = (2 ^ w : Int) := by rfl
  rw [h_div]

  have h_pos : (0 : Int) ≤ (2 ^ w : Int) := Int.natCast_nonneg (2 ^ w)
  rw [← bmod_mul_mod_l_helper (x := ↑x.toNat) (n := 2 ^ w) (y := 2 ^ n) h_pos]
  have h_abs : (2 ^ w : Int).natAbs = 2 ^ w := by rfl
  rw [h_abs]

@[grind_homo] theorem signed_zeroExtend {w : Nat} (x : BitVec w) (v : Nat) :
  (x.zeroExtend v).signed = x.unsigned.bmod (2 ^ v) := by
  dsimp only [signed, unsigned, zeroExtend]
  rw [toInt_setWidth]
  rfl

@[grind_homo] theorem signed_signExtend {w : Nat} (x : BitVec w) (v : Nat) :
  (x.signExtend v).signed = x.signed.bmod (2 ^ min v w) := by
  dsimp only [signed]
  rw [toInt_signExtend]

@[grind_homo] theorem unsigned_signExtend {w : Nat} (x : BitVec w) (v : Nat) :
    (x.signExtend v).unsigned = (x.zeroExtend v).unsigned + (if x.msb then ↑(2^v - 2^w : Nat) else 0) := by
  dsimp [unsigned, zeroExtend]
  rw [toNat_signExtend x]
  split <;> push_cast <;> rfl

@[simp, grind_homo] theorem toInt_lt_zero_iff_msb {w : Nat} (x : BitVec w) : x.toInt < 0 ↔ x.msb = true := by
  rw [toInt_eq_toNat_cond]
  split
  · have hmsb : x.msb = false := msb_eq_false_iff_two_mul_lt.mpr (by assumption)
    rw [hmsb]
    simp
  · have hmsb : x.msb = true := by
      have h1 : ¬ (x.msb = false) := by rwa [msb_eq_false_iff_two_mul_lt]
      cases h2 : x.msb
      · contradiction
      · rfl
    rw [hmsb]
    simp
    have hlt := x.isLt
    have hlt_int : (x.toNat : Int) < (2^w : Int) := by exact_mod_cast hlt
    omega


@[grind_homo] theorem sshiftRight_ge_w_minus_1 {w : Nat} (v : BitVec w) (n : Nat) (h : w - 1 ≤ n := by omega) (hw : w ≠ 0 := by omega) :
    v.sshiftRight n = if v.msb then -1 else 0 := by
  ext i
  simp only [getElem_sshiftRight]
  split <;> rename_i h1
  · have hi0 : i = 0 := by omega
    subst hi0
    simp only [Nat.add_zero]
    have hn : n = w - 1 := by omega
    subst hn
    have hmsb : v[w - 1] = v.msb := by
      unfold BitVec.msb
      rw [getMsbD_eq_getLsbD]
      simp only [Nat.sub_zero]
      rw [getLsbD_eq_getElem (by omega)]
      have : 0 < w := by omega
      simp [this]
    rw [hmsb]
    split <;> rename_i h2 <;> simp [h2, neg_one_eq_allOnes]
  · split <;> rename_i h2 <;> simp [h2, neg_one_eq_allOnes]


theorem ushiftRight_w_minus_1 {w : Nat} (x : BitVec w) (hw : w > 0) :
    x >>> (w - 1) = if x.msb then 1#w else 0#w := by
  ext i hi
  grind


theorem xor_eq_bne (a b : Bool) : xor a b = (a != b) := by
  cases a <;> cases b <;> rfl

theorem drop_eq_truncate_ushiftRight {w : Nat} (n : Nat) (a : BitVec w) :
    a.drop n = (a >>> n).truncate (w - n) := by
  apply BitVec.eq_of_toNat_eq
  simp [drop, extractLsb'_toNat]

@[grind_homo] theorem unsigned_drop {w : Nat} (n : Nat) (a : BitVec w) :
    (a.drop n).unsigned = a.unsigned / 2 ^ n := by
  by_cases h : n ≤ w
  · rw [drop_eq_truncate_ushiftRight]
    rw [unsigned_truncate_small]
    · exact unsigned_ushiftRight a n
    · rw [unsigned_ushiftRight]
      have h1 : a.toNat < 2 ^ n * 2 ^ (w - n) := by
        rw [← Nat.pow_add]
        have : n + (w - n) = w := by omega
        rw [this]
        exact a.isLt
      have h2 : a.toNat / 2 ^ n < 2 ^ (w - n) := Nat.div_lt_of_lt_mul h1
      have h3 := Int.ofNat_lt.mpr h2
      push_cast at h3
      exact h3
  · rw [drop_eq_truncate_ushiftRight]
    cases h_sub : w - n
    · have h0 : (truncate 0 (a >>> n)).unsigned = 0 := unsigned_width0 _
      rw [h0]
      have h4 : (a.toNat : Int) / 2 ^ n = 0 := by
        have h5 : a.toNat / 2 ^ n = 0 := by
          rw [Nat.div_eq_of_lt]
          have hlt := a.isLt
          have hpow : 2^w ≤ 2^n := Nat.pow_le_pow_right Nat.two_pos (by omega)
          omega
        exact_mod_cast h5
      exact h4.symm
    · have : w - n = 0 := by omega
      rw [this] at h_sub
      contradiction

@[grind_homo] theorem unsigned_take {w : Nat} (n : Nat) (a : BitVec w) :
    (a.take n).unsigned = a.unsigned % 2 ^ n := by
  dsimp [take]; rw [unsigned_extractLsb']; simp

@[grind_homo] theorem unsigned_replaceLow {w n} (old : BitVec w) (new : BitVec n) :
    (old.replaceLow new).unsigned = (((old.drop n) ++ new).setWidth w).unsigned := by
  rfl

@[grind_homo] theorem unsigned_replace {w1} (old : BitVec w1) (i : Nat) {w2} (new : BitVec w2) :
    (old.replace i new).unsigned = ((old.drop (i + w2) ++ new ++ old.take i).setWidth w1).unsigned := by
  rfl

@[grind_homo] theorem testBit_toInt {w : Nat} (hw : 0 < w) (y : BitVec w) (i : Nat) :
  y.toInt.testBit i = if i < w then y.getLsbD i else y.getLsbD (w - 1) := by
  by_cases hi : i < w
  · -- Case i < w
    simp [hi]
    rw [BitVec.toInt_eq_msb_cond]
    cases h_msb : y.msb
    · -- Case y.msb = false
      simp
      change y.toNat.testBit i = y.toNat.testBit i
      rfl
    · -- Case y.msb = true
      simp
      have h_neg : (y.toNat : Int) - 2^w = Int.negSucc (2^w - 1 - y.toNat) := by
        have h_lt : (y.toNat : Int) < (2^w : Int) := by exact_mod_cast y.toNat_range
        rw [Int.negSucc_eq]
        have h1 : y.toNat ≤ 2^w - 1 := by omega
        have h2 : 1 ≤ 2^w := Nat.succ_le_of_lt (Nat.two_pow_pos w)
        have h_sub1 : ((2^w - 1 - y.toNat : Nat) : Int) = ((2^w - 1 : Nat) : Int) - (y.toNat : Int) := Int.ofNat_sub h1
        have h_sub2 : ((2^w - 1 : Nat) : Int) = (2^w : Int) - 1 := Int.ofNat_sub h2
        rw [h_sub1, h_sub2]
        omega
      rw [h_neg]
      simp [Int.testBit]
      have h_sub : 2^w - 1 - y.toNat = (~~~y).toNat := by
        rw [BitVec.toNat_not]
      rw [h_sub]
      change (~~~y).toNat.testBit i = ! y.toNat.testBit i
      have h_not : (~~~y).toNat.testBit i = ! (y.toNat.testBit i) := by
        have h_get1 : (~~~y).toNat.testBit i = (~~~y)[i] := by
          rw [getElem_eq_testBit_toNat _ _ hi]
        have h_get2 : y.toNat.testBit i = y[i] := by
          rw [getElem_eq_testBit_toNat _ _ hi]
        rw [h_get1, h_get2, BitVec.getElem_not hi]
      rw [h_not]
  · -- Case i ≥ w
    have h_rhs : (if i < w then y.getLsbD i else y.getLsbD (w - 1)) = y.getLsbD (w - 1) := by
      simp [hi]
    rw [h_rhs]
    rw [BitVec.toInt_eq_msb_cond]
    have h_msb_eq : y.getLsbD (w - 1) = y.msb := by
      dsimp [BitVec.msb, getMsbD]
      simp [hw]
    rw [h_msb_eq]
    cases h_msb : y.msb
    · -- Case y.msb = false
      simp
      simp [Int.testBit]
      apply Nat.testBit_lt_two_pow
      have : y.toNat < 2^w := y.toNat_range
      have : 2^w ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · -- Case y.msb = true
      simp
      have h_neg : (y.toNat : Int) - 2^w = Int.negSucc (2^w - 1 - y.toNat) := by
        have h_lt : (y.toNat : Int) < (2^w : Int) := by exact_mod_cast y.toNat_range
        rw [Int.negSucc_eq]
        have h1 : y.toNat ≤ 2^w - 1 := by omega
        have h2 : 1 ≤ 2^w := Nat.succ_le_of_lt (Nat.two_pow_pos w)
        have h_sub1 : ((2^w - 1 - y.toNat : Nat) : Int) = ((2^w - 1 : Nat) : Int) - (y.toNat : Int) := Int.ofNat_sub h1
        have h_sub2 : ((2^w - 1 : Nat) : Int) = (2^w : Int) - 1 := Int.ofNat_sub h2
        rw [h_sub1, h_sub2]
        omega
      rw [h_neg]
      simp [Int.testBit]
      apply Nat.testBit_lt_two_pow
      have : 2^w - 1 - y.toNat < 2^w := by omega
      have : 2^w ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      omega

attribute [grind_homo] BitVec.xor_self BitVec.not_not BitVec.shiftLeft_zero BitVec.allOnes_and BitVec.and_allOnes BitVec.not_zero


@[grind_homo] theorem slt_simp' {w : Nat} (a b : BitVec w) : (a.slt b = true) = (a.toInt < b.toInt) := by
  exact propext slt_iff_toInt_lt

@[grind_homo] theorem sle_simp' {w : Nat} (a b : BitVec w) : (a.sle b = true) = (a.toInt ≤ b.toInt) := by
  exact propext sle_iff_toInt_le

@[grind_homo_pred] theorem slt_toInt_pred {w : Nat} (a b : BitVec w) : (a.slt b = true) ↔ a.toInt < b.toInt := by
  exact slt_iff_toInt_lt

@[grind_homo_pred] theorem sle_toInt_pred {w : Nat} (a b : BitVec w) : (a.sle b = true) ↔ a.toInt ≤ b.toInt := by
  exact sle_iff_toInt_le

@[grind_homo] theorem toInt_ofNat_eval {w : Nat} (n : Nat) :
    (BitVec.ofNat w n).toInt = (n : Int).bmod (2^w) := by
  exact BitVec.signed_ofNat w n

theorem pow_two_toNat (w n : Nat) : (2^n : BitVec w).toNat = (2^n : Nat) % 2^w := by
  change ((2 : BitVec w).pow n).toNat = 2^n % 2^w
  apply Int.ofNat_inj.mp
  rw [toNat_eq_unsigned, unsigned_pow, unsigned_instOfNat]
  push_cast
  induction n <;> simp_all [Int.pow_succ, Int.mul_emod, Int.mul_comm]

theorem pow_two_eq_ofNat (w n : Nat) : (2 : BitVec w) ^ n = BitVec.ofNat w (2^n) := by
  apply BitVec.eq_of_toNat_eq
  rw [pow_two_toNat, toNat_ofNat]

@[grind_homo] theorem hShiftLeft_eq {w : Nat} (x : BitVec w) (n : Nat) : x <<< n = x * 2^n := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_shiftLeft, toNat_mul, Nat.shiftLeft_eq, pow_two_toNat]
  calc (x.toNat * 2^n) % 2^w
    _ = (x.toNat % 2^w * (2^n % 2^w)) % 2^w := by rw [Nat.mul_mod]
    _ = (x.toNat % 2^w * ((2^n % 2^w) % 2^w)) % 2^w := by rw [Nat.mod_mod]
    _ = (x.toNat * (2^n % 2^w)) % 2^w := by rw [← Nat.mul_mod]

end BitVec

