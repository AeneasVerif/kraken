prelude
import Init.Data.Fin.Basic
import Init.Data.Fin.Fold
import Init.Data.Fin.Log2
import KrakenStdlibCandidates.Init.GrindInternHooks
import Lean


/-!
# Grind homomorphism lemmas for Fin.
-/

-- Annotate existing standard library Fin lemmas as grind_homo
attribute [grind_homo] Fin.val_add
attribute [grind_homo] Fin.val_mul
attribute [grind_homo] Fin.val_sub
attribute [grind_homo] Fin.val_zero
attribute [grind_homo] Fin.val_neg'
attribute [grind_homo] Fin.div_val
attribute [grind_homo] Fin.val_mod
attribute [grind_homo] Fin.val_succ
attribute [grind_homo] Fin.and_val
attribute [grind_homo] Fin.or_val
attribute [grind_homo] Fin.xor_val

namespace Fin

variable {n : Nat}

theorem val_range (x : Fin n) : 0 ≤ x.val ∧ x.val < n := by
  have := x.isLt
  constructor
  · exact Nat.zero_le _
  · exact this

@[grind_homo_pred] theorem val_range_homo (n : Nat) (x : Fin n) :
  0 ≤ x.val ∧ x.val < n := val_range x

@[grind_homo_pred] theorem val_le_iff (a b : Fin n) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl
@[grind_homo_pred] theorem val_lt_iff (a b : Fin n) : a < b ↔ a.val < b.val := Iff.rfl
@[grind_homo_pred] theorem val_eq_iff (a b : Fin n) : a = b ↔ a.val = b.val := Fin.ext_iff
theorem val_injective' {n : Nat} : Function.Injective (Fin.val : Fin n → Nat) := fun _ _ => Fin.ext
attribute [grind inj] val_injective'



@[grind_homo] theorem val_ite (c : Prop) [Decidable c] (x y : Fin n) :
    (if c then x else y).val = if c then x.val else y.val := by
  split <;> rfl

@[grind_homo] theorem val_zero_iff [NeZero n] {x : Fin n} : x = 0 ↔ x.val = 0 := by
  grind

@[grind_homo] theorem val_ne_zero_of_ne_zero [NeZero n] {x : Fin n} (h : x ≠ 0) : x.val ≠ 0 := by
  grind

@[grind_homo] theorem val_width0 (x : Fin 0) : x.val = 0 := by
  nomatch x

@[grind_homo] theorem val_ofNat' [NeZero n] (i : Nat) : ((OfNat.ofNat i : Fin n)).val = i % n := rfl


-- log2 and intCast homomorphisms
@[grind_homo] theorem val_log2 (x : Fin n) : (x.log2).val = Nat.log2 x.val := rfl

theorem sub_mod_self (z y : Nat) (hz : z < y) : (y - z) % y = if z = 0 then 0 else y - z := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [Nat.mod_self]
  · rw [Nat.mod_eq_of_lt]
    · rw [if_neg hz0]
    · omega

theorem toNat_natCast_mod_natCast (x y : Nat) : ((x : Int) % (y : Int)).toNat = x % y := by
  omega

theorem toNat_neg_natCast_mod_natCast (x y : Nat) (hy : y ≠ 0) : (y - x % y) % y = ((- (x : Int)) % (y : Int)).toNat := by
  have hz : x % y < y := Nat.mod_lt x (Nat.pos_of_ne_zero hy)
  rw [sub_mod_self (x % y) y hz]
  have h_int : ((- (x : Int)) % (y : Int)) = if x % y = 0 then (0 : Int) else ((y - x % y : Nat) : Int) := by
    simp only [Int.neg_emod, Int.dvd_iff_emod_eq_zero]
    simp
    omega
  rw [h_int]
  split
  · rfl
  · rfl

open Fin.IntCast in
@[grind_homo] theorem val_intCast [NeZero n] (i : Int) : ((i : Fin n)).val = (i % n).toNat := by
  change (Fin.intCast i).val = (i % (n : Int)).toNat
  rw [Fin.intCast]
  split
  · rename_i h
    simp
    have : i = (i.natAbs : Int) := by omega
    rw [this]
    exact toNat_natCast_mod_natCast i.natAbs n
  · rename_i h
    rw [Fin.val_neg']
    simp
    have : i = - (i.natAbs : Int) := by omega
    rw [this]
    simp
    exact toNat_neg_natCast_mod_natCast i.natAbs n (NeZero.ne n)

def lnot (a : Fin n) : Fin n :=
  ⟨n - 1 - a.val, by have := a.isLt; omega⟩

instance : Complement (Fin n) where
  complement := lnot

attribute [grind_homo] Fin.shiftLeft_val
attribute [grind_homo] Fin.shiftRight_val
@[grind_homo] theorem val_lnot (a : Fin n) : (~~~a).val = n - 1 - a.val := rfl



end Fin
