import Std.Tactic.BVDecide

/-!
# Arithmetic flag computation

x86 and AArch64 both derive carry/borrow and signed-overflow flags from the
same three quantities. The natural (arithmetic) specification reads as:

    cf := v.unsigned != a.unsigned + b.unsigned
    of := v.signed   != a.signed   + b.signed

Here we define the same flags in `BitVec` terms. The idea is to widen by one bit
and look at the carry position, or compare sign bits. The `BitVec` forms are what
the semantics evaluate. The `_spec` theorems are provided for arithmetic reasoning
that is more natural over `Int`.

TODO: `bv_decide` does not reduce `BitVec.carry` and abstracts it as an
opaque variable. We use `setWidth`/`msb` instead which are recognized.

TODO: `bv_decide` does not reduce `Bool.toNat` and  abstracts it as an
opaque variable. We use `ofBool`/`setWidth` instead for a carry input.
-/

namespace Kraken.Flags

/-- Unsigned carry out of `a + b + c`: widen by one bit and read the top bit. -/
def addCarry {w} (a b : BitVec w) (c : Bool) : Bool :=
  (a.setWidth (w + 1) + b.setWidth (w + 1) + (BitVec.ofBool c).setWidth (w + 1)).msb

/-- The carry-in as a bitvector. -/
abbrev carryBit (w : Nat) (c : Bool) : BitVec w := (BitVec.ofBool c).setWidth w

theorem carryBit_eq_ofNat (w : Nat) (c : Bool) :
    carryBit w c = BitVec.ofNat w c.toNat := by
  cases c <;> cases w <;> simp [carryBit] <;> rfl

/-- Signed overflow of `a + b + c`. -/
def addOverflow {w} (a b : BitVec w) (c : Bool) : Bool :=
  let v := a + b + carryBit w c
  (a.msb == b.msb) && (v.msb != a.msb)

/-- Unsigned borrow out of `b - a - c`. -/
def subBorrow {w} (b a : BitVec w) (c : Bool) : Bool :=
  BitVec.ult (b.setWidth (w + 1)) (a.setWidth (w + 1) + (BitVec.ofBool c).setWidth (w + 1))

/-- Signed overflow of `b - a - c`. -/
def subOverflow {w} (b a : BitVec w) (c : Bool) : Bool :=
  let v := b - a - carryBit w c
  (b.msb != a.msb) && (v.msb != b.msb)

private theorem pow_succ_eq {w : Nat} : 2 ^ (w + 1) = 2 * 2 ^ w := by
  rw [Nat.pow_succ]; omega

private theorem pow_eq_two_mul {w : Nat} (hw : 0 < w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  cases w with
  | zero => omega
  | succ n => simp only [Nat.add_sub_cancel, Nat.pow_succ]; omega

private theorem toNat_ofBool_setWidth {w : Nat} (c : Bool) :
    ((BitVec.ofBool c).setWidth (w + 1)).toNat = c.toNat := by
  cases c <;> simp

private theorem toNat_setWidth_succ {w : Nat} (x : BitVec w) :
    (x.setWidth (w + 1)).toNat = x.toNat := by
  have := x.isLt
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (show x.toNat < 2 ^ (w + 1) by rw [pow_succ_eq]; omega)]

private theorem toNat_widened_add {w} (a b : BitVec w) (c : Bool) :
    (a.setWidth (w+1) + b.setWidth (w+1) + (BitVec.ofBool c).setWidth (w+1)).toNat
      = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := pow_succ_eq
  have hct : c.toNat ≤ 1 := by cases c <;> simp
  rw [BitVec.toNat_add, BitVec.toNat_add, toNat_setWidth_succ, toNat_setWidth_succ,
    toNat_ofBool_setWidth,
    Nat.mod_eq_of_lt (show a.toNat + b.toNat < 2 ^ (w+1) by omega),
    Nat.mod_eq_of_lt (show a.toNat + b.toNat + c.toNat < 2 ^ (w+1) by omega)]

theorem addCarry_eq {w} (a b : BitVec w) (c : Bool) :
    addCarry a b c = decide (a.toNat + b.toNat + c.toNat ≥ 2 ^ w) := by
  rw [addCarry, BitVec.msb_eq_decide, toNat_widened_add]
  simp

theorem addCarry_spec {w} (hw : 0 < w) (a b : BitVec w) (c : Bool) :
    addCarry a b c
      = ((((a + b + BitVec.ofNat w c.toNat).toNat : Int))
          != (a.toNat : Int) + (b.toNat : Int) + (c.toNat : Int)) := by
  have hpow : 1 < 2 ^ w := Nat.one_lt_two_pow_iff.mpr (by omega)
  have hct : c.toNat < 2 ^ w := by cases c <;> simp <;> omega
  have ha := a.isLt
  have hb := b.isLt
  have hc : (BitVec.ofNat w c.toNat).toNat = c.toNat := by simp [Nat.mod_eq_of_lt hct]
  have hv : (a + b + BitVec.ofNat w c.toNat).toNat
      = (a.toNat + b.toNat + c.toNat) % 2 ^ w := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hc, Nat.mod_add_mod]
  rw [addCarry_eq, Bool.eq_iff_iff]
  simp only [hv, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases h : a.toNat + b.toNat + c.toNat < 2 ^ w
  · rw [Nat.mod_eq_of_lt h]; omega
  · have := Nat.mod_lt (a.toNat + b.toNat + c.toNat) (show 0 < 2 ^ w by omega)
    omega

theorem addOverflow_spec {w} (hw : 0 < w) (a b : BitVec w) (c : Bool) :
    addOverflow a b c
      = (((a + b + BitVec.ofNat w c.toNat).toInt)
          != a.toInt + b.toInt + (c.toNat : Int)) := by
  have h1 : 1 < 2 ^ w := Nat.one_lt_two_pow_iff.mpr (by omega)
  have ha := a.isLt
  have hb := b.isLt
  have hct : c.toNat ≤ 1 := by cases c <;> simp
  have hcw : (BitVec.ofNat w c.toNat).toNat = c.toNat := by
    simp [Nat.mod_eq_of_lt (show c.toNat < 2 ^ w by omega)]
  have hv : (a + b + BitVec.ofNat w c.toNat).toNat
      = (a.toNat + b.toNat + c.toNat) % 2 ^ w := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hcw, Nat.mod_add_mod]
  have hvc : (a + b + BitVec.ofNat w c.toNat).toNat = a.toNat + b.toNat + c.toNat
      ∨ (a + b + BitVec.ofNat w c.toNat).toNat + 2 ^ w = a.toNat + b.toNat + c.toNat := by
    rw [hv]
    rcases Nat.lt_or_ge (a.toNat + b.toNat + c.toNat) (2 ^ w) with h | h
    · exact Or.inl (Nat.mod_eq_of_lt h)
    · exact Or.inr (by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega)
  have hvlt := (a + b + BitVec.ofNat w c.toNat).isLt
  have hNe := pow_eq_two_mul hw
  clear hv hcw
  have kA : a.msb = false ↔ 2 * a.toNat < 2 ^ w := BitVec.msb_eq_false_iff_two_mul_lt
  have kB : b.msb = false ↔ 2 * b.toNat < 2 ^ w := BitVec.msb_eq_false_iff_two_mul_lt
  have kV : (a + b + BitVec.ofNat w c.toNat).msb = false
      ↔ 2 * (a + b + BitVec.ofNat w c.toNat).toNat < 2 ^ w :=
    BitVec.msb_eq_false_iff_two_mul_lt
  rw [addOverflow, carryBit_eq_ofNat, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, BitVec.toInt_eq_msb_cond]
  rcases hvc with hvc | hvc <;>
    cases hA' : a.msb <;> cases hB' : b.msb <;>
    cases hV' : (a + b + BitVec.ofNat w c.toNat).msb <;>
    simp only [hA', hB', hV', reduceIte, and_true, and_false, true_iff, false_iff,
      Decidable.not_not, Bool.true_eq_false, Bool.false_eq_true,
      not_true_eq_false, not_false_eq_true] at kA kB kV ⊢ <;>
    omega

private theorem toNat_widened_add2 {w} (a : BitVec w) (c : Bool) :
    (a.setWidth (w+1) + (BitVec.ofBool c).setWidth (w+1)).toNat = a.toNat + c.toNat := by
  have ha := a.isLt
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := pow_succ_eq
  have hct : c.toNat ≤ 1 := by cases c <;> simp
  rw [BitVec.toNat_add, toNat_setWidth_succ, toNat_ofBool_setWidth,
    Nat.mod_eq_of_lt (by omega)]

private theorem sub_toNat_cases {w} (hw : 0 < w) (b a : BitVec w) (c : Bool) :
    (b - a - BitVec.ofNat w c.toNat).toNat + a.toNat + c.toNat = b.toNat
      ∨ (b - a - BitVec.ofNat w c.toNat).toNat + a.toNat + c.toNat = b.toNat + 2 ^ w := by
  have hpow : 1 < 2 ^ w := Nat.one_lt_two_pow_iff.mpr (by omega)
  have ha := a.isLt
  have hb := b.isLt
  have hct : c.toNat ≤ 1 := by cases c <;> simp
  have hc : (BitVec.ofNat w c.toNat).toNat = c.toNat := by
    simp [Nat.mod_eq_of_lt (show c.toNat < 2 ^ w by omega)]
  have h : (b - a - BitVec.ofNat w c.toNat).toNat
      = ((2 ^ w - c.toNat) + ((2 ^ w - a.toNat) + b.toNat) % 2 ^ w) % 2 ^ w := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub, hc]
  rw [h]
  by_cases hba : b.toNat < a.toNat
  · rw [Nat.mod_eq_of_lt (show (2 ^ w - a.toNat) + b.toNat < 2 ^ w by omega)]
    by_cases hcc : 2 ^ w - a.toNat + b.toNat < c.toNat
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_sub_mod (show 2 ^ w ≤ (2 ^ w - a.toNat) + b.toNat by omega),
      Nat.mod_eq_of_lt (show (2 ^ w - a.toNat) + b.toNat - 2 ^ w < 2 ^ w by omega)]
    by_cases hcc : b.toNat - a.toNat < c.toNat
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem subBorrow_eq {w} (b a : BitVec w) (c : Bool) :
    subBorrow b a c = decide (b.toNat < a.toNat + c.toNat) := by
  rw [subBorrow, BitVec.ult, toNat_setWidth_succ, toNat_widened_add2]

theorem subBorrow_spec {w} (hw : 0 < w) (b a : BitVec w) (c : Bool) :
    subBorrow b a c
      = ((((b - a - BitVec.ofNat w c.toNat).toNat : Int))
          != (b.toNat : Int) - (a.toNat : Int) - (c.toNat : Int)) := by
  have hpow : 1 < 2 ^ w := Nat.one_lt_two_pow_iff.mpr (by omega)
  have hct : c.toNat < 2 ^ w := by cases c <;> simp <;> omega
  have ha := a.isLt
  have hb := b.isLt
  have hvlt := (b - a - BitVec.ofNat w c.toNat).isLt
  have hvc : (b - a - BitVec.ofNat w c.toNat).toNat + a.toNat + c.toNat = b.toNat
      ∨ (b - a - BitVec.ofNat w c.toNat).toNat + a.toNat + c.toNat = b.toNat + 2 ^ w :=
    sub_toNat_cases hw b a c
  rw [subBorrow_eq, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, bne_iff_ne, ne_eq]
  omega

theorem subOverflow_spec {w} (hw : 0 < w) (b a : BitVec w) (c : Bool) :
    subOverflow b a c
      = (((b - a - BitVec.ofNat w c.toNat).toInt)
          != b.toInt - a.toInt - (c.toNat : Int)) := by
  have h1 : 1 < 2 ^ w := Nat.one_lt_two_pow_iff.mpr (by omega)
  have ha := a.isLt
  have hb := b.isLt
  have hct : c.toNat ≤ 1 := by cases c <;> simp
  have hvlt := (b - a - BitVec.ofNat w c.toNat).isLt
  have hvc := sub_toNat_cases hw b a c
  have hNe := pow_eq_two_mul hw
  have kA : a.msb = false ↔ 2 * a.toNat < 2 ^ w := BitVec.msb_eq_false_iff_two_mul_lt
  have kB : b.msb = false ↔ 2 * b.toNat < 2 ^ w := BitVec.msb_eq_false_iff_two_mul_lt
  have kV : (b - a - BitVec.ofNat w c.toNat).msb = false
      ↔ 2 * (b - a - BitVec.ofNat w c.toNat).toNat < 2 ^ w :=
    BitVec.msb_eq_false_iff_two_mul_lt
  rw [subOverflow, carryBit_eq_ofNat, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, BitVec.toInt_eq_msb_cond]
  rcases hvc with hvc | hvc <;>
    cases hA' : a.msb <;> cases hB' : b.msb <;>
    cases hV' : (b - a - BitVec.ofNat w c.toNat).msb <;>
    simp only [hA', hB', hV', reduceIte, and_true, and_false, true_iff, false_iff,
      Decidable.not_not, Bool.true_eq_false, Bool.false_eq_true,
      not_true_eq_false, not_false_eq_true] at kA kB kV ⊢ <;>
    omega

/-- Regression tests to ensure terms are solvable by `bv_decide`. -/

example (a : BitVec 64) : addCarry a 0 false = false := by
  unfold addCarry; bv_decide

example (a b : BitVec 64) : subBorrow a b false = BitVec.ult a b := by
  unfold subBorrow; bv_decide

example (a : BitVec 64) : addOverflow a 0 false = false := by
  unfold addOverflow; bv_decide

example (a : BitVec 64) : subOverflow a 0 false = false := by
  unfold subOverflow; bv_decide

/-- `INC` overflows exactly at `intMax`. -/
example (a : BitVec 64) : addOverflow a 1 false = (a == BitVec.intMax 64) := by
  unfold addOverflow; bv_decide

/-- Carry-in is bitblasted too, not just the `c = false` case. -/
example (a : BitVec 64) (c : Bool) : addCarry a 0 c = (c && (a == BitVec.allOnes 64)) := by
  unfold addCarry; bv_decide

end Kraken.Flags
