import Kraken.Attribute
import Kraken.StdLibCandidates
import Std

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

namespace BitVec

@[kstep] def take {w : Nat} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def drop {w : Nat} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w - n)

end BitVec

attribute [kstep]
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.truncate

-- Conversion helpers to relate semantics expressed in terms of `BitVec` to `Int`/`Nat`.
namespace BitVec

def unsigned {w : Nat} (x : BitVec w) : Int := x.toNat
def signed {w : Nat} (x : BitVec w) : Int := x.toInt

-- AArch64 specific lemmas.

-- `SMULH`/`UMULH`, `*MADDL`/`*MSUBL`
theorem signExtend_mul_signExtend_eq_ofInt {w n : Nat} (hw : 0 < w) (hn : w + w ≤ n)
    (a b : BitVec w) :
    a.signExtend n * b.signExtend n = BitVec.ofInt n (a.signed * b.signed) :=
  (BitVec.ofInt_mul_toInt hw hn a b).symm

theorem setWidth_mul_setWidth_eq_ofInt {w n : Nat} (hn : w + w ≤ n) (a b : BitVec w) :
    a.setWidth n * b.setWidth n = BitVec.ofInt n (a.unsigned * b.unsigned) :=
  (BitVec.ofInt_mul_toNat hn a b).symm

-- `SMADDL`/`UMADDL`, `SMSUBL`/`UMSUBL`
theorem signExtend_mul_add_eq_ofInt (a b : BitVec 32) (c : BitVec 64) :
    a.signExtend 64 * b.signExtend 64 + c
      = BitVec.ofInt 64 (a.signed * b.signed + c.signed) := by
  simp only [BitVec.signed]
  rw [BitVec.ofInt_add, ← BitVec.ofInt_mul_toInt (by omega) (by omega),
    BitVec.ofInt_toInt]

theorem setWidth_mul_add_eq_ofInt (a b : BitVec 32) (c : BitVec 64) :
    a.setWidth 64 * b.setWidth 64 + c
      = BitVec.ofInt 64 (a.unsigned * b.unsigned + c.unsigned) := by
  simp only [BitVec.unsigned]
  rw [BitVec.ofInt_add, ← BitVec.ofInt_mul_toNat (by omega),
    BitVec.ofInt_toNat_setWidth, BitVec.setWidth_eq]

theorem sub_signExtend_mul_eq_ofInt (a b : BitVec 32) (c : BitVec 64) :
    c - a.signExtend 64 * b.signExtend 64
      = BitVec.ofInt 64 (c.signed - a.signed * b.signed) := by
  simp only [BitVec.signed]
  rw [BitVec.ofInt_sub, ← BitVec.ofInt_mul_toInt (by omega) (by omega),
    BitVec.ofInt_toInt]

theorem sub_setWidth_mul_eq_ofInt (a b : BitVec 32) (c : BitVec 64) :
    c - a.setWidth 64 * b.setWidth 64
      = BitVec.ofInt 64 (c.unsigned - a.unsigned * b.unsigned) := by
  simp only [BitVec.unsigned]
  rw [BitVec.ofInt_sub, ← BitVec.ofInt_mul_toNat (by omega),
    BitVec.ofInt_toNat_setWidth, BitVec.setWidth_eq]

-- x64 specific lemmas.

-- `mul` and `mulx`
theorem mul_widen_unsigned {w n : Nat} (hn : w + w ≤ n) (a b : BitVec w) :
    a.setWidth n * b.setWidth n = BitVec.ofInt n (a.unsigned * b.unsigned) :=
  (BitVec.ofInt_mul_toNat hn a b).symm

-- `imul`
theorem mul_widen_signed {w n : Nat} (hw : 0 < w) (hn : w + w ≤ n) (a b : BitVec w) :
    a.signExtend n * b.signExtend n = BitVec.ofInt n (a.signed * b.signed) :=
  (BitVec.ofInt_mul_toInt hw hn a b).symm

-- `mul` flags
theorem mul_unsigned_flags_spec {w : Nat} (a b : BitVec w) :
    BitVec.umulOverflow a b = true ↔ (a * b).unsigned ≠ a.unsigned * b.unsigned := by
  rw [BitVec.umulOverflow_iff]
  simp only [BitVec.unsigned, ne_eq, ← Int.natCast_mul, Int.natCast_inj]

-- `imul` flags
theorem mul_signed_flags_spec {w : Nat} (hw : 0 < w) (a b : BitVec w) :
    BitVec.smulOverflow a b = true ↔ (a * b).signed ≠ a.signed * b.signed :=
  BitVec.smulOverflow_iff hw a b

end BitVec
