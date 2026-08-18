/-!
# Standard library candidates

Lemmas that are needed in more than one place in Kraken and that are stated
generally enough to be (potentially) upstreamed.

See `DEVELOPER.md` for details on the policy.
-/

namespace BitVec

/-- Reducing a two's-complement value modulo `2 ^ n` is truncation to `n` bits,
provided `n ≤ m`.

`BitVec.ofInt_toInt` covers `n = m`. The side condition is necessary. For
`m < n` the left-hand side sign-extends while `setWidth` zero-extends. -/
theorem ofInt_toInt_setWidth {m n : Nat} (h : n ≤ m) (y : BitVec m) :
    BitVec.ofInt n y.toInt = y.setWidth n := by
  have hd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ m : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_setWidth, BitVec.toInt_eq_toNat_bmod,
    ← Int.emod_emod_of_dvd _ hd, Int.bmod_emod, Int.emod_emod_of_dvd _ hd]
  omega

/-- Reducing an unsigned value modulo `2 ^ n` is truncation to `n` bits. Unlike
`ofInt_toInt_setWidth` this needs no side condition. Both sides zero-extend when
`n` exceeds the source width.

The signed counterpart needs no lemma at all, `BitVec.signExtend` is defined
as `ofInt v x.toInt`. -/
theorem ofInt_toNat_setWidth {m n : Nat} (y : BitVec m) :
    BitVec.ofInt n (y.toNat : Int) = y.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  omega

/-- `BitVec.ofInt` commutes with left shift. Shifting an unbounded integer and
then reducing gives the same result as reducing first and shifting inside the
bitvector, because both discard the bits above `w`. -/
theorem ofInt_shiftLeft {w : Nat} (hw : 0 < w) (i : Int) (n : Nat) :
    BitVec.ofInt w (i <<< n) = BitVec.ofInt w i <<< n := by
  have h1 : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow_iff.mpr (by omega))
  rw [Int.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  congr 1
  rw [BitVec.twoPow_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, h1, Nat.one_mul]
  omega

/-- `BitVec.ofInt` commutes with subtraction. The `add` and `mul` counterparts
are in core while this one is not. -/
theorem ofInt_sub {n : Nat} (x y : Int) :
    BitVec.ofInt n (x - y) = BitVec.ofInt n x - BitVec.ofInt n y := by
  simp [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.sub_eq_add_neg, BitVec.ofInt_neg]

/-- Zero-extending before multiplying loses nothing. The unsigned product fits. -/
theorem toNat_setWidth_mul_setWidth {w n : Nat} (hn : w + w ≤ n) (a b : BitVec w) :
    ((a.setWidth n) * (b.setWidth n)).toNat = a.toNat * b.toNat := by
  have hmono : (2:Nat) ^ (w + w) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hw : (2:Nat) ^ w ≤ 2 ^ (w + w) := Nat.pow_le_pow_right (by omega) (by omega)
  have ha : a.toNat < 2 ^ w := a.isLt
  have hb : b.toNat < 2 ^ w := b.isLt
  have hlt : a.toNat * b.toNat < 2 ^ (w + w) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_lt_of_lt ha hb
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ n),
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ n),
    Nat.mod_eq_of_lt (by omega : a.toNat * b.toNat < 2 ^ n)]

/-- Sign-extending before multiplying loses nothing. The signed product fits.

The bound is not tight -- the signed product of two `w`-bit values is at most
`2 ^ (2 * w - 2)` in absolute value, which is why the `w + w`-bit result never
saturates. `w` must be positive for `BitVec w` to have a sign bit at all. -/
theorem toInt_signExtend_mul_signExtend {w n : Nat} (hw : 0 < w) (hn : w + w ≤ n)
    (a b : BitVec w) :
    ((a.signExtend n) * (b.signExtend n)).toInt = a.toInt * b.toInt := by
  have ha := a.toInt_lt; have ha' := a.le_toInt
  have hb := b.toInt_lt; have hb' := b.le_toInt
  have hc1 : ((2 ^ (w - 1) : Nat) : Int) = (2:Int) ^ (w - 1) := by push_cast; rfl
  have hc2 : ((2 ^ n : Nat) : Int) = (2:Int) ^ n := by push_cast; rfl
  have hhalf : (2:Nat) ^ (w - 1) * 2 = 2 ^ w := by rw [← Nat.pow_succ]; congr 1; omega
  have habs : (a.toInt * b.toInt).natAbs ≤ 2 ^ (w - 1) * 2 ^ (w - 1) := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
  have hfit : ((2 ^ (w - 1) * 2 ^ (w - 1) : Nat) : Int) * 2 < ((2 ^ n : Nat) : Int) := by
    have : (2:Nat) ^ (w - 1) * 2 ^ (w - 1) * 2 < 2 ^ n := by
      rw [← Nat.pow_add, ← Nat.pow_succ]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    exact_mod_cast this
  rw [BitVec.toInt_mul, BitVec.toInt_signExtend, BitVec.toInt_signExtend,
    show min n w = w by omega]
  rw [Int.bmod_eq_of_le_mul_two (x := a.toInt) (by omega) (by omega),
    Int.bmod_eq_of_le_mul_two (x := b.toInt) (by omega) (by omega)]
  rw [Int.bmod_eq_of_le_mul_two (by omega) (by omega)]

/-- The unsigned widening product. -/
theorem ofInt_mul_toNat {w n : Nat} (hn : w + w ≤ n) (a b : BitVec w) :
    BitVec.ofInt n ((a.toNat : Int) * (b.toNat : Int))
      = a.setWidth n * b.setWidth n := by
  rw [← Int.natCast_mul, ← toNat_setWidth_mul_setWidth hn a b, ofInt_toNat_setWidth,
    BitVec.setWidth_eq]

/-- The signed widening product. -/
theorem ofInt_mul_toInt {w n : Nat} (hw : 0 < w) (hn : w + w ≤ n) (a b : BitVec w) :
    BitVec.ofInt n (a.toInt * b.toInt) = a.signExtend n * b.signExtend n := by
  rw [← toInt_signExtend_mul_signExtend hw hn, BitVec.ofInt_toInt]

/-- The high half of an unsigned widening product. Shifting the `Int` product
down by `w` and truncating is the same as slicing bits `w ..< w + w` out of the
`BitVec` product. -/
theorem ofInt_shiftRight_mul_toNat {w n : Nat} (hn : w + w ≤ n) (a b : BitVec w) :
    BitVec.ofInt w (((a.toNat : Int) * (b.toNat : Int)) >>> w)
      = (a.setWidth n * b.setWidth n).extractLsb' w w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, toNat_setWidth_mul_setWidth hn, ← Int.natCast_mul,
    ← Int.natCast_shiftRight, BitVec.ofInt_natCast, BitVec.toNat_ofNat]

theorem umulOverflow_iff {w : Nat} (a b : BitVec w) :
    BitVec.umulOverflow a b = true ↔ (a * b).toNat ≠ a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]
  simp only [BitVec.umulOverflow, ge_iff_le, decide_eq_true_eq]
  have hM : 0 < 2 ^ w := Nat.two_pow_pos w
  generalize a.toNat * b.toNat = P
  have hlt := Nat.mod_lt P hM
  exact ⟨fun h heq => by omega,
    fun h => Nat.le_of_not_lt (fun hlt2 => h (Nat.mod_eq_of_lt hlt2))⟩

theorem smulOverflow_iff {w : Nat} (hw : 0 < w) (a b : BitVec w) :
    BitVec.smulOverflow a b = true ↔ (a * b).toInt ≠ a.toInt * b.toInt := by
  rw [BitVec.toInt_mul]
  simp only [BitVec.smulOverflow, Bool.or_eq_true, decide_eq_true_eq]
  generalize a.toInt * b.toInt = P
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  have hpow : ((2 ^ (v + 1) : Nat) : Int) = 2 * ((2 ^ v : Nat) : Int) := by
    rw [Nat.pow_succ]; push_cast; omega
  have hcast : ((2 ^ v : Nat) : Int) = (2:Int) ^ v := by push_cast; rfl
  rw [Ne, Int.bmod_eq_iff (Nat.two_pow_pos _)]
  simp only [Nat.add_sub_cancel, Int.sub_self, Int.dvd_zero, and_true]
  omega

/-- Rotate right by a bitvector amount, expressed with shifts. -/
def rorBV {w : Nat} (x : BitVec w) (m : BitVec w) : BitVec w :=
  (x >>> m) ||| (x <<< (BitVec.ofNat w w - m))

/-- Rotate left by a bitvector amount, expressed with shifts. -/
def rolBV {w : Nat} (x : BitVec w) (m : BitVec w) : BitVec w :=
  (x <<< m) ||| (x >>> (BitVec.ofNat w w - m))

theorem rolBV_eq_rotateLeft {w : Nat} (x m : BitVec w) (hm : m.toNat < w) :
    x.rolBV m = x.rotateLeft m.toNat := by
  have hwlt : w < 2 ^ w := Nat.lt_two_pow_self
  have hwBV : (BitVec.ofNat w w).toNat = w := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwlt]
  have hsub : ((BitVec.ofNat w w) - m).toNat = w - m.toNat := by
    rw [BitVec.toNat_sub, hwBV]
    have hm2 := m.isLt
    rw [show (2 ^ w - m.toNat) + w = 2 ^ w + (w - m.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hm]
  show (x <<< m.toNat) ||| (x >>> ((BitVec.ofNat w w) - m).toNat) = _
  rw [hsub]

theorem rotateLeft_mod {w : Nat} (x : BitVec w) (n : Nat) :
    x.rotateLeft (n % w) = x.rotateLeft n := by
  simp [BitVec.rotateLeft_def]

theorem rotateRight_mod {w : Nat} (x : BitVec w) (n : Nat) :
    x.rotateRight (n % w) = x.rotateRight n := by
  simp [BitVec.rotateRight_def]

theorem rorBV_eq_rotateRight {w : Nat} (x m : BitVec w) (hm : m.toNat < w) :
    x.rorBV m = x.rotateRight m.toNat := by
  have hwlt : w < 2 ^ w := Nat.lt_two_pow_self
  have hwBV : (BitVec.ofNat w w).toNat = w := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwlt]
  have hsub : ((BitVec.ofNat w w) - m).toNat = w - m.toNat := by
    rw [BitVec.toNat_sub, hwBV]
    have hm2 := m.isLt
    rw [show (2 ^ w - m.toNat) + w = 2 ^ w + (w - m.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hm]
  show (x >>> m.toNat) ||| (x <<< ((BitVec.ofNat w w) - m).toNat) = _
  rw [hsub]

end BitVec

namespace Int64

/-- `Int64.toInt` is by definition its bitvector's `toInt`, so reducing it
modulo `2 ^ n` is truncation of that bitvector. -/
theorem ofInt_toInt_setWidth {n : Nat} (h : n ≤ 64) (x : Int64) :
    BitVec.ofInt n x.toInt = x.toBitVec.setWidth n :=
  BitVec.ofInt_toInt_setWidth h x.toBitVec

/-- At the full width there is nothing to truncate. -/
theorem ofInt_toInt_eq_toBitVec (x : Int64) :
    BitVec.ofInt 64 x.toInt = x.toBitVec :=
  BitVec.ofInt_toInt

/-- Reconstructing an `Int64` from the signed value of a 64-bit bitvector gives
that bitvector back. -/
theorem ofInt_toInt_eq_ofBitVec (y : BitVec 64) :
    Int64.ofInt y.toInt = Int64.ofBitVec y := by
  simp [Int64.ofInt, Int64.ofBitVec, BitVec.ofInt_toInt]

/-- Adding two `Int64`s over `Int` and truncating is `Int64` addition, which
wraps. -/
theorem ofInt_add_toInt (x y : Int64) :
    BitVec.ofInt 64 (x.toInt + y.toInt) = (x + y).toBitVec := by
  rw [BitVec.ofInt_add, ofInt_toInt_eq_toBitVec, ofInt_toInt_eq_toBitVec,
    Int64.toBitVec_add]

end Int64
