module

public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0StepAttr
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.C0Agrees
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Logic.ProofKitMasks
public meta import Lean
public meta import LeanQbe.T.Logic.C0StepAttr
public meta import LeanQbe.T.Logic.C0Step
public meta import LeanQbe.T.Logic.ProofKitMasks

/-!
# ProofKit: Additive C0 / BitVec / U32 / Mask / Frame / Loop Combinators

Strictly additive proof-automation kit extending `C0Step`, `C0HeadStep`, `ControlComb`,
and `C0Agrees` without touching core pipeline modules:

1. **Additive `@[bv_c0]` rules, `U32Kit`, `c0_bv_omega`, & `c0_bv32_omega`**:
   * Safe `@[bv_c0]` normalizations for `OfNat` BitVec literals, arbitrary `n ≤ w`
     `setWidth`/`truncate` widening and narrowing, `signExtend` nonneg rules, shifts
     `<<<`/`>>>`, `udiv`/`umod`, `&&& 1`, and `(x <<< 1 ||| 1)`. Never rewrites `BitVec`
     equality globally.
   * `U32Kit`: `BitVec 32` / `UInt32` arithmetic, shifts, `setWidth 64` / `truncate 32`
     roundtrips, and `u32` bounds.
   * `c0_bv_omega` / `c0_bv32_omega`: goal-driven normalization (with `[h1, ...]` and `[*]`
     forms), bottom-up chained-subtraction resolution, `BitVec.isLt`/`UInt*.toNat` bounds,
     and `omega` closure (`std3` axioms only).
2. **`KissatHdrBitMaskKit`, `PWordKit`, & `pword_mask`** (re-exported via `ProofKitMasks`).
3. **`state_frame` / `state_frame!` tactics**:
   Recursively decomposes conjunctions and `Prop`-valued `structure`s (such as nested
   `LengthsOk`, `Preserves*`, `AgreesExcept`), and closes preserved fields
   (`{ s with f := v }.g = s.g`, `List.length_set`, projected invariants) cleanly.
4. **Structured loop & cursor combinators**:
   * `wp_while_state_mem`, `wp_while_state_agrees`, `c0_while_state`
   * `ArrayCursorInv`, `ArrayMutCursorInv`
   * `wp_while_cursor64`, `wp_while_cursor32`, `wp_while_mut_cursor64`
-/

set_option autoImplicit false

namespace LeanQbe.T.ProofKit

/-! ## 1. Pure Cursor Structures (`@[expose]`) -/

@[expose] public section

/-- Read-only array scan invariant over index slice `[lo, hi)` of `xs` paired with
arbitrary extra loop state `st : α`. -/
structure ArrayCursorInv {β : Type} {α : Type _} (lo hi : Nat) (xs : List β)
    (Inv : Nat → α → Prop) (idx : Nat) (st : α) : Prop where
  lo_le : lo ≤ idx
  idx_le : idx ≤ hi
  hi_le : hi ≤ xs.length
  inv : Inv idx st

/-- Mutating array scan invariant over index slice `[lo, hi)` starting from `xs₀`,
tracking that length is preserved and elements outside `[lo, idx)` still match `xs₀`. -/
structure ArrayMutCursorInv {β : Type} {α : Type _} (lo hi : Nat) (xs₀ : List β)
    (Inv : Nat → List β → α → Prop) (idx : Nat) (xs : List β) (st : α) : Prop where
  lo_le : lo ≤ idx
  idx_le : idx ≤ hi
  hi_le : hi ≤ xs₀.length
  len_eq : xs.length = xs₀.length
  outside_eq : OutsideSliceAgrees lo idx xs₀ xs
  inv : Inv idx xs st

end

/-! ## 2. Additive `@[bv_c0]` Normalization Rules -/

public section

private theorem nat_pow_pos_two (k : Nat) : 0 < 2 ^ k :=
  Nat.pow_pos (by decide)

@[bv_c0] theorem bv_c0_toNat_ofNat_lit {w n : Nat} :
    (@OfNat.ofNat (BitVec w) n BitVec.instOfNat).toNat = n % 2 ^ w :=
  rfl

@[bv_c0] theorem bv_c0_toNat_zero {w : Nat} :
    (0 : BitVec w).toNat = 0 :=
  BitVec.toNat_zero

theorem bv_c0_toNat_setWidth_of_le {n w : Nat} (x : BitVec n) (hle : n ≤ w) :
    (x.setWidth w).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hle))

theorem bv_c0_toNat_setWidth_of_ble {n w : Nat} (x : BitVec n) (h : Nat.ble n w = true) :
    (x.setWidth w).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (Nat.le_of_ble_eq_true h)

@[bv_c0 high] theorem bv_c0_zext1_32 (x : BitVec 1) : (x.setWidth 32).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext1_64 (x : BitVec 1) : (x.setWidth 64).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext8_16 (x : BitVec 8) : (x.setWidth 16).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext_self {w : Nat} (x : BitVec w) :
    (x.setWidth w).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (Nat.le_refl w)

@[bv_c0] theorem bv_c0_toNat_shiftLeft_nat {w : Nat} (x : BitVec w) (k : Nat) :
    (x <<< k).toNat = (x.toNat * 2 ^ k) % 2 ^ w := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

@[bv_c0] theorem bv_c0_toNat_shiftLeft_bv {w m : Nat} (x : BitVec w) (y : BitVec m) :
    (x <<< y).toNat = (x.toNat * 2 ^ y.toNat) % 2 ^ w := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

@[bv_c0] theorem bv_c0_toNat_ushiftRight_nat {w : Nat} (x : BitVec w) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[bv_c0] theorem bv_c0_toNat_ushiftRight_bv {w m : Nat} (x : BitVec w) (y : BitVec m) :
    (x >>> y).toNat = x.toNat / 2 ^ y.toNat := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[bv_c0] theorem bv_c0_toNat_udiv {w : Nat} (x y : BitVec w) :
    (x / y).toNat = x.toNat / y.toNat :=
  BitVec.toNat_udiv

@[bv_c0] theorem bv_c0_toNat_umod {w : Nat} (x y : BitVec w) :
    (x % y).toNat = x.toNat % y.toNat :=
  BitVec.toNat_umod

theorem bv_c0_toNat_and_one_of_le {w : Nat} (x : BitVec w) (hw : 1 ≤ w) :
    (x &&& 1#w).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, BitVec.toNat_one hw]
  simp [Nat.and_two_pow_sub_one_eq_mod x.toNat 1]

@[bv_c0 high] theorem bv_c0_toNat_and_one_64 (x : BitVec 64) :
    (x &&& 1#64).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_one_32 (x : BitVec 32) :
    (x &&& 1#32).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_one_16 (x : BitVec 16) :
    (x &&& 1#16).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_one_8 (x : BitVec 8) :
    (x &&& 1#8).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_bv_one_64 (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 1).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_64 x

@[bv_c0 high] theorem bv_c0_toNat_and_bv_one_32 (x : BitVec 32) :
    (x &&& BitVec.ofNat 32 1).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_32 x

private theorem testBit_two_mul (k j : Nat) : (2 * k).testBit (j + 1) = k.testBit j := by
  have : 2 * k = k <<< 1 := by rw [Nat.shiftLeft_eq]; omega
  rw [this, Nat.testBit_shiftLeft]
  simp

private theorem testBit_two_mul_add_one (k j : Nat) :
    (2 * k + 1).testBit (j + 1) = k.testBit j := by
  rw [Nat.testBit_succ, show (2 * k + 1) / 2 = k by omega]

private theorem nat_two_mul_or_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
    simp [Nat.testBit_zero]
  | succ j =>
    have h1 : (1 : Nat).testBit (j + 1) = false := by simp [Nat.testBit_succ]
    simp [testBit_two_mul, testBit_two_mul_add_one, h1]

theorem bv_c0_toNat_shl1_or_one_of_le {w : Nat} (x : BitVec w) (hw : 1 ≤ w) :
    ((x <<< 1) ||| 1#w).toNat = (2 * x.toNat + 1) % 2 ^ w := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_one hw]
  have hdvd : 2 ∣ 2 ^ w := by
    refine ⟨2 ^ (w - 1), ?_⟩
    have hw' : w = (w - 1) + 1 := by omega
    calc
      2 ^ w = 2 ^ ((w - 1) + 1) := by rw [← hw']
      _ = 2 ^ (w - 1) * 2 := Nat.pow_succ 2 (w - 1)
      _ = 2 * 2 ^ (w - 1) := Nat.mul_comm _ _
  obtain ⟨m, hm⟩ := hdvd
  have heven : (x.toNat * 2 ^ 1) % 2 ^ w = 2 * (x.toNat % m) := by
    rw [Nat.pow_one, Nat.mul_comm x.toNat 2, hm, Nat.mul_mod_mul_left]
  rw [heven, nat_two_mul_or_one]
  have hm_pos : 0 < m := by
    have hpos := nat_pow_pos_two w
    omega
  have hlt : 2 * (x.toNat % m) + 1 < 2 ^ w := by
    have hmod : x.toNat % m < m := Nat.mod_lt _ hm_pos
    omega
  have hmod2 : 2 * (x.toNat % m) = (2 * x.toNat) % (2 * m) :=
    (Nat.mul_mod_mul_left 2 x.toNat m).symm
  rw [← Nat.mod_eq_of_lt hlt, hm, Nat.add_mod (2 * (x.toNat % m)) 1 (2 * m), hmod2,
    Nat.mod_mod, ← Nat.add_mod (2 * x.toNat) 1 (2 * m)]

@[bv_c0 high] theorem bv_c0_toNat_shl1_or_one_64 (x : BitVec 64) :
    ((x <<< 1) ||| 1#64).toNat = (2 * x.toNat + 1) % 2 ^ 64 :=
  bv_c0_toNat_shl1_or_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_shl1_or_one_32 (x : BitVec 32) :
    ((x <<< 1) ||| 1#32).toNat = (2 * x.toNat + 1) % 2 ^ 32 :=
  bv_c0_toNat_shl1_or_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_zext32_shl1_or_one (x : BitVec 32) :
    ((x.setWidth 64 <<< 1) ||| 1#64).toNat = 2 * x.toNat + 1 := by
  rw [bv_c0_toNat_shl1_or_one_64, bv_c0_toNat_setWidth_of_le x (by decide)]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

private theorem nat_two_mul_xor_one (k : Nat) : (2 * k) ^^^ 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    have h1 : (1 : Nat).testBit (j + 1) = false := by simp [Nat.testBit_succ]
    simp [testBit_two_mul, testBit_two_mul_add_one, h1]

private theorem nat_two_mul_add_one_xor_one (k : Nat) : (2 * k + 1) ^^^ 1 = 2 * k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    have h1 : (1 : Nat).testBit (j + 1) = false := by simp [Nat.testBit_succ]
    simp [testBit_two_mul, testBit_two_mul_add_one, h1]

theorem bv_c0_toNat_xor_one_of_le {w : Nat} (x : BitVec w) (hw : 1 ≤ w) :
    (x ^^^ 1#w).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 := by
  rw [BitVec.toNat_xor, BitVec.toNat_one hw]
  split
  · rename_i hm
    have hx : x.toNat = 2 * (x.toNat / 2) := by omega
    calc
      x.toNat ^^^ 1 = (2 * (x.toNat / 2)) ^^^ 1 := by rw [← hx]
      _ = 2 * (x.toNat / 2) + 1 := nat_two_mul_xor_one (x.toNat / 2)
      _ = x.toNat + 1 := by omega
  · rename_i hm
    have hx : x.toNat = 2 * (x.toNat / 2) + 1 := by omega
    calc
      x.toNat ^^^ 1 = (2 * (x.toNat / 2) + 1) ^^^ 1 := by rw [← hx]
      _ = 2 * (x.toNat / 2) := nat_two_mul_add_one_xor_one (x.toNat / 2)
      _ = x.toNat - 1 := by omega

@[bv_c0 high] theorem bv_c0_toNat_xor_one_ushiftRight {w : Nat} (x : BitVec w) (hw : 1 ≤ w) :
    ((x ^^^ 1#w) >>> 1).toNat = x.toNat / 2 := by
  rw [bv_c0_toNat_ushiftRight_nat, bv_c0_toNat_xor_one_of_le x hw, Nat.pow_one]
  split <;> omega

@[bv_c0 high] theorem bv_c0_toNat_xor_one_ushiftRight_64 (x : BitVec 64) :
    ((x ^^^ 1#64) >>> 1).toNat = x.toNat / 2 :=
  bv_c0_toNat_xor_one_ushiftRight x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_xor_one_ushiftRight_32 (x : BitVec 32) :
    ((x ^^^ 1#32) >>> 1).toNat = x.toNat / 2 :=
  bv_c0_toNat_xor_one_ushiftRight x (by decide)

/-! ### `c0_bv_omega`-only equality & subtraction bridges (NOT in `@[bv_c0]`) -/

theorem bv_c0_eq_iff {w : Nat} (a b : BitVec w) : a = b ↔ a.toNat = b.toNat :=
  BitVec.toNat_eq

theorem bv_c0_ne_iff {w : Nat} (a b : BitVec w) : a ≠ b ↔ a.toNat ≠ b.toNat := by
  simp [BitVec.toNat_eq]

theorem bv_c0_lt_iff {w : Nat} (a b : BitVec w) : a < b ↔ a.toNat < b.toNat :=
  BitVec.lt_def

theorem bv_c0_le_iff {w : Nat} (a b : BitVec w) : a ≤ b ↔ a.toNat ≤ b.toNat :=
  BitVec.le_def

theorem bv_c0_toNat_sub_of_le_toNat {w : Nat} (x y : BitVec w) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem bv_c0_toNat_xor_one_64 (x : BitVec 64) :
    (x ^^^ 1#64).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_c0_toNat_xor_one_of_le x (by decide)

theorem bv_c0_toNat_xor_one_32 (x : BitVec 32) :
    (x ^^^ 1#32).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_c0_toNat_xor_one_of_le x (by decide)

theorem bv_c0_toNat_xor_one_8 (x : BitVec 8) :
    (x ^^^ 1#8).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_c0_toNat_xor_one_of_le x (by decide)

theorem bv_c0_ult_iff_toNat {w : Nat} (a b : BitVec w) :
    BitVec.ult a b = true ↔ a.toNat < b.toNat :=
  ⟨of_decide_eq_true, decide_eq_true⟩

theorem bv_c0_ule_iff_toNat {w : Nat} (a b : BitVec w) :
    BitVec.ule a b = true ↔ a.toNat ≤ b.toNat :=
  ⟨of_decide_eq_true, decide_eq_true⟩

theorem bv_c0_toNat_sub_of_eq {w : Nat} (x y : BitVec w) {nx ny : Nat}
    (hx : x.toNat = nx) (hy : y.toNat = ny) (hle : ny ≤ nx) :
    (x - y).toNat = nx - ny := by
  subst hx; subst hy
  exact bv_c0_toNat_sub_of_le_toNat x y hle

@[bv_c0] theorem bv_c0_toNat_truncate {n w : Nat} (x : BitVec n) :
    (x.truncate w).toNat = x.toNat % 2 ^ w :=
  BitVec.toNat_setWidth (i := w) (x := x)

@[bv_c0 high] theorem bv_c0_zext8_32 (x : BitVec 8) :
    (x.setWidth 32).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext8_64 (x : BitVec 8) :
    (x.setWidth 64).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext16_32 (x : BitVec 16) :
    (x.setWidth 32).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext16_64 (x : BitVec 16) :
    (x.setWidth 64).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext32_64 (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

theorem bv_c0_toNat_signExtend_of_lt {n w : Nat} (x : BitVec n)
    (hx : x.toNat < 2 ^ (n - 1)) :
    (x.signExtend w).toNat = x.toNat % 2 ^ w := by
  have hmsb : x.msb = false := by
    rw [BitVec.msb_eq_toNat, decide_eq_false (Nat.not_le.mpr hx)]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb, BitVec.toNat_setWidth]

theorem bv_c0_toNat_signExtend_of_lt_le {n w : Nat} (x : BitVec n)
    (hle : n ≤ w) (hx : x.toNat < 2 ^ (n - 1)) :
    (x.signExtend w).toNat = x.toNat := by
  rw [bv_c0_toNat_signExtend_of_lt x hx]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hle))

theorem bv_c0_toNat_signExtend_of_eq_lt {n w : Nat} (x : BitVec n) {nx : Nat}
    (hx : x.toNat = nx) (hle : n ≤ w) (hlt : nx < 2 ^ (n - 1)) :
    (x.signExtend w).toNat = nx := by
  subst hx
  exact bv_c0_toNat_signExtend_of_lt_le x hle hlt

theorem bv_c0_toNat_signExtend_of_eq_ble {n w : Nat} (x : BitVec n) {nx : Nat}
    (hx : x.toNat = nx) (hble : Nat.ble n w = true) (hlt : nx < 2 ^ (n - 1)) :
    (x.signExtend w).toNat = nx :=
  bv_c0_toNat_signExtend_of_eq_lt x hx (Nat.le_of_ble_eq_true hble) hlt

theorem bv_c0_toNat_truncate_of_ble {n w : Nat} (x : BitVec n) (h : Nat.ble n w = true) :
    (x.truncate w).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_ble x h

theorem list_getElem?_getD_of_lt {α : Type _} {xs : List α} {i : Nat}
    (hi : i < xs.length) (d : α) :
    xs[i]?.getD d = xs[i] := by
  simp [hi]

/-! ### `U32Kit`: 32-bit `BitVec` / `UInt32` Arithmetic & Widening/Narrowing Roundtrips -/

namespace U32Kit

theorem bv32_toNat_lt (x : BitVec 32) : x.toNat < 2 ^ 32 :=
  x.isLt

theorem bv32_toNat_le (x : BitVec 32) : x.toNat ≤ 0xFFFFFFFF := by
  have := x.isLt; omega

theorem u32_toNat_lt (x : UInt32) : x.toNat < 2 ^ 32 :=
  x.toBitVec.isLt

theorem u8_toNat_lt (x : UInt8) : x.toNat < 2 ^ 8 :=
  x.toBitVec.isLt

theorem u64_toNat_lt (x : UInt64) : x.toNat < 2 ^ 64 :=
  x.toBitVec.isLt

@[bv_c0] theorem u32_toNat_toBitVec (x : UInt32) : x.toBitVec.toNat = x.toNat :=
  UInt32.toNat_toBitVec x

@[bv_c0] theorem u32_ofNat_toBitVec (n : Nat) :
    (UInt32.ofNat n).toBitVec = BitVec.ofNat 32 n :=
  UInt32.toBitVec_ofNat n

@[bv_c0] theorem u32_ofNat_toNat (n : Nat) :
    (UInt32.ofNat n).toNat = n % 2 ^ 32 :=
  UInt32.toNat_ofNat'

@[bv_c0] theorem u32_ofNat_lit_toNat (n : Nat) :
    (OfNat.ofNat n : UInt32).toNat = n % 2 ^ 32 :=
  UInt32.toNat_ofNat'

@[bv_c0] theorem u8_ofNat_toNat (n : Nat) :
    (UInt8.ofNat n).toNat = n % 2 ^ 8 :=
  UInt8.toNat_ofNat'

@[bv_c0] theorem u8_ofNat_lit_toNat (n : Nat) :
    (OfNat.ofNat n : UInt8).toNat = n % 2 ^ 8 :=
  UInt8.toNat_ofNat'

@[bv_c0] theorem u64_ofNat_toNat (n : Nat) :
    (UInt64.ofNat n).toNat = n % 2 ^ 64 :=
  UInt64.toNat_ofNat'

@[bv_c0] theorem u64_ofNat_lit_toNat (n : Nat) :
    (OfNat.ofNat n : UInt64).toNat = n % 2 ^ 64 :=
  UInt64.toNat_ofNat'

theorem u8_eq_iff (a b : UInt8) : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt8.toNat, fun h => UInt8.toBitVec_inj.mp
    (BitVec.eq_of_toNat_eq (by simpa [UInt8.toNat_toBitVec] using h))⟩

theorem u32_eq_iff (a b : UInt32) : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt32.toNat, fun h => UInt32.toBitVec_inj.mp
    (BitVec.eq_of_toNat_eq (by simpa [UInt32.toNat_toBitVec] using h))⟩

theorem u64_eq_iff (a b : UInt64) : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt64.toNat, fun h => UInt64.toBitVec_inj.mp
    (BitVec.eq_of_toNat_eq (by simpa [UInt64.toNat_toBitVec] using h))⟩

theorem u8_ne_iff (a b : UInt8) : a ≠ b ↔ a.toNat ≠ b.toNat := by
  simp [u8_eq_iff]

theorem u32_ne_iff (a b : UInt32) : a ≠ b ↔ a.toNat ≠ b.toNat := by
  simp [u32_eq_iff]

theorem u64_ne_iff (a b : UInt64) : a ≠ b ↔ a.toNat ≠ b.toNat := by
  simp [u64_eq_iff]

theorem u8_toNat_sub_of_eq (x y : UInt8) {nx ny : Nat}
    (hx : x.toNat = nx) (hy : y.toNat = ny) (hle : ny ≤ nx) :
    (x - y).toNat = nx - ny := by
  subst hx; subst hy
  exact UInt8.toNat_sub_of_le x y (UInt8.le_iff_toNat_le.mpr hle)

theorem u32_toNat_sub_of_eq (x y : UInt32) {nx ny : Nat}
    (hx : x.toNat = nx) (hy : y.toNat = ny) (hle : ny ≤ nx) :
    (x - y).toNat = nx - ny := by
  subst hx; subst hy
  exact UInt32.toNat_sub_of_le x y (UInt32.le_iff_toNat_le.mpr hle)

theorem u64_toNat_sub_of_eq (x y : UInt64) {nx ny : Nat}
    (hx : x.toNat = nx) (hy : y.toNat = ny) (hle : ny ≤ nx) :
    (x - y).toNat = nx - ny := by
  subst hx; subst hy
  exact UInt64.toNat_sub_of_le x y (UInt64.le_iff_toNat_le.mpr hle)

theorem bv32_toNat_add_of_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv32_toNat_sub_of_le {x y : BitVec 32} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  bv_c0_toNat_sub_of_le_toNat x y h

theorem bv32_toNat_mul_of_lt {x y : BitVec 32} (h : x.toNat * y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem bv32_toNat_shl_of_lt {x : BitVec 32} {k : Nat} (h : x.toNat * 2 ^ k < 2 ^ 32) :
    (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [bv_c0_toNat_shiftLeft_nat, Nat.mod_eq_of_lt h]

theorem bv32_toNat_ushiftRight (x : BitVec 32) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k :=
  bv_c0_toNat_ushiftRight_nat x k

@[bv_c0 high] theorem bv32_setWidth64_toNat (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv32_setWidth64_setWidth32 (x : BitVec 32) :
    (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv32_setWidth64_toNat, Nat.mod_eq_of_lt x.isLt]

@[bv_c0 high] theorem bv32_setWidth64_truncate32 (x : BitVec 32) :
    (x.setWidth 64).truncate 32 = x :=
  bv32_setWidth64_setWidth32 x

theorem bv64_setWidth32_setWidth64_of_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x.setWidth 32).setWidth 64 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32_setWidth64_toNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem bv64_truncate32_setWidth64_of_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x.truncate 32).setWidth 64 = x :=
  bv64_setWidth32_setWidth64_of_lt hx

theorem bv32_setWidth64_add_of_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).setWidth 64 = x.setWidth 64 + y.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [bv32_setWidth64_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (show x.toNat + y.toNat < 2 ^ 64 by omega)]

theorem bv32_setWidth64_sub_of_le {x y : BitVec 32} (h : y.toNat ≤ x.toNat) :
    (x - y).setWidth 64 = x.setWidth 64 - y.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have h64 : (y.setWidth 64).toNat ≤ (x.setWidth 64).toNat := by
    simp only [bv32_setWidth64_toNat]; exact h
  rw [bv32_setWidth64_toNat, bv32_toNat_sub_of_le h,
    bv_c0_toNat_sub_of_le_toNat _ _ h64, bv32_setWidth64_toNat, bv32_setWidth64_toNat]

theorem bv64_add_truncate32 (x y : BitVec 64) :
    (x + y).truncate 32 = x.truncate 32 + y.truncate 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd (x.toNat + y.toNat) (by decide), Nat.add_mod]

theorem bv64_add_setWidth32 (x y : BitVec 64) :
    (x + y).setWidth 32 = x.setWidth 32 + y.setWidth 32 :=
  bv64_add_truncate32 x y

theorem bv32_xor_one_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  rw [bv_c0_toNat_xor_one_32]
  split <;> omega

theorem bv32_xor_one_self (x : BitVec 32) : (x ^^^ 1#32) ^^^ 1#32 = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem bv32_shl1_or_one_ushiftRight1 {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (((x <<< 1) ||| 1#32) >>> 1).toNat = x.toNat := by
  rw [bv_c0_toNat_ushiftRight_nat, bv_c0_toNat_shl1_or_one_32, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega)]
  omega

end U32Kit

end

/-! ## 3. Meta Infrastructure: `bv_c0` Simprocs, `c0_bv_omega`, `state_frame` -/

public section

open Lean Meta Elab Tactic

meta def evalNatExpr? (e : Lean.Expr) : MetaM (Option Nat) :=
  Meta.getNatValue? e

private meta def evalBvLitVal? (e : Lean.Expr) : MetaM (Option (Nat × Nat)) := do
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.ofNat 2 then
    let args := e.getAppArgs
    let some w ← evalNatExpr? args[0]! | return none
    let some n ← evalNatExpr? args[1]! | return none
    return some (w, n % 2 ^ w)
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    let ty := args[0]!
    if ty.isAppOfArity ``BitVec 1 then
      let some w ← evalNatExpr? ty.appArg! | return none
      let some n ← evalNatExpr? args[1]! | return none
      return some (w, n % 2 ^ w)
  return none

private meta def evalCastToNatSimproc (castNm thmNm : Name) (e : Lean.Expr) :
    SimpM Simp.Step := do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let inner := e.appArg!.consumeMData
  unless inner.isAppOfArity castNm 3 do return .continue
  let args := inner.getAppArgs
  let nE := args[0]!
  let wE := args[1]!
  let xE := args[2]!
  let some n ← evalNatExpr? nE | return .continue
  let some w ← evalNatExpr? wE | return .continue
  if n ≤ w then
    let lhs := mkApp2 (mkConst ``BitVec.toNat) nE xE
    let reflTrue ← mkEqRefl (mkConst ``Bool.true)
    let prf := mkApp4 (mkConst thmNm) nE wE xE reflTrue
    return .done { expr := lhs, proof? := some prf }
  return .continue

/-- Kernel-sound pre-`simproc` reducing `(x.setWidth w).toNat` to `x.toNat` for any concrete
widths `n ≤ w`, using `bv_c0_toNat_setWidth_of_ble` with `Eq.refl true`. -/
simproc ↑ [bv_c0] bv_c0_setWidth_toNat (BitVec.toNat (BitVec.setWidth _ _)) :=
  evalCastToNatSimproc ``BitVec.setWidth ``bv_c0_toNat_setWidth_of_ble

/-- Kernel-sound pre-`simproc` reducing `(x.truncate w).toNat` to `x.toNat` for concrete
widths `n ≤ w`. -/
simproc ↑ [bv_c0] bv_c0_truncate_toNat (BitVec.toNat (BitVec.truncate _ _)) :=
  evalCastToNatSimproc ``BitVec.truncate ``bv_c0_toNat_truncate_of_ble

/-- Kernel-sound pre-`simproc` evaluating concrete `(BitVec.signExtend w lit).toNat` for
`n, w ≤ 64` via `Eq.refl`. -/
simproc ↑ [bv_c0] bv_c0_signExtend_toNat (BitVec.toNat (BitVec.signExtend _ _)) := fun e => do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let inner := e.appArg!.consumeMData
  unless inner.isAppOfArity ``BitVec.signExtend 3 do return .continue
  let args := inner.getAppArgs
  let some n ← evalNatExpr? args[0]! | return .continue
  let some w ← evalNatExpr? args[1]! | return .continue
  let some (wn, k) ← evalBvLitVal? args[2]! | return .continue
  if wn == n && n ≤ 64 && w ≤ 64 then
    let val := ((BitVec.ofNat n k).signExtend w).toNat
    let numE := mkNatLit val
    let prf ← mkEqRefl e
    return .done { expr := numE, proof? := some prf }
  return .continue

/-- Kernel-sound pre-`simproc` reducing concrete `(@OfNat.ofNat (BitVec w) n _).toNat`
directly to the numeral `n` when `n < 2 ^ w`. -/
simproc ↑ [bv_c0] bv_c0_ofNat_toNat (BitVec.toNat (@OfNat.ofNat (BitVec _) _ _)) := fun e => do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let inner := e.appArg!
  unless inner.isAppOfArity ``OfNat.ofNat 3 do return .continue
  let args := inner.getAppArgs
  let tyE := args[0]!
  let nE := args[1]!
  let some w ← evalNatExpr? e.appFn!.appArg! | return .continue
  let some n ← evalNatExpr? nE | return .continue
  if n < 2 ^ w && tyE.isAppOfArity ``BitVec 1 then
    let numE := mkNatLit n
    let prf ← mkEqRefl e
    return .done { expr := numE, proof? := some prf }
  return .continue

private meta def heavyConstNames : Array Name := #[
  ``LeanQbe.T.wp, ``LeanQbe.T.Closed, ``LeanQbe.T.Expr, ``LeanQbe.T.Blocks,
  ``LeanQbe.T.Env, ``LeanQbe.T.TableImpl, ``Mem, ``Std.ExtHashMap, ``Std.ExtHashMap.sep
]

private meta def exprHasHeavyConst (e : Lean.Expr) : Bool :=
  (e.find? fun sub => match sub with
    | .const nm _ => heavyConstNames.contains nm
    | _ => false).isSome

private meta def collectHeavyFVars : MetaM (Std.HashSet FVarId) := do
  let mut out : Std.HashSet FVarId := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if exprHasHeavyConst decl.type then
        out := out.insert decl.fvarId
  return out

private meta def isHeavyContextProp (heavyFVars : Std.HashSet FVarId) (ty : Lean.Expr) : Bool :=
  exprHasHeavyConst ty ||
  (ty.find? fun sub => match sub with
    | .fvar fid => heavyFVars.contains fid
    | _ => false).isSome

private meta def propFactsFromLCtx : MetaM (List Lean.Expr) := do
  let heavyFVars ← collectHeavyFVars
  let mut facts : List Lean.Expr := []
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if !isHeavyContextProp heavyFVars decl.type then
        if ← isProp decl.type then
          facts := decl.toExpr :: facts
  return facts

private meta def tryProveWithOmega? (goalTy : Lean.Expr) : MetaM (Option Lean.Expr) := do
  withoutModifyingState do
    try
      let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
      if let some gFalse ← mvar.mvarId!.falseOrByContra then
        gFalse.withContext do
          let facts ← propFactsFromLCtx
          Lean.Elab.Tactic.Omega.omega facts gFalse
      let prf ← instantiateMVars mvar
      if prf.hasExprMVar then return none
      return some prf
    catch _ =>
      return none

/-- Reduce `2 ^ k` for concrete Nat literals `k ≤ 64` so `omega` handles `x * 2 ^ k`
and `x / 2 ^ k` linearly. Uses plain kernel `Eq.refl`. -/
simproc c0PowSimproc ((2 : Nat) ^ _) := fun e => do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``HPow.hPow 6 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat && args[2]!.isConstOf ``Nat do
    return .continue
  let some b ← evalNatExpr? args[4]! | return .continue
  let some k ← evalNatExpr? args[5]! | return .continue
  if b == 2 && k ≤ 64 then
    let valE := mkNatLit (2 ^ k)
    let prf ← mkEqRefl e
    return .done { expr := valE, proof? := some prf }
  return .continue

/-- Bottom-up `simproc` normalizing `(x.signExtend w).toNat` for symbolic nonneg `x`
when `n ≤ w` and `omega` proves `x.toNat < 2 ^ (n - 1)`. -/
simproc ↓ c0SignExtendSimproc (BitVec.toNat (BitVec.signExtend _ _)) := fun e => do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let inner := e.appArg!.consumeMData
  unless inner.isAppOfArity ``BitVec.signExtend 3 do return .continue
  let args := inner.getAppArgs
  let nE := args[0]!
  let wE := args[1]!
  let xE := args[2]!
  let some n ← evalNatExpr? nE | return .continue
  let some w ← evalNatExpr? wE | return .continue
  unless 0 < n && n ≤ w && n ≤ 64 do return .continue
  let xToNat := mkApp2 (mkConst ``BitVec.toNat) nE xE
  let resX ← Simp.simp xToNat
  let nx := resX.expr
  let hx ← resX.getProof
  let boundTy ← mkAppM ``LT.lt #[nx, mkNatLit (2 ^ (n - 1))]
  let some hlt ← tryProveWithOmega? boundTy | return .continue
  let reflTrue ← mkEqRefl (mkConst ``Bool.true)
  let prf := mkAppN (mkConst ``bv_c0_toNat_signExtend_of_eq_ble)
    #[nE, wE, xE, nx, hx, reflTrue, hlt]
  return .visit { expr := nx, proof? := some prf }

/-- Bottom-up recursive post-`simproc` rewriting `(x - y).toNat` (including arbitrary-depth
chained subtractions `((a - b) - c).toNat`) to `nx - ny` whenever `omega` proves `ny ≤ nx`
after recursively simplifying `x.toNat` and `y.toNat`. -/
simproc ↓ c0SubModSimproc (BitVec.toNat (_ - _)) := fun e => do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let inner := e.appArg!.consumeMData
  unless inner.isAppOfArity ``HSub.hSub 6 do return .continue
  let args := inner.getAppArgs
  let wE := e.appFn!.appArg!
  let xE := args[4]!
  let yE := args[5]!
  let xToNat := mkApp2 (mkConst ``BitVec.toNat) wE xE
  let yToNat := mkApp2 (mkConst ``BitVec.toNat) wE yE
  let resX ← Simp.simp xToNat
  let resY ← Simp.simp yToNat
  let nx := resX.expr
  let ny := resY.expr
  let condTy ← mkAppM ``LE.le #[ny, nx]
  let some hle ← tryProveWithOmega? condTy | return .continue
  let hx ← resX.getProof
  let hy ← resY.getProof
  let prf := mkAppN (mkConst ``bv_c0_toNat_sub_of_eq) #[wE, xE, yE, nx, ny, hx, hy, hle]
  let rhs ← mkAppM ``HSub.hSub #[nx, ny]
  return .visit { expr := rhs, proof? := some prf }

private meta def evalUintOfNatSimproc (toNatNm tyNm : Name) (w : Nat) (e : Lean.Expr) :
    SimpM Simp.Step := do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity toNatNm 1 do return .continue
  let inner := e.appArg!.consumeMData
  let nE? : Option Lean.Expr :=
    if inner.isAppOfArity ``OfNat.ofNat 3 && inner.getAppArgs[0]!.isConstOf tyNm then
      some inner.getAppArgs[1]!
    else if inner.isAppOfArity (tyNm ++ `ofNat) 1 then
      some inner.appArg!
    else
      none
  let some nE := nE? | return .continue
  let some n ← evalNatExpr? nE | return .continue
  if n < 2 ^ w then
    let numE := mkNatLit n
    let prf ← mkEqRefl e
    return .done { expr := numE, proof? := some prf }
  return .continue

private meta def subUintSimproc (toNatNm subEqNm : Name) (e : Lean.Expr) :
    SimpM Simp.Step := do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity toNatNm 1 do return .continue
  let inner := e.appArg!.consumeMData
  unless inner.isAppOfArity ``HSub.hSub 6 do return .continue
  let args := inner.getAppArgs
  let xE := args[4]!
  let yE := args[5]!
  let xToNat := mkApp (mkConst toNatNm) xE
  let yToNat := mkApp (mkConst toNatNm) yE
  let resX ← Simp.simp xToNat
  let resY ← Simp.simp yToNat
  let nx := resX.expr
  let ny := resY.expr
  let condTy ← mkAppM ``LE.le #[ny, nx]
  let some hle ← tryProveWithOmega? condTy | return .continue
  let hx ← resX.getProof
  let hy ← resY.getProof
  let prf := mkAppN (mkConst subEqNm) #[xE, yE, nx, ny, hx, hy, hle]
  let rhs ← mkAppM ``HSub.hSub #[nx, ny]
  return .visit { expr := rhs, proof? := some prf }

simproc ↑ c0U8OfNatSimproc (UInt8.toNat _) :=
  evalUintOfNatSimproc ``UInt8.toNat ``UInt8 8

simproc ↑ c0U32OfNatSimproc (UInt32.toNat _) :=
  evalUintOfNatSimproc ``UInt32.toNat ``UInt32 32

simproc ↑ c0U64OfNatSimproc (UInt64.toNat _) :=
  evalUintOfNatSimproc ``UInt64.toNat ``UInt64 64

simproc ↓ c0SubU8Simproc (UInt8.toNat (_ - _)) :=
  subUintSimproc ``UInt8.toNat ``U32Kit.u8_toNat_sub_of_eq

simproc ↓ c0SubU32Simproc (UInt32.toNat (_ - _)) :=
  subUintSimproc ``UInt32.toNat ``U32Kit.u32_toNat_sub_of_eq

simproc ↓ c0SubU64Simproc (UInt64.toNat (_ - _)) :=
  subUintSimproc ``UInt64.toNat ``U32Kit.u64_toNat_sub_of_eq

simproc ↑ c0NatOfNatSimproc (@OfNat.ofNat Nat _ _) := fun e => do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``OfNat.ofNat 3 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat do return .continue
  let some n ← evalNatExpr? args[1]! | return .continue
  let lit := mkNatLit n
  if lit == e then return .continue
  unless ← isDefEq e lit do return .continue
  let prf ← mkEqRefl e
  return .done { expr := lit, proof? := some prf }

simproc ↑ c0NatModSimproc ((_ : Nat) % _) := fun e => do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``HMod.hMod 6 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat &&
      args[2]!.isConstOf ``Nat do
    return .continue
  let some a ← evalNatExpr? args[4]! | return .continue
  let some b ← evalNatExpr? args[5]! | return .continue
  if b > 0 && a ≤ 2 ^ 128 && b ≤ 2 ^ 128 then
    let lit := mkNatLit (a % b)
    unless ← isDefEq e lit do return .continue
    let prf ← mkEqRefl e
    return .done { expr := lit, proof? := some prf }
  return .continue

/-- Post-`simproc` rewriting `a % b` to `a` whenever `omega` proves `a < b` from local
hypotheses. -/
simproc ↓ c0ModLtSimproc ((_ : Nat) % _) := fun e => do
  if e.hasLooseBVars then return .continue
  unless e.isAppOfArity ``HMod.hMod 6 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat && args[2]!.isConstOf ``Nat do
    return .continue
  let aE := args[4]!
  let bE := args[5]!
  let condTy ← mkAppM ``LT.lt #[aE, bE]
  let some hlt ← tryProveWithOmega? condTy | return .continue
  let prf := mkApp3 (mkConst ``Nat.mod_eq_of_lt) aE bE hlt
  return .visit { expr := aE, proof? := some prf }

private meta def collectToNatArgs (e : Lean.Expr) (seen : Std.HashSet Lean.Expr) :
    MetaM (Std.HashSet Lean.Expr) := do
  let ref ← IO.mkRef seen
  e.forEach fun sub => do
    if sub.hasLooseBVars then
      return
    if sub.isAppOfArity ``BitVec.toNat 2 then
      ref.modify (·.insert sub)
  ref.get

private meta def collectBitVecExprs (e : Lean.Expr) (seen : Std.HashSet Lean.Expr) :
    MetaM (Std.HashSet Lean.Expr) := do
  let ref ← IO.mkRef seen
  e.forEach fun sub => do
    if sub.hasLooseBVars then
      return
    try
      let ty ← whnf (← inferType sub)
      if ty.isAppOfArity ``BitVec 1 then
        let fn := sub.getAppFn
        let isArith := fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``HSub.hSub ||
          fn.isConstOf ``HMul.hMul || fn.isConstOf ``HShiftLeft.hShiftLeft ||
          fn.isConstOf ``HShiftRight.hShiftRight || fn.isConstOf ``OfNat.ofNat ||
          fn.isConstOf ``BitVec.ofNat || fn.isConstOf ``BitVec.setWidth ||
          fn.isConstOf ``BitVec.truncate || fn.isConstOf ``BitVec.signExtend ||
          fn.isConstOf ``HAnd.hAnd || fn.isConstOf ``HOr.hOr ||
          fn.isConstOf ``HXor.hXor || fn.isConstOf ``HDiv.hDiv || fn.isConstOf ``HMod.hMod
        if !isArith then
          let wE := ty.appArg!
          ref.modify (·.insert (mkApp2 (mkConst ``BitVec.toNat) wE sub))
    catch _ => pure ()
  ref.get

private meta def collectUIntExprs (e : Lean.Expr) (seen : Std.HashSet (Name × Lean.Expr)) :
    MetaM (Std.HashSet (Name × Lean.Expr)) := do
  let ref ← IO.mkRef seen
  e.forEach fun sub => do
    if sub.hasLooseBVars then
      return
    try
      let ty ← whnf (← inferType sub)
      let some nm := ty.constName? | return
      if nm == ``UInt8 || nm == ``UInt32 || nm == ``UInt64 then
        let fn := sub.getAppFn
        let isArith := fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``HSub.hSub ||
          fn.isConstOf ``HMul.hMul || fn.isConstOf ``HShiftLeft.hShiftLeft ||
          fn.isConstOf ``HShiftRight.hShiftRight || fn.isConstOf ``OfNat.ofNat ||
          fn.isConstOf ``UInt8.ofNat || fn.isConstOf ``UInt32.ofNat ||
          fn.isConstOf ``UInt64.ofNat || fn.isConstOf ``HAnd.hAnd ||
          fn.isConstOf ``HOr.hOr || fn.isConstOf ``HXor.hXor ||
          fn.isConstOf ``HDiv.hDiv || fn.isConstOf ``HMod.hMod
        if !isArith then
          ref.modify (·.insert (nm, sub))
    catch _ => pure ()
  ref.get

private meta partial def collectExprFVarsAux (e : Lean.Expr)
    (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
  if !e.hasFVar then acc else
  match e with
  | .fvar fid => acc.insert fid
  | .app f a => collectExprFVarsAux a (collectExprFVarsAux f acc)
  | .lam _ t b _ => collectExprFVarsAux b (collectExprFVarsAux t acc)
  | .forallE _ t b _ => collectExprFVarsAux b (collectExprFVarsAux t acc)
  | .letE _ t v b _ =>
      collectExprFVarsAux b (collectExprFVarsAux v (collectExprFVarsAux t acc))
  | .mdata _ b => collectExprFVarsAux b acc
  | .proj _ _ b => collectExprFVarsAux b acc
  | _ => acc

private meta def collectExprFVars (e : Lean.Expr) (acc : Std.HashSet FVarId) :
    Std.HashSet FVarId :=
  collectExprFVarsAux e acc

private meta partial def exprMentionsAnyFVar (e : Lean.Expr)
    (fvars : Std.HashSet FVarId) : Bool :=
  if !e.hasFVar then false else
  match e with
  | .fvar fid => fvars.contains fid
  | .app f a => exprMentionsAnyFVar f fvars || exprMentionsAnyFVar a fvars
  | .lam _ t b _ => exprMentionsAnyFVar t fvars || exprMentionsAnyFVar b fvars
  | .forallE _ t b _ => exprMentionsAnyFVar t fvars || exprMentionsAnyFVar b fvars
  | .letE _ t v b _ =>
      exprMentionsAnyFVar t fvars || exprMentionsAnyFVar v fvars ||
      exprMentionsAnyFVar b fvars
  | .mdata _ b => exprMentionsAnyFVar b fvars
  | .proj _ _ b => exprMentionsAnyFVar b fvars
  | _ => false

private meta def collectRelevantHyps (mvar : MVarId) (seedFVars : Std.HashSet FVarId)
    (extraSeeds : Array FVarId) (useAll : Bool) : MetaM (Array FVarId) :=
  mvar.withContext do
    let heavyFVars ← collectHeavyFVars
    let mut allCand : Array LocalDecl := #[]
    for decl in ← getLCtx do
      if !decl.isImplementationDetail then
        if ← isProp decl.type then
          if !isHeavyContextProp heavyFVars decl.type then
            allCand := allCand.push decl
    if useAll then
      return allCand.map (·.fvarId)
    let mut selected : Std.HashSet FVarId := {}
    let mut relFVars : Std.HashSet FVarId := collectExprFVars (← mvar.getType) seedFVars
    for fid in extraSeeds do
      selected := selected.insert fid
      if let some decl := (← getLCtx).find? fid then
        relFVars := collectExprFVars decl.type relFVars
    -- Connected component over arithmetic/type hypotheses reachable from goal + explicit seeds
    for _ in [:8] do
      let prevCount := selected.size
      for decl in allCand do
        if !selected.contains decl.fvarId then
          if exprMentionsAnyFVar decl.type relFVars then
            selected := selected.insert decl.fvarId
            relFVars := collectExprFVars decl.type relFVars
      if selected.size == prevCount then break
    let mut out : Array FVarId := #[]
    for decl in allCand do
      if selected.contains decl.fvarId then
        out := out.push decl.fvarId
    return out

private meta def injectBoundsFor (mvar : MVarId) (hypFVars : Array FVarId)
    (includeUInt : Bool) : MetaM MVarId :=
  mvar.withContext do
    let tgt ← mvar.getType
    let mut toNatTerms : Std.HashSet Lean.Expr := {}
    toNatTerms ← collectToNatArgs tgt toNatTerms
    toNatTerms ← collectBitVecExprs tgt toNatTerms
    let mut uItems : Std.HashSet (Name × Lean.Expr) := {}
    if includeUInt then
      uItems ← collectUIntExprs tgt uItems
    let hypSet : Std.HashSet FVarId := hypFVars.foldl (·.insert ·) {}
    let goalFVars := collectExprFVars tgt {}
    for fid in hypFVars do
      if let some decl ← fid.findDecl? then
        toNatTerms ← collectToNatArgs decl.type toNatTerms
        toNatTerms ← collectBitVecExprs decl.type toNatTerms
        if includeUInt then
          uItems ← collectUIntExprs decl.type uItems
    for decl in ← getLCtx do
      if !decl.isImplementationDetail then
        if hypSet.contains decl.fvarId || goalFVars.contains decl.fvarId then
          let ty ← whnf decl.type
          if ty.isAppOfArity ``BitVec 1 && !decl.toExpr.hasLooseBVars then
            toNatTerms := toNatTerms.insert (mkApp2 (mkConst ``BitVec.toNat) ty.appArg! decl.toExpr)
          else if includeUInt then
            if let some nm := ty.constName? then
              if (nm == ``UInt8 || nm == ``UInt32 || nm == ``UInt64) &&
                  !decl.toExpr.hasLooseBVars then
                uItems := uItems.insert (nm, decl.toExpr)
    let mut cur := mvar
    let mut idx : Nat := 0
    for term in toNatTerms do
      if term.isAppOfArity ``BitVec.toNat 2 then
        let wE := term.appFn!.appArg!
        let xE := term.appArg!
        let boundTy ← mkAppM ``LT.lt #[term, ← mkAppM ``HPow.hPow #[mkNatLit 2, wE]]
        let already ← cur.withContext do
          (← getLCtx).anyM fun d => do
            if d.isImplementationDetail then return false
            withoutModifyingState (isDefEq d.type boundTy)
        if !already then
          let prf := mkApp2 (mkConst ``BitVec.isLt) wE xE
          cur ← cur.assert (Lean.Name.mkSimple s!"_bv_lt_{idx}") boundTy prf
          let (_, cur') ← cur.intro1P
          cur := cur'
          idx := idx + 1
    if includeUInt then
      for (tyNm, xE) in uItems do
        let (toNatNm, ltThmNm, w) :=
          if tyNm == ``UInt8 then (``UInt8.toNat, ``U32Kit.u8_toNat_lt, 8)
          else if tyNm == ``UInt32 then (``UInt32.toNat, ``U32Kit.u32_toNat_lt, 32)
          else (``UInt64.toNat, ``U32Kit.u64_toNat_lt, 64)
        let term := mkApp (mkConst toNatNm) xE
        let boundTy ← mkAppM ``LT.lt #[term, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit w]]
        let already ← cur.withContext do
          (← getLCtx).anyM fun d => do
            if d.isImplementationDetail then return false
            withoutModifyingState (isDefEq d.type boundTy)
        if !already then
          let prf := mkApp (mkConst ltThmNm) xE
          cur ← cur.assert (Lean.Name.mkSimple s!"_u_lt_{idx}") boundTy prf
          let (_, cur') ← cur.intro1P
          cur := cur'
          idx := idx + 1
    return cur

/-- Simplify with `@[bv_c0]` at target and all non-dependent hypotheses. -/
elab "c0_bv_simp" : tactic => do
  evalTactic (← `(tactic| try simp only [bv_c0] at *))

private meta def addLocalNumEqs (thms : SimpTheorems) : MetaM SimpTheorems := do
  let heavyFVars ← collectHeavyFVars
  let mut res := thms
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if !isHeavyContextProp heavyFVars decl.type then
        if let some (_, lhs, rhs) := decl.type.eq? then
          if (← Meta.getNatValue? rhs).isSome && !lhs.hasLooseBVars then
            res ← res.add (.fvar decl.fvarId) #[] decl.toExpr
  return res

private meta def runBvOmegaSimpPass (includeSub includeSubMod includeUInt : Bool)
    (hypFVars : Array FVarId) : TacticM (Array FVarId) := do
  if (← getGoals).isEmpty then return hypFVars
  let (g, tail) := match ← getGoals with
    | g :: gs => (g, gs)
    | [] => unreachable!
  let resGoal? ← g.withContext do
    let mut thms ← match (← getSimpExtension? `bv_c0) with
      | some ext => ext.getTheorems
      | none => pure {}
    if !includeSub then
      thms := thms.eraseCore (.decl ``BitVec.toNat_sub)
    for c in [``bv_c0_eq_iff, ``bv_c0_ne_iff, ``bv_c0_lt_iff, ``bv_c0_le_iff,
        ``bv_c0_ult_iff_toNat, ``bv_c0_ule_iff_toNat, ``bv_c0_toNat_truncate,
        ``bv_c0_toNat_xor_one_64, ``bv_c0_toNat_xor_one_32, ``bv_c0_toNat_xor_one_8,
        ``Bool.not_eq_true, ``Bool.decide_eq_true, ``Bool.decide_eq_false,
        ``Nat.mul_one, ``Nat.one_mul, ``Nat.add_zero, ``Nat.zero_add, ``Nat.mod_mod] do
      thms ← thms.addConst c
    if includeUInt then
      for c in [
          ``U32Kit.u8_eq_iff, ``U32Kit.u32_eq_iff, ``U32Kit.u64_eq_iff,
          ``U32Kit.u8_ne_iff, ``U32Kit.u32_ne_iff, ``U32Kit.u64_ne_iff,
          ``UInt8.le_iff_toNat_le, ``UInt32.le_iff_toNat_le, ``UInt64.le_iff_toNat_le,
          ``UInt8.lt_iff_toNat_lt, ``UInt32.lt_iff_toNat_lt, ``UInt64.lt_iff_toNat_lt,
          ``U32Kit.u8_ofNat_toNat, ``U32Kit.u32_ofNat_toNat, ``U32Kit.u64_ofNat_toNat,
          ``U32Kit.u8_ofNat_lit_toNat, ``U32Kit.u32_ofNat_lit_toNat,
          ``U32Kit.u64_ofNat_lit_toNat,
          ``U32Kit.u32_toNat_toBitVec, ``U32Kit.u32_ofNat_toBitVec,
          ``UInt8.toNat_zero, ``UInt32.toNat_zero, ``UInt64.toNat_zero,
          ``UInt8.toNat_add, ``UInt32.toNat_add, ``UInt64.toNat_add,
          ``UInt8.toNat_mul, ``UInt32.toNat_mul, ``UInt64.toNat_mul,
          ``UInt8.toNat_div, ``UInt32.toNat_div, ``UInt64.toNat_div,
          ``UInt8.toNat_mod, ``UInt32.toNat_mod, ``UInt64.toNat_mod,
          ``UInt8.toNat_shiftLeft, ``UInt32.toNat_shiftLeft, ``UInt64.toNat_shiftLeft,
          ``UInt8.toNat_shiftRight, ``UInt32.toNat_shiftRight, ``UInt64.toNat_shiftRight,
          ``UInt8.toNat_toUInt32, ``UInt8.toNat_toUInt64,
          ``UInt32.toNat_toUInt64, ``UInt64.toNat_toUInt32,
          ``Nat.shiftLeft_eq, ``Nat.shiftRight_eq_div_pow] do
        thms ← thms.addConst c
    thms ← addLocalNumEqs thms
    let mut simprocs : Simp.Simprocs := {}
    if let some bvSimpExt ← Simp.getSimprocExtension? `bv_c0 then
      simprocs ← bvSimpExt.getSimprocs
    simprocs ← simprocs.add ``bv_c0_setWidth_toNat false
    simprocs ← simprocs.add ``bv_c0_truncate_toNat false
    simprocs ← simprocs.add ``bv_c0_signExtend_toNat false
    simprocs ← simprocs.add ``bv_c0_ofNat_toNat false
    simprocs ← simprocs.add ``c0NatOfNatSimproc false
    simprocs ← simprocs.add ``c0NatOfNatSimproc true
    simprocs ← simprocs.add ``c0NatModSimproc false
    simprocs ← simprocs.add ``c0NatModSimproc true
    simprocs ← simprocs.add ``c0PowSimproc false
    simprocs ← simprocs.add ``c0SignExtendSimproc true
    simprocs ← simprocs.add ``c0SubModSimproc includeSubMod
    if includeUInt then
      for post in [false, true] do
        simprocs ← simprocs.add ``c0PowSimproc post
        simprocs ← simprocs.add ``c0U8OfNatSimproc post
        simprocs ← simprocs.add ``c0U32OfNatSimproc post
        simprocs ← simprocs.add ``c0U64OfNatSimproc post
      simprocs ← simprocs.add ``c0SubU8Simproc includeSubMod
      simprocs ← simprocs.add ``c0SubU32Simproc includeSubMod
      simprocs ← simprocs.add ``c0SubU64Simproc includeSubMod
    simprocs ← simprocs.add ``c0ModLtSimproc true
    let ctx ← Simp.mkContext
      (config := { failIfUnchanged := false, maxSteps := 100000 })
      (simpTheorems := #[thms])
    let liveHyps ← hypFVars.filterM fun fid => return (← fid.findDecl?).isSome
    let (res?, _) ← simpGoal g ctx #[simprocs] (simplifyTarget := true)
      (fvarIdsToSimp := liveHyps)
    return res?
  match resGoal? with
  | none => setGoals tail; return #[]
  | some (fvs', g') => setGoals (g' :: tail); return fvs'

private meta def runBvOmegaPasses (includeUInt : Bool) (hypFVars : Array FVarId) :
    TacticM Unit := do
  if (← getGoals).isEmpty then return
  let (g, tail) := match ← getGoals with | g :: gs => (g, gs) | [] => unreachable!
  let g ← injectBoundsFor g hypFVars includeUInt
  setGoals (g :: tail)
  let mut hyps ← runBvOmegaSimpPass false false includeUInt hypFVars
  if (← getGoals).isEmpty then return
  hyps ← runBvOmegaSimpPass false false includeUInt hyps
  if (← getGoals).isEmpty then return
  hyps ← runBvOmegaSimpPass false true includeUInt hyps
  if (← getGoals).isEmpty then return
  hyps ← runBvOmegaSimpPass false true includeUInt hyps
  if (← getGoals).isEmpty then return
  let s1 ← saveState
  try
    evalTactic (← `(tactic| first | rfl | assumption | omega | bv_omega))
    if (← getGoals).isEmpty then return
    s1.restore
  catch _ =>
    s1.restore
  let _ ← runBvOmegaSimpPass true true includeUInt hyps
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try (first | rfl | assumption | omega | bv_omega)))

private meta def assertExplicitHyps (mvar : MVarId) (hyps : Array (TSyntax `term)) :
    TacticM (MVarId × Array FVarId × Std.HashSet FVarId) := do
  let mut cur := mvar
  let mut explicitFVars : Array FVarId := #[]
  let mut seedFVars : Std.HashSet FVarId := {}
  let mut idx : Nat := 0
  for stx in hyps do
    let e ← cur.withContext do Term.elabTerm stx none
    if e.isFVar then
      explicitFVars := explicitFVars.push e.fvarId!
    else
      let ty ← cur.withContext do instantiateMVars (← inferType e)
      seedFVars := collectExprFVars ty seedFVars
      cur ← cur.assert (Lean.Name.mkSimple s!"_bv_arg_{idx}") ty e
      let (fid, cur') ← cur.intro1P
      cur := cur'
      explicitFVars := explicitFVars.push fid
      idx := idx + 1
  return (cur, explicitFVars, seedFVars)

private meta def runBvOmegaCore (includeUInt useAllFlag : Bool)
    (explicitHyps : Option (Array (TSyntax `term))) : TacticM Unit := do
  evalTactic (← `(tactic| try (first | rfl | assumption)))
  if (← getGoals).isEmpty then return
  let (g, tail) := match ← getGoals with | g :: gs => (g, gs) | [] => unreachable!
  match explicitHyps with
  | some hs =>
      let (g', extraFVars, seedFVars) ← assertExplicitHyps g hs
      setGoals (g' :: tail)
      let hypFVars ← collectRelevantHyps g' seedFVars extraFVars false
      runBvOmegaPasses includeUInt hypFVars
      if !(← getGoals).isEmpty then
        evalTactic (← `(tactic| first | rfl | assumption | omega | bv_omega))
  | none =>
      let saved ← saveState
      let goalHyps ← collectRelevantHyps g {} #[] useAllFlag
      runBvOmegaPasses includeUInt goalHyps
      if (← getGoals).isEmpty then return
      if !useAllFlag then
        let allHyps ← g.withContext do collectRelevantHyps g {} #[] true
        if allHyps.size > goalHyps.size then
          saved.restore
          runBvOmegaPasses includeUInt allHyps
          if (← getGoals).isEmpty then return
      evalTactic (← `(tactic| first | rfl | assumption | omega | bv_omega))

/-- Normalize `BitVec` comparisons, `setWidth`, `truncate`, nonneg `signExtend`, shifts
`<<<`/`>>>`, `OfNat`/`BitVec.ofNat`, `&&& 1`, and chained/modular subtractions (`(a - b) - c`),
assert goal-relevant `BitVec.isLt` bounds, and close via `omega`. Supports `c0_bv_omega`,
`c0_bv_omega [h1, ...]`, and `c0_bv_omega [*]`. -/
syntax "c0_bv_omega" : tactic
syntax "c0_bv_omega" " [" "*" "]" : tactic
syntax "c0_bv_omega" " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| c0_bv_omega) => runBvOmegaCore false false none
  | `(tactic| c0_bv_omega [*]) => runBvOmegaCore false true none
  | `(tactic| c0_bv_omega [ $hs,* ]) => runBvOmegaCore false false (some hs.getElems)

/-- 32-bit/UInt arithmetic variant of `c0_bv_omega`, handling `BitVec 32` (`setWidth 64` /
`truncate 32` roundtrips, shifts, masked bounds) as well as `UInt8` / `UInt32` / `UInt64`
arithmetic and casts (`std3` axioms only). -/
syntax "c0_bv32_omega" : tactic
syntax "c0_bv32_omega" " [" "*" "]" : tactic
syntax "c0_bv32_omega" " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| c0_bv32_omega) => runBvOmegaCore true false none
  | `(tactic| c0_bv32_omega [*]) => runBvOmegaCore true true none
  | `(tactic| c0_bv32_omega [ $hs,* ]) => runBvOmegaCore true false (some hs.getElems)

/-! ### `state_frame` and `state_frame!` -/

private meta partial def unfoldOnceForFrame? (ty : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let fn := ty.getAppFn
  let some nm := fn.constName? | return none
  if nm == ``wp || nm == ``PrefixAgrees || nm == ``SliceAgrees ||
      nm == ``OutsideSliceAgrees || nm == ``And || nm == ``Eq || nm == ``Exists ||
      nm == ``LE.le || nm == ``LT.lt then
    return none
  let some (.defnInfo _) := (← getEnv).find? nm | return none
  let some unfolded ← unfoldDefinition? ty | return none
  let uFn := unfolded.getAppFn
  let some uNm := uFn.constName? | return none
  let env ← getEnv
  if uNm == ``And || isStructure env uNm || uNm == ``AgreesExcept ||
      uNm == ``PreservesCoreSlice || uNm == ``Eq then
    return some unfolded
  return none

private meta partial def collectPropProj (e ty : Lean.Expr) (depth : Nat)
    (acc : Array (Lean.Expr × Lean.Expr)) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let acc0 := acc.push (e, ty)
  if depth == 0 then return acc0
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    let acc1 ← collectPropProj (mkApp3 (.const ``And.left []) a b e) a (depth - 1) acc0
    collectPropProj (mkApp3 (.const ``And.right []) a b e) b (depth - 1) acc1
  else
    let env ← getEnv
    let some structNm := ty.getAppFn.constName? | return acc0
    if isStructure env structNm then
      let mut out := acc0
      for fieldNm in getStructureFields env structNm do
        try
          let pe ← mkProjection e fieldNm
          let pty ← inferType pe
          if ← isProp pty then
            out ← collectPropProj pe pty (depth - 1) out
        catch _ => pure ()
      return out
    else if let some unfolded ← unfoldOnceForFrame? ty then
      collectPropProj e unfolded (depth - 1) acc0
    else
      return acc0

private meta def buildPropProjCache : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let mut acc : Array (Lean.Expr × Lean.Expr) := #[]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if ← isProp decl.type then
        acc ← collectPropProj decl.toExpr decl.type 4 acc
  return acc

private meta def tryCloseWithCache (cache : Array (Lean.Expr × Lean.Expr)) (mvar : MVarId) :
    MetaM Bool :=
  mvar.withContext do
    let target ← instantiateMVars (← mvar.getType)
    for (pExpr, pTy) in cache do
      if ← withoutModifyingState (isDefEq pTy target) then
        if ← isDefEq pTy target then
          mvar.assign pExpr
          return true
      if target.eq?.isSome then
        if let some (_, pLhs, pRhs) := pTy.eq? then
          let symmTy ← mkEq pRhs pLhs
          if ← withoutModifyingState (isDefEq symmTy target) then
            if ← isDefEq symmTy target then
              mvar.assign (← mkEqSymm pExpr)
              return true
    return false

private meta def tryCloseFrameLeaf (cache : Array (Lean.Expr × Lean.Expr)) (aggressive : Bool)
    (mvar : MVarId) : TacticM Bool := do
  let saved ← saveState
  setGoals [mvar]
  try
    try
      evalTactic (← `(tactic| rfl))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
    try
      evalTactic (← `(tactic| trivial))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
    for g in (← getGoals) do
      if !(← tryCloseWithCache cache g) then
        pure ()
    let rem ← (← getGoals).filterM fun g => return !(← g.isAssigned)
    setGoals rem
    if (← getGoals).isEmpty then return true
    try
      evalTactic (← `(tactic|
        simp (config := { zeta := true, zetaDelta := true }) only
          [List.length_set, List.length_append, List.length_cons, List.length_nil,
           List.length_map, List.length_take, List.length_drop, List.length_replicate,
           LeanQbe.T.AgreesExcept, LeanQbe.T.PreservesCoreSlice]))
    catch _ => pure ()
    try
      evalTactic (← `(tactic|
        first
        | rfl
        | trivial
        | apply LeanQbe.T.AgreesExcept.refl
        | apply LeanQbe.T.PreservesCoreSlice.refl
        | apply LeanQbe.T.PrefixAgrees.refl
        | apply LeanQbe.T.SliceAgrees.refl
        | apply LeanQbe.T.OutsideSliceAgrees.refl))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
    let mut stillOpen : List MVarId := []
    for g in (← getGoals) do
      if !(← g.isAssigned) then
        if !(← tryCloseWithCache cache g) then
          stillOpen := stillOpen ++ [g]
    setGoals stillOpen
    if stillOpen.isEmpty then return true
    if aggressive then
      try
        evalTactic (← `(tactic| omega))
        if (← getGoals).isEmpty then return true
      catch _ => pure ()
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

private meta partial def splitFrameGoal (cache : Array (Lean.Expr × Lean.Expr)) (depth : Nat)
    (aggressive : Bool) (mvar : MVarId) : TacticM (List MVarId) := do
  if ← tryCloseFrameLeaf cache aggressive mvar then
    return []
  if depth == 0 then
    return [mvar]
  let target ← mvar.withContext do instantiateMVars (← mvar.getType)
  if target.isAppOfArity ``And 2 then
    setGoals [mvar]
    evalTactic (← `(tactic| apply And.intro))
    let sub ← getGoals
    let mut rem : List MVarId := []
    for g in sub do
      rem := rem ++ (← splitFrameGoal cache (depth - 1) aggressive g)
    return rem
  let env ← getEnv
  if let some structNm := target.getAppFn.constName? then
    if isStructure env structNm && (← mvar.withContext (isProp target)) then
      setGoals [mvar]
      evalTactic (← `(tactic| constructor))
      let sub ← getGoals
      let mut rem : List MVarId := []
      for g in sub do
        rem := rem ++ (← splitFrameGoal cache (depth - 1) aggressive g)
      return rem
  if let some unfolded ← mvar.withContext (unfoldOnceForFrame? target) then
    let mvar' ← mvar.change unfolded
    return ← splitFrameGoal cache (depth - 1) aggressive mvar'
  return [mvar]

private meta def runStateFrame (aggressive : Bool) : TacticM Unit := do
  let (g, tail) := match ← getGoals with
    | g :: gs => (g, gs)
    | [] => unreachable!
  let cache ← g.withContext buildPropProjCache
  let rem ← splitFrameGoal cache 8 aggressive g
  setGoals (rem ++ tail)

/-- Recursively splits `∧` and `Prop`-valued `structure`s (such as `LengthsOk` and
`Preserves*`) and closes preserved field obligations (`{ s with f := v }.g = s.g`,
`List.length_set`, `AgreesExcept`, and projected hypotheses from the local context),
leaving any non-trivial obligations as focused subgoals. -/
elab "state_frame" : tactic => runStateFrame false

/-- Variant of `state_frame` that also invokes `omega` on any remaining numeric leaf
obligations (e.g. index upper bounds). -/
elab "state_frame!" : tactic => runStateFrame true

/-! ## 4. Structured While-State and Array-Cursor Combinators -/

theorem ArrayCursorInv.ofNat_add_one {w : Nat} (k : Nat) :
    BitVec.ofNat w k + (1 : BitVec w) = BitVec.ofNat w (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, bv_c0_toNat_ofNat_lit]
  rw [← Nat.add_mod]

theorem ArrayCursorInv.toNat_ofNat_lt {w k : Nat} (hk : k < 2 ^ w) :
    (BitVec.ofNat w k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- Alias for `LeanQbe.T.wp_while_state` exported in `ProofKit`. -/
theorem c0_while_state {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hentry : ∀ J : Cont ts, (∀ st m', Inv st m' → J (proj st) m') →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (m' : Mem 64), Inv st m' →
      (∀ st' m'', μ st' < μ st → Inv st' m'' → J (proj st') m'') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) m') :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  LeanQbe.T.wp_while_state proj μ Inv hentry hbody

/-- `wp_while_state` with pure invariant `Inv : α → Prop` separated from spatial
separation-logic state `MemPred : α → Mem 64 → Prop` and caller frame `R`. -/
theorem wp_while_state_mem {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat)
    (Inv : α → Prop) (MemPred : α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont ts,
      (∀ st ml, Inv st → (MemPred st ⋆ R) ml → J (proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (ml : Mem 64),
      Inv st → (MemPred st ⋆ R) ml →
      (∀ st' ml', μ st' < μ st → Inv st' → (MemPred st' ⋆ R) ml' → J (proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  LeanQbe.T.wp_while_state proj μ (fun st ml => Inv st ∧ (MemPred st ⋆ R) ml)
    (fun J hJ => hentry J fun st ml hi hm => hJ st ml ⟨hi, hm⟩)
    (fun J st ml ⟨hi, hm⟩ hJ => hbody J st ml hi hm fun st' ml' hlt hi' hm' =>
      hJ st' ml' hlt ⟨hi', hm'⟩)

/-- `wp_while_state` carrying transitive `AgreesExcept mask s₀ (snap st)` and
`(MemPred (snap st) ⋆ R) ml` framing automatically across iterations. -/
theorem wp_while_state_agrees {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {σ : Type} (mask : σ → σ) (s₀ : σ) (MemPred : σ → Mem 64 → Prop) (R : Mem 64 → Prop)
    {α : Type _} (snap : α → σ) (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Prop)
    (hentry : ∀ J : Cont ts,
      (∀ st ml, AgreesExcept mask s₀ (snap st) → Inv st →
        (MemPred (snap st) ⋆ R) ml → J (proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (ml : Mem 64),
      AgreesExcept mask s₀ (snap st) → Inv st → (MemPred (snap st) ⋆ R) ml →
      (∀ st' ml', μ st' < μ st → AgreesExcept mask (snap st) (snap st') → Inv st' →
        (MemPred (snap st') ⋆ R) ml' → J (proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  LeanQbe.T.wp_while_state proj μ
    (fun st ml => AgreesExcept mask s₀ (snap st) ∧ Inv st ∧ (MemPred (snap st) ⋆ R) ml)
    (fun J hJ => hentry J fun st ml hag hi hm => hJ st ml ⟨hag, hi, hm⟩)
    (fun J st ml ⟨hag, hi, hm⟩ hJ =>
      hbody J st ml hag hi hm fun st' ml' hlt hstep hi' hm' =>
        hJ st' ml' hlt ⟨AgreesExcept.trans hag hstep, hi', hm'⟩)

/-! ### `ArrayCursorInv` and `ArrayMutCursorInv` combinators -/

namespace ArrayCursorInv

theorem init {β : Type} {α : Type _} {lo hi : Nat} {xs : List β}
    {Inv : Nat → α → Prop} {st : α}
    (hle : lo ≤ hi) (hi_len : hi ≤ xs.length) (hinv : Inv lo st) :
    ArrayCursorInv lo hi xs Inv lo st :=
  ⟨Nat.le_refl lo, hle, hi_len, hinv⟩

theorem step {β : Type} {α : Type _} {lo hi idx : Nat} {xs : List β}
    {Inv : Nat → α → Prop} {st st' : α}
    (h : ArrayCursorInv lo hi xs Inv idx st) (hlt : idx < hi) (hinv : Inv (idx + 1) st') :
    ArrayCursorInv lo hi xs Inv (idx + 1) st' :=
  ⟨Nat.le_trans h.lo_le (Nat.le_succ idx), hlt, h.hi_le, hinv⟩

theorem idx_lt_length {β : Type} {α : Type _} {lo hi idx : Nat} {xs : List β}
    {Inv : Nat → α → Prop} {st : α}
    (h : ArrayCursorInv lo hi xs Inv idx st) (hlt : idx < hi) : idx < xs.length :=
  Nat.lt_of_lt_of_le hlt h.hi_le

theorem done {β : Type} {α : Type _} {lo hi idx : Nat} {xs : List β}
    {Inv : Nat → α → Prop} {st : α}
    (h : ArrayCursorInv lo hi xs Inv idx st) (hne : ¬ idx < hi) :
    idx = hi ∧ Inv hi st := by
  have heq : idx = hi := Nat.le_antisymm h.idx_le (Nat.not_lt.mp hne)
  subst heq
  exact ⟨rfl, h.inv⟩

end ArrayCursorInv

namespace ArrayMutCursorInv

theorem init {β : Type} {α : Type _} {lo hi : Nat} {xs₀ : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (hle : lo ≤ hi) (hi_len : hi ≤ xs₀.length) (hinv : Inv lo xs₀ st) :
    ArrayMutCursorInv lo hi xs₀ Inv lo xs₀ st :=
  ⟨Nat.le_refl lo, hle, hi_len, rfl, OutsideSliceAgrees.refl lo lo xs₀, hinv⟩

theorem step_set {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st st' : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) (hlt : idx < hi) (v : β)
    (hinv : Inv (idx + 1) (xs.set idx v) st') :
    ArrayMutCursorInv lo hi xs₀ Inv (idx + 1) (xs.set idx v) st' := by
  have hmono : OutsideSliceAgrees lo (idx + 1) xs₀ xs :=
    h.outside_eq.mono (Nat.le_refl lo) (Nat.le_succ idx)
  refine ⟨Nat.le_trans h.lo_le (Nat.le_succ idx), hlt, h.hi_le, ?_, ?_, hinv⟩
  · simpa [List.length_set] using h.len_eq
  · exact hmono.update_set v h.lo_le (Nat.lt_succ_self idx)

theorem step_skip {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st st' : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) (hlt : idx < hi)
    (hinv : Inv (idx + 1) xs st') :
    ArrayMutCursorInv lo hi xs₀ Inv (idx + 1) xs st' :=
  ⟨Nat.le_trans h.lo_le (Nat.le_succ idx), hlt, h.hi_le, h.len_eq,
    h.outside_eq.mono (Nat.le_refl lo) (Nat.le_succ idx), hinv⟩

theorem idx_lt_length {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) (hlt : idx < hi) : idx < xs.length := by
  rw [h.len_eq]
  exact Nat.lt_of_lt_of_le hlt h.hi_le

theorem get_unwritten {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) {k : Nat} (hk : idx ≤ k) :
    xs[k]? = xs₀[k]? :=
  h.outside_eq.getElem?_ge hk

theorem prefix_eq {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) :
    PrefixAgrees lo xs₀ xs :=
  h.outside_eq.to_prefix

theorem done {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) (hne : ¬ idx < hi) :
    idx = hi ∧ xs.length = xs₀.length ∧ OutsideSliceAgrees lo hi xs₀ xs ∧ Inv hi xs st := by
  have heq : idx = hi := Nat.le_antisymm h.idx_le (Nat.not_lt.mp hne)
  subst heq
  exact ⟨rfl, h.len_eq, h.outside_eq, h.inv⟩

end ArrayMutCursorInv

/-- Read-only 64-bit array-cursor loop rule (`i64 :: tsRest`), managing index bounds
`ArrayCursorInv lo hi xs Inv idx st` and decreasing measure `hi - idx`. -/
theorem wp_while_cursor64 {Γ : Env} {rs tsRest : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [i64 :: tsRest] → Blocks Val Cont rs [i64 :: tsRest]}
    {entry : Tup Cont [i64 :: tsRest] → Expr Val Cont rs}
    {β : Type} {α : Type _} (lo hi : Nat) (xs : List β) (proj : α → Tup Val tsRest)
    (Inv : Nat → α → Prop) (MemPred : Nat → α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont (i64 :: tsRest),
      (∀ idx st ml, ArrayCursorInv lo hi xs Inv idx st → (MemPred idx st ⋆ R) ml →
        J (BitVec.ofNat 64 idx, proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont (i64 :: tsRest)) (idx : Nat) (st : α) (ml : Mem 64),
      ArrayCursorInv lo hi xs Inv idx st → (MemPred idx st ⋆ R) ml →
      (∀ idx' st' ml', hi - idx' < hi - idx → ArrayCursorInv lo hi xs Inv idx' st' →
        (MemPred idx' st' ⋆ R) ml' → J (BitVec.ofNat 64 idx', proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (BitVec.ofNat 64 idx, proj st)) ml) :
    wp Γ Q X (.group (sig := [i64 :: tsRest]) bodies entry) m :=
  LeanQbe.T.wp_while_state
    (α := Nat × α)
    (fun p => (BitVec.ofNat 64 p.1, proj p.2))
    (fun p => hi - p.1)
    (fun p ml => ArrayCursorInv lo hi xs Inv p.1 p.2 ∧ (MemPred p.1 p.2 ⋆ R) ml)
    (fun J hJ => hentry J fun idx st ml hinv hm => hJ (idx, st) ml ⟨hinv, hm⟩)
    (fun J ⟨idx, st⟩ ml ⟨hinv, hm⟩ hJ =>
      hbody J idx st ml hinv hm fun idx' st' ml' hlt hinv' hm' =>
        hJ (idx', st') ml' hlt ⟨hinv', hm'⟩)

/-- Read-only 32-bit array-cursor loop rule (`i32 :: tsRest`), managing index bounds
`ArrayCursorInv lo hi xs Inv idx st` and decreasing measure `hi - idx`. -/
theorem wp_while_cursor32 {Γ : Env} {rs tsRest : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [i32 :: tsRest] → Blocks Val Cont rs [i32 :: tsRest]}
    {entry : Tup Cont [i32 :: tsRest] → Expr Val Cont rs}
    {β : Type} {α : Type _} (lo hi : Nat) (xs : List β) (proj : α → Tup Val tsRest)
    (Inv : Nat → α → Prop) (MemPred : Nat → α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont (i32 :: tsRest),
      (∀ idx st ml, ArrayCursorInv lo hi xs Inv idx st → (MemPred idx st ⋆ R) ml →
        J (BitVec.ofNat 32 idx, proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont (i32 :: tsRest)) (idx : Nat) (st : α) (ml : Mem 64),
      ArrayCursorInv lo hi xs Inv idx st → (MemPred idx st ⋆ R) ml →
      (∀ idx' st' ml', hi - idx' < hi - idx → ArrayCursorInv lo hi xs Inv idx' st' →
        (MemPred idx' st' ⋆ R) ml' → J (BitVec.ofNat 32 idx', proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (BitVec.ofNat 32 idx, proj st)) ml) :
    wp Γ Q X (.group (sig := [i32 :: tsRest]) bodies entry) m :=
  LeanQbe.T.wp_while_state
    (α := Nat × α)
    (fun p => (BitVec.ofNat 32 p.1, proj p.2))
    (fun p => hi - p.1)
    (fun p ml => ArrayCursorInv lo hi xs Inv p.1 p.2 ∧ (MemPred p.1 p.2 ⋆ R) ml)
    (fun J hJ => hentry J fun idx st ml hinv hm => hJ (idx, st) ml ⟨hinv, hm⟩)
    (fun J ⟨idx, st⟩ ml ⟨hinv, hm⟩ hJ =>
      hbody J idx st ml hinv hm fun idx' st' ml' hlt hinv' hm' =>
        hJ (idx', st') ml' hlt ⟨hinv', hm'⟩)

/-- Mutating 64-bit array-cursor loop rule (`i64 :: tsRest`) carrying `ArrayMutCursorInv`
(length preservation and `OutsideSliceAgrees lo idx xs₀ xs`) and separated memory
predicate `MemPred idx xs st ⋆ R`. -/
theorem wp_while_mut_cursor64 {Γ : Env} {rs tsRest : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [i64 :: tsRest] → Blocks Val Cont rs [i64 :: tsRest]}
    {entry : Tup Cont [i64 :: tsRest] → Expr Val Cont rs}
    {β : Type} {α : Type _} (lo hi : Nat) (xs₀ : List β) (proj : α → Tup Val tsRest)
    (Inv : Nat → List β → α → Prop) (MemPred : Nat → List β → α → Mem 64 → Prop)
    (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont (i64 :: tsRest),
      (∀ idx xs st ml, ArrayMutCursorInv lo hi xs₀ Inv idx xs st →
        (MemPred idx xs st ⋆ R) ml → J (BitVec.ofNat 64 idx, proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont (i64 :: tsRest)) (idx : Nat) (xs : List β) (st : α) (ml : Mem 64),
      ArrayMutCursorInv lo hi xs₀ Inv idx xs st → (MemPred idx xs st ⋆ R) ml →
      (∀ idx' xs' st' ml', hi - idx' < hi - idx →
        ArrayMutCursorInv lo hi xs₀ Inv idx' xs' st' → (MemPred idx' xs' st' ⋆ R) ml' →
        J (BitVec.ofNat 64 idx', proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (BitVec.ofNat 64 idx, proj st)) ml) :
    wp Γ Q X (.group (sig := [i64 :: tsRest]) bodies entry) m :=
  LeanQbe.T.wp_while_state
    (α := Nat × List β × α)
    (fun p => (BitVec.ofNat 64 p.1, proj p.2.2))
    (fun p => hi - p.1)
    (fun p ml => ArrayMutCursorInv lo hi xs₀ Inv p.1 p.2.1 p.2.2 ∧
      (MemPred p.1 p.2.1 p.2.2 ⋆ R) ml)
    (fun J hJ => hentry J fun idx xs st ml hinv hm => hJ (idx, xs, st) ml ⟨hinv, hm⟩)
    (fun J ⟨idx, xs, st⟩ ml ⟨hinv, hm⟩ hJ =>
      hbody J idx xs st ml hinv hm fun idx' xs' st' ml' hlt hinv' hm' =>
        hJ (idx', xs', st') ml' hlt ⟨hinv', hm'⟩)

section AxiomAudit
open Lean Elab Command

/-- Compile-time check that every listed declaration uses only
`[propext, Classical.choice, Quot.sound]`. -/
syntax "check_std_axioms! " ident+ : command

elab_rules : command
  | `(check_std_axioms! $ids:ident*) => do
    let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
    for id in ids do
      let nm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let axs ← liftCoreM <| Lean.collectAxioms nm
      let bad := axs.filter (!allowed.contains ·)
      if !bad.isEmpty then
        throwError "check_std_axioms!: `{nm}` depends on disallowed axioms: {bad.toList}"

end AxiomAudit

end

end LeanQbe.T.ProofKit
