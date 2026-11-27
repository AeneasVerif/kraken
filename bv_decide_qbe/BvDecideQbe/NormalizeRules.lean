module

public import Std.Tactic.BVDecide
public import Lean.Meta.Tactic.BVDecide.Attr

/-!
# Kernel-Proved `BitVec` Normalizer & Ring-Dispatch Rewrite Rules (`E0 / H7` + `H6a`)

Provides zero-axiom (`≤ std3`) `BitVec` rewrite lemmas for:
1. `shiftmul` (`H7`): `x * (1#w <<< s) = x <<< s`, `(1#w <<< s) * x = x <<< s`,
   and `x * BitVec.ofNat w (2 ^ k) = x <<< k` (plus symmetric variants).
2. `opt_share` (`H7`): hoisting shared operands out of `ite` and `cond` branches for
   `+`, `-`, `*`, `&&&`, `|||`, `^^^`, `<<<`, `>>>`, `sshiftRight`, and `sshiftRight'`.
3. Constant `shl → mul` (`H6a`): rewriting constant-amount left shifts into ring
   multiplication so `grind`'s commutative-ring solver can close `fmix32`/`fmix64` cuts.

All `[bv_normalize]` registrations are strictly `scoped` inside `BvDecideQbe.NormalizeRules`
so `bv_decide_qbe`'s default upstream behavior remains 100% compatible with Lean 4's
upstream `bv_decide` test suite.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe.NormalizeRules

/-! ## 1. `shiftmul` Rules (`H7`) -/

theorem mul_one_shiftLeft {w : Nat} (x : BitVec w) (s : Nat) :
    x * (1#w <<< s) = x <<< s := by
  rw [← BitVec.twoPow_eq, BitVec.mul_twoPow_eq_shiftLeft]

theorem one_shiftLeft_mul {w : Nat} (x : BitVec w) (s : Nat) :
    (1#w <<< s) * x = x <<< s := by
  rw [← BitVec.twoPow_eq, BitVec.twoPow_mul_eq_shiftLeft]

theorem mul_one_shiftLeft_bv {w v : Nat} (x : BitVec w) (s : BitVec v) :
    x * (1#w <<< s) = x <<< s := by
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq', ← BitVec.twoPow_eq,
    BitVec.mul_twoPow_eq_shiftLeft]

theorem one_shiftLeft_mul_bv {w v : Nat} (x : BitVec w) (s : BitVec v) :
    (1#w <<< s) * x = x <<< s := by
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq', ← BitVec.twoPow_eq,
    BitVec.twoPow_mul_eq_shiftLeft]

theorem mul_ofNat_one_shiftLeft {w : Nat} (x : BitVec w) (s : Nat) :
    x * ((1 : BitVec w) <<< s) = x <<< s :=
  mul_one_shiftLeft x s

theorem ofNat_one_shiftLeft_mul {w : Nat} (x : BitVec w) (s : Nat) :
    ((1 : BitVec w) <<< s) * x = x <<< s :=
  one_shiftLeft_mul x s

theorem mul_ofNat_one_shiftLeft_bv {w v : Nat} (x : BitVec w) (s : BitVec v) :
    x * ((1 : BitVec w) <<< s) = x <<< s :=
  mul_one_shiftLeft_bv x s

theorem ofNat_one_shiftLeft_mul_bv {w v : Nat} (x : BitVec w) (s : BitVec v) :
    ((1 : BitVec w) <<< s) * x = x <<< s :=
  one_shiftLeft_mul_bv x s

theorem mul_ofNat_two_pow {w : Nat} (x : BitVec w) (k : Nat) :
    x * BitVec.ofNat w (2 ^ k) = x <<< k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod_mod,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem ofNat_two_pow_mul {w : Nat} (x : BitVec w) (k : Nat) :
    BitVec.ofNat w (2 ^ k) * x = x <<< k := by
  rw [BitVec.mul_comm, mul_ofNat_two_pow]

/-! ## 2. Constant `shl → mul` Rules for Ring Dispatch (`H6a`) -/

theorem shiftLeft_nat_eq_mul_ofNat {w : Nat} (x : BitVec w) (k : Nat) :
    x <<< k = x * BitVec.ofNat w (2 ^ k) :=
  (mul_ofNat_two_pow x k).symm

theorem shiftLeft_bv_eq_mul_twoPow {w v : Nat} (x : BitVec w) (s : BitVec v) :
    x <<< s = x * BitVec.twoPow w s.toNat := by
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]

theorem shiftLeft_bv_ofNat_eq_mul_twoPow {w v : Nat} (x : BitVec w) (k : Nat) :
    x <<< BitVec.ofNat v k = x * BitVec.twoPow w (BitVec.ofNat v k).toNat := by
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]

/-! ## 3. `opt_share` Rules for `ite` (`H7`) -/

theorem ite_add_left {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (a + b) (a + d) = a + ite c b d := by
  split <;> rfl

theorem ite_add_right {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (b + a) (d + a) = ite c b d + a := by
  split <;> rfl

theorem ite_sub_left {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (a - b) (a - d) = a - ite c b d := by
  split <;> rfl

theorem ite_sub_right {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (b - a) (d - a) = ite c b d - a := by
  split <;> rfl

theorem ite_mul_left {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (a * b) (a * d) = a * ite c b d := by
  split <;> rfl

theorem ite_mul_right {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (b * a) (d * a) = ite c b d * a := by
  split <;> rfl

theorem ite_and_left {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (a &&& b) (a &&& d) = a &&& ite c b d := by
  split <;> rfl

theorem ite_and_right {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (b &&& a) (d &&& a) = ite c b d &&& a := by
  split <;> rfl

theorem ite_or_left {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (a ||| b) (a ||| d) = a ||| ite c b d := by
  split <;> rfl

theorem ite_or_right {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (b ||| a) (d ||| a) = ite c b d ||| a := by
  split <;> rfl

theorem ite_xor_left {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (a ^^^ b) (a ^^^ d) = a ^^^ ite c b d := by
  split <;> rfl

theorem ite_xor_right {w : Nat} (c : Prop) [Decidable c] (a b d : BitVec w) :
    ite c (b ^^^ a) (d ^^^ a) = ite c b d ^^^ a := by
  split <;> rfl

theorem ite_shiftLeft_nat_left {w : Nat} (c : Prop) [Decidable c]
    (a : BitVec w) (s₁ s₂ : Nat) :
    ite c (a <<< s₁) (a <<< s₂) = a <<< ite c s₁ s₂ := by
  split <;> rfl

theorem ite_shiftLeft_nat_right {w : Nat} (c : Prop) [Decidable c]
    (b d : BitVec w) (s : Nat) :
    ite c (b <<< s) (d <<< s) = ite c b d <<< s := by
  split <;> rfl

theorem ite_shiftLeft_bv_left {w v : Nat} (c : Prop) [Decidable c]
    (a : BitVec w) (s₁ s₂ : BitVec v) :
    ite c (a <<< s₁) (a <<< s₂) = a <<< ite c s₁ s₂ := by
  split <;> rfl

theorem ite_shiftLeft_bv_right {w v : Nat} (c : Prop) [Decidable c]
    (b d : BitVec w) (s : BitVec v) :
    ite c (b <<< s) (d <<< s) = ite c b d <<< s := by
  split <;> rfl

theorem ite_shiftRight_nat_left {w : Nat} (c : Prop) [Decidable c]
    (a : BitVec w) (s₁ s₂ : Nat) :
    ite c (a >>> s₁) (a >>> s₂) = a >>> ite c s₁ s₂ := by
  split <;> rfl

theorem ite_shiftRight_nat_right {w : Nat} (c : Prop) [Decidable c]
    (b d : BitVec w) (s : Nat) :
    ite c (b >>> s) (d >>> s) = ite c b d >>> s := by
  split <;> rfl

theorem ite_shiftRight_bv_left {w v : Nat} (c : Prop) [Decidable c]
    (a : BitVec w) (s₁ s₂ : BitVec v) :
    ite c (a >>> s₁) (a >>> s₂) = a >>> ite c s₁ s₂ := by
  split <;> rfl

theorem ite_shiftRight_bv_right {w v : Nat} (c : Prop) [Decidable c]
    (b d : BitVec w) (s : BitVec v) :
    ite c (b >>> s) (d >>> s) = ite c b d >>> s := by
  split <;> rfl

theorem ite_sshiftRight_left {w : Nat} (c : Prop) [Decidable c]
    (a : BitVec w) (s₁ s₂ : Nat) :
    ite c (BitVec.sshiftRight a s₁) (BitVec.sshiftRight a s₂) =
      BitVec.sshiftRight a (ite c s₁ s₂) := by
  split <;> rfl

theorem ite_sshiftRight_right {w : Nat} (c : Prop) [Decidable c]
    (b d : BitVec w) (s : Nat) :
    ite c (BitVec.sshiftRight b s) (BitVec.sshiftRight d s) =
      BitVec.sshiftRight (ite c b d) s := by
  split <;> rfl

theorem ite_sshiftRight'_left {w v : Nat} (c : Prop) [Decidable c]
    (a : BitVec w) (s₁ s₂ : BitVec v) :
    ite c (BitVec.sshiftRight' a s₁) (BitVec.sshiftRight' a s₂) =
      BitVec.sshiftRight' a (ite c s₁ s₂) := by
  split <;> rfl

theorem ite_sshiftRight'_right {w v : Nat} (c : Prop) [Decidable c]
    (b d : BitVec w) (s : BitVec v) :
    ite c (BitVec.sshiftRight' b s) (BitVec.sshiftRight' d s) =
      BitVec.sshiftRight' (ite c b d) s := by
  split <;> rfl

/-! ## 4. `opt_share` Rules for `cond` (`H7`) -/

theorem cond_add_left {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (a + b) (a + d) = a + cond c b d := by
  cases c <;> rfl

theorem cond_add_right {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (b + a) (d + a) = cond c b d + a := by
  cases c <;> rfl

theorem cond_sub_left {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (a - b) (a - d) = a - cond c b d := by
  cases c <;> rfl

theorem cond_sub_right {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (b - a) (d - a) = cond c b d - a := by
  cases c <;> rfl

theorem cond_mul_left {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (a * b) (a * d) = a * cond c b d := by
  cases c <;> rfl

theorem cond_mul_right {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (b * a) (d * a) = cond c b d * a := by
  cases c <;> rfl

theorem cond_and_left {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (a &&& b) (a &&& d) = a &&& cond c b d := by
  cases c <;> rfl

theorem cond_and_right {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (b &&& a) (d &&& a) = cond c b d &&& a := by
  cases c <;> rfl

theorem cond_or_left {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (a ||| b) (a ||| d) = a ||| cond c b d := by
  cases c <;> rfl

theorem cond_or_right {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (b ||| a) (d ||| a) = cond c b d ||| a := by
  cases c <;> rfl

theorem cond_xor_left {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (a ^^^ b) (a ^^^ d) = a ^^^ cond c b d := by
  cases c <;> rfl

theorem cond_xor_right {w : Nat} (c : Bool) (a b d : BitVec w) :
    cond c (b ^^^ a) (d ^^^ a) = cond c b d ^^^ a := by
  cases c <;> rfl

theorem cond_shiftLeft_nat_left {w : Nat} (c : Bool) (a : BitVec w) (s₁ s₂ : Nat) :
    cond c (a <<< s₁) (a <<< s₂) = a <<< cond c s₁ s₂ := by
  cases c <;> rfl

theorem cond_shiftLeft_nat_right {w : Nat} (c : Bool) (b d : BitVec w) (s : Nat) :
    cond c (b <<< s) (d <<< s) = cond c b d <<< s := by
  cases c <;> rfl

theorem cond_shiftLeft_bv_left {w v : Nat} (c : Bool) (a : BitVec w) (s₁ s₂ : BitVec v) :
    cond c (a <<< s₁) (a <<< s₂) = a <<< cond c s₁ s₂ := by
  cases c <;> rfl

theorem cond_shiftLeft_bv_right {w v : Nat} (c : Bool) (b d : BitVec w) (s : BitVec v) :
    cond c (b <<< s) (d <<< s) = cond c b d <<< s := by
  cases c <;> rfl

theorem cond_shiftRight_nat_left {w : Nat} (c : Bool) (a : BitVec w) (s₁ s₂ : Nat) :
    cond c (a >>> s₁) (a >>> s₂) = a >>> cond c s₁ s₂ := by
  cases c <;> rfl

theorem cond_shiftRight_nat_right {w : Nat} (c : Bool) (b d : BitVec w) (s : Nat) :
    cond c (b >>> s) (d >>> s) = cond c b d >>> s := by
  cases c <;> rfl

theorem cond_shiftRight_bv_left {w v : Nat} (c : Bool) (a : BitVec w) (s₁ s₂ : BitVec v) :
    cond c (a >>> s₁) (a >>> s₂) = a >>> cond c s₁ s₂ := by
  cases c <;> rfl

theorem cond_shiftRight_bv_right {w v : Nat} (c : Bool) (b d : BitVec w) (s : BitVec v) :
    cond c (b >>> s) (d >>> s) = cond c b d >>> s := by
  cases c <;> rfl

theorem cond_sshiftRight_left {w : Nat} (c : Bool) (a : BitVec w) (s₁ s₂ : Nat) :
    cond c (BitVec.sshiftRight a s₁) (BitVec.sshiftRight a s₂) =
      BitVec.sshiftRight a (cond c s₁ s₂) := by
  cases c <;> rfl

theorem cond_sshiftRight_right {w : Nat} (c : Bool) (b d : BitVec w) (s : Nat) :
    cond c (BitVec.sshiftRight b s) (BitVec.sshiftRight d s) =
      BitVec.sshiftRight (cond c b d) s := by
  cases c <;> rfl

theorem cond_sshiftRight'_left {w v : Nat} (c : Bool) (a : BitVec w) (s₁ s₂ : BitVec v) :
    cond c (BitVec.sshiftRight' a s₁) (BitVec.sshiftRight' a s₂) =
      BitVec.sshiftRight' a (cond c s₁ s₂) := by
  cases c <;> rfl

theorem cond_sshiftRight'_right {w v : Nat} (c : Bool) (b d : BitVec w) (s : BitVec v) :
    cond c (BitVec.sshiftRight' b s) (BitVec.sshiftRight' d s) =
      BitVec.sshiftRight' (cond c b d) s := by
  cases c <;> rfl

/-! ## 5. Strictly Scoped `[bv_normalize]` Registration & Programmatic Rule Lists -/

attribute [scoped bv_normalize]
  mul_one_shiftLeft one_shiftLeft_mul
  mul_one_shiftLeft_bv one_shiftLeft_mul_bv
  mul_ofNat_one_shiftLeft ofNat_one_shiftLeft_mul
  mul_ofNat_one_shiftLeft_bv ofNat_one_shiftLeft_mul_bv
  mul_ofNat_two_pow ofNat_two_pow_mul
  ite_add_left ite_add_right ite_sub_left ite_sub_right
  ite_mul_left ite_mul_right ite_and_left ite_and_right
  ite_or_left ite_or_right ite_xor_left ite_xor_right
  ite_shiftLeft_nat_left ite_shiftLeft_nat_right
  ite_shiftLeft_bv_left ite_shiftLeft_bv_right
  ite_shiftRight_nat_left ite_shiftRight_nat_right
  ite_shiftRight_bv_left ite_shiftRight_bv_right
  ite_sshiftRight_left ite_sshiftRight_right
  ite_sshiftRight'_left ite_sshiftRight'_right
  cond_add_left cond_add_right cond_sub_left cond_sub_right
  cond_mul_left cond_mul_right cond_and_left cond_and_right
  cond_or_left cond_or_right cond_xor_left cond_xor_right
  cond_shiftLeft_nat_left cond_shiftLeft_nat_right
  cond_shiftLeft_bv_left cond_shiftLeft_bv_right
  cond_shiftRight_nat_left cond_shiftRight_nat_right
  cond_shiftRight_bv_left cond_shiftRight_bv_right
  cond_sshiftRight_left cond_sshiftRight_right
  cond_sshiftRight'_left cond_sshiftRight'_right

/-- `shiftmul` rewrite theorem names for explicit `simp only` / `bv_cut_qbe`. -/
def shiftmulRuleNames : Array Lean.Name := #[
  ``mul_one_shiftLeft, ``one_shiftLeft_mul,
  ``mul_one_shiftLeft_bv, ``one_shiftLeft_mul_bv,
  ``mul_ofNat_one_shiftLeft, ``ofNat_one_shiftLeft_mul,
  ``mul_ofNat_one_shiftLeft_bv, ``ofNat_one_shiftLeft_mul_bv,
  ``mul_ofNat_two_pow, ``ofNat_two_pow_mul
]

/-- `opt_share` rewrite theorem names (`ite` + `cond`) for explicit `simp only` / `bv_cut_qbe`. -/
def optShareRuleNames : Array Lean.Name := #[
  ``ite_add_left, ``ite_add_right, ``ite_sub_left, ``ite_sub_right,
  ``ite_mul_left, ``ite_mul_right, ``ite_and_left, ``ite_and_right,
  ``ite_or_left, ``ite_or_right, ``ite_xor_left, ``ite_xor_right,
  ``ite_shiftLeft_nat_left, ``ite_shiftLeft_nat_right,
  ``ite_shiftLeft_bv_left, ``ite_shiftLeft_bv_right,
  ``ite_shiftRight_nat_left, ``ite_shiftRight_nat_right,
  ``ite_shiftRight_bv_left, ``ite_shiftRight_bv_right,
  ``ite_sshiftRight_left, ``ite_sshiftRight_right,
  ``ite_sshiftRight'_left, ``ite_sshiftRight'_right,
  ``cond_add_left, ``cond_add_right, ``cond_sub_left, ``cond_sub_right,
  ``cond_mul_left, ``cond_mul_right, ``cond_and_left, ``cond_and_right,
  ``cond_or_left, ``cond_or_right, ``cond_xor_left, ``cond_xor_right,
  ``cond_shiftLeft_nat_left, ``cond_shiftLeft_nat_right,
  ``cond_shiftLeft_bv_left, ``cond_shiftLeft_bv_right,
  ``cond_shiftRight_nat_left, ``cond_shiftRight_nat_right,
  ``cond_shiftRight_bv_left, ``cond_shiftRight_bv_right,
  ``cond_sshiftRight_left, ``cond_sshiftRight_right,
  ``cond_sshiftRight'_left, ``cond_sshiftRight'_right
]

/-- Combined `H7` normalizer rewrite rule names (`shiftmul` + `opt_share`). -/
def normalizeRuleNames : Array Lean.Name :=
  shiftmulRuleNames ++ optShareRuleNames

/-- Constant `shl → mul` rewrite theorem names used before `grind` ring dispatch (`H6a`). -/
def shiftLeftToMulRuleNames : Array Lean.Name := #[
  ``BitVec.shiftLeft_eq_mul_twoPow,
  ``shiftLeft_bv_ofNat_eq_mul_twoPow
]

/-- Constant-folding theorem names turning `BitVec.twoPow` into concrete `BitVec.ofNat`
(paired with `Simp.getSimprocs` for `BitVec.reduceHShiftLeft` / `BitVec.reduceShiftLeft`). -/
def twoPowReduceRuleNames : Array Lean.Name := #[
  ``BitVec.twoPow_eq,
  ``BitVec.toNat_ofNat
]

end BvDecideQbe.NormalizeRules
