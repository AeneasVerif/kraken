prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.BitVec.Basic
import Lean
import KrakenStdlibCandidates.Init.Data.Int.Lemmas
import KrakenStdlibCandidates.Init.Data.Nat.Bitwise.Lemmas


/-!
# Grind homomorphism and bitwise lemmas for Int.
-/

open Lean Meta
set_option autoImplicit true

namespace Int

@[grind_homo] theorem hShiftLeft_eq (a : Int) (n : Nat) : a <<< n = a * 2^n := Int.shiftLeft_eq a n
@[grind_homo] theorem hShiftRight_eq (a : Int) (n : Nat) : a >>> n = a / 2^n := Int.shiftRight_eq_div_pow a n
attribute [grind_homo] Int.shiftRight_eq_div_pow Int.shiftLeft_eq
def testBit : Int → Nat → Bool
  | Int.ofNat n, i => Nat.testBit n i
  | Int.negSucc n, i => !Nat.testBit n i

def land : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

instance : HAnd Int Int Int where hAnd := Int.land

def lor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc b => .negSucc (b ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .negSucc (a ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

instance : HOr Int Int Int where hOr := Int.lor

def lxor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

instance : HXor Int Int Int where hXor := Int.lxor

def lnot : Int → Int
  | ofNat n => negSucc n
  | negSucc n => ofNat n

instance : Complement Int where complement := Int.lnot

@[ext] theorem eq_of_testBit_eq {a b : Int} (h : ∀ i, a.testBit i = b.testBit i) : a = b := by
  have aux (x y : Nat) : x < 2 ^ (x + y + 1) := Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right Nat.two_pos (
    by omega))
  have aux2 (x y : Nat) : y < 2 ^ (x + y + 1) := Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right Nat.two_pos (
    by omega))
  cases a with
  | ofNat a' => cases b with
    | ofNat b' => congr; exact Nat.eq_of_testBit_eq h
    | negSucc b' =>
      have hi := h (a' + b' + 1); revert hi; simp [testBit, Nat.testBit_lt_two_pow (aux a' b'), Nat.testBit_lt_two_pow (aux2 a' b')]
  | negSucc a' => cases b with
    | ofNat b' =>
      have hi := h (a' + b' + 1); revert hi; simp [testBit, Nat.testBit_lt_two_pow (aux a' b'), Nat.testBit_lt_two_pow (aux2 a' b')]
    | negSucc b' => congr; ext i; have hi := h i; revert hi; simp [testBit]

theorem land_mask_eq_mod (a m : Int) (h1 : m ≥ 0) (h2 : (m &&& (m + 1)) = 0) : a &&& m = a % (m + 1) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  have h2_nat : m &&& (m + 1) = 0 := Int.ofNat.inj h2
  cases a with
  | ofNat a => exact congrArg Int.ofNat (Nat.land_mask_eq_mod a m h2_nat)
  | negSucc a =>
    have negSucc_emod_ofNat_add_one (m b : Nat) :
      Int.negSucc m % Int.ofNat (b + 1) = Int.ofNat (b - m % (b + 1)) := by
      change Int.subNatNat (b + 1) (m % (b + 1) + 1) = _
      have : m % (b + 1) < b + 1 := Nat.mod_lt _ (by omega)
      rw [Int.subNatNat_of_le (by omega)]
      congr 1; omega
    change Int.ofNat (m ^^^ (a &&& m)) = Int.negSucc a % Int.ofNat (m + 1)
    rw [Nat.submask_xor_eq_sub _ m h2_nat,  negSucc_emod_ofNat_add_one a m,  Nat.land_mask_eq_mod a m h2_nat]

theorem lnot_def (x : Int) : ~~~x = -x - 1 := by
  cases x <;> (dsimp [Complement.complement, Int.lnot]; omega)

theorem lnot_lnot (x : Int) : ~~~(~~~x) = x := by simp [lnot_def]; try omega
theorem succ_lnot (x : Int) : (~~~x) + 1 = -x := by simp [lnot_def]; try omega
theorem lnot_pred (x : Int) : ~~~(x - 1) = -x := by simp [lnot_def]; try omega
theorem lnot_eq_pred_opp (x : Int) : ~~~x = -x - 1 :=
  by simp [lnot_def]; try omega
theorem opp_lnot (x : Int) : -(~~~x) = x + 1 := by simp [lnot_def]; try omega
theorem lnot_opp (x : Int) : ~~~(-x) = x - 1 := by simp [lnot_def]; try omega
theorem sub_lnot_r (x y : Int) : x - ~~~y = x + y + 1 :=
  by simp [lnot_def]; try omega
theorem pred_sub_lnot_r (x y : Int) : x - ~~~y - 1 = x + y :=
  by simp [lnot_def]; try omega
theorem add_lnot_r (x y : Int) : x + ~~~y = x - y - 1 :=
  by simp [lnot_def]; try omega
theorem succ_add_lnot_r (x y : Int) : x + ~~~y + 1 = x - y :=
  by simp [lnot_def]; try omega
theorem lnot_sub (x y : Int) : ~~~(x - y) = ~~~x + y :=
  by simp [lnot_def]; try omega

@[grind_homo]
theorem testBit_ofNat (n : Nat) (i : Nat) :
  (n : Int).testBit i = n.testBit i := rfl

@[grind_homo] theorem testBit_lnot (a : Int) (i : Nat) : (~~~a).testBit i = !(a.testBit i) := by
  cases a <;> (dsimp [Complement.complement, Int.lnot, Int.testBit]; try (cases Nat.testBit _ i) <;> rfl)

@[grind_homo] theorem testBit_land (a b : Int) (i : Nat) : (a &&& b).testBit i = (a.testBit i && b.testBit i) := by
  change Int.testBit (Int.land a b) i = _
  cases a <;> cases b <;> simp [Int.land, Int.testBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;> rename_i a' b' <;> cases Nat.testBit a' i <;> cases Nat.testBit b' i <;> rfl

@[grind_homo] theorem testBit_lor (a b : Int) (i : Nat) : (a ||| b).testBit i = (a.testBit i || b.testBit i) := by
  change (Int.lor a b).testBit i = _
  cases a <;> cases b <;>
    simp only [Int.lor, Int.testBit, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and] <;>
    cases Nat.testBit _ i <;> cases Nat.testBit _ i <;> rfl

@[grind_homo] theorem testBit_lxor (a b : Int) (i : Nat) : (a ^^^ b).testBit i = (a.testBit i != b.testBit i) := by
  change Int.testBit (Int.lxor a b) i = _
  cases a <;> cases b <;> simp [Int.lxor, Int.testBit, Nat.testBit_xor] <;>
  rename_i a' b' <;> cases Nat.testBit a' i <;> cases Nat.testBit b' i <;> rfl

@[grind_homo] theorem mod_add_mod_l (a b n : Int) : (a % n + b) % n = (a + b) % n := by simp
@[grind_homo] theorem mod_add_mod_r (a b n : Int) : (a + b % n) % n = (a + b) % n := by simp
@[grind_homo] theorem mod_sub_mod_l (a b n : Int) : (a % n - b) % n = (a - b) % n := by simp
@[grind_homo] theorem mod_sub_mod_r (a b n : Int) : (a - b % n) % n = (a - b) % n := by simp
@[grind_homo] theorem mod_mul_mod_l (a b n : Int) : ((a % n) * b) % n = (a * b) % n := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
@[grind_homo] theorem mod_mul_mod_r (a b n : Int) : (a * (b % n)) % n = (a * b) % n := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

theorem land_ofNat_negSucc (a b : Nat) : ((a : Int) &&& Int.negSucc b) = (a ^^^ (a &&& b) : Nat) := rfl
theorem land_negSucc_ofNat (a b : Nat) : (Int.negSucc a &&& (b : Int)) = (b ^^^ (a &&& b) : Nat) := rfl
theorem land_negSucc_negSucc (a b : Nat) : (Int.negSucc a &&& Int.negSucc b) = Int.negSucc (a ||| b) := rfl

theorem lor_ofNat_negSucc (a b : Nat) : ((a : Int) ||| Int.negSucc b) = Int.negSucc (b ^^^ (a &&& b)) := rfl
theorem lor_negSucc_ofNat (a b : Nat) : (Int.negSucc a ||| (b : Int)) = Int.negSucc (a ^^^ (a &&& b)) := rfl
theorem lor_negSucc_negSucc (a b : Nat) : (Int.negSucc a ||| Int.negSucc b) = Int.negSucc (a &&& b) := rfl

theorem lxor_ofNat_negSucc (a b : Nat) : ((a : Int) ^^^ Int.negSucc b) = Int.negSucc (a ^^^ b) := rfl
theorem lxor_negSucc_ofNat (a b : Nat) : (Int.negSucc a ^^^ (b : Int)) = Int.negSucc (a ^^^ b) := rfl
theorem lxor_negSucc_negSucc (a b : Nat) : (Int.negSucc a ^^^ Int.negSucc b) = (a ^^^ b : Nat) := rfl

@[grind_homo] theorem land_ofNat (a b : Nat) : (a : Int) &&& (b : Int) = (a &&& b : Nat) := rfl
@[grind_homo] theorem lor_ofNat (a b : Nat) : (a : Int) ||| (b : Int) = (a ||| b : Nat) := rfl
@[grind_homo] theorem lxor_ofNat (a b : Nat) : (a : Int) ^^^ (b : Int) = (a ^^^ b : Nat) := rfl

theorem land_mask_eq_mod_shift (a m : Int) (k n : Nat) (h_le : n ≤ k) (h : m = (2^k : Int) - (2^n : Int)) :
    a &&& m = ((a >>> n) % (2^(k - n) : Int)) <<< n := by
  subst h
  rw [show (2^k:Int) - (2^n:Int) = Int.ofNat _ from (Int.ofNat_sub (Nat.pow_le_pow_right (
    by decide) h_le)).symm]
  cases a with
  | ofNat a => exact congrArg Int.ofNat (Nat.land_mask_eq_mod_shift _ _ _ h_le)
  | negSucc a =>
    change Int.ofNat _ = _
    rw [show (2 ^ (k - n) : Int) = Int.ofNat _ from rfl,  Int.negSucc_shiftRight,  Int.emod_negSucc]
    change _ = Int.subNatNat (2^(k-n)) (Nat.succ ((a >>> n) % 2^(k-n))) <<< n
    rw [Int.subNatNat_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))]
    change _ = Int.ofNat _
    rw [show _ - Nat.succ ((a >>> n) % 2^(k-n)) = 2^(k-n) - 1 - ((a >>> n) % 2^(k-n))
 by omega]
    exact congrArg Int.ofNat (Nat.neg_land_mask_eq_mod_shift _ _ _ h_le)

theorem land_upper_mask_eq (a m : Int) (k n : Nat) (h_le : n ≤ k) (h2 : m + (2^n : Int) = (2^k : Int)) : a &&& m = ((a >>> n) % (2^(k - n) : Int)) <<< n := by
  apply Int.land_mask_eq_mod_shift _ _ _ _ h_le; omega

theorem land_upper_mask_eq_div (a m : Int) (k n : Nat) (h_le : n ≤ k) (h2 : m + (2^n : Int) = (2^k : Int)) :
  a &&& m = ((a / (2^n : Int)) % (2^(k - n) : Int)) * (2^n : Int) := by
  rw [land_upper_mask_eq a m k n h_le h2]
  rw [Int.shiftRight_eq_div_pow, Int.shiftLeft_eq]
  rfl

theorem land_neg_power_eq (a m : Int) (n : Nat) (h : m = -(2^n : Int)) : a &&& m = a >>> n <<< n := by
  subst h
  change a &&& (-((2^n : Nat) : Int)) = _
  rw [show (-((2^n : Nat) : Int)) = Int.negSucc (2^n - 1) by
  have := Nat.two_pow_pos n; omega]
  cases a with
  | ofNat x =>
    apply congrArg Int.ofNat
    rw [Nat.and_two_pow_sub_one_eq_mod]
    ext i
    simp [Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    grind
  | negSucc x =>
    have lemma5 (x n : Nat) : x ||| (2^n - 1) = ((x >>> n) + 1) <<< n - 1 := by
      have h_pos : 0 < 2^n := Nat.two_pow_pos n
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_mul, Nat.one_mul]
      have h2 : (x / 2^n) * 2^n + 2^n - 1 = (x / 2^n) * 2^n + (2^n - 1) :=
        by omega
      rw [h2, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt (by omega)]
      ext i
      rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow_sub_one]
      by_cases h_i : i < n
      · simp [h_i]
      · simp [h_i, Nat.testBit_shiftLeft, Nat.not_lt.mp h_i]
        rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
        congr 1; omega
    exact congrArg Int.negSucc (lemma5 x n)

theorem lor_add_land (a b : Int) : (a ||| b) + (a &&& b) = a + b := by
  cases a <;> cases b <;> rename_i a b
  · change (↑(a ||| b) : Int) + ↑(a &&& b) = ↑a + ↑b;
    have := Nat.lor_add_land a b; omega
  · change negSucc (b ^^^ (a &&& b)) + ↑(a ^^^ (a &&& b)) = ↑a + negSucc b;
    have := Nat.xor_and_add_self_left a b; have := Nat.xor_and_add_self_right a b; omega
  · change negSucc (a ^^^ (a &&& b)) + ↑(b ^^^ (a &&& b)) = negSucc a + ↑b;
    have := Nat.xor_and_add_self_left a b; have := Nat.xor_and_add_self_right a b; omega
  · change negSucc (a &&& b) + negSucc (a ||| b) = negSucc a + negSucc b;
    have := Nat.lor_add_land a b; omega

theorem xor_add_land (a b : Int) : (a ^^^ b) + (a &&& b) = a ||| b := by
  cases a <;> cases b
  · rename_i a b
    change (↑(a ^^^ b) : Int) + ↑(a &&& b) = ↑(a ||| b)
    have := Nat.xor_add_land a b; omega
  · rename_i a b
    change negSucc (a ^^^ b) + ↑(a ^^^ (a &&& b)) = negSucc (b ^^^ (a &&& b))
    have := Nat.xor_and_add_xor a b; omega
  · rename_i a b
    change negSucc (a ^^^ b) + ↑(b ^^^ (a &&& b)) = negSucc (a ^^^ (a &&& b))
    have := Nat.xor_and_add_xor a b; omega
  · rename_i a b
    change ↑(a ^^^ b) + negSucc (a ||| b) = negSucc (a &&& b)
    have := Nat.xor_add_land a b; omega

theorem lor_sub_land (a b : Int) : (a ||| b) - (a &&& b) = a ^^^ b := by
  have := xor_add_land a b; omega

theorem lor_eq_add_sub_land (x y : Int) : x ||| y = x + y - (x &&& y) := by
  have := lor_add_land x y; omega

theorem xor_eq_add_sub_land (x y : Int) : x ^^^ y = x + y - 2 * (x &&& y) := by
  have := lor_add_land x y; have := xor_add_land x y; omega


theorem sub_lor_l_same_r (x y : Int) : (x ||| y) - y = x - (x &&& y) := by
  have h1 := lor_add_land x y; omega

theorem sub_land_same_l (x y : Int) : x - (x &&& y) = (x ||| y) - y := by
  have h1 := lor_add_land x y; omega

theorem sub_2lor_lxor (x y : Int) : 2 * (x ||| y) - (x ^^^ y) = x + y := by
  have := lor_add_land x y; have := xor_add_land x y; omega

theorem sub_2land_lxor (x y : Int) : x + y - (x ^^^ y) = 2 * (x &&& y) := by
  have := xor_add_land x y; have := lor_add_land x y; omega

@[grind_homo] theorem testBit_neg_one (i : Nat) : (-1 : Int).testBit i = true := by
  change (Int.negSucc 0).testBit i = true; simp [Int.testBit]

@[grind_homo] theorem testBit_zero (i : Nat) : (0 : Int).testBit i = false := by
  change Nat.testBit 0 i = false; simp


@[simp, grind =] theorem zero_and (x : Int) : 0 &&& x = 0 := by
  ext i; grind
scoped grind_pattern zero_and => 0 &&& x

@[simp, grind =] theorem and_zero (x : Int) : x &&& 0 = 0 := by
  ext i; grind
scoped grind_pattern and_zero => x &&& 0

theorem lnot_zero : ~~~(0 : Int) = -1 := by rfl
theorem lnot_neg_one : ~~~(-1 : Int) = 0 := by rfl

theorem land_neg_one (x : Int) : x &&& (-1) = x := by
  ext i; grind

theorem neg_one_and (x : Int) : (-1) &&& x = x := by
  ext i; grind

theorem or_zero (x : Int) : x ||| 0 = x := by
  ext i; grind

theorem zero_or (x : Int) : 0 ||| x = x := by
  ext i; grind

theorem or_neg_one (x : Int) : x ||| (-1) = -1 := by
  ext i; grind

theorem neg_one_or (x : Int) : (-1) ||| x = -1 := by
  ext i; grind

@[simp, grind =] theorem xor_zero (x : Int) : x ^^^ 0 = x := by
  ext i; simp [Int.testBit_lxor, testBit_zero]
scoped grind_pattern xor_zero => x ^^^ 0

@[simp, grind =] theorem zero_xor (x : Int) : 0 ^^^ x = x := by
  ext i; simp [Int.testBit_lxor, testBit_zero]
scoped grind_pattern zero_xor => 0 ^^^ x

@[simp, grind =] theorem xor_self (x : Int) : x ^^^ x = 0 := by
  ext i; grind
scoped grind_pattern xor_self => x ^^^ x

@[simp, grind =] theorem xor_neg_one (x : Int) : x ^^^ -1 = ~~~x := by
  ext i; simp [Int.testBit_lxor, testBit_neg_one, Int.testBit_lnot]
scoped grind_pattern xor_neg_one => x ^^^ -1

@[simp, grind =] theorem neg_one_xor (x : Int) : -1 ^^^ x = ~~~x := by
  ext i; simp [Int.testBit_lxor, testBit_neg_one, Int.testBit_lnot]
scoped grind_pattern neg_one_xor => -1 ^^^ x

theorem not_and (x y : Int) : ~~~(x &&& y) = ~~~x ||| ~~~y := by
  ext i; simp [testBit_lnot, testBit_land, testBit_lor]

theorem not_or (x y : Int) : ~~~(x ||| y) = ~~~x &&& ~~~y := by
  ext i; simp [testBit_lnot, testBit_land, testBit_lor]

theorem not_xor_left (x y : Int) : ~~~(x ^^^ y) = ~~~x ^^^ y := by
  ext i; simp [testBit_lnot, testBit_lxor]

theorem not_xor_right (x y : Int) : ~~~(x ^^^ y) = x ^^^ ~~~y := by
  ext i; simp [testBit_lnot, testBit_lxor]

theorem xor_not_not (x y : Int) : ~~~x ^^^ ~~~y = x ^^^ y := by
  ext i; simp [testBit_lnot, testBit_lxor]

attribute [grind_homo] ofNat_toNat
attribute [grind_homo] toNat_sub'
attribute [grind_homo] lnot_def

end Int
