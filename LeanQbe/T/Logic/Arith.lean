module

public import LeanQbe.T.OpsLemmas

/-!
# Big-integer, signed multiplication, and scalar bitvector arithmetic (`T4`)

* Limb representations (`limbsVal`, `limbsArg`) and algebraic carry/multiply step lemmas
  (`add128_combine`, `mac_combine`, `add_limb_step`, `mul_addc_step`, `carry_zero_of_lt`,
  `mac_bound`) that avoid `omega` recursion blowup on coefficients `≥ 2^128` (§0d).
* Signed widening multiplication identity `smulw_toInt` (from `T1` review `#18` #7) and its
  `ediv`/`emod` corollaries (`smulw_hi_toInt`, `smulw_lo_toNat`).
* Bitvector extension, truncation, subtraction, and `CmpOp` evaluation lemmas.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Multi-limb arithmetic and `grind`-friendly helpers (no `omega` at `≥ 2^128`) -/

/-- Little-endian positional value of `n`-bit limbs. -/
def limbsVal {n : Nat} : List (BitVec n) → Nat
  | [] => 0
  | a :: as => a.toNat + 2 ^ n * limbsVal as

/-- Little-endian positional value of operand limbs. -/
def limbsArg {n : Nat} : List (Arg Val (.bits n)) → Nat
  | [] => 0
  | a :: as => a.val.toNat + 2 ^ n * limbsArg as

@[simp, grind =] theorem limbsVal_nil {n : Nat} : limbsVal (n := n) [] = 0 := rfl
@[simp, grind =] theorem limbsVal_cons {n : Nat} (a : BitVec n) (as : List (BitVec n)) :
    limbsVal (a :: as) = a.toNat + 2 ^ n * limbsVal as := rfl

@[simp, grind =] theorem limbsArg_nil {n : Nat} : limbsArg (n := n) [] = 0 := rfl
@[simp, grind =] theorem limbsArg_cons {n : Nat} (a : Arg Val (.bits n)) (as : List (Arg Val (.bits n))) :
    limbsArg (a :: as) = a.val.toNat + 2 ^ n * limbsArg as := rfl

theorem limbsVal_append {n : Nat} (xs ys : List (BitVec n)) :
    limbsVal (xs ++ ys) = limbsVal xs + 2 ^ (n * xs.length) * limbsVal ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, limbsVal_cons, List.length_cons, ih]
    rw [show n * (xs.length + 1) = n + n * xs.length by rw [Nat.mul_succ, Nat.add_comm],
      Nat.pow_add]
    rw [Nat.mul_add, ← Nat.mul_assoc]
    ac_rfl

theorem limbsArg_eq_limbsVal {n : Nat} (xs : List (Arg Val (.bits n))) :
    limbsArg xs = limbsVal (xs.map Arg.val) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem limbsVal_lt_pow {n : Nat} : ∀ (xs : List (BitVec n)), limbsVal xs < 2 ^ (n * xs.length)
  | [] => by simp
  | x :: xs => by
    simp only [limbsVal_cons, List.length_cons]
    have hx : x.toNat < 2 ^ n := x.isLt
    have hxs : limbsVal xs < 2 ^ (n * xs.length) := limbsVal_lt_pow xs
    have h2 : 2 ^ n * (limbsVal xs + 1) ≤ 2 ^ n * 2 ^ (n * xs.length) := Nat.mul_le_mul_left _ hxs
    rw [Nat.mul_add, Nat.mul_one] at h2
    rw [show n * (xs.length + 1) = n + n * xs.length by rw [Nat.mul_succ, Nat.add_comm],
      Nat.pow_add]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hx _) (Nat.add_comm (2 ^ n) _ ▸ h2)

/-- If `k * B + s = rhs` and `rhs < B`, then `k = 0`. -/
theorem drop_high_carry_eq_zero {k B s rhs : Nat} (h : k * B + s = rhs) (hlt : rhs < B) :
    k = 0 := by
  cases k with
  | zero => rfl
  | succ k' =>
    have hge : B ≤ (k' + 1) * B := Nat.le_mul_of_pos_left B (Nat.succ_pos k')
    omega

/-- If `k * B + s = rhs` and `rhs < B`, then `s = rhs`. -/
theorem drop_high_carry {k B s rhs : Nat} (h : k * B + s = rhs) (hlt : rhs < B) :
    s = rhs := by
  have hk := drop_high_carry_eq_zero h hlt
  subst hk; simpa using h

/-- If `c.toNat * B + rem = rhs` and `rhs < B`, then the carry `c` must be `false`. -/
theorem carry_zero_of_lt {c : Bool} {B rem rhs : Nat} (_hB : 0 < B)
    (heq : c.toNat * B + rem = rhs) (hlt : rhs < B) : c = false :=
  Bool.toNat_eq_zero.mp (drop_high_carry_eq_zero heq hlt)

/-- `Nat` form of `carry_zero_of_lt`. -/
theorem carry_toNat_zero_of_lt {c : Bool} {B rem rhs : Nat} (hB : 0 < B)
    (heq : c.toNat * B + rem = rhs) (hlt : rhs < B) : c.toNat = 0 := by
  rw [carry_zero_of_lt hB heq hlt]; rfl

theorem mul_lt_pow2_two {n : Nat} (a b : BitVec n) :
    a.toNat * b.toNat < 2 ^ n * 2 ^ n :=
  Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt

/-- Generic 2-limb subtraction borrow identity (`ult128` via `subb` + `subb`, avoiding `omega` at `2^128`). -/
theorem subb2_borrow_eq_decide {n : Nat} {a0 a1 b0 b1 d0 d1 : Nat} {ci w0 w1 : Bool}
    (hd0 : d0 < 2 ^ n) (hd1 : d1 < 2 ^ n)
    (h0 : d0 + b0 + ci.toNat = a0 + w0.toNat * 2 ^ n)
    (h1 : d1 + b1 + w0.toNat = a1 + w1.toNat * 2 ^ n) :
    w1 = decide (a1 * 2 ^ n + a0 < b1 * 2 ^ n + b0 + ci.toNat) := by
  have hD : d1 * 2 ^ n + d0 < 2 ^ n * 2 ^ n :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hd0 _) (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hd1)
  have hsum : (d1 * 2 ^ n + d0) + (b1 * 2 ^ n + b0 + ci.toNat) =
      (a1 * 2 ^ n + a0) + w1.toNat * (2 ^ n * 2 ^ n) := by
    calc (d1 * 2 ^ n + d0) + (b1 * 2 ^ n + b0 + ci.toNat)
        = (d1 + b1) * 2 ^ n + (d0 + b0 + ci.toNat) := by simp only [Nat.add_mul]; ac_rfl
      _ = (d1 + b1) * 2 ^ n + (a0 + w0.toNat * 2 ^ n) := by rw [h0]
      _ = (d1 + b1 + w0.toNat) * 2 ^ n + a0 := by simp only [Nat.add_mul]; ac_rfl
      _ = (a1 + w1.toNat * 2 ^ n) * 2 ^ n + a0 := by rw [h1]
      _ = (a1 * 2 ^ n + a0) + w1.toNat * (2 ^ n * 2 ^ n) := by
          simp only [Nat.add_mul, Nat.mul_assoc]; ac_rfl
  cases w1
  · simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hsum
    have hle : b1 * 2 ^ n + b0 + ci.toNat ≤ a1 * 2 ^ n + a0 := by
      have := Nat.le_add_left (b1 * 2 ^ n + b0 + ci.toNat) (d1 * 2 ^ n + d0)
      omega
    simp [Nat.not_lt_of_le hle]
  · simp only [Bool.toNat_true, Nat.one_mul] at hsum
    have hlt : a1 * 2 ^ n + a0 < b1 * 2 ^ n + b0 + ci.toNat := by omega
    simp [hlt]

/-- `a * b + c + d < 2^(2n)` for `n`-bit values, proved without `omega` on `2^(2n)`. -/
theorem mac_bound {n : Nat} (a b c d : BitVec n) :
    a.toNat * b.toNat + c.toNat + d.toNat < 2 ^ n * 2 ^ n := by
  have ha : a.toNat ≤ 2 ^ n - 1 := Nat.le_pred_of_lt a.isLt
  have hb : b.toNat ≤ 2 ^ n - 1 := Nat.le_pred_of_lt b.isLt
  have hc : c.toNat ≤ 2 ^ n - 1 := Nat.le_pred_of_lt c.isLt
  have hd : d.toNat ≤ 2 ^ n - 1 := Nat.le_pred_of_lt d.isLt
  have h1 : a.toNat * b.toNat ≤ (2 ^ n - 1) * (2 ^ n - 1) := Nat.mul_le_mul ha hb
  have hp : 1 ≤ (2 ^ n : Nat) := Nat.one_le_pow _ _ (by decide)
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
  rw [hk] at h1 hc hd ⊢
  simp only [Nat.add_sub_cancel] at h1 hc hd
  rw [Nat.succ_mul, Nat.mul_succ]
  omega

/-- Generic 2-limb addition with carry in/out in factored `2 ^ n * 2 ^ n` form (no kernel `2^128` reduction). -/
theorem add2_combine_mul {n : Nat} {a0 a1 b0 b1 s0 s1 : Nat} {ci c0 c1 : Bool}
    (h0 : c0.toNat * 2 ^ n + s0 = a0 + b0 + ci.toNat)
    (h1 : c1.toNat * 2 ^ n + s1 = a1 + b1 + c0.toNat) :
    c1.toNat * (2 ^ n * 2 ^ n) + (s1 * 2 ^ n + s0) =
      (a1 * 2 ^ n + a0) + (b1 * 2 ^ n + b0) + ci.toNat := by
  calc c1.toNat * (2 ^ n * 2 ^ n) + (s1 * 2 ^ n + s0)
      = (c1.toNat * 2 ^ n + s1) * 2 ^ n + s0 := by
          rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    _ = (a1 + b1 + c0.toNat) * 2 ^ n + s0 := by rw [h1]
    _ = (a1 * 2 ^ n + b1 * 2 ^ n) + (c0.toNat * 2 ^ n + s0) := by
          simp only [Nat.add_mul, Nat.add_assoc]
    _ = (a1 * 2 ^ n + b1 * 2 ^ n) + (a0 + b0 + ci.toNat) := by rw [h0]
    _ = (a1 * 2 ^ n + a0) + (b1 * 2 ^ n + b0) + ci.toNat := by ac_rfl

/-- Generic 2-limb addition with carry in/out (prefer `add2_combine_mul`, `add128_combine`, or
`add256_combine` at concrete widths `≥ 128` to avoid kernel `2^128` reduction). -/
theorem add2_combine {n : Nat} {a0 a1 b0 b1 s0 s1 : Nat} {ci c0 c1 : Bool}
    (h0 : c0.toNat * 2 ^ n + s0 = a0 + b0 + ci.toNat)
    (h1 : c1.toNat * 2 ^ n + s1 = a1 + b1 + c0.toNat) :
    c1.toNat * 2 ^ (2 * n) + (s1 * 2 ^ n + s0) =
      (a1 * 2 ^ n + a0) + (b1 * 2 ^ n + b0) + ci.toNat := by
  rw [show 2 * n = n + n by omega, Nat.pow_add]
  exact add2_combine_mul h0 h1

/-- `add2_combine` specialized for 128-bit addition (`n = 64`, arbitrary carry-in) without kernel `2^128` reduction. -/
theorem add128_combine_ci {a0 a1 b0 b1 s0 s1 : Nat} {ci c0 c1 : Bool}
    (h0 : c0.toNat * 2 ^ 64 + s0 = a0 + b0 + ci.toNat)
    (h1 : c1.toNat * 2 ^ 64 + s1 = a1 + b1 + c0.toNat) :
    c1.toNat * 2 ^ 128 + (s1 * 2 ^ 64 + s0) = (a1 * 2 ^ 64 + a0) + (b1 * 2 ^ 64 + b0) + ci.toNat := by
  have h := add2_combine (n := 64) h0 h1
  rwa [show (2 : Nat) ^ (2 * 64) = 2 ^ 128 from congrArg (2 ^ ·) (by decide)] at h

/-- `add2_combine` specialized for 128-bit addition (`n = 64`, `false.toNat` carry-in) without kernel `2^128` reduction. -/
theorem add128_combine {a0 a1 b0 b1 s0 s1 : Nat} {c0 c1 : Bool}
    (h0 : c0.toNat * 2 ^ 64 + s0 = a0 + b0 + false.toNat)
    (h1 : c1.toNat * 2 ^ 64 + s1 = a1 + b1 + c0.toNat) :
    c1.toNat * 2 ^ 128 + (s1 * 2 ^ 64 + s0) = (a1 * 2 ^ 64 + a0) + (b1 * 2 ^ 64 + b0) := by
  have h := add128_combine_ci h0 h1
  rwa [Bool.toNat_false, Nat.add_zero] at h

/-- `add128_combine` when `+ false.toNat` has already been simplified away from `h0`. -/
theorem add128_combine0 {a0 a1 b0 b1 s0 s1 : Nat} {c0 c1 : Bool}
    (h0 : c0.toNat * 2 ^ 64 + s0 = a0 + b0)
    (h1 : c1.toNat * 2 ^ 64 + s1 = a1 + b1 + c0.toNat) :
    c1.toNat * 2 ^ 128 + (s1 * 2 ^ 64 + s0) = (a1 * 2 ^ 64 + a0) + (b1 * 2 ^ 64 + b0) :=
  add128_combine (by simpa using h0) h1

/-- 4-limb 256-bit addition (`n = 64`, arbitrary carry-in) without `omega` or kernel `2^256` reduction. -/
theorem add256_combine_ci {a0 a1 a2 a3 b0 b1 b2 b3 s0 s1 s2 s3 : Nat} {ci c0 c1 c2 c3 : Bool}
    (h0 : c0.toNat * 2 ^ 64 + s0 = a0 + b0 + ci.toNat)
    (h1 : c1.toNat * 2 ^ 64 + s1 = a1 + b1 + c0.toNat)
    (h2 : c2.toNat * 2 ^ 64 + s2 = a2 + b2 + c1.toNat)
    (h3 : c3.toNat * 2 ^ 64 + s3 = a3 + b3 + c2.toNat) :
    c3.toNat * 2 ^ 256 + (s3 * 2 ^ 192 + s2 * 2 ^ 128 + s1 * 2 ^ 64 + s0) =
      (a3 * 2 ^ 192 + a2 * 2 ^ 128 + a1 * 2 ^ 64 + a0) +
      (b3 * 2 ^ 192 + b2 * 2 ^ 128 + b1 * 2 ^ 64 + b0) + ci.toNat := by
  have lo := add128_combine_ci h0 h1
  have hi := add128_combine_ci h2 h3
  have hp192 : (2 : Nat) ^ 128 * 2 ^ 64 = 2 ^ 192 := by
    rw [← Nat.pow_add]
  have hp256 : (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 := by
    rw [← Nat.pow_add]
  calc c3.toNat * 2 ^ 256 + (s3 * 2 ^ 192 + s2 * 2 ^ 128 + s1 * 2 ^ 64 + s0)
      = (c3.toNat * 2 ^ 128 + (s3 * 2 ^ 64 + s2)) * 2 ^ 128 + (s1 * 2 ^ 64 + s0) := by
          rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, hp192, hp256]; ac_rfl
    _ = ((a3 * 2 ^ 64 + a2) + (b3 * 2 ^ 64 + b2) + c1.toNat) * 2 ^ 128 + (s1 * 2 ^ 64 + s0) := by
          rw [hi]
    _ = (a3 * 2 ^ 192 + a2 * 2 ^ 128 + b3 * 2 ^ 192 + b2 * 2 ^ 128) +
          (c1.toNat * 2 ^ 128 + (s1 * 2 ^ 64 + s0)) := by
          simp only [Nat.add_mul, Nat.mul_assoc, hp192]; ac_rfl
    _ = (a3 * 2 ^ 192 + a2 * 2 ^ 128 + b3 * 2 ^ 192 + b2 * 2 ^ 128) +
          ((a1 * 2 ^ 64 + a0) + (b1 * 2 ^ 64 + b0) + ci.toNat) := by
          rw [lo]
    _ = (a3 * 2 ^ 192 + a2 * 2 ^ 128 + a1 * 2 ^ 64 + a0) +
          (b3 * 2 ^ 192 + b2 * 2 ^ 128 + b1 * 2 ^ 64 + b0) + ci.toNat := by ac_rfl

/-- `add256_combine_ci` specialized to zero carry-in (`h0` without `+ ci.toNat`). -/
theorem add256_combine0 {a0 a1 a2 a3 b0 b1 b2 b3 s0 s1 s2 s3 : Nat} {c0 c1 c2 c3 : Bool}
    (h0 : c0.toNat * 2 ^ 64 + s0 = a0 + b0)
    (h1 : c1.toNat * 2 ^ 64 + s1 = a1 + b1 + c0.toNat)
    (h2 : c2.toNat * 2 ^ 64 + s2 = a2 + b2 + c1.toNat)
    (h3 : c3.toNat * 2 ^ 64 + s3 = a3 + b3 + c2.toNat) :
    c3.toNat * 2 ^ 256 + (s3 * 2 ^ 192 + s2 * 2 ^ 128 + s1 * 2 ^ 64 + s0) =
      (a3 * 2 ^ 192 + a2 * 2 ^ 128 + a1 * 2 ^ 64 + a0) +
      (b3 * 2 ^ 192 + b2 * 2 ^ 128 + b1 * 2 ^ 64 + b0) := by
  have h := add256_combine_ci (ci := false) (by simpa using h0) h1 h2 h3
  rwa [Bool.toNat_false, Nat.add_zero] at h

/-- Horner-form 4-limb addition in arbitrary base `B` (matches `limbsVal` directly). -/
theorem add4_base {B a0 a1 a2 a3 b0 b1 b2 b3 s0 s1 s2 s3 : Nat} {c0 c1 c2 c3 : Bool}
    (h0 : c0.toNat * B + s0 = a0 + b0)
    (h1 : c1.toNat * B + s1 = a1 + b1 + c0.toNat)
    (h2 : c2.toNat * B + s2 = a2 + b2 + c1.toNat)
    (h3 : c3.toNat * B + s3 = a3 + b3 + c2.toNat) :
    c3.toNat * (B * (B * (B * B))) + (s0 + B * (s1 + B * (s2 + B * s3))) =
      (a0 + B * (a1 + B * (a2 + B * a3))) + (b0 + B * (b1 + B * (b2 + B * b3))) := by
  calc c3.toNat * (B * (B * (B * B))) + (s0 + B * (s1 + B * (s2 + B * s3)))
      = s0 + B * (s1 + B * (s2 + B * (c3.toNat * B + s3))) := by
          simp only [Nat.mul_add, ← Nat.mul_assoc]; ac_rfl
    _ = s0 + B * (s1 + B * ((c2.toNat * B + s2) + B * (a3 + b3))) := by
          rw [h3]; simp only [Nat.mul_add]; ac_rfl
    _ = s0 + B * ((c1.toNat * B + s1) + B * ((a2 + b2) + B * (a3 + b3))) := by
          rw [h2]; simp only [Nat.mul_add]; ac_rfl
    _ = (c0.toNat * B + s0) + B * ((a1 + b1) + B * ((a2 + b2) + B * (a3 + b3))) := by
          rw [h1]; simp only [Nat.mul_add]; ac_rfl
    _ = (a0 + b0) + B * ((a1 + b1) + B * ((a2 + b2) + B * (a3 + b3))) := by rw [h0]
    _ = (a0 + B * (a1 + B * (a2 + B * a3))) + (b0 + B * (b1 + B * (b2 + B * b3))) := by
          simp only [Nat.mul_add]; ac_rfl

/-- Horner-form 4-limb subtraction with borrow in arbitrary base `B`. -/
theorem sub4_base {B a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 : Nat} {w0 w1 w2 w3 : Bool}
    (h0 : d0 + b0 = a0 + w0.toNat * B)
    (h1 : d1 + b1 + w0.toNat = a1 + w1.toNat * B)
    (h2 : d2 + b2 + w1.toNat = a2 + w2.toNat * B)
    (h3 : d3 + b3 + w2.toNat = a3 + w3.toNat * B) :
    (d0 + B * (d1 + B * (d2 + B * d3))) + (b0 + B * (b1 + B * (b2 + B * b3))) =
      (a0 + B * (a1 + B * (a2 + B * a3))) + w3.toNat * (B * (B * (B * B))) := by
  calc (d0 + B * (d1 + B * (d2 + B * d3))) + (b0 + B * (b1 + B * (b2 + B * b3)))
      = (d0 + b0) + B * ((d1 + b1) + B * ((d2 + b2) + B * (d3 + b3))) := by
          simp only [Nat.mul_add]; ac_rfl
    _ = a0 + B * ((d1 + b1 + w0.toNat) + B * ((d2 + b2) + B * (d3 + b3))) := by
          rw [h0]; simp only [Nat.mul_add]; ac_rfl
    _ = a0 + B * (a1 + B * ((d2 + b2 + w1.toNat) + B * (d3 + b3))) := by
          rw [h1]; simp only [Nat.mul_add]; ac_rfl
    _ = a0 + B * (a1 + B * (a2 + B * (d3 + b3 + w2.toNat))) := by
          rw [h2]; simp only [Nat.mul_add]; ac_rfl
    _ = a0 + B * (a1 + B * (a2 + B * (a3 + w3.toNat * B))) := by rw [h3]
    _ = (a0 + B * (a1 + B * (a2 + B * a3))) + w3.toNat * (B * (B * (B * B))) := by
          simp only [Nat.mul_add, ← Nat.mul_assoc]; ac_rfl

/-- `subb2_borrow_eq_decide` specialized for 128-bit comparison (`n = 64`, `false.toNat` borrow-in). -/
theorem subb128_borrow_eq_decide {a0 a1 b0 b1 d0 d1 : BitVec 64} {w0 w1 : Bool}
    (h0 : d0.toNat + b0.toNat + false.toNat = a0.toNat + w0.toNat * 2 ^ 64)
    (h1 : d1.toNat + b1.toNat + w0.toNat = a1.toNat + w1.toNat * 2 ^ 64) :
    w1 = decide (a1.toNat * 2 ^ 64 + a0.toNat < b1.toNat * 2 ^ 64 + b0.toNat) := by
  have h := subb2_borrow_eq_decide (n := 64) d0.isLt d1.isLt h0 h1
  rw [Bool.toNat_false, Nat.add_zero] at h
  exact h

/-- `subb128_borrow_eq_decide` when `+ false.toNat` has already been simplified away from `h0`. -/
theorem subb128_borrow_eq_decide0 {a0 a1 b0 b1 d0 d1 : BitVec 64} {w0 w1 : Bool}
    (h0 : d0.toNat + b0.toNat = a0.toNat + w0.toNat * 2 ^ 64)
    (h1 : d1.toNat + b1.toNat + w0.toNat = a1.toNat + w1.toNat * 2 ^ 64) :
    w1 = decide (a1.toNat * 2 ^ 64 + a0.toNat < b1.toNat * 2 ^ 64 + b0.toNat) :=
  subb128_borrow_eq_decide (by simpa using h0) h1

/-- Generic inductive limb-addition step for `n`-bit limbs at index `k`. -/
theorem add_limb_step {n k : Nat} {a b s ss as bs co : Nat} {ci c' : Bool}
    (h0 : c'.toNat * 2 ^ n + s = a + b + ci.toNat)
    (hrest : ss + co * 2 ^ (n * k) = as + bs + c'.toNat) :
    (s + 2 ^ n * ss) + co * 2 ^ (n * (k + 1)) =
      (a + 2 ^ n * as) + (b + 2 ^ n * bs) + ci.toNat := by
  rw [show n * (k + 1) = n * k + n by rw [Nat.mul_succ], Nat.pow_add]
  calc (s + 2 ^ n * ss) + co * (2 ^ (n * k) * 2 ^ n)
      = s + 2 ^ n * (ss + co * 2 ^ (n * k)) := by
          rw [Nat.mul_add, Nat.mul_comm (2 ^ (n * k)) (2 ^ n), ← Nat.mul_assoc,
            Nat.mul_comm co (2 ^ n), Nat.mul_assoc, Nat.add_assoc]
    _ = s + 2 ^ n * (as + bs + c'.toNat) := by rw [hrest]
    _ = (c'.toNat * 2 ^ n + s) + 2 ^ n * as + 2 ^ n * bs := by
          simp only [Nat.mul_add]; rw [Nat.mul_comm (2 ^ n) c'.toNat]; ac_rfl
    _ = (a + 2 ^ n * as) + (b + 2 ^ n * bs) + ci.toNat := by
          rw [h0]; ac_rfl

/-- Algebraic multiply-accumulate identity `a * b + c + d = hi2 * 2^n + lo2` (with carries `x1, x2`
proved zero via `mac_bound` instead of `omega` on `2^128`). -/
theorem mac_combine {n : Nat} {a b c d : BitVec n} {lo hi lo1 hi1 lo2 hi2 : Nat}
    {c1 x1 c2 x2 : Bool}
    (hm : hi * 2 ^ n + lo = a.toNat * b.toNat)
    (he1 : c1.toNat * 2 ^ n + lo1 = lo + c.toNat)
    (he2 : x1.toNat * 2 ^ n + hi1 = hi + c1.toNat)
    (he3 : c2.toNat * 2 ^ n + lo2 = lo1 + d.toNat)
    (he4 : x2.toNat * 2 ^ n + hi2 = hi1 + c2.toNat) :
    hi2 * 2 ^ n + lo2 = a.toNat * b.toNat + c.toNat + d.toNat := by
  have hsum : (x1.toNat + x2.toNat) * (2 ^ n * 2 ^ n) + (hi2 * 2 ^ n + lo2) =
      a.toNat * b.toNat + c.toNat + d.toNat := by
    calc (x1.toNat + x2.toNat) * (2 ^ n * 2 ^ n) + (hi2 * 2 ^ n + lo2)
        = x1.toNat * 2 ^ n * 2 ^ n + ((x2.toNat * 2 ^ n + hi2) * 2 ^ n + lo2) := by
            simp only [Nat.add_mul, Nat.mul_assoc]; ac_rfl
      _ = x1.toNat * 2 ^ n * 2 ^ n + (hi1 * 2 ^ n + (c2.toNat * 2 ^ n + lo2)) := by
            rw [he4]; simp only [Nat.add_mul]; ac_rfl
      _ = (x1.toNat * 2 ^ n + hi1) * 2 ^ n + lo1 + d.toNat := by
            rw [he3, Nat.add_mul]; ac_rfl
      _ = hi * 2 ^ n + (c1.toNat * 2 ^ n + lo1) + d.toNat := by
            rw [he2, Nat.add_mul]; ac_rfl
      _ = hi * 2 ^ n + lo + c.toNat + d.toNat := by
            rw [he1]; ac_rfl
      _ = a.toNat * b.toNat + c.toNat + d.toNat := by rw [hm]
  have hlt := mac_bound a b c d
  have hpos : 0 < 2 ^ n * 2 ^ n := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have hx0 : x1.toNat + x2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos (x1.toNat + x2.toNat) with hz | hp
    · exact hz
    · have hge : 2 ^ n * 2 ^ n ≤ (x1.toNat + x2.toNat) * (2 ^ n * 2 ^ n) :=
        Nat.le_mul_of_pos_left _ hp
      omega
  rw [hx0, Nat.zero_mul, Nat.zero_add] at hsum
  exact hsum

/-- Schoolbook multiply-accumulate step with incoming carry bit (`umulw` + `addc` + `addc`):
`(hi' * 2^n + lo') + co * 2^(2*n) = a * b + acc + ci` (when `ci` is absorbed into `lo`). -/
theorem schoolbook_step {n : Nat} {a b acc lo hi lo' hi' : Nat} {ci c1 co : Bool}
    (hm : hi * 2 ^ n + lo = a * b)
    (h1 : c1.toNat * 2 ^ n + lo' = lo + acc + ci.toNat)
    (h2 : co.toNat * 2 ^ n + hi' = hi + c1.toNat) :
    co.toNat * (2 ^ n * 2 ^ n) + (hi' * 2 ^ n + lo') = a * b + acc + ci.toNat := by
  calc co.toNat * (2 ^ n * 2 ^ n) + (hi' * 2 ^ n + lo')
      = (co.toNat * 2 ^ n + hi') * 2 ^ n + lo' := by
          rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    _ = hi * 2 ^ n + (c1.toNat * 2 ^ n + lo') := by
          rw [h2, Nat.add_mul]; ac_rfl
    _ = hi * 2 ^ n + lo + acc + ci.toNat := by
          rw [h1]; ac_rfl
    _ = a * b + acc + ci.toNat := by rw [hm]

/-- Two-carry-chain schoolbook multiply-accumulate step (`umulw` + `adcx`/`adox`-style
interleaving): low carry `ci1 → co1` threads through the low limb `lo + accLo + ci1`, while high
carry `ci2 → co2` threads independently through the high limb `hi + accHi + ci2`. -/
theorem schoolbook_2carry_step {n : Nat} {a b accLo accHi lo hi lo' hi' : Nat}
    {ci1 ci2 co1 co2 : Bool}
    (hm : hi * 2 ^ n + lo = a * b)
    (h1 : co1.toNat * 2 ^ n + lo' = lo + accLo + ci1.toNat)
    (h2 : co2.toNat * 2 ^ n + hi' = hi + accHi + ci2.toNat) :
    co2.toNat * (2 ^ n * 2 ^ n) + (hi' * 2 ^ n + lo') + co1.toNat * 2 ^ n =
      a * b + (accHi * 2 ^ n + accLo) + ci1.toNat + ci2.toNat * 2 ^ n := by
  calc co2.toNat * (2 ^ n * 2 ^ n) + (hi' * 2 ^ n + lo') + co1.toNat * 2 ^ n
      = (co2.toNat * 2 ^ n + hi') * 2 ^ n + (co1.toNat * 2 ^ n + lo') := by
          rw [Nat.add_mul, Nat.mul_assoc]; ac_rfl
    _ = (hi + accHi + ci2.toNat) * 2 ^ n + (lo + accLo + ci1.toNat) := by rw [h2, h1]
    _ = (hi * 2 ^ n + lo) + (accHi * 2 ^ n + accLo) + ci1.toNat + ci2.toNat * 2 ^ n := by
          simp only [Nat.add_mul]; ac_rfl
    _ = a * b + (accHi * 2 ^ n + accLo) + ci1.toNat + ci2.toNat * 2 ^ n := by rw [hm]

/-! ## Signed widening multiplication `smulw` (`T1` review `#18` #7) -/

theorem bitvec_split_toNat {n : Nat} (x : BitVec (n + n)) :
    (x.extractLsb' n n).toNat * 2 ^ n + (x.setWidth n).toNat = x.toNat := by
  have hex : (x.extractLsb' n n).toNat = x.toNat / 2 ^ n := by
    simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by
      have := x.isLt; rwa [Nat.pow_add] at this))
  rw [hex, BitVec.toNat_setWidth, Nat.mul_comm]
  exact Nat.div_add_mod x.toNat (2 ^ n)

theorem bitvec_split_toInt {n : Nat} (hn : 1 ≤ n) (x : BitVec (n + n)) :
    (x.extractLsb' n n).toInt * (2 ^ n : Int) + ((x.setWidth n).toNat : Int) = x.toInt := by
  have hhi_msb : (x.extractLsb' n n).msb = x.msb := by
    simp only [BitVec.msb, BitVec.getMsbD, BitVec.getLsbD_extractLsb']
    have hlt1 : 0 < n := by omega
    have hlt2 : 0 < n + n := by omega
    have hlt3 : n - 1 < n := by omega
    have heq1 : n + (n - 1) = n + n - 1 := by omega
    simp [hlt1, hlt2, hlt3, heq1]
  rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond, hhi_msb]
  have hnat : ((x.extractLsb' n n).toNat : Int) * (2 ^ n : Int) + ((x.setWidth n).toNat : Int) =
      (x.toNat : Int) := by
    have h := bitvec_split_toNat x
    have h' : (((x.extractLsb' n n).toNat * 2 ^ n + (x.setWidth n).toNat : Nat) : Int) =
        (x.toNat : Int) := congrArg Int.ofNat h
    push_cast at h'
    exact h'
  cases hx : x.msb
  · simpa using hnat
  · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int] at hnat ⊢
    have hpow : (2 : Int) ^ (n + n) = (2 : Int) ^ n * (2 : Int) ^ n := by rw [← Int.pow_add]
    rw [Int.sub_mul, hpow, ← hnat]
    omega

theorem toInt_emod_two_pow {n : Nat} (a : BitVec n) :
    a.toInt % (2 ^ n : Int) = (a.toNat : Int) := by
  rw [BitVec.toInt_eq_msb_cond]
  have ha : 0 ≤ (a.toNat : Int) ∧ (a.toNat : Int) < (2 ^ n : Int) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast a.isLt⟩
  cases a.msb
  · simp [Int.emod_eq_of_lt ha.1 ha.2]
  · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]
    rw [Int.sub_emod_right, Int.emod_eq_of_lt ha.1 ha.2]

private theorem natAbs_le_of_bounds {x : Int} {B : Nat} (h1 : -(B : Int) ≤ x) (h2 : x ≤ (B : Int)) :
    x.natAbs ≤ B := by
  omega

/-- Exact signed product identity for `OpCode.smulw`:
`hi.toInt * 2^n + lo.toNat = a.toInt * b.toInt` for all `n : Nat`. -/
theorem smulw_toInt {n : Nat} (a b : BitVec n) :
    ((BitVec.ofInt (n + n) (a.toInt * b.toInt)).extractLsb' n n).toInt * (2 ^ n : Int) +
      ((a * b).toNat : Int) = a.toInt * b.toInt := by
  by_cases hn : n = 0
  · subst hn
    have ha : a = 0#0 := Subsingleton.elim a 0#0
    have hb : b = 0#0 := Subsingleton.elim b 0#0
    subst ha; subst hb; rfl
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
    have ha_abs : a.toInt.natAbs ≤ 2 ^ (n - 1) := by
      have h1 : -((2 ^ (n - 1) : Nat) : Int) ≤ a.toInt := by
        simpa [Int.natCast_pow] using a.le_toInt
      have h2 : a.toInt ≤ ((2 ^ (n - 1) : Nat) : Int) := by
        have := a.toInt_lt
        simp only [Int.natCast_pow, Int.cast_ofNat_Int] at this ⊢
        omega
      exact natAbs_le_of_bounds h1 h2
    have hb_abs : b.toInt.natAbs ≤ 2 ^ (n - 1) := by
      have h1 : -((2 ^ (n - 1) : Nat) : Int) ≤ b.toInt := by
        simpa [Int.natCast_pow] using b.le_toInt
      have h2 : b.toInt ≤ ((2 ^ (n - 1) : Nat) : Int) := by
        have := b.toInt_lt
        simp only [Int.natCast_pow, Int.cast_ofNat_Int] at this ⊢
        omega
      exact natAbs_le_of_bounds h1 h2
    have hprod_abs : (a.toInt * b.toInt).natAbs ≤ 2 ^ (n - 1) * 2 ^ (n - 1) := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha_abs hb_abs
    have hpow_lt : 2 ^ (n - 1) * 2 ^ (n - 1) < 2 ^ (n + n - 1) := by
      have h1 : 2 ^ (n - 1) * 2 ^ (n - 1) = 2 ^ ((n - 1) + (n - 1)) := (Nat.pow_add _ _ _).symm
      rw [h1]
      exact Nat.pow_lt_pow_right (by decide) (by omega)
    have hprod_lt : (a.toInt * b.toInt).natAbs < 2 ^ (n + n - 1) :=
      Nat.lt_of_le_of_lt hprod_abs hpow_lt
    have hbounds : -(2 ^ (n + n - 1) : Int) < a.toInt * b.toInt ∧
        a.toInt * b.toInt < (2 ^ (n + n - 1) : Int) := by
      have hlt_int : ((a.toInt * b.toInt).natAbs : Int) < ((2 ^ (n + n - 1) : Nat) : Int) := by
        exact_mod_cast hprod_lt
      simp only [Int.natCast_pow, Int.cast_ofNat_Int] at hlt_int
      omega
    have hp_toInt : (BitVec.ofInt (n + n) (a.toInt * b.toInt)).toInt = a.toInt * b.toInt := by
      rw [BitVec.toInt_ofInt, Int.bmod_def]
      simp only [Int.natCast_pow, Int.cast_ofNat_Int]
      have hpow : (2 : Int) ^ (n + n) = 2 * (2 ^ (n + n - 1) : Int) := by
        rw [show n + n = 1 + (n + n - 1) by omega, Int.pow_add]; simp
      have hhalf : ((2 : Int) ^ (n + n) + 1) / 2 = (2 ^ (n + n - 1) : Int) := by rw [hpow]; omega
      rw [hhalf]
      by_cases hsign : 0 ≤ a.toInt * b.toInt
      · have he : a.toInt * b.toInt % (2 : Int) ^ (n + n) = a.toInt * b.toInt :=
          Int.emod_eq_of_lt hsign (by omega)
        simp [he, hbounds.2]
      · have h1 : 0 ≤ a.toInt * b.toInt + (2 : Int) ^ (n + n) := by omega
        have h2 : a.toInt * b.toInt + (2 : Int) ^ (n + n) < (2 : Int) ^ (n + n) := by omega
        have he : a.toInt * b.toInt % (2 : Int) ^ (n + n) =
            a.toInt * b.toInt + (2 : Int) ^ (n + n) := by
          rw [← Int.add_emod_right, Int.emod_eq_of_lt h1 h2]
        have hge : ¬ a.toInt * b.toInt + (2 : Int) ^ (n + n) < (2 ^ (n + n - 1) : Int) := by omega
        simp [he, hge]
    have hset : (BitVec.ofInt (n + n) (a.toInt * b.toInt)).setWidth n = a * b := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_mul]
      simp only [Int.natCast_pow, Int.cast_ofNat_Int]
      have hdvd : (2 : Int) ^ n ∣ (2 : Int) ^ (n + n) := ⟨2 ^ n, by rw [← Int.pow_add]⟩
      have hmod1 : ((a.toInt * b.toInt) % (2 : Int) ^ (n + n)).toNat % 2 ^ n =
          ((a.toInt * b.toInt) % (2 : Int) ^ n).toNat := by
        have hnn1 : 0 ≤ (a.toInt * b.toInt) % (2 : Int) ^ (n + n) :=
          Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
        have hnn2 : 0 ≤ (a.toInt * b.toInt) % (2 : Int) ^ n :=
          Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
        apply Int.ofNat.inj
        show (((a.toInt * b.toInt % (2 : Int) ^ (n + n)).toNat % 2 ^ n : Nat) : Int) =
          (((a.toInt * b.toInt % (2 : Int) ^ n).toNat : Nat) : Int)
        rw [Int.natCast_emod, Int.natCast_pow, Int.cast_ofNat_Int,
          Int.toNat_of_nonneg hnn1, Int.toNat_of_nonneg hnn2, Int.emod_emod_of_dvd _ hdvd]
      rw [hmod1]
      have hmod2 : (a.toInt * b.toInt) % (2 : Int) ^ n = ((a.toNat * b.toNat : Nat) : Int) % (2 : Int) ^ n := by
        rw [Int.mul_emod, toInt_emod_two_pow, toInt_emod_two_pow, ← Int.natCast_mul]
      rw [hmod2, show (2 : Int) ^ n = ((2 ^ n : Nat) : Int) by push_cast; rfl,
        ← Int.natCast_emod, Int.toNat_natCast]
    have hsplit := bitvec_split_toInt hn1 (BitVec.ofInt (n + n) (a.toInt * b.toInt))
    rwa [hp_toInt, hset] at hsplit

theorem smulw_hi_toInt {n : Nat} (a b : BitVec n) :
    ((BitVec.ofInt (n + n) (a.toInt * b.toInt)).extractLsb' n n).toInt =
      (a.toInt * b.toInt) / (2 ^ n : Int) := by
  have h := smulw_toInt a b
  have hlt : ((a * b).toNat : Int) < (2 ^ n : Int) := by exact_mod_cast (a * b).isLt
  have hnn : 0 ≤ ((a * b).toNat : Int) := Int.natCast_nonneg _
  have hpos : (0 : Int) < (2 ^ n : Int) := Int.pow_pos (by decide)
  symm
  calc (a.toInt * b.toInt) / (2 ^ n : Int)
      = ((BitVec.extractLsb' n n (BitVec.ofInt (n + n) (a.toInt * b.toInt))).toInt * (2 ^ n : Int) +
          ((a * b).toNat : Int)) / (2 ^ n : Int) := congrArg (· / (2 ^ n : Int)) h.symm
    _ = ((BitVec.extractLsb' n n (BitVec.ofInt (n + n) (a.toInt * b.toInt))).toInt * (2 ^ n : Int)) / (2 ^ n : Int) +
          ((a * b).toNat : Int) / (2 ^ n : Int) := Int.add_ediv_of_dvd_left (Int.dvd_mul_left _ _)
    _ = (BitVec.extractLsb' n n (BitVec.ofInt (n + n) (a.toInt * b.toInt))).toInt := by
          rw [Int.mul_ediv_cancel _ (Int.ne_of_gt hpos), Int.ediv_eq_zero_of_lt hnn hlt, Int.add_zero]

theorem smulw_lo_toNat {n : Nat} (a b : BitVec n) :
    ((a * b).toNat : Int) = (a.toInt * b.toInt) % (2 ^ n : Int) := by
  have h := smulw_toInt a b
  have hlt : ((a * b).toNat : Int) < (2 ^ n : Int) := by exact_mod_cast (a * b).isLt
  have hnn : 0 ≤ ((a * b).toNat : Int) := Int.natCast_nonneg _
  rw [← h, Int.mul_add_emod_self_right, Int.emod_eq_of_lt hnn hlt]

/-! ## Scalar BitVec width, arithmetic, and comparison lemmas -/

theorem zext_toNat {m n : Nat} (a : BitVec m) (h : m ≤ n) :
    (a.setWidth n).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) h))

theorem trunc_toNat {m n : Nat} (a : BitVec m) :
    (a.setWidth n).toNat = a.toNat % 2 ^ n :=
  BitVec.toNat_setWidth _ _

theorem sext_toInt {m n : Nat} (a : BitVec m) (_hm : 0 < m) (h : m ≤ n) :
    (a.signExtend n).toInt = a.toInt :=
  BitVec.toInt_signExtend_of_le h

theorem ofBool_toNat {n : Nat} (hn : 0 < n) (b : Bool) :
    (BitVec.ofNat n b.toNat).toNat = b.toNat := by
  rw [BitVec.toNat_ofNat]
  have hpow : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hb := Bool.toNat_le b
  exact Nat.mod_eq_of_lt (by omega)

theorem toNat_sub_one {n : Nat} {a : BitVec n} (ha : a ≠ 0) :
    (a - 1).toNat = a.toNat - 1 := by
  by_cases hn : n = 0
  · subst hn; exact absurd (Subsingleton.elim a 0) ha
  · have ha0 : 0 < a.toNat := by
      rcases Nat.eq_zero_or_pos a.toNat with h0 | hpos
      · exact absurd (BitVec.eq_of_toNat_eq (by simp [h0])) ha
      · exact hpos
    have h1 : (1 : BitVec n).toNat = 1 := by
      simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow hn)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]

theorem toNat_add_of_lt {n : Nat} {a b : BitVec n} (h : a.toNat + b.toNat < 2 ^ n) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_sub_of_le' {n : Nat} {a b : BitVec n} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

@[simp] theorem evalBits_eq_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .eq a b = true ↔ a = b := by
  simp [CmpOp.evalBits]

@[simp] theorem evalBits_ne_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .ne a b = true ↔ a ≠ b := by
  simp [CmpOp.evalBits]

@[simp] theorem evalBits_ult_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .ult a b = true ↔ a.toNat < b.toNat := by
  simp [CmpOp.evalBits, BitVec.ult]

@[simp] theorem evalBits_ule_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .ule a b = true ↔ a.toNat ≤ b.toNat := by
  simp [CmpOp.evalBits, BitVec.ule]

@[simp] theorem evalBits_ugt_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .ugt a b = true ↔ b.toNat < a.toNat := by
  simp [CmpOp.evalBits, BitVec.ult]

@[simp] theorem evalBits_uge_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .uge a b = true ↔ b.toNat ≤ a.toNat := by
  simp [CmpOp.evalBits, BitVec.ule]

@[simp] theorem evalBits_slt_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .slt a b = true ↔ a.toInt < b.toInt := by
  simp [CmpOp.evalBits, BitVec.slt]

@[simp] theorem evalBits_sle_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .sle a b = true ↔ a.toInt ≤ b.toInt := by
  simp [CmpOp.evalBits, BitVec.sle]

@[simp] theorem evalBits_sgt_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .sgt a b = true ↔ b.toInt < a.toInt := by
  simp [CmpOp.evalBits, BitVec.slt]

@[simp] theorem evalBits_sge_iff {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .sge a b = true ↔ b.toInt ≤ a.toInt := by
  simp [CmpOp.evalBits, BitVec.sle]

theorem evalBits_ult_eq_decide {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .ult a b = decide (a.toNat < b.toNat) := by
  simp [CmpOp.evalBits, BitVec.ult]

theorem evalBits_ule_eq_decide {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .ule a b = decide (a.toNat ≤ b.toNat) := by
  simp [CmpOp.evalBits, BitVec.ule]

theorem evalBits_ugt_eq_decide {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .ugt a b = decide (b.toNat < a.toNat) := by
  simp [CmpOp.evalBits, BitVec.ult]

theorem evalBits_uge_eq_decide {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .uge a b = decide (b.toNat ≤ a.toNat) := by
  simp [CmpOp.evalBits, BitVec.ule]

theorem evalBits_slt_eq_decide {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .slt a b = decide (a.toInt < b.toInt) := by
  simp [CmpOp.evalBits, BitVec.slt]

theorem evalBits_sle_eq_decide {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .sle a b = decide (a.toInt ≤ b.toInt) := by
  simp [CmpOp.evalBits, BitVec.sle]

theorem evalBits_sgt_eq_decide {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .sgt a b = decide (b.toInt < a.toInt) := by
  simp [CmpOp.evalBits, BitVec.slt]

theorem evalBits_sge_eq_decide {n : Nat} (a b : BitVec n) :
    CmpOp.evalBits .sge a b = decide (b.toInt ≤ a.toInt) := by
  simp [CmpOp.evalBits, BitVec.sle]

/-! ## Non-`Decidable`-indexed `CmpOp` reductions (for `t_wp_unfold`) -/

theorem evalBits_eq_beq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .eq a b = (a == b) := by
  apply Bool.eq_iff_iff.2; simp [CmpOp.evalBits]

theorem evalBits_ne_bne {n : Nat} (a b : BitVec n) : CmpOp.evalBits .ne a b = (a != b) := by
  apply Bool.eq_iff_iff.2; simp [CmpOp.evalBits]

theorem evalBits_ult_eq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .ult a b = a.ult b := rfl
theorem evalBits_ule_eq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .ule a b = a.ule b := rfl
theorem evalBits_ugt_eq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .ugt a b = b.ult a := rfl
theorem evalBits_uge_eq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .uge a b = b.ule a := rfl
theorem evalBits_slt_eq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .slt a b = a.slt b := rfl
theorem evalBits_sle_eq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .sle a b = a.sle b := rfl
theorem evalBits_sgt_eq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .sgt a b = b.slt a := rfl
theorem evalBits_sge_eq {n : Nat} (a b : BitVec n) : CmpOp.evalBits .sge a b = b.sle a := rfl

theorem evalBool_eq_beq (a b : Bool) : CmpOp.evalBool .eq a b = (a == b) := by
  cases a <;> cases b <;> rfl
theorem evalBool_ne_bne (a b : Bool) : CmpOp.evalBool .ne a b = (a != b) := by
  cases a <;> cases b <;> rfl
theorem evalBool_ult_eq (a b : Bool) : CmpOp.evalBool .ult a b = (!a && b) := rfl
theorem evalBool_ule_eq (a b : Bool) : CmpOp.evalBool .ule a b = (!a || b) := rfl
theorem evalBool_ugt_eq (a b : Bool) : CmpOp.evalBool .ugt a b = (a && !b) := rfl
theorem evalBool_uge_eq (a b : Bool) : CmpOp.evalBool .uge a b = (a || !b) := rfl
theorem evalBool_slt_eq (a b : Bool) : CmpOp.evalBool .slt a b = (a && !b) := rfl
theorem evalBool_sle_eq (a b : Bool) : CmpOp.evalBool .sle a b = (a || !b) := rfl
theorem evalBool_sgt_eq (a b : Bool) : CmpOp.evalBool .sgt a b = (!a && b) := rfl
theorem evalBool_sge_eq (a b : Bool) : CmpOp.evalBool .sge a b = (!a || b) := rfl

/-! ## `sdivDefined` and bitvector division/modulus characterizations -/

private theorem bitVec_allOnes_eq_neg_one (n : Nat) : BitVec.allOnes n = (-1 : BitVec n) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · have hp : 1 < 2 ^ n := Nat.one_lt_two_pow hn
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec n).toNat = 1 := by
      show (BitVec.ofNat n 1).toNat = 1
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
    rw [BitVec.toNat_allOnes, BitVec.toNat_neg, h1, Nat.mod_eq_of_lt (by omega)]

theorem sdivDefined_iff {n : Nat} (a b : BitVec n) :
    sdivDefined a b = true ↔ b ≠ 0 ∧ ¬ (a = BitVec.intMin n ∧ b = -1) := by
  simp only [sdivDefined, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    bne_iff_ne, beq_eq_false_iff_ne, bitVec_allOnes_eq_neg_one]
  constructor
  · rintro ⟨hb, h⟩
    refine ⟨hb, fun ⟨ha, hneg⟩ => ?_⟩
    rcases h with ha' | hb'
    · exact ha' ha
    · exact hb' hneg
  · rintro ⟨hb, h⟩
    refine ⟨hb, ?_⟩
    by_cases ha : a = BitVec.intMin n
    · right; intro hneg; exact h ⟨ha, hneg⟩
    · left; exact ha

theorem sdivDefined_of_pos {n : Nat} {a b : BitVec n} (hb0 : b ≠ 0) (hbpos : 0 ≤ b.toInt) :
    sdivDefined a b = true := by
  rw [sdivDefined_iff]
  refine ⟨hb0, fun ⟨_, hb1⟩ => ?_⟩
  by_cases hn : n = 0
  · subst hn; exact hb0 (Subsingleton.elim b 0)
  · subst hb1
    have h1 : (-1 : BitVec n).toInt = -1 := by
      rw [← bitVec_allOnes_eq_neg_one, BitVec.toInt_allOnes]
      simp [Nat.pos_of_ne_zero hn]
    omega

end LeanQbe.T
