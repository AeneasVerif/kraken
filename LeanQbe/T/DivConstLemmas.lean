module

public import LeanQbe.T.DivConst
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.Logic.Arith

/-!
# Correctness of `DivConst` (`O-M1`)

Proves elementary arithmetic soundness of the boolean certificates (`uNoAddCert_sound`,
`uAddShiftCert_sound`, `sPow2Cert_sound`, `sDivCert_sound`) without external-solver or
native tactics, together with WP refinement and relational well-formedness preservation:

* `divConst_wp` / `divConst_wf`
* `Func.divConst_spec` / `Func.divConst_wf`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Elementary Nat/Int/BitVec helpers -/

private theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => have := Nat.two_pow_pos k; rw [Nat.pow_succ]; omega

private theorem mod_eq_of_lt_n {n s : Nat} (hs : s < n) :
    (BitVec.ofNat n s).toNat % n = s := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hs (lt_two_pow_self n)),
    Nat.mod_eq_of_lt hs]

private theorem two_le_of_is32or64 {n : Nat} (h : ¬(!(n == 32 || n == 64)) = true) :
    2 ≤ n := by
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  by_cases h32 : n = 32 <;> by_cases h64 : n = 64 <;> simp_all

private theorem one_toNat_of_two_le {n : Nat} (hn : 2 ≤ n) : (1#n : BitVec n).toNat = 1 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]

private theorem one_ne_zero_of_two_le {n : Nat} (hn : 2 ≤ n) : (1#n : BitVec n) ≠ 0#n := by
  intro h; have hnat := congrArg BitVec.toNat h
  rw [one_toNat_of_two_le hn] at hnat; simp at hnat

private theorem one_ne_allOnes_of_two_le {n : Nat} (hn : 2 ≤ n) :
    (1#n : BitVec n) ≠ BitVec.allOnes n := by
  intro h
  have hpow : 4 ≤ 2 ^ n := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hn)
  have hnat := congrArg BitVec.toNat h
  rw [one_toNat_of_two_le hn, BitVec.toNat_allOnes] at hnat; omega

private theorem twoPow_ne_zero {n m : Nat} (hm : m < n) : BitVec.twoPow n m ≠ 0#n := by
  intro h; have hnat := congrArg BitVec.toNat h
  simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hm)] at hnat

private theorem twoPow_ne_allOnes_of_pos {n m : Nat} (hm1 : 1 ≤ m) (hm : m + 1 < n) :
    BitVec.twoPow n m ≠ BitVec.allOnes n := by
  intro h
  have hlt : 2 ^ m < 2 ^ (n - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hlt2 : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega)
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [show n = 1 + (n - 1) by omega, Nat.pow_add]; simp
  have hnat := congrArg BitVec.toNat h
  rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt2, BitVec.toNat_allOnes] at hnat; omega

private theorem udiv_twoPow_eq {n m : Nat} (hm : m < n) (a : BitVec n) :
    a >>> ((BitVec.ofNat n m).toNat % n) = a / BitVec.twoPow n m := by
  apply BitVec.eq_of_toNat_eq
  rw [mod_eq_of_lt_n hm, BitVec.toNat_ushiftRight, BitVec.toNat_udiv, BitVec.toNat_twoPow,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hm), Nat.shiftRight_eq_div_pow]

private theorem urem_twoPow_eq {n m : Nat} (hn : 2 ≤ n) (hm : m < n) (a : BitVec n) :
    a &&& (BitVec.twoPow n m - 1#n) = a % BitVec.twoPow n m := by
  have h1 := one_toNat_of_two_le hn
  have hpow : (BitVec.twoPow n m).toNat = 2 ^ m := by
    rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hm)]
  have hsub : (BitVec.twoPow n m - 1#n).toNat = 2 ^ m - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hpow, h1]; exact Nat.two_pow_pos m), hpow, h1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_umod, hpow, hsub, Nat.and_two_pow_sub_one_eq_mod]

private theorem sub_udiv_mul_eq_urem {n : Nat} (x d : BitVec n) : x - (x / d) * d = x % d := by
  apply BitVec.eq_of_toNat_eq
  have hle : (x / d).toNat * d.toNat ≤ x.toNat := by
    rw [BitVec.toNat_udiv]; exact Nat.div_mul_le_self _ _
  have hmul : ((x / d) * d).toNat = (x / d).toNat * d.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle x.isLt)]
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (hmul ▸ hle)), BitVec.toNat_umod, hmul,
    BitVec.toNat_udiv]
  have hdiv := Nat.div_add_mod x.toNat d.toNat
  rw [Nat.mul_comm] at hdiv; omega

private theorem sub_sdiv_mul_eq_srem {n : Nat} (x d : BitVec n) :
    x - (x.sdiv d) * d = x.srem d := by
  have hsdiv : x.sdiv d = BitVec.ofInt n (x.toInt.tdiv d.toInt) := by
    apply BitVec.eq_of_toInt_eq; rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt]
  have hsrem : x.srem d = BitVec.ofInt n (x.toInt.tmod d.toInt) := by
    rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]
  have hsum : (x.sdiv d) * d + x.srem d = x := by
    calc (x.sdiv d) * d + x.srem d
        = BitVec.ofInt n (x.toInt.tdiv d.toInt) * BitVec.ofInt n d.toInt +
            BitVec.ofInt n (x.toInt.tmod d.toInt) := by rw [hsdiv, hsrem, BitVec.ofInt_toInt]
      _ = BitVec.ofInt n (d.toInt * x.toInt.tdiv d.toInt + x.toInt.tmod d.toInt) := by
          rw [← BitVec.ofInt_mul, ← BitVec.ofInt_add, Int.mul_comm d.toInt]
      _ = x := by rw [Int.mul_tdiv_add_tmod, BitVec.ofInt_toInt]
  rw [show x - (x.sdiv d) * d = (x.srem d + (x.sdiv d) * d) - (x.sdiv d) * d by
    rw [BitVec.add_comm, hsum], BitVec.add_sub_cancel]

private theorem sdiv_one_eq {n : Nat} (hn : 2 ≤ n) (a : BitVec n) : a.sdiv 1#n = a := by
  have hpowI : (4 : Int) ≤ ((2 ^ n : Nat) : Int) := by
    exact_mod_cast Nat.le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)
  have hmod : (1 : Int) % ((2 ^ n : Nat) : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  have h1bv : (1#n : BitVec n) = BitVec.ofInt n 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [one_toNat_of_two_le hn, BitVec.toNat_ofInt]; exact_mod_cast hmod.symm
  have h1int : (1#n : BitVec n).toInt = 1 := by
    rw [h1bv, BitVec.toInt_ofInt, Int.bmod_def, hmod]; split <;> omega
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, h1int, Int.tdiv_one, ← BitVec.toInt_ofInt, BitVec.ofInt_toInt]

private theorem int_bmod_eq_self {n : Nat} (hn : 1 ≤ n) {z : Int}
    (hlo : -(2 ^ (n - 1) : Int) ≤ z) (hhi : z < (2 ^ (n - 1) : Int)) :
    z.bmod (2 ^ n) = z := by
  have hp : (2 : Int) ^ n = 2 * (2 ^ (n - 1) : Int) := by
    rw [show n = 1 + (n - 1) by omega, Int.pow_add]; simp
  rw [Int.bmod_def, Int.natCast_pow, Int.cast_ofNat_Int, hp]
  by_cases hz : 0 ≤ z
  · rw [Int.emod_eq_of_lt hz (by omega)]; split <;> omega
  · have hm : z % (2 * (2 : Int) ^ (n - 1)) = z + 2 * (2 : Int) ^ (n - 1) := by
      rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hm]; split <;> omega

private theorem int_ediv_pow_add (z : Int) (a b : Nat) :
    (z / (2 ^ a : Int)) / (2 ^ b : Int) = z / (2 ^ (a + b) : Int) := by
  rw [Int.ediv_ediv]
  have hpos : ¬ ((2 : Int) ^ a < 0) := Int.not_lt.mpr (Int.pow_nonneg (by decide))
  simp [hpos, ← Int.pow_add]

private theorem lshr_sign_bit_toInt {n : Nat} (hn : 2 ≤ n) (q : BitVec n) :
    (q >>> (n - 1)).toInt = if q.toInt < 0 then 1 else 0 := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [show n = 1 + (n - 1) by omega, Nat.pow_add]; simp
  have hpow2 : 2 ≤ 2 ^ (n - 1) :=
    Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
  have hqI : (q.toNat : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast q.isLt
  by_cases hge : 2 ^ (n - 1) ≤ q.toNat
  · have hdiv : (q >>> (n - 1)).toNat = 1 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    have hmsb_res : (q >>> (n - 1)).msb = false := by
      rw [BitVec.msb_eq_toNat, hdiv, decide_eq_false_iff_not]; omega
    rw [BitVec.toInt_eq_msb_cond, hmsb_res]; simp only [Bool.false_eq_true, ↓reduceIte, hdiv]
    rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_toNat, decide_eq_true hge]
    simp only [↓reduceIte]; split <;> omega
  · have hdiv : (q >>> (n - 1)).toNat = 0 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by omega)
    have hmsb_res : (q >>> (n - 1)).msb = false := by
      rw [BitVec.msb_eq_toNat, hdiv, decide_eq_false_iff_not]; omega
    rw [BitVec.toInt_eq_msb_cond, hmsb_res]; simp only [Bool.false_eq_true, ↓reduceIte, hdiv]
    rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_toNat, decide_eq_false hge]
    simp only [Bool.false_eq_true, ↓reduceIte]; split <;> omega

/-! ## Unsigned certificate soundness -/

/-- Core Nat theorem underlying both `uNoAddCert` and `uAddShiftCert`. -/
theorem nat_umagic_div_eq {W D M S X : Nat} (hD : 0 < D) (hX : X ≤ W - 1)
    (hlo : S ≤ M * D) (hhi : (W - 1) * (M * D - S) < S) :
    (X * M) / S = X / D := by
  let q := X / D; let r := X % D; let e := M * D - S
  have hdiv : D * q + r = X := Nat.div_add_mod X D
  have hr : r < D := Nat.mod_lt X hD
  have hlo' : q * S ≤ X * M := by
    calc q * S ≤ q * (M * D) := Nat.mul_le_mul_left q hlo
      _ = (D * q) * M := by ac_rfl
      _ ≤ (D * q + r) * M := Nat.mul_le_mul_right M (Nat.le_add_right _ r)
      _ = X * M := by rw [hdiv]
  have hmul_lt : (X * M) * D < ((q + 1) * S) * D := by
    have hXe : X * e < S := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right e hX) hhi
    have hDr : S ≤ (D - r) * S := Nat.le_mul_of_pos_left S (by omega)
    have hXDr : (q + 1) * D = X + (D - r) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q D, ← hdiv]; omega
    calc (X * M) * D = X * (S + e) := by rw [Nat.mul_assoc, (Nat.add_sub_of_le hlo).symm]
      _ = X * S + X * e := Nat.mul_add X S e
      _ < X * S + (D - r) * S := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hXe _) (by omega)
      _ = ((q + 1) * S) * D := by rw [← Nat.add_mul, ← hXDr]; ac_rfl
  exact Nat.div_eq_of_lt_le hlo' (Nat.lt_of_mul_lt_mul_right hmul_lt)

/-- Soundness of `pow2ShiftCert`: `d = 2^m` with `2 ≤ n`, `1 ≤ m < n`, and `d ≠ 0#n`. -/
theorem pow2ShiftCert_sound {n : Nat} {d : BitVec n} {m : Nat}
    (h : pow2ShiftCert n d m = true) :
    2 ≤ n ∧ 1 ≤ m ∧ m < n ∧ d = BitVec.twoPow n m ∧ d ≠ 0#n := by
  simp only [pow2ShiftCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨hn, hm1⟩, hmn⟩, hd⟩
  exact ⟨hn, hm1, hmn, hd, hd ▸ twoPow_ne_zero hmn⟩

/-- Soundness of `uNoAddCert` (`(_, hi) := umulw n x m; q := lshr n hi s`). -/
theorem uNoAddCert_sound {n : Nat} {d : BitVec n} {M s : Nat}
    (hcert : uNoAddCert n d M s = true) (x : BitVec n) :
    d ≠ 0#n ∧
      (BitVec.ofNat n (x.toNat * (BitVec.ofNat n M).toNat / 2 ^ n)) >>>
        ((BitVec.ofNat n s).toNat % n) = x / d := by
  simp only [uNoAddCert, Bool.and_eq_true, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨hn, hsn⟩, hd0⟩, _⟩, hMlt⟩, hlo, hhi⟩
  refine ⟨fun h => by subst h; simp at hd0, ?_⟩
  have hm_toNat : (BitVec.ofNat n M).toNat = M := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hMlt]
  have hhi_lt : x.toNat * M / 2 ^ n < 2 ^ n :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt x.isLt hMlt)
  apply BitVec.eq_of_toNat_eq
  rw [mod_eq_of_lt_n hsn, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hm_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhi_lt, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    nat_umagic_div_eq hd0 (Nat.le_pred_of_lt x.isLt) hlo hhi, BitVec.toNat_udiv]

private theorem nat_add_half_diff {a b : Nat} (h : a ≤ b) :
    a + (b - a) / 2 = (a + b) / 2 := by
  rw [show a + b = (b - a) + 2 * a by omega, Nat.add_mul_div_left (b - a) a (by decide)]; omega

/-- Soundness of `uAddShiftCert` (`umulw + sub + lshr 1 + add + lshr (s - 1)`). -/
theorem uAddShiftCert_sound {n : Nat} {d : BitVec n} {M s : Nat}
    (hcert : uAddShiftCert n d M s = true) (x : BitVec n) :
    let m : BitVec n := BitVec.ofNat n (M - 2 ^ n)
    let hi : BitVec n := BitVec.ofNat n (x.toNat * m.toNat / 2 ^ n)
    let t1 : BitVec n := x - hi
    let t2 : BitVec n := t1 >>> ((1#n : BitVec n).toNat % n)
    let t3 : BitVec n := hi + t2
    d ≠ 0#n ∧ t3 >>> ((BitVec.ofNat n (s - 1)).toNat % n) = x / d := by
  simp only [uAddShiftCert, Bool.and_eq_true, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨⟨hn, hs1⟩, hsn⟩, hd0⟩, hMge⟩, hMlt⟩, hlo, hhi⟩
  refine ⟨fun h => by subst h; simp at hd0, ?_⟩
  have hmlt : M - 2 ^ n < 2 ^ n := by omega
  have hm_eq : M - 2 ^ n + 2 ^ n = M := Nat.sub_add_cancel hMge
  have hm_toNat : (BitVec.ofNat n (M - 2 ^ n)).toNat = M - 2 ^ n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmlt]
  have hhi_toNat : (BitVec.ofNat n (x.toNat * (BitVec.ofNat n (M - 2 ^ n)).toNat / 2 ^ n)).toNat =
      x.toNat * (M - 2 ^ n) / 2 ^ n := by
    rw [hm_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt x.isLt hmlt))]
  have hhi_le_x : x.toNat * (M - 2 ^ n) / 2 ^ n ≤ x.toNat :=
    Nat.div_le_of_le_mul (by
      rw [Nat.mul_comm (2 ^ n) x.toNat]; exact Nat.mul_le_mul_left x.toNat (Nat.le_of_lt hmlt))
  have h1_mod : (1#n : BitVec n).toNat % n = 1 := by
    rw [one_toNat_of_two_le hn, Nat.mod_eq_of_lt (by omega)]
  let m : BitVec n := BitVec.ofNat n (M - 2 ^ n)
  let hi : BitVec n := BitVec.ofNat n (x.toNat * m.toNat / 2 ^ n)
  let t1 : BitVec n := x - hi
  let t2 : BitVec n := t1 >>> ((1#n : BitVec n).toNat % n)
  let t3 : BitVec n := hi + t2
  have ht1 : t1.toNat = x.toNat - hi.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hhi_toNat]; exact hhi_le_x))
  have ht2 : t2.toNat = (x.toNat - hi.toNat) / 2 := by
    show (t1 >>> ((1#n : BitVec n).toNat % n)).toNat = (x.toNat - hi.toNat) / 2
    rw [h1_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht1, Nat.pow_one]
  have ht3 : t3.toNat = (x.toNat * M) / 2 ^ (n + 1) := by
    have ht3_half : t3.toNat = (hi.toNat + x.toNat) / 2 := by
      show (hi + t2).toNat = (hi.toNat + x.toNat) / 2
      rw [BitVec.toNat_add,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by rw [ht2, hhi_toNat]; omega) x.isLt), ht2]
      exact nat_add_half_diff (hhi_toNat ▸ hhi_le_x)
    have hhi_plus_x : hi.toNat + x.toNat = (x.toNat * M) / 2 ^ n := by
      rw [hhi_toNat, ← Nat.add_mul_div_left (x.toNat * (M - 2 ^ n)) x.toNat (Nat.two_pow_pos n),
        Nat.mul_comm (2 ^ n) x.toNat, ← Nat.mul_add, hm_eq]
    rw [ht3_half, hhi_plus_x, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  apply BitVec.eq_of_toNat_eq
  show (t3 >>> ((BitVec.ofNat n (s - 1)).toNat % n)).toNat = (x / d).toNat
  rw [mod_eq_of_lt_n (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht3,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, show n + 1 + (s - 1) = n + s by omega,
    nat_umagic_div_eq hd0 (Nat.le_pred_of_lt x.isLt) hlo hhi, BitVec.toNat_udiv]

/-! ## Signed arithmetic and certificate soundness -/

/-- Soundness of `sPow2Cert`: `d = 2^m` with `2 ≤ n`, `1 ≤ m`, `m + 1 < n`, and `d ∉ {0, -1}`. -/
theorem sPow2Cert_sound {n : Nat} {d : BitVec n} {m : Nat}
    (h : sPow2Cert n d m = true) :
    2 ≤ n ∧ 1 ≤ m ∧ m + 1 < n ∧ d = BitVec.twoPow n m ∧
      d ≠ 0#n ∧ d ≠ BitVec.allOnes n := by
  simp only [sPow2Cert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨hn, hm1⟩, hmn⟩, hd⟩
  exact ⟨hn, hm1, hmn, hd, hd ▸ twoPow_ne_zero (by omega),
    hd ▸ twoPow_ne_allOnes_of_pos hm1 hmn⟩

private theorem neg_int_ediv_pow2_bias {K P : Nat} (hP : 0 < P) :
    (-(K : Int) + (P : Int) - 1) / (P : Int) = -((K / P : Nat) : Int) := by
  let q := K / P
  let r := K % P
  have hdiv : P * q + r = K := Nat.div_add_mod K P
  have hr : r < P := Nat.mod_lt K hP
  have hsplit : -(K : Int) + (P : Int) - 1 =
      (((P - 1 - r : Nat) : Int)) + (P : Int) * (-(q : Int)) := by
    have hr' : (r : Int) + 1 ≤ (P : Int) := by exact_mod_cast hr
    have hcast : ((P - 1 - r : Nat) : Int) = (P : Int) - 1 - (r : Int) := by omega
    have hdivZ : (P : Int) * (q : Int) + (r : Int) = (K : Int) := by exact_mod_cast hdiv
    have hmul : (P : Int) * (-(q : Int)) = -((P : Int) * (q : Int)) := Int.mul_neg _ _
    omega
  rw [hsplit, Int.add_mul_ediv_left _ _ (Int.ne_of_gt (by exact_mod_cast hP)),
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast (by omega : P - 1 - r < P)),
    Int.zero_add]

private theorem sdiv_twoPow_toInt_eq {n m : Nat} (hn : 2 ≤ n) (hmn : m + 1 < n) (x : BitVec n) :
    ((if x.toInt < 0 then x.toInt + (2 ^ m : Int) - 1 else x.toInt) / (2 ^ m : Int)).bmod
      (2 ^ n) = (x.sdiv (BitVec.twoPow n m)).toInt := by
  have hpow_m_lt : 2 ^ m < 2 ^ (n - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hd_toNat : (BitVec.twoPow n m).toNat = 2 ^ m := by
    rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
  have hd_msb : (BitVec.twoPow n m).msb = false := by
    rw [BitVec.msb_eq_toNat, hd_toNat, decide_eq_false_iff_not]; omega
  have hd_toInt : (BitVec.twoPow n m).toInt = (2 ^ m : Int) := by
    rw [BitVec.toInt_eq_msb_cond, hd_msb]
    simp only [Bool.false_eq_true, ↓reduceIte, hd_toNat, Int.natCast_pow, Int.cast_ofNat_Int]
  rw [BitVec.toInt_sdiv, hd_toInt]; congr 1
  have hm2 : (2 ^ m : Int) = ((2 ^ m : Nat) : Int) := by push_cast; rfl
  by_cases hneg : x.toInt < 0
  · simp only [hneg, ↓reduceIte]
    have hKpos : 0 < x.toInt.natAbs := by omega
    have htd : (-(x.toInt.natAbs : Int)).tdiv (2 ^ m : Int) =
        -((x.toInt.natAbs / 2 ^ m : Nat) : Int) := by
      rw [hm2]; change Int.tdiv (-Int.ofNat _) (Int.ofNat _) = -Int.ofNat _
      cases hka : x.toInt.natAbs with | zero => omega | succ _ => rfl
    rw [show x.toInt = -(x.toInt.natAbs : Int) by omega, htd]
    simpa [Int.natCast_pow] using neg_int_ediv_pow2_bias (K := x.toInt.natAbs) (Nat.two_pow_pos m)
  · simp only [hneg, ↓reduceIte]
    rw [← Int.natAbs_of_nonneg (Int.not_lt.mp hneg), hm2]; rfl

private theorem allOnes_lshr_eq {n m : Nat} (hn : 2 ≤ n) (hmn : m + 1 < n) :
    (BitVec.allOnes n >>> (n - m)).toInt = (2 ^ m : Int) - 1 := by
  have hpow : 2 ^ n = 2 ^ m * 2 ^ (n - m) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  have hlt1 : 2 ^ m - 1 < 2 ^ (n - 1) :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ 1) (Nat.pow_lt_pow_right (by decide) (by omega))
  have hm_pos := Nat.two_pow_pos m
  have hnm_pos := Nat.two_pow_pos (n - m)
  have hnat : (BitVec.allOnes n >>> (n - m)).toNat = 2 ^ m - 1 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_allOnes]
    exact Nat.div_eq_of_lt_le (by rw [Nat.sub_mul, Nat.one_mul, ← hpow]; omega)
      (by rw [Nat.sub_add_cancel hm_pos, ← hpow]; exact Nat.sub_lt (Nat.two_pow_pos n) (by decide))
  have hmsb : (BitVec.allOnes n >>> (n - m)).msb = false := by
    rw [BitVec.msb_eq_toNat, hnat, decide_eq_false_iff_not]; omega
  rw [BitVec.toInt_eq_msb_cond, hmsb]
  simp only [Bool.false_eq_true, ↓reduceIte, hnat]
  rw [Int.ofNat_sub hm_pos]; push_cast; rfl

private theorem sdiv_twoPow_finish {n m : Nat} (hn : 2 ≤ n) (hmn : m + 1 < n) (x : BitVec n)
    (hpow_m_pos : (1 : Int) ≤ (2 ^ m : Int)) (hsummand : Int)
    (hsum_eq : x.toInt + hsummand =
      if x.toInt < 0 then x.toInt + (2 ^ m : Int) - 1 else x.toInt)
    (hsum_bounds : -(2 ^ (n - 1) : Int) ≤ x.toInt + hsummand ∧
      x.toInt + hsummand < (2 ^ (n - 1) : Int)) :
    (x.toInt + hsummand).bmod (2 ^ n) / (2 ^ m : Int) = (x.sdiv (BitVec.twoPow n m)).toInt := by
  have hp : (0 : Int) < 2 ^ m := by omega
  have h1 : -(2 ^ (n - 1) : Int) ≤
      if x.toInt < 0 then x.toInt + (2 ^ m : Int) - 1 else x.toInt := by omega
  have h2 : (if x.toInt < 0 then x.toInt + (2 ^ m : Int) - 1 else x.toInt) <
      (2 ^ (n - 1) : Int) := by omega
  have hlo_mul : -(2 ^ (n - 1) : Int) * (2 ^ m : Int) ≤
      if x.toInt < 0 then x.toInt + (2 ^ m : Int) - 1 else x.toInt := by
    have := Int.mul_le_mul_of_nonpos_left (by omega : -(2 ^ (n - 1) : Int) ≤ 0) hpow_m_pos; omega
  have hhi_mul : (if x.toInt < 0 then x.toInt + (2 ^ m : Int) - 1 else x.toInt) <
      (2 ^ (n - 1) : Int) * (2 ^ m : Int) := by
    have hnn : (0 : Int) ≤ 2 ^ (n - 1) := Int.pow_nonneg (by decide)
    have := Int.mul_le_mul_of_nonneg_left hpow_m_pos hnn; omega
  rw [int_bmod_eq_self (by omega) hsum_bounds.1 hsum_bounds.2, hsum_eq,
    ← int_bmod_eq_self (by omega) (Int.le_ediv_of_mul_le hp hlo_mul)
      (Int.ediv_lt_of_lt_mul hp hhi_mul)]
  exact sdiv_twoPow_toInt_eq hn hmn x

/-- Signed power-of-two division correctness for `m = 1` (`d = 2`). -/
theorem sdiv_twoPow_one_eq {n : Nat} {d : BitVec n}
    (hcert : sPow2Cert n d 1 = true) (x : BitVec n) :
    let t1 := x >>> ((BitVec.ofNat n (n - 1)).toNat % n)
    let t2 := x + t1
    t2.sshiftRight ((1#n : BitVec n).toNat % n) = x.sdiv d := by
  obtain ⟨hn, _, hmn, rfl, _, _⟩ := sPow2Cert_sound hcert
  have h1m : (1#n : BitVec n).toNat % n = 1 := by
    rw [one_toNat_of_two_le hn, Nat.mod_eq_of_lt (by omega)]
  have hxlo : -(2 ^ (n - 1) : Int) ≤ x.toInt := by simpa [Int.natCast_pow] using x.le_toInt
  have hxhi : x.toInt < (2 ^ (n - 1) : Int) := by simpa [Int.natCast_pow] using x.toInt_lt
  have hmain := sdiv_twoPow_finish hn hmn x (by decide)
    (if x.toInt < 0 then 1 else 0) (by split <;> omega) (by split <;> omega)
  apply BitVec.eq_of_toInt_eq
  rw [mod_eq_of_lt_n (by omega), h1m, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow,
    BitVec.toInt_add, lshr_sign_bit_toInt hn x, Int.natCast_pow, Int.cast_ofNat_Int]
  exact hmain

/-- Signed power-of-two division correctness for `1 ≤ m` and `m + 1 < n`. -/
theorem sdiv_twoPow_ge_eq {n m : Nat} {d : BitVec n}
    (hcert : sPow2Cert n d m = true) (x : BitVec n) :
    let t1 := x.sshiftRight ((BitVec.ofNat n (n - 1)).toNat % n)
    let t2 := t1 >>> ((BitVec.ofNat n (n - m)).toNat % n)
    let t3 := x + t2
    t3.sshiftRight ((BitVec.ofNat n m).toNat % n) = x.sdiv d := by
  obtain ⟨hn, _, hmn, rfl, _, _⟩ := sPow2Cert_sound hcert
  have hxlo : -(2 ^ (n - 1) : Int) ≤ x.toInt := by simpa [Int.natCast_pow] using x.le_toInt
  have hxhi : x.toInt < (2 ^ (n - 1) : Int) := by simpa [Int.natCast_pow] using x.toInt_lt
  have ht1_val : x.sshiftRight (n - 1) = if x.toInt < 0 then BitVec.allOnes n else 0#n := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, Int.natCast_pow, Int.cast_ofNat_Int]
    have hpos : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide)
    by_cases hneg : x.toInt < 0
    · simp only [hneg, ↓reduceIte, BitVec.toInt_allOnes, show 0 < n by omega]
      have hq : x.toInt = (x.toInt + (2 ^ (n - 1) : Int)) + (2 ^ (n - 1) : Int) * (-1) := by omega
      rw [hq, Int.add_mul_ediv_left _ _ (Int.ne_of_gt hpos),
        Int.ediv_eq_zero_of_lt (by omega) (by omega), Int.zero_add]
    · simp only [hneg, ↓reduceIte, BitVec.toInt_zero]
      exact Int.ediv_eq_zero_of_lt (Int.not_lt.mp hneg) hxhi
  have ht2_toInt : ((x.sshiftRight (n - 1)) >>> (n - m)).toInt =
      if x.toInt < 0 then (2 ^ m : Int) - 1 else 0 := by
    rw [ht1_val]; split
    · exact allOnes_lshr_eq hn hmn
    · simp
  have hpow_m_lt : (2 ^ m : Int) < (2 ^ (n - 1) : Int) := by
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : m < n - 1)
  have hpow_m_pos : (1 : Int) ≤ (2 ^ m : Int) := by exact_mod_cast Nat.two_pow_pos m
  have hmain := sdiv_twoPow_finish hn hmn x hpow_m_pos
    (if x.toInt < 0 then (2 ^ m : Int) - 1 else 0) (by split <;> omega) (by split <;> omega)
  apply BitVec.eq_of_toInt_eq
  rw [mod_eq_of_lt_n (by omega), mod_eq_of_lt_n (by omega), mod_eq_of_lt_n (by omega),
    BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, BitVec.toInt_add, ht2_toInt,
    Int.natCast_pow, Int.cast_ofNat_Int]
  exact hmain

private theorem le_anc_of_mod_eq_pred {X Xmax D : Nat} (hD : 0 < D) (hX : X ≤ Xmax)
    (hmod : X % D = D - 1) : X ≤ Xmax - (Xmax + 1) % D := by
  have hdiv1 : (X + 1) / D ≤ (Xmax + 1) / D := Nat.div_le_div_right (Nat.succ_le_succ hX)
  have hX1 : X + 1 = D * (X / D + 1) := by
    have h := Nat.div_add_mod X D
    rw [hmod] at h; rw [Nat.mul_add, Nat.mul_one]; omega
  have hdivX : (X + 1) / D = X / D + 1 := by rw [hX1, Nat.mul_div_right _ hD]
  have hmul_le : D * ((X + 1) / D) ≤ D * ((Xmax + 1) / D) := Nat.mul_le_mul_left D hdiv1
  have hmax : D * ((Xmax + 1) / D) = (Xmax + 1) - (Xmax + 1) % D := by
    have h := Nat.div_add_mod (Xmax + 1) D; omega
  rw [hdivX, ← hX1, hmax] at hmul_le
  have hmod_le := Nat.mod_le (Xmax + 1) D
  omega

/-- Nat lemma for same-sign quadrant (`x * d ≥ 0`) of signed GM division. -/
theorem nat_smagic_same {D A B e X Xmax : Nat} (hD : 0 < D) (hAD : A * D = B + e)
    (hX : X ≤ Xmax) (hanc : (Xmax - (Xmax + 1) % D) * e < B) (h2B : Xmax * e < 2 * B) :
    (X * A) / B = X / D := by
  let q := X / D
  let r := X % D
  have hdiv : D * q + r = X := Nat.div_add_mod X D
  have hr : r < D := Nat.mod_lt X hD
  have hlo : q * B ≤ X * A := by
    calc q * B ≤ q * (B + e) := Nat.mul_le_mul_left q (Nat.le_add_right B e)
      _ = (D * q) * A := by rw [← hAD]; ac_rfl
      _ ≤ (D * q + r) * A := Nat.mul_le_mul_right A (Nat.le_add_right _ r)
      _ = X * A := by rw [hdiv]
  have hXe : X * e < (D - r) * B := by
    by_cases hr1 : r = D - 1
    · rw [show D - r = 1 by omega, Nat.one_mul]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right e (le_anc_of_mod_eq_pred hD hX hr1)) hanc
    · calc X * e ≤ Xmax * e := Nat.mul_le_mul_right e hX
        _ < 2 * B := h2B
        _ ≤ (D - r) * B := Nat.mul_le_mul_right B (by omega)
  have hmul_lt : (X * A) * D < ((q + 1) * B) * D := by
    have hXDr : (q + 1) * D = X + (D - r) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q D, ← hdiv]; omega
    calc (X * A) * D = X * (B + e) := by rw [Nat.mul_assoc, hAD]
      _ = X * B + X * e := Nat.mul_add X B e
      _ < (X + (D - r)) * B := by rw [Nat.add_mul]; exact Nat.add_lt_add_left hXe _
      _ = ((q + 1) * B) * D := by rw [← hXDr]; ac_rfl
  exact Nat.div_eq_of_lt_le hlo (Nat.lt_of_mul_lt_mul_right hmul_lt)

/-- Nat lemma for opposite-sign quadrant (`x * d < 0`) of signed GM division. -/
theorem nat_smagic_opp {D A B e X Xmax : Nat} (hD : 0 < D) (hA : 0 < A) (he : 0 < e)
    (hAD : A * D = B + e) (hXpos : 0 < X) (hX : X ≤ Xmax)
    (hanc : (Xmax - (Xmax + 1) % D) * e ≤ B) (h2B : Xmax * e ≤ 2 * B) :
    (X * A - 1) / B = X / D := by
  let q := X / D; let r := X % D
  have hdiv : D * q + r = X := Nat.div_add_mod X D
  have hr : r < D := Nat.mod_lt X hD
  have hlt_lo : q * B < X * A := by
    have hpos_rem : 0 < q * e + r * A := by
      by_cases hr0 : r = 0
      · have hqpos : 0 < q := Nat.pos_of_ne_zero fun hq0 => by
          rw [hq0, hr0, Nat.mul_zero, Nat.add_zero] at hdiv; omega
        exact Nat.add_pos_left (Nat.mul_pos hqpos he) _
      · exact Nat.add_pos_right _ (Nat.mul_pos (Nat.pos_of_ne_zero hr0) hA)
    calc q * B < q * B + (q * e + r * A) := Nat.lt_add_of_pos_right hpos_rem
      _ = q * (B + e) + r * A := by rw [Nat.mul_add]; ac_rfl
      _ = (D * q + r) * A := by rw [← hAD, Nat.add_mul]; ac_rfl
      _ = X * A := by rw [hdiv]
  have hXe : X * e ≤ (D - r) * B := by
    by_cases hr1 : r = D - 1
    · rw [show D - r = 1 by omega, Nat.one_mul]
      exact Nat.le_trans (Nat.mul_le_mul_right e (le_anc_of_mod_eq_pred hD hX hr1)) hanc
    · calc X * e ≤ Xmax * e := Nat.mul_le_mul_right e hX
        _ ≤ 2 * B := h2B
        _ ≤ (D - r) * B := Nat.mul_le_mul_right B (by omega)
  have hmul_le : (X * A) * D ≤ ((q + 1) * B) * D := by
    have hXDr : (q + 1) * D = X + (D - r) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q D, ← hdiv]; omega
    calc (X * A) * D = X * (B + e) := by rw [Nat.mul_assoc, hAD]
      _ = X * B + X * e := Nat.mul_add X B e
      _ ≤ (X + (D - r)) * B := by rw [Nat.add_mul]; exact Nat.add_le_add_left hXe _
      _ = ((q + 1) * B) * D := by rw [← hXDr]; ac_rfl
  have hhi_le : X * A ≤ (q + 1) * B := Nat.le_of_mul_le_mul_right hmul_le hD
  exact Nat.div_eq_of_lt_le (Nat.le_pred_of_lt hlt_lo) (show X * A - 1 < (q + 1) * B by omega)

private theorem int_neg_ediv_succ {K B : Nat} (hK : 0 < K) (hB : 0 < B) :
    (-(K : Int)) / (B : Int) + 1 = -(((K - 1) / B : Nat) : Int) := by
  let q := (K - 1) / B; let r := (K - 1) % B
  have hdiv : B * q + r = K - 1 := Nat.div_add_mod (K - 1) B
  have hr : r < B := Nat.mod_lt (K - 1) hB
  have hKeq : -(K : Int) = ((B - 1 - r : Nat) : Int) + (B : Int) * (-(q + 1 : Int)) := by
    have hr' : (r : Int) + 1 ≤ (B : Int) := by exact_mod_cast hr
    have hcast : ((B - 1 - r : Nat) : Int) = (B : Int) - 1 - (r : Int) := by omega
    have hdivZ : (B : Int) * (q : Int) + (r : Int) = (K : Int) - 1 := by
      have : ((B * q + r : Nat) : Int) = ((K - 1 : Nat) : Int) := congrArg Int.ofNat hdiv
      push_cast at this; rw [Int.ofNat_sub hK] at this; exact this
    have hmul : (B : Int) * (-(q + 1 : Int)) = -((B : Int) * (q : Int)) - (B : Int) := by
      rw [Int.mul_neg, Int.mul_add, Int.mul_one]; omega
    omega
  rw [hKeq, Int.add_mul_ediv_left _ _ (Int.ne_of_gt (by exact_mod_cast hB)),
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast (by omega : B - 1 - r < B)),
    Int.zero_add]; omega

private theorem toInt_natAbs_neg_lt {n : Nat} (x : BitVec n) :
    x.toInt < 0 → x.toInt.natAbs ≤ 2 ^ (n - 1) := by
  intro hneg; have hlo : -((2 ^ (n - 1) : Nat) : Int) ≤ x.toInt := by
    simpa [Int.natCast_pow] using x.le_toInt
  omega

private theorem toInt_natAbs_nonneg {n : Nat} (x : BitVec n) :
    0 ≤ x.toInt → x.toInt.natAbs ≤ 2 ^ (n - 1) - 1 := by
  intro hnn; have hhi : x.toInt < ((2 ^ (n - 1) : Nat) : Int) := by
    simpa [Int.natCast_pow] using x.toInt_lt
  have hp := Nat.two_pow_pos (n - 1)
  omega

private theorem mul_hi_bounds {n A : Nat} (hA1 : 1 ≤ A) (hAlt : A < 2 ^ n)
    (dPos : Bool) (x : BitVec n) :
    let mFull : Int := if dPos then (A : Int) else -(A : Int);
    -(2 ^ (n - 1) : Int) ≤ (x.toInt * mFull) / (2 ^ n : Int) ∧
      (x.toInt * mFull) / (2 ^ n : Int) < (2 ^ (n - 1) : Int) := by
  have hxlo : -((2 ^ (n - 1) : Nat) : Int) ≤ x.toInt := by
    simpa [Int.natCast_pow] using x.le_toInt
  have hxhi : x.toInt < ((2 ^ (n - 1) : Nat) : Int) := by
    simpa [Int.natCast_pow] using x.toInt_lt
  have hxabs : x.toInt.natAbs ≤ 2 ^ (n - 1) := by omega
  let mFull : Int := if dPos then (A : Int) else -(A : Int)
  have hmabs : mFull.natAbs = A := by cases dPos <;> simp [mFull]
  have hHpos : 1 ≤ 2 ^ (n - 1) := Nat.two_pow_pos (n - 1)
  have hxm_lt : x.toInt.natAbs * A < 2 ^ (n - 1) * 2 ^ n :=
    calc x.toInt.natAbs * A ≤ 2 ^ (n - 1) * (2 ^ n - 1) := Nat.mul_le_mul hxabs (by omega)
      _ < 2 ^ (n - 1) * 2 ^ n := Nat.mul_lt_mul_of_pos_left (by omega) hHpos
  have hxm_ltZ : ((x.toInt * mFull).natAbs : Int) < (2 ^ (n - 1) : Int) * (2 ^ n : Int) := by
    rw [Int.natAbs_mul, hmabs]
    simpa [Int.natCast_pow] using Int.ofNat_lt.mpr hxm_lt
  have hbound : -((2 ^ (n - 1) : Int) * (2 ^ n : Int)) ≤ x.toInt * mFull ∧
      x.toInt * mFull < (2 ^ (n - 1) : Int) * (2 ^ n : Int) := by
    rcases Int.natAbs_eq (x.toInt * mFull) with h | h <;> omega
  rw [← Int.neg_mul] at hbound
  have hpn : (0 : Int) < (2 ^ n : Int) := Int.pow_pos (by decide)
  exact ⟨Int.le_ediv_of_mul_le hpn (by simpa [mFull] using hbound.1),
    Int.ediv_lt_of_lt_mul hpn (by simpa [mFull] using hbound.2)⟩

private theorem tdiv_of_signs {a b : Int} :
    a.tdiv b =
      if (0 ≤ a ∧ 0 ≤ b) ∨ (a < 0 ∧ b < 0) then ((a.natAbs / b.natAbs : Nat) : Int)
      else -((a.natAbs / b.natAbs : Nat) : Int) := by
  cases a <;> cases b <;> simp [Int.natCast_nonneg, Int.negSucc_lt_zero] <;> rfl

/-- Soundness of `sDivCert`: signed Granlund-Montgomery quotient matches `x.sdiv d`. -/
theorem sDivCert_sound {n : Nat} {d : BitVec n} {A s : Nat}
    (hcert : sDivCert n d A s = true) (x : BitVec n) :
    let mInt : Int := if 0 < d.toInt then (A : Int) else -(A : Int);
    let m : BitVec n := BitVec.ofInt n mInt;
    let hi : BitVec n := (BitVec.ofInt (n + n) (x.toInt * m.toInt)).extractLsb' n n;
    let t : BitVec n :=
      if 0 < d.toInt && m.toInt < 0 then hi + x
      else if d.toInt < 0 && 0 < m.toInt then hi - x
      else hi;
    let q0 : BitVec n := if s == 0 then t else t.sshiftRight ((BitVec.ofNat n s).toNat % n);
    let sgn : BitVec n := q0 >>> ((BitVec.ofNat n (n - 1)).toNat % n);
    d ≠ 0#n ∧ d ≠ BitVec.allOnes n ∧ q0 + sgn = x.sdiv d := by
  simp only [sDivCert, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hcert
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, hd0⟩, hd1⟩, _⟩, hA1⟩, hAlt⟩, hsn⟩, hBAD, ⟨⟨⟨hancS, hxS⟩, hancO⟩, hxO⟩⟩ := hcert
  let H := 2 ^ (n - 1); let D := d.toInt.natAbs; let B := 2 ^ (n + s); let e := A * D - B
  have hDpos : 0 < D := Nat.pos_of_ne_zero fun h =>
    hd0 (BitVec.eq_of_toInt_eq (by simpa using Int.natAbs_eq_zero.mp h))
  have hAD : A * D = B + e := (Nat.add_sub_of_le (Nat.le_of_lt hBAD)).symm
  have he : 0 < e := Nat.sub_pos_of_lt hBAD
  have hBpos : 0 < B := Nat.two_pow_pos (n + s)
  let mInt : Int := if 0 < d.toInt then (A : Int) else -(A : Int)
  let m : BitVec n := BitVec.ofInt n mInt
  let hi : BitVec n := (BitVec.ofInt (n + n) (x.toInt * m.toInt)).extractLsb' n n
  let t : BitVec n :=
    if 0 < d.toInt && m.toInt < 0 then hi + x
    else if d.toInt < 0 && 0 < m.toInt then hi - x else hi
  let q0 : BitVec n := if s == 0 then t else t.sshiftRight ((BitVec.ofNat n s).toNat % n)
  let sgn : BitVec n := q0 >>> ((BitVec.ofNat n (n - 1)).toNat % n)
  have hhi_toInt : hi.toInt = (x.toInt * m.toInt) / (2 ^ n : Int) := smulw_hi_toInt x m
  have hpn : (0 : Int) < (2 ^ n : Int) := Int.pow_pos (by decide)
  have ht_toInt : t.toInt = (x.toInt * mInt) / (2 ^ n : Int) := by
    have hpow : (2 : Int) ^ n = 2 * (2 ^ (n - 1) : Int) := by
      rw [show n = 1 + (n - 1) by omega, Int.pow_add]; simp
    have hHcast : (2 : Int) ^ (n - 1) = (H : Int) := by push_cast [H]; rfl
    have hAlt' : (A : Int) < (2 : Int) ^ n := by exact_mod_cast hAlt
    have hhalf : ((2 : Int) ^ n + 1) / 2 = (H : Int) := by rw [hpow, hHcast]; omega
    have hbounds : -(2 ^ (n - 1) : Int) ≤ (x.toInt * mInt) / (2 ^ n : Int) ∧
        (x.toInt * mInt) / (2 ^ n : Int) < (2 ^ (n - 1) : Int) := by
      have hb := mul_hi_bounds hA1 hAlt (decide (0 < d.toInt)) x
      by_cases hdp : 0 < d.toInt <;> simpa [mInt, hdp] using hb
    have hm_bmod : m.toInt = mInt.bmod (2 ^ n) := by simp [m, BitVec.toInt_ofInt]
    dsimp only [t]
    by_cases hdpos : 0 < d.toInt
    · have hm_eq : m.toInt = if H ≤ A then (A : Int) - (2 ^ n : Int) else (A : Int) := by
        rw [hm_bmod, Int.bmod_def, Int.natCast_pow, Int.cast_ofNat_Int]
        have hmod : (A : Int) % (2 : Int) ^ n = (A : Int) :=
          Int.emod_eq_of_lt (Int.natCast_nonneg A) hAlt'
        simp only [mInt, hdpos, ↓reduceIte, hmod, hhalf]
        by_cases hHA : H ≤ A
        · simp [show ¬ ((A : Int) < (H : Int)) by exact_mod_cast (by omega : ¬ A < H), hHA]
        · simp [show (A : Int) < (H : Int) by exact_mod_cast (by omega : A < H), hHA]
      by_cases hHA : H ≤ A
      · have hmneg : m.toInt < 0 := by simp only [hm_eq, hHA, ↓reduceIte]; omega
        have hm_sub : m.toInt = mInt - (2 ^ n : Int) := by
          simp only [hm_eq, hHA, ↓reduceIte, mInt, hdpos]
        simp only [hdpos, hmneg, decide_true, Bool.and_self, ↓reduceIte]
        rw [BitVec.toInt_add, hhi_toInt, hm_sub, Int.mul_sub, Int.sub_eq_add_neg,
          show -(x.toInt * (2 ^ n : Int)) = (2 ^ n : Int) * (-x.toInt) by
            rw [Int.mul_neg, Int.mul_comm],
          Int.add_mul_ediv_left _ _ (Int.ne_of_gt hpn),
          show (x.toInt * mInt) / (2 ^ n : Int) + -x.toInt + x.toInt =
            (x.toInt * mInt) / (2 ^ n : Int) by omega]
        exact int_bmod_eq_self (by omega) hbounds.1 hbounds.2
      · have hm_eq' : m.toInt = mInt := by simp only [hm_eq, hHA, ↓reduceIte, mInt, hdpos]
        have hmnneg : ¬ (m.toInt < 0) := by rw [hm_eq']; dsimp only [mInt]; simp [hdpos]
        simp only [hdpos, hmnneg, show ¬ (d.toInt < 0) by omega, decide_true, decide_false,
          Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [hhi_toInt, hm_eq']
    · have hdneg : d.toInt < 0 := by omega
      have hm_eq : m.toInt = if H < A then (2 : Int) ^ n - (A : Int) else -(A : Int) := by
        rw [hm_bmod, Int.bmod_def, Int.natCast_pow, Int.cast_ofNat_Int]
        have hmod : (-(A : Int)) % (2 : Int) ^ n = (2 : Int) ^ n - (A : Int) := by
          rw [← Int.add_emod_right (-(A : Int)) ((2 : Int) ^ n), Int.add_comm,
            ← Int.sub_eq_add_neg]; exact Int.emod_eq_of_lt (by omega) (by omega)
        simp only [mInt, hdpos, ↓reduceIte, hmod, hhalf]
        by_cases hHA : H < A
        · have : (H : Int) < (A : Int) := by exact_mod_cast hHA
          simp [hHA, show (2 : Int) ^ n - (A : Int) < (H : Int) by omega]
        · have : (A : Int) ≤ (H : Int) := by exact_mod_cast (by omega : A ≤ H)
          simp [hHA, show ¬ ((2 : Int) ^ n - (A : Int) < (H : Int)) by omega]; omega
      by_cases hHA : H < A
      · have hm_add : m.toInt = mInt + (2 ^ n : Int) := by
          simp only [hm_eq, hHA, ↓reduceIte, mInt, hdpos]; omega
        have hmpos : 0 < m.toInt := by rw [hm_add]; dsimp only [mInt]; simp [hdpos]; omega
        simp only [hdpos, hdneg, hmpos, decide_false, decide_true, Bool.false_and, Bool.and_self,
          Bool.false_eq_true, ↓reduceIte]
        rw [BitVec.toInt_sub, hhi_toInt, hm_add, Int.mul_add,
          show x.toInt * (2 ^ n : Int) = (2 ^ n : Int) * x.toInt by rw [Int.mul_comm],
          Int.add_mul_ediv_left _ _ (Int.ne_of_gt hpn),
          show (x.toInt * mInt) / (2 ^ n : Int) + x.toInt - x.toInt =
            (x.toInt * mInt) / (2 ^ n : Int) by omega]
        exact int_bmod_eq_self (by omega) hbounds.1 hbounds.2
      · have hm_eq' : m.toInt = mInt := by simp only [hm_eq, hHA, ↓reduceIte, mInt, hdpos]
        have hmnpos : ¬ (0 < m.toInt) := by rw [hm_eq']; dsimp only [mInt]; simp [hdpos]
        simp only [hdpos, hdneg, hmnpos, decide_false, Bool.false_and, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte]
        rw [hhi_toInt, hm_eq']
  have hq0_toInt : q0.toInt = (x.toInt * mInt) / (2 ^ (n + s) : Int) := by
    dsimp only [q0]
    by_cases hs0 : s = 0
    · simp only [hs0, beq_self_eq_true, ↓reduceIte, Nat.add_zero]; exact ht_toInt
    · simp only [beq_false_of_ne hs0, Bool.false_eq_true, ↓reduceIte]
      rw [mod_eq_of_lt_n hsn, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, ht_toInt,
        Int.natCast_pow, Int.cast_ofNat_Int, int_ediv_pow_add]
  have hsgn_toInt : sgn.toInt = if q0.toInt < 0 then 1 else 0 := by
    dsimp only [sgn]; rw [mod_eq_of_lt_n (by omega)]; exact lshr_sign_bit_toInt hn q0
  have hq_eq_tdiv : q0.toInt + sgn.toInt = x.toInt.tdiv d.toInt := by
    rw [hsgn_toInt, hq0_toInt, tdiv_of_signs]
    by_cases hx0 : x.toInt = 0
    · simp [hx0]
    · have hXpos : 0 < x.toInt.natAbs := Int.natAbs_pos.mpr hx0
      have hBcast : (2 : Int) ^ (n + s) = (B : Int) := by push_cast [B]; rfl
      by_cases hsame : (0 ≤ x.toInt ∧ 0 ≤ d.toInt) ∨ (x.toInt < 0 ∧ d.toInt < 0)
      · have hXle : x.toInt.natAbs ≤ if 0 < d.toInt then H - 1 else H := by
          rcases hsame with ⟨h1, _⟩ | ⟨h1, _⟩
          · simp only [show 0 < d.toInt by omega, ↓reduceIte]; exact toInt_natAbs_nonneg x h1
          · simp only [show ¬ 0 < d.toInt by omega, ↓reduceIte]; exact toInt_natAbs_neg_lt x h1
        have hprod : x.toInt * mInt = ((x.toInt.natAbs * A : Nat) : Int) := by
          rcases hsame with ⟨h1, _⟩ | ⟨h1, _⟩
          · dsimp only [mInt]; simp only [show 0 < d.toInt by omega, ↓reduceIte]
            push_cast; rw [Int.natAbs_of_nonneg h1]
          · dsimp only [mInt]; simp only [show ¬ 0 < d.toInt by omega, ↓reduceIte]
            push_cast; rw [Int.ofNat_natAbs_of_nonpos (by omega)]
            simp only [Int.neg_mul, Int.mul_neg]
        have hnlt : ¬ (((x.toInt.natAbs * A : Nat) : Int) / (B : Int) < 0) :=
          Int.not_lt.mpr (Int.ediv_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
        simp only [hsame, ↓reduceIte, hprod, hBcast, hnlt, Int.add_zero]
        exact congrArg Int.ofNat (nat_smagic_same hDpos hAD hXle hancS hxS)
      · have hXle : x.toInt.natAbs ≤ if 0 < d.toInt then H else H - 1 := by
          by_cases hdpos : 0 < d.toInt
          · simp only [hdpos, ↓reduceIte]; exact toInt_natAbs_neg_lt x (by omega)
          · simp only [hdpos, ↓reduceIte]; exact toInt_natAbs_nonneg x (by omega)
        have hprod : x.toInt * mInt = -((x.toInt.natAbs * A : Nat) : Int) := by
          by_cases hdpos : 0 < d.toInt
          · dsimp only [mInt]; simp only [hdpos, ↓reduceIte]
            push_cast; rw [Int.ofNat_natAbs_of_nonpos (by omega)]
            simp only [Int.neg_mul, Int.neg_neg]
          · dsimp only [mInt]; simp only [hdpos, ↓reduceIte]
            push_cast; rw [Int.natAbs_of_nonneg (by omega)]; simp only [Int.mul_neg]
        have hKpos : 0 < x.toInt.natAbs * A := Nat.mul_pos hXpos hA1
        have hneg_div : (-((x.toInt.natAbs * A : Nat) : Int)) / (B : Int) < 0 := by
          have h1 : (-((x.toInt.natAbs * A : Nat) : Int)) / (B : Int) + 1 =
              -((((x.toInt.natAbs * A - 1) / B : Nat) : Int)) := int_neg_ediv_succ hKpos hBpos
          have h2 : (0 : Int) ≤ (((x.toInt.natAbs * A - 1) / B : Nat) : Int) := Int.natCast_nonneg _
          omega
        simp only [hsame, ↓reduceIte, hprod, hBcast, hneg_div, int_neg_ediv_succ hKpos hBpos]
        exact congrArg (fun k : Nat => -(k : Int))
          (nat_smagic_opp hDpos hA1 he hAD hXpos hXle hancO hxO)
  refine ⟨hd0, hd1, BitVec.eq_of_toInt_eq ?_⟩
  rw [BitVec.toInt_add, hq_eq_tdiv, BitVec.toInt_sdiv]

/-! ## Emitter WP soundness -/

private theorem wp_bv_add {Γ rs Q X m n} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n] → Expr Val Cont rs) (h : wp Γ Q X (k (a.val + b.val, ())) m) :
    wp Γ Q X (.let_ (op2 (.add (.bits n)) a b) k) m := by
  rw [wp_let_op2, OpCode.wp_add]; simpa [Ty.hasFloat, lift2] using h

private theorem wp_bv_sub {Γ rs Q X m n} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n] → Expr Val Cont rs) (h : wp Γ Q X (k (a.val - b.val, ())) m) :
    wp Γ Q X (.let_ (op2 (.sub (.bits n)) a b) k) m := by
  rw [wp_let_op2, OpCode.wp_sub]; simpa [Ty.hasFloat, lift2] using h

private theorem wp_bv_mul {Γ rs Q X m n} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n] → Expr Val Cont rs) (h : wp Γ Q X (k (a.val * b.val, ())) m) :
    wp Γ Q X (.let_ (op2 (.mul (.bits n)) a b) k) m := by
  rw [wp_let_op2, OpCode.wp_mul]; simpa [Ty.hasFloat, lift2] using h

private theorem wp_bv_and {Γ rs Q X m n} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n] → Expr Val Cont rs) (h : wp Γ Q X (k (a.val &&& b.val, ())) m) :
    wp Γ Q X (.let_ (op2 (.and (.bits n)) a b) k) m := by
  rw [wp_let_op2, OpCode.wp_and]; simpa [lift2] using h

private theorem wp_bv_lshr {Γ rs Q X m n} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : wp Γ Q X (k (a.val >>> (b.val.toNat % n), ())) m) :
    wp Γ Q X (.let_ (op2 (.lshr (.bits n)) a b) k) m := by
  rw [wp_let_op2, OpCode.wp_lshr]; simpa [Ty.hasFloat, lift2] using h

private theorem wp_bv_ashr {Γ rs Q X m n} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n] → Expr Val Cont rs)
    (h : wp Γ Q X (k (a.val.sshiftRight (b.val.toNat % n), ())) m) :
    wp Γ Q X (.let_ (op2 (.ashr (.bits n)) a b) k) m := by
  rw [wp_let_op2, OpCode.wp_ashr]; simpa [Ty.hasFloat, lift2] using h

private theorem wp_bv_umulw {Γ rs Q X m n} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n, .bits n] → Expr Val Cont rs)
    (h : wp Γ Q X (k (a.val * b.val, BitVec.ofNat n (a.val.toNat * b.val.toNat / 2 ^ n), ())) m) :
    wp Γ Q X (.let_ (op2 (.umulw n) a b) k) m := by
  rw [wp_let_op2, OpCode.wp_umulw]; exact h

private theorem wp_bv_smulw {Γ rs Q X m n} (a b : Arg Val (.bits n))
    (k : Tup Val [.bits n, .bits n] → Expr Val Cont rs)
    (h : wp Γ Q X (k (a.val * b.val,
      (BitVec.ofInt (n + n) (a.val.toInt * b.val.toInt)).extractLsb' n n, ())) m) :
    wp Γ Q X (.let_ (op2 (.smulw n) a b) k) m := by
  rw [wp_let_op2, OpCode.wp_smulw]; exact h

theorem emitUDivConst_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {n : Nat} {x : Arg Val (.bits n)} {d : BitVec n}
    {k : Arg Val (.bits n) → Expr Val Cont rs} {e' : Expr Val Cont rs}
    (he : emitUDivConst n x d k = some e')
    (hcont : d ≠ 0#n → ∀ res : Arg Val (.bits n), res.val = x.val / d → wp Γ Q X (k res) m) :
    d ≠ 0#n ∧ wp Γ Q X e' m := by
  unfold emitUDivConst at he
  split at he; · cases he
  · split at he; · cases he
    · split at he
      · rename_i hn _ hd1
        have hd : d = 1#n := eq_of_beq hd1
        have hne : d ≠ 0#n := hd ▸ one_ne_zero_of_two_le (two_le_of_is32or64 hn)
        cases he; refine ⟨hne, hcont hne x ?_⟩; rw [hd]; simp
      · dsimp only at he
        cases hfp : findPow2Shift n d with
        | some sh =>
          rw [hfp] at he; dsimp only at he
          split at he <;> first | contradiction | (rename_i hc; cases he)
          obtain ⟨_, _, hshn, rfl, hne⟩ := pow2ShiftCert_sound hc
          exact ⟨hne, wp_bv_lshr _ _ _ (hcont hne (.var _) (udiv_twoPow_eq hshn x.val))⟩
        | none =>
          rw [hfp] at he; dsimp only at he
          cases hfm : findUMagic n d with
          | none => simp [hfm] at he
          | some val =>
            rcases val with ⟨M, s, addShift⟩; rw [hfm] at he
            cases addShift <;> dsimp only at he <;>
              split at he <;> first | contradiction | (rename_i hc; cases he)
            · obtain ⟨hne, hdiv⟩ := uNoAddCert_sound hc x.val
              exact ⟨hne, wp_bv_umulw _ _ _ (wp_bv_lshr _ _ _ (hcont hne (.var _) hdiv))⟩
            · obtain ⟨hne, hdiv⟩ := uAddShiftCert_sound hc x.val
              exact ⟨hne, wp_bv_umulw _ _ _ (wp_bv_sub _ _ _ (wp_bv_lshr _ _ _
                (wp_bv_add _ _ _ (wp_bv_lshr _ _ _ (hcont hne (.var _) hdiv)))))⟩

theorem emitURemConst_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {n : Nat} {x : Arg Val (.bits n)} {d : BitVec n}
    {k : Arg Val (.bits n) → Expr Val Cont rs} {e' : Expr Val Cont rs}
    (he : emitURemConst n x d k = some e')
    (hcont : d ≠ 0#n → ∀ res : Arg Val (.bits n), res.val = x.val % d → wp Γ Q X (k res) m) :
    d ≠ 0#n ∧ wp Γ Q X e' m := by
  unfold emitURemConst at he
  split at he; · cases he
  · split at he; · cases he
    · split at he
      · rename_i hn _ hd1
        have hd : d = 1#n := eq_of_beq hd1
        have hne : d ≠ 0#n := hd ▸ one_ne_zero_of_two_le (two_le_of_is32or64 hn)
        cases he; refine ⟨hne, hcont hne (.imm 0#n) ?_⟩; rw [hd]; simp
      · dsimp only at he
        cases hfp : findPow2Shift n d with
        | some sh =>
          rw [hfp] at he; dsimp only at he
          split at he <;> first | contradiction | (rename_i hc; cases he)
          obtain ⟨hn2, _, hshn, rfl, hne⟩ := pow2ShiftCert_sound hc
          exact ⟨hne, wp_bv_and _ _ _ (hcont hne (.var _) (urem_twoPow_eq hn2 hshn x.val))⟩
        | none =>
          rw [hfp] at he; dsimp only at he
          exact emitUDivConst_wp he fun hne q hq =>
            wp_bv_mul _ _ _ (wp_bv_sub _ _ _ (by
              refine hcont hne (.var _) ?_; rw [Arg.val_var, Arg.val_var, Arg.val_imm, hq]
              exact sub_udiv_mul_eq_urem x.val d))

theorem emitSDivConst_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {n : Nat} {x : Arg Val (.bits n)} {d : BitVec n}
    {k : Arg Val (.bits n) → Expr Val Cont rs} {e' : Expr Val Cont rs}
    (he : emitSDivConst n x d k = some e')
    (hcont : d ≠ 0#n → d ≠ BitVec.allOnes n →
      ∀ res : Arg Val (.bits n), res.val = x.val.sdiv d → wp Γ Q X (k res) m) :
    d ≠ 0#n ∧ d ≠ BitVec.allOnes n ∧ wp Γ Q X e' m := by
  unfold emitSDivConst at he
  split at he; · cases he
  · split at he; · cases he
    · split at he
      · rename_i hn _ hd1
        have hn2 := two_le_of_is32or64 hn
        have hd : d = 1#n := eq_of_beq hd1
        have hne0 : d ≠ 0#n := hd ▸ one_ne_zero_of_two_le hn2
        have hne1 : d ≠ BitVec.allOnes n := hd ▸ one_ne_allOnes_of_two_le hn2
        cases he; refine ⟨hne0, hne1, hcont hne0 hne1 x ?_⟩; rw [hd, sdiv_one_eq hn2]
      · dsimp only at he
        cases hfp : findSPow2Shift n d with
        | some sh =>
          rw [hfp] at he; dsimp only at he; split at he
          · rename_i hc
            obtain ⟨_, _, _, rfl, hne0, hne1⟩ := sPow2Cert_sound hc
            split at he
            · rename_i hsh1; obtain rfl : sh = 1 := eq_of_beq hsh1; cases he
              exact ⟨hne0, hne1, wp_bv_lshr _ _ _ (wp_bv_add _ _ _ (wp_bv_ashr _ _ _
                (hcont hne0 hne1 (.var _) (sdiv_twoPow_one_eq hc x.val))))⟩
            · cases he
              exact ⟨hne0, hne1, wp_bv_ashr _ _ _ (wp_bv_lshr _ _ _ (wp_bv_add _ _ _
                (wp_bv_ashr _ _ _ (hcont hne0 hne1 (.var _) (sdiv_twoPow_ge_eq hc x.val)))))⟩
          · cases he
        | none =>
          rw [hfp] at he; dsimp only at he
          cases hfm : findSMagic n d with
          | none => simp [hfm] at he
          | some val =>
            rcases val with ⟨A, s⟩
            rw [hfm] at he; dsimp only at he
            split at he
            · rename_i hc; cases he
              obtain ⟨hne0, hne1, hq_eq⟩ := sDivCert_sound hc x.val
              refine ⟨hne0, hne1, ?_⟩
              let mult := BitVec.ofInt n (if 0 < d.toInt then (A : Int) else -(A : Int))
              let hiVal := (BitVec.ofInt (n + n) (x.val.toInt * mult.toInt)).extractLsb' n n
              let tVal := if 0 < d.toInt && mult.toInt < 0 then hiVal + x.val
                else if d.toInt < 0 && 0 < mult.toInt then hiVal - x.val else hiVal
              have hafter : ∀ t : Arg Val (.bits n), t.val = tVal → wp Γ Q X (if s == 0 then
                  .let_ (op2 (.lshr (.bits n)) t (.imm (BitVec.ofNat n (n - 1)))) fun (sgn, ()) =>
                  .let_ (op2 (.add (.bits n)) t (.var sgn)) fun (q, ()) => k (.var q)
                else
                  .let_ (op2 (.ashr (.bits n)) t (.imm (BitVec.ofNat n s))) fun (q0, ()) =>
                  .let_ (op2 (.lshr (.bits n)) (.var q0) (.imm (BitVec.ofNat n (n - 1))))
                    fun (sgn, ()) =>
                  .let_ (op2 (.add (.bits n)) (.var q0) (.var sgn)) fun (q, ()) => k (.var q))
                  m := by
                intro t ht
                by_cases hs0 : s = 0
                · simp only [hs0, beq_self_eq_true, ↓reduceIte]
                  refine wp_bv_lshr _ _ _ (wp_bv_add _ _ _ (hcont hne0 hne1 (.var _) ?_))
                  rw [Arg.val_var, Arg.val_var, Arg.val_imm, ht]
                  simpa [hs0, tVal, hiVal, mult] using hq_eq
                · have hsne : (s == 0) = false := beq_false_of_ne hs0
                  simp only [hsne, Bool.false_eq_true, ↓reduceIte]
                  refine wp_bv_ashr _ _ _ (wp_bv_lshr _ _ _ (wp_bv_add _ _ _
                    (hcont hne0 hne1 (.var _) ?_)))
                  rw [Arg.val_var, Arg.val_var, Arg.val_imm, Arg.val_imm, ht]
                  simpa [hsne, tVal, hiVal, mult] using hq_eq
              refine wp_bv_smulw _ _ _ ?_; dsimp only [Arg.val_imm]
              by_cases hc1 : (decide (0 < d.toInt) && decide ((BitVec.ofInt n
                  (if 0 < d.toInt then (A : Int) else -(A : Int))).toInt < 0)) = true
              · simp only [hc1, ↓reduceIte]
                exact wp_bv_add _ _ _ (hafter (.var _) (by
                  simp only [tVal, Arg.val_var, hiVal, mult, hc1, ↓reduceIte]))
              · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
                by_cases hc2 : (decide (d.toInt < 0) && decide (0 < (BitVec.ofInt n
                    (if 0 < d.toInt then (A : Int) else -(A : Int))).toInt)) = true
                · simp only [hc2, ↓reduceIte]
                  exact wp_bv_sub _ _ _ (hafter (.var _) (by
                    simp only [tVal, Arg.val_var, hiVal, mult, hc1, hc2,
                      Bool.false_eq_true, ↓reduceIte]))
                · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
                  exact hafter (.var _) (by
                    simp only [tVal, Arg.val_var, hiVal, mult, hc1, hc2,
                      Bool.false_eq_true, ↓reduceIte])
            · cases he

theorem emitSRemConst_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {n : Nat} {x : Arg Val (.bits n)} {d : BitVec n}
    {k : Arg Val (.bits n) → Expr Val Cont rs} {e' : Expr Val Cont rs}
    (he : emitSRemConst n x d k = some e')
    (hcont : d ≠ 0#n → d ≠ BitVec.allOnes n →
      ∀ res : Arg Val (.bits n), res.val = x.val.srem d → wp Γ Q X (k res) m) :
    d ≠ 0#n ∧ d ≠ BitVec.allOnes n ∧ wp Γ Q X e' m := by
  unfold emitSRemConst at he
  split at he; · cases he
  · split at he; · cases he
    · split at he
      · rename_i hn _ hd1
        have hn2 := two_le_of_is32or64 hn
        have hd : d = 1#n := eq_of_beq hd1
        have hne0 : d ≠ 0#n := hd ▸ one_ne_zero_of_two_le hn2
        have hne1 : d ≠ BitVec.allOnes n := hd ▸ one_ne_allOnes_of_two_le hn2
        cases he; refine ⟨hne0, hne1, hcont hne0 hne1 (.imm 0#n) ?_⟩; rw [hd]; simp
      · dsimp only at he
        exact emitSDivConst_wp he fun hne0 hne1 q hq =>
          wp_bv_mul _ _ _ (wp_bv_sub _ _ _ (by
            refine hcont hne0 hne1 (.var _) ?_; rw [Arg.val_var, Arg.val_var, Arg.val_imm, hq]
            exact sub_sdiv_mul_eq_srem x.val d))

/-! ## `divConst` WP preservation (`divConst_wp`) -/

private theorem divFlatArg_val {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {t : Ty} {a₁ : Arg (Arg Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → (divFlatArg a₁).val = a₂.val
  | .var hm => hG _ hm
  | .imm _ => rfl

private theorem divFlatArgs_vals {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {ts : List Ty} {as₁ : Tup (Arg (Arg Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (divFlatArgs as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => divFlatArg) (fun ha => divFlatArg_val hG ha) h

private theorem divArgTup_zip_val :
    {ts : List Ty} → (xs : Tup Val ts) → ∀ p ∈ Tup.zip (divArgTup xs) xs, p.2.1.val = p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, xs), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact divArgTup_zip_val xs _ hp

private theorem ctx_val_append {H G : Ctx (Arg Val) Val}
    (hH : ∀ p ∈ H, p.2.1.val = p.2.2) (hG : ∀ p ∈ G, p.2.1.val = p.2.2) :
    ∀ p ∈ H ++ G, p.2.1.val = p.2.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hH p hp
  · exact hG p hp

private theorem ctx_val_cons_var {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {t : Ty} (v : Val t) : ∀ p ∈ (⟨t, .var v, v⟩ :: G), p.2.1.val = p.2.2 := by
  intro p hp; cases hp with | head => rfl | tail _ hp => exact hG p hp

private theorem divArgTup_vals : {ts : List Ty} → (xs : Tup Val ts) → vals (divArgTup xs) = xs
  | [], () => rfl
  | _ :: _, (_, xs) => Prod.ext rfl (divArgTup_vals xs)

private theorem tup_zip_vals_val {ts : List Ty} :
    ∀ (r₁ : Tup (Arg Val) ts) (r₂ : Tup Val ts), vals r₁ = r₂ →
      ∀ p ∈ Tup.zip r₁ r₂, p.2.1.val = p.2.2
  | _, _, h, _, hp => by
    induction ts with
    | nil => cases hp
    | cons _ _ ih =>
      cases hp with
      | head => exact (Prod.ext_iff.mp h).1
      | tail _ hp => exact ih _ _ (Prod.ext_iff.mp h).2 hp

private theorem divConstOp_bin_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {o : Option (Expr Val Cont rs)} {fb : Expr Val Cont rs}
    (hfb : wp Γ Q X fb m) (hsome : ∀ {e'}, o = some e' → wp Γ Q X e' m) :
    wp Γ Q X (o.getD fb) m := by
  cases ho : o with
  | none => exact hfb
  | some _ => exact hsome ho

private theorem divConstOp_wp {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {op₁ : Op (Arg Val) ts} {op₂ : Op Val ts} (hop : OpRel G op₁ op₂)
    {k₁ : Tup (Arg Val) ts → Expr Val Cont rs} {k₂ : Tup Val ts → Expr Val Cont rs}
    (hk : ∀ r₁ r₂, vals r₁ = r₂ → wp Γ Q X (k₂ r₂) m → wp Γ Q X (k₁ r₁) m)
    (hw : op₂.wp (fun r => wp Γ Q X (k₂ r) m)) :
    wp Γ Q X (divConstOp op₁ k₁) m := by
  cases hop with
  | @mk _ _ code args₁ args₂ hargs =>
    have hvals : vals (divFlatArgs args₁) = vals args₂ := divFlatArgs_vals hG hargs
    have hw_flat : (divFlatOp ⟨code, args₁⟩).wp (fun r => wp Γ Q X (k₂ r) m) := by
      simpa [divFlatOp, Op.wp, hvals] using hw
    have hfallback :
        wp Γ Q X (.let_ (divFlatOp ⟨code, args₁⟩) fun xs => k₁ (divArgTup xs)) m := by
      simp only [wp]
      exact Op.wp_mono (fun xs hxs => hk (divArgTup xs) xs (divArgTup_vals xs) hxs) hw_flat
    unfold divConstOp; dsimp only [divFlatOp]
    cases code with
    | udiv n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
      dsimp only [divFlatOp, divFlatArgs, tupMapArg] at hw_flat hfallback ⊢
      cases hb : divFlatArg b₁ <;> simp only [hb] at hw_flat hfallback ⊢
      · exact hfallback
      · simp only [Op.wp, vals, Arg.val_imm, OpCode.wp_udiv] at hw_flat
        exact divConstOp_bin_wp hfallback fun he => (emitUDivConst_wp he fun _ r hr =>
          hk (r, ()) ((divFlatArg a₁).val / _, ()) (Prod.ext hr rfl) hw_flat.2).2
    | urem n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
      dsimp only [divFlatOp, divFlatArgs, tupMapArg] at hw_flat hfallback ⊢
      cases hb : divFlatArg b₁ <;> simp only [hb] at hw_flat hfallback ⊢
      · exact hfallback
      · simp only [Op.wp, vals, Arg.val_imm, OpCode.wp_urem] at hw_flat
        exact divConstOp_bin_wp hfallback fun he => (emitURemConst_wp he fun _ r hr =>
          hk (r, ()) ((divFlatArg a₁).val % _, ()) (Prod.ext hr rfl) hw_flat.2).2
    | sdiv n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
      dsimp only [divFlatOp, divFlatArgs, tupMapArg] at hw_flat hfallback ⊢
      cases hb : divFlatArg b₁ <;> simp only [hb] at hw_flat hfallback ⊢
      · exact hfallback
      · simp only [Op.wp, vals, Arg.val_imm, OpCode.wp_sdiv] at hw_flat
        exact divConstOp_bin_wp hfallback fun he => (emitSDivConst_wp he fun _ _ r hr =>
          hk (r, ()) ((divFlatArg a₁).val.sdiv _, ()) (Prod.ext hr rfl) hw_flat.2).2.2
    | srem n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
      dsimp only [divFlatOp, divFlatArgs, tupMapArg] at hw_flat hfallback ⊢
      cases hb : divFlatArg b₁ <;> simp only [hb] at hw_flat hfallback ⊢
      · exact hfallback
      · simp only [Op.wp, vals, Arg.val_imm, OpCode.wp_srem] at hw_flat
        exact divConstOp_bin_wp hfallback fun he => (emitSRemConst_wp he fun _ _ r hr =>
          hk (r, ()) ((divFlatArg a₁).val.srem _, ()) (Prod.ext hr rfl) hw_flat.2).2.2
    | _ => exact hfallback

private theorem divConstB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks (Arg V) L rs sig} →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (divConstB bs).get i xs = divConst (bs.get i (divArgTup xs))
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ _, _, .there i, xs => divConstB_get i xs

/-- Weakest-precondition preservation for `divConst`, proved via `Wf.induct`. -/
theorem divConst_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (Arg Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (Arg Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ m, (∀ p ∈ G, p.2.1.val = p.2.2) → (∀ p ∈ D, p.2.1 = p.2.2) →
      wp Γ Q X e₂ m → wp Γ Q X (divConst e₁) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro m hG hD hw; simp only [wp, divConst] at hw ⊢
    exact divConstOp_wp hG hop
      (fun r₁ r₂ hr hkr => ih r₁ r₂ m (ctx_val_append (tup_zip_vals_val r₁ r₂ hr) hG) hD hkr) hw
  | load t ha _ ih =>
    intro m hG hD ⟨v, hv, hk⟩; simp only [divConst, wp]; rw [divFlatArg_val hG ha]
    exact ⟨v, hv, ih (.var v) v m (ctx_val_cons_var hG v) hD hk⟩
  | store hv ha _ ih =>
    intro m hG hD ⟨hok, hk⟩; simp only [divConst, wp]
    rw [divFlatArg_val hG hv, divFlatArg_val hG ha]; exact ⟨hok, ih _ hG hD hk⟩
  | call f hargs _ ih =>
    intro m hG hD ⟨P, E, hΓ, hP, hE⟩; simp only [divConst, wp]
    rw [divFlatArgs_vals hG hargs]
    exact ⟨P, E, hΓ, fun r m' hr =>
      ih (divArgTup r) r m' (ctx_val_append (divArgTup_zip_val r) hG) hD (hP r m' hr), hE⟩
  | jnz hc _ _ iht ihe =>
    intro m hG hD ⟨ht, he⟩; simp only [divConst, wp]; rw [divFlatArg_val hG hc]
    exact ⟨fun h => iht m hG hD (ht h), fun h => ihe m hG hD (he h)⟩
  | jump hj hargs =>
    intro m hG hD hw; simp only [divConst, wp] at hw ⊢
    have hj' := hD _ hj; dsimp only at hj'; rw [hj', divFlatArgs_vals hG hargs]; exact hw
  | ret hvs =>
    intro m hG _ hw; simp only [divConst, wp] at hw ⊢; rw [divFlatArgs_vals hG hvs]; exact hw
  | exit f hargs =>
    intro m hG _ hw; simp only [divConst, wp] at hw ⊢; rw [divFlatArgs_vals hG hargs]; exact hw
  | hlt => intro _ _ _ hw; exact hw
  | group _ _ ihb ihk =>
    intro m hG hD hw Js hc
    refine ihk Js Js m hG (tup_zip_self_eq hD Js) (hw Js ?_)
    rw [closed_iff] at hc ⊢
    intro _ i xs m' hb
    exact hc i xs m' (by
      rw [divConstB_get]
      exact ihb Js Js i (divArgTup xs) xs m'
        (ctx_val_append (divArgTup_zip_val xs) hG) (tup_zip_self_eq hD Js) hb)

/-! ## `divConst` well-formedness preservation (`divConst_wf`) -/

private theorem divFlatArg_rel {V₁ V₂ : Ty → Type}
    {G_in : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_in, ArgRel G p.1 p.2.1 p.2.2)
    {t : Ty} {a₁ : Arg (Arg V₁) t} {a₂ : Arg (Arg V₂) t} :
    ArgRel G_in t a₁ a₂ → ArgRel G t (divFlatArg a₁) (divFlatArg a₂)
  | .var hm => hG _ hm
  | .imm c => .imm c

private theorem divFlatArgs_rel {V₁ V₂ : Ty → Type}
    {G_in : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_in, ArgRel G p.1 p.2.1 p.2.2)
    {ts : List Ty} {as₁ : Tup (Arg (Arg V₁)) ts} {as₂ : Tup (Arg (Arg V₂)) ts} :
    TRel (ArgRel G_in) as₁ as₂ → TRel (ArgRel G) (divFlatArgs as₁) (divFlatArgs as₂) :=
  TRel.tupMapArg_rel (fun _ => divFlatArg) (fun _ => divFlatArg) (fun ha => divFlatArg_rel hG ha)

private theorem mem_zip_divArgTup {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    ∀ p ∈ Tup.zip (divArgTup xs₁) (divArgTup xs₂), ArgRel (Tup.zip xs₁ xs₂) p.1 p.2.1 p.2.2
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), _, hp => by
    cases hp with
    | head => exact .var List.mem_cons_self
    | tail _ hp =>
      exact (mem_zip_divArgTup _ _ _ hp).weaken (fun _ hq => List.mem_cons_of_mem _ hq)

private theorem ctx_argRel_append {V₁ V₂ : Ty → Type}
    {H G_in : Ctx (Arg V₁) (Arg V₂)} {G₁ G₂ : Ctx V₁ V₂}
    (hH : ∀ p ∈ H, ArgRel G₁ p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G_in, ArgRel G₂ p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G_in, ArgRel (G₁ ++ G₂) p.1 p.2.1 p.2.2 := by
  intro p hp; rcases List.mem_append.1 hp with hp | hp
  · exact (hH p hp).weaken (fun _ hq => List.mem_append_left _ hq)
  · exact (hG p hp).weaken (fun _ hq => List.mem_append_right _ hq)

private theorem ctx_argRel_cons_var {V₁ V₂ : Ty → Type}
    {G_in : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_in, ArgRel G p.1 p.2.1 p.2.2) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    ∀ p ∈ (⟨t, .var v₁, .var v₂⟩ :: G_in), ArgRel (⟨t, v₁, v₂⟩ :: G) p.1 p.2.1 p.2.2 := by
  intro p hp; cases hp with
  | head => exact .var List.mem_cons_self
  | tail _ hp => exact (hG p hp).weaken (fun _ hq => List.mem_cons_of_mem _ hq)

private theorem wf_let_op2 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {t u r : Ty} (code : OpCode [t, u] [r])
    {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} {b₁ : Arg V₁ u} {b₂ : Arg V₂ u}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G u b₁ b₂)
    {k₁ : Tup V₁ [r] → Expr V₁ L₁ rs} {k₂ : Tup V₂ [r] → Expr V₂ L₂ rs}
    (hk : ∀ {G' : Ctx V₁ V₂}, (∀ p ∈ G, p ∈ G') → ∀ v₁ v₂, ArgRel G' r (.var v₁) (.var v₂) →
      Wf G' D (k₁ (v₁, ())) (k₂ (v₂, ()))) :
    Wf G D (.let_ (op2 code a₁ b₁) k₁) (.let_ (op2 code a₂ b₂) k₂) :=
  .let_ (.mk code (.cons ha (.cons hb .nil))) fun (v₁, ()) (v₂, ()) =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) v₁ v₂ (.var List.mem_cons_self)

private theorem wf_let_mulw {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {n : Nat}
    (code : OpCode [.bits n, .bits n] [.bits n, .bits n])
    {a₁ : Arg V₁ (.bits n)} {a₂ : Arg V₂ (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂)
    {b₁ : Arg V₁ (.bits n)} {b₂ : Arg V₂ (.bits n)} (hb : ArgRel G (.bits n) b₁ b₂)
    {k₁ : Tup V₁ [.bits n, .bits n] → Expr V₁ L₁ rs}
    {k₂ : Tup V₂ [.bits n, .bits n] → Expr V₂ L₂ rs}
    (hk : ∀ {G' : Ctx V₁ V₂}, (∀ p ∈ G, p ∈ G') → ∀ lo₁ lo₂ hi₁ hi₂,
      ArgRel G' (.bits n) (.var hi₁) (.var hi₂) →
      Wf G' D (k₁ (lo₁, hi₁, ())) (k₂ (lo₂, hi₂, ()))) :
    Wf G D (.let_ (op2 code a₁ b₁) k₁) (.let_ (op2 code a₂ b₂) k₂) :=
  .let_ (.mk code (.cons ha (.cons hb .nil))) fun (lo₁, hi₁, ()) (lo₂, hi₂, ()) =>
    hk (fun _ hp => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)) lo₁ lo₂ hi₁ hi₂
      (.var (List.mem_cons_of_mem _ List.mem_cons_self))

private abbrev EmitWf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G : Ctx V₁ V₂) (D : Ctx L₁ L₂)
    (o₁ : Option (Expr V₁ L₁ rs)) (o₂ : Option (Expr V₂ L₂ rs)) : Prop :=
  o₁.isSome = o₂.isSome ∧ ∀ {e₁ e₂}, o₁ = some e₁ → o₂ = some e₂ → Wf G D e₁ e₂

private abbrev ContWf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G : Ctx V₁ V₂) (D : Ctx L₁ L₂) (n : Nat)
    (k₁ : Arg V₁ (.bits n) → Expr V₁ L₁ rs) (k₂ : Arg V₂ (.bits n) → Expr V₂ L₂ rs) : Prop :=
  ∀ {G' : Ctx V₁ V₂}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' (.bits n) r₁ r₂ →
    Wf G' D (k₁ r₁) (k₂ r₂)

private theorem none_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} :
    EmitWf G D (none : Option (Expr V₁ L₁ rs)) (none : Option (Expr V₂ L₂ rs)) :=
  ⟨rfl, fun h _ => by cases h⟩

private theorem if_some_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (b : Bool)
    {a₁ : Expr V₁ L₁ rs} {a₂ : Expr V₂ L₂ rs} (h : b = true → Wf G D a₁ a₂) :
    EmitWf G D (if b then some a₁ else none) (if b then some a₂ else none) := by
  cases b <;> simp [EmitWf, h]

private theorem emitSDivAfter_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {n : Nat} (s : Nat)
    {t₁ : Arg V₁ (.bits n)} {t₂ : Arg V₂ (.bits n)} (ht : ArgRel G (.bits n) t₁ t₂)
    {k₁ : Arg V₁ (.bits n) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits n) → Expr V₂ L₂ rs}
    (hk : ContWf G D n k₁ k₂) :
    Wf G D
      (if s == 0 then
        .let_ (op2 (.lshr (.bits n)) t₁ (.imm (BitVec.ofNat n (n - 1)))) fun (sgn, ()) =>
        .let_ (op2 (.add (.bits n)) t₁ (.var sgn)) fun (q, ()) => k₁ (.var q)
      else
        .let_ (op2 (.ashr (.bits n)) t₁ (.imm (BitVec.ofNat n s))) fun (q0, ()) =>
        .let_ (op2 (.lshr (.bits n)) (.var q0) (.imm (BitVec.ofNat n (n - 1)))) fun (sgn, ()) =>
        .let_ (op2 (.add (.bits n)) (.var q0) (.var sgn)) fun (q, ()) => k₁ (.var q))
      (if s == 0 then
        .let_ (op2 (.lshr (.bits n)) t₂ (.imm (BitVec.ofNat n (n - 1)))) fun (sgn, ()) =>
        .let_ (op2 (.add (.bits n)) t₂ (.var sgn)) fun (q, ()) => k₂ (.var q)
      else
        .let_ (op2 (.ashr (.bits n)) t₂ (.imm (BitVec.ofNat n s))) fun (q0, ()) =>
        .let_ (op2 (.lshr (.bits n)) (.var q0) (.imm (BitVec.ofNat n (n - 1)))) fun (sgn, ()) =>
        .let_ (op2 (.add (.bits n)) (.var q0) (.var sgn)) fun (q, ()) => k₂ (.var q)) := by
  by_cases hs : s == 0
  · simp only [hs, ↓reduceIte]
    refine wf_let_op2 (.lshr (.bits n)) ht (.imm _) fun hsubA _ _ hs => ?_
    exact wf_let_op2 (.add (.bits n)) (ht.weaken hsubA) hs fun hsubB q1 q2 hq =>
      hk (fun _ hp => hsubB _ (hsubA _ hp)) (.var q1) (.var q2) hq
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    refine wf_let_op2 (.ashr (.bits n)) ht (.imm _) fun hsubA q01 q02 hq0 => ?_
    refine wf_let_op2 (.lshr (.bits n)) hq0 (.imm _) fun hsubB _ _ hs => ?_
    exact wf_let_op2 (.add (.bits n)) (hq0.weaken hsubB) hs fun hsubC q1 q2 hq =>
      hk (fun _ hp => hsubC _ (hsubB _ (hsubA _ hp))) (.var q1) (.var q2) hq

private theorem emitUDivConst_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {n : Nat}
    {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)} (hx : ArgRel G (.bits n) x₁ x₂) (d : BitVec n)
    {k₁ : Arg V₁ (.bits n) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits n) → Expr V₂ L₂ rs}
    (hk : ContWf G D n k₁ k₂) :
    EmitWf G D (emitUDivConst n x₁ d k₁) (emitUDivConst n x₂ d k₂) := by
  unfold emitUDivConst
  split; · exact none_wf
  · split; · exact none_wf
    · split
      · exact ⟨rfl, fun h₁ h₂ => by cases h₁; cases h₂; exact hk (fun _ hp => hp) x₁ x₂ hx⟩
      · cases hfp : findPow2Shift n d with
        | some sh =>
          dsimp only; exact if_some_wf _ fun _ =>
            wf_let_op2 (.lshr (.bits n)) hx (.imm _) fun hsub q1 q2 hr =>
              hk hsub (.var q1) (.var q2) hr
        | none =>
          dsimp only; cases hfm : findUMagic n d with
          | none => exact none_wf
          | some val =>
            rcases val with ⟨M, s, addShift⟩
            cases addShift <;> dsimp only
            · exact if_some_wf _ fun _ =>
                wf_let_mulw (.umulw n) hx (.imm _) fun hsub1 _ _ _ _ hhi =>
                  wf_let_op2 (.lshr (.bits n)) hhi (.imm _) fun hsub2 q1 q2 hr =>
                    hk (fun _ hp => hsub2 _ (hsub1 _ hp)) (.var q1) (.var q2) hr
            · exact if_some_wf _ fun _ =>
                wf_let_mulw (.umulw n) hx (.imm _) fun hsub1 _ _ _ _ hhi =>
                  wf_let_op2 (.sub (.bits n)) (hx.weaken hsub1) hhi fun hsub2 _ _ ht1 =>
                    wf_let_op2 (.lshr (.bits n)) ht1 (.imm _) fun hsub3 _ _ ht2 =>
                      wf_let_op2 (.add (.bits n))
                        (hhi.weaken (fun _ hp => hsub3 _ (hsub2 _ hp))) ht2 fun hsub4 _ _ ht3 =>
                          wf_let_op2 (.lshr (.bits n)) ht3 (.imm _) fun hsub5 q1 q2 hr =>
                            hk (fun _ hp => hsub5 _ (hsub4 _ (hsub3 _ (hsub2 _ (hsub1 _ hp)))))
                              (.var q1) (.var q2) hr

private theorem emitURemConst_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {n : Nat}
    {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)} (hx : ArgRel G (.bits n) x₁ x₂) (d : BitVec n)
    {k₁ : Arg V₁ (.bits n) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits n) → Expr V₂ L₂ rs}
    (hk : ContWf G D n k₁ k₂) :
    EmitWf G D (emitURemConst n x₁ d k₁) (emitURemConst n x₂ d k₂) := by
  unfold emitURemConst
  split; · exact none_wf
  · split; · exact none_wf
    · split
      · exact ⟨rfl, fun h₁ h₂ => by
          cases h₁; cases h₂
          exact hk (fun _ hp => hp) (.imm 0#n) (.imm 0#n) (.imm (t := .bits n) 0#n)⟩
      · cases hfp : findPow2Shift n d with
        | some sh =>
          dsimp only; exact if_some_wf _ fun _ =>
            wf_let_op2 (.and (.bits n)) hx (.imm _) fun hsub r1 r2 hr =>
              hk hsub (.var r1) (.var r2) hr
        | none =>
          dsimp only; exact emitUDivConst_wf hx d fun hsub1 _ _ hq =>
            wf_let_op2 (.mul (.bits n)) hq (.imm d) fun hsub2 _ _ hp =>
              wf_let_op2 (.sub (.bits n)) (hx.weaken (fun _ pm => hsub2 _ (hsub1 _ pm))) hp
                fun hsub3 r1 r2 hr =>
                  hk (fun _ pm => hsub3 _ (hsub2 _ (hsub1 _ pm))) (.var r1) (.var r2) hr

private theorem emitSDivConst_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {n : Nat}
    {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)} (hx : ArgRel G (.bits n) x₁ x₂) (d : BitVec n)
    {k₁ : Arg V₁ (.bits n) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits n) → Expr V₂ L₂ rs}
    (hk : ContWf G D n k₁ k₂) :
    EmitWf G D (emitSDivConst n x₁ d k₁) (emitSDivConst n x₂ d k₂) := by
  unfold emitSDivConst
  split; · exact none_wf
  · split; · exact none_wf
    · split
      · exact ⟨rfl, fun h₁ h₂ => by cases h₁; cases h₂; exact hk (fun _ hp => hp) x₁ x₂ hx⟩
      · cases hfp : findSPow2Shift n d with
        | some sh =>
          dsimp only
          by_cases hc : sPow2Cert n d sh = true
          · simp only [hc, ↓reduceIte]
            by_cases hm1 : sh == 1
            · simp only [hm1, ↓reduceIte]
              refine ⟨rfl, fun h₁ h₂ => ?_⟩; cases h₁; cases h₂
              refine wf_let_op2 (.lshr (.bits n)) hx (.imm _) fun hsub1 _ _ ht1 => ?_
              refine wf_let_op2 (.add (.bits n)) (hx.weaken hsub1) ht1 fun hsub2 _ _ ht2 => ?_
              exact wf_let_op2 (.ashr (.bits n)) ht2 (.imm _) fun hsub3 q1 q2 hr =>
                hk (fun _ hp => hsub3 _ (hsub2 _ (hsub1 _ hp))) (.var q1) (.var q2) hr
            · simp only [hm1, Bool.false_eq_true, ↓reduceIte]
              refine ⟨rfl, fun h₁ h₂ => ?_⟩; cases h₁; cases h₂
              refine wf_let_op2 (.ashr (.bits n)) hx (.imm _) fun hsub1 _ _ ht1 => ?_
              refine wf_let_op2 (.lshr (.bits n)) ht1 (.imm _) fun hsub2 _ _ ht2 => ?_
              refine wf_let_op2 (.add (.bits n))
                (hx.weaken (fun _ hp => hsub2 _ (hsub1 _ hp))) ht2 fun hsub3 _ _ ht3 => ?_
              exact wf_let_op2 (.ashr (.bits n)) ht3 (.imm _) fun hsub4 q1 q2 hr =>
                hk (fun _ hp => hsub4 _ (hsub3 _ (hsub2 _ (hsub1 _ hp)))) (.var q1) (.var q2) hr
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact none_wf
        | none =>
          dsimp only; cases hfm : findSMagic n d with
          | none => exact none_wf
          | some val =>
            rcases val with ⟨A, s⟩; dsimp only
            exact if_some_wf _ fun _ => by
              refine wf_let_mulw (.smulw n) hx (.imm _) fun hsub1 _ _ _ _ hhi => ?_
              by_cases hc1 : (decide (0 < d.toInt) && decide ((BitVec.ofInt n
                  (if 0 < d.toInt then (A : Int) else -(A : Int))).toInt < 0)) = true
              · simp only [hc1, ↓reduceIte]
                exact wf_let_op2 (.add (.bits n)) hhi (hx.weaken hsub1) fun hsub2 t1 t2 ht =>
                  emitSDivAfter_wf s ht fun hsubA => hk (fun _ hp => hsubA _ (hsub2 _ (hsub1 _ hp)))
              · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
                by_cases hc2 : (decide (d.toInt < 0) && decide (0 < (BitVec.ofInt n
                    (if 0 < d.toInt then (A : Int) else -(A : Int))).toInt)) = true
                · simp only [hc2, ↓reduceIte]
                  exact wf_let_op2 (.sub (.bits n)) hhi (hx.weaken hsub1) fun hsub2 t1 t2 ht =>
                    emitSDivAfter_wf s ht fun hsubA =>
                      hk (fun _ hp => hsubA _ (hsub2 _ (hsub1 _ hp)))
                · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
                  exact emitSDivAfter_wf s hhi fun hsubA => hk (fun _ hp => hsubA _ (hsub1 _ hp))

private theorem emitSRemConst_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {n : Nat}
    {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)} (hx : ArgRel G (.bits n) x₁ x₂) (d : BitVec n)
    {k₁ : Arg V₁ (.bits n) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits n) → Expr V₂ L₂ rs}
    (hk : ContWf G D n k₁ k₂) :
    EmitWf G D (emitSRemConst n x₁ d k₁) (emitSRemConst n x₂ d k₂) := by
  unfold emitSRemConst
  split; · exact none_wf
  · split; · exact none_wf
    · split
      · exact ⟨rfl, fun h₁ h₂ => by
          cases h₁; cases h₂
          exact hk (fun _ hp => hp) (.imm 0#n) (.imm 0#n) (.imm (t := .bits n) 0#n)⟩
      · exact emitSDivConst_wf hx d fun hsub1 _ _ hq =>
          wf_let_op2 (.mul (.bits n)) hq (.imm d) fun hsub2 _ _ hp =>
            wf_let_op2 (.sub (.bits n)) (hx.weaken (fun _ pm => hsub2 _ (hsub1 _ pm))) hp
              fun hsub3 r1 r2 hr =>
                hk (fun _ pm => hsub3 _ (hsub2 _ (hsub1 _ pm))) (.var r1) (.var r2) hr

private theorem divConstOp_imm_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {o₁ : Option (Expr V₁ L₁ rs)} {o₂ : Option (Expr V₂ L₂ rs)}
    {fb₁ : Expr V₁ L₁ rs} {fb₂ : Expr V₂ L₂ rs} (hfb : Wf G D fb₁ fb₂)
    (h : EmitWf G D o₁ o₂) :
    Wf G D (o₁.getD fb₁) (o₂.getD fb₂) := by
  cases he₁ : o₁ <;> cases he₂ : o₂
  · exact hfb
  · exfalso; simp [EmitWf, he₁, he₂] at h
  · exfalso; simp [EmitWf, he₁, he₂] at h
  · exact h.2 he₁ he₂

private theorem divArgTup_trel {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    TRel (ArgRel (Tup.zip xs₁ xs₂)) (divArgTup xs₁) (divArgTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_, _), (_, _) =>
    .cons (.var List.mem_cons_self)
      (TRel.mono (fun _ _ _ h => ArgRel.weaken (fun _ hp => List.mem_cons_of_mem _ hp) h)
        (divArgTup_trel _ _))

private theorem divConstOp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G_in : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    (hG : ∀ p ∈ G_in, ArgRel G p.1 p.2.1 p.2.2)
    {op₁ : Op (Arg V₁) ts} {op₂ : Op (Arg V₂) ts} (hop : OpRel G_in op₁ op₂)
    {k₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs} {k₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs}
    (hk : ∀ {G' : Ctx V₁ V₂}, (∀ p ∈ G, p ∈ G') →
      ∀ (r₁ : Tup (Arg V₁) ts) (r₂ : Tup (Arg V₂) ts), TRel (ArgRel G') r₁ r₂ →
        Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (divConstOp op₁ k₁) (divConstOp op₂ k₂) := by
  cases hop with
  | @mk _ _ code args₁ args₂ hargs =>
    have hflat_args := divFlatArgs_rel hG hargs
    have hfallback :
        Wf G D (.let_ (divFlatOp ⟨code, args₁⟩) fun xs => k₁ (divArgTup xs))
               (.let_ (divFlatOp ⟨code, args₂⟩) fun xs => k₂ (divArgTup xs)) :=
      .let_ (.mk code hflat_args) fun xs₁ xs₂ =>
        hk (fun _ hp => List.mem_append_right _ hp) _ _
          (TRel.mono (fun _ _ _ h => ArgRel.weaken (fun _ hp => List.mem_append_left G hp) h)
            (divArgTup_trel xs₁ xs₂))
    unfold divConstOp; dsimp only [divFlatOp]
    cases code with
    | udiv n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hflat_args with _ | ⟨hx, _ | ⟨hd, _⟩⟩
      dsimp only [divFlatOp, divFlatArgs, tupMapArg] at hfallback ⊢
      cases hb₁ : divFlatArg b₁ <;> cases hb₂ : divFlatArg b₂ <;>
        simp only [hb₁, hb₂] at hd hfallback ⊢
      all_goals first
        | exact hfallback
        | (cases hd <;> exact divConstOp_imm_wf hfallback (emitUDivConst_wf hx _
            fun hsub r₁ r₂ hr => hk hsub (r₁, ()) (r₂, ()) (.cons hr .nil)))
    | urem n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hflat_args with _ | ⟨hx, _ | ⟨hd, _⟩⟩
      dsimp only [divFlatOp, divFlatArgs, tupMapArg] at hfallback ⊢
      cases hb₁ : divFlatArg b₁ <;> cases hb₂ : divFlatArg b₂ <;>
        simp only [hb₁, hb₂] at hd hfallback ⊢
      all_goals first
        | exact hfallback
        | (cases hd <;> exact divConstOp_imm_wf hfallback (emitURemConst_wf hx _
            fun hsub r₁ r₂ hr => hk hsub (r₁, ()) (r₂, ()) (.cons hr .nil)))
    | sdiv n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hflat_args with _ | ⟨hx, _ | ⟨hd, _⟩⟩
      dsimp only [divFlatOp, divFlatArgs, tupMapArg] at hfallback ⊢
      cases hb₁ : divFlatArg b₁ <;> cases hb₂ : divFlatArg b₂ <;>
        simp only [hb₁, hb₂] at hd hfallback ⊢
      all_goals first
        | exact hfallback
        | (cases hd <;> exact divConstOp_imm_wf hfallback (emitSDivConst_wf hx _
            fun hsub r₁ r₂ hr => hk hsub (r₁, ()) (r₂, ()) (.cons hr .nil)))
    | srem n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hflat_args with _ | ⟨hx, _ | ⟨hd, _⟩⟩
      dsimp only [divFlatOp, divFlatArgs, tupMapArg] at hfallback ⊢
      cases hb₁ : divFlatArg b₁ <;> cases hb₂ : divFlatArg b₂ <;>
        simp only [hb₁, hb₂] at hd hfallback ⊢
      all_goals first
        | exact hfallback
        | (cases hd <;> exact divConstOp_imm_wf hfallback (emitSRemConst_wf hx _
            fun hsub r₁ r₂ hr => hk hsub (r₁, ()) (r₂, ()) (.cons hr .nil)))
    | _ => exact hfallback

private theorem mem_zip_argRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → {as₁ : Tup (Arg V₁) ts} → {as₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G) as₁ as₂ → ∀ p ∈ Tup.zip as₁ as₂, ArgRel G p.1 p.2.1 p.2.2
  | [], (), (), .nil, _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), .cons h hs, _, hp => by
    cases hp with | head => exact h | tail _ hp => exact mem_zip_argRel hs _ hp

/-- Well-formedness preservation for `divConst`, proved via `Wf.induct`. -/
theorem divConst_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G_in : Ctx (Arg V₁) (Arg V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (Arg V₁) L₁ rs} {e₂ : Expr (Arg V₂) L₂ rs}
    (hwf : Wf G_in D e₁ e₂) :
    ∀ {G : Ctx V₁ V₂}, (∀ p ∈ G_in, ArgRel G p.1 p.2.1 p.2.2) →
      Wf G D (divConst e₁) (divConst e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro G hG; simp only [divConst]
    refine divConstOp_wf hG hop fun hsub r₁ r₂ hr => ih r₁ r₂ fun p hp => ?_
    rcases List.mem_append.1 hp with hp | hp
    · exact mem_zip_argRel hr p hp
    · exact (hG p hp).weaken hsub
  | load t ha _ ih =>
    intro G hG; exact .load t (divFlatArg_rel hG ha) fun v₁ v₂ =>
      ih (.var v₁) (.var v₂) (ctx_argRel_cons_var hG v₁ v₂)
  | store hv ha _ ih =>
    intro G hG; exact .store (divFlatArg_rel hG hv) (divFlatArg_rel hG ha) (ih hG)
  | call f hargs _ ih =>
    intro G hG; exact .call f (divFlatArgs_rel hG hargs) fun xs₁ xs₂ =>
      ih (divArgTup xs₁) (divArgTup xs₂) (ctx_argRel_append (mem_zip_divArgTup xs₁ xs₂) hG)
  | jnz hc _ _ iht ihe =>
    intro G hG; exact .jnz (divFlatArg_rel hG hc) (iht hG) (ihe hG)
  | jump hj hargs => intro G hG; exact .jump hj (divFlatArgs_rel hG hargs)
  | ret hvs => intro G hG; exact .ret (divFlatArgs_rel hG hvs)
  | exit f hargs => intro G hG; exact .exit f (divFlatArgs_rel hG hargs)
  | hlt => intro _ _; exact .hlt
  | group _ _ ihb ihk =>
    intro G hG
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ihk Js₁ Js₂ hG)
    simp only [divConstB_get]
    exact ihb Js₁ Js₂ i (divArgTup xs₁) (divArgTup xs₂)
      (ctx_argRel_append (mem_zip_divArgTup xs₁ xs₂) hG)

/-! ## Closed function theorems -/

/-- `Func.divConst` preserves `Func.Wf`. -/
theorem Func.divConst_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.divConst f).Wf := fun V₁ V₂ L₁ L₂ xs₁ xs₂ =>
  LeanQbe.T.divConst_wf (hf (Arg V₁) (Arg V₂) L₁ L₂ (divArgTup xs₁) (divArgTup xs₂))
    (mem_zip_divArgTup xs₁ xs₂)

/-- `Func.divConst` refines function contracts: any source contract holds on `Func.divConst f`. -/
theorem Func.divConst_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.divConst f) xs m Q X :=
  LeanQbe.T.divConst_wp (hf (Arg Val) Val Cont Cont (divArgTup xs) xs) m
    (divArgTup_zip_val xs) (fun _ hp => nomatch hp) h

end LeanQbe.T
