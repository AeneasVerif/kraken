module

public import LeanQbe.T.LeanLCNF.LcnfC0Strings
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
import LeanQbe.T.LeanLCNF.LcnfC0StringsProofAlloc
import LeanQbe.T.LeanLCNF.LcnfC0StringsProof1

/-!
# Soundness Proofs for `LcnfC0Strings`, Part 4a: `lcnf_nat_to_str` Helpers & AST Pieces

Arithmetic/MPZ helpers, Phases 1–2 WP lemmas, and factored AST sub-expressions for
`lcnf_nat_to_str` (`LcnfC0StringsProof4`).
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T Std.ExtHashMap

public section

theorem msep_left_comm (p q r : Mem 64 → Prop) : p ⋆ (q ⋆ r) = q ⋆ (p ⋆ r) := by
  rw [← Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm p q, Std.ExtHashMap.sep_assoc]

/-! ## Pure arithmetic, decimal-digit, MPZ-limb, and heap helpers for `lcnf_nat_to_str` -/

theorem bv64_toNat_ofNat_lt4 {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv64_and_mask32 {a : BitVec 64} :
    (a &&& 4294967295#64).toNat = a.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and, show (4294967295#64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem bv64_ushiftRight32 {a : BitVec 64} : (a >>> 32).toNat = a.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_pack32_toNat {hi lo : BitVec 64}
    (hhi : hi.toNat < 2 ^ 32) (hlo : lo.toNat < 2 ^ 32) :
    ((hi <<< 32) ||| lo).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  have hdisj : ((hi <<< 32) &&& lo) = 0#64 := by
    ext i hi_lt
    simp only [BitVec.getElem_and, BitVec.getElem_zero, Bool.and_eq_false_iff,
      BitVec.getElem_shiftLeft]
    by_cases h : i < 32
    · left; simp [h]
    · right
      rw [← BitVec.getLsbD_eq_getElem, ← BitVec.testBit_toNat]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, BitVec.toNat_add,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hmod1 : (hi.toNat * 2 ^ 32) % 2 ^ 64 = hi.toNat * 2 ^ 32 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod1, Nat.mod_eq_of_lt (by omega)]

theorem bv64_pack32_low {a b : BitVec 64} (ha : a.toNat < 2 ^ 32) :
    ((a ||| (b <<< 32)) &&& 4294967295#64) = a := by
  ext i hi_lt
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft]
  by_cases h : i < 32
  · have hm : (4294967295#64)[i] = true := by
      rw [← BitVec.getLsbD_eq_getElem, ← BitVec.testBit_toNat,
        show (4294967295#64).toNat = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]
      simp [h]
    simp [h, hm]
  · have hm : (4294967295#64)[i] = false := by
      rw [← BitVec.getLsbD_eq_getElem, ← BitVec.testBit_toNat,
        show (4294967295#64).toNat = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]
      simp [h]
    have ha0 : a[i] = false := by
      rw [← BitVec.getLsbD_eq_getElem, ← BitVec.testBit_toNat]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hm, ha0]

private theorem bv64_pack32_high {a b : BitVec 64}
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    ((a ||| (b <<< 32)) >>> 32) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.or_comm, bv64_ushiftRight32, bv64_pack32_toNat hb ha]
  omega

private theorem align8_ge (n : Nat) : n ≤ align8 n := by unfold align8; omega

private theorem align8_mono {a b : Nat} (h : a ≤ b) : align8 a ≤ align8 b := by
  unfold align8; exact Nat.mul_le_mul_right 8 (Nat.div_le_div_right (by omega))

theorem align8_mod8 (n : Nat) : align8 n % 8 = 0 := by
  unfold align8; exact Nat.mul_mod_left _ 8

theorem strAllocBytes_mono4 {a b : Nat} (h : a ≤ b) : strAllocBytes a ≤ strAllocBytes b := by
  unfold strAllocBytes; exact align8_mono (by omega)

theorem natDigitsRev_zero : natDigitsRev 0 = [] := by rw [natDigitsRev.eq_def]; simp

private theorem natDigitsRev_ne {n : Nat} (hn : n ≠ 0) :
    natDigitsRev n = UInt8.ofNat (48 + n % 10) :: natDigitsRev (n / 10) := by
  rw [natDigitsRev.eq_def, dite_eq_right hn]

theorem natDigitsRev_length_pos {n : Nat} (hn : 0 < n) : 1 ≤ (natDigitsRev n).length := by
  rw [natDigitsRev_ne (by omega)]; simp

theorem natDigitsRev_length_le {k n : Nat} (hk : n < 10 ^ k) :
    (natDigitsRev n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hk
    subst hn0
    rw [natDigitsRev_zero]
    simp
  | succ k ih =>
    by_cases hn : n = 0
    · subst hn; rw [natDigitsRev_zero]; simp
    · have hlt : n / 10 < 10 ^ k :=
        Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ'] at hk; omega)
      rw [natDigitsRev_ne hn]
      simp only [List.length_cons]
      exact Nat.succ_le_succ (ih hlt)

private theorem pow2_63_lt_pow10_19 : 2 ^ 63 < 10 ^ 19 := by decide
private theorem pow2_64_lt_pow10_20 : 2 ^ 64 < 10 ^ 20 := by decide

theorem pow_64_lt_pow10_20 {k : Nat} (hk : 0 < k) : (2 ^ 64) ^ k < (10 ^ 20) ^ k := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero => exact pow2_64_lt_pow10_20
    | succ k ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      have h1 : (2 ^ 64) ^ (k + 1) * 2 ^ 64 < (10 ^ 20) ^ (k + 1) * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right (ih (Nat.succ_pos _)) (by decide)
      have h2 : (10 ^ 20) ^ (k + 1) * 2 ^ 64 < (10 ^ 20) ^ (k + 1) * 10 ^ 20 :=
        Nat.mul_lt_mul_of_pos_left pow2_64_lt_pow10_20 (Nat.pow_pos (by decide))
      exact Nat.lt_trans h1 h2

theorem natDigitsRev_take_step {val v : Nat} {dlen : Nat}
    (hv : 0 < v) (hpref : (natDigitsRev val).take dlen ++ natDigitsRev v = natDigitsRev val) :
    (h1 : dlen < (natDigitsRev val).length) →
      (natDigitsRev val)[dlen] = UInt8.ofNat (48 + v % 10) ∧
        (natDigitsRev val).take (dlen + 1) ++ natDigitsRev (v / 10) = natDigitsRev val := by
  intro h1
  have hrev := natDigitsRev_ne (by omega : v ≠ 0)
  rw [hrev] at hpref
  have htakeLen : ((natDigitsRev val).take dlen).length = dlen :=
    List.length_take_of_le (Nat.le_of_lt h1)
  have hget : (natDigitsRev val)[dlen] = UInt8.ofNat (48 + v % 10) := by
    have hidx : (natDigitsRev val)[dlen] =
        ((natDigitsRev val).take dlen ++
          UInt8.ofNat (48 + v % 10) :: natDigitsRev (v / 10))[dlen]'(by rw [hpref]; exact h1) := by
      congr 1; exact hpref.symm
    rw [hidx, List.getElem_append_right (by omega)]
    simp [htakeLen]
  refine ⟨hget, ?_⟩
  rw [List.take_add_one, List.getElem?_eq_getElem h1]
  simp only [Option.toList_some, List.append_assoc, List.cons_append, List.nil_append]
  rw [hget]
  exact hpref

theorem mpzLimbsVal_nil : mpzLimbsVal [] = 0 := rfl

private theorem mpzLimbsVal_cons (x : BitVec 64) (xs : List (BitVec 64)) :
    mpzLimbsVal (x :: xs) = x.toNat + 2 ^ 64 * mpzLimbsVal xs := rfl

private theorem mpzLimbsVal_append_singleton (xs : List (BitVec 64)) (x : BitVec 64) :
    mpzLimbsVal (xs ++ [x]) = mpzLimbsVal xs + (2 ^ 64) ^ xs.length * x.toNat := by
  induction xs with
  | nil => simp [mpzLimbsVal]
  | cons y ys ih =>
    simp only [List.cons_append, mpzLimbsVal_cons, List.length_cons] at ih ⊢
    rw [ih, Nat.mul_add, Nat.pow_succ (2 ^ 64), Nat.mul_comm ((2 ^ 64) ^ ys.length) (2 ^ 64),
      ← Nat.mul_assoc, Nat.add_assoc]

theorem mpzLimbsVal_lt_pow (xs : List (BitVec 64)) :
    mpzLimbsVal xs < (2 ^ 64) ^ xs.length := by
  induction xs with
  | nil => simp [mpzLimbsVal]
  | cons x xs ih =>
    simp only [mpzLimbsVal_cons, List.length_cons]
    have hx : x.toNat < 2 ^ 64 := x.isLt
    have hpos : 1 ≤ (2 ^ 64) ^ xs.length := Nat.pow_pos (by decide)
    have hmul : 2 ^ 64 * mpzLimbsVal xs ≤ 2 ^ 64 * ((2 ^ 64) ^ xs.length - 1) :=
      Nat.mul_le_mul_left (2 ^ 64) (Nat.le_pred_of_lt ih)
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm (2 ^ 64) ((2 ^ 64) ^ xs.length),
      ← Nat.pow_succ (2 ^ 64)] at hmul
    have hge : 2 ^ 64 ≤ (2 ^ 64) ^ (xs.length + 1) := by
      rw [Nat.pow_succ (2 ^ 64)]
      exact Nat.le_mul_of_pos_left (2 ^ 64) hpos
    omega

theorem list_take_succ_append4 {α : Type _} (xs : List α) {k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ xs.length) :
    List.take k xs = List.take (k - 1) xs ++ [xs[k - 1]] := by
  have hk' : k - 1 < xs.length := by omega
  have heq : k = (k - 1) + 1 := by omega
  conv => lhs; rw [heq, List.take_add_one]
  rw [List.getElem?_eq_getElem hk']
  simp only [Option.toList_some]

theorem mpzLimbsVal_pos_of_last_ne {xs : List (BitVec 64)} {k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ xs.length) (hne : xs[k - 1] ≠ 0#64) :
    0 < mpzLimbsVal (List.take k xs) := by
  rw [list_take_succ_append4 xs hk1 hk2, mpzLimbsVal_append_singleton]
  have hnz : 0 < (xs[k - 1]).toNat := Nat.pos_of_ne_zero fun h0 => hne (BitVec.eq_of_toNat_eq h0)
  have hmul := Nat.mul_pos
    (Nat.pow_pos (by decide) : 1 ≤ (2 ^ 64) ^ (List.take (k - 1) xs).length) hnz
  omega

private theorem trimZeroLimbsLen_le (xs : List (BitVec 64)) (k : Nat) :
    trimZeroLimbsLen xs k ≤ k := by
  induction k with
  | zero => rw [trimZeroLimbsLen.eq_1]; omega
  | succ k ih =>
    rw [trimZeroLimbsLen.eq_2]
    by_cases h : xs.getD k 0#64 = 0#64
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right h]; omega

theorem trimZeroLimbsLen_val (xs : List (BitVec 64)) (k : Nat) :
    mpzLimbsVal (List.take (trimZeroLimbsLen xs k) xs) = mpzLimbsVal (List.take k xs) := by
  induction k with
  | zero => rw [trimZeroLimbsLen.eq_1]
  | succ k ih =>
    rw [trimZeroLimbsLen.eq_2]
    by_cases h : xs.getD k 0#64 = 0#64
    · rw [ite_eq_left h, ih]
      by_cases hlt : k < xs.length
      · have hxk : xs[k] = 0#64 := by
          have hgetD : xs.getD k 0#64 = xs[k] := by simp [List.getD, hlt]
          rw [← hgetD, h]
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some]
        rw [mpzLimbsVal_append_singleton, hxk]
        simp
      · have hle : xs.length ≤ k := Nat.le_of_not_lt hlt
        rw [List.take_of_length_le (Nat.le_trans hle (Nat.le_succ k)),
          List.take_of_length_le hle]
    · rw [ite_eq_right h]

theorem trimZeroLimbsLen_last_ne (xs : List (BitVec 64)) (k : Nat)
    (hk : k ≤ xs.length) (hpos : 0 < trimZeroLimbsLen xs k) :
    ∀ {c}, c = trimZeroLimbsLen xs k → c ≤ xs.length ∧ (0 < c) ∧
      ∃ hlt : c - 1 < xs.length, xs[c - 1]'hlt ≠ 0#64 := by
  induction k with
  | zero =>
    intro c hc
    rw [trimZeroLimbsLen.eq_1] at hc hpos
    omega
  | succ k ih =>
    intro c hc
    rw [trimZeroLimbsLen.eq_2] at hc hpos
    by_cases h : xs.getD k 0#64 = 0#64
    · rw [ite_eq_left h] at hc hpos
      exact ih (by omega) hpos hc
    · rw [ite_eq_right h] at hc
      subst hc
      have hlt : k + 1 - 1 < xs.length := by omega
      refine ⟨hk, by omega, hlt, ?_⟩
      simp only [Nat.add_sub_cancel]
      have hgetD : xs.getD k 0#64 = xs[k] := by
        simp [List.getD, List.getElem?_eq_getElem (by omega : k < xs.length)]
      rwa [← hgetD]

theorem list_take_set_of_le4 {α : Type _} (xs : List α) {i j : Nat} (v : α)
    (hle : i ≤ j) : List.take i (xs.set j v) = List.take i xs := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_set]
  · intro idx h1 h2
    have hidx : idx < i := by simp only [List.length_take] at h2; omega
    simp only [List.getElem_take]
    rw [List.getElem_set_ne (by omega)]

private theorem list_drop_take_set_succ {xs : List (BitVec 64)} {k len : Nat}
    (w : BitVec 64) (hk1 : 1 ≤ k) (hk2 : k ≤ len) (hlen : len ≤ xs.length) :
    List.drop (k - 1) (List.take len (xs.set (k - 1) w)) =
      w :: List.drop k (List.take len xs) := by
  have hlen1 : (List.take len (xs.set (k - 1) w)).length = len := by
    rw [List.length_take, List.length_set]; exact Nat.min_eq_left hlen
  have hlen2 : (List.take len xs).length = len := List.length_take_of_le hlen
  apply List.ext_getElem
  · simp only [List.length_drop, hlen1, hlen2, List.length_cons]
    omega
  · intro idx h1 h2
    cases idx with
    | zero =>
      simp only [List.getElem_drop, Nat.add_zero, List.getElem_take, List.getElem_cons_zero]
      have hkl : k - 1 < (xs.set (k - 1) w).length := by rw [List.length_set]; omega
      rw [List.getElem_set_self hkl]
    | succ m =>
      simp only [List.getElem_cons_succ, List.getElem_drop, List.getElem_take]
      have hm : k + m < len := by
        simp only [List.length_drop, hlen2, List.length_cons] at h2
        omega
      have hidx : k - 1 + (m + 1) = k + m := by omega
      have hset : (xs.set (k - 1) w)[k - 1 + (m + 1)]'(by rw [List.length_set]; omega) =
          xs[k + m]'(by omega) := by
        rw [List.getElem_set_ne (by omega)]
        simp only [hidx]
      exact hset

theorem u32_split_div10_step (remIn hi lo : Nat)
    (hrem : remIn < 10) (hhi : hi < 2 ^ 32) (hlo : lo < 2 ^ 32) :
    (remIn * 2 ^ 32 + hi) / 10 < 2 ^ 32 ∧
      ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) / 10 < 2 ^ 32 ∧
      ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) % 10 < 10 ∧
      remIn * 2 ^ 64 + (hi * 2 ^ 32 + lo) =
        10 * ((remIn * 2 ^ 32 + hi) / 10 * 2 ^ 32 +
          ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) / 10) +
          ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) % 10 := by
  have hc1 : remIn * 2 ^ 32 + hi < 10 * 2 ^ 32 := by omega
  have hq1 : (remIn * 2 ^ 32 + hi) / 10 < 2 ^ 32 := Nat.div_lt_of_lt_mul hc1
  have hr1 : (remIn * 2 ^ 32 + hi) % 10 < 10 := Nat.mod_lt _ (by decide)
  have hm1 : (remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 ≤ 9 * 2 ^ 32 :=
    Nat.mul_le_mul_right (2 ^ 32) (Nat.le_pred_of_lt hr1)
  have hc2 : (remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo < 10 * 2 ^ 32 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_of_le_of_lt hm1 hlo) (by decide)
  have hq2 : ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) / 10 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul hc2
  have hr2 : ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) % 10 < 10 := Nat.mod_lt _ (by decide)
  refine ⟨hq1, hq2, hr2, ?_⟩
  have hdiv1 := Nat.div_add_mod (remIn * 2 ^ 32 + hi) 10
  have hdiv2 := Nat.div_add_mod ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) 10
  have h2 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  calc remIn * 2 ^ 64 + (hi * 2 ^ 32 + lo)
      = (remIn * 2 ^ 32 + hi) * 2 ^ 32 + lo := by
          rw [h2, ← Nat.mul_assoc, Nat.add_mul, Nat.add_assoc]
    _ = (10 * ((remIn * 2 ^ 32 + hi) / 10) + (remIn * 2 ^ 32 + hi) % 10) * 2 ^ 32 + lo := by
          rw [hdiv1]
    _ = 10 * ((remIn * 2 ^ 32 + hi) / 10 * 2 ^ 32) +
          ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) := by
          rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    _ = 10 * ((remIn * 2 ^ 32 + hi) / 10 * 2 ^ 32) +
          (10 * (((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) / 10) +
            ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) % 10) := by
          rw [hdiv2]
    _ = 10 * ((remIn * 2 ^ 32 + hi) / 10 * 2 ^ 32 +
          ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) / 10) +
          ((remIn * 2 ^ 32 + hi) % 10 * 2 ^ 32 + lo) % 10 := by
          rw [← Nat.add_assoc, ← Nat.mul_add]

theorem mpz_div10_invariant_step {xs : List (BitVec 64)} {k len remIn r2 V : Nat}
    (w : BitVec 64) (hk1 : 1 ≤ k) (hk2 : k ≤ len) (hlen : len ≤ xs.length)
    (hstep : remIn * 2 ^ 64 + (xs[k - 1]'(by omega)).toNat = 10 * w.toNat + r2)
    (hinv : mpzLimbsVal (List.take k xs) +
      (2 ^ 64) ^ k * (10 * mpzLimbsVal (List.drop k (List.take len xs)) + remIn) = V) :
    let xs' := xs.set (k - 1) w
    mpzLimbsVal (List.take (k - 1) xs') +
      (2 ^ 64) ^ (k - 1) * (10 * mpzLimbsVal (List.drop (k - 1) (List.take len xs')) + r2) =
      V := by
  intro xs'
  rw [list_take_set_of_le4 xs w (by omega), list_drop_take_set_succ w hk1 hk2 hlen,
    mpzLimbsVal_cons]
  rw [list_take_succ_append4 xs hk1 (by omega), mpzLimbsVal_append_singleton] at hinv
  have hpow : (2 ^ 64) ^ k = (2 ^ 64) ^ (k - 1) * 2 ^ 64 := by
    rw [← Nat.pow_succ (2 ^ 64), show (k - 1).succ = k by omega]
  rw [List.length_take_of_le (by omega), hpow] at hinv
  have hdist : 10 * (w.toNat + 2 ^ 64 * mpzLimbsVal (List.drop k (List.take len xs))) + r2 =
      (10 * w.toNat + r2) + 2 ^ 64 * (10 * mpzLimbsVal (List.drop k (List.take len xs))) := by omega
  rw [hdist, ← hstep]
  have hm1 : (2 ^ 64) ^ (k - 1) * (remIn * 2 ^ 64 + (xs[k - 1]'(by omega)).toNat +
      2 ^ 64 * (10 * mpzLimbsVal (List.drop k (List.take len xs)))) =
      (2 ^ 64) ^ (k - 1) * (xs[k - 1]'(by omega)).toNat +
        (2 ^ 64) ^ (k - 1) * 2 ^ 64 *
          (10 * mpzLimbsVal (List.drop k (List.take len xs)) + remIn) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add,
      show (2 ^ 64) ^ (k - 1) * (remIn * 2 ^ 64) = (2 ^ 64) ^ (k - 1) * 2 ^ 64 * remIn by
        rw [Nat.mul_comm remIn (2 ^ 64), Nat.mul_assoc],
      ← Nat.mul_assoc ((2 ^ 64) ^ (k - 1)) (2 ^ 64)]
    omega
  rw [hm1]; omega

theorem mpz_div10_exit_eq {q r V : Nat} (hr : r < 10) (h : 10 * q + r = V) :
    r = V % 10 ∧ q = V / 10 := by omega

theorem lcnfHeap_addr_uniq {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    {o1 o2 : LcnfObj} {a : BitVec 64} (hm : (lcnfHeap objs ⋆ R) m)
    (h1 : o1 ∈ objs) (ha1 : o1.addr = a) (h2 : o2 ∈ objs) (ha2 : o2.addr = a) :
    o1 = o2 := by
  obtain ⟨i1, hi1, he1⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨i2, hi2, he2⟩ := List.mem_iff_getElem.mp h2
  by_cases hlt : i1 < i2
  · exact absurd (by rw [he1, he2, ha1, ha2]) (lcnfHeap_addr_ne hlt hi2 hm)
  · by_cases hgt : i2 < i1
    · exact absurd (by rw [he1, he2, ha1, ha2]) (lcnfHeap_addr_ne hgt hi1 hm).symm
    · have hij : i1 = i2 := by omega
      subst hij
      rw [← he1, ← he2]

theorem lcnfObjMem_mpz_meta_shift {o : LcnfObj} (hcanon : MpzCanon o) :
    o.mpzMeta >>> 32 = BitVec.ofNat 64 o.arrSize := by
  unfold LcnfObj.mpzMeta
  have h1 := hcanon.2.2.2.2.2.2.2.1; have h2 := hcanon.2.2.2.2.2.2.2.2
  exact bv64_pack32_high (by rw [bv64_toNat_ofNat_lt4 (by omega)]; omega)
    (by rw [bv64_toNat_ofNat_lt4 (by omega)]; omega)

theorem bytes_set_store8 {a i : BitVec 64} {bs : List UInt8} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (h24 : (bytes (a + 24#64) bs ⋆ R) m) (hi : i.toNat < bs.length) (hle : bs.length ≤ 2 ^ 64) :
    storeOk m i8 (a + 24#64 + i) ∧
      (bytes (a + 24#64) (bs.set i.toNat (UInt8.ofNat (BitVec.truncate 8 v).toNat)) ⋆ R)
        (storeMem m i8 (a + 24#64 + i) (BitVec.truncate 8 v)) :=
  r2_c0_store_bytes_bv (a := a + 24#64) (BitVec.truncate 8 v) h24 hi hle

theorem bytes_set_store8_32 {a i : BitVec 64} {bs : List UInt8} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64}
    (h32 : (bytes (a + 32#64) bs ⋆ R) m) (hi : i.toNat < bs.length) (hle : bs.length ≤ 2 ^ 64) :
    storeOk m i8 (a + 32#64 + i) ∧
      (bytes (a + 32#64) (bs.set i.toNat (UInt8.ofNat v.toNat)) ⋆ R)
        (storeMem m i8 (a + 32#64 + i) v) :=
  r2b_c0_store_bytes_add32 v h32 hi hle

private theorem uint8_ofNat_trunc64_toNat {k : Nat} (hk : k < 256) :
    UInt8.ofNat (BitVec.truncate 8 (BitVec.ofNat 64 k)).toNat = UInt8.ofNat k := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, bv64_toNat_ofNat_lt4 (by omega),
    Nat.mod_eq_of_lt hk]

/-! ## Phase 1: Boxed (`n &&& 1 ≠ 0`) `lcnf_nat_to_str` -/

private theorem natDigitsRev_rev_take_step {val v : Nat} (hv : 0 < v)
    (hrem : (natDigitsRev v).length ≤ (natDigitsRev val).length)
    (htake : (natDigitsRev val).reverse.take (natDigitsRev v).length = (natDigitsRev v).reverse) :
    ((natDigitsRev val).reverse.take (natDigitsRev v).length).length - 1 =
        (natDigitsRev v).length - 1 ∧
      ((natDigitsRev val).reverse.take ((natDigitsRev v).length - 1) =
        (natDigitsRev (v / 10)).reverse) ∧
      (∃ hlt : (natDigitsRev v).length - 1 < (natDigitsRev val).reverse.length,
        (natDigitsRev val).reverse[(natDigitsRev v).length - 1]'hlt =
          UInt8.ofNat (48 + v % 10)) := by
  have hrev := natDigitsRev_ne (by omega : v ≠ 0)
  have hlenv : (natDigitsRev v).length = (natDigitsRev (v / 10)).length + 1 := by
    rw [hrev, List.length_cons]
  have hlt : (natDigitsRev v).length - 1 < (natDigitsRev val).reverse.length := by
    rw [List.length_reverse]; omega
  refine ⟨by rw [List.length_take_of_le (by rw [List.length_reverse]; exact hrem)], ?_, hlt, ?_⟩
  · have htake' : (natDigitsRev val).reverse.take ((natDigitsRev (v / 10)).length + 1) =
        (natDigitsRev (v / 10)).reverse ++ [UInt8.ofNat (48 + v % 10)] := by
      rw [← hlenv, htake, hrev, List.reverse_cons]
    have hpreLen : (natDigitsRev (v / 10)).reverse.length = (natDigitsRev v).length - 1 := by
      rw [List.length_reverse, hlenv]; omega
    have hsub1 : (natDigitsRev v).length - 1 = (natDigitsRev (v / 10)).length := by omega
    rw [hsub1]
    have htakeL : List.take (natDigitsRev (v / 10)).length (natDigitsRev val).reverse =
        List.take (natDigitsRev (v / 10)).length
          (List.take ((natDigitsRev (v / 10)).length + 1) (natDigitsRev val).reverse) := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_succ _)]
    rw [htakeL, htake', ← hsub1, ← hpreLen, List.take_left]
  · have hidx : (natDigitsRev val).reverse[(natDigitsRev v).length - 1]'hlt =
        ((natDigitsRev val).reverse.take (natDigitsRev v).length)[(natDigitsRev v).length - 1]'(by
          rw [List.length_take_of_le (by rw [List.length_reverse]; exact hrem)]; omega) := by
      simp [List.getElem_take]
    have hpreLen : (natDigitsRev (v / 10)).reverse.length = (natDigitsRev v).length - 1 := by
      rw [List.length_reverse, hlenv]; omega
    have hstep1 : ((natDigitsRev val).reverse.take (natDigitsRev v).length)[
          (natDigitsRev v).length - 1]'(by
            rw [List.length_take_of_le (by rw [List.length_reverse]; exact hrem)]; omega) =
        ((natDigitsRev (v / 10)).reverse ++
          [UInt8.ofNat (48 + v % 10)])[(natDigitsRev v).length - 1]'(by simp [hpreLen]) := by
      congr 1; rw [htake, hrev, List.reverse_cons]
    refine Eq.trans hidx (Eq.trans hstep1 ?_)
    rw [List.getElem_append_right (by omega)]; simp [hpreLen]

private theorem nat_to_str_boxed_fill_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {s cntBv valBv : Val i64} {sBs0 : List UInt8} {m : Mem 64}
    (_hpos : 0 < valBv.toNat) (hcnt : cntBv.toNat = (natDigitsRev valBv.toNat).length)
    (hcntLe : cntBv.toNat ≤ 19) (hlen : sBs0.length = cntBv.toNat)
    (hm : (bytes (s + 32#64) sBs0 ⋆ R) m)
    (hk : ∀ m', (bytes (s + 32#64) (natDigitsRev valBv.toNat).reverse ⋆ R) m' →
      Q (s, ()) m') :
    wp rtR2bEnv Q X
      (Expr.group
        (fun Js =>
          Blocks.cons
            (fun (p_9 : Tup Val [i64, i64]) =>
              Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool)
                (Arg.var p_9.snd.fst, Arg.imm 0, ()))
                fun p_10 =>
                Expr.jnz (Arg.var p_10.fst)
                  (Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var p_9.snd.fst, Arg.imm 1, ()))
                    fun p_11 =>
                    Expr.let_ (Op.mk (OpCode.urem 64) (Arg.var p_9.fst, Arg.imm 10, ()))
                      fun p_12 =>
                      Expr.let_ (Op.mk (OpCode.udiv 64) (Arg.var p_9.fst, Arg.imm 10, ()))
                        fun p_13 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var s, Arg.imm 32, ())) fun p =>
                          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.var p_11.fst, ()))
                            fun p =>
                            Expr.let_ (Op.mk (OpCode.add i64) (Arg.imm 48, Arg.var p_12.fst, ()))
                              fun p_14 =>
                              Expr.let_ (Op.mk (OpCode.trunc 64 8) (Arg.var p_14.fst, ()))
                                fun p_15 =>
                                Expr.store (Arg.var p_15.fst) (Arg.var p.fst)
                                  (Expr.jump Js.fst (Arg.var p_13.fst, Arg.var p_11.fst, ())))
                  (Expr.ret (Arg.var s, ())))
            Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.var valBv, Arg.var cntBv, ()))) m := by
  let dec := (natDigitsRev valBv.toNat).reverse
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xs mk =>
    match xs with
    | (v, rem, PUnit.unit) =>
      ∃ sBs : List UInt8,
        meas = rem.toNat ∧
        rem.toNat = (natDigitsRev v.toNat).length ∧
        rem.toNat ≤ dec.length ∧
        sBs.length = cntBv.toNat ∧
        dec.take rem.toNat = (natDigitsRev v.toNat).reverse ∧
        (∀ i (hi1 : i < sBs.length) (hi2 : i < dec.length),
          rem.toNat ≤ i → sBs[i] = dec[i]) ∧
        (bytes (s + 32#64) sBs ⋆ R) mk
  apply wp_loop_group Inv
  · intro J meas xs mk hIH hInv
    rcases xs with ⟨v, rem, ⟨⟩⟩
    rcases hInv with ⟨sBs, hmeas, hremLen, hremLe, hsLen, htake, hget, hmk⟩
    c0_step
    rw [wp_jnz]
    dsimp only [Arg.val_var]
    refine ⟨fun hgt => ?_, fun hle0 => ?_⟩
    · rw [BitVec.ult, decide_eq_true_eq] at hgt
      have hremPos : 0 < rem.toNat := hgt
      have hvPos : 0 < v.toNat := by
        have hvNe : v.toNat ≠ 0 := by
          intro hv0
          rw [hv0, natDigitsRev_zero, List.length_nil] at hremLen
          omega
        omega
      have hrem1 : (rem - 1#64).toNat = rem.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
          (by rw [show (1#64).toNat = 1 from rfl]; omega))]
        rfl
      have hdiv : (v / 10#64).toNat = v.toNat / 10 := by
        rw [BitVec.toNat_udiv, show (10#64).toNat = 10 from rfl]
      have hmod : (v % 10#64).toNat = v.toNat % 10 := by
        rw [BitVec.toNat_umod, show (10#64).toNat = 10 from rfl]
      have hdecLen : dec.length = cntBv.toNat := by
        dsimp [dec]; rw [List.length_reverse, hcnt]
      have hin : (rem - 1#64).toNat < sBs.length := by omega
      have hdecStep := natDigitsRev_rev_take_step (val := valBv.toNat) hvPos
        (by rw [← hremLen, ← hcnt, ← hdecLen]; exact hremLe) (by rwa [← hremLen])
      rcases hdecStep with ⟨_, htakeNext, hltDec, hgetDec⟩
      rw [← hremLen] at htakeNext
      have hgetDec' : dec[rem.toNat - 1]'(by dsimp [dec]; rw [List.length_reverse]; omega) =
          UInt8.ofNat (48 + v.toNat % 10) := by
        dsimp [dec]
        exact Eq.trans (by congr 1; omega) hgetDec
      repeat rw [wp_let]
      dsimp only [Op.wp, vals, Arg.val_var, Arg.val_imm, lift2]
      refine ⟨by decide, by decide, by decide, ?_⟩
      dsimp only [vals, Arg.val_var, Arg.val_imm, lift2]
      rw [show (32 : BitVec 64) = 32#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
        show (48 : BitVec 64) = 48#64 from rfl, show (10 : BitVec 64) = 10#64 from rfl]
      let byteV : BitVec 8 := BitVec.setWidth 8 (48#64 + v % 10#64)
      have hst := bytes_set_store8_32 byteV hmk hin (by omega)
      rw [wp_store]
      simp only [Arg.val_var]
      refine ⟨hst.1, ?_⟩
      c0_step
      have hbyteEq : UInt8.ofNat byteV.toNat = UInt8.ofNat (48 + v.toNat % 10) := by
        have hlt10 : v.toNat % 10 < 10 := Nat.mod_lt _ (by decide)
        have hadd : (48#64 + v % 10#64).toNat = 48 + v.toNat % 10 := by
          rw [BitVec.toNat_add, show (48#64).toNat = 48 from rfl, hmod, Nat.mod_eq_of_lt (by omega)]
        rw [BitVec.toNat_setWidth, hadd, Nat.mod_eq_of_lt (by omega)]
      refine hIH (rem - 1#64).toNat (v / 10#64, rem - 1#64, ()) _ (by omega)
        ⟨sBs.set (rem - 1#64).toNat (UInt8.ofNat byteV.toNat), rfl, ?_, by omega,
          by simp [hsLen], ?_, ?_, hst.2⟩
      · rw [hrem1, hremLen, hdiv]
        have hrev := natDigitsRev_ne (by omega : v.toNat ≠ 0)
        rw [hrev, List.length_cons]
        omega
      · rw [hrem1, hdiv]; exact htakeNext
      · intro i hi1 hi2 hirem
        rw [hrem1] at hirem
        by_cases heqi : i = rem.toNat - 1
        · have hidx : (rem - 1#64).toNat = i := by omega
          have hset : (sBs.set (rem - 1#64).toNat (UInt8.ofNat byteV.toNat))[i]'hi1 =
              UInt8.ofNat byteV.toNat := by
            simp [hidx]
          rw [hset, hbyteEq, ← hgetDec']
          congr 1
          omega
        · rw [List.getElem_set_ne (by omega)]
          exact hget i (by simp [List.length_set] at hi1; exact hi1) hi2 (by omega)
    · rw [BitVec.ult, decide_eq_false_iff_not] at hle0
      have h0eq : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0eq] at hle0
      have hrem0 : rem.toNat = 0 := by omega
      rw [wp_ret]
      apply hk
      have hdecLen : dec.length = cntBv.toNat := by
        dsimp [dec]; rw [List.length_reverse, hcnt]
      have hEq : sBs = dec := by
        apply List.ext_getElem (by omega)
        intro i hi1 hi2
        exact hget i hi1 hi2 (by omega)
      rwa [hEq] at hmk
  · intro J hJ
    c0_step
    apply hJ cntBv.toNat
    have hdecLen : dec.length = cntBv.toNat := by
      dsimp [dec]; rw [List.length_reverse, hcnt]
    exact ⟨sBs0, rfl, hcnt, by omega, hlen,
      by rw [← hdecLen, List.take_length], fun _ _ hi2 hle => by omega, hm⟩

@[expose] def boxedNonzeroExpr (rt valBv : Val i64) : Expr Val Cont [i64] :=
  Expr.group
    (fun Js =>
      Blocks.cons
        (fun (p_6 : Tup Val [i64, i64]) =>
          Expr.let_
            (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var p_6.fst, Arg.imm 0, ()))
            fun p_7 =>
            Expr.jnz (Arg.var p_7.fst)
              (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_6.snd.fst, Arg.imm 1, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.udiv 64) (Arg.var p_6.fst, Arg.imm 10, ())) fun p_8 =>
               Expr.jump Js.fst (Arg.var p_8.fst, Arg.var p.fst, ()))
              (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_6.snd.fst, Arg.imm 1, ())) fun p_8 =>
               Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
                 (Arg.var rt, Arg.var p_8.fst, Arg.var p_6.snd.fst, Arg.var p_6.snd.fst, ())
                 fun (p_s : Tup Val [i64]) =>
               Expr.group
                 (fun Js =>
                   Blocks.cons
                     (fun (p_9 : Tup Val [i64, i64]) =>
                       Expr.let_
                         (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool)
                           (Arg.var p_9.snd.fst, Arg.imm 0, ()))
                         fun p_10 =>
                         Expr.jnz (Arg.var p_10.fst)
                           (Expr.let_
                              (Op.mk (OpCode.sub i64) (Arg.var p_9.snd.fst, Arg.imm 1, ()))
                              fun p_11 =>
                            Expr.let_ (Op.mk (OpCode.urem 64) (Arg.var p_9.fst, Arg.imm 10, ()))
                              fun p_12 =>
                            Expr.let_ (Op.mk (OpCode.udiv 64) (Arg.var p_9.fst, Arg.imm 10, ()))
                              fun p_13 =>
                            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_s.fst, Arg.imm 32, ()))
                              fun p =>
                            Expr.let_
                              (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.var p_11.fst, ()))
                              fun p =>
                            Expr.let_ (Op.mk (OpCode.add i64) (Arg.imm 48, Arg.var p_12.fst, ()))
                              fun p_14 =>
                            Expr.let_ (Op.mk (OpCode.trunc 64 8) (Arg.var p_14.fst, ())) fun p_15 =>
                            Expr.store (Arg.var p_15.fst) (Arg.var p.fst)
                              (Expr.jump Js.fst (Arg.var p_13.fst, Arg.var p_11.fst, ())))
                           (Expr.ret (Arg.var p_s.fst, ())))
                     Blocks.nil)
                 (fun Js => Expr.jump Js.fst (Arg.var valBv, Arg.var p_6.snd.fst, ()))))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.var valBv, Arg.imm 0, ()))

theorem nat_to_str_boxed_nonzero_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt valBv : Val i64} {st : RtC0State} {m : Mem 64}
    (hpos : 0 < valBv.toNat) (hlt : valBv.toNat < 2 ^ 63)
    (hfree : st.hasFree (strAllocBytes ((natDigitsRev valBv.toNat).length + 1)) ∨
      strAllocBytes ((natDigitsRev valBv.toNat).length + 1) ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ R) m)
    (hpost : ∀ (s : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      have dec := (natDigitsRev valBv.toNat).reverse;
      StrCanon (mkStrObj s (1#32) (dec.length + 1) dec dec.length) →
      (rtC0Inv rt st' ⋆ lcnfObjMem (mkStrObj s (1#32) (dec.length + 1) dec dec.length) ⋆ R) m' →
      Q (s, ()) m') :
    wp rtR2bEnv Q X (boxedNonzeroExpr rt valBv) m := by
  unfold boxedNonzeroExpr
  have hlenLe19 : (natDigitsRev valBv.toNat).length ≤ 19 :=
    natDigitsRev_length_le (Nat.lt_trans hlt pow2_63_lt_pow10_19)
  have hlenPos : 1 ≤ (natDigitsRev valBv.toNat).length := natDigitsRev_length_pos hpos
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xs mk =>
    match xs with
    | (v, dlen, PUnit.unit) =>
      mk = m ∧ meas = v.toNat ∧
      dlen.toNat + (natDigitsRev v.toNat).length = (natDigitsRev valBv.toNat).length
  apply wp_loop_group Inv
  · intro J meas xs mk hIH hInv
    rcases xs with ⟨v, dlen, ⟨⟩⟩
    rcases hInv with ⟨rfl, hmeas, hsum⟩
    c0_step
    rw [wp_jnz]
    dsimp only [Arg.val_var]
    refine ⟨fun hgt => ?_, fun hle0 => ?_⟩
    · rw [BitVec.ult, decide_eq_true_eq] at hgt
      have hvPos : 0 < v.toNat := hgt
      have hdiv : (v / 10#64).toNat = v.toNat / 10 := by
        rw [BitVec.toNat_udiv, show (10#64).toNat = 10 from rfl]
      have hadd1 : (dlen + 1#64).toNat = dlen.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      repeat rw [wp_let]
      dsimp only [Op.wp, vals, Arg.val_var, Arg.val_imm, lift2]
      refine ⟨by decide, ?_⟩
      dsimp only [vals, Arg.val_var, Arg.val_imm, lift2]
      rw [wp_jump]
      simp only [vals, Arg.val_var]
      rw [show (1 : BitVec 64) = 1#64 from rfl, show (10 : BitVec 64) = 10#64 from rfl]
      refine hIH (v / 10#64).toNat (v / 10#64, dlen + 1#64, ()) mk
        (by rw [hdiv, hmeas]; exact Nat.div_lt_self hvPos (by decide : 1 < 10)) ⟨rfl, rfl, ?_⟩
      rw [hadd1, hdiv]
      have hrev := natDigitsRev_ne (by omega : v.toNat ≠ 0)
      rw [hrev, List.length_cons] at hsum
      omega
    · rw [BitVec.ult, decide_eq_false_iff_not] at hle0
      have h0eq : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0eq] at hle0
      have hv0 : v.toNat = 0 := by omega
      rw [hv0, natDigitsRev_zero, List.length_nil, Nat.add_zero] at hsum
      c0_let_simp
      apply wp_call_of_spec
      apply rtR2bEnv_r2b_str_alloc_cap
      dsimp only [r2bStrAllocCapSpec, vals, Arg.val_var]
      have hcapVal : (dlen + 1#64).toNat = dlen.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hbounds : dlen.toNat < strMaxCap ∧ dlen.toNat < (dlen + 1#64).toNat ∧
          (dlen + 1#64).toNat ≤ strMaxCap := by
        simp only [strMaxCap]; omega
      have h1eq : (1 : BitVec 64) = 1#64 := rfl
      have hfree' : st.hasFree (strAllocBytes (dlen.toNat + 1)) ∨
          strAllocBytes (dlen.toNat + 1) ≤ st.rem := by
        rwa [hsum]
      rw [h1eq, ite_eq_left hbounds, hcapVal]
      refine ⟨st, R, hfree', hm, fun s st1 m1 hs0 hs8 hpr1 hrem1 _ hm1 => ?_⟩
      have hpop : ∃ sBs0 : List UInt8, sBs0.length = dlen.toNat ∧
          (bytes (s + 32#64) sBs0 ⋆
            (rtC0Inv rt st1 ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (dlen + 1#64) ⋆
              cell64 (s + 16#64) (dlen + 1#64) ⋆ cell64 (s + 24#64) dlen ⋆
              bytes (s + 32#64 + dlen) [0] ⋆
              region (s + 32#64 + dlen + 1#64)
                (strAllocBytes (dlen.toNat + 1) - (32 + dlen.toNat + 1)) ⋆ R)) m1 := by
        have hreg := region_pop_bytes (k := dlen.toNat) (Nat.le_refl _) (by omega)
          (sep_cast hm1 (by ac_rfl) : (region (s + 32#64) dlen.toNat ⋆
            (rtC0Inv rt st1 ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (dlen + 1#64) ⋆
              cell64 (s + 16#64) (dlen + 1#64) ⋆ cell64 (s + 24#64) dlen ⋆
              bytes (s + 32#64 + dlen) [0] ⋆
              region (s + 32#64 + dlen + 1#64)
                (strAllocBytes (dlen.toNat + 1) - (32 + dlen.toNat + 1)) ⋆ R)) m1)
        rcases hreg with ⟨sBs0, hsBs0Len, hsBs0Mem⟩
        rw [Nat.sub_self, region_zero] at hsBs0Mem
        refine ⟨sBs0, hsBs0Len, ?_⟩
        rw [Std.ExtHashMap.sep_emp] at hsBs0Mem
        exact sep_cast hsBs0Mem (by ac_rfl)
      rcases hpop with ⟨sBs0, hsBs0Len, hmPop⟩
      refine nat_to_str_boxed_fill_wp hpos hsum (by omega) hsBs0Len hmPop fun m2 hm2 => ?_
      have hcapBv : BitVec.ofNat 64 (dlen.toNat + 1) = dlen + 1#64 := by
        apply BitVec.eq_of_toNat_eq
        rw [bv64_toNat_ofNat_lt4 (by omega), hcapVal]
      have hdlenBv : BitVec.ofNat 64 dlen.toNat = dlen :=
        BitVec.eq_of_toNat_eq (by rw [bv64_toNat_ofNat_lt4 (by omega)])
      have hdecLen : (natDigitsRev valBv.toNat).reverse.length = dlen.toNat := by
        rw [List.length_reverse, hsum]
      have hmemStr : (rtC0Inv rt st1 ⋆
          lcnfObjMem (mkStrObj s (1#32) ((natDigitsRev valBv.toNat).reverse.length + 1)
            (natDigitsRev valBv.toNat).reverse (natDigitsRev valBv.toNat).reverse.length) ⋆
          R) m2 := by
        have hm2' : (cell64 s strHeaderWord ⋆
            cell64 (s + 8#64) (BitVec.ofNat 64 ((natDigitsRev valBv.toNat).reverse.length + 1)) ⋆
            cell64 (s + 16#64)
              (BitVec.ofNat 64 ((natDigitsRev valBv.toNat).reverse.length + 1)) ⋆
            cell64 (s + 24#64) (BitVec.ofNat 64 (natDigitsRev valBv.toNat).reverse.length) ⋆
            bytes (s + 32#64) (natDigitsRev valBv.toNat).reverse ⋆
            bytes (s + 32#64 + BitVec.ofNat 64 (natDigitsRev valBv.toNat).reverse.length) [0] ⋆
            region
              (s + 32#64 + BitVec.ofNat 64 (natDigitsRev valBv.toNat).reverse.length + 1#64)
              (strAllocBytes ((natDigitsRev valBv.toNat).reverse.length + 1) -
                (32 + (natDigitsRev valBv.toNat).reverse.length + 1)) ⋆
            (rtC0Inv rt st1 ⋆ R)) m2 := by
          rw [hdecLen, hcapBv, hdlenBv]
          exact sep_cast hm2 (by ac_rfl)
        exact sep_cast (mkStrObj_mem_of_parts (by simp only [strMaxCap]; omega)
          (Nat.le_refl _) hm2') (by ac_rfl)
      have hcanon : StrCanon (mkStrObj s (1#32) ((natDigitsRev valBv.toNat).reverse.length + 1)
          (natDigitsRev valBv.toNat).reverse (natDigitsRev valBv.toNat).reverse.length) :=
        mkStrObj_canon hs0 hs8 (by decide) (Nat.le_refl _) (by simp only [strMaxCap]; omega)
          (by omega)
      exact hpost s st1 m2 hs0 hs8 hpr1 hrem1 hcanon hmemStr
  · intro J hJ
    c0_step
    exact hJ valBv.toNat (valBv, 0#64, ()) m ⟨rfl, rfl, by simp⟩

/-! ## Phase 2: Shared `trimZeroLimbs` and MPZ limb copy loop -/

theorem nat_to_str_trim_limbs_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {addr sz : Val i64} {xs : List (BitVec 64)} {m : Mem 64}
    {k : Val i64 → Expr Val Cont [i64]}
    (hsz : sz.toNat ≤ xs.length) (_hxsLen : xs.length < 2 ^ 64)
    (hm : (array64 (addr + 16#64) xs ⋆ R) m)
    (hk : ∀ cnBv : Val i64,
      cnBv.toNat = trimZeroLimbsLen xs sz.toNat → cnBv.toNat ≤ sz.toNat →
      wp rtR2bEnv Q X (k cnBv) m) :
    wp rtR2bEnv Q X
      (Expr.group
        (fun Js =>
          Blocks.cons
            (fun (p_6 : Tup Val [i64, i64]) =>
              Expr.let_
                (Op.mk (OpCode.cmp CmpOp.ne i64 Ty.bool) (Arg.var p_6.snd.fst, Arg.imm 0, ()))
                fun p_7 =>
                Expr.jnz (Arg.var p_7.fst)
                  (Expr.group
                    (fun _Js_1 =>
                      Blocks.cons
                        (fun (p : Tup Val [i64, i64]) =>
                          Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ()))
                        Blocks.nil)
                    fun Js =>
                    Expr.let_
                      (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var p_6.fst, Arg.imm 0, ()))
                      fun p_8 =>
                      Expr.jnz (Arg.var p_8.fst)
                        (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var addr, Arg.imm 16, ())) fun p =>
                          Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var p_6.fst, Arg.imm 1, ()))
                            fun p_9 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 8, Arg.var p_9.fst, ()))
                              fun p_10 =>
                              Expr.let_
                                (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.var p_10.fst, ()))
                                fun p =>
                                Expr.load i64 (Arg.var p.fst) fun ld =>
                                  Expr.group
                                    (fun _Js_1 =>
                                      Blocks.cons
                                        (fun (p : Tup Val [i64, i64]) =>
                                          Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ()))
                                        Blocks.nil)
                                    fun Js =>
                                    Expr.let_
                                      (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool)
                                        (Arg.var ld, Arg.imm 0, ()))
                                      fun p =>
                                      Expr.jnz (Arg.var p.fst)
                                        (Expr.let_
                                          (Op.mk (OpCode.sub i64) (Arg.var p_6.fst, Arg.imm 1, ()))
                                          fun p =>
                                          Expr.jump Js.fst
                                            (Arg.var p.fst, Arg.var p_6.snd.fst, ()))
                                        (Expr.jump Js.fst (Arg.var p_6.fst, Arg.imm 0, ())))
                        (Expr.jump Js.fst (Arg.var p_6.fst, Arg.imm 0, ())))
                  (k p_6.fst))
            Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.var sz, Arg.imm 1, ()))) m := by
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xsP mk =>
    match xsP with
    | (curLen, cont, PUnit.unit) =>
      mk = m ∧ curLen.toNat ≤ sz.toNat ∧
      (cont = 0#64 → curLen.toNat = trimZeroLimbsLen xs sz.toNat ∧ meas = 0) ∧
      (cont ≠ 0#64 →
        trimZeroLimbsLen xs curLen.toNat = trimZeroLimbsLen xs sz.toNat ∧
        meas = curLen.toNat + 1)
  apply wp_loop_group Inv
  · intro J meas xsP mk hIH hInv
    rcases xsP with ⟨curLen, cont, ⟨⟩⟩
    rcases hInv with ⟨rfl, hcurLe, h0, hnz⟩
    c0_step
    rw [wp_jnz]
    dsimp only [Arg.val_var]
    refine ⟨fun hcontNe => ?_, fun hcontEq0 => ?_⟩
    · have hcNe : cont ≠ 0#64 := by simpa [bne_iff_ne] using hcontNe
      obtain ⟨htrim, hmeas⟩ := hnz hcNe
      refine LeanQbe.T.wp_unroll_group fun Jc hJc => ?_
      c0_step
      rw [wp_jnz]
      dsimp only [Arg.val_var]
      refine ⟨fun hgt => ?_, fun hle0 => ?_⟩
      · rw [BitVec.ult, decide_eq_true_eq] at hgt
        have h0eq : (0 : BitVec 64).toNat = 0 := rfl
        rw [h0eq] at hgt
        have hcurPos : 0 < curLen.toNat := hgt
        have hsub1 : (curLen - 1#64).toNat = curLen.toNat - 1 := by
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
            (by rw [show (1#64).toNat = 1 from rfl]; omega))]
          rfl
        have hlt : (curLen - 1#64).toNat < xs.length := by omega
        c0_let_simp
        have hld := r2b_c0_load_array64_add16_mul8 (i := curLen - 1#64) hm hlt
        rw [show (16 : BitVec 64) = 16#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
          show (8 : BitVec 64) = 8#64 from rfl]
        apply wp_load_of (v := xs[(curLen - 1#64).toNat])
          (by simpa [Arg.val_var] using hld)
        refine LeanQbe.T.wp_unroll_group fun Jc2 hJc2 => ?_
        c0_step
        rw [wp_jnz]
        dsimp only [Arg.val_var]
        have hstepEq : trimZeroLimbsLen xs curLen.toNat =
            if xs.getD (curLen.toNat - 1) 0#64 = 0#64
            then trimZeroLimbsLen xs (curLen.toNat - 1) else curLen.toNat := by
          conv => lhs; rw [show curLen.toNat = (curLen.toNat - 1) + 1 from by omega,
            trimZeroLimbsLen.eq_2]
          simp [Nat.sub_add_cancel hcurPos]
        have hgetD : xs.getD (curLen.toNat - 1) 0#64 = xs[(curLen - 1#64).toNat] := by
          simp only [List.getD,
            List.getElem?_eq_getElem (by omega : curLen.toNat - 1 < xs.length),
            Option.getD_some]
          congr 1
          exact hsub1.symm
        refine ⟨fun heq0 => ?_, fun hne0 => ?_⟩
        · have hx0 : xs[(curLen - 1#64).toNat] = 0#64 := by simpa using heq0
          rw [hgetD, hx0, ite_eq_left rfl] at hstepEq
          rw [wp_let]
          dsimp only [Op.wp, vals, Arg.val_var, Arg.val_imm, lift2]
          apply hJc2
          c0_let_simp
          apply hJc
          c0_let_simp
          exact hIH (curLen.toNat - 1 + 1) (curLen - 1#64, cont, ()) mk (by omega)
            ⟨rfl, by omega, fun hbad => absurd hbad hcNe, fun _ =>
              ⟨by rw [hsub1, ← hstepEq, htrim], by rw [hsub1]⟩⟩
        · have hxNe : xs[(curLen - 1#64).toNat] ≠ 0#64 := by simpa using hne0
          rw [hgetD, ite_eq_right hxNe] at hstepEq
          apply hJc2
          c0_let_simp
          apply hJc
          c0_let_simp
          exact hIH 0 (curLen, 0#64, ()) mk (by omega)
            ⟨rfl, hcurLe, fun _ => ⟨by rw [← hstepEq, htrim], rfl⟩, fun hbad => absurd rfl hbad⟩
      · rw [BitVec.ult, decide_eq_false_iff_not] at hle0
        have h0eq : (0 : BitVec 64).toNat = 0 := rfl
        rw [h0eq] at hle0
        have hcur0 : curLen.toNat = 0 := by omega
        have htrim0 : trimZeroLimbsLen xs sz.toNat = 0 := by
          rw [← htrim, hcur0, trimZeroLimbsLen.eq_1]
        apply hJc
        c0_let_simp
        exact hIH 0 (curLen, 0#64, ()) mk (by omega)
          ⟨rfl, hcurLe, fun _ => ⟨by rw [hcur0, htrim0], rfl⟩, fun hbad => absurd rfl hbad⟩
    · have hc0 : cont = 0#64 := by simpa [bne_iff_ne] using hcontEq0
      exact hk curLen (h0 hc0).1 hcurLe
  · intro J hJ
    c0_step
    exact hJ (sz.toNat + 1) (sz, 1#64, ()) m
      ⟨rfl, Nat.le_refl _, fun h => by simp at h, fun _ => ⟨rfl, rfl⟩⟩

theorem nat_to_str_copy_loop_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {tmp n cnBv : Val i64} {nXs tmpXs0 : List (BitVec 64)} {m : Mem 64}
    {k : Expr Val Cont [i64]}
    (hcnLe : cnBv.toNat ≤ nXs.length) (htmpLen : tmpXs0.length = cnBv.toNat)
    (_hcnLt : cnBv.toNat < 2 ^ 64)
    (hm : (array64 (tmp + 16#64) tmpXs0 ⋆ array64 (n + 16#64) nXs ⋆ R) m)
    (hk : ∀ tmpXs m', tmpXs.length = cnBv.toNat → tmpXs = List.take cnBv.toNat nXs →
      (array64 (tmp + 16#64) tmpXs ⋆ array64 (n + 16#64) nXs ⋆ R) m' → wp rtR2bEnv Q X k m') :
    wp rtR2bEnv Q X
      (Expr.group
        (fun Js =>
          Blocks.cons
            (fun (p_11 : Tup Val [i64]) =>
              Expr.let_
                (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var p_11.fst, Arg.var cnBv, ()))
                fun p_12 =>
                Expr.jnz (Arg.var p_12.fst)
                  (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmp, Arg.imm 16, ())) fun p_13 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 8, Arg.var p_11.fst, ())) fun p_14 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_13.fst, Arg.var p_14.fst, ()))
                        fun p_15 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var n, Arg.imm 16, ())) fun p =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 8, Arg.var p_11.fst, ()))
                            fun p_16 =>
                            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.var p_16.fst, ()))
                              fun p =>
                              Expr.load i64 (Arg.var p.fst) fun ld =>
                                Expr.store (Arg.var ld) (Arg.var p_15.fst)
                                  (Expr.let_
                                    (Op.mk (OpCode.add i64) (Arg.var p_11.fst, Arg.imm 1, ()))
                                    fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
                  k)
            Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m := by
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xsP mk =>
    match xsP with
    | (i, PUnit.unit) =>
      ∃ tmpXs : List (BitVec 64),
        meas = cnBv.toNat - i.toNat ∧
        i.toNat ≤ cnBv.toNat ∧
        tmpXs.length = cnBv.toNat ∧
        List.take i.toNat tmpXs = List.take i.toNat nXs ∧
        (array64 (tmp + 16#64) tmpXs ⋆ array64 (n + 16#64) nXs ⋆ R) mk
  apply wp_loop_group Inv
  · intro J meas xsP mk hIH hInv
    rcases xsP with ⟨i, ⟨⟩⟩
    rcases hInv with ⟨tmpXs, hmeas, hiLe, hlen, htake, hmk⟩
    c0_step
    rw [wp_jnz]
    dsimp only [Arg.val_var]
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hiLt : i.toNat < cnBv.toNat := by simpa [BitVec.ult] using hlt
      c0_let_simp
      have hmkN : (array64 (n + 16#64) nXs ⋆ (array64 (tmp + 16#64) tmpXs ⋆ R)) mk :=
        sep_cast hmk (by ac_rfl)
      have hld := r2b_c0_load_array64_add16_mul8 (i := i) hmkN (by omega)
      rw [show (16 : BitVec 64) = 16#64 from rfl, show (8 : BitVec 64) = 8#64 from rfl]
      apply wp_load_of (v := nXs[i.toNat]) (by simpa [Arg.val_var] using hld)
      have hmkTmp : (array64 (tmp + 16#64) tmpXs ⋆ (array64 (n + 16#64) nXs ⋆ R)) mk :=
        sep_cast hmk (by ac_rfl)
      have hst := r2b_c0_store_array64_add16_mul8 (i := i) nXs[i.toNat] hmkTmp (by omega)
      rw [wp_store]
      simp only [Arg.val_var]
      refine ⟨hst.1, ?_⟩
      c0_step
      have hadd1 : (i + 1#64).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hst2 : (array64 (tmp + 16#64) (tmpXs.set i.toNat nXs[i.toNat]) ⋆
          array64 (n + 16#64) nXs ⋆ R)
          (storeMem mk i64 (tmp + 16#64 + 8#64 * i) nXs[i.toNat]) :=
        sep_cast hst.2 (by ac_rfl)
      refine hIH (cnBv.toNat - (i.toNat + 1)) (i + 1#64, ()) _ (by omega)
        ⟨tmpXs.set i.toNat nXs[i.toNat], by rw [hadd1], by rw [hadd1]; omega, by simp [hlen],
          ?_, hst2⟩
      rw [hadd1,
        list_take_succ_append4 (tmpXs.set i.toNat nXs[i.toNat]) (by omega)
          (by simp only [List.length_set, hlen]; omega),
        list_take_succ_append4 nXs (by omega) (by omega), list_take_set_of_le4 tmpXs _ (by omega)]
      have hsetSelf : (tmpXs.set i.toNat nXs[i.toNat])[i.toNat]'(by simp [hlen]; omega) =
          nXs[i.toNat] :=
        List.getElem_set_self (by rw [List.length_set]; omega)
      simp only [Nat.add_sub_cancel, htake, hsetSelf]
    · have hiEq : i.toNat = cnBv.toNat := by
        have hnot : ¬ (i.toNat < cnBv.toNat) := by simpa [BitVec.ult] using hge
        omega
      rw [hiEq, List.take_of_length_le (Nat.le_of_eq hlen)] at htake
      exact hk tmpXs mk hlen htake hmk
  · intro J hJ
    c0_step
    exact hJ cnBv.toNat (0#64, ()) m ⟨tmpXs0, rfl, Nat.zero_le _, htmpLen, rfl, hm⟩

/-! ## Sub-expression Factoring for Phases 3–5 (`≤ 100` chars, Zero AST Duplication) -/

@[expose] def trimLimbsExpr (addr sz : Val i64)
    (k : Val i64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun Js =>
      Blocks.cons
        (fun (p_6 : Tup Val [i64, i64]) =>
          Expr.let_
            (Op.mk (OpCode.cmp CmpOp.ne i64 Ty.bool) (Arg.var p_6.snd.fst, Arg.imm 0, ()))
            fun p_7 =>
            Expr.jnz (Arg.var p_7.fst)
              (Expr.group
                (fun _Js_1 =>
                  Blocks.cons
                    (fun (p : Tup Val [i64, i64]) =>
                      Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ()))
                    Blocks.nil)
                fun Js =>
                Expr.let_
                  (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var p_6.fst, Arg.imm 0, ()))
                  fun p_8 =>
                  Expr.jnz (Arg.var p_8.fst)
                    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var addr, Arg.imm 16, ())) fun p =>
                      Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var p_6.fst, Arg.imm 1, ()))
                        fun p_9 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 8, Arg.var p_9.fst, ()))
                          fun p_10 =>
                          Expr.let_
                            (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.var p_10.fst, ()))
                            fun p =>
                            Expr.load i64 (Arg.var p.fst) fun ld =>
                              Expr.group
                                (fun _Js_1 =>
                                  Blocks.cons
                                    (fun (p : Tup Val [i64, i64]) =>
                                      Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ()))
                                    Blocks.nil)
                                fun Js =>
                                Expr.let_
                                  (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool)
                                    (Arg.var ld, Arg.imm 0, ()))
                                  fun p =>
                                  Expr.jnz (Arg.var p.fst)
                                    (Expr.let_
                                      (Op.mk (OpCode.sub i64) (Arg.var p_6.fst, Arg.imm 1, ()))
                                      fun p =>
                                      Expr.jump Js.fst (Arg.var p.fst, Arg.var p_6.snd.fst, ()))
                                    (Expr.jump Js.fst (Arg.var p_6.fst, Arg.imm 0, ())))
                    (Expr.jump Js.fst (Arg.var p_6.fst, Arg.imm 0, ())))
              (k p_6.fst))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.var sz, Arg.imm 1, ()))

@[expose] def copyLoopExpr (tmp n cnBv : Val i64)
    (k : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun Js =>
      Blocks.cons
        (fun (p_11 : Tup Val [i64]) =>
          Expr.let_
            (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var p_11.fst, Arg.var cnBv, ()))
            fun p_12 =>
            Expr.jnz (Arg.var p_12.fst)
              (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmp, Arg.imm 16, ())) fun p_13 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 8, Arg.var p_11.fst, ())) fun p_14 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_13.fst, Arg.var p_14.fst, ()))
                    fun p_15 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var n, Arg.imm 16, ())) fun p =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 8, Arg.var p_11.fst, ()))
                        fun p_16 =>
                        Expr.let_
                          (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.var p_16.fst, ()))
                          fun p =>
                          Expr.load i64 (Arg.var p.fst) fun ld =>
                            Expr.store (Arg.var ld) (Arg.var p_15.fst)
                              (Expr.let_
                                (Op.mk (OpCode.add i64) (Arg.var p_11.fst, Arg.imm 1, ()))
                                fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
              k)
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))

@[expose] def innerDiv10Expr (tmp curLenBv : Val i64)
    (k : Val i64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun Js_1 =>
      Blocks.cons
        (fun (p : Tup Val [i64, i64]) =>
          Expr.let_
            (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var p.snd.fst, Arg.imm 0, ()))
            fun p_18 =>
            Expr.jnz (Arg.var p_18.fst)
              (Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p_19 =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmp, Arg.imm 16, ())) fun p_20 =>
               Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 8, Arg.var p_19.fst, ())) fun p_21 =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_20.fst, Arg.var p_21.fst, ()))
                 fun p_22 =>
               Expr.load i64 (Arg.var p_22.fst) fun ld =>
               Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm (t := i32) 32, ())) fun p_23 =>
               Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var p.fst, Arg.var p_23.fst, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm (t := i32) 32, ())) fun p_24 =>
               Expr.let_ (Op.mk (OpCode.lshr i64) (Arg.var ld, Arg.var p_24.fst, ())) fun p_25 =>
               Expr.let_ (Op.mk (OpCode.or i64) (Arg.var p.fst, Arg.var p_25.fst, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.udiv 64) (Arg.var p.fst, Arg.imm 10, ())) fun p_26 =>
               Expr.let_ (Op.mk (OpCode.urem 64) (Arg.var p.fst, Arg.imm 10, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm (t := i32) 32, ())) fun p_27 =>
               Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var p.fst, Arg.var p_27.fst, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.and i64) (Arg.var ld, Arg.imm 4294967295, ())) fun p_28 =>
               Expr.let_ (Op.mk (OpCode.or i64) (Arg.var p.fst, Arg.var p_28.fst, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.udiv 64) (Arg.var p.fst, Arg.imm 10, ())) fun p_29 =>
               Expr.let_ (Op.mk (OpCode.urem 64) (Arg.var p.fst, Arg.imm 10, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmp, Arg.imm 16, ())) fun p_30 =>
               Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 8, Arg.var p_19.fst, ())) fun p_31 =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_30.fst, Arg.var p_31.fst, ()))
                 fun p_32 =>
               Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm (t := i32) 32, ())) fun p_33 =>
               Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var p_26.fst, Arg.var p_33.fst, ()))
                 fun p_34 =>
               Expr.let_ (Op.mk (OpCode.or i64) (Arg.var p_34.fst, Arg.var p_29.fst, ()))
                 fun p_35 =>
               Expr.store (Arg.var p_35.fst) (Arg.var p_32.fst)
                 (Expr.jump Js_1.fst (Arg.var p.fst, Arg.var p_19.fst, ())))
              (k p.fst))
        Blocks.nil)
    (fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, Arg.var curLenBv, ()))

@[expose] def outerDivExpr (tmp buf cnBv maxDig : Val i64)
    (k : Val i64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun Js =>
      Blocks.cons
        (fun (p_16 : Tup Val [i64, i64]) =>
          Expr.let_
            (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var p_16.snd.fst, Arg.imm 0, ()))
            fun p_17 =>
            Expr.jnz (Arg.var p_17.fst)
              (innerDiv10Expr tmp p_16.snd.fst fun remBv =>
                Expr.group
                  (fun _Js_2 =>
                    Blocks.cons
                      (fun (p : Tup Val [i64, i64]) =>
                        trimLimbsExpr tmp p.snd.fst
                          (fun cnNext => Expr.jump Js.fst (Arg.var p.fst, Arg.var cnNext, ())))
                      Blocks.nil)
                  fun Js =>
                  Expr.let_
                    (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool)
                      (Arg.var p_16.fst, Arg.var maxDig, ()))
                    fun p_19 =>
                    Expr.jnz (Arg.var p_19.fst)
                      (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var buf, Arg.imm 24, ())) fun p_20 =>
                       Expr.let_
                         (Op.mk (OpCode.add i64) (Arg.var p_20.fst, Arg.var p_16.fst, ()))
                         fun p_21 =>
                       Expr.let_ (Op.mk (OpCode.add i64) (Arg.imm 48, Arg.var remBv, ())) fun p =>
                       Expr.let_ (Op.mk (OpCode.trunc 64 8) (Arg.var p.fst, ())) fun p =>
                       Expr.store (Arg.var p.fst) (Arg.var p_21.fst)
                         (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_16.fst, Arg.imm 1, ()))
                            fun p =>
                          Expr.jump Js.fst (Arg.var p.fst, Arg.var p_16.snd.fst, ())))
                      (Expr.jump Js.fst (Arg.var p_16.fst, Arg.imm 0, ())))
              (k p_16.fst))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.var cnBv, ()))

@[expose] def revLoopExpr (buf s dlenBv : Val i64)
    (k : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun Js =>
      Blocks.cons
        (fun (p_21 : Tup Val [i64]) =>
          Expr.let_
            (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool) (Arg.var p_21.fst, Arg.var dlenBv, ()))
            fun p_22 =>
            Expr.jnz (Arg.var p_22.fst)
              (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var buf, Arg.imm 24, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var dlenBv, Arg.imm 1, ())) fun p_23 =>
               Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var p_23.fst, Arg.var p_21.fst, ()))
                 fun p_24 =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.var p_24.fst, ())) fun p =>
               Expr.load i8 (Arg.var p.fst) fun ld =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var s, Arg.imm 32, ())) fun p =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.var p_21.fst, ())) fun p =>
               Expr.store (Arg.var ld) (Arg.var p.fst)
                 (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_21.fst, Arg.imm 1, ())) fun p =>
                  Expr.jump Js.fst (Arg.var p.fst, ())))
              k)
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))

@[expose] def boxedExpr (rt n : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm (t := i32) 1, ())) fun p_3 =>
  Expr.let_ (Op.mk (OpCode.lshr i64) (Arg.var n, Arg.var p_3.fst, ())) fun p_4 =>
  Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var p_4.fst, Arg.imm 0, ())) fun p_5 =>
  Expr.jnz (Arg.var p_5.fst)
    (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
       (Arg.var rt, Arg.imm 2, Arg.imm 1, Arg.imm 1, ()) fun (p : Tup Val [i64]) =>
     Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.imm 32, ())) fun p_6 =>
     Expr.let_ (Op.mk (OpCode.trunc 64 8) (Arg.imm (t := i64) 48, ())) fun p_7 =>
     Expr.store (Arg.var p_7.fst) (Arg.var p_6.fst) (Expr.ret (Arg.var p.fst, ())))
    (boxedNonzeroExpr rt p_4.fst)

@[expose] def mpzFreeExpr (rt tmp buf s : Val i64) : Expr Val Cont [i64] :=
  Expr.call (as := [i64, i64]) (bs := []) "lcnf_free_obj"
    (Arg.var rt, Arg.var buf, ()) fun _p_23 =>
  Expr.call (as := [i64, i64]) (bs := []) "lcnf_free_obj"
    (Arg.var rt, Arg.var tmp, ()) fun _p =>
  Expr.ret (Arg.var s, ())

@[expose] def revFreeExpr (rt tmp buf s dlen : Val i64) : Expr Val Cont [i64] :=
  revLoopExpr buf s dlen (mpzFreeExpr rt tmp buf s)

@[expose] def afterDecExpr (rt tmp cnBv : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.imm 20, Arg.var cnBv, ())) fun p_14 =>
  Expr.call (as := [i64, i64]) (bs := [i64]) "r2b_alloc_sarray"
    (Arg.var rt, Arg.var p_14.fst, ()) fun p_15 =>
  outerDivExpr tmp p_15.fst cnBv p_14.fst fun dlen =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_15.fst, Arg.imm 8, ())) fun p_18 =>
  Expr.store (Arg.var dlen) (Arg.var p_18.fst)
    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var dlen, Arg.imm 1, ())) fun p_19 =>
     Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
       (Arg.var rt, Arg.var p_19.fst, Arg.var dlen, Arg.var dlen, ()) fun p_20 =>
     revFreeExpr rt tmp p_15.fst p_20.fst dlen)

@[expose] def afterTrimExpr (rt n cnBv : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool) (Arg.var cnBv, Arg.imm 0, ())) fun p_8 =>
  Expr.jnz (Arg.var p_8.fst)
    (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
       (Arg.var rt, Arg.imm 2, Arg.imm 1, Arg.imm 1, ()) fun (p : Tup Val [i64]) =>
     Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.imm 32, ())) fun p_10 =>
     Expr.let_ (Op.mk (OpCode.trunc 64 8) (Arg.imm (t := i64) 48, ())) fun p_11 =>
     Expr.store (Arg.var p_11.fst) (Arg.var p_10.fst)
       (Expr.call (as := [i64, i64]) (bs := []) "r2b_dec_obj" (Arg.var rt, Arg.var n, ())
         fun _p_9 => Expr.ret (Arg.var p.fst, ())))
    (Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool) (Arg.var cnBv, Arg.imm 13421770, ()))
       fun p_9 =>
     Expr.jnz (Arg.var p_9.fst)
       (Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt, Arg.imm 2, ()))
       (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "r2b_alloc_mpz"
          (Arg.var rt, Arg.var cnBv, Arg.var cnBv, ()) fun p_10 =>
        copyLoopExpr p_10.fst n cnBv
          (Expr.call (as := [i64, i64]) (bs := []) "r2b_dec_obj" (Arg.var rt, Arg.var n, ())
             fun _p_13 => afterDecExpr rt p_10.fst cnBv)))

end

end LeanQbe.T.LeanLCNF
