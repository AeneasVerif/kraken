module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofEls

/-!
# Kissat `D-Full` M6 — ELS Union-Find Fold & Top-Level Pass (`31..32/39`)

Parametric `(Γ : Env)` `Func.wp` proofs for `2/39` owned functions (`32/39` cumulative):
- `31/39`: `full_m6_els_fold_wp` (`m6ElsFoldSpec`)
- `32/39`: `full_m6_dense_els_wp` (`m6DenseElsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullArenaTactics M6ElsBv
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Union-Find & Flatness Helpers -/

private theorem m6_nat_xor1_cases (x : Nat) : x ^^^ 1 = if x % 2 = 0 then x + 1 else x - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp only [Nat.testBit_zero, show (1 : Nat) % 2 = 1 from rfl, decide_true, Bool.xor_true]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega
  · simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit,
      Bool.xor_false]
    split <;> rename_i h
    · rw [show (x + 1) / 2 = x / 2 by omega]
    · rw [show (x - 1) / 2 = x / 2 by omega]

private theorem m6_nat_xor1_even (k : Nat) : (2 * k) ^^^ 1 = 2 * k + 1 := by
  rw [m6_nat_xor1_cases, Nat.mul_mod_right]; rfl

private theorem m6_nat_xor1_odd (k : Nat) : (2 * k + 1) ^^^ 1 = 2 * k := by
  rw [m6_nat_xor1_cases]; split <;> omega

private theorem m6_nat_xor1_lt {x N : Nat} (hx : x < 2 * N) : x ^^^ 1 < 2 * N := by
  rw [m6_nat_xor1_cases]; split <;> omega

private theorem m6_xor1_div2 (x : Nat) : (x ^^^ 1) / 2 = x / 2 := litVar_litNeg x

private theorem m6_xor1_xor1 (x : Nat) : (x ^^^ 1) ^^^ 1 = x := litNeg_litNeg x

private theorem m6_xor1_ne_of_div2_ne {x y : Nat} (h : x / 2 ≠ y / 2) :
    x ≠ y ^^^ 1 ∧ x ≠ y := by
  rw [m6_nat_xor1_cases]; split <;> omega

private theorem m6_list_set2_eq {α : Type _} (xs : List α) {i1 j1 i2 j2 : Nat}
    {v1 v2 w1 w2 : α} (hi : i1 = j1) (hj : i2 = j2) (hv1 : v1 = w1) (hv2 : v2 = w2) :
    (xs.set i1 v1).set i2 v2 = (xs.set j1 w1).set j2 w2 := by
  subst hi hj hv1 hv2; rfl

private theorem m6_bv8_sext32_eq0_iff (v : BitVec 8) : v.signExtend 32 = 0#32 ↔ v = 0#8 := by
  have h := m6_els_bv8_eq0 v
  constructor <;> intro hv
  · have hb : (v.signExtend 32 == 0#32) = true := beq_iff_eq.mpr hv
    rw [h] at hb; exact beq_iff_eq.mp hb
  · have hb : (v == 0#8) = true := beq_iff_eq.mpr hv
    rw [← h] at hb; exact beq_iff_eq.mp hb

private def M6FoldWf (F_cur : List (List Nat)) (cv : Nat) (repr : List (BitVec 32)) : Prop :=
  2 * cv ≤ repr.length ∧
  (∀ v < cv, let r := (repr[2 * v]?.getD 0#32).toNat
    r < 2 * cv ∧ (r = 2 * v ∨ r / 2 < v)) ∧
  (∀ v < cv, repr[2 * v + 1]?.getD 0#32 = repr[2 * v]?.getD 0#32 ^^^ 1#32) ∧
  (∀ l < 2 * cv, LitEquiv (cnfOfClauses F_cur) l (repr[l]?.getD 0#32).toNat)

private theorem m6_foldWf_lit_prop {F_cur : List (List Nat)} {cv : Nat}
    {repr : List (BitVec 32)} (h : M6FoldWf F_cur cv repr) {l : Nat} (hl : l < 2 * cv) :
    let r := (repr[l]?.getD 0#32).toNat
    r < 2 * cv ∧ (r = l ∨ r / 2 < l / 2) := by
  by_cases he : l % 2 = 0
  · have hl2 : l = 2 * (l / 2) := by omega
    have hv : l / 2 < cv := by omega
    have h0 := h.2.1 (l / 2) hv
    rw [← hl2] at h0; exact h0
  · have hl2 : l = 2 * (l / 2) + 1 := by omega
    have hv : l / 2 < cv := by omega
    have h0 := h.2.1 (l / 2) hv
    have hp := h.2.2.1 (l / 2) hv
    dsimp only
    rw [hl2, hp, BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
    have hlt : (repr[2 * (l / 2)]?.getD 0#32).toNat < 2 * cv := h0.1
    refine ⟨m6_nat_xor1_lt hlt, ?_⟩
    rcases h0.2 with heq | hlt2
    · left; rw [heq, m6_nat_xor1_even]
    · right; rw [m6_xor1_div2, show (2 * (l / 2) + 1) / 2 = l / 2 by omega]; exact hlt2

private theorem m6_foldWf_of_id {F_cur : List (List Nat)} {cv : Nat}
    {repr : List (BitVec 32)} (hlen : 2 * cv ≤ repr.length) (hcv : 2 * cv < 2 ^ 32)
    (hid : ∀ i < 2 * cv, repr[i]?.getD 0#32 = BitVec.ofNat 32 i) :
    M6FoldWf F_cur cv repr := by
  refine ⟨hlen, fun v hv => ?_, fun v hv => ?_, fun l hl => ?_⟩
  · have h2 := hid (2 * v) (by omega)
    dsimp only; rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, Or.inl rfl⟩
  · have h2 := hid (2 * v) (by omega); have h21 := hid (2 * v + 1) (by omega)
    rw [h2, h21]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), m6_nat_xor1_even]
  · rw [hid l hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

private theorem m6_foldWf_merge {F_cur : List (List Nat)} {cv : Nat}
    {repr : List (BitVec 32)} (hwf : M6FoldWf F_cur cv repr) {ra rb : BitVec 32}
    (hralt : ra.toNat < 2 * cv) (hrblt : rb.toNat < 2 * cv)
    (heqv : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat)
    (hvar_lt : ra.toNat / 2 < rb.toNat / 2) :
    let repr' := (repr.set rb.toNat ra).set (rb ^^^ 1#32).toNat (ra ^^^ 1#32)
    M6FoldWf F_cur cv repr' := by
  intro repr'
  have hrb_xor : (rb ^^^ 1#32).toNat = rb.toNat ^^^ 1 := by simp
  have hra_xor : (ra ^^^ 1#32).toNat = ra.toNat ^^^ 1 := by simp
  have hrb1_lt : rb.toNat ^^^ 1 < 2 * cv := m6_nat_xor1_lt hrblt
  have hra1_lt : ra.toNat ^^^ 1 < 2 * cv := m6_nat_xor1_lt hralt
  have hlen : 2 * cv ≤ repr'.length := by simp [repr', List.length_set, hwf.1]
  have hget : ∀ i < 2 * cv,
      repr'[i]?.getD 0#32 =
        if i = rb.toNat ^^^ 1 then ra ^^^ 1#32
        else if i = rb.toNat then ra else repr[i]?.getD 0#32 := by
    intro i _
    by_cases h1 : i = rb.toNat ^^^ 1
    · subst h1; dsimp only [repr']; rw [← hrb_xor]
      rw [List.getElem?_set_self (by simp [List.length_set]; have := hwf.1; omega),
        Option.getD_some]
      simp [hrb_xor]
    · simp only [h1, ↓reduceIte]; dsimp only [repr']
      rw [List.getElem?_set_ne (by rw [hrb_xor]; exact Ne.symm h1)]
      by_cases h2 : i = rb.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by have := hwf.1; omega), Option.getD_some]
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  refine ⟨hlen, fun v hv => ?_, fun v hv => ?_, fun l hl => ?_⟩
  · dsimp only; rw [hget (2 * v) (by omega)]
    by_cases hv0 : 2 * v = rb.toNat ^^^ 1
    · simp only [hv0, ↓reduceIte, hra_xor]
      exact ⟨hra1_lt, Or.inr (by
        have h1 := congrArg (· / 2) hv0
        rw [m6_xor1_div2, Nat.mul_div_right _ (by omega)] at h1
        rw [m6_xor1_div2, h1]; exact hvar_lt)⟩
    · simp only [hv0, ↓reduceIte]
      by_cases hv1 : 2 * v = rb.toNat
      · simp only [hv1, ↓reduceIte]; exact ⟨hralt, Or.inr (by omega)⟩
      · simp only [hv1, ↓reduceIte]; exact hwf.2.1 v hv
  · rw [hget (2 * v + 1) (by omega), hget (2 * v) (by omega)]
    by_cases hv0 : v = rb.toNat / 2
    · subst hv0
      by_cases hpar : rb.toNat % 2 = 0
      · have he2 : 2 * (rb.toNat / 2) = rb.toNat := by omega
        have he1 : 2 * (rb.toNat / 2) + 1 = rb.toNat ^^^ 1 := by
          conv => rhs; rw [← he2]
          rw [m6_nat_xor1_even]
        have hne_rb : 2 * (rb.toNat / 2) ≠ rb.toNat ^^^ 1 := by rw [← he1]; omega
        rw [ite_eq_left he1, ite_eq_right hne_rb, ite_eq_left he2]
      · have he1 : 2 * (rb.toNat / 2) + 1 = rb.toNat := by omega
        have he2 : 2 * (rb.toNat / 2) = rb.toNat ^^^ 1 := by
          conv => rhs; rw [← he1]
          rw [m6_nat_xor1_odd]
        have hne_rb : 2 * (rb.toNat / 2) + 1 ≠ rb.toNat ^^^ 1 := by rw [← he2]; omega
        rw [ite_eq_right hne_rb, ite_eq_left he1, ite_eq_left he2]
        simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · have ha1 := m6_xor1_ne_of_div2_ne (x := 2 * v + 1) (y := rb.toNat) (by omega)
      have ha0 := m6_xor1_ne_of_div2_ne (x := 2 * v) (y := rb.toNat) (by omega)
      rw [ite_eq_right ha1.1, ite_eq_right ha1.2, ite_eq_right ha0.1, ite_eq_right ha0.2]
      exact hwf.2.2.1 v hv
  · rw [hget l hl]
    by_cases hl1 : l = rb.toNat ^^^ 1
    · rw [ite_eq_left hl1, hra_xor, hl1]; exact m6_litEquiv_neg heqv.symm
    · rw [ite_eq_right hl1]
      by_cases hl0 : l = rb.toNat
      · rw [ite_eq_left hl0, hl0]; exact heqv.symm
      · rw [ite_eq_right hl0]; exact hwf.2.2.2 l hl

private theorem m6_foldWf_flatten_step {F_cur : List (List Nat)} {cv : Nat}
    {repr : List (BitVec 32)} (hwf : M6FoldWf F_cur cv repr) {v : Nat} (hv : v < cv)
    (hcv32 : 2 * cv < 2 ^ 32)
    (hflat : ∀ w < v, repr[(repr[2 * w]?.getD 0#32).toNat]? = repr[2 * w]? ∧
      repr[(repr[2 * w + 1]?.getD 0#32).toNat]? = repr[2 * w + 1]?) :
    let pl := BitVec.ofNat 32 (2 * v)
    let r := repr[2 * v]?.getD 0#32
    let r' := if r ≠ pl then repr[r.toNat]?.getD 0#32 else r
    let repr' := if r ≠ pl then (repr.set (2 * v) r').set (2 * v + 1) (r' ^^^ 1#32) else repr
    M6FoldWf F_cur cv repr' ∧
    (∀ w < v + 1, repr'[(repr'[2 * w]?.getD 0#32).toNat]? = repr'[2 * w]? ∧
      repr'[(repr'[2 * w + 1]?.getD 0#32).toNat]? = repr'[2 * w + 1]?) := by
  intro pl r r' repr'
  have hwf_v := hwf.2.1 v hv
  have hlt_r : r.toNat < 2 * cv := hwf_v.1
  by_cases hne : r = pl
  · dsimp only [repr']; rw [ite_eq_right (fun h => h hne)]
    refine ⟨hwf, fun w hw => ?_⟩
    by_cases hwe : w = v
    · subst hwe
      have hrl : r.toNat = 2 * w := by
        rw [hne]; unfold pl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hneg := hwf.2.2.1 w hv
      have hrl1 : (repr[2 * w + 1]?.getD 0#32).toNat = 2 * w + 1 := by
        rw [hneg, BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hrl, m6_nat_xor1_even]
      exact ⟨by change repr[r.toNat]? = repr[2 * w]?; rw [hrl], by rw [hrl1]⟩
    · exact hflat w (by omega)
  · dsimp only [repr']; rw [ite_eq_left hne]
    have hr_lt_v : r.toNat / 2 < v := by
      rcases hwf_v.2 with heq | hlt
      · exfalso; apply hne; apply BitVec.eq_of_toNat_eq
        rw [heq]; unfold pl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · exact hlt
    have hr_prop := m6_foldWf_lit_prop hwf hlt_r
    dsimp only at hr_prop
    have hr'_eq : r' = repr[r.toNat]?.getD 0#32 := by simp [r', hne]
    have hr'_root : repr[r'.toNat]? = some r' := by
      have hfl := hflat (r.toNat / 2) hr_lt_v
      by_cases hpar : r.toNat % 2 = 0
      · have hr2 : 2 * (r.toNat / 2) = r.toNat := by omega
        have h1 := hfl.1; rw [hr2] at h1; rw [hr'_eq, h1]
        rw [List.getElem?_eq_getElem (by have := hwf.1; omega), Option.getD_some]
      · have hr2 : 2 * (r.toNat / 2) + 1 = r.toNat := by omega
        have h1 := hfl.2; rw [hr2] at h1; rw [hr'_eq, h1]
        rw [List.getElem?_eq_getElem (by have := hwf.1; omega), Option.getD_some]
    have hr'_lt : r'.toNat < 2 * cv := by rw [hr'_eq]; exact hr_prop.1
    have hr'_var : r'.toNat / 2 ≤ r.toNat / 2 := by
      rw [hr'_eq]; rcases hr_prop.2 with heq | hlt
      · rw [heq]; exact Nat.le_refl _
      · exact Nat.le_of_lt hlt
    have hr'_lt_v : r'.toNat / 2 < v := Nat.lt_of_le_of_lt hr'_var hr_lt_v
    have hr'_xor : (r' ^^^ 1#32).toNat = r'.toNat ^^^ 1 := by simp
    have hr'1_lt : (r' ^^^ 1#32).toNat < 2 * cv := by rw [hr'_xor]; exact m6_nat_xor1_lt hr'_lt
    have hr'_neg_root : repr[(r' ^^^ 1#32).toNat]? = some (r' ^^^ 1#32) := by
      have hvr : r'.toNat / 2 < cv := by omega
      have hpol := hwf.2.2.1 (r'.toNat / 2) hvr
      have hpar : (r'.toNat % 2 = 0) ∨ (r'.toNat % 2 = 1) := by omega
      have hr'_get : repr[r'.toNat]?.getD 0#32 = r' := by rw [hr'_root]; rfl
      rcases hpar with hp0 | hp1
      · have h0 : 2 * (r'.toNat / 2) = r'.toNat := by omega
        have h1 : 2 * (r'.toNat / 2) + 1 = (r' ^^^ 1#32).toNat := by
          rw [hr'_xor, m6_nat_xor1_cases]; split <;> omega
        rw [← h1]
        have hsome : repr[2 * (r'.toNat / 2) + 1]? =
            some (repr[2 * (r'.toNat / 2) + 1]?.getD 0#32) := by
          rw [List.getElem?_eq_getElem (by have := hwf.1; omega), Option.getD_some]
        rw [hsome, hpol, h0, hr'_get]
      · have h0 : 2 * (r'.toNat / 2) + 1 = r'.toNat := by omega
        have h1 : 2 * (r'.toNat / 2) = (r' ^^^ 1#32).toNat := by
          rw [hr'_xor, m6_nat_xor1_cases]; split <;> omega
        rw [← h1]
        have hsome : repr[2 * (r'.toNat / 2)]? =
            some (repr[2 * (r'.toNat / 2)]?.getD 0#32) := by
          rw [List.getElem?_eq_getElem (by have := hwf.1; omega), Option.getD_some]
        rw [hsome]; congr 1
        rw [h0, hr'_get] at hpol
        have hxx := congrArg (· ^^^ 1#32) hpol
        simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at hxx
        exact hxx.symm
    have hget_new : ∀ i,
        ((repr.set (2 * v) r').set (2 * v + 1) (r' ^^^ 1#32))[i]? =
          if i = 2 * v + 1 then some (r' ^^^ 1#32)
          else if i = 2 * v then some r' else repr[i]? := by
      intro i
      by_cases h1 : i = 2 * v + 1
      · subst h1
        rw [ite_eq_left rfl,
          List.getElem?_set_self (by simp [List.length_set]; have := hwf.1; omega)]
      · rw [ite_eq_right h1, List.getElem?_set_ne (Ne.symm h1)]
        by_cases h0 : i = 2 * v
        · subst h0; rw [ite_eq_left rfl, List.getElem?_set_self (by have := hwf.1; omega)]
        · rw [ite_eq_right h0, List.getElem?_set_ne (Ne.symm h0)]
    refine ⟨⟨by simp [List.length_set, hwf.1], fun w hw => ?_, fun w hw => ?_, fun l hl => ?_⟩,
        fun w hw => ?_⟩
    · dsimp only; rw [hget_new (2 * w)]
      by_cases hwe : w = v
      · subst hwe; rw [ite_eq_right (by omega), ite_eq_left rfl, Option.getD_some]
        exact ⟨hr'_lt, Or.inr hr'_lt_v⟩
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact hwf.2.1 w hw
    · rw [hget_new (2 * w + 1), hget_new (2 * w)]
      by_cases hwe : w = v
      · subst hwe; rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left rfl]; rfl
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        exact hwf.2.2.1 w hw
    · rw [hget_new l]
      by_cases h1 : l = 2 * v + 1
      · subst h1; rw [ite_eq_left rfl, Option.getD_some]
        have he_r : LitEquiv (cnfOfClauses F_cur) r.toNat r'.toNat := by
          rw [hr'_eq]; exact hwf.2.2.2 r.toNat hlt_r
        have he1 := (hwf.2.2.2 (2 * v) (by omega)).trans he_r
        have he2 := m6_litEquiv_neg he1
        simpa only [m6_nat_xor1_even, ← hr'_xor] using he2
      · rw [ite_eq_right h1]
        by_cases h0 : l = 2 * v
        · subst h0; rw [ite_eq_left rfl, Option.getD_some]
          have he_r : LitEquiv (cnfOfClauses F_cur) r.toNat r'.toNat := by
            rw [hr'_eq]; exact hwf.2.2.2 r.toNat hlt_r
          exact (hwf.2.2.2 (2 * v) (by omega)).trans he_r
        · rw [ite_eq_right h0]; exact hwf.2.2.2 l hl
    · by_cases hwe : w = v
      · subst hwe
        rw [hget_new (2 * w), ite_eq_right (by omega), ite_eq_left rfl, Option.getD_some]
        rw [hget_new (2 * w + 1), ite_eq_left rfl, Option.getD_some]
        have hdiv_r' : r'.toNat / 2 ≠ w := by omega
        have hne_r' : r'.toNat ≠ 2 * w + 1 ∧ r'.toNat ≠ 2 * w := by omega
        have hr'x_ne0 : r'.toNat ^^^ 1 ≠ 2 * w := by
          intro he; have := congrArg (· / 2) he; rw [m6_xor1_div2] at this; omega
        have hr'x_ne1 : r'.toNat ^^^ 1 ≠ 2 * w + 1 := by
          intro he; have := congrArg (· / 2) he; rw [m6_xor1_div2] at this; omega
        refine ⟨?_, ?_⟩
        · rw [hget_new r'.toNat, ite_eq_right hne_r'.1, ite_eq_right hne_r'.2, hr'_root]
        · rw [hget_new (r' ^^^ 1#32).toNat, ite_eq_right (by rw [hr'_xor]; exact hr'x_ne1),
            ite_eq_right (by rw [hr'_xor]; exact hr'x_ne0), hr'_neg_root]
      · have hfl := hflat w (by omega)
        have hw0 : (repr[2 * w]?.getD 0#32).toNat / 2 ≤ w := by
          rcases (hwf.2.1 w (by omega)).2 with heq | hlt
          · rw [heq]; omega
          · exact Nat.le_of_lt hlt
        have hw1 : (repr[2 * w + 1]?.getD 0#32).toNat / 2 ≤ w := by
          have hneg := hwf.2.2.1 w (by omega)
          rw [hneg, BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, m6_xor1_div2]; exact hw0
        have hn0 : 2 * w ≠ 2 * v + 1 ∧ 2 * w ≠ 2 * v := by omega
        have hn1 : 2 * w + 1 ≠ 2 * v + 1 ∧ 2 * w + 1 ≠ 2 * v := by omega
        rw [hget_new (2 * w), ite_eq_right hn0.1, ite_eq_right hn0.2]
        rw [hget_new (2 * w + 1), ite_eq_right hn1.1, ite_eq_right hn1.2]
        rw [hget_new (repr[2 * w]?.getD 0#32).toNat,
          ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [hget_new (repr[2 * w + 1]?.getD 0#32).toNat,
          ite_eq_right (by omega), ite_eq_right (by omega)]
        exact hfl

private theorem m6_foldWf_to_flat {F_cur : List (List Nat)} {cv : Nat}
    {repr : List (BitVec 32)} (hwf : M6FoldWf F_cur cv repr)
    (hflat : ∀ w < cv, repr[(repr[2 * w]?.getD 0#32).toNat]? = repr[2 * w]? ∧
      repr[(repr[2 * w + 1]?.getD 0#32).toNat]? = repr[2 * w + 1]?) :
    M6ReprFlatInv F_cur (2 * cv) repr := by
  refine ⟨⟨⟨hwf.1, fun l hl => ?_⟩, hwf.2.2.2⟩, ?_, ?_⟩
  · have hlp := m6_foldWf_lit_prop hwf hl
    rcases hlp.2 with heq | hlt <;> omega
  · intro l hl
    by_cases hpar : l % 2 = 0
    · have hl2 : 2 * (l / 2) = l := by omega
      have h1 := (hflat (l / 2) (by omega)).1; rwa [hl2] at h1
    · have hl2 : 2 * (l / 2) + 1 = l := by omega
      have h1 := (hflat (l / 2) (by omega)).2; rwa [hl2] at h1
  · intro l hl
    by_cases hpar : l % 2 = 0
    · have h2 : l = 2 * (l / 2) := by omega
      have h1 : l ^^^ 1 = 2 * (l / 2) + 1 := by conv => lhs; rw [h2, m6_nat_xor1_even]
      rw [h1]; conv => rhs; rw [h2]
      rw [hwf.2.2.1 (l / 2) (by omega)]; simp [BitVec.toNat_xor]
    · have h2 : l = 2 * (l / 2) + 1 := by omega
      have h1 : l ^^^ 1 = 2 * (l / 2) := by conv => lhs; rw [h2, m6_nat_xor1_odd]
      rw [h1]; conv => rhs; rw [h2]
      rw [hwf.2.2.1 (l / 2) (by omega)]
      simp [BitVec.toNat_xor, show ∀ n, (n ^^^ 1) ^^^ 1 = n from litNeg_litNeg]

private theorem m6_reprFlat_set_id {F_cur : List (List Nat)} {cv v : Nat}
    {repr : List (BitVec 32)} (hflat : M6ReprFlatInv F_cur (2 * cv) repr) (hv : v < cv)
    (hcv32 : 2 * cv < 2 ^ 32) (hne : repr[2 * v]?.getD 0#32 ≠ BitVec.ofNat 32 (2 * v)) :
    let l32 := BitVec.ofNat 32 (2 * v)
    let repr' := (repr.set (2 * v) l32).set (2 * v + 1) (l32 ^^^ 1#32)
    M6ReprFlatInv F_cur (2 * cv) repr' := by
  intro l32 repr'
  have hl_to : l32.toNat = 2 * v := by
    unfold l32; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hl1_to : (l32 ^^^ 1#32).toNat = 2 * v + 1 := by
    rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hl_to, m6_nat_xor1_even]
  have hlen : 2 * cv ≤ repr'.length := by simp [repr', List.length_set, hflat.1.1.1]
  have hget : ∀ i, repr'[i]? =
      if i = 2 * v + 1 then some (l32 ^^^ 1#32)
      else if i = 2 * v then some l32 else repr[i]? := by
    intro i
    by_cases h1 : i = 2 * v + 1
    · subst h1; rw [ite_eq_left rfl]
      exact List.getElem?_set_self (by simp [List.length_set]; have := hflat.1.1.1; omega)
    · rw [ite_eq_right h1]; dsimp only [repr']; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h0 : i = 2 * v
      · subst h0; rw [ite_eq_left rfl]; exact List.getElem?_set_self (by have := hflat.1.1.1; omega)
      · rw [ite_eq_right h0, List.getElem?_set_ne (Ne.symm h0)]
  have hno_hit0 : ∀ w < 2 * cv, w ≠ 2 * v → (repr[w]?.getD 0#32).toNat ≠ 2 * v := by
    intro w hw _ heq
    apply hne
    have hidem := m6_reprFlat_idem hflat hw
    rw [heq] at hidem
    have hs2 : repr[2 * v]?.getD 0#32 = repr[w]?.getD 0#32 := by rw [← hidem]
    apply BitVec.eq_of_toNat_eq; rw [hs2, heq, hl_to]
  have hno_hit1 : ∀ w < 2 * cv, w ≠ 2 * v + 1 → (repr[w]?.getD 0#32).toNat ≠ 2 * v + 1 := by
    intro w hw hne1 heq
    have hwx_lt : w ^^^ 1 < 2 * cv := m6_nat_xor1_lt hw
    have hneg := m6_reprFlat_neg hflat (l := w ^^^ 1) hwx_lt
    rw [show (w ^^^ 1) ^^^ 1 = w from litNeg_litNeg w, heq] at hneg
    have hneg2 : (repr[w ^^^ 1]?.getD 0#32).toNat = 2 * v := by
      have h1 := congrArg (· ^^^ 1) hneg
      rw [m6_nat_xor1_odd, m6_xor1_xor1] at h1; exact h1.symm
    have hwx_ne : w ^^^ 1 ≠ 2 * v := by
      intro heq'; have h1 := congrArg (· ^^^ 1) heq'
      rw [m6_xor1_xor1, m6_nat_xor1_even] at h1; exact hne1 h1
    exact hno_hit0 (w ^^^ 1) hwx_lt hwx_ne hneg2
  refine ⟨⟨⟨hlen, fun l hl => ?_⟩, fun l hl => ?_⟩, fun l hl => ?_, fun l hl => ?_⟩
  · rw [hget l]
    by_cases h1 : l = 2 * v + 1
    · rw [ite_eq_left h1, Option.getD_some, hl1_to]; omega
    · rw [ite_eq_right h1]
      by_cases h0 : l = 2 * v
      · rw [ite_eq_left h0, Option.getD_some, hl_to]; omega
      · rw [ite_eq_right h0]; exact hflat.1.1.2 l hl
  · rw [hget l]
    by_cases h1 : l = 2 * v + 1
    · subst h1; rw [ite_eq_left rfl, Option.getD_some, hl1_to]; exact LitEquiv.refl _ _
    · rw [ite_eq_right h1]
      by_cases h0 : l = 2 * v
      · subst h0; rw [ite_eq_left rfl, Option.getD_some, hl_to]; exact LitEquiv.refl _ _
      · rw [ite_eq_right h0]; exact hflat.1.2 l hl
  · rw [hget l]
    by_cases h1 : l = 2 * v + 1
    · rw [ite_eq_left h1, Option.getD_some, hl1_to, hget (2 * v + 1), ite_eq_left rfl]
    · rw [ite_eq_right h1]
      by_cases h0 : l = 2 * v
      · rw [ite_eq_left h0, Option.getD_some, hl_to, hget (2 * v),
          ite_eq_right (by omega), ite_eq_left rfl]
      · rw [ite_eq_right h0]
        have hnh0 := hno_hit0 l hl h0
        have hnh1 := hno_hit1 l hl h1
        rw [hget (repr[l]?.getD 0#32).toNat, ite_eq_right hnh1, ite_eq_right hnh0]
        exact m6_reprFlat_idem hflat hl
  · have hlx := m6_nat_xor1_cases l
    rw [hget (l ^^^ 1), hget l]
    by_cases h1 : l = 2 * v + 1
    · have h2 : l ^^^ 1 = 2 * v := by rw [h1, m6_nat_xor1_odd]
      rw [ite_eq_right (by omega), ite_eq_left h2, ite_eq_left h1,
        Option.getD_some, Option.getD_some, hl_to, hl1_to, m6_nat_xor1_odd v]
    · rw [ite_eq_right h1]
      by_cases h0 : l = 2 * v
      · have h2 : l ^^^ 1 = 2 * v + 1 := by rw [h0, m6_nat_xor1_even]
        rw [ite_eq_left h2, ite_eq_left h0, Option.getD_some, Option.getD_some,
          hl_to, hl1_to, m6_nat_xor1_even v]
      · have h20 : l ^^^ 1 ≠ 2 * v := by
          intro h; have h' := congrArg (· ^^^ 1) h
          rw [m6_xor1_xor1, m6_nat_xor1_even] at h'; omega
        have h21 : l ^^^ 1 ≠ 2 * v + 1 := by
          intro h; have h' := congrArg (· ^^^ 1) h
          rw [m6_xor1_xor1, m6_nat_xor1_odd] at h'; omega
        rw [ite_eq_right h21, ite_eq_right h20, ite_eq_right h0]; exact m6_reprFlat_neg hflat hl

/-! ## 2. `full_m6_els_fold_wp` (`31/39`) -/

private def M6ElsFoldFrame (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) : Prop :=
  FullDenseInvW c F0 F_cur sL ∧
  sL.core.cur_vars = s.core.cur_vars ∧ sL.core.fuel = s.core.fuel ∧
  sL.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  sL.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
  sL.scratch.scratch_buf = s.scratch.scratch_buf ∧
  sL.scratch.work_stk1 = s.scratch.work_stk1

private theorem m6_els_fold_fail_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {m' : Mem 64} {R : Mem 64 → Prop} {Q : Post [.bool]}
    (hfr : M6ElsFoldFrame c F0 F_cur s s') (huns : (cnfOfClauses F_cur).Unsat)
    (hm' : (FullMem c { s' with core := { s'.core with inconsistent := 1#64 } } ⋆ R) m')
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      (ok = true → M6ReprFlatInv F_cur (2 * s'.core.cur_vars) s'.core.repr) →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (false, ()) m' :=
  hQ false { s' with core := { s'.core with inconsistent := 1#64 } } m'
    (m6_denseInvW_set_inconsistent hfr.1 huns) hfr.2.1 hfr.2.2.1 hfr.2.2.2.1 hfr.2.2.2.2.1
    hfr.2.2.2.2.2.1 hfr.2.2.2.2.2.2 (fun h => Bool.noConfusion h)
    (fun _ => ⟨hfr.1.2.1.ext_sound.2 huns, by simp⟩) hm'

/-- `31/39`: Parametric `Func.wp` proof for `full_m6_els_fold`. -/
theorem full_m6_els_fold_wp (Γ : Env)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hExtPush2 : M6EnvSpec Γ "full_extend_push2" m6ExtendPush2Spec)
    (hSetInact : M6EnvSpec Γ "full_set_inactive" Full.fullSetInactiveSpec) :
    ∀ args m Q X, m6ElsFoldSpec args m Q X →
      Func.wp Γ full_m6_els_fold_body args m Q X := by
  rintro ⟨h, neq, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, heqb, hm, hQ⟩
  have hcl := hinv.1.core_ok; have hsl := hinv.1.scratch_ok
  have hmx := c.hmaxv; have hex := c.hext; unfold dimacsBound at hmx hex
  have hcv_le := hcl.cur_vars_le; have hcv32 : 2 * s.core.cur_vars < 2 ^ 32 := by omega
  have hrp_len := hcl.repr_len; have hws2_len := hsl.work_stk2_len
  -- Loop 1 (`i = 0 ..< 2 * cv: repr[i] = i`):
  c0_hsteps_nogrp
  refine wp_while_state (ts := [i64]) (proj := fun i : BitVec 64 => (i, ()))
    (μ := fun i => 2 * s.core.cur_vars - i.toNat)
    (Inv := fun i ml => i.toNat ≤ 2 * s.core.cur_vars ∧ ∃ rp1 : List (BitVec 32),
      rp1.length = 2 * c.max_vars ∧
      (∀ k < i.toNat, rp1[k]?.getD 0#32 = BitVec.ofNat 32 k) ∧
      (FullMem c { s with core := { s.core with repr := rp1 } } ⋆ R) ml) ?_ ?_
  · intro J1 hJ1; c0_hsteps!
    exact hJ1 0#64 m ⟨Nat.zero_le _, s.core.repr, hrp_len, (fun _ hk => by cases hk), hm⟩
  · rintro J1 i1 ml1 ⟨hi1_le, rp1, hrp1, hid1, hml1⟩ ih1
    clear hm
    c0_hsplit
    · have hi_lt : i1.toNat < 2 * s.core.cur_vars := by bv_omega
      have hi_bd : i1.toNat < rp1.length := by rw [hrp1]; omega
      have hi1 : (i1 + 1#64).toNat = i1.toNat + 1 := by bv_omega
      c0_hsteps_nogrp
      refine ih1 (i1 + 1#64) _ (by rw [hi1]; omega) ⟨by omega,
        rp1.set i1.toNat (BitVec.setWidth 32 i1), by simp [hrp1], fun k hk => ?_, by assumption⟩
      by_cases hki : k = i1.toNat
      · subst hki; rw [List.getElem?_set_self hi_bd, Option.getD_some]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : i1.toNat < 2 ^ 32)]
      · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hid1 k (by omega)
    · -- Exit Loop 1 -> `M6FoldWf`! Then Loop 2 (`ei = 0 ..< neq`)!
      have hi_eq : i1.toNat = 2 * s.core.cur_vars := by bv_omega
      have hwf1 : M6FoldWf F_cur s.core.cur_vars rp1 :=
        m6_foldWf_of_id (by rw [hrp1]; omega) hcv32 (fun k hk => hid1 k (hi_eq ▸ hk))
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i64]) (proj := fun ei : BitVec 64 => (ei, ()))
        (μ := fun ei => neq.toNat - ei.toNat)
        (Inv := fun ei ml => ei.toNat ≤ neq.toNat ∧ ∃ rp2 : List (BitVec 32),
          rp2.length = 2 * c.max_vars ∧ M6FoldWf F_cur s.core.cur_vars rp2 ∧
          (FullMem c { s with core := { s.core with repr := rp2 } } ⋆ R) ml) ?_ ?_
      · intro J2 hJ2; c0_hsteps!
        exact hJ2 0#64 ml1 ⟨Nat.zero_le _, rp1, hrp1, hwf1, hml1⟩
      · rintro J2 ei2 ml ⟨hei_le, rp2, hrp2, hwf2, hml⟩ ih2
        clear ml1 hml1
        c0_hsplit
        · -- `ei < neq`: walk `a -> ra` and `b -> rb`, check contra or merge!
          have hei_lt : ei2.toNat < neq.toNat := by bv_omega
          have hei1 : (ei2 + 1#64).toNat = ei2.toNat + 1 := by bv_omega
          have heq_i := heqb.2 ei2.toNat hei_lt
          have h2e0_c0 : (ei2 <<< 1#64).toNat = 2 * ei2.toNat := by
            rw [m6_els_bv64_shl1_bv, Nat.mod_eq_of_lt (by have := heqb.1; omega)]
          have h2e1_c0 : (ei2 <<< 1#64 + 1#64).toNat = 2 * ei2.toNat + 1 := by
            rw [BitVec.toNat_add, h2e0_c0, show (1#64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by have := heqb.1; omega)]
          have h2e0_lt : 2 * ei2.toNat < s.scratch.work_stk2.length := by
            rw [hws2_len]; have := heqb.1; omega
          have h2e1_lt : 2 * ei2.toNat + 1 < s.scratch.work_stk2.length := by
            rw [hws2_len]; have := heqb.1; omega
          have _h2e0_bd : (ei2 <<< 1#64).toNat < s.scratch.work_stk2.length := by
            rw [h2e0_c0]; exact h2e0_lt
          have _h2e1_bd : (ei2 <<< 1#64 + 1#64).toNat < s.scratch.work_stk2.length := by
            rw [h2e1_c0]; exact h2e1_lt
          have _h2e0_bd' : (ei2 <<< (1 : BitVec 64)).toNat < s.scratch.work_stk2.length := _h2e0_bd
          have _h2e1_bd' : (ei2 <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat <
              s.scratch.work_stk2.length := _h2e1_bd
          let a := s.scratch.work_stk2[2 * ei2.toNat]'h2e0_lt
          let b := s.scratch.work_stk2[2 * ei2.toNat + 1]'h2e1_lt
          let a_c0 := s.scratch.work_stk2[(ei2 <<< (1 : BitVec 64)).toNat]'_h2e0_bd'
          let b_c0 :=
            s.scratch.work_stk2[(ei2 <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat]'_h2e1_bd'
          have ha_eq : a_c0 = a := m6_getElem_congr h2e0_c0 _ h2e0_lt
          have hb_eq : b_c0 = b := m6_getElem_congr h2e1_c0 _ h2e1_lt
          have ha_lt : a.toNat < 2 * s.core.cur_vars := by
            have := heq_i.1; rwa [List.getElem?_eq_getElem h2e0_lt, Option.getD_some] at this
          have hb_lt : b.toNat < 2 * s.core.cur_vars := by
            have := heq_i.2.1; rwa [List.getElem?_eq_getElem h2e1_lt, Option.getD_some] at this
          have hab_eq : LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat := by
            have := heq_i.2.2
            rwa [List.getElem?_eq_getElem h2e0_lt, List.getElem?_eq_getElem h2e1_lt,
              Option.getD_some, Option.getD_some] at this
          c0_hsteps_nogrp
          -- Inner walk A (`ra, ga`): zero `∨` in invariant because `v = 0` is always a root!
          refine wp_while_state (ts := [i32, i64])
            (proj := fun p : BitVec 32 × BitVec 64 => (p.1, p.2, ()))
            (μ := fun p => p.2.toNat)
            (Inv := fun p mA => p.1.toNat < 2 * s.core.cur_vars ∧
              p.1.toNat / 2 < p.2.toNat ∧ p.2.toNat ≤ s.core.cur_vars ∧
              LitEquiv (cnfOfClauses F_cur) a.toNat p.1.toNat ∧ mA = ml) ?_ ?_
          · intro JA hJA; c0_hsteps!
            exact hJA (a_c0, BitVec.ofNat 64 s.core.cur_vars) ml (by
              dsimp only
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ha_eq]
              exact ⟨ha_lt, by omega, by omega, LitEquiv.refl _ _, rfl⟩)
          · rintro JA ⟨ra, ga⟩ mA ⟨hra_lt, hra_ga, hga_le, heq_a, hmA⟩ ihA
            dsimp only at hra_lt hra_ga hga_le heq_a
            subst mA
            have hga_pos : 0 < ga.toNat := by omega
            have hra_bd : ra.toNat < rp2.length := by rw [hrp2]; omega
            have _hra_c0 : (BitVec.setWidth 64 ra).toNat < rp2.length := by
              rw [bv_c0_zext32_64]; exact hra_bd
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun () mEx =>
                rp2[ra.toNat]'hra_bd = ra ∧ mEx = ml) ?_ ?_
            · -- Exit Walk A: `rp2[ra] = ra`! Now Walk B (`rb, gb`)!
              rintro _ ⟨⟩ mEx ⟨hra_root, hmEx⟩
              subst mEx
              c0_hsteps_nogrp
              refine wp_while_state (ts := [i32, i64])
                (proj := fun p : BitVec 32 × BitVec 64 => (p.1, p.2, ()))
                (μ := fun p => p.2.toNat)
                (Inv := fun p mB => p.1.toNat < 2 * s.core.cur_vars ∧
                  p.1.toNat / 2 < p.2.toNat ∧ p.2.toNat ≤ s.core.cur_vars ∧
                  LitEquiv (cnfOfClauses F_cur) b.toNat p.1.toNat ∧ mB = ml) ?_ ?_
              · intro JB hJB; c0_hsteps!; dsimp only
                exact hJB (b_c0, BitVec.ofNat 64 s.core.cur_vars) ml (by
                  dsimp only
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hb_eq]
                  exact ⟨hb_lt, by omega, by omega, LitEquiv.refl _ _, rfl⟩)
              · rintro JB ⟨rb, gb⟩ mB ⟨hrb_lt, hrb_gb, hgb_le, heq_b, hmB⟩ ihB
                dsimp only at hrb_lt hrb_gb hgb_le heq_b
                subst mB
                have hgb_pos : 0 < gb.toNat := by omega
                have hrb_bd : rb.toNat < rp2.length := by rw [hrp2]; omega
                have _hrb_c0 : (BitVec.setWidth 64 rb).toNat < rp2.length := by
                  rw [bv_c0_zext32_64]; exact hrb_bd
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun () mExB =>
                    rp2[rb.toNat]'hrb_bd = rb ∧ mExB = ml) ?_ ?_
                · rintro _ ⟨⟩ mExB ⟨hrb_root, hmExB⟩
                  subst mExB
                  -- Exit Walk B: `ra, rb` roots, `LitEquiv F_cur ra rb`!
                  have heqv_ab : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat :=
                    (heq_a.symm.trans hab_eq).trans heq_b
                  c0_hsplit
                  · -- `ra == rb ^ 1`: UNSAT! `h->inconsistent = 1; return false;`
                    have hcon : ra = rb ^^^ 1#32 := by assumption
                    have huns : (cnfOfClauses F_cur).Unsat := by
                      rw [CNF.unsat_iff_not_sat]; intro β hβ
                      have h1 := litEquiv_eval hβ heqv_ab
                      rw [hcon, m6_els_bv32_xor1_toNat, show rb.toNat ^^^ 1 = litNeg rb.toNat
                        from rfl, evalLitVal_litNeg] at h1
                      cases h : evalLitVal β rb.toNat <;> rw [h] at h1 <;> cases h1
                    c0_hsteps!
                    have hfr : M6ElsFoldFrame c F0 F_cur s
                        { s with core := { s.core with repr := rp2 } } :=
                      ⟨m6_denseInvW_set_repr hinv hrp2, rfl, rfl, rfl, rfl, rfl, rfl⟩
                    exact m6_els_fold_fail_unsat hfr huns (by assumption) hQ
                  · have hne_opp : ra ≠ rb ^^^ 1#32 := by assumption
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i32, i32]) (fun (_ra_d, _rb_d, ()) mNxt =>
                        ∃ rp2' : List (BitVec 32), rp2'.length = 2 * c.max_vars ∧
                          M6FoldWf F_cur s.core.cur_vars rp2' ∧
                          (FullMem c { s with core := { s.core with repr := rp2' } } ⋆ R) mNxt)
                      ?_ ?_
                    · rintro _ ⟨_ra_d, _rb_d, ⟨⟩⟩ mNxt ⟨rp2', hrp2', hwf2', hmNxt⟩
                      c0_hsteps!
                      exact ih2 (ei2 + 1#64) mNxt (by rw [hei1]; omega)
                        ⟨by omega, rp2', hrp2', hwf2', hmNxt⟩
                    · intro J_m hJ_m
                      c0_hsplit
                      · -- `ra ≠ rb`: check swap `(rb >> 1) < (ra >> 1)` then merge!
                        have hne_same : ra ≠ rb := by assumption
                        have hne_var : ra.toNat / 2 ≠ rb.toNat / 2 := by
                          intro hdv
                          have : ra.toNat = rb.toNat ∨ ra.toNat = rb.toNat ^^^ 1 := by
                            rw [m6_nat_xor1_cases]; split <;> omega
                          rcases this with he | he
                          · exact hne_same (BitVec.eq_of_toNat_eq he)
                          · exact hne_opp (BitVec.eq_of_toNat_eq
                              (by rw [m6_els_bv32_xor1_toNat]; exact he))
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32, i32])
                          (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                          (fun (ra', rb') m_sw => m_sw = ml ∧ ra'.toNat < 2 * s.core.cur_vars ∧
                            rb'.toNat < 2 * s.core.cur_vars ∧ ra'.toNat / 2 < rb'.toNat / 2 ∧
                            LitEquiv (cnfOfClauses F_cur) ra'.toNat rb'.toNat) ?_ ?_
                        · rintro _ ⟨ra', rb'⟩ m_sw ⟨rfl, hra', hrb', hdv', heqv'⟩
                          have hrb_bd' : rb'.toNat < rp2.length := by rw [hrp2]; omega
                          have hrx_bd' : (rb' ^^^ 1#32).toNat < rp2.length := by
                            rw [hrp2, m6_els_bv32_xor1_toNat]
                            exact Nat.lt_of_lt_of_le (m6_nat_xor1_lt hrb') (by omega)
                          have _hrb_64 : (BitVec.setWidth 64 rb').toNat < rp2.length := by
                            rw [bv_c0_zext32_64]; exact hrb_bd'
                          have _hrx_64 : (BitVec.setWidth 64 (rb' ^^^ 1#32)).toNat <
                              (rp2.set (BitVec.setWidth 64 rb').toNat ra').length := by
                            rw [List.length_set, bv_c0_zext32_64]; exact hrx_bd'
                          let rp2' := (rp2.set rb'.toNat ra').set (rb' ^^^ 1#32).toNat
                            (ra' ^^^ 1#32)
                          have hwf' : M6FoldWf F_cur s.core.cur_vars rp2' :=
                            m6_foldWf_merge hwf2 hra' hrb' heqv' hdv'
                          have hset_sw :
                              (rp2.set (BitVec.setWidth 64 rb').toNat ra').set
                                (BitVec.setWidth 64 (rb' ^^^ 1#32)).toNat (ra' ^^^ 1#32) =
                              rp2' := by
                            simp only [rp2', bv_c0_zext32_64]
                          c0_hsteps!
                          refine hJ_m (ra', rb', ()) _ ⟨rp2', by simp [rp2', hrp2], hwf', ?_⟩
                          dsimp only
                          rw [← hset_sw]
                          assumption
                        · intro Jsw hJsw
                          c0_hsplit
                          · have hlt_v : rb.toNat / 2 < ra.toNat / 2 := by bv_omega
                            c0_hsteps!
                            exact hJsw (rb, ra) ml ⟨rfl, hrb_lt, hra_lt, hlt_v, heqv_ab.symm⟩
                          · have hnlt_v : ¬ rb.toNat / 2 < ra.toNat / 2 := by bv_omega
                            c0_hsteps!
                            exact hJsw (ra, rb) ml ⟨rfl, hra_lt, hrb_lt, by omega, heqv_ab⟩
                      · -- `ra == rb`: skip
                        c0_hsteps!
                        exact hJ_m (ra, rb, ()) ml ⟨rp2, hrp2, hwf2, hml⟩
                · intro JwB hJwB
                  c0_hsplit
                  · c0_hsplit
                    · have hne_rb : rp2[rb.toNat]'hrb_bd ≠ rb := by
                        first
                        | exact ‹_›
                        | (intro heq
                           have hc' : ¬ rp2[(BitVec.setWidth 64 rb).toNat]'_hrb_c0 = rb := by
                             assumption
                           exact hc' (by rwa [m6_getElem_congr (bv_c0_zext32_64 rb) _ hrb_bd]))
                      have hprop := m6_foldWf_lit_prop hwf2 hrb_lt
                      rw [List.getElem?_eq_getElem hrb_bd, Option.getD_some] at hprop
                      have hlt_step : (rp2[rb.toNat]'hrb_bd).toNat / 2 < rb.toNat / 2 := by
                        rcases hprop.2 with heq | hlt
                        · exfalso; exact hne_rb (BitVec.eq_of_toNat_eq heq)
                        · exact hlt
                      have heq_step : LitEquiv (cnfOfClauses F_cur) b.toNat
                          (rp2[rb.toNat]'hrb_bd).toNat := by
                        have h2 := hwf2.2.2.2 rb.toNat hrb_lt
                        rw [List.getElem?_eq_getElem hrb_bd, Option.getD_some] at h2
                        exact heq_b.trans h2
                      have hgb1 : (gb - 1#64).toNat = gb.toNat - 1 := by bv_omega
                      c0_hsteps!; dsimp only
                      rw [m6_getElem_congr (bv_c0_zext32_64 rb) _ hrb_bd]
                      exact ihB (rp2[rb.toNat]'hrb_bd, gb - 1#64) ml
                        (by dsimp only; rw [hgb1]; omega)
                        (by dsimp only; rw [hgb1]; exact ⟨hprop.1, by omega, by omega, heq_step,
                          rfl⟩)
                    · have hrb_root : rp2[rb.toNat]'hrb_bd = rb := by
                        first
                        | exact ‹_›
                        | (have hh : rp2[(BitVec.setWidth 64 rb).toNat]'_hrb_c0 = rb := by
                             assumption
                           rwa [m6_getElem_congr (bv_c0_zext32_64 rb) _ hrb_bd] at hh)
                      c0_hsteps!
                      exact hJwB () ml ⟨hrb_root, rfl⟩
                  · exfalso; bv_omega
            · intro JwA hJwA
              c0_hsplit
              · c0_hsplit
                · -- `rp2[ra] ≠ ra`: step `ra := rp2[ra]`, `ga := ga - 1`
                  have hne_ra : rp2[ra.toNat]'hra_bd ≠ ra := by
                    first
                    | exact ‹_›
                    | (intro heq
                       have hc' : ¬ rp2[(BitVec.setWidth 64 ra).toNat]'_hra_c0 = ra := by
                         assumption
                       exact hc' (by rwa [m6_getElem_congr (bv_c0_zext32_64 ra) _ hra_bd]))
                  have hprop := m6_foldWf_lit_prop hwf2 hra_lt
                  rw [List.getElem?_eq_getElem hra_bd, Option.getD_some] at hprop
                  have hlt_step : (rp2[ra.toNat]'hra_bd).toNat / 2 < ra.toNat / 2 := by
                    rcases hprop.2 with heq | hlt
                    · exfalso; exact hne_ra (BitVec.eq_of_toNat_eq heq)
                    · exact hlt
                  have heq_step : LitEquiv (cnfOfClauses F_cur) a.toNat
                      (rp2[ra.toNat]'hra_bd).toNat := by
                    have h2 := hwf2.2.2.2 ra.toNat hra_lt
                    rw [List.getElem?_eq_getElem hra_bd, Option.getD_some] at h2
                    exact heq_a.trans h2
                  have hga1 : (ga - 1#64).toNat = ga.toNat - 1 := by bv_omega
                  c0_hsteps!; dsimp only
                  rw [m6_getElem_congr (bv_c0_zext32_64 ra) _ hra_bd]
                  exact ihA (rp2[ra.toNat]'hra_bd, ga - 1#64) ml
                    (by dsimp only; rw [hga1]; omega)
                    (by dsimp only; rw [hga1]; exact ⟨hprop.1, by omega, by omega, heq_step, rfl⟩)
                · have hra_root : rp2[ra.toNat]'hra_bd = ra := by
                    first
                    | exact ‹_›
                    | (have hh : rp2[(BitVec.setWidth 64 ra).toNat]'_hra_c0 = ra := by
                         assumption
                       rwa [m6_getElem_congr (bv_c0_zext32_64 ra) _ hra_bd] at hh)
                  c0_hsteps!
                  exact hJwA () ml ⟨hra_root, rfl⟩
              · exfalso; bv_omega
        · -- Exit Loop 2 (`ei = neq`): Loop 3 (flatten) -> Pass 2 (units) -> Pass 3 (ext/inact)
          c0_hsteps_nogrp
          refine wp_while_state (ts := [i64]) (proj := fun v : BitVec 64 => (v, ()))
            (μ := fun v => s.core.cur_vars - v.toNat)
            (Inv := fun v ml3 => v.toNat ≤ s.core.cur_vars ∧ ∃ rp3 : List (BitVec 32),
              rp3.length = 2 * c.max_vars ∧ M6FoldWf F_cur s.core.cur_vars rp3 ∧
              (∀ w < v.toNat, rp3[(rp3[2 * w]?.getD 0#32).toNat]? = rp3[2 * w]? ∧
                rp3[(rp3[2 * w + 1]?.getD 0#32).toNat]? = rp3[2 * w + 1]?) ∧
              (FullMem c { s with core := { s.core with repr := rp3 } } ⋆ R) ml3) ?_ ?_
          · intro J3 hJ3; c0_hsteps!
            exact hJ3 0#64 ml ⟨Nat.zero_le _, rp2, hrp2, hwf2, (fun _ hw => by cases hw), hml⟩
          · rintro J3 v3 ml3 ⟨hv3_le, rp3, hrp3, hwf3, hfl3, hml3⟩ ih3
            c0_hsplit
            · have hv_lt : v3.toNat < s.core.cur_vars := by bv_omega
              have hv1 : (v3 + 1#64).toNat = v3.toNat + 1 := by bv_omega
              obtain ⟨hpl, _⟩ := m6_bv32_shl1_even v3 (by omega)
              have h2v_rp : (BitVec.setWidth 32 (v3 <<< 1#64)).toNat < rp3.length := by
                rw [hrp3, hpl]; omega
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (proj := fun x : BitVec 32 => (x, ()))
                (fun _ ml3' => ∃ rp3' : List (BitVec 32),
                  rp3'.length = 2 * c.max_vars ∧ M6FoldWf F_cur s.core.cur_vars rp3' ∧
                  (∀ w < v3.toNat + 1,
                    rp3'[(rp3'[2 * w]?.getD 0#32).toNat]? = rp3'[2 * w]? ∧
                    rp3'[(rp3'[2 * w + 1]?.getD 0#32).toNat]? = rp3'[2 * w + 1]?) ∧
                  (FullMem c { s with core := { s.core with repr := rp3' } } ⋆ R) ml3')
                ?_ ?_
              · rintro _ _ ml3' ⟨rp3', hrp3', hwf3', hfl3', hml3'⟩
                c0_hsteps!
                exact ih3 (v3 + 1#64) ml3' (by rw [hv1]; omega)
                  ⟨by omega, rp3', hrp3', hwf3', hv1 ▸ hfl3', hml3'⟩
              · intro Jl3 hJl3
                c0_hsplit
                · -- `r != pl`
                  have hne_rp : rp3[(BitVec.setWidth 32 (v3 <<< 1#64)).toNat]'h2v_rp ≠
                      BitVec.setWidth 32 (v3 <<< 1#64) := ‹_›
                  have h2v_bd : 2 * v3.toNat < rp3.length := by rw [hrp3]; omega
                  have hr_bd : (rp3[2 * v3.toNat]'h2v_bd).toNat < rp3.length := by
                    have := (hwf3.2.1 v3.toNat hv_lt).1
                    rw [List.getElem?_eq_getElem h2v_bd, Option.getD_some] at this
                    rw [hrp3]; omega
                  have hr_c0_bd : (rp3[(BitVec.setWidth 32 (v3 <<< 1#64)).toNat]'h2v_rp).toNat <
                      rp3.length := by
                    rw [m6_getElem_congr hpl h2v_rp h2v_bd]; exact hr_bd
                  have hstep := m6_foldWf_flatten_step hwf3 hv_lt hcv32 hfl3
                  have hne_ofNat :
                      rp3[2 * v3.toNat]?.getD 0#32 ≠ BitVec.ofNat 32 (2 * v3.toNat) := by
                    rw [List.getElem?_eq_getElem h2v_bd, Option.getD_some]
                    intro he; apply hne_rp
                    rw [m6_getElem_congr hpl h2v_rp h2v_bd, he]
                    apply BitVec.eq_of_toNat_eq
                    rw [hpl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  dsimp only at hstep; simp only [ite_eq_left hne_ofNat] at hstep
                  have h2v1_rp : ((BitVec.setWidth 32 (v3 <<< 1#64)) ||| 1#32).toNat =
                      2 * v3.toNat + 1 := by
                    rw [m6_bv32_lit_or1 _ (by rw [hpl]; omega), m6_els_bv32_xor1_toNat, hpl,
                      m6_nat_xor1_even]
                  have h2v1_bd : ((BitVec.setWidth 32 (v3 <<< 1#64)) ||| 1#32).toNat <
                      rp3.length := by rw [hrp3, h2v1_rp]; omega
                  have h2v_64 : (BitVec.setWidth 64 (BitVec.setWidth 32 (v3 <<< 1#64))).toNat <
                      rp3.length := by rw [bv_c0_zext32_64]; exact h2v_rp
                  have hr_64 : (BitVec.setWidth 64
                      (rp3[(BitVec.setWidth 32 (v3 <<< 1#64)).toNat]'h2v_rp)).toNat <
                      rp3.length := by rw [bv_c0_zext32_64]; exact hr_c0_bd
                  have h2v1_64 : (BitVec.setWidth 64
                      ((BitVec.setWidth 32 (v3 <<< 1#64)) ||| 1#32)).toNat <
                      (rp3.set (BitVec.setWidth 32 (v3 <<< 1#64)).toNat
                        (rp3[(rp3[(BitVec.setWidth 32 (v3 <<< 1#64)).toNat]'h2v_rp).toNat]'
                          hr_c0_bd)).length := by
                    rw [List.length_set, bv_c0_zext32_64]; exact h2v1_bd
                  c0_hsteps!
                  have hix :
                      (rp3[(BitVec.setWidth 32 (v3 <<< 1#64)).toNat]'h2v_rp).toNat =
                        (rp3[2 * v3.toNat]'h2v_bd).toNat := by
                    rw [m6_getElem_congr hpl h2v_rp h2v_bd]
                  let r0_c0 :=
                    rp3[(rp3[(BitVec.setWidth 32 (v3 <<< 1#64)).toNat]'h2v_rp).toNat]'hr_c0_bd
                  let r0_n := rp3[(rp3[2 * v3.toNat]?.getD 0#32).toNat]?.getD 0#32
                  have hr0_eq : r0_c0 = r0_n := by
                    dsimp only [r0_c0, r0_n]
                    rw [List.getElem?_eq_getElem h2v_bd, Option.getD_some,
                      m6_getElem_congr hix hr_c0_bd hr_bd, List.getElem?_eq_getElem hr_bd,
                      Option.getD_some]
                  let rp3_n := (rp3.set (2 * v3.toNat) r0_n).set (2 * v3.toNat + 1) (r0_n ^^^ 1#32)
                  have hset_rp3 :
                      (rp3.set (BitVec.setWidth 32 (v3 <<< 1#64)).toNat r0_c0).set
                        ((BitVec.setWidth 32 (v3 <<< 1#64) ||| 1#32)).toNat (r0_c0 ^^^ 1#32) =
                      rp3_n :=
                    m6_list_set2_eq rp3 hpl h2v1_rp hr0_eq (congrArg (· ^^^ 1#32) hr0_eq)
                  refine hJl3 r0_c0 _ ⟨rp3_n, by simp [rp3_n, hrp3], hstep.1, hstep.2, ?_⟩
                  rw [← hset_rp3]; assumption
                · -- `r == pl`: unchanged
                  have heq_rp : rp3[(BitVec.setWidth 32 (v3 <<< 1#64)).toNat]'h2v_rp =
                      BitVec.setWidth 32 (v3 <<< 1#64) := by assumption
                  have hstep := m6_foldWf_flatten_step hwf3 hv_lt hcv32 hfl3
                  have heq_ofNat :
                      rp3[2 * v3.toNat]?.getD 0#32 = BitVec.ofNat 32 (2 * v3.toNat) := by
                    rw [List.getElem?_eq_getElem (by rw [hrp3]; omega), Option.getD_some]
                    rw [← m6_getElem_congr hpl h2v_rp (by rw [hrp3]; omega), heq_rp]
                    apply BitVec.eq_of_toNat_eq
                    rw [hpl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  dsimp only at hstep
                  rw [ite_eq_right (fun h => h heq_ofNat)] at hstep
                  c0_hsteps!
                  exact hJl3 _ ml3 ⟨rp3, hrp3, hstep.1, hstep.2, hml3⟩
            · -- Exit Loop 3 (`v = cv`): `M6ReprFlatInv F_cur (2 * cv) rp3`!
              have hv_eq : v3.toNat = s.core.cur_vars := by bv_omega
              have hflat3 : M6ReprFlatInv F_cur (2 * s.core.cur_vars) rp3 :=
                m6_foldWf_to_flat hwf3 (fun w hw => hfl3 w (hv_eq ▸ hw))
              let s3 : FullState := { s with core := { s.core with repr := rp3 } }
              have hinv3 : FullDenseInvW c F0 F_cur s3 := m6_denseInvW_set_repr hinv hrp3
              -- Pass 2: `v = 0 ..< cv`: sync level-0 unit values with `repr`
              c0_hsteps_nogrp
              refine wp_while_state (ts := [i64]) (proj := fun v : BitVec 64 => (v, ()))
                (μ := fun v => s.core.cur_vars - v.toNat)
                (Inv := fun v ml4 => v.toNat ≤ s.core.cur_vars ∧ ∃ s4 : FullState,
                  M6ElsFoldFrame c F0 F_cur s s4 ∧
                  M6ReprFlatInv F_cur (2 * s4.core.cur_vars) s4.core.repr ∧
                  (FullMem c s4 ⋆ R) ml4) ?_ ?_
              · intro J4 hJ4; c0_hsteps!
                exact hJ4 0#64 ml3 ⟨Nat.zero_le _, s3, ⟨hinv3, rfl, rfl, rfl, rfl, rfl, rfl⟩,
                  hflat3, hml3⟩
              · rintro J4 v4 ml4 ⟨hv4_le, s4, hfr4, hfl4, hm4⟩ ih4
                have hinv4 := hfr4.1; have hcl4 := hinv4.1.core_ok; have hw4 := hinv4.2.1
                have hcv4 : s4.core.cur_vars = s.core.cur_vars := hfr4.2.1
                have hcv4_le := hcl4.cur_vars_le; have hvl4 := hcl4.vals_len
                have hrp4 := hcl4.repr_len; have hcl0_4 := hinv4.2.2.2.2.2.1
                c0_hsplit
                · have hv_lt : v4.toNat < s4.core.cur_vars := by bv_omega
                  have hv1 : (v4 + 1#64).toNat = v4.toNat + 1 := by bv_omega
                  obtain ⟨hlit_to, _⟩ := m6_bv32_shl1_even v4 (by omega)
                  have hlit_lt :
                      (BitVec.setWidth 32 (v4 <<< 1#64)).toNat < 2 * s4.core.cur_vars := by
                    rw [hlit_to]; omega
                  have hlit_rp :
                      (BitVec.setWidth 32 (v4 <<< 1#64)).toNat < s4.core.repr.length := by
                    rw [hrp4]; omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := []) (fun () mN4 => ∃ s4' : FullState,
                      M6ElsFoldFrame c F0 F_cur s s4' ∧
                      M6ReprFlatInv F_cur (2 * s4'.core.cur_vars) s4'.core.repr ∧
                      (FullMem c s4' ⋆ R) mN4) ?_ ?_
                  · rintro _ ⟨⟩ mN4 ⟨s4', hfr4', hfl4', hmN4⟩
                    c0_hsteps!
                    have hcv4' : s4'.core.cur_vars = s.core.cur_vars := hfr4'.2.1
                    exact ih4 (v4 + 1#64) mN4 (by rw [hv1]; omega)
                      ⟨by omega, s4', hfr4', hfl4', hmN4⟩
                  · intro JN4 hJN4
                    c0_hsplit
                    · -- `rep != lit`
                      let lit32 := BitVec.setWidth 32 (v4 <<< 1#64)
                      have hlit32_to : lit32.toNat = 2 * v4.toNat := hlit_to
                      let rep32 := s4.core.repr[lit32.toNat]'hlit_rp
                      have hrep_lt : rep32.toNat < 2 * s4.core.cur_vars := by
                        have := m6_reprFlat_lt hfl4 hlit_lt
                        rwa [List.getElem?_eq_getElem hlit_rp, Option.getD_some] at this
                      have heqv_lr : LitEquiv (cnfOfClauses F_cur) lit32.toNat rep32.toNat := by
                        have := m6_reprFlat_equiv hfl4 hlit_lt
                        rwa [List.getElem?_eq_getElem hlit_rp, Option.getD_some] at this
                      have hlit_vl : lit32.toNat < s4.core.vals.length := by
                        rw [hvl4, hlit32_to]; omega
                      have hrep_vl : rep32.toNat < s4.core.vals.length := by
                        rw [hvl4]; exact Nat.lt_of_lt_of_le hrep_lt (by omega)
                      have hlit_mod : 2 * v4.toNat % 2 ^ 64 % 2 ^ 32 = lit32.toNat := by
                        rw [hlit32_to, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      have hvl_c0_eq :
                          s4.core.vals[(2 * v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by
                            rw [hlit_mod]; exact hlit_vl) =
                          s4.core.vals[lit32.toNat]'hlit_vl :=
                        m6_getElem_congr hlit_mod _ hlit_vl
                      have hrep_c0_eq :
                          s4.core.repr[(2 * v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by
                            rw [hlit_mod]; exact hlit_rp) = rep32 :=
                        m6_getElem_congr hlit_mod _ hlit_rp
                      have hvr_c0_eq :
                          s4.core.vals[(s4.core.repr[(2 * v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by
                            rw [hlit_mod]; exact hlit_rp)).toNat]'(by
                            rw [hrep_c0_eq]; exact hrep_vl) =
                          s4.core.vals[rep32.toNat]'hrep_vl :=
                        m6_getElem_congr (congrArg BitVec.toNat hrep_c0_eq) _ hrep_vl
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun () mN4 => ∃ s4' : FullState,
                          M6ElsFoldFrame c F0 F_cur s s4' ∧
                          M6ReprFlatInv F_cur (2 * s4'.core.cur_vars) s4'.core.repr ∧
                          (FullMem c s4' ⋆ R) mN4) ?_ ?_
                      · rintro _ ⟨⟩ mN4 ⟨s4', hfr4', hfl4', hmN4⟩
                        c0_hsteps!; exact hJN4 () mN4 ⟨s4', hfr4', hfl4', hmN4⟩
                      · intro JNa hJNa
                        refine wp_join_group (ts := []) (fun () mE1 => mE1 = ml4 ∧
                            ¬ (s4.core.vals[lit32.toNat]'hlit_vl ≠ 0#8 ∧
                              s4.core.vals[rep32.toNat]'hrep_vl = 0#8)) ?_ ?_
                        · rintro _ ⟨⟩ mE1 ⟨hmE1, hnot1⟩
                          refine wp_join_group (ts := []) (fun () mN5 => ∃ s4' : FullState,
                              M6ElsFoldFrame c F0 F_cur s s4' ∧
                              M6ReprFlatInv F_cur (2 * s4'.core.cur_vars) s4'.core.repr ∧
                              (FullMem c s4' ⋆ R) mN5) ?_ ?_
                          · rintro _ ⟨⟩ mN5 ⟨s4', hfr4', hfl4', hmN5⟩
                            c0_hsteps!; exact hJNa () mN5 ⟨s4', hfr4', hfl4', hmN5⟩
                          · intro JNb hJNb
                            refine wp_join_group (ts := []) (fun () mE2 => mE2 = ml4 ∧
                                ¬ (s4.core.vals[rep32.toNat]'hrep_vl ≠ 0#8 ∧
                                  s4.core.vals[lit32.toNat]'hlit_vl = 0#8)) ?_ ?_
                            · rintro _ ⟨⟩ mE2 ⟨hmE2, hnot2⟩
                              -- `else if (vl != 0 && vl != vr)`: UNSAT!
                              c0_hsplit
                              · c0_hsplit
                                · have hvl_nz : s4.core.vals[lit32.toNat]'hlit_vl ≠ 0#8 := by
                                    have hc' : (s4.core.vals[(2 * v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by
                                        rw [hlit_mod]; exact hlit_vl)).signExtend 32 ≠ 0#32 := by
                                      assumption
                                    rw [hvl_c0_eq, ne_eq, m6_bv8_sext32_eq0_iff] at hc'
                                    exact hc'
                                  have hvl_ne_vr : s4.core.vals[lit32.toNat]'hlit_vl ≠
                                      s4.core.vals[rep32.toNat]'hrep_vl := by
                                    have hcn :
                                        (s4.core.vals[(2 * v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by
                                          rw [hlit_mod]; exact hlit_vl)).signExtend 32 ≠
                                        (s4.core.vals[(s4.core.repr[(2 * v4.toNat % 2 ^ 64 %
                                          2 ^ 32)]'(by rw [hlit_mod]; exact hlit_rp)).toNat]'(by
                                          rw [hrep_c0_eq]; exact hrep_vl)).signExtend 32 := by
                                      assumption
                                    rw [hvl_c0_eq, hvr_c0_eq] at hcn
                                    exact fun heq => hcn (congrArg (BitVec.signExtend 32) heq)
                                  have hvr_nz : s4.core.vals[rep32.toNat]'hrep_vl ≠ 0#8 :=
                                    fun h0 => hnot1 ⟨hvl_nz, h0⟩
                                  have hdom_l : s4.core.vals[lit32.toNat]'hlit_vl = 1#8 ∨
                                      s4.core.vals[lit32.toNat]'hlit_vl = 0xFF#8 := by
                                    rcases hw4.vals_domain lit32.toNat hlit_lt with h0 | h1 | h2
                                    · rw [List.getElem?_eq_getElem hlit_vl,
                                        Option.getD_some] at h0
                                      exact absurd h0 hvl_nz
                                    · rw [List.getElem?_eq_getElem hlit_vl,
                                        Option.getD_some] at h1
                                      exact Or.inl h1
                                    · rw [List.getElem?_eq_getElem hlit_vl,
                                        Option.getD_some] at h2
                                      exact Or.inr h2
                                  have hdom_r : s4.core.vals[rep32.toNat]'hrep_vl = 1#8 ∨
                                      s4.core.vals[rep32.toNat]'hrep_vl = 0xFF#8 := by
                                    rcases hw4.vals_domain rep32.toNat hrep_lt with h0 | h1 | h2
                                    · rw [List.getElem?_eq_getElem hrep_vl,
                                        Option.getD_some] at h0
                                      exact absurd h0 hvr_nz
                                    · rw [List.getElem?_eq_getElem hrep_vl,
                                        Option.getD_some] at h1
                                      exact Or.inl h1
                                    · rw [List.getElem?_eq_getElem hrep_vl,
                                        Option.getD_some] at h2
                                      exact Or.inr h2
                                  have huns : (cnfOfClauses F_cur).Unsat := by
                                    rcases hdom_l with hl1 | hlf <;>
                                      rcases hdom_r with hr1 | hrf
                                    · exact absurd (hl1.trans hr1.symm) hvl_ne_vr
                                    · exact m6_litEquiv_unsat_contra heqv_lr
                                        (m6_lvl0_true_entails hw4 hcl0_4 hlit_lt (by
                                          rw [List.getElem?_eq_getElem hlit_vl, Option.getD_some]
                                          exact hl1))
                                        (m6_lvl0_false_entails hw4 hcl0_4 hrep_lt (by
                                          rw [List.getElem?_eq_getElem hrep_vl, Option.getD_some]
                                          exact hrf))
                                    · exact m6_litEquiv_unsat_contra heqv_lr.symm
                                        (m6_lvl0_true_entails hw4 hcl0_4 hrep_lt (by
                                          rw [List.getElem?_eq_getElem hrep_vl, Option.getD_some]
                                          exact hr1))
                                        (m6_lvl0_false_entails hw4 hcl0_4 hlit_lt (by
                                          rw [List.getElem?_eq_getElem hlit_vl, Option.getD_some]
                                          exact hlf))
                                    · exact absurd (hlf.trans hrf.symm) hvl_ne_vr
                                  subst mE2
                                  c0_hsteps!
                                  exact m6_els_fold_fail_unsat hfr4 huns (by assumption) hQ
                                · c0_hsteps!; rw [hmE2]; exact hJNb () ml4 ⟨s4, hfr4, hfl4, hm4⟩
                              · c0_hsteps!; rw [hmE2]; exact hJNb () ml4 ⟨s4, hfr4, hfl4, hm4⟩
                            · intro JE2 hJE2
                              c0_hsplit
                              · c0_hsplit
                                · have hvr_nz : s4.core.vals[rep32.toNat]'hrep_vl ≠ 0#8 := by
                                    rw [ne_eq, ← m6_bv8_sext32_eq0_iff]; assumption
                                  have hvr_dom : s4.core.vals[rep32.toNat]'hrep_vl = 1#8 ∨
                                      s4.core.vals[rep32.toNat]'hrep_vl = 0xFF#8 := by
                                    rcases hw4.vals_domain rep32.toNat hrep_lt with h0 | h1 | h2
                                    · rw [List.getElem?_eq_getElem hrep_vl,
                                        Option.getD_some] at h0
                                      exact absurd h0 hvr_nz
                                    · rw [List.getElem?_eq_getElem hrep_vl,
                                        Option.getD_some] at h1
                                      exact Or.inl h1
                                    · rw [List.getElem?_eq_getElem hrep_vl,
                                        Option.getD_some] at h2
                                      exact Or.inr h2
                                  have hlit_xor1_lt :
                                      (lit32 ^^^ 1#32).toNat < 2 * s4.core.cur_vars := by
                                    rw [m6_els_bv32_xor1_toNat]; exact m6_nat_xor1_lt hlit_lt
                                  have hent_pos :
                                      (0#32).slt ((s4.core.vals[rep32.toNat]'hrep_vl).signExtend
                                        32) = true →
                                      (cnfOfClauses F_cur).EntailsClause
                                        (cnfClause [lit32.toNat]) := by
                                    intro hgt
                                    rcases hvr_dom with hv1_eq | hvf_eq
                                    · have he1 := m6_lvl0_true_entails hw4 hcl0_4 hrep_lt (by
                                        rw [List.getElem?_eq_getElem hrep_vl, Option.getD_some]
                                        exact hv1_eq)
                                      exact m6_entails_unit_of_dup (m6_entails_bin_subst
                                        heqv_lr.symm heqv_lr.symm
                                        (CNF.entails_clause_def.mpr fun β hβ => by
                                          have h := (clauseEvalVal_iff β _).mpr
                                            (CNF.entails_clause_def.mp he1 β hβ)
                                          rw [← clauseEvalVal_iff]
                                          simpa [clauseEvalVal] using h))
                                    · have : (0#32).slt ((s4.core.vals[rep32.toNat]'
                                          hrep_vl).signExtend 32) = false := by
                                        rw [m6_els_bv8_sgt0, hvf_eq]; decide
                                      rw [this] at hgt; cases hgt
                                  have hent_neg :
                                      (0#32).slt ((s4.core.vals[rep32.toNat]'hrep_vl).signExtend
                                        32) ≠ true →
                                      (cnfOfClauses F_cur).EntailsClause
                                        (cnfClause [(lit32 ^^^ 1#32).toNat]) := by
                                    intro hngt
                                    rcases hvr_dom with hv1_eq | hvf_eq
                                    · have : (0#32).slt ((s4.core.vals[rep32.toNat]'
                                          hrep_vl).signExtend 32) = true := by
                                        rw [m6_els_bv8_sgt0, hv1_eq]; decide
                                      exact absurd this hngt
                                    · have he1 := m6_lvl0_false_entails hw4 hcl0_4 hrep_lt (by
                                        rw [List.getElem?_eq_getElem hrep_vl, Option.getD_some]
                                        exact hvf_eq)
                                      have heqv_neg := m6_litEquiv_neg heqv_lr.symm
                                      refine m6_entails_unit_of_dup ?_
                                      rw [m6_els_bv32_xor1_toNat]
                                      exact m6_entails_bin_subst heqv_neg heqv_neg
                                        (CNF.entails_clause_def.mpr fun β hβ => by
                                          have h := (clauseEvalVal_iff β _).mpr
                                            (CNF.entails_clause_def.mp he1 β hβ)
                                          rw [← clauseEvalVal_iff]
                                          simpa [clauseEvalVal] using h)
                                  c0_hsteps_nogrp
                                  refine wp_join_state (ts := [i32])
                                    (proj := fun u : BitVec 32 => (u, ()))
                                    (fun u mU => mU = ml4 ∧ u.toNat < 2 * s4.core.cur_vars ∧
                                      (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat]))
                                    ?_ ?_
                                  · rintro _ u mU ⟨hmU_eq, hu_lt, hent_uu⟩
                                    c0_hsteps_nogrp
                                    c0_call hAddUnit
                                    refine ⟨c, F0, F_cur, s4, R, rfl, hinv4.1, hw4,
                                      fun _ => hent_uu, hmU_eq ▸ hm4, ?_⟩
                                    intro okU vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass'
                                      unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mU sU
                                      hlenU hwU hclU hfail _ hmU
                                    have hinvU := m6_denseInvW_after_addUnit hinv4 hlenU hwU hclU
                                    have hfrU : M6ElsFoldFrame c F0 F_cur s sU :=
                                      ⟨hinvU, hfr4.2.1, hfr4.2.2.1, hfr4.2.2.2.1, hfr4.2.2.2.2.1,
                                        hfr4.2.2.2.2.2.1, hfr4.2.2.2.2.2.2⟩
                                    c0_hsplit
                                    · c0_hsteps!; exact hJNb () mU ⟨sU, hfrU, hfl4, hmU⟩
                                    · have hokf : okU = false := by
                                        cases okU <;>
                                          first | rfl | contradiction | exact absurd rfl ‹_›
                                      c0_hsteps!
                                      exact hQ false sU mU hinvU hfrU.2.1 hfrU.2.2.1 hfrU.2.2.2.1
                                        hfrU.2.2.2.2.1 hfrU.2.2.2.2.2.1 hfrU.2.2.2.2.2.2
                                        (fun h => Bool.noConfusion h)
                                        (fun _ => hfail hu_lt hokf) hmU
                                  · intro Ju hJu
                                    subst mE1
                                    c0_hsplit
                                    · c0_hsteps!
                                      have hgt : (0#32).slt ((s4.core.vals[rep32.toNat]'hrep_vl
                                          ).signExtend 32) = true := by
                                        rw [m6_els_bv8_sgt0]
                                        have h0 : (0#8).slt (s4.core.vals[(s4.core.repr[(2 *
                                            v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by rw [hlit_mod]; exact
                                            hlit_rp)).toNat]'(by rw [hrep_c0_eq]; exact
                                            hrep_vl)) = true := by assumption
                                        rwa [hvr_c0_eq] at h0
                                      exact hJu lit32 ml4 ⟨rfl, hlit_lt, hent_pos hgt⟩
                                    · c0_hsteps!
                                      have hngt : (0#32).slt ((s4.core.vals[rep32.toNat]'hrep_vl
                                          ).signExtend 32) ≠ true := by
                                        rw [m6_els_bv8_sgt0]
                                        have h0 : (0#8).slt (s4.core.vals[(s4.core.repr[(2 *
                                            v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by rw [hlit_mod]; exact
                                            hlit_rp)).toNat]'(by rw [hrep_c0_eq]; exact
                                            hrep_vl)) = false := by assumption
                                        rw [hvr_c0_eq] at h0; rw [h0]; decide
                                      exact hJu (lit32 ^^^ 1#32) ml4 ⟨rfl, hlit_xor1_lt,
                                        hent_neg hngt⟩
                                · c0_hsteps!
                                  have hnot2 : ¬ (s4.core.vals[rep32.toNat]'hrep_vl ≠ 0#8 ∧
                                      s4.core.vals[lit32.toNat]'hlit_vl = 0#8) := by
                                    rintro ⟨_, hlz⟩
                                    have hcn : s4.core.vals[(2 * v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by
                                        rw [hlit_mod]; exact hlit_vl) ≠ 0#8 := by assumption
                                    rw [hvl_c0_eq] at hcn; exact hcn hlz
                                  rw [hmE1]; exact hJE2 () ml4 ⟨rfl, hnot2⟩
                              · c0_hsteps!
                                have hnot2 : ¬ (s4.core.vals[rep32.toNat]'hrep_vl ≠ 0#8 ∧
                                    s4.core.vals[lit32.toNat]'hlit_vl = 0#8) := by
                                  rintro ⟨hrnz, _⟩
                                  have hcz : (s4.core.vals[rep32.toNat]'hrep_vl).signExtend 32 =
                                      0#32 := by assumption
                                  exact hrnz ((m6_bv8_sext32_eq0_iff _).mp hcz)
                                rw [hmE1]; exact hJE2 () ml4 ⟨rfl, hnot2⟩
                        · intro JE1 hJE1
                          c0_hsplit
                          · c0_hsplit
                            · have hvl_nz : s4.core.vals[lit32.toNat]'hlit_vl ≠ 0#8 := by
                                have hc' : (s4.core.vals[(2 * v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by
                                    rw [hlit_mod]; exact hlit_vl)).signExtend 32 ≠ 0#32 := by
                                  assumption
                                rw [hvl_c0_eq, ne_eq, m6_bv8_sext32_eq0_iff] at hc'; exact hc'
                              have hvl_dom : s4.core.vals[lit32.toNat]'hlit_vl = 1#8 ∨
                                  s4.core.vals[lit32.toNat]'hlit_vl = 0xFF#8 := by
                                rcases hw4.vals_domain lit32.toNat hlit_lt with h0 | h1 | h2
                                · rw [List.getElem?_eq_getElem hlit_vl, Option.getD_some] at h0
                                  exact absurd h0 hvl_nz
                                · rw [List.getElem?_eq_getElem hlit_vl, Option.getD_some] at h1
                                  exact Or.inl h1
                                · rw [List.getElem?_eq_getElem hlit_vl, Option.getD_some] at h2
                                  exact Or.inr h2
                              have hrep_xor1_lt :
                                  (rep32 ^^^ 1#32).toNat < 2 * s4.core.cur_vars := by
                                rw [m6_els_bv32_xor1_toNat]; exact m6_nat_xor1_lt hrep_lt
                              have hent_pos :
                                  (0#32).slt ((s4.core.vals[lit32.toNat]'hlit_vl).signExtend 32) =
                                    true →
                                  (cnfOfClauses F_cur).EntailsClause (cnfClause [rep32.toNat]) := by
                                intro hgt
                                rcases hvl_dom with hv1_eq | hvf_eq
                                · have he1 := m6_lvl0_true_entails hw4 hcl0_4 hlit_lt (by
                                    rw [List.getElem?_eq_getElem hlit_vl, Option.getD_some]
                                    exact hv1_eq)
                                  exact m6_entails_unit_of_dup (m6_entails_bin_subst heqv_lr heqv_lr
                                    (CNF.entails_clause_def.mpr fun β hβ => by
                                      have h := (clauseEvalVal_iff β _).mpr
                                        (CNF.entails_clause_def.mp he1 β hβ)
                                      rw [← clauseEvalVal_iff]
                                      simpa only [clauseEvalVal, List.any_cons, List.any_nil,
                                        Bool.or_false, Bool.or_self] using h))
                                · have : (0#32).slt
                                      ((s4.core.vals[lit32.toNat]'hlit_vl).signExtend 32) =
                                        false := by rw [m6_els_bv8_sgt0, hvf_eq]; decide
                                  rw [this] at hgt; cases hgt
                              have hent_neg :
                                  (0#32).slt ((s4.core.vals[lit32.toNat]'hlit_vl).signExtend 32) ≠
                                    true →
                                  (cnfOfClauses F_cur).EntailsClause
                                    (cnfClause [(rep32 ^^^ 1#32).toNat]) := by
                                intro hngt
                                rcases hvl_dom with hv1_eq | hvf_eq
                                · have : (0#32).slt
                                      ((s4.core.vals[lit32.toNat]'hlit_vl).signExtend 32) =
                                        true := by rw [m6_els_bv8_sgt0, hv1_eq]; decide
                                  exact absurd this hngt
                                · have he1 := m6_lvl0_false_entails hw4 hcl0_4 hlit_lt (by
                                    rw [List.getElem?_eq_getElem hlit_vl, Option.getD_some]
                                    exact hvf_eq)
                                  have heqv_neg := m6_litEquiv_neg heqv_lr
                                  refine m6_entails_unit_of_dup ?_
                                  rw [m6_els_bv32_xor1_toNat]
                                  exact m6_entails_bin_subst heqv_neg heqv_neg
                                    (CNF.entails_clause_def.mpr fun β hβ => by
                                      have h := (clauseEvalVal_iff β _).mpr
                                        (CNF.entails_clause_def.mp he1 β hβ)
                                      rw [← clauseEvalVal_iff]
                                      simpa only [clauseEvalVal, List.any_cons, List.any_nil,
                                        Bool.or_false, Bool.or_self] using h)
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [i32])
                                (proj := fun u : BitVec 32 => (u, ()))
                                (fun u mU => mU = ml4 ∧ u.toNat < 2 * s4.core.cur_vars ∧
                                  (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat]))
                                ?_ ?_
                              · rintro _ u mU ⟨hmU_eq, hu_lt, hent_uu⟩
                                c0_hsteps_nogrp
                                c0_call hAddUnit
                                refine ⟨c, F0, F_cur, s4, R, rfl, hinv4.1, hw4,
                                  fun _ => hent_uu, hmU_eq ▸ hm4, ?_⟩
                                intro okU vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass'
                                  unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mU sU
                                  hlenU hwU hclU hfail _ hmU
                                have hinvU := m6_denseInvW_after_addUnit hinv4 hlenU hwU hclU
                                have hfrU : M6ElsFoldFrame c F0 F_cur s sU :=
                                  ⟨hinvU, hfr4.2.1, hfr4.2.2.1, hfr4.2.2.2.1, hfr4.2.2.2.2.1,
                                    hfr4.2.2.2.2.2.1, hfr4.2.2.2.2.2.2⟩
                                c0_hsplit
                                · c0_hsteps!; exact hJNa () mU ⟨sU, hfrU, hfl4, hmU⟩
                                · have hokf : okU = false := by
                                    cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
                                  c0_hsteps!
                                  exact hQ false sU mU hinvU hfrU.2.1 hfrU.2.2.1 hfrU.2.2.2.1
                                    hfrU.2.2.2.2.1 hfrU.2.2.2.2.2.1 hfrU.2.2.2.2.2.2
                                    (fun h => Bool.noConfusion h)
                                    (fun _ => hfail hu_lt hokf) hmU
                              · intro Ju hJu
                                c0_hsplit
                                · c0_hsteps!
                                  have hgt : (0#32).slt ((s4.core.vals[lit32.toNat]'hlit_vl
                                      ).signExtend 32) = true := by
                                    rw [m6_els_bv8_sgt0]
                                    have h0 : (0#8).slt (s4.core.vals[(2 * v4.toNat % 2 ^ 64 %
                                        2 ^ 32)]'(by rw [hlit_mod]; exact hlit_vl)) = true := by
                                      assumption
                                    rwa [hvl_c0_eq] at h0
                                  exact hJu rep32 ml4 ⟨rfl, hrep_lt, hent_pos hgt⟩
                                · c0_hsteps!
                                  have hngt : (0#32).slt ((s4.core.vals[lit32.toNat]'hlit_vl
                                      ).signExtend 32) ≠ true := by
                                    rw [m6_els_bv8_sgt0]
                                    have h0 : (0#8).slt (s4.core.vals[(2 * v4.toNat % 2 ^ 64 %
                                        2 ^ 32)]'(by rw [hlit_mod]; exact hlit_vl)) = false := by
                                      assumption
                                    rw [hvl_c0_eq] at h0; rw [h0]; decide
                                  exact hJu (rep32 ^^^ 1#32) ml4 ⟨rfl, hrep_xor1_lt, hent_neg hngt⟩
                            · c0_hsteps!
                              have hnot1 : ¬ (s4.core.vals[lit32.toNat]'hlit_vl ≠ 0#8 ∧
                                  s4.core.vals[rep32.toNat]'hrep_vl = 0#8) := by
                                rintro ⟨_, hrz⟩
                                have hcn : s4.core.vals[(s4.core.repr[(2 * v4.toNat % 2 ^ 64 %
                                    2 ^ 32)]'(by rw [hlit_mod]; exact hlit_rp)).toNat]'(by
                                    rw [hrep_c0_eq]; exact hrep_vl) ≠ 0#8 := by assumption
                                rw [hvr_c0_eq] at hcn; exact hcn hrz
                              exact hJE1 () ml4 ⟨rfl, hnot1⟩
                          · c0_hsteps!
                            have hnot1 : ¬ (s4.core.vals[lit32.toNat]'hlit_vl ≠ 0#8 ∧
                                s4.core.vals[rep32.toNat]'hrep_vl = 0#8) := by
                              rintro ⟨hlnz, _⟩
                              have hcz : (s4.core.vals[(2 * v4.toNat % 2 ^ 64 % 2 ^ 32)]'(by
                                  rw [hlit_mod]; exact hlit_vl)).signExtend 32 = 0#32 := by
                                assumption
                              rw [hvl_c0_eq, m6_bv8_sext32_eq0_iff] at hcz; exact hlnz hcz
                            exact hJE1 () ml4 ⟨rfl, hnot1⟩
                    · -- `rep == lit`: skip
                      c0_hsteps!; exact hJN4 () ml4 ⟨s4, hfr4, hfl4, hm4⟩
                · -- Exit Pass 2 -> Pass 3 (`v5 = 0 ..< cv`):
                  c0_hsteps_nogrp
                  refine wp_while_state (ts := [i64]) (proj := fun v : BitVec 64 => (v, ()))
                    (μ := fun v => s.core.cur_vars - v.toNat)
                    (Inv := fun v ml5 => v.toNat ≤ s.core.cur_vars ∧ ∃ s5 : FullState,
                      M6ElsFoldFrame c F0 F_cur s s5 ∧
                      M6ReprFlatInv F_cur (2 * s5.core.cur_vars) s5.core.repr ∧
                      (FullMem c s5 ⋆ R) ml5) ?_ ?_
                  · intro J5 hJ5; c0_hsteps!
                    exact hJ5 0#64 ml4 ⟨Nat.zero_le _, s4, hfr4, hfl4, hm4⟩
                  · rintro J5 v5 ml5 ⟨hv5_le, s5, hfr5, hfl5, hm5⟩ ih5
                    have hinv5 := hfr5.1; have hcl5 := hinv5.1.core_ok
                    have hcv5 : s5.core.cur_vars = s.core.cur_vars := hfr5.2.1
                    have hcv5_le := hcl5.cur_vars_le; have hrp5 := hcl5.repr_len
                    have hfll5 := hcl5.flags_len; have hvl5 := hcl5.vals_len
                    c0_hsplit
                    · have hv_lt : v5.toNat < s5.core.cur_vars := by bv_omega
                      have hv1 : (v5 + 1#64).toNat = v5.toNat + 1 := by bv_omega
                      obtain ⟨hlit_to, _⟩ := m6_bv32_shl1_even v5 (by omega)
                      have hlit_lt :
                          (BitVec.setWidth 32 (v5 <<< 1#64)).toNat < 2 * s5.core.cur_vars := by
                        rw [hlit_to]; omega
                      have hlit_rp :
                          (BitVec.setWidth 32 (v5 <<< 1#64)).toNat < s5.core.repr.length := by
                        rw [hrp5]; omega
                      have hlit_rp' : (BitVec.setWidth 64
                          (BitVec.setWidth 32 (v5 <<< 1#64))).toNat < s5.core.repr.length := by
                        rw [hrp5, bv_c0_zext32_64, hlit_to]; omega
                      have hlit1_rp : (BitVec.setWidth 64
                          (BitVec.setWidth 32 (v5 <<< 1#64) ||| 1#32)).toNat <
                          s5.core.repr.length := by
                        rw [hrp5, bv_c0_zext32_64, m6_bv32_lit_or1 _ (by rw [hlit_to]; omega),
                          m6_els_bv32_xor1_toNat, hlit_to, m6_nat_xor1_even]; omega
                      have hlit1_rp' : (BitVec.setWidth 64
                          (BitVec.setWidth 32 (v5 <<< 1#64) ||| 1#32)).toNat <
                          (s5.core.repr.set
                            (BitVec.setWidth 64 (BitVec.setWidth 32 (v5 <<< 1#64))).toNat
                            (BitVec.setWidth 32 (v5 <<< 1#64))).length := by
                        rw [List.length_set]; exact hlit1_rp
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun () mN5 => ∃ s5' : FullState,
                          M6ElsFoldFrame c F0 F_cur s s5' ∧
                          M6ReprFlatInv F_cur (2 * s5'.core.cur_vars) s5'.core.repr ∧
                          (FullMem c s5' ⋆ R) mN5) ?_ ?_
                      · rintro _ ⟨⟩ mN5 ⟨s5', hfr5', hfl5', hmN5⟩
                        c0_hsteps!
                        have hcv5' : s5'.core.cur_vars = s.core.cur_vars := hfr5'.2.1
                        exact ih5 (v5 + 1#64) mN5 (by rw [hv1]; omega)
                          ⟨by omega, s5', hfr5', hfl5', hmN5⟩
                      · intro JN5 hJN5
                        c0_hsplit
                        · -- `rep != lit`
                          let lit32 := BitVec.setWidth 32 (v5 <<< 1#64)
                          have hlit32_to : lit32.toNat = 2 * v5.toNat := hlit_to
                          let rep32 := s5.core.repr[lit32.toNat]'hlit_rp
                          have hrep_lt : rep32.toNat < 2 * s5.core.cur_vars := by
                            have := m6_reprFlat_lt hfl5 hlit_lt
                            rwa [List.getElem?_eq_getElem hlit_rp, Option.getD_some] at this
                          have hne_rep : rep32 ≠ lit32 := ‹_›
                          have hcv32_5 : 2 * s5.core.cur_vars < 2 ^ 32 := by omega
                          have hne_ofNat : s5.core.repr[2 * v5.toNat]?.getD 0#32 ≠
                              BitVec.ofNat 32 (2 * v5.toNat) := by
                            rw [List.getElem?_eq_getElem (by rw [hrp5]; omega), Option.getD_some]
                            intro he; apply hne_rep
                            change s5.core.repr[lit32.toNat]'hlit_rp = lit32
                            rw [m6_getElem_congr hlit_to hlit_rp (by rw [hrp5]; omega), he]
                            apply BitVec.eq_of_toNat_eq
                            rw [hlit_to, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                          refine wp_join_group (ts := []) (fun () mN6 => ∃ s5' : FullState,
                              M6ElsFoldFrame c F0 F_cur s s5' ∧
                              M6ReprFlatInv F_cur (2 * s5'.core.cur_vars) s5'.core.repr ∧
                              (FullMem c s5' ⋆ R) mN6) ?_ ?_
                          · rintro _ ⟨⟩ mN6 ⟨s5', hfr5', hfl5', hmN6⟩
                            c0_hsteps!; exact hJN5 () mN6 ⟨s5', hfr5', hfl5', hmN6⟩
                          · intro JNa hJNa
                            refine wp_join_group (ts := []) (fun () mRst => mRst = ml5) ?_ ?_
                            · rintro _ ⟨⟩ mRst rfl
                              c0_hsteps_nogrp
                              have hflatR := m6_reprFlat_set_id hfl5 hv_lt hcv32_5 hne_ofNat
                              let l32 := BitVec.ofNat 32 (2 * v5.toNat)
                              have hl32_to : l32.toNat = 2 * v5.toNat := by
                                dsimp only [l32]
                                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                              have hl32_eq : BitVec.setWidth 32 (v5 <<< 1#64) = l32 :=
                                BitVec.eq_of_toNat_eq (hlit_to.trans hl32_to.symm)
                              have hl32_x1 : l32 ^^^ 1#32 = lit32 ||| 1#32 := by
                                rw [← hl32_eq]
                                exact (m6_bv32_lit_or1 lit32 (by rw [hlit_to]; omega)).symm
                              have h2v1_eq : 2 * v5.toNat + 1 = (lit32 ||| 1#32).toNat := by
                                rw [← hl32_x1, m6_els_bv32_xor1_toNat, hl32_to, m6_nat_xor1_even]
                              have hset_eq := m6_list_set2_eq s5.core.repr
                                hlit_to.symm h2v1_eq hl32_eq.symm hl32_x1
                              dsimp only at hflatR
                              rw [hset_eq] at hflatR
                              let rpR := (s5.core.repr.set lit32.toNat lit32).set
                                (lit32 ||| 1#32).toNat (lit32 ||| 1#32)
                              have hrpR_len : rpR.length = 2 * c.max_vars := by simp [rpR, hrp5]
                              let sR : FullState :=
                                { s5 with core := { s5.core with repr := rpR } }
                              have hinvR := m6_denseInvW_set_repr hinv5 hrpR_len
                              have hfrR : M6ElsFoldFrame c F0 F_cur s sR :=
                                ⟨hinvR, hfr5.2.1, hfr5.2.2.1, hfr5.2.2.2.1, hfr5.2.2.2.2.1,
                                  hfr5.2.2.2.2.2.1, hfr5.2.2.2.2.2.2⟩
                              refine hJNa () _ ⟨sR, hfrR, hflatR, ?_⟩
                              dsimp only [sR, rpR, lit32]
                              rw [← bv_c0_zext32_64 (BitVec.setWidth 32 (v5 <<< 1#64)),
                                ← bv_c0_zext32_64 (BitVec.setWidth 32 (v5 <<< 1#64) ||| 1#32)]
                              assumption
                            · intro JR hJR
                              have hv5_fl : v5.toNat < s5.core.flags.length := by rw [hfll5]; omega
                              have hrep_fl5 : (BitVec.setWidth 64 (rep32 >>> (1 : Nat))).toNat <
                                  s5.core.flags.length := by
                                rw [hfll5, bv_c0_zext32_64, m6_els_bv32_shr1_nat]; omega
                              have hrep_c0_lt : (s5.core.repr[(BitVec.setWidth 64
                                  (BitVec.setWidth 32 (v5 <<< 1#64))).toNat]'(by
                                    rw [bv_c0_zext32_64]; exact hlit_rp)).toNat <
                                  2 * s5.core.cur_vars := by
                                rw [m6_getElem_congr (bv_c0_zext32_64 lit32) _ hlit_rp]
                                exact hrep_lt
                              have hlit_vl5 : lit32.toNat < s5.core.vals.length := by
                                rw [hvl5, hlit32_to]; omega
                              have hrep_vl5 : rep32.toNat < s5.core.vals.length := by
                                rw [hvl5]; omega
                              c0_hsplit
                              · c0_hsteps!; exact hJR () ml5 rfl
                              c0_hsplit
                              · c0_hsteps!; exact hJR () ml5 rfl
                              c0_hsteps_nogrp
                              c0_hsplit
                              · c0_hsteps!; exact hJR () ml5 rfl
                              c0_hsteps_nogrp
                              c0_hsplit
                              · c0_hsteps!; exact hJR () ml5 rfl
                              · -- `extend_len + 4 <= extend_cap`
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := [])
                                  (fun () mJex => ∃ s5' : FullState,
                                    M6ElsFoldFrame c F0 F_cur s s5' ∧
                                    M6ReprFlatInv F_cur (2 * s5'.core.cur_vars) s5'.core.repr ∧
                                    (FullMem c s5' ⋆ R) mJex) ?_ ?_
                                · rintro _ ⟨⟩ mJex ⟨s5', hfr5', hfl5', hmJex⟩
                                  c0_hsteps!; exact hJNa () mJex ⟨s5', hfr5', hfl5', hmJex⟩
                                · intro Jex hJex
                                  c0_hsplit
                                  · -- `extend_len + 4 ≤ extend_cap`
                                    have hext5 : s5.scratch.extend_len ≤ c.extend_cap :=
                                      hinv5.2.2.2.2.1.2
                                    have hlt_ext : s5.scratch.extend_len + 4 ≤ c.extend_cap := by
                                      bv_omega
                                    c0_hsteps_nogrp
                                    c0_call hExtPush2
                                    refine ⟨c, s5, R, ⟨rfl, hext5⟩, hinv5.1, hm5, ?_⟩
                                    rintro ⟨_okE1, ⟨⟩⟩ sE1 mE1 hcoreE1 hsokE1
                                      ⟨hll1, hext1, hscrE1, htmkE1, htrhE1, hwsE1⟩ hmE1
                                    change (FullMem c sE1 ⋆ R) mE1 at hmE1
                                    have hcoreE1' : sE1.core = s5.core :=
                                      fullCoreState_agrees_with_scratch hcoreE1
                                    have hinvE1 := (m6_denseInvW_after_extPush2 hinv5 hsokE1
                                      hcoreE1 hll1 hext1).1
                                    c0_hsteps_nogrp
                                    c0_call hExtPush2
                                    refine ⟨c, sE1, R, ⟨rfl, hext1⟩, hsokE1, hmE1, ?_⟩
                                    rintro ⟨_okE2, ⟨⟩⟩ sE2 mE2 hcoreE2 hsokE2
                                      ⟨hll2, hext2, hscrE2, htmkE2, htrhE2, hwsE2⟩ hmE2
                                    change (FullMem c sE2 ⋆ R) mE2 at hmE2
                                    have hcoreE2' : sE2.core = sE1.core :=
                                      fullCoreState_agrees_with_scratch hcoreE2
                                    have hinvE2 := (m6_denseInvW_after_extPush2 hinvE1 hsokE2
                                      hcoreE2 hll2 hext2).1
                                    have hcvE2 : sE2.core.cur_vars = s5.core.cur_vars := by
                                      rw [hcoreE2', hcoreE1']
                                    have hv_ltE2 : (BitVec.setWidth 32 v5).toNat <
                                        sE2.core.cur_vars := by
                                      rw [hcvE2, BitVec.toNat_setWidth,
                                        Nat.mod_eq_of_lt (by omega)]; exact hv_lt
                                    c0_hsteps_nogrp
                                    c0_call hSetInact
                                    refine ⟨c, sE2, R, rfl, hsokE2, hmE2, ?_⟩
                                    rw [ite_eq_right (by omega : ¬ sE2.core.cur_vars ≤
                                      (BitVec.setWidth 32 v5).toNat)]
                                    intro flags' unass' mI hfll' sI hmI
                                    have hinvI := m6_denseInvW_set_flags_unass hinvE2
                                      (unass' := unass') hfll'
                                    have hrpI : sI.core.repr = s5.core.repr := by
                                      dsimp only [sI]; rw [hcoreE2', hcoreE1']
                                    have hflI : M6ReprFlatInv F_cur (2 * sI.core.cur_vars)
                                        sI.core.repr := by
                                      rw [hrpI]; change M6ReprFlatInv F_cur
                                        (2 * sE2.core.cur_vars) s5.core.repr
                                      rw [hcvE2]; exact hfl5
                                    have hrep_fl :
                                        (BitVec.setWidth 64 (rep32 >>> 1#32)).toNat <
                                          flags'.length := by
                                      have hsh : (rep32 >>> 1#32).toNat = rep32.toNat / 2 := by
                                        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                      rw [hfll', bv_c0_zext32_64, hsh]; omega
                                    c0_hsteps_nogrp
                                    let flags2 :=
                                      flags'.set (BitVec.setWidth 64 (rep32 >>> 1#32)).toNat
                                        ((flags'[(BitVec.setWidth 64
                                          (rep32 >>> 1#32)).toNat]'hrep_fl) ||| 1024#32)
                                    let sF : FullState :=
                                      { sI with
                                        core := { sI.core with flags := flags2 }
                                        scratch :=
                                          { sI.scratch with
                                            subst_cnt := sI.scratch.subst_cnt + 1#64 } }
                                    have hinvF := m6_denseInvW_set_fl_subst hinvI
                                      (flags' := flags2)
                                      (sc' := sI.scratch.subst_cnt + 1#64)
                                      (by rw [List.length_set, hfll'])
                                    have hfrF : M6ElsFoldFrame c F0 F_cur s sF := by
                                      refine ⟨hinvF, ?_, ?_, ?_, ?_, ?_, ?_⟩
                                      · dsimp only [sF, sI]; rw [hcoreE2', hcoreE1']; exact hfr5.2.1
                                      · dsimp only [sF, sI]; rw [hcoreE2', hcoreE1']
                                        exact hfr5.2.2.1
                                      · dsimp only [sF, sI]; rw [htmkE2, htmkE1]
                                        exact hfr5.2.2.2.1
                                      · dsimp only [sF, sI]; rw [htrhE2, htrhE1]
                                        exact hfr5.2.2.2.2.1
                                      · dsimp only [sF, sI]; rw [hscrE2, hscrE1]
                                        exact hfr5.2.2.2.2.2.1
                                      · dsimp only [sF, sI]; rw [hwsE2, hwsE1]
                                        exact hfr5.2.2.2.2.2.2
                                    refine hJex () _ ⟨sF, hfrF, hflI, ?_⟩
                                    dsimp only [sF, sI, flags2]
                                    assumption
                                  · c0_hsteps!
                                    have hflatR := m6_reprFlat_set_id hfl5 hv_lt hcv32_5 hne_ofNat
                                    let l32 := BitVec.ofNat 32 (2 * v5.toNat)
                                    have hl32_to : l32.toNat = 2 * v5.toNat := by
                                      dsimp only [l32]
                                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                                    have hl32_eq : BitVec.setWidth 32 (v5 <<< 1#64) = l32 :=
                                      BitVec.eq_of_toNat_eq (hlit_to.trans hl32_to.symm)
                                    have hl32_x1 : l32 ^^^ 1#32 = lit32 ||| 1#32 := by
                                      rw [← hl32_eq]
                                      exact (m6_bv32_lit_or1 lit32 (by rw [hlit_to]; omega)).symm
                                    have h2v1_eq : 2 * v5.toNat + 1 = (lit32 ||| 1#32).toNat := by
                                      rw [← hl32_x1, m6_els_bv32_xor1_toNat, hl32_to,
                                        m6_nat_xor1_even]
                                    have hset_eq := m6_list_set2_eq s5.core.repr
                                      hlit_to.symm h2v1_eq hl32_eq.symm hl32_x1
                                    dsimp only at hflatR
                                    rw [hset_eq] at hflatR
                                    let rpR := (s5.core.repr.set lit32.toNat lit32).set
                                      (lit32 ||| 1#32).toNat (lit32 ||| 1#32)
                                    have hrpR_len : rpR.length = 2 * c.max_vars := by
                                      simp [rpR, hrp5]
                                    let sR : FullState :=
                                      { s5 with core := { s5.core with repr := rpR } }
                                    have hinvR := m6_denseInvW_set_repr hinv5 hrpR_len
                                    have hfrR : M6ElsFoldFrame c F0 F_cur s sR :=
                                      ⟨hinvR, hfr5.2.1, hfr5.2.2.1, hfr5.2.2.2.1, hfr5.2.2.2.2.1,
                                        hfr5.2.2.2.2.2.1, hfr5.2.2.2.2.2.2⟩
                                    refine hJex () _ ⟨sR, hfrR, hflatR, ?_⟩
                                    dsimp only [sR, rpR, lit32]
                                    rw [← bv_c0_zext32_64 (BitVec.setWidth 32 (v5 <<< 1#64)),
                                      ← bv_c0_zext32_64 (BitVec.setWidth 32 (v5 <<< 1#64) ||| 1#32)]
                                    assumption
                        · -- `rep == lit`
                          c0_hsteps!; exact hJN5 () ml5 ⟨s5, hfr5, hfl5, hm5⟩
                    · -- Exit Pass 3 (`v5 = cv`): return true!
                      c0_hsteps!
                      exact hQ true s5 ml5 hinv5 hfr5.2.1 hfr5.2.2.1 hfr5.2.2.2.1 hfr5.2.2.2.2.1
                        hfr5.2.2.2.2.2.1 hfr5.2.2.2.2.2.2 (fun _ => hfl5)
                        (fun h => Bool.noConfusion h) hm5

/-! ## 3. `full_m6_dense_els_wp` (`32/39`) -/

/-- `32/39`: Parametric `Func.wp` proof for `full_m6_dense_els`. -/
theorem full_m6_dense_els_wp (Γ : Env)
    (hFold : M6EnvSpec Γ "full_m6_els_fold" m6ElsFoldSpec)
    (hLit : M6EnvSpec Γ "full_m6_els_lit" m6ElsLitSpec)
    (hProp : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec) :
    ∀ args m Q X, m6DenseElsSpec args m Q X →
      Func.wp Γ full_m6_dense_els_body args m Q X := by
  rintro ⟨h, neq, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, heqb, hm, hQ⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () m_early =>
      (neq = 0#32 ∨ s.core.inconsistent ≠ 0#64) ∧ (FullMem c s ⋆ R) m_early) ?_ ?_
  · rintro _ ⟨⟩ m_early ⟨_, hm_e⟩
    c0_hsteps!
    by_cases hinc0 : s.core.inconsistent = 0#64
    · simpa [hinc0] using hQ true s m_early hinv rfl rfl rfl rfl rfl (by simp [hinc0])
        (fun h => Bool.noConfusion h) hm_e
    · have huns : F0.Unsat := hinv.2.1.ext_sound.2 (hinv.2.1.inconsistent_sound hinc0)
      simpa [beq_false_of_ne hinc0] using hQ false s m_early hinv rfl rfl rfl rfl rfl
        (by simp [hinc0]) (fun _ => ⟨huns, hinc0⟩) hm_e
  · intro J_e hJ_e
    c0_hsplit
    · c0_hsteps!; exact hJ_e () m ⟨Or.inl ‹_›, hm⟩
    c0_hsplit
    · c0_hsteps!; exact hJ_e () m ⟨Or.inr ‹_›, hm⟩
    have hneq_nz : neq ≠ 0#32 := ‹_›
    have hinc_z : s.core.inconsistent = 0#64 := ‹_›
    c0_hsteps_nogrp
    c0_call hFold
    refine ⟨c, F0, F_cur, s, R, rfl, hinv, heqb, hm, ?_⟩
    intro okF sF mF hinvF hcvF hflF htmkF htrhF hscrF _ hflatF hfailF hmF
    c0_hsplit
    · -- `els_fold` returned `true`: rewrite loop `v = 0 ..< cv`
      have hok_t : okF = true := ‹_›
      have hflatT := hflatF hok_t
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i64]) (proj := fun v : BitVec 64 => (v, ()))
        (μ := fun v => sF.core.cur_vars - v.toNat)
        (Inv := fun v ml => v.toNat ≤ sF.core.cur_vars ∧ ∃ sL : FullState,
          FullDenseInvW c F0 F_cur sL ∧ sL.core.cur_vars = s.core.cur_vars ∧
          sL.core.fuel = s.core.fuel ∧ sL.core.repr = sF.core.repr ∧
          sL.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
          sL.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
          sL.scratch.scratch_buf = s.scratch.scratch_buf ∧
          (FullMem c sL ⋆ R) ml) ?_ ?_
      · intro Jlp hJlp; c0_hsteps!
        exact hJlp 0#64 mF ⟨Nat.zero_le _, sF, hinvF, hcvF, hflF, rfl, htmkF, htrhF, hscrF, hmF⟩
      · rintro Jlp vL ml ⟨hv_le, sL, hinvL, hcvL, hflL, hrpL, htmkL, htrhL, hscrL, hmL⟩ ih
        have hclL := hinvL.1.core_ok; have hcvL_le := hclL.cur_vars_le
        have hmx := c.hmaxv; unfold dimacsBound at hmx
        have hflatL : M6ReprFlatInv F_cur (2 * sL.core.cur_vars) sL.core.repr := by
          rw [hrpL, hcvL, ← hcvF]; exact hflatT
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun () mEx => ∃ sE : FullState,
            FullDenseInvW c F0 F_cur sE ∧ sE.core.cur_vars = s.core.cur_vars ∧
            sE.core.fuel = s.core.fuel ∧ sE.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
            sE.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
            sE.scratch.scratch_buf = s.scratch.scratch_buf ∧ (FullMem c sE ⋆ R) mEx) ?_ ?_
        · rintro _ ⟨⟩ mEx ⟨sE, hinvE, hcvE, hflE, htmkE, htrhE, hscrE, hmEx⟩
          c0_hsplit
          · have hinc_nz : sE.core.inconsistent ≠ 0#64 := ‹_›
            have huns : F0.Unsat := hinvE.2.1.ext_sound.2 (hinvE.2.1.inconsistent_sound hinc_nz)
            c0_hsteps!
            exact hQ false sE mEx hinvE hcvE hflE htmkE htrhE hscrE (by simp [hinc_nz])
              (fun _ => ⟨huns, hinc_nz⟩) hmEx
          · c0_hsteps_nogrp
            c0_call hProp
            refine ⟨c, F0, F_cur, sE, R, rfl, hinvE, hmEx, ?_⟩
            intro okP sP mP hinvP hcvP hflP _ _ _ htmkP htrhP hscrP _ _ hinc_iff hfailP hmP
            c0_hsteps!
            exact hQ okP sP mP hinvP (hcvP.trans hcvE) (hflP.trans hflE)
              (htmkP.trans htmkE) (htrhP.trans htrhE) (hscrP.trans hscrE)
              hinc_iff hfailP hmP
        · intro Jex hJex
          c0_hsplit
          · have hv_lt : vL.toNat < sL.core.cur_vars := by bv_omega
            have hv1 : (vL + 1#64).toNat = vL.toNat + 1 := by bv_omega
            c0_hsplit
            · c0_hsplit
              · obtain ⟨hlit_to, _⟩ := m6_bv32_shl1_even vL (by omega)
                have hlit_lt : (BitVec.setWidth 32 (vL <<< 1#64)).toNat < 2 * sL.core.cur_vars := by
                  rw [hlit_to]; omega
                have hlit_rp : (BitVec.setWidth 32 (vL <<< 1#64)).toNat < sL.core.repr.length := by
                  rw [hclL.repr_len]; omega
                let lit32 := BitVec.setWidth 32 (vL <<< 1#64)
                let rl32 := sL.core.repr[lit32.toNat]'hlit_rp
                have hrl_lt : rl32.toNat < 2 * sL.core.cur_vars := by
                  have := m6_reprFlat_lt hflatL hlit_lt
                  rwa [List.getElem?_eq_getElem hlit_rp, Option.getD_some] at this
                have heqv_pos : LitEquiv (cnfOfClauses F_cur) lit32.toNat rl32.toNat := by
                  have := m6_reprFlat_equiv hflatL hlit_lt
                  rwa [List.getElem?_eq_getElem hlit_rp, Option.getD_some] at this
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun () mN => ∃ sN : FullState,
                    FullDenseInvW c F0 F_cur sN ∧ sN.core.cur_vars = s.core.cur_vars ∧
                    sN.core.fuel = s.core.fuel ∧ sN.core.repr = sF.core.repr ∧
                    sN.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
                    sN.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
                    sN.scratch.scratch_buf = s.scratch.scratch_buf ∧ (FullMem c sN ⋆ R) mN)
                  ?_ ?_
                · rintro _ ⟨⟩ mN ⟨sN, hinvN, hcvN, hflN, hrpN, htmkN, htrhN, hscrN, hmN⟩
                  c0_hsteps!
                  have hcvN' : sN.core.cur_vars = sF.core.cur_vars := by rw [hcvN, ← hcvF]
                  exact ih (vL + 1#64) mN (by rw [hv1]; omega)
                    ⟨by omega, sN, hinvN, hcvN, hflN, hrpN, htmkN, htrhN, hscrN, hmN⟩
                · intro JN hJN
                  c0_hsplit
                  · c0_hsteps_nogrp
                    c0_call hLit
                    refine ⟨c, F0, F_cur, sL, R, rfl, hinvL, hlit_lt, hrl_lt, heqv_pos,
                      hflatL, hmL, ?_⟩
                    intro ok1 s1 m1 hinv1 hcv1 hfl1 hrp1 htmk1 htrh1 hscr1 _ _ hfail1 hm1
                    c0_hsplit
                    · have hok1 : ok1 = true := ‹_›
                      have hflat1 : M6ReprFlatInv F_cur (2 * s1.core.cur_vars) s1.core.repr := by
                        rw [hrp1, hcv1]; exact hflatL
                      have hlit1_to : (lit32 ||| 1#32).toNat = lit32.toNat ^^^ 1 := by
                        rw [m6_bv32_lit_or1 lit32 (by rw [hlit_to]; omega),
                          m6_els_bv32_xor1_toNat]
                      have hlit1_lt : (lit32 ||| 1#32).toNat < 2 * s1.core.cur_vars := by
                        rw [hlit1_to, hcv1]; exact m6_nat_xor1_lt hlit_lt
                      have hrl1_lt : (rl32 ^^^ 1#32).toNat < 2 * s1.core.cur_vars := by
                        rw [m6_els_bv32_xor1_toNat, hcv1]; exact m6_nat_xor1_lt hrl_lt
                      have heqv_neg : LitEquiv (cnfOfClauses F_cur)
                          (lit32 ||| 1#32).toNat (rl32 ^^^ 1#32).toNat := by
                        rw [hlit1_to, m6_els_bv32_xor1_toNat]; exact m6_litEquiv_neg heqv_pos
                      c0_hsteps_nogrp
                      c0_call hLit
                      refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, hlit1_lt, hrl1_lt, heqv_neg,
                        hflat1, hm1, ?_⟩
                      intro ok2 s2 m2 hinv2 hcv2 hfl2 hrp2 htmk2 htrh2 hscr2 _ _ hfail2 hm2
                      c0_hsplit
                      · c0_hsteps!
                        exact hJN () m2 ⟨s2, hinv2, hcv2.trans (hcv1.trans hcvL),
                          hfl2.trans (hfl1.trans hflL), hrp2.trans (hrp1.trans hrpL),
                          htmk2.trans (htmk1.trans htmkL), htrh2.trans (htrh1.trans htrhL),
                          hscr2.trans (hscr1.trans hscrL), hm2⟩
                      · have hok2 : ok2 = false := by
                          cases ok2 <;> first | rfl | contradiction | exact absurd rfl ‹_›
                        c0_hsteps!
                        exact hQ false s2 m2 hinv2 (hcv2.trans (hcv1.trans hcvL))
                          (hfl2.trans (hfl1.trans hflL))
                          (htmk2.trans (htmk1.trans htmkL)) (htrh2.trans (htrh1.trans htrhL))
                          (hscr2.trans (hscr1.trans hscrL)) (by simp [(hfail2 hok2).2])
                          (fun _ => hfail2 hok2) hm2
                    · have hok1 : ok1 = false := by
                        cases ok1 <;> first | rfl | contradiction | exact absurd rfl ‹_›
                      c0_hsteps!
                      exact hQ false s1 m1 hinv1 (hcv1.trans hcvL) (hfl1.trans hflL)
                        (htmk1.trans htmkL) (htrh1.trans htrhL) (hscr1.trans hscrL)
                        (by simp [(hfail1 hok1).2]) (fun _ => hfail1 hok1) hm1
                  · c0_hsteps!
                    exact hJN () ml ⟨sL, hinvL, hcvL, hflL, hrpL, htmkL, htrhL, hscrL, hmL⟩
              · c0_hsteps!
                exact hJex () ml ⟨sL, hinvL, hcvL, hflL, htmkL, htrhL, hscrL, hmL⟩
            · c0_hsteps!
              exact hJex () ml ⟨sL, hinvL, hcvL, hflL, htmkL, htrhL, hscrL, hmL⟩
          · c0_hsteps!
            exact hJex () ml ⟨sL, hinvL, hcvL, hflL, htmkL, htrhL, hscrL, hmL⟩
    · -- `els_fold` returned `false`
      have hokf : okF = false := by
        cases okF <;> first | rfl | contradiction | exact absurd rfl ‹_›
      c0_hsteps!
      exact hQ false sF mF hinvF hcvF hflF htmkF htrhF hscrF
        (by simp [(hfailF hokf).2]) (fun _ => hfailF hokf) hmF

end LeanQbe.T.Examples.Kissat.FullM6Sweep
