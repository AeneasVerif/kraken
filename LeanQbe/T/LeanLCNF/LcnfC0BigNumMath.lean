module

public import LeanQbe.T.Logic.Arith
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Logic.Rules
import all Kraken.Mem
import all Kraken.Separation

/-!
# Algebraic, Bitwise & Separation-Logic Lemmas for Pure C0 `BigNum` (`Milestone R1`)

Pure mathematical and separation-logic building blocks shared across `LcnfC0BigNumSpec` and
`LcnfC0BigNumProof*`:
1. `limbsVal` / `trimLenLoop` / canonical `getLast` lemmas.
2. Lexicographic limb comparison (`cmpLimbsFixed`, `cmpLimbs`) vs `<` / `=` / `>` on `limbsVal`.
3. Symbolic `2^64`-factored carry/borrow/MAC identities (never expanding `2^(64*k)` in `omega`).
4. `testBit` characterization of `limbsVal`, bitwise ops (`and`/`or`/`xor`), shifts, `log2`/`clz`.
5. Bitwise restoring division step & `pow`/`gcd`/signed `Int` (`ediv`, `emod`, `tdiv`, `tmod`)
algebra.
6. `array64` / `bn_region_to_array64` / `intSmallEnc` helpers.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

/-! ## 1. `limbsVal` and `trimLenLoop` -/

theorem limbsVal_singleton (x : BitVec 64) : limbsVal [x] = x.toNat := by
  simp [limbsVal]

theorem limbsVal_snoc (xs : List (BitVec 64)) (x : BitVec 64) :
    limbsVal (xs ++ [x]) = limbsVal xs + 2 ^ (64 * xs.length) * x.toNat := by
  rw [limbsVal_append, limbsVal_singleton]

theorem limbsVal_replicate_zero (k : Nat) :
    limbsVal (List.replicate k (0#64)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, limbsVal_cons, ih]

theorem limbsVal_take_zero {xs : List (BitVec 64)} :
    limbsVal (xs.take 0) = 0 := rfl

theorem list_take_succ_append {xs : List (BitVec 64)} {i : Nat} (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  rfl

theorem limbsVal_take_succ {xs : List (BitVec 64)} {i : Nat} (hi : i < xs.length) :
    limbsVal (xs.take (i + 1)) = limbsVal (xs.take i) + 2 ^ (64 * i) * xs[i].toNat := by
  rw [list_take_succ_append hi, limbsVal_snoc, List.length_take_of_le (Nat.le_of_lt hi)]

theorem limbsVal_take_lt_pow (xs : List (BitVec 64)) (n : Nat) :
    limbsVal (xs.take n) < 2 ^ (64 * n) := by
  have h := limbsVal_lt_pow (xs.take n)
  have hle : (xs.take n).length ≤ n := List.length_take_le n xs
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 64 hle))

theorem bv64_toNat_pos_of_ne {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat :=
  Nat.pos_of_ne_zero (fun h0 => h (BitVec.eq_of_toNat_eq h0))

theorem bv64_ne_of_toNat_ne {x : BitVec 64} (h : x.toNat ≠ 0) : x ≠ 0#64 :=
  fun hx => h (by simp [hx])

theorem list_getLast!_eq_getLast {α : Type} [Inhabited α] (xs : List α) (h : xs ≠ []) :
    xs.getLast! = xs.getLast h := by
  cases xs with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem limbsVal_zero_iff : ∀ {xs : List (BitVec 64)},
    limbsVal xs = 0 ↔ ∀ x ∈ xs, x = 0#64
  | [] => by simp
  | x :: xs => by
    rw [limbsVal_cons]
    constructor
    · intro h
      have hx0 : x.toNat = 0 := by omega
      have hxs0 : limbsVal xs = 0 := by
        by_cases hne : limbsVal xs = 0
        · exact hne
        · have hpos : 2 ^ 64 ≤ 2 ^ 64 * limbsVal xs :=
          Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
          omega
      have hx : x = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hx
      · exact (limbsVal_zero_iff.mp hxs0) y hy'
    · intro h
      have hx : x = 0#64 := h x List.mem_cons_self
      have hxs : limbsVal xs = 0 := limbsVal_zero_iff.mpr fun y hy =>
        h y (List.mem_cons_of_mem _ hy)
      rw [hx, hxs]
      rfl

/-- Pure mirror of `bn_trim(buf, n)` scanning downward from `n`. -/
@[expose] def trimLenLoop (xs : List (BitVec 64)) : Nat → Nat
  | 0 => 0
  | k + 1 => if xs[k]! == 0#64 then trimLenLoop xs k else k + 1

theorem trimLenLoop_le (xs : List (BitVec 64)) : ∀ n, trimLenLoop xs n ≤ n
  | 0 => Nat.le_refl 0
  | k + 1 => by
    unfold trimLenLoop
    split
    · exact Nat.le_trans (trimLenLoop_le xs k) (Nat.le_succ k)
    · exact Nat.le_refl _

theorem trimLenLoop_nonzero (xs : List (BitVec 64)) : ∀ n,
    0 < trimLenLoop xs n → xs[trimLenLoop xs n - 1]! ≠ 0#64
  | 0, h => by simp [trimLenLoop] at h
  | k + 1, h => by
    unfold trimLenLoop at h ⊢
    by_cases heq : (xs[k]! == 0#64) = true
    · simp only [heq, ↓reduceIte] at h ⊢
      exact trimLenLoop_nonzero xs k h
    · simp only [heq, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
      intro h0
      exact heq (beq_iff_eq.mpr h0)

theorem trimLenLoop_upper_zero (xs : List (BitVec 64)) : ∀ n i,
    trimLenLoop xs n ≤ i → i < n → xs[i]! = 0#64
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, h1, h2 => by
    unfold trimLenLoop at h1
    split at h1
    · rename_i heq
      simp only [beq_iff_eq] at heq
      by_cases hik : i = k
      · subst hik; exact heq
      · exact trimLenLoop_upper_zero xs k i h1 (by omega)
    · omega

theorem limbsVal_trimLenLoop (xs : List (BitVec 64)) : ∀ n, n ≤ xs.length →
    limbsVal (xs.take (trimLenLoop xs n)) = limbsVal (xs.take n)
  | 0, _ => rfl
  | k + 1, hk => by
    unfold trimLenLoop
    split
    · rename_i heq
      simp only [beq_iff_eq] at heq
      have hhk : k < xs.length := by omega
      have ih := limbsVal_trimLenLoop xs k (by omega)
      rw [ih, limbsVal_take_succ hhk]
      have hxk : xs[k] = 0#64 := by simpa [getElem!_pos xs k hhk] using heq
      simp [hxk]
    · rfl

theorem trimLenLoop_eq_zero_iff (xs : List (BitVec 64)) : ∀ n, n ≤ xs.length →
    (trimLenLoop xs n = 0 ↔ limbsVal (xs.take n) = 0)
  | 0, _ => by simp [trimLenLoop]
  | k + 1, hk => by
    have hhk : k < xs.length := by omega
    rw [limbsVal_take_succ hhk]
    unfold trimLenLoop
    split
    · rename_i heq
      simp only [beq_iff_eq] at heq
      have hxk : xs[k] = 0#64 := by simpa [getElem!_pos xs k hhk] using heq
      simp [hxk, trimLenLoop_eq_zero_iff xs k (by omega)]
    · rename_i hne
      simp only [beq_iff_eq] at hne
      have hxk : xs[k] ≠ 0#64 := by simpa [getElem!_pos xs k hhk] using hne
      have hpos : 0 < xs[k].toNat := bv64_toNat_pos_of_ne hxk
      have hpow : 0 < 2 ^ (64 * k) := Nat.pow_pos (by decide)
      have hmul : 0 < 2 ^ (64 * k) * xs[k].toNat := Nat.mul_pos hpow hpos
      constructor
      · intro h; omega
      · intro h; omega

theorem trimLenLoop_idem (xs : List (BitVec 64)) (n : Nat) :
    trimLenLoop xs (trimLenLoop xs n) = trimLenLoop xs n := by
  cases h : trimLenLoop xs n with
  | zero => rfl
  | succ m =>
    have hnz := trimLenLoop_nonzero xs n (by omega)
    rw [h] at hnz
    unfold trimLenLoop
    split
    · rename_i hc; exact absurd (by simpa [beq_iff_eq] using hc) (by simpa using hnz)
    · rfl

theorem getLast_take_ne_zero (xs : List (BitVec 64)) (n : Nat)
    (hpos : 0 < trimLenLoop xs n) (hn : n ≤ xs.length) :
    (xs.take (trimLenLoop xs n)).getLast! ≠ 0#64 := by
  have hle : trimLenLoop xs n ≤ xs.length := Nat.le_trans (trimLenLoop_le xs n) hn
  have hlen : (xs.take (trimLenLoop xs n)).length = trimLenLoop xs n := List.length_take_of_le hle
  have hne_nil : xs.take (trimLenLoop xs n) ≠ [] := by
    intro hnil; rw [hnil] at hlen; simp at hlen; omega
  rw [list_getLast!_eq_getLast _ hne_nil, List.getLast_eq_getElem]
  rw [List.getElem_take]
  simpa [hlen,
    getElem!_pos xs (trimLenLoop xs n - 1) (by omega)] using trimLenLoop_nonzero xs n hpos

theorem limbsVal_ge_pow_of_nonzero_last {xs : List (BitVec 64)} (hne : xs ≠ [])
    (hlast : xs.getLast hne ≠ 0#64) :
    2 ^ (64 * (xs.length - 1)) ≤ limbsVal xs := by
  have hlen_pos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hsplit : xs = xs.take (xs.length - 1) ++ [xs.getLast hne] := by
    rw [List.getLast_eq_getElem]
    have h1 := list_take_succ_append (xs := xs) (i := xs.length - 1) (by omega)
    rw [Nat.sub_add_cancel hlen_pos, List.take_length] at h1
    exact h1
  have hlen : (xs.take (xs.length - 1)).length = xs.length - 1 :=
    List.length_take_of_le (Nat.sub_le _ _)
  have hval : limbsVal xs = limbsVal (xs.take (xs.length - 1)) +
      2 ^ (64 * (xs.length - 1)) * (xs.getLast hne).toNat := by
    conv => lhs; rw [hsplit]
    rw [limbsVal_snoc, hlen]
  have hpos : 1 ≤ (xs.getLast hne).toNat := bv64_toNat_pos_of_ne hlast
  have hmul := Nat.mul_le_mul_left (2 ^ (64 * (xs.length - 1))) hpos
  rw [Nat.mul_one] at hmul
  rw [hval]
  exact Nat.le_trans hmul (Nat.le_add_left _ _)

/-! ## 2. Lexicographic Limb Comparison -/

/-- Pure mirror of `bn_cmp_fixed(a, b, n)`. -/
@[expose] def cmpLimbsFixed (a b : List (BitVec 64)) : Nat → Int
  | 0 => 0
  | k + 1 =>
    if a[k]! < b[k]! then -1
    else if b[k]! < a[k]! then 1
    else cmpLimbsFixed a b k

theorem cmpLimbsFixed_spec (a b : List (BitVec 64)) : ∀ n,
    n ≤ a.length → n ≤ b.length →
    (cmpLimbsFixed a b n = -1 ↔ limbsVal (a.take n) < limbsVal (b.take n)) ∧
    (cmpLimbsFixed a b n = 0 ↔ limbsVal (a.take n) = limbsVal (b.take n)) ∧
    (cmpLimbsFixed a b n = 1 ↔ limbsVal (b.take n) < limbsVal (a.take n))
  | 0, _, _ => by simp [cmpLimbsFixed]
  | k + 1, ha, hb => by
    have hka : k < a.length := by omega
    have hkb : k < b.length := by omega
    have hta : limbsVal (a.take k) < 2 ^ (64 * k) := limbsVal_take_lt_pow a k
    have htb : limbsVal (b.take k) < 2 ^ (64 * k) := limbsVal_take_lt_pow b k
    rw [limbsVal_take_succ hka, limbsVal_take_succ hkb]
    unfold cmpLimbsFixed
    have hae : a[k]! = a[k] := getElem!_pos a k hka
    have hbe : b[k]! = b[k] := getElem!_pos b k hkb
    rw [hae, hbe]
    split
    · rename_i hlt
      have hnat : a[k].toNat < b[k].toNat := hlt
      have hpow : limbsVal (a.take k) + 2 ^ (64 * k) * a[k].toNat <
          limbsVal (b.take k) + 2 ^ (64 * k) * b[k].toNat := by
        have hdiff : 2 ^ (64 * k) * (a[k].toNat + 1) ≤ 2 ^ (64 * k) * b[k].toNat :=
          Nat.mul_le_mul_left _ hnat
        rw [Nat.mul_add, Nat.mul_one] at hdiff
        omega
      refine ⟨by simp [hpow], by simp; omega, by simp; omega⟩
    · rename_i hnlt
      split
      · rename_i hgt
        have hnat : b[k].toNat < a[k].toNat := hgt
        have hpow : limbsVal (b.take k) + 2 ^ (64 * k) * b[k].toNat <
            limbsVal (a.take k) + 2 ^ (64 * k) * a[k].toNat := by
          have hdiff : 2 ^ (64 * k) * (b[k].toNat + 1) ≤ 2 ^ (64 * k) * a[k].toNat :=
            Nat.mul_le_mul_left _ hnat
          rw [Nat.mul_add, Nat.mul_one] at hdiff
          omega
        refine ⟨by simp; omega, by simp; omega, by simp [hpow]⟩
      · rename_i hngt
        have hnot1 : ¬ a[k].toNat < b[k].toNat := hnlt
        have hnot2 : ¬ b[k].toNat < a[k].toNat := hngt
        have heq : a[k].toNat = b[k].toNat := by omega
        rw [heq]
        have ih := cmpLimbsFixed_spec a b k (by omega) (by omega)
        rcases ih with ⟨h1, h2, h3⟩
        refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro hh
        · exact Nat.add_lt_add_right (h1.mp hh) _
        · exact h1.mpr (by omega)
        · rw [h2.mp hh]
        · exact h2.mpr (by omega)
        · exact Nat.add_lt_add_right (h3.mp hh) _
        · exact h3.mpr (by omega)

/-- Pure mirror of `bn_cmp(a, na, b, nb)`. -/
@[expose] def cmpLimbs (a : List (BitVec 64)) (na : Nat) (b : List (BitVec 64)) (nb : Nat) : Int :=
  let ta := trimLenLoop a na
  let tb := trimLenLoop b nb
  if ta < tb then -1
  else if tb < ta then 1
  else cmpLimbsFixed a b ta

theorem cmpLimbs_spec (a : List (BitVec 64)) (na : Nat) (b : List (BitVec 64)) (nb : Nat)
    (ha : na ≤ a.length) (hb : nb ≤ b.length) :
    (cmpLimbs a na b nb = -1 ↔ limbsVal (a.take na) < limbsVal (b.take nb)) ∧
    (cmpLimbs a na b nb = 0 ↔ limbsVal (a.take na) = limbsVal (b.take nb)) ∧
    (cmpLimbs a na b nb = 1 ↔ limbsVal (b.take nb) < limbsVal (a.take na)) := by
  unfold cmpLimbs
  dsimp only
  have hta_le : trimLenLoop a na ≤ a.length := Nat.le_trans (trimLenLoop_le a na) ha
  have htb_le : trimLenLoop b nb ≤ b.length := Nat.le_trans (trimLenLoop_le b nb) hb
  rw [← limbsVal_trimLenLoop a na ha, ← limbsVal_trimLenLoop b nb hb]
  by_cases hlt : trimLenLoop a na < trimLenLoop b nb
  · simp only [hlt, ↓reduceIte]
    have htb_pos : 0 < trimLenLoop b nb := by omega
    have hlast := getLast_take_ne_zero b nb htb_pos hb
    have hlb : 2 ^ (64 * (trimLenLoop b nb - 1)) ≤ limbsVal (b.take (trimLenLoop b nb)) := by
      have hlen : (b.take (trimLenLoop b nb)).length = trimLenLoop b nb :=
        List.length_take_of_le htb_le
      have hne : b.take (trimLenLoop b nb) ≠ [] := by intro he; rw [he] at hlen; simp at hlen; omega
      rw [list_getLast!_eq_getLast _ hne] at hlast
      simpa [hlen] using limbsVal_ge_pow_of_nonzero_last hne hlast
    have hua : limbsVal (a.take (trimLenLoop a na)) < 2 ^ (64 * trimLenLoop a na) :=
      limbsVal_take_lt_pow a _
    have hpow : 2 ^ (64 * trimLenLoop a na) ≤ 2 ^ (64 * (trimLenLoop b nb - 1)) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 64 (by omega))
    have hval : limbsVal (a.take (trimLenLoop a na)) < limbsVal (b.take (trimLenLoop b nb)) :=
      Nat.lt_of_lt_of_le hua (Nat.le_trans hpow hlb)
    refine ⟨by simp [hval], by simp; omega, by simp; omega⟩
  · simp only [hlt, ↓reduceIte]
    by_cases hgt : trimLenLoop b nb < trimLenLoop a na
    · simp only [hgt, ↓reduceIte]
      have hta_pos : 0 < trimLenLoop a na := by omega
      have hlast := getLast_take_ne_zero a na hta_pos ha
      have hla : 2 ^ (64 * (trimLenLoop a na - 1)) ≤ limbsVal (a.take (trimLenLoop a na)) := by
        have hlen : (a.take (trimLenLoop a na)).length = trimLenLoop a na :=
          List.length_take_of_le hta_le
        have hne : a.take (trimLenLoop a na) ≠ [] := by
          intro he; rw [he] at hlen; simp at hlen; omega
        rw [list_getLast!_eq_getLast _ hne] at hlast
        simpa [hlen] using limbsVal_ge_pow_of_nonzero_last hne hlast
      have hub : limbsVal (b.take (trimLenLoop b nb)) < 2 ^ (64 * trimLenLoop b nb) :=
        limbsVal_take_lt_pow b _
      have hpow : 2 ^ (64 * trimLenLoop b nb) ≤ 2 ^ (64 * (trimLenLoop a na - 1)) :=
        Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 64 (by omega))
      have hval : limbsVal (b.take (trimLenLoop b nb)) < limbsVal (a.take (trimLenLoop a na)) :=
        Nat.lt_of_lt_of_le hub (Nat.le_trans hpow hla)
      refine ⟨by simp; omega, by simp; omega, by simp [hval]⟩
    · simp only [hgt, ↓reduceIte]
      have heq : trimLenLoop a na = trimLenLoop b nb := by omega
      rw [← heq] at htb_le
      rw [← heq]
      exact cmpLimbsFixed_spec a b (trimLenLoop a na) hta_le htb_le

/-! ## 3. Symbolic `2^64` Carry / Borrow / MAC Helpers -/

theorem addc64_nat (x y : BitVec 64) (cin : Bool) :
    let sum := x.toNat + y.toNat + (if cin then 1 else 0)
    let s := BitVec.ofNat 64 sum
    let co := decide (2 ^ 64 ≤ sum)
    s.toNat + (if co then 2 ^ 64 else 0) = x.toNat + y.toNat + (if cin then 1 else 0) := by
  dsimp only
  have hx := x.isLt
  have hy := y.isLt
  have hcin : (if cin then 1 else 0) ≤ 1 := by cases cin <;> decide
  rw [BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat + (if cin then 1 else 0)
  · have hlt : (x.toNat + y.toNat + (if cin then 1 else 0)) - 2 ^ 64 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hlt, decide_eq_true h]
    simp only [↓reduceIte]
    exact Nat.sub_add_cancel h
  · have hmod : (x.toNat + y.toNat + (if cin then 1 else 0)) % 2 ^ 64 =
        x.toNat + y.toNat + (if cin then 1 else 0) := Nat.mod_eq_of_lt (by omega)
    rw [hmod, decide_eq_false h]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem subb64_nat (x y : BitVec 64) (bin : Bool) :
    let diff := (2 ^ 64 : Nat) + x.toNat - y.toNat - (if bin then 1 else 0)
    let d := BitVec.ofNat 64 diff
    let bo := decide (x.toNat < y.toNat + (if bin then 1 else 0))
    d.toNat + y.toNat + (if bin then 1 else 0) = x.toNat + (if bo then 2 ^ 64 else 0) := by
  dsimp only
  have hx := x.isLt
  have hy := y.isLt
  have hyb : y.toNat + (if bin then 1 else 0) ≤ 2 ^ 64 := by
    cases bin <;> simp <;> omega
  rw [BitVec.toNat_ofNat]
  by_cases h : x.toNat < y.toNat + (if bin then 1 else 0)
  · have hm : ((2 ^ 64 + x.toNat - y.toNat - (if bin then 1 else 0)) % 2 ^ 64) =
        2 ^ 64 + x.toNat - y.toNat - (if bin then 1 else 0) :=
      Nat.mod_eq_of_lt (by omega)
    rw [hm, decide_eq_true h]
    simp only [↓reduceIte]
    omega
  · have heq : 2 ^ 64 + x.toNat - y.toNat - (if bin then 1 else 0) =
        2 ^ 64 + (x.toNat - y.toNat - (if bin then 1 else 0)) := by omega
    rw [heq, Nat.add_mod_left]
    have hm : (x.toNat - y.toNat - (if bin then 1 else 0)) % 2 ^ 64 =
        x.toNat - y.toNat - (if bin then 1 else 0) := Nat.mod_eq_of_lt (by omega)
    rw [hm, decide_eq_false h]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega

theorem umul128_nat (a b : BitVec 64) :
    let prod := a.toNat * b.toNat
    let lo := BitVec.ofNat 64 prod
    let hi := BitVec.ofNat 64 (prod >>> 64)
    lo.toNat + 2 ^ 64 * hi.toNat = a.toNat * b.toNat := by
  dsimp only
  have ha := a.isLt
  have hb := b.isLt
  have hprod : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by decide
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hhi : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hprod
  rw [Nat.mod_eq_of_lt hhi, Nat.add_comm, Nat.mul_comm]
  exact Nat.div_add_mod' (a.toNat * b.toNat) (2 ^ 64)

theorem mac_step_nat (a b cur carry : BitVec 64) :
    let prod := a.toNat * b.toNat
    let lo := BitVec.ofNat 64 prod
    let hi := BitVec.ofNat 64 (prod >>> 64)
    let sum1 := cur.toNat + lo.toNat
    let s1 := BitVec.ofNat 64 sum1
    let c1 := decide (2 ^ 64 ≤ sum1)
    let sum2 := s1.toNat + carry.toNat
    let s2 := BitVec.ofNat 64 sum2
    let c2 := decide (2 ^ 64 ≤ sum2)
    let carry' := hi + (if c1 then 1#64 else 0#64) + (if c2 then 1#64 else 0#64)
    s2.toNat + 2 ^ 64 * carry'.toNat = cur.toNat + carry.toNat + a.toNat * b.toNat := by
  dsimp only
  have ha := a.isLt; have hb := b.isLt; have hc := cur.isLt; have hcr := carry.isLt
  have hmul := umul128_nat a b
  dsimp only at hmul
  have hc1 := addc64_nat cur (BitVec.ofNat 64 (a.toNat * b.toNat)) false
  dsimp only at hc1
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc1
  have hc2 :=
    addc64_nat (BitVec.ofNat 64 (cur.toNat +
      (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat)) carry false
  dsimp only at hc2
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc2
  have hprod_le : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hmax : (2 ^ 64 - 1) * (2 ^ 64 - 1) = 2 ^ 128 - 2 * 2 ^ 64 + 1 := by decide
  rw [hmax] at hprod_le
  have hbound : cur.toNat + carry.toNat + a.toNat * b.toNat < 2 ^ 128 := by omega
  let hi := BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)
  let c1 := decide (2 ^ 64 ≤ cur.toNat + (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat)
  let c2 :=
    decide (2 ^ 64 ≤ (BitVec.ofNat 64 (cur.toNat +
      (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat)).toNat + carry.toNat)
  have hsum : (BitVec.ofNat 64 ((BitVec.ofNat 64 (cur.toNat +
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat)).toNat + carry.toNat)).toNat +
      2 ^ 64 * (hi.toNat + (if c1 then 1 else 0) + (if c2 then 1 else 0)) =
      cur.toNat + carry.toNat + a.toNat * b.toNat := by
    dsimp only [hi, c1, c2]
    rw [Nat.mul_add, Nat.mul_add]
    have h1 : 2 ^ 64 * (if decide (2 ^ 64 ≤ cur.toNat +
      (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat) then 1 else 0) =
        if decide (2 ^ 64 ≤ cur.toNat +
          (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat) then 2 ^ 64 else 0 := by
      split <;> simp
    have h2 : 2 ^ 64 * (if decide (2 ^ 64 ≤ (BitVec.ofNat 64 (cur.toNat +
      (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat)).toNat + carry.toNat) then 1 else 0) =
        if decide (2 ^ 64 ≤ (BitVec.ofNat 64 (cur.toNat +
          (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat)).toNat + carry.toNat) then 2 ^ 64 else 0 :=
            by
      split <;> simp
    rw [h1, h2]
    omega
  have hhi_bound : hi.toNat + (if c1 then 1 else 0) + (if c2 then 1 else 0) < 2 ^ 64 := by
    by_cases hlt : hi.toNat + (if c1 then 1 else 0) + (if c2 then 1 else 0) < 2 ^ 64
    · exact hlt
    · have hbig : 2 ^ 128 ≤ 2 ^ 64 * (hi.toNat + (if c1 then 1 else 0) + (if c2 then 1 else 0)) :=
      by
        have : 2 ^ 64 * 2 ^ 64 = 2 ^ 128 := by decide
        calc 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := this.symm
          _ ≤ 2 ^ 64 * (hi.toNat + (if c1 then 1 else 0) + (if c2 then 1 else 0)) :=
            Nat.mul_le_mul_left _ (by omega)
      omega
  have hbv : (hi + (if c1 then 1#64 else 0#64) + (if c2 then 1#64 else 0#64)).toNat =
      hi.toNat + (if c1 then 1 else 0) + (if c2 then 1 else 0) := by
    rw [BitVec.toNat_add, BitVec.toNat_add]
    have h1' : (if c1 then 1#64 else 0#64).toNat = if c1 then 1 else 0 := by cases c1 <;> rfl
    have h2' : (if c2 then 1#64 else 0#64).toNat = if c2 then 1 else 0 := by cases c2 <;> rfl
    rw [h1', h2', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  dsimp only [hi, c1, c2] at hbv hsum
  rw [hbv]
  exact hsum

theorem sub_borrow_false_of_le {outV aV bV k : Nat} {br : Bool}
    (hout : outV < 2 ^ (64 * k)) (hba : bV ≤ aV)
    (heq : outV + bV = aV + (if br then 2 ^ (64 * k) else 0)) :
    br = false ∧ outV = aV - bV := by
  cases br
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at heq
    exact ⟨rfl, by omega⟩
  · simp only [↓reduceIte] at heq; omega

theorem sub_one_borrow_false_of_pos {outV aV k : Nat} {br : Bool}
    (hout : outV < 2 ^ (64 * k)) (hpos : 1 ≤ aV)
    (heq : outV + 1 = aV + (if br then 2 ^ (64 * k) else 0)) :
    br = false ∧ outV = aV - 1 :=
  sub_borrow_false_of_le hout hpos heq

/-! ## 4. `testBit` Characterization, Bitwise, Shifts, and `log2`/`clz` -/

theorem testBit_add_pow64 {x : BitVec 64} {y k : Nat} :
    (x.toNat + 2 ^ 64 * y).testBit k =
      if k < 64 then x.toNat.testBit k else y.testBit (k - 64) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hk : k < 64
  · simp only [hk, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have h64 : 64 = k + (64 - k) := by omega
    have hpow : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k) := by rw [← Nat.pow_add, ← h64]
    have h2 : 2 ^ (64 - k) = 2 * 2 ^ (64 - k - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    rw [hpow, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide))]
    rw [h2, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  · simp only [hk, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hk64 : k = 64 + (k - 64) := by omega
    conv => lhs; rw [hk64, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64)]
    rw [Nat.div_eq_of_lt x.isLt, Nat.zero_add]

theorem limbsVal_testBit (xs : List (BitVec 64)) (k : Nat) :
    (limbsVal xs).testBit k =
      if h : k / 64 < xs.length then xs[k / 64].toNat.testBit (k % 64) else false := by
  induction xs generalizing k with
  | nil => simp [limbsVal]
  | cons x xs ih =>
    rw [limbsVal_cons, testBit_add_pow64]
    by_cases hk : k < 64
    · have hkdiv : k / 64 = 0 := Nat.div_eq_of_lt hk
      have hkmod : k % 64 = k := Nat.mod_eq_of_lt hk
      simp [hk, hkdiv, hkmod]
    · have hkdiv : k / 64 = (k - 64) / 64 + 1 := by omega
      have hkmod : k % 64 = (k - 64) % 64 := by omega
      simp [hk, ih, hkdiv, hkmod]

theorem limbsVal_log2 {xs : List (BitVec 64)} (hne : xs ≠ [])
    (hlast : xs.getLast hne ≠ 0#64) :
    (limbsVal xs).log2 = 64 * xs.length - 1 - (xs.getLast hne).clz.toNat := by
  let hi := xs.getLast hne
  have hlen_pos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hsplit : xs = xs.take (xs.length - 1) ++ [hi] := by
    dsimp only [hi]
    rw [List.getLast_eq_getElem]
    have h1 := list_take_succ_append (xs := xs) (i := xs.length - 1) (by omega)
    rw [Nat.sub_add_cancel hlen_pos, List.take_length] at h1
    exact h1
  have hlen : (xs.take (xs.length - 1)).length = xs.length - 1 :=
    List.length_take_of_le (Nat.sub_le _ _)
  have hval : limbsVal xs = limbsVal (xs.take (xs.length - 1)) +
    2 ^ (64 * (xs.length - 1)) * hi.toNat := by
    conv => lhs; rw [hsplit]
    rw [limbsVal_snoc, hlen]
  have hhi_nz : hi.toNat ≠ 0 := fun h0 => hlast (BitVec.eq_of_toNat_eq h0)
  have hhi_lt64 : hi.toNat.log2 < 64 := by
    rw [Nat.log2_lt hhi_nz]; exact hi.isLt
  have hclz : hi.clz.toNat = 64 - (hi.toNat.log2 + 1) := by
    rw [BitVec.toNat_clz]
    have hne0 : hi ≠ 0 := hlast
    simp only [hne0, ↓reduceIte]
  have hhi_lb : 2 ^ hi.toNat.log2 ≤ hi.toNat := (Nat.le_log2 hhi_nz).mp (Nat.le_refl _)
  have hhi_ub : hi.toNat < 2 ^ (hi.toNat.log2 + 1) := (Nat.log2_lt hhi_nz).mp (Nat.lt_succ_self _)
  have hrem_lt : limbsVal (xs.take (xs.length - 1)) < 2 ^ (64 * (xs.length - 1)) := by
    simpa [hlen] using limbsVal_lt_pow (xs.take (xs.length - 1))
  have hnz_val : limbsVal xs ≠ 0 := by
    have h1 : 1 ≤ hi.toNat := Nat.pos_of_ne_zero hhi_nz
    have h2 : 2 ^ (64 * (xs.length - 1)) ≤ 2 ^ (64 * (xs.length - 1)) * hi.toNat := by
      simpa using Nat.mul_le_mul_left (2 ^ (64 * (xs.length - 1))) h1
    have hpow : 0 < 2 ^ (64 * (xs.length - 1)) := Nat.pow_pos (by decide)
    omega
  let target := 64 * (xs.length - 1) + hi.toNat.log2
  have hlb : 2 ^ target ≤ limbsVal xs := by
    rw [hval, Nat.pow_add]
    have hmul : 2 ^ (64 * (xs.length - 1)) * 2 ^ hi.toNat.log2 ≤
        2 ^ (64 * (xs.length - 1)) * hi.toNat := Nat.mul_le_mul_left _ hhi_lb
    omega
  have hub : limbsVal xs < 2 ^ (target + 1) := by
    rw [hval, show target + 1 = 64 * (xs.length - 1) + (hi.toNat.log2 + 1) by omega, Nat.pow_add]
    have hmul : 2 ^ (64 * (xs.length - 1)) * (hi.toNat + 1) ≤
        2 ^ (64 * (xs.length - 1)) * 2 ^ (hi.toNat.log2 + 1) := Nat.mul_le_mul_left _ hhi_ub
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hlog : (limbsVal xs).log2 = target := by
    have hge := (Nat.le_log2 hnz_val).mpr hlb
    have hlt := (Nat.log2_lt hnz_val).mpr hub
    omega
  rw [hlog, hclz]
  omega

theorem ofNat64_mask_bits (v : BitVec 64) (b : BitVec 64) :
    (if b == 0#64 then 0#64
     else if 64#64 ≤ b then v
     else v &&& ((1#64 <<< b.toNat) - 1#64)) =
    if b.toNat = 0 then 0#64
    else if 64 ≤ b.toNat then v
    else BitVec.ofNat 64 (v.toNat % 2 ^ b.toNat) := by
  by_cases hb0 : b = 0#64
  · simp [hb0]
  · have hb0_n : b.toNat ≠ 0 := fun h => hb0 (BitVec.eq_of_toNat_eq h)
    by_cases h64 : 64 ≤ b.toNat
    · have hle : 64#64 ≤ b := by rw [BitVec.le_def]; exact h64
      simp [hb0, hb0_n, h64, hle]
    · have hle : ¬ (64#64 ≤ b) := by rw [BitVec.le_def]; exact h64
      simp [hb0, hb0_n, h64, hle]
      apply BitVec.eq_of_toNat_eq
      have hpow_lt : 2 ^ b.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
      have hshl : (1#64 <<< b.toNat).toNat = 2 ^ b.toNat := by
        rw [BitVec.toNat_shiftLeft]
        have hone : (1#64).toNat = 1 := rfl
        rw [hone, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hpow_lt]
      have hmask : ((1#64 <<< b.toNat) - 1#64).toNat = 2 ^ b.toNat - 1 := by
        rw [BitVec.toNat_sub, hshl]
        have hpos : 1 ≤ 2 ^ b.toNat := Nat.pow_pos (by decide)
        change (2 ^ 64 - 1 + 2 ^ b.toNat) % 2 ^ 64 = 2 ^ b.toNat - 1
        rw [show 2 ^ 64 - 1 + 2 ^ b.toNat = 2 ^ 64 + (2 ^ b.toNat - 1) by omega]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hland : (v &&& ((1#64 <<< b.toNat) - 1#64)).toNat = v.toNat &&& (2 ^ b.toNat - 1) := by
        rw [BitVec.toNat_and, hmask]
      rw [hland, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.pow_pos (by decide))) hpow_lt)]

/-! ## 5. Division Step, Exponentiation, GCD, and Signed `Int` Arithmetic -/

theorem divmod_bit_step {aVal qVal bVal rVal pos : Nat}
    (hr : rVal < bVal)
    (hinv : aVal >>> (pos + 1) = (qVal >>> (pos + 1)) * bVal + rVal) :
    let inBit := if aVal.testBit pos then 1 else 0
    let r' := 2 * rVal + inBit
    let qBit := decide (bVal ≤ r')
    let rNext := if qBit then r' - bVal else r'
    let qNext := if qBit then qVal ||| (1 <<< pos) else qVal
    qNext >>> pos = 2 * (qVal >>> (pos + 1)) + (if qBit then 1 else 0) →
    aVal >>> pos = (qNext >>> pos) * bVal + rNext ∧ rNext < bVal := by
  intro inBit r' qBit rNext qNext hq
  have ha : aVal >>> pos = 2 * (aVal >>> (pos + 1)) + inBit := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight]
    cases i with
    | zero =>
      simp only [Nat.add_zero, Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
      have hdiv_mod : (2 * (aVal >>> (pos + 1)) + inBit) % 2 = inBit % 2 := by omega
      rw [hdiv_mod, ← Nat.testBit_eq_decide_div_mod_eq]
      dsimp only [inBit]
      by_cases hb : aVal.testBit pos = true <;> simp [hb]
    | succ i' =>
      rw [show pos + (i' + 1) = (pos + 1) + i' by omega]
      have hbit : inBit < 2 := by dsimp [inBit]; split <;> decide
      have hdiv2 : (2 * (aVal >>> (pos + 1)) + inBit) / 2 = aVal >>> (pos + 1) := by omega
      conv => rhs; rw [Nat.testBit_eq_decide_div_mod_eq]
      have hp : (2 : Nat) ^ (i' + 1) = 2 * 2 ^ i' := by rw [Nat.pow_succ']
      rw [hp, ← Nat.div_div_eq_div_mul, hdiv2, ← Nat.testBit_eq_decide_div_mod_eq,
        Nat.testBit_shiftRight]
  rw [hq]
  by_cases hge : bVal ≤ r'
  · have hqbit : qBit = true := decide_eq_true hge
    dsimp only [rNext, r'] at hge ⊢
    simp only [hqbit, ↓reduceIte]
    rw [ha, hinv]
    have hleft : (2 * (qVal >>> (pos + 1)) + 1) * bVal + (2 * rVal + inBit - bVal) =
        2 * ((qVal >>> (pos + 1)) * bVal + rVal) + inBit := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_assoc]; omega
    have hin : inBit ≤ 1 := by dsimp [inBit]; split <;> decide
    exact ⟨hleft.symm, by clear hinv ha hq; omega⟩
  · have hqbit : qBit = false := decide_eq_false hge
    dsimp only [rNext, r'] at hge ⊢
    simp only [hqbit, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [ha, hinv]
    have hleft : 2 * (qVal >>> (pos + 1)) * bVal + (2 * rVal + inBit) =
        2 * ((qVal >>> (pos + 1)) * bVal + rVal) + inBit := by
      rw [Nat.mul_add, Nat.mul_assoc]; omega
    exact ⟨hleft.symm, by omega⟩

theorem pow_limbs_bound {aVal origExp resVal baseVal exp slice : Nat}
    (ha : 2 ≤ aVal) (hexp : 1 ≤ exp) (hslice : 2 ≤ slice)
    (hinv : resVal * baseVal ^ exp = aVal ^ origExp)
    (hcap : aVal ^ origExp < 2 ^ (64 * (slice - 2)))
    {rn bn : Nat}
    (hrn : rn = 0 ∨ 2 ^ (64 * (rn - 1)) ≤ resVal)
    (hbn : bn = 0 ∨ 2 ^ (64 * (bn - 1)) ≤ baseVal) :
    rn + bn < slice ∧ (2 ≤ exp → bn + bn < slice) := by
  have ha_pos : 1 ≤ aVal ^ origExp := Nat.one_le_pow _ _ (by omega)
  have hb_ge1 : 1 ≤ baseVal := by
    by_cases hb0 : baseVal = 0
    · rw [hb0, Nat.zero_pow (by omega), Nat.mul_zero] at hinv; omega
    · exact Nat.pos_of_ne_zero hb0
  have hr_ge1 : 1 ≤ resVal := by
    by_cases hr0 : resVal = 0
    · rw [hr0, Nat.zero_mul] at hinv; omega
    · exact Nat.pos_of_ne_zero hr0
  have hpow_ge : baseVal ≤ baseVal ^ exp := Nat.le_self_pow (by omega) _
  have hprod_le : resVal * baseVal ≤ aVal ^ origExp := by
    calc resVal * baseVal ≤ resVal * baseVal ^ exp := Nat.mul_le_mul_left _ hpow_ge
      _ = aVal ^ origExp := hinv
  have hrn_bn : rn + bn < slice := by
    rcases hrn with rfl | hrn
    · rcases hbn with rfl | hbn
      · omega
      · have h1 : 2 ^ (64 * (bn - 1)) < 2 ^ (64 * (slice - 2)) :=
          Nat.lt_of_le_of_lt (Nat.le_trans hbn (Nat.le_trans (Nat.le_mul_of_pos_left _ hr_ge1)
          hprod_le)) hcap
        have hexp_lt : 64 * (bn - 1) < 64 * (slice - 2) :=
          (Nat.pow_lt_pow_iff_right (by decide)).mp h1
        omega
    · rcases hbn with rfl | hbn
      · have h1 : 2 ^ (64 * (rn - 1)) < 2 ^ (64 * (slice - 2)) :=
          Nat.lt_of_le_of_lt (Nat.le_trans hrn (Nat.le_trans (Nat.le_mul_of_pos_right _ hb_ge1)
          hprod_le)) hcap
        have hexp_lt : 64 * (rn - 1) < 64 * (slice - 2) :=
          (Nat.pow_lt_pow_iff_right (by decide)).mp h1
        omega
      · have hmul : 2 ^ (64 * (rn - 1) + 64 * (bn - 1)) ≤ resVal * baseVal := by
          rw [Nat.pow_add]; exact Nat.mul_le_mul hrn hbn
        have hlt : 2 ^ (64 * (rn - 1) + 64 * (bn - 1)) < 2 ^ (64 * (slice - 2)) :=
          Nat.lt_of_le_of_lt (Nat.le_trans hmul hprod_le) hcap
        have hexp_lt : 64 * (rn - 1) + 64 * (bn - 1) < 64 * (slice - 2) :=
          (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
        omega
  refine ⟨hrn_bn, fun h2 => ?_⟩
  rcases hbn with rfl | hbn
  · omega
  · have hsq_le : baseVal * baseVal ≤ aVal ^ origExp := by
      have : baseVal * baseVal = baseVal ^ 2 := (Nat.pow_two baseVal).symm
      calc baseVal * baseVal = baseVal ^ 2 := this
        _ ≤ baseVal ^ exp := Nat.pow_le_pow_right hb_ge1 h2
        _ ≤ resVal * baseVal ^ exp := Nat.le_mul_of_pos_left _ hr_ge1
        _ = aVal ^ origExp := hinv
    have hlt : 2 ^ (64 * (bn - 1) + 64 * (bn - 1)) < 2 ^ (64 * (slice - 2)) := by
      rw [Nat.pow_add]
      exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul hbn hbn) hsq_le) hcap
    have hexp_lt : 64 * (bn - 1) + 64 * (bn - 1) < 64 * (slice - 2) :=
      (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
    omega

theorem int_signed_val_eq (neg : Bool) (mag : Nat) :
    let z : Int := if neg then -(mag : Int) else (mag : Int)
    z.natAbs = mag ∧ (mag = 0 → z = 0) := by
  cases neg <;> simp

private theorem ediv_emod_pos_neg {a B : Int} (hB : 0 < B) (q r : Int)
    (hid : r + B * q = a) (hlo : 0 ≤ r) (hhi : r < B) :
    a / B = q ∧ a % B = r ∧ a / (-B) = -q ∧ a % (-B) = r := by
  have hpos := (Int.ediv_emod_unique hB).mpr ⟨hid, hlo, hhi⟩
  refine ⟨hpos.1, hpos.2, ?_, ?_⟩
  · rw [Int.ediv_neg, hpos.1]
  · rw [Int.emod_neg, hpos.2]

theorem int_ediv_emod_of_natAbs {a b : Int} (hb : b ≠ 0) :
    let A := a.natAbs
    let B := b.natAbs
    let Q := A / B
    let R := A % B
    (a < 0 → R = 0 → a / b = if (a < 0) == (b < 0) then (Q : Int) else -(Q : Int)) ∧
    (a < 0 → R ≠ 0 →
      a / b = if (a < 0) == (b < 0) then ((Q + 1 : Nat) : Int) else -((Q + 1 : Nat) : Int)) ∧
    (0 ≤ a → a / b = if (a < 0) == (b < 0) then (Q : Int) else -(Q : Int)) ∧
    (0 ≤ a → a % b = (R : Int)) ∧
    (a < 0 → R = 0 → a % b = 0) ∧
    (a < 0 → R ≠ 0 → a % b = ((B - R : Nat) : Int)) := by
  dsimp only
  have hB_pos : (0 : Int) < (b.natAbs : Int) := Int.natCast_pos.mpr (Int.natAbs_pos.mpr hb)
  have hmod_lt : a.natAbs % b.natAbs < b.natAbs := Nat.mod_lt _ (Int.natAbs_pos.mpr hb)
  have hdiv_mod : b.natAbs * (a.natAbs / b.natAbs) + a.natAbs % b.natAbs = a.natAbs :=
    Nat.div_add_mod a.natAbs b.natAbs
  have hdiv_modZ : (b.natAbs : Int) * ((a.natAbs / b.natAbs : Nat) : Int) +
      ((a.natAbs % b.natAbs : Nat) : Int) = (a.natAbs : Int) := by
    exact_mod_cast hdiv_mod
  have ed_nn : 0 ≤ a → a / (b.natAbs : Int) = ((a.natAbs / b.natAbs : Nat) : Int) ∧
      a % (b.natAbs : Int) = ((a.natAbs % b.natAbs : Nat) : Int) ∧
      a / (-(b.natAbs : Int)) = -((a.natAbs / b.natAbs : Nat) : Int) ∧
      a % (-(b.natAbs : Int)) = ((a.natAbs % b.natAbs : Nat) : Int) := by
    intro ha
    exact ediv_emod_pos_neg hB_pos _ _ (by rw [Int.add_comm, hdiv_modZ]; omega)
      (Int.natCast_nonneg _) (by omega)
  have ed_neg0 : a < 0 → a.natAbs % b.natAbs = 0 →
      a / (b.natAbs : Int) = -((a.natAbs / b.natAbs : Nat) : Int) ∧
      a % (b.natAbs : Int) = 0 ∧
      a / (-(b.natAbs : Int)) = ((a.natAbs / b.natAbs : Nat) : Int) ∧
      a % (-(b.natAbs : Int)) = 0 := by
    intro ha hr
    have hid : (0 : Int) + (b.natAbs : Int) * -((a.natAbs / b.natAbs : Nat) : Int) = a := by
      rw [Int.zero_add, Int.mul_neg]; omega
    simpa [Int.neg_neg] using ediv_emod_pos_neg hB_pos _ _ hid (by decide) hB_pos
  have ed_neg1 : a < 0 → a.natAbs % b.natAbs ≠ 0 →
      a / (b.natAbs : Int) = -((a.natAbs / b.natAbs + 1 : Nat) : Int) ∧
      a % (b.natAbs : Int) = ((b.natAbs - a.natAbs % b.natAbs : Nat) : Int) ∧
      a / (-(b.natAbs : Int)) = ((a.natAbs / b.natAbs + 1 : Nat) : Int) ∧
      a % (-(b.natAbs : Int)) = ((b.natAbs - a.natAbs % b.natAbs : Nat) : Int) := by
    intro ha hr
    have hmul : (b.natAbs : Int) * -((a.natAbs / b.natAbs + 1 : Nat) : Int) =
        -((b.natAbs : Int) * ((a.natAbs / b.natAbs : Nat) : Int)) - (b.natAbs : Int) := by
      rw [Int.mul_neg, Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one]; omega
    have hid : ((b.natAbs - a.natAbs % b.natAbs : Nat) : Int) +
        (b.natAbs : Int) * -((a.natAbs / b.natAbs + 1 : Nat) : Int) = a := by
      rw [hmul]; omega
    simpa [Int.neg_neg] using ediv_emod_pos_neg hB_pos _ _ hid (Int.natCast_nonneg _) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ha hr
    rcases ed_neg0 ha hr with ⟨h1, _, h3, _⟩
    by_cases hbn : b < 0 <;> simp [ha, hbn]
    · rw [show b = -(b.natAbs : Int) by omega, show (-(b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h3
    · rw [show b = (b.natAbs : Int) by omega, show ((b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h1
  · intro ha hr
    rcases ed_neg1 ha hr with ⟨h1, _, h3, _⟩
    by_cases hbn : b < 0 <;> simp [ha, hbn]
    · rw [show b = -(b.natAbs : Int) by omega, show (-(b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h3
    · rw [show b = (b.natAbs : Int) by omega, show ((b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h1
  · intro ha
    rcases ed_nn ha with ⟨h1, _, h3, _⟩
    have hna : ¬ a < 0 := by omega
    by_cases hbn : b < 0 <;> simp [hna, hbn]
    · rw [show b = -(b.natAbs : Int) by omega, show (-(b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h3
    · rw [show b = (b.natAbs : Int) by omega, show ((b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h1
  · intro ha
    rcases ed_nn ha with ⟨_, h2, _, h4⟩
    by_cases hbn : b < 0
    · rw [show b = -(b.natAbs : Int) by omega, show (-(b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h4
    · rw [show b = (b.natAbs : Int) by omega, show ((b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h2
  · intro ha hr
    rcases ed_neg0 ha hr with ⟨_, h2, _, h4⟩
    by_cases hbn : b < 0
    · rw [show b = -(b.natAbs : Int) by omega]; exact h4
    · rw [show b = (b.natAbs : Int) by omega]; exact h2
  · intro ha hr
    rcases ed_neg1 ha hr with ⟨_, h2, _, h4⟩
    by_cases hbn : b < 0
    · rw [show b = -(b.natAbs : Int) by omega, show (-(b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h4
    · rw [show b = (b.natAbs : Int) by omega, show ((b.natAbs : Int)).natAbs = b.natAbs by simp]
      simpa using h2

theorem int_tdiv_tmod_of_natAbs (a b : Int) :
    let Q := a.natAbs / b.natAbs
    let R := a.natAbs % b.natAbs
    a.tdiv b = (if Q = 0 then 0 else if (a < 0) == (b < 0) then (Q : Int) else -(Q : Int)) ∧
    a.tmod b = (if R = 0 then 0 else if a < 0 then -(R : Int) else (R : Int)) := by
  dsimp only
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      cases n with
      | zero =>
        simp only [Int.tdiv, Int.tmod, Int.ofNat_eq_natCast, Int.natAbs_natCast, Nat.div_zero,
          Nat.mod_zero]
        have hnn : ¬ ((m : Int) < 0) := by omega
        by_cases hm : m = 0 <;> simp [hm, hnn]
      | succ n =>
        simp only [Int.tdiv, Int.tmod, Int.ofNat_eq_natCast, Int.natAbs_natCast]
        have h1 : ¬ ((m : Int) < 0) := by omega
        have h2 : ¬ ((Nat.succ n : Int) < 0) := by omega
        simp only [h1, h2, decide_false, beq_self_eq_true, ↓reduceIte]
        constructor
        · by_cases hq : m / Nat.succ n = 0
          · simp [hq]
          · simp [hq]
        · by_cases hr : m % Nat.succ n = 0
          · simp [hr]
          · simp [hr]
    | negSucc n =>
      simp only [Int.tdiv, Int.tmod, Int.ofNat_eq_natCast, Int.natAbs_natCast, Int.natAbs_negSucc]
      have h1 : ¬ ((m : Int) < 0) := by omega
      have h2 : Int.negSucc n < 0 := Int.negSucc_lt_zero n
      simp only [h1, h2, decide_false, decide_true, Bool.false_beq, ↓reduceIte]
      constructor
      · by_cases hq : m / (n + 1) = 0 <;> simp [hq]
      · by_cases hr : m % (n + 1) = 0 <;> simp [hr]
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n with
      | zero => simp [Int.tdiv, Int.tmod]
      | succ n =>
        simp only [Int.tdiv, Int.tmod, Int.ofNat_eq_natCast, Int.natAbs_natCast, Int.natAbs_negSucc]
        have h1 : Int.negSucc m < 0 := Int.negSucc_lt_zero m
        have h2 : ¬ ((Nat.succ n : Int) < 0) := by omega
        simp only [h1, h2, decide_true, decide_false, Bool.true_beq, ↓reduceIte]
        constructor
        · by_cases hq : (m + 1) / Nat.succ n = 0 <;> simp [hq]
        · by_cases hr : (m + 1) % Nat.succ n = 0 <;> simp [hr]
    | negSucc n =>
      simp only [Int.tdiv, Int.tmod, Int.natAbs_negSucc]
      have h1 : Int.negSucc m < 0 := Int.negSucc_lt_zero m
      have h2 : Int.negSucc n < 0 := Int.negSucc_lt_zero n
      simp only [h1, h2, decide_true, beq_self_eq_true, ↓reduceIte]
      constructor
      · by_cases hq : (m + 1) / (n + 1) = 0 <;> simp [hq]
      · by_cases hr : (m + 1) % (n + 1) = 0 <;> simp [hr]

/-! ## 6. Separation-Logic `array64`, `region`, and `intSmallEnc` Helpers -/

theorem bn_region_to_array64 {a : BitVec 64} (k : Nat) (hk : 8 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (8 * k) f) : ∃ xs : List (BitVec 64), xs.length = k ∧ array64 a xs f := by
  obtain ⟨ws, hlen, hwa⟩ := region_to_word8Array k hk hf
  rw [← array64_eq_word8Array] at hwa
  exact ⟨ws, hlen, hwa⟩

theorem array64_to_region_len {a : BitVec 64} (xs : List (BitVec 64))
    (h : 8 * xs.length ≤ 2 ^ 64) {f : Mem 64} (hf : array64 a xs f) :
    region a (8 * xs.length) f := by
  rw [array64_eq_word8Array] at hf
  exact word8Array_to_region h hf

theorem intSmallEnc_toInt {z : Int} (hlo : -(2 ^ 62 : Int) ≤ z) (hhi : z < (2 ^ 62 : Int)) :
    let w := BitVec.ofInt 64 (2 * z + 1)
    (w &&& 1#64) = 1#64 ∧ (w.sshiftRight 1).toInt = z := by
  dsimp only
  have hm_eq : (2 * z + 1) % (↑(2 ^ 64 : Nat) : Int) =
      if 0 ≤ 2 * z + 1 then 2 * z + 1 else 2 * z + 1 + (↑(2 ^ 64 : Nat) : Int) := by
    split
    · exact Int.emod_eq_of_lt (by omega) (by omega)
    · have h1 := Int.add_mul_emod_self_right (2 * z + 1) 1 (↑(2 ^ 64 : Nat) : Int)
      rw [Int.one_mul] at h1
      rw [← h1]
      exact Int.emod_eq_of_lt (by omega) (by omega)
  have hmod_eq : (2 * z + 1).bmod (2 ^ 64) = 2 * z + 1 := by
    rw [Int.bmod_def, hm_eq]
    split <;> omega
  have hw : (BitVec.ofInt 64 (2 * z + 1)).toInt = 2 * z + 1 := by
    rw [BitVec.toInt_ofInt]; exact hmod_eq
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofInt]
    change ((((2 * z + 1) % (↑(2 ^ 64 : Nat) : Int)).toNat) &&& 1) = 1
    rw [Nat.and_one_is_mod, hm_eq]
    split
    · rename_i hnn
      have hcast : ((2 * z + 1).toNat : Int) = 2 * z + 1 := Int.toNat_of_nonneg hnn
      have h2 : (((2 * z + 1).toNat : Int) % 2) = 1 := by
        rw [hcast]
        have he : (2 * z + 1) % 2 = (1 + z * 2) % 2 := by rw [Int.add_comm, Int.mul_comm]
        rw [he, Int.add_mul_emod_self_right]
        decide
      exact_mod_cast h2
    · have hnn : 0 ≤ 2 * z + 1 + (↑(2 ^ 64 : Nat) : Int) := by omega
      have hcast : ((2 * z + 1 + (↑(2 ^ 64 : Nat) : Int)).toNat : Int) = 2 * z + 1 +
        (↑(2 ^ 64 : Nat) : Int) :=
        Int.toNat_of_nonneg hnn
      have h2 : (((2 * z + 1 + (↑(2 ^ 64 : Nat) : Int)).toNat : Int) % 2) = 1 := by
        rw [hcast, show (↑(2 ^ 64 : Nat) : Int) = 2 ^ 63 * 2 by decide]
        have he : 2 * z + 1 + 2 ^ 63 * 2 = 1 + (z + 2 ^ 63) * 2 := by rw [Int.add_mul]; omega
        rw [he, Int.add_mul_emod_self_right]
        decide
      exact_mod_cast h2
  · rw [BitVec.toInt_sshiftRight, hw, Int.shiftRight_eq_div_pow, Nat.pow_one]
    exact ((Int.ediv_emod_unique (r := 1) (q := z) (by decide : (0 : Int) < 2)).mpr
      ⟨by omega, by decide, by decide⟩).1

end LeanQbe.T.LeanLCNF
