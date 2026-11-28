/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Canonical `full_learn_clause_m6` Helpers & Post-AC Proof (`WpLearnClausePost`)

Plain `public section` (`@[expose]` ONLY on `S13Tpi`/`s13Lv`/`S13AddClPre`/`S13NrSpec` &
`s13PostAcExpr`, `0` `@[expose]` on theorems/lemmas, `0` `import all`, `<= 100` cols,
every theorem `<= 320`L):
1. Pure permutation/level helpers (`S13Tpi`, `s13_ins_body_wp`,
   `s13_orUsed31_preserves_fullSparseW`).
2. `S13AddClPre`, `S13NrSpec`, `s13_add_call_wp` (using `fullAddClauseSpec`).
3. `s13_learn_clause_post_ac_wp`: post-add-clause assignment (`jumpreasons` when
   `new_ref == 0xFFFFFFFEULL` + `max_lvl > 0`) and `fullEagerSubsumeSpec` call.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Learn

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
open LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
open LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Helpers

/-! ## 1. Permutation, Level Ordering & `used = 31` Helpers -/

@[expose] def S13Tpi (t0 t : List (BitVec 32)) (n : Nat) : Prop :=
  t.length = t0.length ∧ t[0]? = t0[0]? ∧ (t.take n).Perm (t0.take n)

@[expose] def s13Lv (lvl : List (BitVec 32)) (x : BitVec 32) : Nat :=
  (lvl[x.toNat / 2]?.getD 0#32).toNat

theorem s13Tpi_refl (t0 : List (BitVec 32)) (n : Nat) : S13Tpi t0 t0 n :=
  ⟨rfl, rfl, .refl _⟩

private theorem s13_tmp_shift_hole {xs orig : List (BitVec 32)} {sz j : Nat}
    {x prev : BitVec 32} (hlen : xs.length = orig.length) (hsz : sz ≤ orig.length)
    (hj0 : 0 < j) (hjsz : j < sz) (hprev : xs[j - 1]? = some prev)
    (hperm : ((xs.set j x).take sz).Perm (orig.take sz)) :
    (((xs.set j prev).set (j - 1) x).take sz).Perm (orig.take sz) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj0)
  rw [Nat.succ_sub_one] at hprev ⊢
  let A := (xs.set (m + 1) x).take sz; let B := ((xs.set (m + 1) prev).set m x).take sz
  have hAl : A.length = sz := by simp [A, List.length_take, hlen]; omega
  let head := A.take m; let tail := A.drop (m + 2)
  have htk : head.length = m := by simp [head, List.length_take, hAl]; omega
  have hsp : ∀ (C : List (BitVec 32)) (a b : BitVec 32), C.length = sz →
      (∀ k < m, C[k]? = A[k]?) → C[m]? = some a → C[m + 1]? = some b →
      (∀ k, m + 2 ≤ k → C[k]? = A[k]?) → C = head ++ a :: b :: tail := by
    intro C a b hCl hk_lt hk_m hk_j hk_gt; refine List.ext_getElem? fun k => ?_
    by_cases hkm : k < m
    · rw [List.getElem?_append_left (by omega), List.getElem?_take]; simp [hkm, hk_lt k hkm]
    · rw [List.getElem?_append_right (by omega), htk]
      by_cases hk0 : k = m
      · subst hk0; simp [hk_m]
      · by_cases hk1 : k = m + 1
        · subst hk1; simp [hk_j]
        · rw [show k - m = (k - (m + 2)) + 2 by omega]
          simp only [List.getElem?_cons_succ, tail, List.getElem?_drop]
          rw [show m + 2 + (k - (m + 2)) = k by omega]; exact hk_gt k (by omega)
  have hA := hsp A prev x hAl (fun _ _ => rfl)
    (by simp only [A, List.getElem?_take, show m < sz by omega, ↓reduceIte,
          List.getElem?_set_ne (by omega : m + 1 ≠ m)]; exact hprev)
    (by simp only [A, List.getElem?_take, hjsz, ↓reduceIte]
        exact List.getElem?_set_self (by omega))
    fun _ _ => rfl
  have hB := hsp B x prev (by simp [B, List.length_take, hlen]; omega)
    (fun k hk => by
      simp only [A, B, List.getElem?_take, List.getElem?_set_ne (by omega : m ≠ k),
        List.getElem?_set_ne (by omega : m + 1 ≠ k)])
    (by simp only [B, List.getElem?_take, show m < sz by omega, ↓reduceIte]
        exact List.getElem?_set_self (by simp; omega))
    (by simp only [B, List.getElem?_take, hjsz, ↓reduceIte,
          List.getElem?_set_ne (by omega : m ≠ m + 1)]
        exact List.getElem?_set_self (by omega))
    fun k hk => by
      simp only [A, B, List.getElem?_take, List.getElem?_set_ne (by omega : m ≠ k),
        List.getElem?_set_ne (by omega : m + 1 ≠ k)]
  have hswap : B.Perm A := by
    rw [hA, hB]; exact List.Perm.append_left head (List.Perm.swap prev x tail)
  exact hswap.trans hperm

theorem s13Tpi_lt {t0 t : List (BitVec 32)} {n B : Nat} (h : S13Tpi t0 t n)
    (hn : n ≤ t0.length) (hlt : ∀ k < n, (t0[k]?.getD 0#32).toNat < B) :
    ∀ k < n, (t[k]?.getD 0#32).toNat < B := fun k hk => by
  obtain ⟨hl, _, hperm⟩ := h
  have hm : t[k]'(by omega) ∈ t0.take n := hperm.mem_iff.mp (by
    rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩)
  obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hm
  have hidx_n : idx < n := by rw [List.length_take] at hidx; omega
  have hget := hlt idx hidx_n
  rw [List.getElem_take] at heq
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq]
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget

private theorem s13_perm_pos {A B : List (BitVec 32)} {n j : Nat}
    (hp : (A.take n).Perm (B.take n)) (h0 : A[0]? = B[0]?)
    (hnd : ((B.take n).map fun x => x.toNat / 2).Nodup) (hj1 : 1 ≤ j) (hjn : j < n)
    (hnB : n ≤ B.length) : ∃ k, 1 ≤ k ∧ k < n ∧ A[k]? = B[j]? := by
  have hjB : j < B.length := by omega
  have hmem : B[j] ∈ A.take n := hp.mem_iff.mpr (List.mem_iff_getElem.mpr
    ⟨j, by simp; omega, by simp [List.getElem_take]⟩)
  obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
  simp only [List.length_take] at hk
  rw [List.getElem_take] at hkeq
  refine ⟨k, ?_, by omega, by
    rw [List.getElem?_eq_getElem (by omega), hkeq, List.getElem?_eq_getElem hjB]⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exfalso
    have hB0 : 0 < B.length := by omega
    have hA0 : 0 < A.length := by omega
    have hbeq : B[0] = B[j] := by
      rw [List.getElem?_eq_getElem hA0, List.getElem?_eq_getElem hB0] at h0
      exact (Option.some.inj h0).symm.trans hkeq
    have hlen : ((B.take n).map fun x => x.toNat / 2).length = n := by simp; omega
    have := (List.Nodup.getElem_inj hnd (i := 0) (j := j) (hi := by omega)
      (hj := by omega)).mp (by simp [List.getElem_take, hbeq])
    omega
  · exact hk0

theorem s13_final_props {t0 t lvl : List (BitVec 32)} {n : Nat} {uip : BitVec 32}
    (h : S13Tpi t0 t n) (h2 : 2 ≤ n) (hn : n ≤ t0.length) (h0 : t0[0]? = some uip)
    (hnd : ((t0.take n).map fun x => x.toNat / 2).Nodup)
    (hmax : ∀ k, 1 ≤ k → k < n →
      s13Lv lvl (t[k]?.getD 0#32) ≤ s13Lv lvl (t[1]?.getD 0#32)) :
    (∀ l, l ∈ (t.take n).map BitVec.toNat ↔ l ∈ (t0.take n).map BitVec.toNat) ∧
    (∀ l ∈ (t.take n).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < n ∧ (t0[j]?.getD 0#32).toNat = l) ∧
    ((t.take n).map fun x => x.toNat / 2).Nodup ∧ t[0]? = some uip ∧
    (∃ j, 1 ≤ j ∧ j < n ∧ t0[j]?.getD 0#32 = t[1]?.getD 0#32) ∧
    (∀ j, 1 ≤ j → j < n →
      s13Lv lvl (t0[j]?.getD 0#32) ≤ s13Lv lvl (t[1]?.getD 0#32)) := by
  obtain ⟨hl, ht0, hp⟩ := h
  have hiff : ∀ l, l ∈ (t.take n).map BitVec.toNat ↔ l ∈ (t0.take n).map BitVec.toNat := by
    intro l; simp only [List.mem_map]
    exact ⟨fun ⟨x, hx, he⟩ => ⟨x, hp.mem_iff.mp hx, he⟩,
      fun ⟨x, hx, he⟩ => ⟨x, hp.mem_iff.mpr hx, he⟩⟩
  have hnd' : ((t.take n).map fun x => x.toNat / 2).Nodup := (hp.map _).nodup_iff.mpr hnd
  refine ⟨hiff, ?_, hnd', ht0.trans h0, ?_, ?_⟩
  · intro l hl'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((hiff l).mp hl')
    obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_take] at hidx
    rw [List.getElem_take] at heq
    rcases Nat.eq_zero_or_pos idx with rfl | hpos
    · left; rw [List.getElem?_eq_getElem (by omega)] at h0; rw [← heq, Option.some.inj h0]
    · right; exact ⟨idx, hpos, by omega, by rw [List.getElem?_eq_getElem (by omega), ← heq]; rfl⟩
  · obtain ⟨k, hk1, hkn, hkeq⟩ :=
      s13_perm_pos hp.symm ht0.symm hnd' (j := 1) (Nat.le_refl _) (by omega) (by omega)
    exact ⟨k, hk1, hkn, by rw [hkeq]⟩
  · intro j hj1 hjn
    obtain ⟨k, hk1, hkn, hkeq⟩ := s13_perm_pos hp ht0 hnd hj1 hjn (by omega)
    rw [← hkeq]; exact hmax k hk1 hkn

private theorem s13_ins_step {lvl t3 : List (BitVec 32)} {x : BitVec 32} {i j j' M : Nat}
    (hjj : j' + 1 = j) (hj1 : 1 < j) (hji : j ≤ i) (hil : i < t3.length)
    (hA : ∀ k, 1 ≤ k → k ≤ i → k ≠ j → s13Lv lvl (t3[k]?.getD 0#32) ≤ M)
    (hB : 1 < j → s13Lv lvl (t3[1]?.getD 0#32) = M)
    (hcond : s13Lv lvl (t3[j']?.getD 0#32) < s13Lv lvl x) (v : BitVec 32)
    (hv : t3[j']? = some v) :
    (∀ k, 1 ≤ k → k ≤ i → k ≠ j' → s13Lv lvl ((t3.set j v)[k]?.getD 0#32) ≤ M) ∧
    (1 < j' → s13Lv lvl ((t3.set j v)[1]?.getD 0#32) = M) ∧
    (j' = 1 → M < s13Lv lvl x) := by
  subst hjj
  refine ⟨fun k hk1 hki hkj => ?_, fun hj2 => ?_, fun hj2 => ?_⟩
  · by_cases hkj' : k = j' + 1
    · subst hkj'; rw [List.getElem?_set_self (by omega)]
      have := hA j' (by omega) (by omega) (by omega); rwa [hv] at this
    · rw [List.getElem?_set_ne (Ne.symm hkj')]; exact hA k hk1 hki hkj'
  · rw [List.getElem?_set_ne (by omega)]; exact hB hj1
  · subst hj2; rw [← hB hj1]; exact hcond

private theorem s13_ins_exit {lvl t3 : List (BitVec 32)} {x : BitVec 32} {i j j' M : Nat}
    (hjj : j' + 1 = j) (hji : j ≤ i) (hil : i < t3.length)
    (hA : ∀ k, 1 ≤ k → k ≤ i → k ≠ j → s13Lv lvl (t3[k]?.getD 0#32) ≤ M)
    (hB : 1 < j → s13Lv lvl (t3[1]?.getD 0#32) = M)
    (hC : j = 1 → M < s13Lv lvl x)
    (hexit : j = 1 ∨ s13Lv lvl x ≤ s13Lv lvl (t3[j']?.getD 0#32)) :
    ∀ k, 1 ≤ k → k < i + 1 →
      s13Lv lvl ((t3.set j x)[k]?.getD 0#32) ≤ s13Lv lvl ((t3.set j x)[1]?.getD 0#32) := by
  subst hjj; intro k hk1 hki
  rcases Nat.lt_or_ge 1 (j' + 1) with hj | hj
  · rw [List.getElem?_set_ne (show j' + 1 ≠ 1 by omega), hB hj]
    by_cases hkj : k = j' + 1
    · subst hkj; rw [List.getElem?_set_self (by omega), Option.getD_some]
      rcases hexit with h | h
      · omega
      · exact Nat.le_trans h (hA j' (by omega) (by omega) (by omega))
    · rw [List.getElem?_set_ne (Ne.symm hkj)]; exact hA k hk1 (by omega) hkj
  · have hj1' : j' = 0 := by omega
    subst hj1'
    have hset1 : (t3.set (0 + 1) x)[1]?.getD 0#32 = x := by
      rw [show (0 + 1 : Nat) = 1 from rfl, List.getElem?_set_self (by omega), Option.getD_some]
    unfold s13Lv at hC ⊢; rw [hset1]
    by_cases hk : k = 1
    · subst hk; rw [hset1]; exact Nat.le_refl _
    · rw [show (0 + 1 : Nat) = 1 from rfl, List.getElem?_set_ne (Ne.symm hk)]
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hA k hk1 (by omega) hk) (hC rfl))

private theorem s13_shift' {xs orig : List (BitVec 32)} {sz j j' : Nat} {x prev : BitVec 32}
    (hjj : j' + 1 = j) (hlen : xs.length = orig.length) (hsz : sz ≤ orig.length) (hjsz : j < sz)
    (hprev : xs[j']? = some prev) (hperm : ((xs.set j x).take sz).Perm (orig.take sz)) :
    (((xs.set j prev).set j' x).take sz).Perm (orig.take sz) := by
  subst hjj
  have h := s13_tmp_shift_hole (j := j' + 1) hlen hsz (Nat.succ_pos _) hjsz
    (by simpa using hprev) hperm
  simpa using h

theorem s13Lv_of_idx {lvl : List (BitVec 32)} {y : BitVec 32} {idx : Nat}
    (hidx : idx = y.toNat / 2) (h : idx < lvl.length) :
    s13Lv lvl y = (lvl[idx]'h).toNat := by
  subst hidx; unfold s13Lv; rw [List.getElem?_eq_getElem h, Option.getD_some]

private theorem s13_getElem?_of_idx {t : List (BitVec 32)} {k k' : Nat} (hk : k = k')
    (h : k < t.length) : t[k']? = some (t[k]'h) := by
  subst hk; exact List.getElem?_eq_getElem h

private theorem s13Lv_eq_lvl {lvl t : List (BitVec 32)} {k k' i1 : Nat} (hk : k = k')
    (hkt : k < t.length) (hi1 : i1 = (t[k]'hkt).toNat / 2) (h1 : i1 < lvl.length) :
    s13Lv lvl (t[k']?.getD 0#32) = (lvl[i1]'h1).toNat := by
  subst hk hi1; unfold s13Lv
  rw [List.getElem?_eq_getElem hkt, Option.getD_some, List.getElem?_eq_getElem h1,
    Option.getD_some]

private theorem s13_lt_of_lvl {lvl t : List (BitVec 32)} {x : BitVec 32} {k k' i1 i2 : Nat}
    (hk : k = k') (hkt : k < t.length) (hi1 : i1 = (t[k]'hkt).toNat / 2)
    (hi2 : i2 = x.toNat / 2) {h1 : i1 < lvl.length} {h2 : i2 < lvl.length}
    (hc : (lvl[i1]'h1).toNat < (lvl[i2]'h2).toNat) :
    s13Lv lvl (t[k']?.getD 0#32) < s13Lv lvl x := by
  rw [s13Lv_eq_lvl hk hkt hi1 h1, s13Lv_of_idx hi2 h2]; exact hc

private theorem s13_le_of_lvl {lvl t : List (BitVec 32)} {x : BitVec 32} {k k' i1 i2 : Nat}
    (hk : k = k') (hkt : k < t.length) (hi1 : i1 = (t[k]'hkt).toNat / 2)
    (hi2 : i2 = x.toNat / 2) {h1 : i1 < lvl.length} {h2 : i2 < lvl.length}
    (hc : ¬ (lvl[i1]'h1).toNat < (lvl[i2]'h2).toNat) :
    s13Lv lvl x ≤ s13Lv lvl (t[k']?.getD 0#32) := by
  rw [s13Lv_eq_lvl hk hkt hi1 h1, s13Lv_of_idx hi2 h2]; omega

theorem s13_lshr1 (y : BitVec 32) : (y.setWidth 64 >>> 1).toNat = y.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, bv32_setWidth64_toNat]

private theorem s13_la_bv32_lshr_1 (x : BitVec 32) :
    (x >>> 1#32).toNat = x.toNat / 2 := bv32_lshr_1 x
private theorem s13_la_i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (i8_sext32_eq0 v)
private theorem s13_la_bv32_0_sext_mul4 :
    ((0#32 : BitVec 32).signExtend 64 * 4#64) = 0#64 := rfl
private theorem s13_la_bv32_1_sext_mul4 :
    ((1#32 : BitVec 32).signExtend 64 * 4#64) = 4#64 := rfl
attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true s13_la_bv32_lshr_1
  s13_la_i8_sext32_eq0_prop s13_la_bv32_0_sext_mul4 s13_la_bv32_1_sext_mul4

theorem s13_la_bv64_sub1_toNat {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx := x.isLt; bv_omega

theorem s13_nat_lt31_bv32_msb0 {n : Nat} (hn : n < 2 ^ 31 - 1) :
    let v := (BitVec.ofNat 64 n).setWidth 32
    v.toNat = n ∧ v ≠ 0xFFFFFFFF#32 ∧ (v &&& 0x80000000#32) = 0#32 := by
  have hn_mod : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  have hto : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), hn_mod]
  refine ⟨hto, ?_, ?_⟩
  · intro heq; have h1 := congrArg BitVec.toNat heq; rw [hto] at h1
    have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
  · apply BitVec.eq_of_getElem_eq; intro i hi
    rw [BitVec.getElem_and, BitVec.getElem_zero]
    by_cases h31 : i = 31
    · subst h31; rw [BitVec.getElem_eq_testBit_toNat, hto, Nat.testBit,
        Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega : n < 2 ^ 31)]; simp
    · rw [show (0x80000000#32 : BitVec 32)[i]'hi = false from by revert i hi h31; decide]
      simp

theorem s13_tmp_take1_eq {tmp : List (BitVec 32)} {u : BitVec 32} (h1 : 1 ≤ tmp.length)
    (h0 : tmp[0]? = some u) : (tmp.take 1).map BitVec.toNat = [u.toNat] := by
  cases tmp with
  | nil => simp at h1
  | cons a _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0; simp

theorem s13_tmp_take2_eq {tmp : List (BitVec 32)} {u v : BitVec 32} (h2 : 2 ≤ tmp.length)
    (h0 : tmp[0]? = some u) (h1 : tmp[1]? = some v) :
    (tmp.take 2).map BitVec.toNat = [u.toNat, v.toNat] := by
  rcases tmp with _ | ⟨a, _ | ⟨b, _⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    subst h0 h1; simp

private theorem s13_bv32_or_used31_garb (h : BitVec 32) :
    ((h ||| 0xF8000000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_and]
  have h0 : ((0xF8000000#32 : BitVec 32)[i]'hi && (0x00080000#32 : BitVec 32)[i]'hi) = false := by
    revert i hi; decide
  cases h1 : (0x00080000#32 : BitVec 32)[i]'hi <;>
    cases h2 : (0xF8000000#32 : BitVec 32)[i]'hi <;> simp_all

private theorem s13_bv32_or_used31_shrk (h : BitVec 32) :
    ((h ||| 0xF8000000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_and]
  have h0 : ((0xF8000000#32 : BitVec 32)[i]'hi && (0x00800000#32 : BitVec 32)[i]'hi) = false := by
    revert i hi; decide
  cases h1 : (0x00800000#32 : BitVec 32)[i]'hi <;>
    cases h2 : (0xF8000000#32 : BitVec 32)[i]'hi <;> simp_all

theorem s13_orUsed31_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hs : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) :
    let ar' := s.core.arena.set cref (fullArenaHdr s cref ||| 0xF8000000#32)
    let s' : FullState := { s with core := { s.core with arena := ar' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro ar' s'
  have hlen := hs.1.core_ok
  have hw := hs.2.1
  have ha := hw.arena
  have hcref_wf := ha.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : s.core.arena[cref]? = some (fullArenaHdrCore s.core cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have ha_cref : s'.core.arena[cref]? = some (fullArenaHdrCore s.core cref ||| 0xF8000000#32) :=
    List.getElem?_set_self har_len
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (ha.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]? :=
        List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [s13_bv32_or_used31_shrk,
        show fullArenaHdrCore s.core cref = s.core.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
        · have := (ha.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (ha.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s', ar']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
      · have := (ha.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    by_cases hrc : r = cref
    · subst r
      rw [ha_cref, hget_cref, Option.getD_some, Option.getD_some, s13_bv32_or_used31_garb]
    · dsimp only [s', ar']; rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hszr := hsz_eq r hr
    unfold fullArenaClauseLitsCore
    rw [hszr]; congr 1
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, s', ar', List.length_set]
    · intro j hj1 hj2
      simp only [List.getElem_take, List.getElem_drop]
      dsimp only [s', ar']
      have hne_idx : cref ≠ r + 3 + j := by
        by_cases hrc : r = cref
        · subst r; omega
        · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
          · simp only [List.length_take, List.length_drop, s', ar', List.length_set] at hj1
            omega
          · omega
      exact List.getElem_set_ne hne_idx _
  have ha' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := ha.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢
          simpa only [ha_cref, hget_cref, Option.getD_some, s13_bv32_or_used31_shrk] using hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa only [s', ar', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (ha.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, ht0_hi, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (ha.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (ha.refs_wf cref hr).2.1; omega
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
          · omega
          · have := (ha.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo,
        by dsimp only [s']; exact Nat.lt_of_le_of_lt ht0_hi ht2, ?_⟩
      dsimp only [s', ar']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr] at hl
      exact ha.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng
      change (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLitsCore s'.core r))
      rw [hlits_eq r hr]
      exact ha.entails r hr hng
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := ha'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        change if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
        split
        · rename_i hbin; rw [ite_eq_left hbin] at hrs; exact hrs
        · rename_i hlg; rw [ite_eq_right hlg] at hrs
          obtain ⟨hrr, hng, hall⟩ := hrs
          exact ⟨hrefs.symm ▸ hrr, (hgarb_eq _ hrr).trans hng,
            fun q hq => hall q ((hlits_eq _ hrr) ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hmem := hw.reason_lit_mem idx hidx hne hlg
        have hrs := hw.reason_inv idx hidx hne
        rw [ite_eq_right (fun h => h hlg)] at hrs
        change (s.core.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s'.core _
        rw [hlits_eq _ hrs.1]; exact hmem }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen with arena_len_arr := by simp [s', ar', hlen.arena_len_arr] }, hs.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgarb_eq r hr] at hng
    change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
    rw [hlits_eq r hr]; exact hs.2.2.2.1 r hr hng
  have hext' : FullExtScratchOk c s' :=
    fullExtScratchOk_of_pres hs.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
  exact ⟨⟨hlen', hw', hs.2.2.1, hnd', hext', hs.2.2.2.2.2⟩, hrefs,
    fun r hr => ⟨hgarb_eq r hr, hlits_eq r hr⟩⟩

/-! ## 2. Insertion Sort Body, `S13AddClPre`, `S13NrSpec`, & `s13_add_call_wp` -/

theorem s13_ins_body_wp {Γ : Env} {Q : Post [i64]} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {t2 : List (BitVec 32)} {i : BitVec 64}
    {m2 : Mem 64} (J : Cont [i64])
    (hi : i.toNat < s.core.tmp_len) (hi2 : 2 ≤ i.toNat) (ht2 : S13Tpi s.core.tmp t2 s.core.tmp_len)
    (hmax2 : ∀ k, 1 ≤ k → k < i.toNat →
      s13Lv s.core.lvl (t2[k]?.getD 0#32) ≤ s13Lv s.core.lvl (t2[1]?.getD 0#32))
    (hm2 : (FullMem c { s with core := { s.core with tmp := t2 } } ⋆ R) m2)
    (htl_cv : s.core.tmp_len ≤ s.core.cur_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (htmp_len_arr : s.core.tmp.length = c.max_vars) (hll : s.core.lvl.length = c.max_vars)
    (hmv : c.max_vars < 2 * 2 ^ 28)
    (hlits : ∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (ih : ∀ (i' : BitVec 64) (m' : Mem 64), s.core.tmp_len - i'.toNat < s.core.tmp_len - i.toNat →
      (∃ t2' : List (BitVec 32), 2 ≤ i'.toNat ∧ i'.toNat ≤ s.core.tmp_len ∧
        S13Tpi s.core.tmp t2' s.core.tmp_len ∧
        (∀ k, 1 ≤ k → k < i'.toNat →
          s13Lv s.core.lvl (t2'[k]?.getD 0#32) ≤ s13Lv s.core.lvl (t2'[1]?.getD 0#32)) ∧
        (FullMem c { s with core := { s.core with tmp := t2' } } ⋆ R) m') → J (i', ()) m') :
    wp Γ Q X
      (Expr.load i32 (Arg.var (c.pTmp + i * 4)) fun ld =>
      Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
      Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_1 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var (Prod.fst p),
        Arg.var (Prod.fst p_1), ()) }
      fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p),
        Arg.imm 4, ()) } fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.pLevel,
        Arg.var (Prod.fst p), ()) }
      fun p =>
      Expr.load i32 (Arg.var (Prod.fst p)) fun ld_1 =>
      Expr.group (sig := [[i64]])
      (fun Js =>
      Blocks.cons
      (fun p =>
      Expr.group (sig := [[]])
      (fun _ =>
      Blocks.cons
      (fun _ =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p), Arg.imm 4, ()) }
      fun p =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p), ()) }
      fun p =>
      Expr.store (Arg.var ld) (Arg.var (Prod.fst p))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var i, Arg.imm 1, ()) }
      fun p => Expr.jump J (Arg.var (Prod.fst p), ())))
      Blocks.nil)
      fun Js_1 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_2 =>
      Expr.jnz (Arg.var (Prod.fst p_2))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_3 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p_3), Arg.imm 4, ()) }
      fun p_4 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_4), ()) }
      fun p_5 =>
      Expr.load i32 (Arg.var (Prod.fst p_5)) fun ld =>
      Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) }
      fun p_6 =>
      Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
      fun p_7 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.lshr i64,
        args := (Arg.var (Prod.fst p_6), Arg.var (Prod.fst p_7), ()) }
      fun p_8 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p_8), Arg.imm 4, ()) }
      fun p_9 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pLevel, Arg.var (Prod.fst p_9), ()) }
      fun p_10 =>
      Expr.load i32 (Arg.var (Prod.fst p_10)) fun ld =>
      Expr.let_
      { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var ld, Arg.var ld_1, ()) }
      fun p_11 =>
      Expr.jnz (Arg.var (Prod.fst p_11))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p), Arg.imm 4, ()) }
      fun p_12 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_12), ()) }
      fun p_13 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_14 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64,
        args := (Arg.var (Prod.fst p_14), Arg.imm 4, ()) }
      fun p_15 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_15), ()) }
      fun p_16 =>
      Expr.load i32
      (Arg.var (Prod.fst p_16))
      fun ld =>
      Expr.store (Arg.var ld)
      (Arg.var (Prod.fst p_13))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p => Expr.jump (Prod.fst Js) (Arg.var (Prod.fst p), ())))
      (Expr.jump (Prod.fst Js_1) ()))
      (Expr.jump (Prod.fst Js_1) ()))
      Blocks.nil)
      fun Js => Expr.jump (Prod.fst Js) (Arg.var i, ()))
      m2 := by
  have ht2l := ht2.1
  have ht2_lt := s13Tpi_lt ht2 (by omega) hlits
  have hi_t : i.toNat < t2.length := by omega
  have hx_lt : (t2[i.toNat]'hi_t).toNat < 2 * s.core.cur_vars := by
    have := ht2_lt i.toNat hi
    rwa [List.getElem?_eq_getElem hi_t, Option.getD_some] at this
  c0_clean; c0_steps
  refine wp_loop_inv (ts := [i64])
    (fun (j, ()) m3 => ∃ t3 : List (BitVec 32), 1 ≤ j.toNat ∧ j.toNat ≤ i.toNat ∧
      t3.length = s.core.tmp.length ∧ t3[0]? = s.core.tmp[0]? ∧
      ((t3.set j.toNat (t2[i.toNat]'hi_t)).take s.core.tmp_len).Perm
        (s.core.tmp.take s.core.tmp_len) ∧
      (∀ k, 1 ≤ k → k ≤ i.toNat → k ≠ j.toNat →
        s13Lv s.core.lvl (t3[k]?.getD 0#32) ≤ s13Lv s.core.lvl (t2[1]?.getD 0#32)) ∧
      (1 < j.toNat →
        s13Lv s.core.lvl (t3[1]?.getD 0#32) = s13Lv s.core.lvl (t2[1]?.getD 0#32)) ∧
      (j.toNat = 1 →
        s13Lv s.core.lvl (t2[1]?.getD 0#32) < s13Lv s.core.lvl (t2[i.toNat]'hi_t)) ∧
      (FullMem c { s with core := { s.core with tmp := t3 } } ⋆ R) m3)
    (fun (j, ()) _ => j.toNat) ?_ ?_
  · intro J2 hJ2
    c0_steps
    refine hJ2 _ m2 ⟨t2, by omega, Nat.le_refl _, ht2l, ht2.2.1, ?_,
      fun k hk1 hk2 hk3 => hmax2 k hk1 (by omega), fun _ => rfl, fun h => by omega, hm2⟩
    rw [List.set_getElem_self]; exact ht2.2.2
  intro J2 ⟨j, ⟨⟩⟩ m3 ⟨t3, hj1, hji, ht3l, ht30, hp3, hA, hB, hC, hm3⟩ ih2
  have hj_t : j.toNat < t3.length := by omega
  have hjm1 : (j - 1).toNat + 1 = j.toNat := by bv_omega
  refine wp_join_group (ts := [])
    (fun () m4 => (FullMem c { s with core := { s.core with tmp := t3 } } ⋆ R) m4 ∧
      (j.toNat = 1 ∨ s13Lv s.core.lvl (t2[i.toNat]'hi_t) ≤
        s13Lv s.core.lvl (t3[(j - 1).toNat]?.getD 0#32))) ?_ ?_
  · rintro _ ⟨⟩ m4 ⟨hm4, hexit⟩
    c0_clean; c0_steps
    have hi1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
    refine ih (i + 1) m ?_ ⟨t3.set j.toNat (t2[i.toNat]'hi_t), by omega, by omega,
      ⟨by simp [ht3l], by rw [List.getElem?_set_ne (by omega)]; exact ht30, hp3⟩, ?_, hm⟩
    · omega
    · rw [hi1]; exact s13_ins_exit hjm1 hji (by omega) hA hB hC hexit
  · intro Jx hJx
    c0_clean; c0_split
    · have hj2 : 1 < j.toNat := by bv_omega
      have hb3 : ∀ k < s.core.tmp_len, (((t3.set j.toNat (t2[i.toNat]'hi_t)))[k]?.getD
          0#32).toNat < 2 * s.core.cur_vars :=
        s13Tpi_lt ⟨by simp [ht3l], by rw [List.getElem?_set_ne (by omega)]; exact ht30, hp3⟩
          (by omega) hlits
      have hjm1_t : (j - 1).toNat < t3.length := by omega
      have hprev_lt : (t3[(j - 1).toNat]'hjm1_t).toNat < 2 * s.core.cur_vars := by
        have := hb3 (j - 1).toNat (by omega)
        rwa [List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hjm1_t,
          Option.getD_some] at this
      have hjm1n : (2 ^ 64 - 1 + j.toNat) % 2 ^ 64 = (j - 1).toNat := by bv_omega
      c0_clean; c0_steps
      · have hjt' : (2 ^ 64 - 1 + j.toNat) % 2 ^ 64 < t3.length := by omega
        have hcond := s13_lt_of_lvl (lvl := s.core.lvl) hjm1n hjt' (s13_lshr1 _) (s13_lshr1 _) hc
        have hv := s13_getElem?_of_idx hjm1n hjt'
        obtain ⟨hA', hB', hC'⟩ :=
          s13_ins_step hjm1 hj2 hji (by omega) hA hB hcond (t3[_]'hjt') hv
        refine ih2 (j - 1, ()) m (by dsimp only; omega) ⟨_, by omega, by omega,
          by simp [ht3l], by rw [List.getElem?_set_ne (by omega)]; exact ht30,
          s13_shift' hjm1 (by omega) (by omega) (by omega) hv hp3, hA', hB', hC', hm⟩
      · exact hJx () m3 ⟨hm3, Or.inr (s13_le_of_lvl (lvl := s.core.lvl) hjm1n (by omega)
          (s13_lshr1 _) (s13_lshr1 _) hc)⟩
    · c0_clean; c0_steps; exact hJx () m3 ⟨hm3, Or.inl (by bv_omega)⟩

@[expose] def S13AddClPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (nlvl : BitVec 64) (tmp_sw : List (BitVec 32)) (vals_bt : List (BitVec 8))
    (lvl_bt trl_bt : List (BitVec 32)) (te_bt : Nat) (sg : FullState) : Prop :=
  FullSparseInvW c F0 F_cur sg ∧ sg.core.cur_level = nlvl.toNat ∧
  sg.core.cur_vars = s.core.cur_vars ∧ sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  sg.core.tmp = tmp_sw ∧ sg.core.tmp_len = s.core.tmp_len ∧
  sg.core.vals = vals_bt ∧ sg.core.lvl = lvl_bt ∧ sg.core.trl = trl_bt ∧
  sg.core.trail_end = te_bt ∧ sg.core.probing = s.core.probing ∧
  sg.core.min_clr_len = s.core.min_clr_len ∧ sg.scratch.work_stk1 = s.scratch.work_stk1 ∧
  sg.scratch.work_stk2 = s.scratch.work_stk2

@[expose] def S13NrSpec (F_cur : List (List Nat)) (s : FullState) (uip wm : BitVec 32)
    (tmp_sw : List (BitVec 32)) (sac : FullState) (r_ac : BitVec 64) : Prop :=
  r_ac = 0xFFFFFFFF#64 ∨
  (r_ac ≠ 0xFFFFFFFF#64 ∧
    if r_ac = 0xFFFFFFFE#64 then
      (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat, wm.toNat])
    else
      r_ac.toNat < 2 ^ 31 - 1 ∧
      r_ac.toNat ∈ fullArenaClauseRefs sac ∧
      fullArenaClauseGarb sac r_ac.toNat = false ∧
      (∀ q ∈ fullArenaClauseLits sac r_ac.toNat,
        q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat) ∧
      uip.toNat ∈ fullArenaClauseLits sac r_ac.toNat)

theorem s13_add_call_wp {Γ : Env} {Q : Post [i64]} {X : XPost} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {nlvl glue : BitVec 64} {uip wm : BitVec 32}
    {tmp_sw : List (BitVec 32)} {vals_bt : List (BitVec 8)} {lvl_bt trl_bt : List (BitVec 32)}
    {te_bt : Nat} {R : Mem 64 → Prop} {extg : List (BitVec 64)} {sg : FullState} {mg : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hAddCl : ∀ a m Q X, Proof.Clause.Spec.fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (htl_2 : 2 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hsw_0 : tmp_sw[0]? = some uip) (hsw_1 : tmp_sw[1]? = some wm)
    (hsw_lits_lt : ∀ l ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat, l < 2 * s.core.cur_vars)
    (hsw_nd : ((tmp_sw.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup)
    (hent_sw : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp_sw.take s.core.tmp_len).map BitVec.toNat)))
    (hextg : M6HdrExtOk extg)
    (hsg_pre : S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt sg)
    (hm_g : (FullM6HdrMem c extg sg ⋆ R) mg)
    (hk : ∀ new_ref64 s_ac m_ac,
      S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_ac →
      S13NrSpec F_cur s uip wm tmp_sw s_ac new_ref64 →
      (FullM6HdrMem c extg s_ac ⋆ R) m_ac →
      wp Γ Q X (k (new_ref64, ())) m_ac) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32, .bool]) (bs := [i64]) (rs := [i64])
        "full_add_clause"
        (Arg.var c.hdr, Arg.var ((BitVec.ofNat 64 sg.core.tmp_len).setWidth 32),
          Arg.var (glue.setWidth 32), Arg.imm true, ()) k) mg := by
  have _ := hextg
  obtain ⟨hsp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s, htrl_s, hte_s,
    hprb_s, hmcl_s, hws1_s, hws2_s⟩ := hsg_pre
  have hlen_s := hsp.1
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have htl_tr32 : ((BitVec.ofNat 64 s.core.tmp_len).setWidth 32).toNat = s.core.tmp_len := by
    have hcv_le := hlen_s.core_ok.cur_vars_le
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s.core.tmp_len < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have hm_gf := fullM6HdrMem_focus_full hm_g
  let Rg : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) extg ⋆ R
  change (FullMem c sg ⋆ Rg) mg at hm_gf
  refine wp_call_of_spec _ _ ?_
  dsimp only [Arg.val_var, vals]
  refine hAddCl _ _ _ _ ⟨c, F0, F_cur, sg, Rg, rfl, hlen_s, hsp.2.1, hsp.2.2.2.2.2,
    by rw [htl_s, htl_tr32]; have := hlen_s.core_ok.cur_vars_le; omega,
    fun _ => by rw [htmp_s, htl_s, htl_tr32, hcv_s]; exact ⟨hsw_lits_lt, hsw_nd, hent_sw⟩,
    hm_gf, ?_⟩
  rw [htl_s, htl_tr32]
  simp only [show ¬ s.core.tmp_len < 2 by omega, ↓reduceIte]
  by_cases htl2 : s.core.tmp_len = 2
  · simp only [htl2, ↓reduceIte]
    intro r_ac flags_a wvec_a wstk_a wlen_a wu_a nb_a wsort_a m_ac hr_ac hac_len hac_w hm_ac
    let s_ac : FullState :=
      { sg with
        core := { sg.core with
          flags := flags_a, wvec := wvec_a, wstk := wstk_a, wlen := wlen_a,
          wusable := wu_a, num_binary := nb_a }
        scratch := { sg.scratch with wsort := wsort_a } }
    have hac_sp : FullSparseInvW c F0 F_cur s_ac :=
      ⟨hac_len, hac_w, hsp.2.2.1, hsp.2.2.2.1,
        fullExtScratchOk_of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
        hsp.2.2.2.2.2⟩
    have hnr : S13NrSpec F_cur s uip wm tmp_sw s_ac r_ac := by
      rcases hr_ac with rfl | rfl
      · exact Or.inl rfl
      · right; refine ⟨by decide, ?_⟩; simp only [↓reduceIte]
        have hcv_le := hlen_s.core_ok.cur_vars_le
        have hlen2_sw : 2 ≤ tmp_sw.length := by
          have := hlen_s.core_ok.tmp_len_arr; rw [htmp_s] at this; omega
        rw [htl2, s13_tmp_take2_eq hlen2_sw hsw_0 hsw_1] at hent_sw
        exact hent_sw
    exact hk r_ac s_ac m_ac ⟨hac_sp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s,
      htrl_s, hte_s, hprb_s, hmcl_s, hws1_s, hws2_s⟩ hnr (fullM6HdrMem_unfocus_full hm_ac)
  · simp only [htl2, ↓reduceIte]
    intro r_ac arena_a alen_a wvec_a wstk_a wlen_a wu_a fred_a ni_a nr_a wsort_a m_ac
      hr_ac hac_len hac_w hrefs_sub hnd_imp hok_a hm_ac
    let s_ac : FullState :=
      { sg with
        core := { sg.core with
          arena := arena_a, arena_len := alen_a, wvec := wvec_a, wstk := wstk_a,
          wlen := wlen_a, wusable := wu_a, first_reducible := fred_a, num_irred := ni_a,
          num_redundant := nr_a }
        scratch := { sg.scratch with wsort := wsort_a } }
    have hac_sp : FullSparseInvW c F0 F_cur s_ac :=
      ⟨hac_len, hac_w, hsp.2.2.1, hnd_imp hsp.2.2.2.1,
        fullExtScratchOk_of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ hrefs_sub,
        hsp.2.2.2.2.2⟩
    have hnr : S13NrSpec F_cur s uip wm tmp_sw s_ac r_ac := by
      rcases hr_ac with rfl | rfl
      · exact Or.inl rfl
      · obtain ⟨_, href_a, hng_a, hlits_a⟩ := hok_a rfl
        have hal_lt31 : sg.core.arena_len < 2 ^ 31 - 1 := by
          have := hlen_s.core_ok.arena_len_le; omega
        have hnr_toNat : (BitVec.ofNat 64 sg.core.arena_len).toNat = sg.core.arena_len :=
          Proof.Spec.bv64_ofNat_toNat (by omega)
        have hne_ff : BitVec.ofNat 64 sg.core.arena_len ≠ 0xFFFFFFFF#64 := fun heq => by
          have := congrArg BitVec.toNat heq; rw [hnr_toNat] at this
          have : (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1 := rfl; omega
        have hne_fe : BitVec.ofNat 64 sg.core.arena_len ≠ 0xFFFFFFFE#64 := fun heq => by
          have := congrArg BitVec.toNat heq; rw [hnr_toNat] at this
          have : (0xFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 32 - 2 := rfl; omega
        right; refine ⟨hne_ff, ?_⟩; simp only [hne_fe, ↓reduceIte, hnr_toNat]
        have hlits_eq : fullArenaClauseLits s_ac sg.core.arena_len =
            (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
          change fullArenaClauseLits s_ac sg.core.arena_len =
            (sg.core.tmp.take s.core.tmp_len).map BitVec.toNat at hlits_a
          rwa [htmp_s] at hlits_a
        refine ⟨hal_lt31, href_a, hng_a, fun q hq => by rwa [hlits_eq] at hq, ?_⟩
        rw [hlits_eq, List.mem_map]
        have hcv_le := hlen_s.core_ok.cur_vars_le
        have h0_sw : 0 < tmp_sw.length := by
          have := hlen_s.core_ok.tmp_len_arr; rw [htmp_s] at this; omega
        have hu_sw : tmp_sw[0]'h0_sw = uip := by
          have := List.getElem?_eq_getElem h0_sw; rw [hsw_0] at this
          exact (Option.some.inj this).symm
        exact ⟨uip, List.mem_iff_getElem.mpr ⟨0, by rw [List.length_take]; omega,
          by rw [List.getElem_take]; exact hu_sw⟩, rfl⟩
    exact hk r_ac s_ac m_ac ⟨hac_sp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s,
      htrl_s, hte_s, hprb_s, hmcl_s, hws1_s, hws2_s⟩ hnr (fullM6HdrMem_unfocus_full hm_ac)

/-! ## 3. Post-Add-Clause Assignment (`jumpreasons`) + Eager Subsume -/

@[expose] def s13PostAcExpr (c : FullCfg) (uip_lit : Val i32) (new_ref64 : Val i64)
    (max_lvl : Nat) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
      args := (Arg.var new_ref64, Arg.imm 4294967295, ()) } fun p36 =>
  Expr.jnz (Arg.var p36.1) (Expr.ret (Arg.imm 0, ()))
    (Expr.let_
      { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var uip_lit, ()) } fun p37 =>
    Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pVals, Arg.var p37.1, ()) } fun p38 =>
    Expr.load i8 (Arg.var p38.1) fun ld =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p39 =>
    Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld, ()) } fun p40 =>
    Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var p39.1, ()) } fun p41 =>
    Expr.let_
      { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
        args := (Arg.var p40.1, Arg.var p41.1, ()) } fun p42 =>
    Expr.jnz (Arg.var p42.1) (Expr.ret (Arg.imm 0, ()))
      (Expr.group (sig := [[]])
        (fun _Ju =>
          Blocks.cons
            (fun _ =>
              Expr.let_
                { sig := [i64], code := OpCode.trunc 64 32,
                  args := (Arg.var new_ref64, ()) } fun rsn0 =>
              Expr.group (sig := [[i32]])
                (fun _Jol =>
                  Blocks.cons
                    (fun p43 =>
                      Expr.let_
                        { sig := [i64], code := OpCode.trunc 64 32,
                          args := (Arg.var (BitVec.ofNat 64 max_lvl), ()) } fun p44 =>
                      Expr.call (as := [i64, i32, i32, i32]) (bs := []) (rs := [i64])
                        "full_assign_lvl"
                        (Arg.var c.hdr, Arg.var uip_lit, Arg.var p43.1, Arg.var p44.1, ())
                        fun (_ : Tup Val []) =>
                        Expr.call (as := [i64, i64]) (bs := []) (rs := [i64])
                          "full_eager_subsume" (Arg.var c.hdr, Arg.var new_ref64, ())
                          fun (_ : Tup Val []) => Expr.ret (rs := [i64]) (Arg.imm 1, ()))
                    Blocks.nil)
                fun Jol =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                    args := (Arg.var new_ref64, Arg.imm 4294967294, ()) } fun p =>
                Expr.jnz (Arg.var p.1)
                  (Expr.let_
                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p.1, Arg.imm 4, ()) } fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pTmp, Arg.var p.1, ()) } fun p =>
                  Expr.load i32 (Arg.var p.1) fun ld =>
                  Expr.let_
                    { sig := [i32, i32], code := OpCode.and i32,
                      args := (Arg.var ld, Arg.imm 2147483647, ()) } fun p =>
                  Expr.let_
                    { sig := [i32, i32], code := OpCode.or i32,
                      args := (Arg.var p.1, Arg.imm 2147483648, ()) } fun rsn1 =>
                  Expr.group (sig := [[i32]])
                    (fun _Js2 => Blocks.cons (fun p =>
                      Expr.jump Jol.1 (Arg.var p.1, ())) Blocks.nil)
                    fun Js2 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                        args := (Arg.var (BitVec.ofNat 64 max_lvl), Arg.imm 0, ()) } fun pm =>
                    Expr.jnz (Arg.var pm.1)
                      (Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.hdr, Arg.imm 88, ()) } fun prs =>
                      Expr.load i64 (Arg.var prs.1) fun rsns_lc =>
                      Expr.let_
                        { sig := [i32], code := OpCode.sext 32 64,
                          args := (Arg.imm 1, ()) } fun p1a =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var p1a.1, Arg.imm 4, ()) } fun p1b =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.pTmp, Arg.var p1b.1, ()) } fun p1c =>
                      Expr.load i32 (Arg.var p1c.1) fun t1b =>
                      Expr.let_
                        { sig := [i32, i32], code := OpCode.lshr i32,
                          args := (Arg.var t1b, Arg.imm 1, ()) } fun t1s =>
                      Expr.let_
                        { sig := [i32], code := OpCode.zext 32 64,
                          args := (Arg.var t1s.1, ()) } fun t1s64 =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var t1s64.1, Arg.imm 4, ()) } fun t1off =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var rsns_lc, Arg.var t1off.1, ()) } fun t1p =>
                      Expr.load i32 (Arg.var t1p.1) fun nr_lc =>
                      Expr.group (sig := [[i32]])
                        (fun _Js3 => Blocks.cons (fun jr =>
                          Expr.jump Js2.1 (Arg.var jr.1, ())) Blocks.nil)
                        fun Js3 =>
                        Expr.let_
                          { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                            args := (Arg.var nr_lc, Arg.imm 4294967295, ()) } fun cne =>
                        Expr.jnz (Arg.var cne.1)
                          (Expr.let_
                            { sig := [i32, i32], code := OpCode.and i32,
                              args := (Arg.var nr_lc, Arg.imm 2147483648, ()) } fun chi =>
                          Expr.let_
                            { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                              args := (Arg.var chi.1, Arg.imm 0, ()) } fun chib =>
                          Expr.jnz (Arg.var chib.1)
                            (Expr.jump Js3.1 (Arg.var nr_lc, ()))
                            (Expr.jump Js3.1 (Arg.var rsn1.1, ())))
                          (Expr.jump Js3.1 (Arg.var rsn1.1, ())))
                      (Expr.jump Js2.1 (Arg.var rsn1.1, ())))
                  (Expr.jump Jol.1 (Arg.var rsn0.1, ())))
            Blocks.nil)
        fun Ju =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
            args := (Arg.var new_ref64, Arg.imm 4294967294, ()) } fun p =>
        Expr.jnz (Arg.var p.1)
          (Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p =>
          Expr.load i64 (Arg.var p.1) fun ld =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
              args := (Arg.var new_ref64, Arg.var ld, ()) } fun p =>
          Expr.jnz (Arg.var p.1)
            (Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.hdr, Arg.imm 112, ()) } fun p =>
            Expr.load i64 (Arg.var p.1) fun ld_ar =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var new_ref64, Arg.imm 4, ()) } fun p =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var ld_ar, Arg.var p.1, ()) } fun p_st =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var new_ref64, Arg.imm 4, ()) } fun p2 =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var ld_ar, Arg.var p2.1, ()) } fun p_el =>
            Expr.load i32 (Arg.var p_el.1) fun ld_h =>
            Expr.let_
              { sig := [i32, i32], code := OpCode.shl i32,
                args := (Arg.imm 31, Arg.imm 27, ()) } fun p_sh =>
            Expr.let_
              { sig := [i32, i32], code := OpCode.or i32,
                args := (Arg.var ld_h, Arg.var p_sh.1, ()) } fun p_nh =>
            Expr.store (Arg.var p_nh.1) (Arg.var p_st.1) (Expr.jump Ju.1 ()))
            (Expr.jump Ju.1 ()))
          (Expr.jump Ju.1 ())))

theorem s13_learn_clause_post_ac_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_ac : FullState} {R : Mem 64 → Prop} {m_ac : Mem 64}
    {uip_lit wm : BitVec 32} {new_ref64 : BitVec 64} {max_lvl : Nat}
    {tmp_sw : List (BitVec 32)}
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hEsub : ∀ a m Q X, Proof.Learn.Spec.fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X)
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.probing = s.core.probing → s'.core.min_clr_len = s.core.min_clr_len →
      s'.scratch.work_stk1 = s.scratch.work_stk1 → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hac_sparse : FullSparseInvW c F0 F_cur s_ac)
    (hcur_lt : s_ac.core.cur_level < s.core.cur_level)
    (hmax_pos : 0 < max_lvl) (hmax_le : max_lvl ≤ s_ac.core.cur_level)
    (hmax_lt28 : max_lvl < 2 * 2 ^ 28)
    (hcv_eq : s_ac.core.cur_vars = s.core.cur_vars)
    (hfuel : s_ac.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hprb : s_ac.core.probing = s.core.probing) (hmcl : s_ac.core.min_clr_len = s.core.min_clr_len)
    (hws1 : s_ac.scratch.work_stk1 = s.scratch.work_stk1)
    (hws2 : s_ac.scratch.work_stk2 = s.scratch.work_stk2)
    (htmp_eq : s_ac.core.tmp = tmp_sw) (htlen_eq : s_ac.core.tmp_len = s.core.tmp_len)
    (hsw_1 : tmp_sw[1]? = some wm)
    (htl_2 : 2 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (huip_lt : uip_lit.toNat < 2 * s.core.cur_vars)
    (hwm_lt : wm.toNat < 2 * s.core.cur_vars)
    (htmp_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hwm_on_bt : ∃ idx < s_ac.core.trail_end,
      (s_ac.core.trl[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
      (s_ac.core.lvl[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hlow : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
      q = uip_lit.toNat ∨ ∃ idx < s_ac.core.trail_end,
        (s_ac.core.trl[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s_ac.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hr_spec : S13NrSpec F_cur s uip_lit wm tmp_sw s_ac new_ref64)
    (hm_ac : (FullMem c s_ac ⋆ R) m_ac) :
    wp Γ Q X (s13PostAcExpr c uip_lit new_ref64 max_lvl) m_ac := by
  unfold s13PostAcExpr
  have hac_len := hac_sparse.1
  have hcl := hac_len.core_ok
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have huip_vlen : uip_lit.toNat < s_ac.core.vals.length := by
    rw [hcl.vals_len]; have := hcl.cur_vars_le; omega
  c0_split
  · c0_steps
    exact hQ 0#64 s_ac m_ac hac_len (Or.inl rfl) hcv_eq hfuel hprb hmcl hws1 hws2
      (fun h => by cases h) (fun _ => hac_sparse) (fun h => by cases h) hm_ac
  · have hne_ff : new_ref64 ≠ 0xFFFFFFFF#64 := by assumption
    have hnr_ok := (hr_spec.resolve_left hne_ff).2
    c0_split
    · c0_steps
      exact hQ 0#64 s_ac m_ac hac_len (Or.inl rfl) hcv_eq hfuel hprb hmcl hws1 hws2
        (fun h => by cases h) (fun _ => hac_sparse) (fun h => by cases h) hm_ac
    · have huip_z : s_ac.core.vals[uip_lit.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]
        exact (by assumption : s_ac.core.vals[uip_lit.toNat] = 0#8)
      refine wp_join_group (ts := []) (fun () m_u =>
          ∃ ar_u : List (BitVec 32),
            let s_u : FullState := { s_ac with core := { s_ac.core with arena := ar_u } }
            FullSparseInvW c F0 F_cur s_u ∧ fullArenaClauseRefs s_u = fullArenaClauseRefs s_ac ∧
            (∀ r ∈ fullArenaClauseRefs s_ac,
              fullArenaClauseGarb s_u r = fullArenaClauseGarb s_ac r ∧
              fullArenaClauseLits s_u r = fullArenaClauseLits s_ac r) ∧
            (FullMem c s_u ⋆ R) m_u) ?_ ?_
      · rintro _ ⟨⟩ m_u ⟨ar_u, hu_sparse, hrefs_u, hprops_u, hm_u⟩
        let s_u : FullState := { s_ac with core := { s_ac.core with arena := ar_u } }
        have hu_len := hu_sparse.1
        c0_clean; c0_to_group
        refine wp_join_group (ts := [i32]) (fun (rsn_bv, ()) m_r =>
            m_r = m_u ∧ rsn_bv ≠ 0xFFFFFFFF#32 ∧
            (if (rsn_bv &&& 0x80000000#32) ≠ 0#32 then
              let ot := (rsn_bv &&& 0x7FFFFFFF#32).toNat
              ot < 2 * s_u.core.cur_vars ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [uip_lit.toNat, ot]) ∧
              ∃ m < s_u.core.trail_end, (s_u.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
                (s_u.core.lvl[ot / 2]?.getD 0#32).toNat ≤ max_lvl
            else
              rsn_bv.toNat ∈ fullArenaClauseRefsCore s_u.core ∧
              fullArenaClauseGarbCore s_u.core rsn_bv.toNat = false ∧
              (∀ q ∈ fullArenaClauseLitsCore s_u.core rsn_bv.toNat,
                q = uip_lit.toNat ∨ ∃ m < s_u.core.trail_end,
                  (s_u.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                  (s_u.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl) ∧
              uip_lit.toNat ∈ fullArenaClauseLitsCore s_u.core rsn_bv.toNat)) ?_ ?_
        · rintro _ ⟨rsn_bv, ⟨⟩⟩ m_r ⟨rfl, hrsn_ne, hrsn_prop⟩
          have hte_lt : s_u.core.trail_end < c.max_vars := by
            have h1 := hu_sparse.2.1.trail_end_lt_of_unassigned (hcv_eq ▸ huip_lt) huip_z
            have := hcl.cur_vars_le; dsimp only [s_u] at h1 ⊢; omega
          have hml_tr : ((BitVec.ofNat 64 max_lvl).setWidth 32).toNat = max_lvl := by
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : max_lvl < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
          have hml_nz : (BitVec.ofNat 64 max_lvl).setWidth 32 ≠ 0#32 := fun heq => by
            have h0 := congrArg BitVec.toNat heq
            rw [hml_tr, show (0#32 : BitVec 32).toNat = 0 from rfl] at h0; omega
          c0_to_group; c0_call hAsgn
          refine ⟨c, s_u, R, rfl, hu_len, hm_u, ?_⟩
          rw [ite_eq_right (fun h => by
            dsimp only [s_u] at h hte_lt
            simp only [huip_z, ne_eq, not_true_eq_false, or_false] at h
            have := hcv_eq ▸ huip_lt; omega)]
          intro v rsn_let unfl_let flags' unass' phases' m_as hfll hph s_as0 hm_as
          have hrsn_let : rsn_let = rsn_bv := ite_eq_right hml_nz
          have hunfl_let : unfl_let = s_u.core.unflushed := ite_eq_right hml_nz
          c0_clean; c0_to_group
          let s_as : FullState :=
            { s_u with
              core :=
                { s_u.core with
                  vals := (s_u.core.vals.set uip_lit.toNat 1#8).set (uip_lit.toNat ^^^ 1) 0xFF#8
                  flags := flags'
                  lvl := s_u.core.lvl.set (uip_lit.toNat / 2)
                    ((BitVec.ofNat 64 max_lvl).setWidth 32)
                  rsns := s_u.core.rsns.set (uip_lit.toNat / 2) rsn_bv
                  trl := s_u.core.trl.set s_u.core.trail_end uip_lit
                  trail_pos := s_u.core.trail_pos.set (uip_lit.toNat / 2)
                    (BitVec.ofNat 32 s_u.core.trail_end)
                  trail_end := s_u.core.trail_end + 1
                  unassigned := unass', unflushed := s_u.core.unflushed }
              scratch := { s_u.scratch with phases := phases' } }
          have hml_bv : (BitVec.ofNat 64 max_lvl).setWidth 32 = BitVec.ofNat 32 max_lvl :=
            BitVec.eq_of_toNat_eq (by rw [hml_tr, Proof.Spec.bv32_ofNat_toNat (by omega)])
          have hsc_as : s_as.scratch.LengthsOk c := { hu_len.scratch_ok with phases_len := hph }
          have ⟨has_len, has_w⟩ := chronoAssign_preserves_fullWitness hu_sparse.2.1 hu_len hsc_as
            (rsn := rsn_bv) (unassigned' := unass') (unflushed' := s_u.core.unflushed)
            hfll (hcv_eq ▸ huip_lt) huip_z hmax_le (fun _ => hrsn_ne)
            (fun h0 => absurd h0 (by omega))
            (fun _ _ => by
              split
              · rename_i hbin; rw [ite_eq_left hbin] at hrsn_prop; exact hrsn_prop
              · rename_i hnbin; rw [ite_eq_right hnbin] at hrsn_prop
                exact ⟨hrsn_prop.1, hrsn_prop.2.1, hrsn_prop.2.2.1⟩)
            (fun _ _ hzero => by
              rw [ite_eq_right (fun h => absurd hzero h)] at hrsn_prop; exact hrsn_prop.2.2.2)
          have hm_as' : (FullMem c s_as ⋆ R) m_as := by
            simpa only [s_as, s_as0, v, hrsn_let, hunfl_let] using hm_as
          have hmne0 : max_lvl ≠ 0 := by omega
          have has_sparse : FullSparseInvW c F0 F_cur s_as :=
            ⟨by simpa [s_as, hml_bv, hmne0] using has_len,
             by simpa [s_as, hml_bv, hmne0] using has_w,
             hu_sparse.2.2.1, hu_sparse.2.2.2.1, hu_sparse.2.2.2.2.1, hu_sparse.2.2.2.2.2⟩
          have htmp_as_lt : ∀ k < s_as.core.tmp_len,
              (s_as.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk => by
            simpa only [s_as, s_u, htmp_eq, htlen_eq] using
              htmp_lt k (by simpa [s_as, s_u, htlen_eq] using hk)
          c0_call hEsub
          refine ⟨c, F0, F_cur, s_as, R, rfl, has_sparse, htmp_as_lt, ?_, hm_as', ?_⟩
          · intro _
            by_cases hfe : new_ref64 = 0xFFFFFFFE#64
            · subst hfe; exfalso; have : (0xFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 32 - 2 := rfl
              omega
            · simp only [hfe, ↓reduceIte] at hnr_ok
              change new_ref64.toNat ∈ fullArenaClauseRefs s_u
              rw [hrefs_u]; exact hnr_ok.2.1
          · intro ar' ag' _nr' sc' m_fin _ hfin_sparse hws1' hws2' hm_fin
            c0_steps
            exact hQ 1#64 _ m_fin hfin_sparse.1 (Or.inr (Or.inl rfl)) hcv_eq hfuel hprb hmcl
              (hws1'.trans (by simp [s_as, s_u, hws1]))
              (hws2'.trans (by simp [s_as, s_u, hws2])) (fun h => by cases h)
              (fun h => by cases h) (fun _ => ⟨hfin_sparse, hcur_lt⟩) hm_fin
        · intro Jrsn hJrsn; c0_split
          · have hfe : new_ref64 = 0xFFFFFFFE#64 := by assumption
            simp only [hfe, ↓reduceIte] at hnr_ok
            have := hcl.cur_vars_le
            have hwm_lt31 : wm.toNat < 2 ^ 31 - 1 := by omega
            have hmask := bin_rsn_mask_props (l := wm) hwm_lt31
            have h1_lt : 1 < s_u.core.tmp.length := by rw [hu_len.core_ok.tmp_len_arr]; omega
            have htmp1_eq : s_u.core.tmp[1]'h1_lt = wm := Option.some.inj
              (by rw [← List.getElem?_eq_getElem h1_lt, show s_u.core.tmp = tmp_sw from htmp_eq,
                hsw_1])
            c0_steps
            refine wp_load_of (load_full_tmp1 (c := c) (s := s_u) (R := R) h1_lt hm_u) ?_
            rw [htmp1_eq]
            c0_to_group
            refine wp_join_group (ts := [i32]) (fun (jr1, ()) m_j1 =>
                m_j1 = m_u ∧ jr1 ≠ 0xFFFFFFFF#32 ∧
                (if (jr1 &&& 0x80000000#32) ≠ 0#32 then
                  let ot := (jr1 &&& 0x7FFFFFFF#32).toNat
                  ot < 2 * s_u.core.cur_vars ∧
                  (cnfOfClauses F_cur).EntailsClause (cnfClause [uip_lit.toNat, ot]) ∧
                  ∃ m < s_u.core.trail_end, (s_u.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
                    (s_u.core.lvl[ot / 2]?.getD 0#32).toNat ≤ max_lvl
                else
                  jr1.toNat ∈ fullArenaClauseRefsCore s_u.core ∧
                  fullArenaClauseGarbCore s_u.core jr1.toNat = false ∧
                  (∀ q ∈ fullArenaClauseLitsCore s_u.core jr1.toNat,
                    q = uip_lit.toNat ∨ ∃ m < s_u.core.trail_end,
                      (s_u.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                      (s_u.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl) ∧
                  uip_lit.toNat ∈ fullArenaClauseLitsCore s_u.core jr1.toNat)) ?_ ?_
            · rintro _ ⟨jr1, ⟨⟩⟩ m_j1 ⟨rfl, hj1_ne, hrest⟩
              c0_steps; exact hJrsn (jr1, ()) m_j1 ⟨rfl, hj1_ne, hrest⟩
            · intro Js_ml hJs_ml
              c0_split
              · have hv_lt : wm.toNat / 2 < c.max_vars := by omega
                have hidx_o : ((wm >>> 1#32).setWidth 64).toNat = wm.toNat / 2 := by
                  rw [bv_c0_zext32_64]; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                have hbd_rsns : ((wm >>> 1#32).setWidth 64).toNat < s_u.core.rsns.length := by
                  rw [hidx_o, hu_len.core_ok.rsns_len]; exact hv_lt
                c0_hsteps_nogrp
                have htmp1_eq' :
                    s_u.core.tmp[(BitVec.ofNat 64 1).toNat]'(by simpa using h1_lt) = wm :=
                  htmp1_eq
                rw [htmp1_eq']
                refine wp_load_of (FullArenaTactics.c0_load_full_rsns hbd_rsns hm_u) ?_
                let nr_lc := s_u.core.rsns[((wm >>> 1#32).setWidth 64).toNat]'hbd_rsns
                c0_to_group
                refine wp_join_group (ts := [i32]) (fun (jr2, ()) m_j2 =>
                    m_j2 = m_u ∧ jr2 ≠ 0xFFFFFFFF#32 ∧ (jr2 &&& 0x80000000#32) ≠ 0#32 ∧
                    let ot := (jr2 &&& 0x7FFFFFFF#32).toNat
                    ot < 2 * s_u.core.cur_vars ∧
                    (cnfOfClauses F_cur).EntailsClause (cnfClause [uip_lit.toNat, ot]) ∧
                    ∃ m < s_u.core.trail_end, (s_u.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
                      (s_u.core.lvl[ot / 2]?.getD 0#32).toNat ≤ max_lvl) ?_ ?_
                · rintro _ ⟨jr2, ⟨⟩⟩ m_j2 ⟨rfl, hj2_ne, hj2_hi, hrest⟩
                  c0_steps; refine hJs_ml (jr2, ()) m_j2 ⟨rfl, hj2_ne, ?_⟩
                  rw [ite_eq_left hj2_hi]; exact hrest
                · intro Js2 hJs2
                  c0_split
                  · c0_split
                    · have hnr_ne : nr_lc ≠ 0xFFFFFFFF#32 := by assumption
                      have hnr_hi : (nr_lc &&& 0x80000000#32) ≠ 0#32 := by assumption
                      have hw_u := hu_sparse.2.1
                      have h1_sw : 1 < tmp_sw.length := (List.getElem?_eq_some_iff.mp hsw_1).1
                      have hwm_f2 : s_u.core.vals[wm.toNat]?.getD 0#8 = 0xFF#8 := by
                        have hmem : wm.toNat ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
                          rw [List.mem_map]; refine ⟨wm, List.mem_iff_getElem.mpr ⟨1, by
                            rw [List.length_take]; omega, by
                            rw [List.getElem_take]; exact Option.some.inj (by
                              rw [← List.getElem?_eq_getElem h1_sw, hsw_1])⟩, rfl⟩
                        obtain heq_wu | ⟨idx, hidx_u, heq_u, _⟩ := hlow wm.toNat hmem
                        · obtain ⟨m0, hm0, hm0_eq⟩ := hwm_on_bt
                          exact (hw_u.vals_false_iff wm.toNat (hcv_eq ▸ hwm_lt)).mpr
                            ⟨m0, hm0, hm0_eq.1⟩
                        · exact (hw_u.vals_false_iff wm.toNat (hcv_eq ▸ hwm_lt)).mpr
                            ⟨idx, hidx_u, heq_u⟩
                      obtain ⟨m_o, hm_o, hm_oeq⟩ :=
                        (hw_u.vals_false_iff wm.toNat (hcv_eq ▸ hwm_lt)).mp hwm_f2
                      have hvar_o : (s_u.core.trl[m_o]?.getD 0#32).toNat / 2 = wm.toNat / 2 := by
                        rw [hm_oeq, fullInv_var_xor1]
                      have hrsn_get : s_u.core.rsns[(s_u.core.trl[m_o]?.getD 0#32).toNat / 2]?.getD
                          0xFFFFFFFF#32 = nr_lc := by
                        rw [hvar_o, List.getElem?_eq_getElem
                          (by rw [hu_len.core_ok.rsns_len]; exact hv_lt), Option.getD_some]
                        exact Option.some.inj (by
                          rw [← List.getElem?_eq_getElem
                                (by rw [hu_len.core_ok.rsns_len]; exact hv_lt),
                              ← List.getElem?_eq_getElem hbd_rsns, hidx_o])
                      have hinv_r := hw_u.reason_inv m_o hm_o (by rw [hrsn_get]; exact hnr_ne)
                      rw [hrsn_get, ite_eq_left (fun h => absurd h hnr_hi)] at hinv_r
                      obtain ⟨hot_lt, hent_ot, m_t, hm_t, hmt_eq, hot_lv⟩ := hinv_r
                      have hwm_lv_le :
                          (s_u.core.lvl[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
                        obtain ⟨_, _, _, hwm_lv⟩ := hwm_on_bt; exact hwm_lv
                      have htrl_lv_le :
                          (s_u.core.lvl[(s_u.core.trl[m_o]?.getD 0#32).toNat / 2]?.getD
                          0#32).toNat ≤ max_lvl := by rwa [hvar_o]
                      have hent_res : (cnfOfClauses F_cur).EntailsClause
                          (cnfClause [uip_lit.toNat, (nr_lc &&& 0x7FFFFFFF#32).toNat]) :=
                        s13_bin_resolve (by simpa [hm_oeq] using hent_ot)
                          (entails_of_mem_or_false hnr_ok fun l hl => Or.inl (by
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
                            rcases hl with rfl | rfl <;> simp))
                      c0_steps
                      exact hJs2 (nr_lc, ()) m_u ⟨rfl, hnr_ne, hnr_hi, hot_lt, hent_res, m_t,
                        Nat.lt_trans hm_t hm_o, hmt_eq, Nat.le_trans hot_lv htrl_lv_le⟩
                    · c0_steps; refine hJs2 ((wm &&& 0x7FFFFFFF#32) ||| 0x80000000#32, ()) m_u
                        ⟨rfl, hmask.1, hmask.2.1, ?_⟩
                      rw [hmask.2.2]; exact ⟨hcv_eq ▸ hwm_lt, hnr_ok, hwm_on_bt⟩
                  · c0_steps; refine hJs2 ((wm &&& 0x7FFFFFFF#32) ||| 0x80000000#32, ()) m_u
                      ⟨rfl, hmask.1, hmask.2.1, ?_⟩
                    rw [hmask.2.2]; exact ⟨hcv_eq ▸ hwm_lt, hnr_ok, hwm_on_bt⟩
          · have hne_fe : new_ref64 ≠ 0xFFFFFFFE#64 := by assumption
            simp only [hne_fe, ↓reduceIte] at hnr_ok
            obtain ⟨hlt31, href, hng, hlits_sub, huip_in⟩ := hnr_ok
            have hnr_bv := s13_nat_lt31_bv32_msb0 hlt31
            rw [BitVec.eq_of_toNat_eq (Proof.Spec.bv64_ofNat_toNat new_ref64.isLt)] at hnr_bv
            c0_steps
            refine hJrsn (new_ref64.setWidth 32, ()) m_u ⟨rfl, hnr_bv.2.1, ?_⟩
            rw [ite_eq_right (fun h => absurd hnr_bv.2.2 h), hnr_bv.1]
            obtain ⟨hgu, hlu⟩ := hprops_u new_ref64.toNat href
            exact ⟨by change _ ∈ fullArenaClauseRefs s_u; rw [hrefs_u]; exact href,
              hgu.trans hng,
              fun q hq => hlow q (hlits_sub q (by
                change q ∈ fullArenaClauseLits s_ac _; rw [← hlu]; exact hq)),
              by change uip_lit.toNat ∈ fullArenaClauseLits s_u _; rw [hlu]; exact huip_in⟩
      · intro Ju hJu; c0_split
        · have hne_fe : new_ref64 ≠ 0xFFFFFFFE#64 := by assumption
          simp only [hne_fe, ↓reduceIte] at hnr_ok
          obtain ⟨_, href, _, _, _⟩ := hnr_ok
          c0_split
          · have hnr_ar : new_ref64.toNat < s_ac.core.arena.length := by
              have hwf := hac_sparse.2.1.arena.refs_wf new_ref64.toNat href
              have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
            have hhdr_eq : s_ac.core.arena[new_ref64.toNat]'hnr_ar =
                fullArenaHdr s_ac new_ref64.toNat := by
              unfold fullArenaHdr fullArenaHdrCore
              rw [List.getElem?_eq_getElem hnr_ar, Option.getD_some]
            have hmask31 : ((31 : BitVec 32) <<< (27 : BitVec 32)) = 0xF8000000#32 := by decide
            have hmask31n : ((31 : BitVec 32) <<< (27 : Nat)) = 0xF8000000#32 := by decide
            c0_steps
            refine wp_load_of (FullArenaTactics.load_full_arena_ptr hm_ac) ?_
            c0_steps
            obtain ⟨hu_sp, hrefs_u, hprops_u⟩ :=
              s13_orUsed31_preserves_fullSparseW hac_sparse href
            exact hJu () m ⟨_, hu_sp, hrefs_u, hprops_u,
              by simpa only [hhdr_eq, hmask31, hmask31n] using hm⟩
          · c0_steps; exact hJu () m_ac ⟨s_ac.core.arena, hac_sparse, rfl,
              fun _ _ => ⟨rfl, rfl⟩, hm_ac⟩
        · c0_steps; exact hJu () m_ac ⟨s_ac.core.arena, hac_sparse, rfl,
            fun _ _ => ⟨rfl, rfl⟩, hm_ac⟩

end LeanQbe.T.Examples.Kissat.Proof.Learn

end
