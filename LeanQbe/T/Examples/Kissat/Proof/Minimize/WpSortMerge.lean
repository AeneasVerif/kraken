/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpSortSteps
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Rules

/-!
# Bottom-Up Merge-Sort Fallback WP for `full_sort_tmp`

WP of the bottom-up merge-sort fallback phase `s7SortMergeExpr` of
`Src.Minimize.full_sort_tmp_body`: `tmp[1..tlen)` is a permutation of the input slice, sorted by
level (`lvl[x / 2]`), with `tmp[0]` untouched and `wsort` used as scratch.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Minimize.FullMinTactics
open Kraken.Bedrock2.Test

private theorem s7_get_tmp {st s : FullState} {t : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := t }) {i : Nat} (hi : i < t.length) :
    st.core.tmp[i]'(by rw [hc]; exact hi) = t[i]'hi := by
  have h : st.core.tmp = t := by rw [hc]
  cases h; rfl

private theorem s7_get_wsort {st s : FullState} {ws : List (BitVec 32)}
    (hs : st.scratch = { s.scratch with wsort := ws }) {i : Nat} (hi : i < ws.length) :
    st.scratch.wsort[i]'(by rw [hs]; exact hi) = ws[i]'hi := by
  have h : st.scratch.wsort = ws := by rw [hs]
  cases h; rfl

private theorem s7_get_lvl_of {st s : FullState} {t : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := t }) {i j : Nat} (hi : i < st.core.lvl.length)
    (hij : i = j) (hj : j < s.core.lvl.length) :
    st.core.lvl[i]'hi = s.core.lvl[j]'hj := by
  subst hij; simp only [hc]

private theorem s7_lshr1 (v : BitVec 32) :
    (v.setWidth 64 >>> ((BitVec.signExtend 64 1#32).toNat % 64)).toNat =
      v.toNat / 2 := by c0_bound

private theorem s7_lshr1_one (v : BitVec 32) :
    (v.setWidth 64 >>> (1 : Nat)).toNat = v.toNat / 2 := by c0_bound

private theorem s7_st_upd_tmp {st s : FullState} {t : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := t }) {i : Nat} {v : BitVec 32} :
    ({ st with core := { st.core with tmp := st.core.tmp.set i v } }).core =
      { s.core with tmp := t.set i v } := by
  rw [hc]

private theorem s7_st_upd_wsort {st s : FullState} {ws : List (BitVec 32)}
    (hs : st.scratch = { s.scratch with wsort := ws }) {i : Nat} {v : BitVec 32} :
    ({ st with scratch := { st.scratch with wsort := st.scratch.wsort.set i v } }).scratch =
      { s.scratch with wsort := ws.set i v } := by
  rw [hs]

/-! ## 1. Pure Helpers: Level Key, Merge Invariant, Run Arithmetic -/

/-- Level key of the literal stored at index `i` of `xs`. -/
private def s7kAt (lvl xs : List (BitVec 32)) (i : Nat) : Nat :=
  (lvl[(xs[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

private theorem s7kAt_of_eq {lvl xs ys : List (BitVec 32)} {i j : Nat}
    (h : xs[i]? = ys[j]?) : s7kAt lvl xs i = s7kAt lvl ys j := by
  unfold s7kAt; rw [h]

private theorem s7kAt_eq {lvl xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length)
    (hl : (xs[i]'hi).toNat / 2 < lvl.length) :
    s7kAt lvl xs i = (lvl[(xs[i]'hi).toNat / 2]'hl).toNat := by
  unfold s7kAt
  rw [List.getElem?_eq_getElem hi, Option.getD_some, List.getElem?_eq_getElem hl,
    Option.getD_some]

private theorem s7Slice_congr_rng {α : Type _} {xs ys : List α} {lo hi : Nat}
    (hx : hi ≤ xs.length) (hy : hi ≤ ys.length)
    (heq : ∀ q, lo ≤ q → q < hi → xs[q]? = ys[q]?) :
    m7Slice xs lo hi = m7Slice ys lo hi := by
  apply List.ext_getElem
  · simp [m7Slice_length]; omega
  · intro k hk1 hk2
    rw [m7Slice_getElem, m7Slice_getElem]
    rw [m7Slice_length] at hk1
    have hq := heq (lo + k) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
    exact Option.some.inj hq

/-- Shared merge / tail invariant on `(i0, i1, dst)` for merging the sorted runs
`t[lo, mid)` and `t[mid, hi)` into the scratch `h[lo, dst)`. -/
private def s7MInv (lvl t h : List (BitVec 32)) (lo mid hi i0 i1 dst : Nat) : Prop :=
  lo ≤ i0 ∧ i0 ≤ mid ∧ mid ≤ i1 ∧ i1 ≤ hi ∧ dst = i0 + (i1 - mid) ∧
  (m7Slice h lo dst).Perm (m7Slice t lo i0 ++ m7Slice t mid i1) ∧
  (∀ a b, lo ≤ a → a ≤ b → b < dst → s7kAt lvl h a ≤ s7kAt lvl h b) ∧
  (∀ a, lo ≤ a → a < dst →
    (∀ k, i0 ≤ k → k < mid → s7kAt lvl h a ≤ s7kAt lvl t k) ∧
    (∀ k, i1 ≤ k → k < hi → s7kAt lvl h a ≤ s7kAt lvl t k))

private theorem s7MInv_init (lvl t h : List (BitVec 32)) {lo mid hi : Nat}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) : s7MInv lvl t h lo mid hi lo mid lo := by
  refine ⟨Nat.le_refl _, h1, Nat.le_refl _, h2, by omega, ?_, fun a b ha hab hb => by omega,
    fun a ha hb => absurd hb (by omega)⟩
  rw [m7Slice_nil _ (Nat.le_refl _), m7Slice_nil _ (Nat.le_refl _), m7Slice_nil _ (Nat.le_refl _)]
  exact List.Perm.refl _

private theorem s7MInv_step0 {lvl t h : List (BitVec 32)} {lo mid hi i0 i1 dst : Nat}
    {v : BitVec 32} (hinv : s7MInv lvl t h lo mid hi i0 i1 dst) (hi0 : i0 < mid)
    (hht : hi ≤ t.length) (hhh : hi ≤ h.length) (hv : t[i0]? = some v)
    (hr0 : ∀ a b, lo ≤ a → a ≤ b → b < mid → s7kAt lvl t a ≤ s7kAt lvl t b)
    (hr1 : ∀ a b, mid ≤ a → a ≤ b → b < hi → s7kAt lvl t a ≤ s7kAt lvl t b)
    (hle : i1 < hi → s7kAt lvl t i0 ≤ s7kAt lvl t i1) :
    s7MInv lvl t (h.set dst v) lo mid hi (i0 + 1) i1 (dst + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, hperm, hsort, hbd⟩ := hinv
  have hdst : dst < hi := by omega
  have hset_self : (h.set dst v)[dst]? = some v := by
    rw [List.getElem?_set_self (by omega)]
  have hkd : s7kAt lvl (h.set dst v) dst = s7kAt lvl t i0 :=
    s7kAt_of_eq (by rw [hset_self, hv])
  have hkne : ∀ a, a ≠ dst → s7kAt lvl (h.set dst v) a = s7kAt lvl h a := fun a ha =>
    s7kAt_of_eq (List.getElem?_set_ne (Ne.symm ha))
  refine ⟨by omega, by omega, h3, h4, by omega, ?_, ?_, ?_⟩
  · have hv' : t[i0]'(by omega) = v := by
      rw [List.getElem?_eq_getElem (by omega)] at hv; exact Option.some.inj hv
    rw [m7Slice_set_end _ _ (by omega) (by omega), m7Slice_append_succ _ h1 (by omega), hv']
    refine (hperm.append_right [v]).trans ?_
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  · intro a b ha hab hb
    by_cases hbd' : b = dst
    · rw [hbd', hkd]
      by_cases had : a = dst
      · rw [had, hkd]; exact Nat.le_refl _
      · rw [hkne a had]; exact (hbd a ha (by omega)).1 i0 (Nat.le_refl _) hi0
    · rw [hkne a (by omega), hkne b hbd']; exact hsort a b ha hab (by omega)
  · intro a ha hadst
    by_cases had : a = dst
    · rw [had, hkd]
      exact ⟨fun k hk1 hk2 => hr0 i0 k h1 (by omega) hk2,
        fun k hk1 hk2 => Nat.le_trans (hle (by omega)) (hr1 i1 k h3 hk1 hk2)⟩
    · rw [hkne a had]
      have hb := hbd a ha (by omega)
      exact ⟨fun k hk1 hk2 => hb.1 k (by omega) hk2, hb.2⟩

private theorem s7MInv_step1 {lvl t h : List (BitVec 32)} {lo mid hi i0 i1 dst : Nat}
    {v : BitVec 32} (hinv : s7MInv lvl t h lo mid hi i0 i1 dst) (hi1 : i1 < hi)
    (hht : hi ≤ t.length) (hhh : hi ≤ h.length) (hv : t[i1]? = some v)
    (hr0 : ∀ a b, lo ≤ a → a ≤ b → b < mid → s7kAt lvl t a ≤ s7kAt lvl t b)
    (hr1 : ∀ a b, mid ≤ a → a ≤ b → b < hi → s7kAt lvl t a ≤ s7kAt lvl t b)
    (hle : i0 < mid → s7kAt lvl t i1 ≤ s7kAt lvl t i0) :
    s7MInv lvl t (h.set dst v) lo mid hi i0 (i1 + 1) (dst + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, hperm, hsort, hbd⟩ := hinv
  have hdst : dst < hi := by omega
  have hset_self : (h.set dst v)[dst]? = some v := by
    rw [List.getElem?_set_self (by omega)]
  have hkd : s7kAt lvl (h.set dst v) dst = s7kAt lvl t i1 :=
    s7kAt_of_eq (by rw [hset_self, hv])
  have hkne : ∀ a, a ≠ dst → s7kAt lvl (h.set dst v) a = s7kAt lvl h a := fun a ha =>
    s7kAt_of_eq (List.getElem?_set_ne (Ne.symm ha))
  refine ⟨h1, h2, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · have hv' : t[i1]'(by omega) = v := by
      rw [List.getElem?_eq_getElem (by omega)] at hv; exact Option.some.inj hv
    rw [m7Slice_set_end _ _ (by omega) (by omega), m7Slice_append_succ _ h3 (by omega), hv']
    rw [← List.append_assoc]
    exact hperm.append_right [v]
  · intro a b ha hab hb
    by_cases hbd' : b = dst
    · rw [hbd', hkd]
      by_cases had : a = dst
      · rw [had, hkd]; exact Nat.le_refl _
      · rw [hkne a had]; exact (hbd a ha (by omega)).2 i1 (Nat.le_refl _) hi1
    · rw [hkne a (by omega), hkne b hbd']; exact hsort a b ha hab (by omega)
  · intro a ha hadst
    by_cases had : a = dst
    · rw [had, hkd]
      exact ⟨fun k hk1 hk2 => Nat.le_trans (hle (by omega)) (hr0 i0 k h1 hk1 hk2),
        fun k hk1 hk2 => hr1 i1 k h3 (by omega) hk2⟩
    · rw [hkne a had]
      have hb := hbd a ha (by omega)
      exact ⟨hb.1, fun k hk1 hk2 => hb.2 k (by omega) hk2⟩

private theorem s7MInv_final {lvl t h : List (BitVec 32)} {lo mid hi dst : Nat}
    (hinv : s7MInv lvl t h lo mid hi mid hi dst) (hht : hi ≤ t.length) :
    dst = hi ∧ (m7Slice h lo hi).Perm (m7Slice t lo hi) ∧
    (∀ a b, lo ≤ a → a ≤ b → b < hi → s7kAt lvl h a ≤ s7kAt lvl h b) := by
  obtain ⟨h1, h2, h3, h4, h5, hperm, hsort, _⟩ := hinv
  have hd : dst = hi := by omega
  subst hd
  refine ⟨rfl, ?_, hsort⟩
  rw [← m7Slice_append_slice t h1 h3 hht]
  exact hperm

private theorem s7_div_eq {m w q : Nat} (h1 : q * w ≤ m) (h2 : m < q * w + w) :
    m / w = q :=
  Nat.div_eq_of_lt_le h1 (by rw [Nat.add_mul, Nat.one_mul]; exact h2)

/-- The two halves `[lo, mid)` / `[mid, hi)` of a `2w`-block are sorted `w`-runs. -/
private theorem s7_pass_runs {lvl t : List (BitVec 32)} {N w lo B : Nat}
    (hlo : lo = 1 + 2 * (B * w))
    (hsuf : ∀ i j, lo ≤ i → i ≤ j → j < N → (i - 1) / w = (j - 1) / w →
      s7kAt lvl t i ≤ s7kAt lvl t j) :
    (∀ a b, lo ≤ a → a ≤ b → b < min (lo + w) N → s7kAt lvl t a ≤ s7kAt lvl t b) ∧
    (∀ a b, min (lo + w) N ≤ a → a ≤ b → b < min (lo + 2 * w) N →
      s7kAt lvl t a ≤ s7kAt lvl t b) := by
  have e1 : (2 * B) * w = 2 * (B * w) := Nat.mul_assoc 2 B w
  have e2 : (2 * B + 1) * w = 2 * (B * w) + w := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  constructor
  · intro a b ha hab hb
    have hb' : b < lo + w := by omega
    refine hsuf a b ha hab (by omega) ?_
    rw [s7_div_eq (q := 2 * B) (by omega) (by omega),
      s7_div_eq (q := 2 * B) (by omega) (by omega)]
  · intro a b ha hab hb
    have hlt : lo + w < N := by
      rcases Nat.lt_or_ge (lo + w) N with h | h
      · exact h
      · rw [Nat.min_eq_right h] at ha; omega
    rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at ha
    have hb' : b < lo + 2 * w := by omega
    refine hsuf a b (by omega) hab (by omega) ?_
    rw [s7_div_eq (q := 2 * B + 1) (by omega) (by omega),
      s7_div_eq (q := 2 * B + 1) (by omega) (by omega)]

/-- After merging the block `[lo, hi)`, the prefix `[1, hi)` has sorted `2w`-runs and the
suffix `[hi, N)` keeps its sorted `w`-runs. -/
private theorem s7_pass_step {lvl t tc : List (BitVec 32)} {N w lo B : Nat}
    (hw : 1 ≤ w) (hlo : lo = 1 + 2 * (B * w))
    (hpre : ∀ i j, 1 ≤ i → i ≤ j → j < lo → (i - 1) / (2 * w) = (j - 1) / (2 * w) →
      s7kAt lvl t i ≤ s7kAt lvl t j)
    (hsuf : ∀ i j, lo ≤ i → i ≤ j → j < N → (i - 1) / w = (j - 1) / w →
      s7kAt lvl t i ≤ s7kAt lvl t j)
    (hout : ∀ q, (q < lo ∨ min (lo + 2 * w) N ≤ q) → tc[q]? = t[q]?)
    (hsort : ∀ a b, lo ≤ a → a ≤ b → b < min (lo + 2 * w) N →
      s7kAt lvl tc a ≤ s7kAt lvl tc b) :
    (∀ i j, 1 ≤ i → i ≤ j → j < min (lo + 2 * w) N →
      (i - 1) / (2 * w) = (j - 1) / (2 * w) → s7kAt lvl tc i ≤ s7kAt lvl tc j) ∧
    (∀ i j, min (lo + 2 * w) N ≤ i → i ≤ j → j < N → (i - 1) / w = (j - 1) / w →
      s7kAt lvl tc i ≤ s7kAt lvl tc j) := by
  have e3 : B * (2 * w) = 2 * (B * w) := Nat.mul_left_comm B 2 w
  have hw2 : 0 < 2 * w := by omega
  constructor
  · intro i j hi hij hj hdiv
    rcases Nat.lt_or_ge j lo with hjlo | hjlo
    · rw [s7kAt_of_eq (hout i (Or.inl (by omega))), s7kAt_of_eq (hout j (Or.inl hjlo))]
      exact hpre i j hi hij hjlo hdiv
    · rcases Nat.lt_or_ge i lo with hilo | hilo
      · have hA : (i - 1) / (2 * w) < B := by
          rw [Nat.div_lt_iff_lt_mul hw2]; omega
        have hB : B ≤ (j - 1) / (2 * w) := by
          rw [Nat.le_div_iff_mul_le hw2]; omega
        omega
      · exact hsort i j hilo hij hj
  · intro i j hi hij hj hdiv
    rw [s7kAt_of_eq (hout i (Or.inr hi)), s7kAt_of_eq (hout j (Or.inr (by omega)))]
    exact hsuf i j (by omega) hij hj hdiv

private theorem s7_shl1_bv64 {w : Nat} :
    BitVec.ofNat 64 w <<< (1 : Nat) = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.pow_one]
  omega

/-! ## 2. Sub-AST Abbreviations (`rfl`-identical sub-terms of `s7SortMergeExpr`) -/

/-- Copy-back loop `tmp[lo, hi) := sh[lo, hi)`, then `lo := hi`. -/
abbrev s7CopyExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (lo hi pTmp pWsort : Val i64) (JL : Cont [i64]) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun JC =>
    .cons (fun xc =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var xc.1, Arg.var hi, ())) fun c5 =>
      .jnz (Arg.var c5.1)
        (.let_ (Op.mk (.mul i64) (Arg.var xc.1, Arg.imm 4, ())) fun h1 =>
        .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var h1.1, ())) fun h2 =>
        .let_ (Op.mk (.mul i64) (Arg.var xc.1, Arg.imm 4, ())) fun h3 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var h3.1, ())) fun h4 =>
        .load i32 (Arg.var h4.1) fun v2 =>
        .store (t := i32) (Arg.var v2) (Arg.var h2.1) (
          .let_ (Op.mk (.add i64) (Arg.var xc.1, Arg.imm 1, ())) fun h5 =>
          .jump JC.1 (Arg.var h5.1, ())))
        (.jump JL (Arg.var hi, ())))
    .nil)
    (fun J => .jump J.1 (Arg.var lo, ()))

/-- Tail loop draining the second run `t[i1, hi)`, then the copy-back. -/
abbrev s7Tail1Expr {Val : Ty → Type} {Cont : List Ty → Type}
    (i1 dst lo hi pTmp pWsort : Val i64) (JL : Cont [i64]) : Expr Val Cont [] :=
  .group (sig := [[i64, i64]]) (fun JT1 =>
    .cons (fun t1 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var t1.1, Arg.var hi, ())) fun c4 =>
      .jnz (Arg.var c4.1)
        (.let_ (Op.mk (.mul i64) (Arg.var t1.2.1, Arg.imm 4, ())) fun g1 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var g1.1, ())) fun g2 =>
        .let_ (Op.mk (.mul i64) (Arg.var t1.1, Arg.imm 4, ())) fun g3 =>
        .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var g3.1, ())) fun g4 =>
        .load i32 (Arg.var g4.1) fun v1 =>
        .store (t := i32) (Arg.var v1) (Arg.var g2.1) (
          .let_ (Op.mk (.add i64) (Arg.var t1.1, Arg.imm 1, ())) fun g5 =>
          .let_ (Op.mk (.add i64) (Arg.var t1.2.1, Arg.imm 1, ())) fun g6 =>
          .jump JT1.1 (Arg.var g5.1, Arg.var g6.1, ())))
        (s7CopyExpr lo hi pTmp pWsort JL))
    .nil)
    (fun J => .jump J.1 (Arg.var i1, Arg.var dst, ()))

/-- Tail loop draining the first run `t[i0, mid)`, then the second tail. -/
abbrev s7Tail0Expr {Val : Ty → Type} {Cont : List Ty → Type}
    (i0 i1 dst lo mid hi pTmp pWsort : Val i64) (JL : Cont [i64]) : Expr Val Cont [] :=
  .group (sig := [[i64, i64]]) (fun JT0 =>
    .cons (fun t0 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var t0.1, Arg.var mid, ())) fun c3 =>
      .jnz (Arg.var c3.1)
        (.let_ (Op.mk (.mul i64) (Arg.var t0.2.1, Arg.imm 4, ())) fun f1 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var f1.1, ())) fun f2 =>
        .let_ (Op.mk (.mul i64) (Arg.var t0.1, Arg.imm 4, ())) fun f3 =>
        .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var f3.1, ())) fun f4 =>
        .load i32 (Arg.var f4.1) fun v0 =>
        .store (t := i32) (Arg.var v0) (Arg.var f2.1) (
          .let_ (Op.mk (.add i64) (Arg.var t0.1, Arg.imm 1, ())) fun f5 =>
          .let_ (Op.mk (.add i64) (Arg.var t0.2.1, Arg.imm 1, ())) fun f6 =>
          .jump JT0.1 (Arg.var f5.1, Arg.var f6.1, ())))
        (s7Tail1Expr i1 t0.2.1 lo hi pTmp pWsort JL))
    .nil)
    (fun J => .jump J.1 (Arg.var i0, Arg.var dst, ()))

/-- Merge loop over `(i0, i1, dst)` of the block `[lo, mid) ∪ [mid, hi)`. -/
abbrev s7MergeExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (lo mid hi pTmp pLvl pWsort : Val i64) (JL : Cont [i64]) : Expr Val Cont [] :=
  .group (sig := [[i64, i64, i64]]) (fun JM =>
    .cons (fun xm =>
      .group (sig := [[]]) (fun _ =>
        .cons (fun _ => s7Tail0Expr xm.1 xm.2.1 xm.2.2.1 lo mid hi pTmp pWsort JL) .nil)
        (fun JA =>
          .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var xm.1, Arg.var mid, ())) fun c6 =>
          .jnz (Arg.var c6.1)
            (.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var xm.2.1, Arg.var hi, ())) fun c7 =>
            .jnz (Arg.var c7.1)
              (.group (sig := [[i64, i64]]) (fun _ =>
                .cons (fun xu =>
                  .let_ (Op.mk (.add i64) (Arg.var xm.2.2.1, Arg.imm 1, ())) fun k1 =>
                  .jump JM.1 (Arg.var xu.1, Arg.var xu.2.1, Arg.var k1.1, ()))
                .nil)
                (fun JU =>
                  .let_ (Op.mk (.mul i64) (Arg.var xm.1, Arg.imm 4, ())) fun l1 =>
                  .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var l1.1, ())) fun l2 =>
                  .load i32 (Arg.var l2.1) fun va =>
                  .let_ (Op.mk (.zext 32 64) (Arg.var va, ())) fun l3 =>
                  .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun l4 =>
                  .let_ (Op.mk (.lshr i64) (Arg.var l3.1, Arg.var l4.1, ())) fun l5 =>
                  .let_ (Op.mk (.mul i64) (Arg.var l5.1, Arg.imm 4, ())) fun l6 =>
                  .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var l6.1, ())) fun l7 =>
                  .load i32 (Arg.var l7.1) fun vla =>
                  .let_ (Op.mk (.mul i64) (Arg.var xm.2.1, Arg.imm 4, ())) fun m1 =>
                  .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var m1.1, ())) fun m2 =>
                  .load i32 (Arg.var m2.1) fun vb =>
                  .let_ (Op.mk (.zext 32 64) (Arg.var vb, ())) fun m3 =>
                  .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun m4 =>
                  .let_ (Op.mk (.lshr i64) (Arg.var m3.1, Arg.var m4.1, ())) fun m5 =>
                  .let_ (Op.mk (.mul i64) (Arg.var m5.1, Arg.imm 4, ())) fun m6 =>
                  .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var m6.1, ())) fun m7 =>
                  .load i32 (Arg.var m7.1) fun vlb =>
                  .let_ (Op.mk (.cmp .ule i32 .bool rfl) (Arg.var vla, Arg.var vlb, ())) fun c8 =>
                  .jnz (Arg.var c8.1)
                    (.let_ (Op.mk (.mul i64) (Arg.var xm.2.2.1, Arg.imm 4, ())) fun n1 =>
                    .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var n1.1, ())) fun n2 =>
                    .let_ (Op.mk (.mul i64) (Arg.var xm.1, Arg.imm 4, ())) fun n3 =>
                    .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var n3.1, ())) fun n4 =>
                    .load i32 (Arg.var n4.1) fun vc =>
                    .store (t := i32) (Arg.var vc) (Arg.var n2.1) (
                      .let_ (Op.mk (.add i64) (Arg.var xm.1, Arg.imm 1, ())) fun n5 =>
                      .jump JU.1 (Arg.var n5.1, Arg.var xm.2.1, ())))
                    (.let_ (Op.mk (.mul i64) (Arg.var xm.2.2.1, Arg.imm 4, ())) fun o1 =>
                    .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var o1.1, ())) fun o2 =>
                    .let_ (Op.mk (.mul i64) (Arg.var xm.2.1, Arg.imm 4, ())) fun o3 =>
                    .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var o3.1, ())) fun o4 =>
                    .load i32 (Arg.var o4.1) fun vd =>
                    .store (t := i32) (Arg.var vd) (Arg.var o2.1) (
                      .let_ (Op.mk (.add i64) (Arg.var xm.2.1, Arg.imm 1, ())) fun o5 =>
                      .jump JU.1 (Arg.var xm.1, Arg.var o5.1, ())))))
              (.jump JA.1 ()))
            (.jump JA.1 ())))
    .nil)
    (fun J => .jump J.1 (Arg.var lo, Arg.var mid, Arg.var lo, ()))

/-- One `lo`-pass over all `2w`-blocks (`mid` / `hi` computation, merge), then `w := 2w`. -/
abbrev s7PassExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (xw n64 pTmp pLvl pWsort : Val i64) (JW : Cont [i64]) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun JL =>
    .cons (fun xlo =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var xlo.1, Arg.var n64, ())) fun c2 =>
      .jnz (Arg.var c2.1)
        (.group (sig := [[i64]]) (fun _ =>
          .cons (fun xmid =>
            .group (sig := [[i64]]) (fun _ =>
              .cons (fun xhi => s7MergeExpr xlo.1 xmid.1 xhi.1 pTmp pLvl pWsort JL.1) .nil)
              (fun J =>
                .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun q1 =>
                .let_ (Op.mk (.shl i64) (Arg.var xw, Arg.var q1.1, ())) fun q2 =>
                .let_ (Op.mk (.add i64) (Arg.var xlo.1, Arg.var q2.1, ())) fun q3 =>
                .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var q3.1, Arg.var n64, ())) fun c9 =>
                .jnz (Arg.var c9.1)
                  (.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun q4 =>
                  .let_ (Op.mk (.shl i64) (Arg.var xw, Arg.var q4.1, ())) fun q5 =>
                  .let_ (Op.mk (.add i64) (Arg.var xlo.1, Arg.var q5.1, ())) fun q6 =>
                  .jump J.1 (Arg.var q6.1, ()))
                  (.jump J.1 (Arg.var n64, ()))))
          .nil)
          (fun J =>
            .let_ (Op.mk (.add i64) (Arg.var xlo.1, Arg.var xw, ())) fun r1 =>
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var r1.1, Arg.var n64, ())) fun c10 =>
            .jnz (Arg.var c10.1)
              (.let_ (Op.mk (.add i64) (Arg.var xlo.1, Arg.var xw, ())) fun r2 =>
              .jump J.1 (Arg.var r2.1, ()))
              (.jump J.1 (Arg.var n64, ()))))
        (.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun s1 =>
        .let_ (Op.mk (.shl i64) (Arg.var xw, Arg.var s1.1, ())) fun s2 =>
        .jump JW (Arg.var s2.1, ())))
    .nil)
    (fun J => .jump J.1 (Arg.imm 1, ()))

/-- Bottom-up merge-sort fallback phase of `full_sort_tmp`, with `n64 = tlen`,
`nm1 = tlen - 1` and `wsort` (`pWsort`) as merge scratch. -/
abbrev s7SortMergeExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (n64 nm1 pTmp pLvl pWsort : Val i64) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun JW =>
    .cons (fun xw =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var xw.1, Arg.var nm1, ())) fun c1 =>
      .jnz (Arg.var c1.1) (s7PassExpr xw.1 n64 pTmp pLvl pWsort JW.1) (.ret ()))
    .nil)
    (fun J => .jump J.1 (Arg.imm 1, ()))

/-! ## 3. Copy-Back Loop -/

private theorem s7_copy_wp {Γ : Env} {c : FullCfg} {s st0 : FullState} {R : Mem 64 → Prop}
    {m0 : Mem 64} {Q : Post []} {X : XPost} {lo hi : Nat} {t h : List (BitVec 32)}
    {xlo xhi : Val i64} {JL : Cont [i64]}
    (hxlo : xlo = BitVec.ofNat 64 lo) (hxhi : xhi = BitVec.ofNat 64 hi)
    (hlohi : lo ≤ hi) (hhi : hi ≤ c.max_vars)
    (htl : t.length = c.max_vars) (hhl : h.length = 2 * c.max_vars)
    (hc0 : st0.core = { s.core with tmp := t })
    (hs0 : st0.scratch = { s.scratch with wsort := h })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hJL : ∀ st' tc m', st'.core = { s.core with tmp := tc } →
      st'.scratch = { s.scratch with wsort := h } → tc.length = c.max_vars →
      (∀ q, lo ≤ q → q < hi → tc[q]? = h[q]?) →
      (∀ q, (q < lo ∨ hi ≤ q) → tc[q]? = t[q]?) →
      (FullMem c st' ⋆ R) m' → JL (BitVec.ofNat 64 hi, ()) m') :
    wp Γ Q X (s7CopyExpr xlo xhi c.pTmp c.pWsort JL) m0 := by
  subst hxlo hxhi
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ cp st tc, xs.1 = BitVec.ofNat 64 cp ∧ lo ≤ cp ∧ cp ≤ hi ∧ meas = hi - cp ∧
      st.core = { s.core with tmp := tc } ∧ st.scratch = { s.scratch with wsort := h } ∧
      tc.length = c.max_vars ∧ (∀ q, lo ≤ q → q < cp → tc[q]? = h[q]?) ∧
      (∀ q, (q < lo ∨ cp ≤ q) → tc[q]? = t[q]?) ∧ (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro JC meas xs m hIH ⟨cp, st, tc, hxs, hcp1, hcp2, hmeas, hst_c, hst_s, htc_len, hin,
      hout, hm⟩
    rcases xs with ⟨cp_bv, ⟨⟩⟩; dsimp only at hxs; subst hxs
    rw [Blocks.get_here]; c0_hsplit
    · have hcp : cp < hi := by c0_grind
      have hcp_h : (BitVec.ofNat 64 cp).toNat < st.scratch.wsort.length := by
        rw [m7_scr_ws_eq hst_s, hhl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      have hcp_t : (BitVec.ofNat 64 cp).toNat < st.core.tmp.length := by
        rw [m7_core_tmp_eq hst_c, htc_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      c0_hsteps!
      have hidx : (BitVec.ofNat 64 cp).toNat = cp := by c0_bound
      have hgw : st.scratch.wsort[(BitVec.ofNat 64 cp).toNat]'hcp_h = h[cp]'(by omega) := by
        simpa only [hidx] using s7_get_wsort hst_s (i := cp) (by omega)
      have hadd : BitVec.ofNat 64 cp + (1 : BitVec 64) = BitVec.ofNat 64 (cp + 1) := by c0_bound
      rw [hadd]
      let core1 := st.core
      let tmp1 := core1.tmp.set (BitVec.ofNat 64 cp).toNat
        (st.scratch.wsort[(BitVec.ofNat 64 cp).toNat]'hcp_h)
      refine hIH (hi - (cp + 1)) _ _ (by omega) ⟨cp + 1,
        { core := { core1 with tmp := tmp1 }, scratch := st.scratch },
        tc.set cp (h[cp]'(by omega)), rfl,
        by omega, by omega, rfl, ?_, hst_s, by simp [htc_len], ?_, ?_, hm⟩
      · dsimp only [core1, tmp1]
        rw [hgw, hidx]
        exact s7_st_upd_tmp hst_c
      · intro q hq1 hq2
        by_cases hqc : q = cp
        · rw [hqc, List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
        · rw [List.getElem?_set_ne (Ne.symm hqc)]; exact hin q hq1 (by omega)
      · intro q hq; rw [List.getElem?_set_ne (by omega)]; exact hout q (by omega)
    · have hcp : hi ≤ cp := by c0_grind
      c0_hsteps!
      exact hJL st tc m hst_c hst_s htc_len (fun q h1 h2 => hin q h1 (by omega))
        (fun q hq => hout q (by omega)) hm
  · intro J hJ; c0_hsteps!
    exact hJ _ _ _ ⟨lo, st0, t, rfl, Nat.le_refl _, hlohi, rfl, hc0, hs0, htl,
      fun q h1 h2 => by omega, fun q _ => rfl, hm0⟩

/-! ## 4. Tail Loops -/

private theorem s7_tail1_wp {Γ : Env} {c : FullCfg} {s st0 : FullState} {R : Mem 64 → Prop}
    {m0 : Mem 64} {Q : Post []} {X : XPost} {lo mid hi i1 dst : Nat}
    {t h0 : List (BitVec 32)} {xi1 xdst xlo xhi : Val i64} {JL : Cont [i64]}
    (hxi1 : xi1 = BitVec.ofNat 64 i1) (hxdst : xdst = BitVec.ofNat 64 dst)
    (hxlo : xlo = BitVec.ofNat 64 lo) (hxhi : xhi = BitVec.ofNat 64 hi)
    (hhi : hi ≤ c.max_vars)
    (htl : t.length = c.max_vars) (hhl : h0.length = 2 * c.max_vars)
    (hr0 : ∀ a b, lo ≤ a → a ≤ b → b < mid → s7kAt s.core.lvl t a ≤ s7kAt s.core.lvl t b)
    (hr1 : ∀ a b, mid ≤ a → a ≤ b → b < hi → s7kAt s.core.lvl t a ≤ s7kAt s.core.lvl t b)
    (hinv0 : s7MInv s.core.lvl t h0 lo mid hi mid i1 dst)
    (hc0 : st0.core = { s.core with tmp := t })
    (hs0 : st0.scratch = { s.scratch with wsort := h0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hJL : ∀ st' tc h' m', st'.core = { s.core with tmp := tc } →
      st'.scratch = { s.scratch with wsort := h' } → tc.length = c.max_vars →
      h'.length = 2 * c.max_vars → (m7Slice tc lo hi).Perm (m7Slice t lo hi) →
      (∀ q, (q < lo ∨ hi ≤ q) → tc[q]? = t[q]?) →
      (∀ a b, lo ≤ a → a ≤ b → b < hi → s7kAt s.core.lvl tc a ≤ s7kAt s.core.lvl tc b) →
      (FullMem c st' ⋆ R) m' → JL (BitVec.ofNat 64 hi, ()) m') :
    wp Γ Q X (s7Tail1Expr xi1 xdst xlo xhi c.pTmp c.pWsort JL) m0 := by
  subst hxi1 hxdst hxlo hxhi
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ j1 d st h, xs.1 = BitVec.ofNat 64 j1 ∧ xs.2.1 = BitVec.ofNat 64 d ∧ meas = hi - j1 ∧
      s7MInv s.core.lvl t h lo mid hi mid j1 d ∧
      st.core = { s.core with tmp := t } ∧ st.scratch = { s.scratch with wsort := h } ∧
      h.length = 2 * c.max_vars ∧ (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro JT meas xs m hIH ⟨j1, d, st, h, hx1, hx2, hmeas, hinv, hst_c, hst_s, hhl', hm⟩
    have ⟨hlm, _, hmj, hjhi, hd, _⟩ := hinv
    rcases xs with ⟨j1_bv, d_bv, ⟨⟩⟩; dsimp only at hx1 hx2; subst hx1 hx2
    rw [Blocks.get_here]; c0_hsplit
    · have hj : j1 < hi := by c0_grind
      have hj_t : (BitVec.ofNat 64 j1).toNat < st.core.tmp.length := by
        rw [m7_core_tmp_eq hst_c, htl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      have hd_h : (BitVec.ofNat 64 d).toNat < st.scratch.wsort.length := by
        rw [m7_scr_ws_eq hst_s, hhl', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      c0_hsteps!
      have hj_i : (BitVec.ofNat 64 j1).toNat = j1 := by c0_bound
      have hd_i : (BitVec.ofNat 64 d).toNat = d := by c0_bound
      have hgt : st.core.tmp[(BitVec.ofNat 64 j1).toNat]'hj_t = t[j1]'(by omega) := by
        simpa only [hj_i] using s7_get_tmp hst_c (i := j1) (by omega)
      have ha1 : BitVec.ofNat 64 j1 + (1 : BitVec 64) = BitVec.ofNat 64 (j1 + 1) := by c0_bound
      have ha2 : BitVec.ofNat 64 d + (1 : BitVec 64) = BitVec.ofNat 64 (d + 1) := by c0_bound
      rw [ha1, ha2]
      let scr1 := st.scratch
      let ws1 := scr1.wsort.set (BitVec.ofNat 64 d).toNat
        (st.core.tmp[(BitVec.ofNat 64 j1).toNat]'hj_t)
      refine hIH (hi - (j1 + 1)) _ _ (by omega) ⟨j1 + 1, d + 1,
        { core := st.core, scratch := { scr1 with wsort := ws1 } },
        h.set d (t[j1]'(by omega)), rfl, rfl, rfl, ?_, hst_c, ?_, by simp [hhl'], hm⟩
      · exact s7MInv_step1 hinv hj (by omega) (by omega) (List.getElem?_eq_getElem (by omega)) hr0
          hr1 (fun h' => absurd h' (Nat.lt_irrefl _))
      · simpa only [scr1, ws1, hd_i, hgt] using s7_st_upd_wsort hst_s
          (i := (BitVec.ofNat 64 d).toNat) (v := st.core.tmp[(BitVec.ofNat 64 j1).toNat]'hj_t)
    · have hj : hi ≤ j1 := by c0_grind
      have hjeq : j1 = hi := by omega
      rw [hjeq] at hinv
      obtain ⟨_, hperm, hsort⟩ := s7MInv_final hinv (by omega)
      refine s7_copy_wp (xlo := BitVec.ofNat 64 lo) (xhi := BitVec.ofNat 64 hi) rfl rfl
        (by omega) hhi htl hhl' hst_c hst_s hm ?_
      intro st' tc m' hc' hs' htc hin hout hm'
      refine hJL st' tc h m' hc' hs' htc hhl' ?_ hout ?_ hm'
      · rw [s7Slice_congr_rng (by omega) (by omega) hin]; exact hperm
      · intro a b ha hab hb
        rw [s7kAt_of_eq (hin a ha (by omega)), s7kAt_of_eq (hin b (by omega) hb)]
        exact hsort a b ha hab hb
  · intro J hJ; c0_hsteps!
    exact hJ _ _ _ ⟨i1, dst, st0, h0, rfl, rfl, rfl, hinv0, hc0, hs0, hhl, hm0⟩

private theorem s7_tail0_wp {Γ : Env} {c : FullCfg} {s st0 : FullState} {R : Mem 64 → Prop}
    {m0 : Mem 64} {Q : Post []} {X : XPost} {lo mid hi i0 i1 dst : Nat}
    {t h0 : List (BitVec 32)} {xi0 xi1 xdst xlo xmid xhi : Val i64} {JL : Cont [i64]}
    (hxi0 : xi0 = BitVec.ofNat 64 i0) (hxi1 : xi1 = BitVec.ofNat 64 i1)
    (hxdst : xdst = BitVec.ofNat 64 dst) (hxlo : xlo = BitVec.ofNat 64 lo)
    (hxmid : xmid = BitVec.ofNat 64 mid) (hxhi : xhi = BitVec.ofNat 64 hi)
    (hhi : hi ≤ c.max_vars)
    (htl : t.length = c.max_vars) (hhl : h0.length = 2 * c.max_vars)
    (hr0 : ∀ a b, lo ≤ a → a ≤ b → b < mid → s7kAt s.core.lvl t a ≤ s7kAt s.core.lvl t b)
    (hr1 : ∀ a b, mid ≤ a → a ≤ b → b < hi → s7kAt s.core.lvl t a ≤ s7kAt s.core.lvl t b)
    (hinv0 : s7MInv s.core.lvl t h0 lo mid hi i0 i1 dst) (hex0 : i0 = mid ∨ i1 = hi)
    (hc0 : st0.core = { s.core with tmp := t })
    (hs0 : st0.scratch = { s.scratch with wsort := h0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hJL : ∀ st' tc h' m', st'.core = { s.core with tmp := tc } →
      st'.scratch = { s.scratch with wsort := h' } → tc.length = c.max_vars →
      h'.length = 2 * c.max_vars → (m7Slice tc lo hi).Perm (m7Slice t lo hi) →
      (∀ q, (q < lo ∨ hi ≤ q) → tc[q]? = t[q]?) →
      (∀ a b, lo ≤ a → a ≤ b → b < hi → s7kAt s.core.lvl tc a ≤ s7kAt s.core.lvl tc b) →
      (FullMem c st' ⋆ R) m' → JL (BitVec.ofNat 64 hi, ()) m') :
    wp Γ Q X (s7Tail0Expr xi0 xi1 xdst xlo xmid xhi c.pTmp c.pWsort JL) m0 := by
  subst hxi0 hxi1 hxdst hxlo hxmid hxhi
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ j0 d st h, xs.1 = BitVec.ofNat 64 j0 ∧ xs.2.1 = BitVec.ofNat 64 d ∧ meas = mid - j0 ∧
      s7MInv s.core.lvl t h lo mid hi j0 i1 d ∧ (j0 = mid ∨ i1 = hi) ∧
      st.core = { s.core with tmp := t } ∧ st.scratch = { s.scratch with wsort := h } ∧
      h.length = 2 * c.max_vars ∧ (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro JT meas xs m hIH ⟨j0, d, st, h, hx1, hx2, hmeas, hinv, hex, hst_c, hst_s, hhl', hm⟩
    have ⟨hlj, hjm, hmi, hihi, hd, _⟩ := hinv
    rcases xs with ⟨j0_bv, d_bv, ⟨⟩⟩; dsimp only at hx1 hx2; subst hx1 hx2
    rw [Blocks.get_here]; c0_hsplit
    · have hj : j0 < mid := by c0_grind
      have hi1 : i1 = hi := by omega
      have hj_t : (BitVec.ofNat 64 j0).toNat < st.core.tmp.length := by
        rw [m7_core_tmp_eq hst_c, htl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      have hd_h : (BitVec.ofNat 64 d).toNat < st.scratch.wsort.length := by
        rw [m7_scr_ws_eq hst_s, hhl', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      c0_hsteps!
      have hj_i : (BitVec.ofNat 64 j0).toNat = j0 := by c0_bound
      have hd_i : (BitVec.ofNat 64 d).toNat = d := by c0_bound
      have hgt : st.core.tmp[(BitVec.ofNat 64 j0).toNat]'hj_t = t[j0]'(by omega) := by
        simpa only [hj_i] using s7_get_tmp hst_c (i := j0) (by omega)
      have ha1 : BitVec.ofNat 64 j0 + (1 : BitVec 64) = BitVec.ofNat 64 (j0 + 1) := by c0_bound
      have ha2 : BitVec.ofNat 64 d + (1 : BitVec 64) = BitVec.ofNat 64 (d + 1) := by c0_bound
      rw [ha1, ha2]
      let scr1 := st.scratch
      let ws1 := scr1.wsort.set (BitVec.ofNat 64 d).toNat
        (st.core.tmp[(BitVec.ofNat 64 j0).toNat]'hj_t)
      refine hIH (mid - (j0 + 1)) _ _ (by omega) ⟨j0 + 1, d + 1,
        { core := st.core, scratch := { scr1 with wsort := ws1 } },
        h.set d (t[j0]'(by omega)), rfl, rfl, rfl, ?_, Or.inr hi1, hst_c, ?_, by simp [hhl'], hm⟩
      · exact s7MInv_step0 hinv hj (by omega) (by omega) (List.getElem?_eq_getElem (by omega)) hr0
          hr1 (fun h' => absurd h' (by omega))
      · simpa only [scr1, ws1, hd_i, hgt] using s7_st_upd_wsort hst_s
          (i := (BitVec.ofNat 64 d).toNat) (v := st.core.tmp[(BitVec.ofNat 64 j0).toNat]'hj_t)
    · have hj : mid ≤ j0 := by c0_grind
      have hjeq : j0 = mid := by omega
      rw [hjeq] at hinv
      exact s7_tail1_wp (xi1 := BitVec.ofNat 64 i1) (xdst := BitVec.ofNat 64 d)
        (xlo := BitVec.ofNat 64 lo) (xhi := BitVec.ofNat 64 hi) rfl rfl rfl rfl
        hhi htl hhl' hr0 hr1 hinv hst_c hst_s hm hJL
  · intro J hJ; c0_hsteps!
    exact hJ _ _ _ ⟨i0, dst, st0, h0, rfl, rfl, rfl, hinv0, hex0, hc0, hs0, hhl, hm0⟩

/-! ## 5. Merge Loop of One Block -/

private theorem s7_merge_wp {Γ : Env} {c : FullCfg} {s st0 : FullState} {R : Mem 64 → Prop}
    {m0 : Mem 64} {Q : Post []} {X : XPost} {lo mid hi : Nat}
    {t h0 : List (BitVec 32)} {xlo xmid xhi : Val i64} {JL : Cont [i64]}
    (hxlo : xlo = BitVec.ofNat 64 lo) (hxmid : xmid = BitVec.ofNat 64 mid)
    (hxhi : xhi = BitVec.ofNat 64 hi)
    (hlomid : lo ≤ mid) (hmidhi : mid ≤ hi) (hhi : hi ≤ c.max_vars)
    (htl : t.length = c.max_vars) (hhl : h0.length = 2 * c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (hbd : ∀ p, lo ≤ p → p < hi → (t[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hr0 : ∀ a b, lo ≤ a → a ≤ b → b < mid → s7kAt s.core.lvl t a ≤ s7kAt s.core.lvl t b)
    (hr1 : ∀ a b, mid ≤ a → a ≤ b → b < hi → s7kAt s.core.lvl t a ≤ s7kAt s.core.lvl t b)
    (hc0 : st0.core = { s.core with tmp := t })
    (hs0 : st0.scratch = { s.scratch with wsort := h0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hJL : ∀ st' tc h' m', st'.core = { s.core with tmp := tc } →
      st'.scratch = { s.scratch with wsort := h' } → tc.length = c.max_vars →
      h'.length = 2 * c.max_vars → (m7Slice tc lo hi).Perm (m7Slice t lo hi) →
      (∀ q, (q < lo ∨ hi ≤ q) → tc[q]? = t[q]?) →
      (∀ a b, lo ≤ a → a ≤ b → b < hi → s7kAt s.core.lvl tc a ≤ s7kAt s.core.lvl tc b) →
      (FullMem c st' ⋆ R) m' → JL (BitVec.ofNat 64 hi, ()) m') :
    wp Γ Q X (s7MergeExpr xlo xmid xhi c.pTmp c.pLevel c.pWsort JL) m0 := by
  subst hxlo hxmid hxhi
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64, i64, i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ j0 j1 d st h, xs.1 = BitVec.ofNat 64 j0 ∧ xs.2.1 = BitVec.ofNat 64 j1 ∧
      xs.2.2.1 = BitVec.ofNat 64 d ∧ meas = (mid - j0) + (hi - j1) ∧
      s7MInv s.core.lvl t h lo mid hi j0 j1 d ∧
      st.core = { s.core with tmp := t } ∧ st.scratch = { s.scratch with wsort := h } ∧
      h.length = 2 * c.max_vars ∧ (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro JM meas xs m hIH ⟨j0, j1, d, st, h, hx1, hx2, hx3, hmeas, hinv, hst_c, hst_s,
      hhl', hm⟩
    have ⟨hlj0, hj0m, hmj1, hj1h, hd, _⟩ := hinv
    rcases xs with ⟨j0_bv, j1_bv, d_bv, ⟨⟩⟩; dsimp only at hx1 hx2 hx3; subst hx1 hx2 hx3
    rw [Blocks.get_here]
    refine wp_join_group (fun _ m' => m' = m ∧ (j0 = mid ∨ j1 = hi)) ?_ ?_
    · intro JA u m' ⟨hm', hex⟩
      rw [hm', Blocks.get_here]
      exact s7_tail0_wp (xi0 := BitVec.ofNat 64 j0) (xi1 := BitVec.ofNat 64 j1)
        (xdst := BitVec.ofNat 64 d) (xlo := BitVec.ofNat 64 lo) (xmid := BitVec.ofNat 64 mid)
        (xhi := BitVec.ofNat 64 hi) rfl rfl rfl rfl rfl rfl hhi htl hhl' hr0 hr1 hinv hex
        hst_c hst_s hm hJL
    · intro JA hExitA
      c0_hsplit
      · have hj0 : j0 < mid := by c0_grind
        c0_hsplit
        · have hj1 : j1 < hi := by c0_grind
          refine wp_join_group
            (fun xu m' => ∃ n', n' < meas ∧
              Inv n' (xu.1, xu.2.1, BitVec.ofNat 64 d + 1, ()) m') ?_ ?_
          · intro JU xu m' ⟨n', hn', hinv'⟩
            rw [Blocks.get_here]; c0_hsteps!; exact hIH n' _ m' hn' hinv'
          · intro JU hExitU
            have hj0_i : (BitVec.ofNat 64 j0).toNat = j0 := by c0_bound
            have hj1_i : (BitVec.ofNat 64 j1).toNat = j1 := by c0_bound
            have hd_i : (BitVec.ofNat 64 d).toNat = d := by c0_bound
            have hj0_t : (BitVec.ofNat 64 j0).toNat < st.core.tmp.length := by
              rw [m7_core_tmp_eq hst_c, htl, hj0_i]; omega
            have hj1_t : (BitVec.ofNat 64 j1).toNat < st.core.tmp.length := by
              rw [m7_core_tmp_eq hst_c, htl, hj1_i]; omega
            have hgt0 : st.core.tmp[(BitVec.ofNat 64 j0).toNat]'hj0_t = t[j0]'(by omega) := by
              simpa only [hj0_i] using s7_get_tmp hst_c (i := j0) (by omega)
            have hgt1 : st.core.tmp[(BitVec.ofNat 64 j1).toNat]'hj1_t = t[j1]'(by omega) := by
              simpa only [hj1_i] using s7_get_tmp hst_c (i := j1) (by omega)
            have hbd_a : (t[j0]'(by omega)).toNat < 2 * c.max_vars := by
              have h1 := hbd j0 hlj0 (by omega)
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
            have hbd_b : (t[j1]'(by omega)).toNat < 2 * c.max_vars := by
              have h1 := hbd j1 (by omega) hj1
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
            have hla : ((st.core.tmp[(BitVec.ofNat 64 j0).toNat]'hj0_t).setWidth 64 >>>
                ((BitVec.signExtend 64 1#32).toNat % 64)).toNat < st.core.lvl.length := by
              rw [hgt0, s7_lshr1, m7_core_lvl_eq hst_c, hlvl_len]; omega
            have hlb : ((st.core.tmp[(BitVec.ofNat 64 j1).toNat]'hj1_t).setWidth 64 >>>
                ((BitVec.signExtend 64 1#32).toNat % 64)).toNat < st.core.lvl.length := by
              rw [hgt1, s7_lshr1, m7_core_lvl_eq hst_c, hlvl_len]; omega
            have hka : s7kAt s.core.lvl t j0 = (s.core.lvl[(t[j0]'(by omega)).toNat / 2]'(by
                rw [hlvl_len]; omega)).toNat :=
              s7kAt_eq (by omega) (by rw [hlvl_len]; omega)
            have hkb : s7kAt s.core.lvl t j1 = (s.core.lvl[(t[j1]'(by omega)).toNat / 2]'(by
                rw [hlvl_len]; omega)).toNat :=
              s7kAt_eq (by omega) (by rw [hlvl_len]; omega)
            have hd_h : (BitVec.ofNat 64 d).toNat < st.scratch.wsort.length := by
              rw [m7_scr_ws_eq hst_s, hhl', hd_i]; omega
            c0_hsplit
            · have hle' : (s.core.lvl[(t[j0]'(by omega)).toNat / 2]'(by
                  rw [hlvl_len]; omega)).toNat ≤
                  (s.core.lvl[(t[j1]'(by omega)).toNat / 2]'(by
                  rw [hlvl_len]; omega)).toNat := by
                have hc' := hc
                have hgt0' := hgt0; have hgt1' := hgt1
                simp only [BitVec.toNat_ofNat] at hgt0' hgt1'
                rw [s7_get_lvl_of hst_c _ (by rw [hgt0', s7_lshr1_one]) (by rw [hlvl_len]; omega),
                  s7_get_lvl_of hst_c _ (by rw [hgt1', s7_lshr1_one]) (by rw [hlvl_len]; omega)]
                  at hc'
                c0_grind
              c0_hsteps!
              have ha0 : BitVec.ofNat 64 j0 + (1 : BitVec 64) = BitVec.ofNat 64 (j0 + 1) := by
                c0_bound
              have ha_d : BitVec.ofNat 64 d + (1 : BitVec 64) = BitVec.ofNat 64 (d + 1) := by
                c0_bound
              rw [ha0]
              let scr1 := st.scratch
              let ws1 := scr1.wsort.set (BitVec.ofNat 64 d).toNat
                (st.core.tmp[(BitVec.ofNat 64 j0).toNat]'hj0_t)
              refine hExitU _ _ ⟨(mid - (j0 + 1)) + (hi - j1), by omega, j0 + 1, j1, d + 1,
                { core := st.core, scratch := { scr1 with wsort := ws1 } },
                h.set d (t[j0]'(by omega)), rfl, rfl, ha_d, rfl, ?_, hst_c, ?_, by simp [hhl'],
                hm⟩
              · exact s7MInv_step0 hinv hj0 (by omega) (by omega)
                  (List.getElem?_eq_getElem (by omega)) hr0 hr1
                  (fun _ => by rw [hka, hkb]; exact hle')
              · simpa only [scr1, ws1, hd_i, hgt0] using s7_st_upd_wsort hst_s
                  (i := (BitVec.ofNat 64 d).toNat)
                  (v := st.core.tmp[(BitVec.ofNat 64 j0).toNat]'hj0_t)
            · have hgt' : (s.core.lvl[(t[j1]'(by omega)).toNat / 2]'(by
                  rw [hlvl_len]; omega)).toNat <
                  (s.core.lvl[(t[j0]'(by omega)).toNat / 2]'(by
                  rw [hlvl_len]; omega)).toNat := by
                have hc' := hc
                have hgt0' := hgt0; have hgt1' := hgt1
                simp only [BitVec.toNat_ofNat] at hgt0' hgt1'
                rw [s7_get_lvl_of hst_c _ (by rw [hgt0', s7_lshr1_one]) (by rw [hlvl_len]; omega),
                  s7_get_lvl_of hst_c _ (by rw [hgt1', s7_lshr1_one]) (by rw [hlvl_len]; omega)]
                  at hc'
                c0_grind
              c0_hsteps!
              have ha1 : BitVec.ofNat 64 j1 + (1 : BitVec 64) = BitVec.ofNat 64 (j1 + 1) := by
                c0_bound
              have ha_d : BitVec.ofNat 64 d + (1 : BitVec 64) = BitVec.ofNat 64 (d + 1) := by
                c0_bound
              rw [ha1]
              let scr1 := st.scratch
              let ws1 := scr1.wsort.set (BitVec.ofNat 64 d).toNat
                (st.core.tmp[(BitVec.ofNat 64 j1).toNat]'hj1_t)
              refine hExitU _ _ ⟨(mid - j0) + (hi - (j1 + 1)), by omega, j0, j1 + 1, d + 1,
                { core := st.core, scratch := { scr1 with wsort := ws1 } },
                h.set d (t[j1]'(by omega)), rfl, rfl, ha_d, rfl, ?_, hst_c, ?_, by simp [hhl'],
                hm⟩
              · exact s7MInv_step1 hinv hj1 (by omega) (by omega)
                  (List.getElem?_eq_getElem (by omega)) hr0 hr1
                  (fun _ => by rw [hka, hkb]; exact Nat.le_of_lt hgt')
              · simpa only [scr1, ws1, hd_i, hgt1] using s7_st_upd_wsort hst_s
                  (i := (BitVec.ofNat 64 d).toNat)
                  (v := st.core.tmp[(BitVec.ofNat 64 j1).toNat]'hj1_t)
        · have hj1 : hi ≤ j1 := by c0_grind
          c0_hsteps!; exact hExitA () m ⟨rfl, Or.inr (by omega)⟩
      · have hj0 : mid ≤ j0 := by c0_grind
        c0_hsteps!; exact hExitA () m ⟨rfl, Or.inl (by omega)⟩
  · intro J hJ; c0_hsteps!
    exact hJ _ _ _ ⟨lo, mid, lo, st0, h0, rfl, rfl, rfl, rfl,
      s7MInv_init _ _ _ hlomid hmidhi, hc0, hs0, hhl, hm0⟩

/-! ## 6. One `lo`-Pass Over All `2w`-Blocks -/

private theorem s7_pass_wp {Γ : Env} {c : FullCfg} {s st0 : FullState} {R : Mem 64 → Prop}
    {m0 : Mem 64} {Q : Post []} {X : XPost} {N w : Nat} {tw ws : List (BitVec 32)}
    {xw xn : Val i64} {JW : Cont [i64]}
    (hxw : xw = BitVec.ofNat 64 w) (hxn : xn = BitVec.ofNat 64 N)
    (hN : N ≤ c.max_vars) (hw1 : 1 ≤ w) (hwN : w < N)
    (htw : tw.length = c.max_vars) (hws : ws.length = 2 * c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (hbd : ∀ p, 1 ≤ p → p < N → (tw[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hruns : ∀ i j, 1 ≤ i → i ≤ j → j < N → (i - 1) / w = (j - 1) / w →
      s7kAt s.core.lvl tw i ≤ s7kAt s.core.lvl tw j)
    (hc0 : st0.core = { s.core with tmp := tw })
    (hs0 : st0.scratch = { s.scratch with wsort := ws })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hJW : ∀ st' tw' ws' m', st'.core = { s.core with tmp := tw' } →
      st'.scratch = { s.scratch with wsort := ws' } → tw'.length = c.max_vars →
      ws'.length = 2 * c.max_vars → (m7Slice tw' 1 N).Perm (m7Slice tw 1 N) →
      tw'[0]? = tw[0]? →
      (∀ i j, 1 ≤ i → i ≤ j → j < N → (i - 1) / (2 * w) = (j - 1) / (2 * w) →
        s7kAt s.core.lvl tw' i ≤ s7kAt s.core.lvl tw' j) →
      (FullMem c st' ⋆ R) m' → JW (BitVec.ofNat 64 (2 * w), ()) m') :
    wp Γ Q X (s7PassExpr xw xn c.pTmp c.pLevel c.pWsort JW) m0 := by
  subst hxw hxn
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  have hshl : BitVec.ofNat 64 w <<< (1 : Nat) = BitVec.ofNat 64 (2 * w) := s7_shl1_bv64
  let InvL : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ lo st tl wl, xs.1 = BitVec.ofNat 64 lo ∧ 1 ≤ lo ∧ lo ≤ N ∧ meas = N - lo ∧
      (lo = N ∨ ∃ B, lo = 1 + 2 * (B * w)) ∧
      st.core = { s.core with tmp := tl } ∧ st.scratch = { s.scratch with wsort := wl } ∧
      tl.length = c.max_vars ∧ wl.length = 2 * c.max_vars ∧
      (m7Slice tl 1 N).Perm (m7Slice tw 1 N) ∧ tl[0]? = tw[0]? ∧
      (∀ i j, 1 ≤ i → i ≤ j → j < lo → (i - 1) / (2 * w) = (j - 1) / (2 * w) →
        s7kAt s.core.lvl tl i ≤ s7kAt s.core.lvl tl j) ∧
      (∀ i j, lo ≤ i → i ≤ j → j < N → (i - 1) / w = (j - 1) / w →
        s7kAt s.core.lvl tl i ≤ s7kAt s.core.lvl tl j) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group InvL ?_ ?_
  · intro JL meas xs m hIH ⟨lo, st, tl, wl, hxs, hlo1, hloN, hmeas, hblk, hst_c, hst_s, htl,
      hwl, hperm, h0, hpre, hsuf, hm⟩
    rcases xs with ⟨lo_bv, ⟨⟩⟩; dsimp only at hxs; subst hxs
    rw [Blocks.get_here]; c0_hsplit
    · have hlo : lo < N := by c0_grind
      obtain ⟨B, hB⟩ : ∃ B, lo = 1 + 2 * (B * w) := by
        rcases hblk with h | h <;> first | omega | exact h
      clear hblk
      have hbd_l : ∀ p, 1 ≤ p → p < N → (tl[p]?.getD 0#32).toNat < 2 * c.max_vars :=
        m7Slice_perm_bd hperm (by omega) (by omega) hbd
      have hruns2 := s7_pass_runs (lvl := s.core.lvl) (t := tl) (N := N) hB hsuf
      have haddw : BitVec.ofNat 64 lo + BitVec.ofNat 64 w = BitVec.ofNat 64 (lo + w) := by c0_bound
      have hadd2w : BitVec.ofNat 64 lo + BitVec.ofNat 64 (2 * w) =
          BitVec.ofNat 64 (lo + 2 * w) := by c0_bound
      refine wp_join_group
        (fun xs' m' => xs'.1 = BitVec.ofNat 64 (min (lo + w) N) ∧ m' = m) ?_ ?_
      · intro Jm xmid m' ⟨hxmid, hm'⟩
        rw [hm', Blocks.get_here]
        refine wp_join_group
          (fun xs' m' => xs'.1 = BitVec.ofNat 64 (min (lo + 2 * w) N) ∧ m' = m) ?_ ?_
        · intro Jh xhi m'' ⟨hxhi, hm''⟩
          rw [hm'', Blocks.get_here]
          refine s7_merge_wp (xlo := BitVec.ofNat 64 lo) (xmid := xmid.1) (xhi := xhi.1)
            (JL := JL) rfl hxmid hxhi (by omega) (by omega) (by omega) htl hwl hlvl_len
            (fun p hp1 hp2 => hbd_l p (by omega) (by omega)) hruns2.1 hruns2.2
            hst_c hst_s hm ?_
          intro st' tc h' m3 hc' hs' htc hh' hperm' hout hsort hm3
          have hstep := s7_pass_step (N := N) hw1 hB hpre hsuf hout hsort
          refine hIH (N - min (lo + 2 * w) N) _ m3 (by omega) ⟨min (lo + 2 * w) N, st', tc,
            h', rfl, by omega, by omega, rfl, ?_, hc', hs', htc, hh', ?_, ?_, hstep.1, hstep.2,
            hm3⟩
          · rcases Nat.lt_or_ge (lo + 2 * w) N with h | h
            · right; refine ⟨B + 1, ?_⟩
              have e : (B + 1) * w = B * w + w := by rw [Nat.add_mul, Nat.one_mul]
              rw [Nat.min_eq_left (Nat.le_of_lt h), e]; omega
            · left; exact Nat.min_eq_right h
          · exact (m7_slice_perm_sub hlo1 (by omega) (by omega) (by omega) (by omega) hperm'
              hout).trans hperm
          · rw [hout 0 (Or.inl (by omega))]; exact h0
        · intro Jh hExit; c0_hsplit
          · have h2 : lo + 2 * w < N := by
              have : lo + 2 * w < 2 ^ 64 := by omega
              have : N < 2 ^ 64 := by omega
              try simp only [Nat.shiftLeft_eq, Nat.pow_one] at hc
              omega
            c0_hsteps!; rw [hshl, hadd2w]; exact hExit _ _ ⟨by rw [Nat.min_eq_left (by omega)], rfl⟩
          · have h2 : N ≤ lo + 2 * w := by
              have : lo + 2 * w < 2 ^ 64 := by omega
              have : N < 2 ^ 64 := by omega
              try simp only [Nat.shiftLeft_eq, Nat.pow_one] at hc
              omega
            c0_hsteps!; exact hExit _ _ ⟨by rw [Nat.min_eq_right h2], rfl⟩
      · intro Jm hExit; c0_hsplit
        · have h2 : lo + w < N := by omega
          c0_hsteps!; rw [haddw]; exact hExit _ _ ⟨by rw [Nat.min_eq_left (by omega)], rfl⟩
        · have h2 : N ≤ lo + w := by omega
          c0_hsteps!; exact hExit _ _ ⟨by rw [Nat.min_eq_right h2], rfl⟩
    · have hlo : N ≤ lo := by c0_grind
      c0_hsteps!; rw [hshl]
      exact hJW st tl wl m hst_c hst_s htl hwl hperm h0
        (fun i j h1 h2 h3 h4 => hpre i j h1 h2 (by omega) h4) hm
  · intro J hJ; c0_hsteps!
    exact hJ _ (BitVec.ofNat 64 1, ()) _ ⟨1, st0, tw, ws, rfl, Nat.le_refl _, by omega, rfl,
      Or.inr ⟨0, by simp⟩, hc0, hs0, htw, hws, List.Perm.refl _, rfl,
      fun i j h1 h2 h3 _ => absurd h3 (by omega), hruns, hm0⟩

/-! ## 7. Main Theorem: Bottom-Up Merge-Sort Fallback -/

theorem s7_sort_merge_wp {Γ : Env} {c : FullCfg} {s st0 : FullState} {ws0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    (htmp_len : s.core.tmp.length = c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (htl : s.core.tmp_len ≤ c.max_vars) (h2 : 2 ≤ s.core.tmp_len)
    (hbd0 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hws_len : ws0.length = 2 * c.max_vars)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hPost : ∀ st' tmp' ws' m',
      st'.core = { s.core with tmp := tmp' } →
      st'.scratch = { s.scratch with wsort := ws' } →
      tmp'.length = c.max_vars → ws'.length = 2 * c.max_vars →
      (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) →
      tmp'[0]? = s.core.tmp[0]? →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c st' ⋆ R) m' → Q () m') :
    wp Γ Q X (s7SortMergeExpr (BitVec.ofNat 64 s.core.tmp_len)
      (BitVec.ofNat 64 (s.core.tmp_len - 1)) c.pTmp c.pLevel c.pWsort) m0 := by
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let InvW : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ w st tw ws, xs.1 = BitVec.ofNat 64 w ∧ 1 ≤ w ∧ w < 2 * s.core.tmp_len ∧
      meas = s.core.tmp_len - w ∧
      st.core = { s.core with tmp := tw } ∧ st.scratch = { s.scratch with wsort := ws } ∧
      tw.length = c.max_vars ∧ ws.length = 2 * c.max_vars ∧
      (m7Slice tw 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) ∧
      tw[0]? = s.core.tmp[0]? ∧
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len → (i - 1) / w = (j - 1) / w →
        s7kAt s.core.lvl tw i ≤ s7kAt s.core.lvl tw j) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group InvW ?_ ?_
  · intro JW meas xs m hIH ⟨w, st, tw, ws, hxs, hw1, hw2, hmeas, hst_c, hst_s, htw, hws,
      hperm, h0, hruns, hm⟩
    rcases xs with ⟨w_bv, ⟨⟩⟩; dsimp only at hxs; subst hxs
    rw [Blocks.get_here]; c0_hsplit
    · have hwlt : w < s.core.tmp_len - 1 := by c0_grind
      refine s7_pass_wp (xw := BitVec.ofNat 64 w) (xn := BitVec.ofNat 64 s.core.tmp_len)
        (JW := JW) rfl rfl htl hw1 (by omega) htw hws hlvl_len
        (m7Slice_perm_bd hperm (by omega) (by omega) hbd0) hruns hst_c hst_s hm ?_
      intro st' tw' ws' m' hc' hs' htw' hws' hperm' h0' hruns' hm'
      exact hIH (s.core.tmp_len - 2 * w) _ m' (by omega) ⟨2 * w, st', tw', ws', rfl, by omega,
        by omega, rfl, hc', hs', htw', hws', hperm'.trans hperm, h0'.trans h0, hruns', hm'⟩
    · have hwge : s.core.tmp_len - 1 ≤ w := by c0_grind
      c0_hsteps!
      have hsorted : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
          s7kAt s.core.lvl tw i ≤ s7kAt s.core.lvl tw j := by
        intro i j hi hij hj
        have hdi : (i - 1) / w = 0 := Nat.div_eq_of_lt (by omega)
        have hdj : (j - 1) / w = 0 := Nat.div_eq_of_lt (by omega)
        exact hruns i j hi hij hj (by rw [hdi, hdj])
      exact hPost st tw ws m hst_c hst_s htw hws hperm h0 hsorted hm
  · intro J hJ; c0_hsteps!
    refine hJ _ (BitVec.ofNat 64 1, ()) _ ⟨1, st0, s.core.tmp, ws0, rfl, Nat.le_refl _, by omega,
      rfl, hc0, hs0, htmp_len, hws_len, List.Perm.refl _, rfl, ?_, hm0⟩
    intro i j hi hij hj hd
    rw [Nat.div_one, Nat.div_one] at hd
    have hij' : i = j := by omega
    rw [hij']; exact Nat.le_refl _

end LeanQbe.T.Examples.Kissat.Proof.Minimize
