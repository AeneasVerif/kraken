/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Transitive.Inv

/-!
# Transitive Reduction BFS Unroll & Sparse-Preservation Helpers (`Proof.Transitive.UnrollInv`)

Defines `TransUnrollInv` (bounded BFS implication unrolling with trail rollback),
`FullSparseInv` / `FullWitnessInv` frame preservation helpers across external calls
(`full_wstack_defrag`, `full_backtrack`, `full_propagate`, `full_add_unit`, `probing`, `work_stk1`),
and shared BitVec / memory helper lemmas for `WpSort`, `WpLit`, and `WpTop`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Transitive

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Shared BitVec & State Helpers -/

theorem tr_bv32_setWidth64 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem tr_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem tr_bv64_sub1 {f : BitVec 64} (hf : f ≠ 0#64) : (f - 1#64).toNat = f.toNat - 1 := by
  bv_omega

theorem tr_bv64_sub1_nat {n : Nat} (hn1 : 0 < n) (hn2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1#64).toNat = n - 1 := by
  bv_omega

theorem tr_bv64_add1 {f : BitVec 64} (hf : f.toNat + 1 < 2 ^ 64) :
    (f + 1#64).toNat = f.toNat + 1 := by
  bv_omega

theorem tr_bv64_add2 {f : BitVec 64} (hf : f.toNat + 2 < 2 ^ 64) :
    (f + 2#64).toNat = f.toNat + 2 := by
  bv_omega

theorem tr_bv64_shl1 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem tr_nat_two_mul_or_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j => simp [Nat.testBit_succ, show (2 * k + 1) / 2 = k by omega, Nat.div_eq_of_lt]

theorem tr_bv64_shl1_setWidth32 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 32) :
    ((x <<< (1 : Nat)).setWidth 32) = BitVec.ofNat 32 (2 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, tr_bv64_shl1 (by omega), BitVec.toNat_ofNat]

theorem tr_bv64_shl1_or1_setWidth32 {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 32) :
    (((x <<< (1 : Nat)) ||| 1#64).setWidth 32) = BitVec.ofNat 32 (2 * x.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, tr_bv64_shl1 (by omega),
    show (1#64 : BitVec 64).toNat = 1 from rfl, tr_nat_two_mul_or_one, BitVec.toNat_ofNat]

theorem tr_bv32_ofNat_eq {c : FullCfg} {n : Nat} (hn : n < 2 * c.max_vars) :
    (BitVec.ofNat 32 n).toNat = n := by
  have := c.hmaxv; unfold dimacsBound at *
  simp [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]

theorem tr_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (heq : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m :=
  heq ▸ hm

theorem tr_bnds {c : FullCfg} {k : FullCoreState} (hl : k.LengthsOk c) :
    2 * k.cur_vars + 1 < 2 ^ 30 ∧ k.wlen ≤ c.wcap ∧ k.wlen < 2 ^ 64 ∧ k.trail_end < 2 ^ 64 := by
  have := hl.cur_vars_le; have := hl.wlen_le; have := hl.trail_end_le
  have := c.hmaxv; have := c.hwcap; unfold dimacsBound at *; omega

theorem tr_wstk_lt {c : FullCfg} {k : FullCoreState} {p end_v : Nat}
    (hl : FullCoreState.LengthsOk c k) (hp : p < end_v) (he : end_v ≤ k.wlen) :
    p < k.wstk.length := by
  rw [hl.wstk_len_arr]; have := hl.wlen_le; omega

theorem tr_vals_lt {c : FullCfg} {k : FullCoreState} {l : Nat}
    (hl : FullCoreState.LengthsOk c k) (h : l < 2 * k.cur_vars) :
    l < k.vals.length := by
  rw [hl.vals_len]; have := hl.cur_vars_le; omega

theorem tr_getElem_toNat {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    (xs[i]'hi).toNat = (xs[i]?.getD 0#32).toNat := by
  simp [List.getElem?_eq_getElem hi]

theorem tr_bv32_ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem tr_bv64_sub_sz (a b r : BitVec 64) {bn rn : Nat}
    (hb : b.toNat = bn) (hr : r.toNat = rn) (h : rn ≤ bn) (hbn : bn < 2 ^ 32) :
    BitVec.setWidth 32 (a + b - a - r) = BitVec.ofNat 32 (bn - rn) := by
  apply BitVec.eq_of_toNat_eq; have : (a + b - a - r).toNat = bn - rn := by bv_omega
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, this, Nat.mod_eq_of_lt (by omega)]

theorem tr_vals_ff_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32)
    (hslt : (v.signExtend 32).slt z = true) : v = 0xFF#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd hslt (by decide)

theorem tr_vals_zero_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32) (heq : v.signExtend 32 = z) :
    v = 0#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd heq (by decide)

/-! ## 2. BFS & Unroll Invariants (`TransUnrollInv`) -/

/-- Unroll/BFS invariant for `full_trans_lit_m6`. -/
structure TransUnrollInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st_pre : FullState) (src saved : Nat) (st : FullState) : Prop where
  len_ok : st.LengthsOk c
  same_core : st.core = { st_pre.core with
    vals := st.core.vals, trl := st.core.trl, trail_end := st.core.trail_end }
  same_scratch : st.scratch = st_pre.scratch
  saved_eq : saved = st_pre.core.trail_end
  saved_le_te : saved ≤ st.core.trail_end
  trl_pres : ∀ i < saved, st.core.trl[i]? = st_pre.core.trl[i]?
  vals_pres : ∀ l < 2 * st_pre.core.cur_vars,
    st_pre.core.vals[l]?.getD 0#8 ≠ 0#8 → st.core.vals[l]?.getD 0#8 = st_pre.core.vals[l]?.getD 0#8
  vals_hi_pres : ∀ l, 2 * st_pre.core.cur_vars ≤ l → st.core.vals[l]? = st_pre.core.vals[l]?
  bfs_trl_inv : ∀ i, saved ≤ i → i < st.core.trail_end →
    ∃ l : BitVec 32, st.core.trl[i]? = some l ∧ l.toNat < 2 * st_pre.core.cur_vars ∧
      st_pre.core.vals[l.toNat]?.getD 0#8 = 0#8 ∧ st.core.vals[l.toNat]?.getD 0#8 = 1#8 ∧
      st.core.vals[l.toNat ^^^ 1]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [src, l.toNat])
  bfs_vars_nodup : ∀ i j, saved ≤ i → i < j → j < st.core.trail_end →
    (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ (st.core.trl[j]?.getD 0#32).toNat / 2
  vals_only_trl : ∀ l < 2 * st_pre.core.cur_vars,
    st_pre.core.vals[l]?.getD 0#8 = 0#8 → st.core.vals[l]?.getD 0#8 ≠ 0#8 →
    ∃ i, saved ≤ i ∧ i < st.core.trail_end ∧
      ((st.core.trl[i]?.getD 0#32).toNat = l ∨ (st.core.trl[i]?.getD 0#32).toNat ^^^ 1 = l)

theorem TransUnrollInv.vals_domain {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved l : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hl : l < 2 * st_pre.core.cur_vars) :
    st.core.vals[l]?.getD 0#8 = 0#8 ∨ st.core.vals[l]?.getD 0#8 = 1#8 ∨
    st.core.vals[l]?.getD 0#8 = 0xFF#8 := by
  by_cases h0 : st_pre.core.vals[l]?.getD 0#8 = 0#8
  · by_cases hcur : st.core.vals[l]?.getD 0#8 = 0#8; · exact Or.inl hcur
    obtain ⟨i, hi1, hi2, he⟩ := h.vals_only_trl l hl h0 hcur
    obtain ⟨lit, hget, _, _, hv1, hvff, _⟩ := h.bfs_trl_inv i hi1 hi2
    rw [show (st.core.trl[i]?.getD 0#32).toNat = lit.toNat by simp [hget]] at he
    rcases he with rfl | rfl <;> first | exact Or.inr (Or.inl hv1) | exact Or.inr (Or.inr hvff)
  · rw [h.vals_pres l hl h0, hpre_vals]; exact hw0.vals_domain l (hpre_cv ▸ hl)

theorem TransUnrollInv.trail_end_lt_of_unassigned {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 st_pre st : FullState} {src saved ot : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_te : st_pre.core.trail_end = s0.core.trail_end)
    (hpre_trl : ∀ i < s0.core.trail_end, st_pre.core.trl[i]? = s0.core.trl[i]?)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hot : ot < 2 * st_pre.core.cur_vars)
    (hzero : st.core.vals[ot]?.getD 0#8 = 0#8) : st.core.trail_end < st_pre.core.cur_vars := by
  have hs_te := h.saved_eq.trans hpre_te
  have htr : ∀ i < saved, (st.core.trl[i]?.getD 0#32).toNat = (s0.core.trl[i]?.getD 0#32).toNat :=
    fun i hi => by rw [h.trl_pres i hi, hpre_trl i (hs_te ▸ hi)]
  have hcross : ∀ a b, a < saved → saved ≤ b → b < st.core.trail_end →
      (st.core.trl[a]?.getD 0#32).toNat / 2 ≠ (st.core.trl[b]?.getD 0#32).toNat / 2 := by
    intro a b ha hb1 hb2 hij; obtain ⟨lit, hget, hlt, hpre0, _, _, _⟩ := h.bfs_trl_inv b hb1 hb2
    rw [htr a ha, show (st.core.trl[b]?.getD 0#32).toNat = lit.toNat by simp [hget]] at hij
    rcases (litVar_eq_iff _ _).mp hij.symm with heq | heq
    · have ht := (hw0.vals_true_iff _ (hpre_cv ▸ hlt)).mpr ⟨a, hs_te ▸ ha, heq.symm⟩
      rw [← hpre_vals, hpre0] at ht; cases ht
    · have hf := (hw0.vals_false_iff _ (hpre_cv ▸ hlt)).mpr
        ⟨a, hs_te ▸ ha, by rw [heq]; exact (litNeg_litNeg _).symm⟩
      rw [← hpre_vals, hpre0] at hf; cases hf
  refine inj_lt_of_missing (fun i => (st.core.trl[i]?.getD 0#32).toNat / 2) ?_ ?_
    (by omega : ot / 2 < st_pre.core.cur_vars) ?_
  · intro i j hi hj hij; by_cases his : i < saved <;> by_cases hjs : j < saved
    · rw [htr i his, htr j hjs] at hij
      exact hw0.trail_vars_nodup i j (hs_te ▸ his) (hs_te ▸ hjs) hij
    · exact False.elim (hcross i j his (by omega) hj hij)
    · exact False.elim (hcross j i hjs (by omega) hi hij.symm)
    · rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
      · exact False.elim (h.bfs_vars_nodup i j (by omega) hlt hj hij)
      · rfl
      · exact False.elim (h.bfs_vars_nodup j i (by omega) hgt hi hij.symm)
  · intro i hi; by_cases his : i < saved
    · rw [htr i his, hpre_cv]; have := hw0.trail_lits_lt i (hs_te ▸ his); omega
    · obtain ⟨_, hget, _, _⟩ := h.bfs_trl_inv i (by omega) hi; simp [hget]; omega
  · intro i hi hij; by_cases his : i < saved
    · have hpre_nz : st_pre.core.vals[ot]?.getD 0#8 ≠ 0#8 := by
        rw [hpre_vals]; intro hz; rw [htr i his] at hij
        exact (hw0.vals_zero_iff (hpre_cv ▸ hot)).mp hz i (hs_te ▸ his) hij
      rw [h.vals_pres ot hot hpre_nz] at hzero; exact hpre_nz hzero
    · obtain ⟨lit, hget, _, _, hv1, hvff, _⟩ := h.bfs_trl_inv i (by omega) hi
      simp [hget] at hij; rcases (litVar_eq_iff _ _).mp hij with heq | heq
      · rw [heq, hzero] at hv1; cases hv1
      · change lit.toNat = ot ^^^ 1 at heq; rw [show lit.toNat ^^^ 1 = ot by
          rw [heq]; exact litNeg_litNeg ot, hzero] at hvff; cases hvff

private theorem pre_xor_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre : FullState} {l : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpv : st_pre.core.vals = s0.core.vals) (hpcv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hl : l < 2 * st_pre.core.cur_vars) (h0 : st_pre.core.vals[l]?.getD 0#8 = 0#8) :
    st_pre.core.vals[l ^^^ 1]?.getD 0#8 = 0#8 := by
  rw [hpv]; refine (hw0.vals_zero_iff (hpcv ▸ litNeg_lt_two_mul hl)).mpr fun i hi => ?_
  rw [fullInv_var_xor1]; exact (hw0.vals_zero_iff (hpcv ▸ hl)).mp (hpv ▸ h0) i hi

theorem TransUnrollInv.init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre : FullState} {src : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hlen : st_pre.LengthsOk c) (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_te : st_pre.core.trail_end = s0.core.trail_end)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hsrc_lt : src < 2 * st_pre.core.cur_vars) (hsrc0 : st_pre.core.vals[src]?.getD 0#8 = 0#8) :
    let saved := st_pre.core.trail_end; let not_src := src ^^^ 1
    let vals2 := (st_pre.core.vals.set not_src 1#8).set src 0xFF#8
    let trl1 := st_pre.core.trl.set saved (BitVec.ofNat 32 not_src)
    let st' := { st_pre with core :=
      { st_pre.core with vals := vals2, trl := trl1, trail_end := saved + 1 } }
    saved < st_pre.core.cur_vars ∧
    TransUnrollInv c F0 F_cur s0 st_pre src saved st' ∧ saved < st'.core.trail_end := by
  intro saved not_src vals2 trl1 st'; have hte_lt : saved < st_pre.core.cur_vars := by
    rw [show saved = st_pre.core.trail_end from rfl, hpre_te, hpre_cv]
    exact hw0.trail_end_lt_of_unassigned (hpre_cv ▸ hsrc_lt) (hpre_vals ▸ hsrc0)
  have hnot_lt := litNeg_lt_two_mul hsrc_lt; have hnot_ne : not_src ≠ src := litNeg_ne_self src
  have hnot0 := pre_xor_zero hw0 hpre_vals hpre_cv hsrc_lt hsrc0
  have hmx := hlen.core_ok.cur_vars_le
  have hbv_not : (BitVec.ofNat 32 not_src).toNat = not_src := tr_bv32_ofNat_eq (c := c) (by omega)
  have hv_len := hlen.core_ok.vals_len; have htrl_len := hlen.core_ok.trl_len; refine ⟨hte_lt, {
    len_ok := ⟨{ hlen.core_ok with
      vals_len := by simp [st', vals2, hv_len], trl_len := by simp [st', trl1, htrl_len]
      trail_end_le := by simp [st']; omega
      propagated_le := by simp [st']; have := hlen.core_ok.propagated_le; omega }, hlen.scratch_ok⟩
    same_core := rfl, same_scratch := rfl, saved_eq := rfl, saved_le_te := by simp [st']
    trl_pres := fun i hi => List.getElem?_set_ne (by omega)
    vals_pres := fun l hl hnz => getD_set2_ne (fun e => hnz (e ▸ hnot0)) (fun e => hnz (e ▸ hsrc0))
    vals_hi_pres := fun l hl =>
      (List.getElem?_set_ne (by omega)).trans (List.getElem?_set_ne (by omega))
    bfs_trl_inv := fun i hi1 hi2 => by
      have hi : i = saved := by simp [st'] at hi2; omega
      subst hi; refine ⟨BitVec.ofNat 32 not_src, List.getElem?_set_self (by rw [htrl_len]; omega),
        hbv_not.symm ▸ hnot_lt, hbv_not.symm ▸ hnot0, ?_, ?_,
        hbv_not.symm ▸ entails_pair_taut src⟩
      · rw [hbv_not, List.getElem?_set_ne hnot_ne.symm,
          List.getElem?_set_self (by rw [hv_len]; omega)]; rfl
      · rw [hbv_not]; change vals2[(src ^^^ 1) ^^^ 1]?.getD 0#8 = 0xFF#8
        rw [show (src ^^^ 1) ^^^ 1 = src from litNeg_litNeg src,
          List.getElem?_set_self (by rw [List.length_set, hv_len]; omega)]; rfl
    bfs_vars_nodup := fun i j hi1 hij hj2 => by simp [st'] at hj2; omega
    vals_only_trl := fun l hl hpre0 hcur => by
      have hmem : l = not_src ∨ l = src := Classical.byContradiction fun hc => by
        simp only [not_or] at hc; rw [show st'.core.vals[l]?.getD 0#8 =
          st_pre.core.vals[l]?.getD 0#8 from getD_set2_ne hc.1 hc.2, hpre0] at hcur
        exact hcur rfl
      have hg : (st'.core.trl[saved]?.getD 0#32).toNat = not_src := by
        change (trl1[saved]?.getD 0#32).toNat = not_src
        rw [List.getElem?_set_self (by rw [htrl_len]; omega)]; simp [hbv_not]
      refine ⟨saved, Nat.le_refl _, by simp [st'], ?_⟩; rw [hg]
      exact hmem.elim (fun h => Or.inl h.symm)
        fun h => Or.inr (by rw [h]; exact litNeg_litNeg src) }, by simp [st']⟩

theorem TransUnrollInv.push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved ot : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_te : st_pre.core.trail_end = s0.core.trail_end)
    (hpre_trl : ∀ i < s0.core.trail_end, st_pre.core.trl[i]? = s0.core.trl[i]?)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hot : ot < 2 * st_pre.core.cur_vars)
    (hzero : st.core.vals[ot]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [src, ot])) :
    let te := st.core.trail_end; let vals2 := (st.core.vals.set ot 1#8).set (ot ^^^ 1) 0xFF#8
    let trl1 := st.core.trl.set te (BitVec.ofNat 32 ot); let st' := { st with core :=
      { st.core with vals := vals2, trl := trl1, trail_end := te + 1 } }
    te < st_pre.core.cur_vars ∧ TransUnrollInv c F0 F_cur s0 st_pre src saved st' := by
  intro te vals2 trl1 st'
  have hte_lt := h.trail_end_lt_of_unassigned hw0 hpre_vals hpre_te hpre_trl hpre_cv hot hzero
  have hnot_lt : ot ^^^ 1 < 2 * st_pre.core.cur_vars := litNeg_lt_two_mul hot
  have hnot_ne : ot ≠ ot ^^^ 1 := (litNeg_ne_self ot).symm
  have hpre_ot0 : st_pre.core.vals[ot]?.getD 0#8 = 0#8 := Classical.byContradiction fun hnz => by
    rw [h.vals_pres ot hot hnz] at hzero; exact hnz hzero
  have hpre_not0 := pre_xor_zero hw0 hpre_vals hpre_cv hot hpre_ot0
  have hcv_eq : st.core.cur_vars = st_pre.core.cur_vars := by rw [h.same_core]
  have hmx : st_pre.core.cur_vars ≤ c.max_vars := hcv_eq ▸ h.len_ok.core_ok.cur_vars_le
  have hbv_ot : (BitVec.ofNat 32 ot).toNat = ot := tr_bv32_ofNat_eq (c := c) (by omega)
  have hv_len := h.len_ok.core_ok.vals_len; have htrl_len := h.len_ok.core_ok.trl_len
  have hmiss : ∀ i, saved ≤ i → i < te → (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ ot / 2 := by
    intro i hi1 hi2 heq; obtain ⟨lit, hget, _, _, hv1, hvff, _⟩ := h.bfs_trl_inv i hi1 hi2
    simp [hget] at heq; rcases (litVar_eq_iff _ _).mp heq with hl | hl
    · rw [hl, hzero] at hv1; cases hv1
    · change lit.toNat = ot ^^^ 1 at hl
      rw [show lit.toNat ^^^ 1 = ot by rw [hl]; exact litNeg_litNeg ot, hzero] at hvff; cases hvff
  refine ⟨hte_lt, {
    len_ok := ⟨{ h.len_ok.core_ok with
      vals_len := by simp [st', vals2, hv_len], trl_len := by simp [st', trl1, htrl_len]
      trail_end_le := by simp [st']; omega
      propagated_le := by simp [st']; have := h.len_ok.core_ok.propagated_le; omega },
      h.len_ok.scratch_ok⟩
    same_core := by dsimp only [st']; rw [h.same_core], same_scratch := h.same_scratch
    saved_eq := h.saved_eq, saved_le_te := by simp [st']; have := h.saved_le_te; omega
    trl_pres := fun i hi =>
      (List.getElem?_set_ne (by have := h.saved_le_te; omega)).trans (h.trl_pres i hi)
    vals_pres := fun l hl hnz => by
      rw [show st'.core.vals[l]?.getD 0#8 = st.core.vals[l]?.getD 0#8 from getD_set2_ne
        (fun e => hnz (e ▸ hpre_ot0)) (fun e => hnz (e ▸ hpre_not0))]; exact h.vals_pres l hl hnz
    vals_hi_pres := fun l hl => ((List.getElem?_set_ne (by omega)).trans
      (List.getElem?_set_ne (by omega))).trans (h.vals_hi_pres l hl)
    bfs_trl_inv := fun i hi1 hi2 => by
      by_cases hit : i = te
      · subst hit
        have hv1 : vals2[ot]?.getD 0#8 = 1#8 := by
          rw [List.getElem?_set_ne hnot_ne.symm, List.getElem?_set_self (by rw [hv_len]; omega)]
          rfl
        have hvff : vals2[ot ^^^ 1]?.getD 0#8 = 0xFF#8 := by
          rw [List.getElem?_set_self (by rw [List.length_set, hv_len]; omega)]; rfl
        refine ⟨BitVec.ofNat 32 ot, List.getElem?_set_self (by rw [htrl_len]; omega),
          hbv_ot.symm ▸ hot, hbv_ot.symm ▸ hpre_ot0, hbv_ot.symm ▸ hv1, hbv_ot.symm ▸ hvff,
          hbv_ot.symm ▸ hent⟩
      · have hi2' : i < te := by simp [st'] at hi2; omega
        obtain ⟨lit, hget, hlt, hp0, hv1, hvff, he⟩ := h.bfs_trl_inv i hi1 hi2'
        obtain ⟨hne1, hne2, hne3, hne4⟩ := var_ne_xor_pair (by simpa [hget] using hmiss i hi1 hi2')
        exact ⟨lit, (List.getElem?_set_ne (Ne.symm hit)).trans hget, hlt, hp0,
          by change vals2[lit.toNat]?.getD 0#8 = 1#8; rwa [getD_set2_ne hne1 hne2],
          by change vals2[lit.toNat ^^^ 1]?.getD 0#8 = 0xFF#8; rwa [getD_set2_ne hne3 hne4], he⟩
    bfs_vars_nodup := fun i j hi1 hij hj2 => by
      have hj' : j ≤ te := by simp [st'] at hj2; omega
      have hg1 : (st'.core.trl[i]?.getD 0#32).toNat = (st.core.trl[i]?.getD 0#32).toNat := by
        change (trl1[i]?.getD 0#32).toNat = _; rw [List.getElem?_set_ne (by omega)]
      by_cases hje : j = te
      · subst hje; have hg2 : (st'.core.trl[te]?.getD 0#32).toNat = ot := by
          change (trl1[te]?.getD 0#32).toNat = ot
          rw [List.getElem?_set_self (by rw [htrl_len]; omega)]; exact hbv_ot
        rw [hg1, hg2]; exact hmiss i hi1 hij
      · have hg2 : (st'.core.trl[j]?.getD 0#32).toNat = (st.core.trl[j]?.getD 0#32).toNat := by
          change (trl1[j]?.getD 0#32).toNat = _; rw [List.getElem?_set_ne (Ne.symm hje)]
        rw [hg1, hg2]; exact h.bfs_vars_nodup i j hi1 hij (by omega)
    vals_only_trl := fun l hl hpre0 hcur => by
      by_cases hmem : l = ot ∨ l = ot ^^^ 1
      · have hg : (st'.core.trl[te]?.getD 0#32).toNat = ot := by
          change (trl1[te]?.getD 0#32).toNat = ot
          rw [List.getElem?_set_self (by rw [htrl_len]; omega)]; exact hbv_ot
        exact ⟨te, h.saved_le_te, by simp [st'], by rw [hg]; exact Or.imp Eq.symm Eq.symm hmem⟩
      · simp only [not_or] at hmem; rw [show st'.core.vals[l]?.getD 0#8 =
          st.core.vals[l]?.getD 0#8 from getD_set2_ne hmem.1 hmem.2] at hcur
        obtain ⟨i, hi1, hi2, hw⟩ := h.vals_only_trl l hl hpre0 hcur
        have hg : (st'.core.trl[i]?.getD 0#32).toNat = (st.core.trl[i]?.getD 0#32).toNat := by
          change (trl1[i]?.getD 0#32).toNat = _; rw [List.getElem?_set_ne (by omega)]
        exact ⟨i, hi1, by simp [st']; omega, by rwa [hg]⟩ }⟩

theorem TransUnrollInv.entails_src_of_falsified {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 st_pre st : FullState} {src saved ot : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars) (_hcl0 : s0.core.cur_level = 0)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hot : ot < 2 * st_pre.core.cur_vars)
    (hfals : st.core.vals[ot]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [src, ot])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [src]) := by
  by_cases hp0 : st_pre.core.vals[ot]?.getD 0#8 = 0#8
  · obtain ⟨i, hi1, hi2, hmem⟩ := h.vals_only_trl ot hot hp0 (by rw [hfals]; decide)
    obtain ⟨lit, hget, _, _, hv1, _, hent_lit⟩ := h.bfs_trl_inv i hi1 hi2
    simp [hget] at hmem; rcases hmem with rfl | hneg
    · rw [hfals] at hv1; cases hv1
    · rw [show lit.toNat = ot ^^^ 1 by rw [← hneg]; exact (litNeg_litNeg _).symm] at hent_lit
      exact entails_pair_collapse hent hent_lit
  · have hpre_ff : s0.core.vals[ot]?.getD 0#8 = 0xFF#8 := by
      rw [← hpre_vals, ← h.vals_pres ot hot hp0, hfals]
    obtain ⟨i, hi, heq⟩ := (hw0.vals_false_iff ot (hpre_cv ▸ hot)).mp hpre_ff
    have hs := hw0.level0_sound i hi (by have := hw0.lvl_le i hi; omega); rw [heq] at hs
    exact entails_unit_resolve_pair hent hs

theorem TransUnrollInv.unroll_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hlen_pre : st_pre.LengthsOk c) (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st)
    (hgt : saved < st.core.trail_end) :
    let te' := st.core.trail_end - 1
    ∃ ul : BitVec 32, st.core.trl[te']? = some ul ∧ ul.toNat < 2 * st_pre.core.cur_vars ∧
      let vals2 := (st.core.vals.set ul.toNat 0#8).set (ul.toNat ^^^ 1) 0#8
      let st' := { st with core := { st.core with vals := vals2, trail_end := te' } }
      TransUnrollInv c F0 F_cur s0 st_pre src saved st' := by
  intro te'; obtain ⟨ul, hget, hult, hp0, _, _, _⟩ := h.bfs_trl_inv te' (by omega) (by omega)
  refine ⟨ul, hget, hult, ?_⟩; intro vals2 st'; have hnot_lt := litNeg_lt_two_mul hult
  have hpre_not0 := pre_xor_zero hw0 hpre_vals hpre_cv hult hp0
  have hv_len := h.len_ok.core_ok.vals_len; have hmx := hlen_pre.core_ok.cur_vars_le
  have hmiss : ∀ i, saved ≤ i → i < te' →
      (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ ul.toNat / 2 := fun i hi1 hi2 heq => by
    have hnd := h.bfs_vars_nodup i te' hi1 hi2 (by omega); simp [hget] at hnd; exact hnd heq
  exact {
    len_ok := ⟨{ h.len_ok.core_ok with
      vals_len := by simp [st', vals2, hv_len]
      trail_end_le := by simp [st']; have := h.len_ok.core_ok.trail_end_le; omega
      propagated_le := by
        simp only [st'] at *; rw [h.same_core]; dsimp only
        have : st_pre.core.propagated ≤ saved := h.saved_eq ▸ hlen_pre.core_ok.propagated_le
        omega }, h.len_ok.scratch_ok⟩
    same_core := by dsimp only [st']; rw [h.same_core]
    same_scratch := h.same_scratch, saved_eq := h.saved_eq, saved_le_te := by simp [st']; omega
    trl_pres := h.trl_pres, vals_pres := fun l hl hnz => by
      rw [show st'.core.vals[l]?.getD 0#8 = st.core.vals[l]?.getD 0#8 from
        getD_set2_ne (fun he => hnz (he ▸ hp0)) (fun he => hnz (he ▸ hpre_not0))]
      exact h.vals_pres l hl hnz
    vals_hi_pres := fun l hl =>
      ((List.getElem?_set_ne (by omega)).trans (List.getElem?_set_ne (by omega))).trans
        (h.vals_hi_pres l hl)
    bfs_trl_inv := fun i hi1 hi2 => by
      have hi2' : i < te' := by simp [st'] at hi2; exact hi2
      obtain ⟨lit, hgl, hll, hpl, hv1, hvff, he⟩ := h.bfs_trl_inv i hi1 (by omega)
      have hlit : (st.core.trl[i]?.getD 0#32).toNat = lit.toNat := by simp [hgl]
      obtain ⟨hne1, hne2, hne3, hne4⟩ := var_ne_xor_pair (hlit ▸ hmiss i hi1 hi2')
      exact ⟨lit, hgl, hll, hpl,
        by change vals2[lit.toNat]?.getD 0#8 = 1#8; rwa [getD_set2_ne hne1 hne2],
        by change vals2[lit.toNat ^^^ 1]?.getD 0#8 = 0xFF#8; rwa [getD_set2_ne hne3 hne4], he⟩
    bfs_vars_nodup := fun i j hi1 hij hj2 =>
      h.bfs_vars_nodup i j hi1 hij (by simp [st'] at hj2; omega)
    vals_only_trl := fun l hl hpre0 hcur => by
      have hne_ul : ul.toNat ≠ ul.toNat ^^^ 1 := (litNeg_ne_self ul.toNat).symm
      have hmem : l ≠ ul.toNat ∧ l ≠ ul.toNat ^^^ 1 := by
        constructor <;> rintro rfl
        · exact hcur (by rw [List.getElem?_set_ne hne_ul.symm,
            List.getElem?_set_self (by rw [hv_len]; omega)]; rfl)
        · exact hcur (by rw [List.getElem?_set_self (by rw [List.length_set, hv_len]; omega)]; rfl)
      rw [show st'.core.vals[l]?.getD 0#8 = st.core.vals[l]?.getD 0#8 from
        getD_set2_ne hmem.1 hmem.2] at hcur
      obtain ⟨i, hi1, hi2, hw⟩ := h.vals_only_trl l hl hpre0 hcur; have hne : i ≠ te' := by
        rintro rfl; simp [hget] at hw
        exact hw.elim (fun e => hmem.1 e.symm) (fun e => hmem.2 e.symm)
      exact ⟨i, hi1, by simp [st']; omega, hw⟩ }

theorem TransUnrollInv.done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src off p end_v reduced saved : Nat}
    (ho : TransOuterInv c F0 F_cur s0 src off p end_v reduced st_pre)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hte : st.core.trail_end = saved) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced st := by
  have hvals_eq : st.core.vals = st_pre.core.vals := List.ext_getElem? fun l => by
    by_cases hl : l < 2 * st_pre.core.cur_vars
    · have hl1 : l < st.core.vals.length := by
        rw [h.len_ok.core_ok.vals_len]; have := ho.base.len_ok.core_ok.cur_vars_le; omega
      have hl2 : l < st_pre.core.vals.length := by
        rw [ho.base.len_ok.core_ok.vals_len]; have := ho.base.len_ok.core_ok.cur_vars_le; omega
      have hgd : st.core.vals[l]?.getD 0#8 = st_pre.core.vals[l]?.getD 0#8 := by
        by_cases h0 : st_pre.core.vals[l]?.getD 0#8 = 0#8
        · rw [h0]; exact Classical.byContradiction fun hnz => by
            obtain ⟨i, _, _, _⟩ := h.vals_only_trl l hl h0 hnz; omega
        · exact h.vals_pres l hl h0
      rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2] at hgd ⊢
      exact congrArg some hgd
    · exact h.vals_hi_pres l (by omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ :=
    ho.base.core_pres
  have hc_eq : st.core = { st_pre.core with trl := st.core.trl } := by
    rw [h.same_core, hvals_eq, hte, h.saved_eq]
  have hrefs : ∀ r ∈ fullArenaClauseRefsCore st_pre.core, r ∈ fullArenaClauseRefsCore st.core :=
    fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [hc_eq]
  exact {
    base := {
      len_ok := h.len_ok, scratch_pres := by rw [h.same_scratch]; exact ho.base.scratch_pres
      core_pres := by
        rw [hc_eq]; exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
          fun i hi => by rw [← hc_eq, h.trl_pres i (h.saved_eq ▸ c15 ▸ hi)]; exact c16 i hi, c17⟩
      off_le_end := ho.base.off_le_end, src_off := by rw [hc_eq]; exact ho.base.src_off
      src_sz := by rw [hc_eq]; exact ho.base.src_sz
      end_le_wlen := by rw [hc_eq]; exact ho.base.end_le_wlen, off_pos := ho.base.off_pos
      other_bounds := fun l hl hls => by rw [hc_eq] at hl ⊢; exact ho.base.other_bounds l hl hls
      other_pos_off := fun l hl hls p => by
        rw [hc_eq] at hl p ⊢; exact ho.base.other_pos_off l hl hls p
      disjoint_all := fun a b ha hb ne pa pb => by
        rw [hc_eq] at ha hb pa pb ⊢; exact ho.base.disjoint_all a b ha hb ne pa pb
      other_no_sent := fun l hl hls i hi => by
        rw [hc_eq] at hl hi ⊢; exact ho.base.other_no_sent l hl hls i hi
      other_slices := fun l hl hls => by
        rw [hc_eq] at hl ⊢; exact WatchSliceOk.relocate_same (k := st_pre.core) (Nat.le_refl _)
          (fun _ h => h) (fun _ _ => rfl) (ho.base.other_slices l hl hls) }
    off_le_p := ho.off_le_p, p_le_end := ho.p_le_end, red_le := ho.red_le
    src_pref := TombWatchSliceOk.mono (k := st_pre.core) (k' := st.core)
      (by rw [hc_eq]; exact Nat.le_refl _) hrefs (fun _ _ _ => by rw [hc_eq]) ho.src_pref
    src_rem := WatchSliceOk.relocate_same (k := st_pre.core) (k' := st.core)
      (by rw [hc_eq]; exact Nat.le_refl _) hrefs (fun _ _ => by rw [hc_eq]) ho.src_rem }

theorem TransUnrollInv.watch_slice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src off p end_v reduced saved nl : Nat}
    (ho : TransOuterInv c F0 F_cur s0 src off p end_v reduced st_pre)
    (hu : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hnl : nl < 2 * st.core.cur_vars) :
    fullWatchOffCore st.core nl + fullWatchSizeCore st.core nl ≤ st.core.wlen ∧ ∃ nt,
      TombWatchSliceOk F_cur st.core nl
        (fullWatchOffCore st.core nl) (fullWatchSizeCore st.core nl) nt := by
  have hsc := hu.same_core; have hcv : st.core.cur_vars = st_pre.core.cur_vars := by rw [hsc]
  have hws : st.core.wstk = st_pre.core.wstk := by rw [hsc]
  have hrefs : ∀ r ∈ fullArenaClauseRefsCore st_pre.core, r ∈ fullArenaClauseRefsCore st.core :=
    fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [hsc]
  rw [show fullWatchOffCore st.core nl = fullWatchOffCore st_pre.core nl by
      unfold fullWatchOffCore; rw [hsc],
    show fullWatchSizeCore st.core nl = fullWatchSizeCore st_pre.core nl by
      unfold fullWatchSizeCore; rw [hsc],
    show st.core.wlen = st_pre.core.wlen by rw [hsc]]
  by_cases hns : nl = src
  · subst hns; rw [ho.base.src_off, ho.base.src_sz]; exact ⟨by
      have := ho.base.off_le_end; have := ho.base.end_le_wlen; omega, reduced,
      TombWatchSliceOk.mono (by omega) hrefs (fun _ _ _ => by rw [hws]) ho.src_full_tomb⟩
  · exact ⟨ho.base.other_bounds nl (hcv ▸ hnl) hns, 0, TombWatchSliceOk.of_watchSlice
      (WatchSliceOk.relocate_same (p' := fullWatchOffCore st_pre.core nl) (by omega) hrefs
        (fun _ _ => by rw [hws]) (ho.base.other_slices nl (hcv ▸ hnl) hns))⟩

theorem tr_unroll_c0_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st_r : FullState} {src saved : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hlen_pre : st_pre.LengthsOk c) (hu_r : TransUnrollInv c F0 F_cur s0 st_pre src saved st_r)
    (hte_gt : saved < st_r.core.trail_end) (hte_r_lt : st_r.core.trail_end < 2 ^ 64) :
    let idx := (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat
    ∃ hidx : idx < st_r.core.trl.length, let ul := st_r.core.trl[idx]'hidx
      (BitVec.setWidth 64 ul).toNat < st_r.core.vals.length ∧
      (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat < st_r.core.vals.length ∧
      (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat = st_r.core.trail_end - 1 ∧
      TransUnrollInv c F0 F_cur s0 st_pre src saved { st_r with core := { st_r.core with
        vals := (st_r.core.vals.set (BitVec.setWidth 64 ul).toNat 0#8).set
          (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat 0#8,
        trail_end := (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat } } := by
  have hlen_r := hu_r.len_ok
  obtain ⟨ul, hul_get, hul_lt, hu_r'⟩ := hu_r.unroll_step hw0 hpre_vals hpre_cv hlen_pre hte_gt
  have hcv_r : st_pre.core.cur_vars ≤ c.max_vars := by
    have := hlen_r.core_ok.cur_vars_le; rw [hu_r.same_core] at this; exact this
  have hte1_bv := tr_bv64_sub1_nat (n := st_r.core.trail_end) (by omega) hte_r_lt
  have hul_vlen := tr_vals_lt (l := ul.toNat) hlen_r.core_ok (by rw [hu_r.same_core]; exact hul_lt)
  have huln_vlen := tr_vals_lt (l := (ul ^^^ 1#32).toNat) hlen_r.core_ok
    (by rw [tr_bv32_xor1, hu_r.same_core]; exact litNeg_lt_two_mul hul_lt)
  have hte1_len : (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat < st_r.core.trl.length := by
    rw [hte1_bv, hlen_r.core_ok.trl_len]
    have := hlen_r.core_ok.trail_end_le; have := hlen_r.core_ok.cur_vars_le; omega
  have hte1_bv_len : (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat <
      st_r.core.trl.length := by simpa using hte1_len
  have hul_ge2 : st_r.core.trl[(BitVec.ofNat 64
      (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len = ul := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)] using
      Option.some.inj ((List.getElem?_eq_getElem hte1_len).symm.trans (by rw [hte1_bv, hul_get]))
  exact ⟨hte1_bv_len, by rw [hul_ge2, tr_bv32_setWidth64]; exact hul_vlen,
    by rw [hul_ge2, tr_bv32_setWidth64]; exact huln_vlen, hte1_bv,
    by rw [hul_ge2, tr_bv32_setWidth64, tr_bv32_setWidth64, hte1_bv, tr_bv32_xor1]; exact hu_r'⟩

theorem tr_compact_done_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v reduced : Nat} {wu' nb_bv : BitVec 64} {idx : Nat}
    {new_sz : BitVec 32} {st : FullState} (hsp0 : FullSparseInv c F0 s0)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hb : TransOuterBase c F0 F_cur s0 src off end_v st)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hred : reduced ≤ end_v - off)
    (hsl : WatchSliceOk F_cur st.core src off (end_v - off - reduced)) (hidx : idx = 2 * src + 1)
    (hsz : new_sz = BitVec.ofNat 32 (end_v - off - reduced)) :
    let st' := { st with core :=
      { st.core with wvec := st.core.wvec.set idx new_sz, wusable := wu', num_binary := nb_bv } }
    FullSparseInv c F0 st' ∧ FullWitnessInv c F0 F_cur st'.core := by
  subst hidx; subst hsz; have hnb : ((nb_bv.toNat : Nat) : BitVec 64) = nb_bv := by simp
  simpa only [hnb] using
    hb.of_compact_done_full hsp0 hw0 hsrc_lt hred hsl (wu' := wu') (nb' := nb_bv.toNat)

theorem tr_outer_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {src off p end_v reduced : Nat} (tk : BitVec 64)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced
      { st with scratch := { st.scratch with ant_sz := tk } } :=
  h.with_scratch { h.base.len_ok.scratch_ok with
    walk_vals_len := h.base.len_ok.scratch_ok.walk_vals_len } rfl rfl

theorem tr_unroll_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved : Nat} (tk : BitVec 64)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) :
    TransUnrollInv c F0 F_cur s0
      { st_pre with scratch := { st_pre.scratch with ant_sz := tk } } src saved
      { st with scratch := { st.scratch with ant_sz := tk } } :=
  { len_ok := ⟨h.len_ok.core_ok,
      { h.len_ok.scratch_ok with walk_vals_len := h.len_ok.scratch_ok.walk_vals_len }⟩
    same_core := h.same_core
    same_scratch := by dsimp only; rw [h.same_scratch]
    saved_eq := h.saved_eq, saved_le_te := h.saved_le_te
    trl_pres := h.trl_pres, vals_pres := h.vals_pres, vals_hi_pres := h.vals_hi_pres
    bfs_trl_inv := h.bfs_trl_inv, bfs_vars_nodup := h.bfs_vars_nodup
    vals_only_trl := h.vals_only_trl }

/-! ## 3. Sparse & Witness Frame Preservation Across Callees -/

theorem fullWitnessInv_with_flags_probing {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (fl' : List (BitVec 32)) (pr' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with flags := fl', probing := pr' } :=
  let k' : FullCoreState := { k with flags := fl', probing := pr' }
  { hw with
    arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt,
      hw.arena.entails⟩
    watches := by
      have hwm := hw.watches; unfold ModeWatchesInv at hwm ⊢; by_cases hc : k.dense_mode = 0#64
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hwm
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show k'.dense_mode = 0#64 from hc))]
        exact ⟨⟨hwm.layout.bounds, hwm.layout.pos_off, hwm.layout.disjoint, hwm.layout.no_sentinel⟩,
          fun l hl => WatchSliceOk.relocate_same (k := k) (k' := k') (Nat.le_refl _)
            (fun _ h => h) (fun _ _ => rfl) (hwm.slices l hl)⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hwm
        rw [ite_eq_right_of_eq_false _ _ (eq_false (show k'.dense_mode ≠ 0#64 from hc))]
        exact ⟨⟨hwm.layout.bounds, hwm.layout.pos_off, hwm.layout.disjoint, hwm.layout.no_sentinel⟩,
          fun l hl => DenseWatchSliceOk.relocate_same (k := k) (k' := k') (Nat.le_refl _)
            (fun _ h => h) (fun _ _ => rfl) (hwm.slices l hl)⟩ }

theorem fullSparseInv_frame {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlmk : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm' : s'.core.dense_mode = 0#64)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len)
    (hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') : FullSparseInv c F0 s' := by
  obtain ⟨_, ⟨hm, hlm⟩, hnd, ⟨hll0, hel0⟩, _⟩ := hsp
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨fun v hv => by rw [hmrk]; exact hm v hv,
    fun l hl => by rw [hlmk]; exact hlm l hl⟩, ?_, ⟨?_, by rw [hel]; exact hel0⟩, hdm'⟩
  · intro r hr hng; unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [har, hal] at hr; rw [har] at hng ⊢; exact hnd r hr hng
  · intro i hi; dsimp only; unfold FullLastLearnedWf at hll0; rw [hll]
    exact (hll0 i hi).imp id (hrefs _)

theorem fullSparseInv_with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (pr' : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with probing := pr' } } :=
  let ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hsc, hdm⟩ := hsp
  ⟨⟨⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩,
    F_cur, fullWitnessInv_with_flags_probing hw s.core.flags pr'⟩, hlm, hnd, hsc, hdm⟩

theorem fullSparseInv_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (asz' : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with ant_sz := asz' } } :=
  let ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hsc, hdm⟩ := hsp
  ⟨⟨⟨hlen.core_ok, { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩,
    F_cur, hw⟩, hlm, hnd, hsc, hdm⟩

theorem fullSparseInv_clear_fl_trans {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) {v : Nat} {fv' : BitVec 32} :
    FullSparseInv c F0 { s with core := { s.core with flags := s.core.flags.set v fv' } } :=
  let ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hsc, hdm⟩ := hsp
  ⟨⟨⟨{ hlen.core_ok with flags_len := by simp [hlen.core_ok.flags_len] }, hlen.scratch_ok⟩,
    F_cur, fullWitnessInv_with_flags_probing hw (s.core.flags.set v fv') s.core.probing⟩,
    hlm, hnd, hsc, hdm⟩

theorem fullSparseInv_with_trans_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (tc' : BitVec 64) : let s' := { s with scratch := { s.scratch with trans_cnt := tc' } }
    FullSparseInv c F0 s' ∧ FullWitnessInv c F0 F_cur s'.core :=
  let ⟨⟨⟨hc, hs⟩, _, _⟩, hlm, hnd, hsc, hdm⟩ := hsp
  ⟨⟨⟨⟨hc, { hs with walk_vals_len := hs.walk_vals_len }⟩, F_cur, hw⟩, hlm, hnd, hsc, hdm⟩, hw⟩

theorem tr_sparse_with_ws1 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {ws1' : List (BitVec 32)} (hsp : FullSparseInv c F0 s) (hlen : ws1'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨⟨hsp.1.lengths.core_ok, { hsp.1.lengths.scratch_ok with work_stk1_len := hlen }⟩,
    hsp.1.witness⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

theorem tr_ws1_set_lt_bound {ws1 : List (BitVec 32)} {n cv k : Nat} {v : BitVec 32}
    (hkl : k < ws1.length) (hv : v.toNat < cv)
    (hall : ∀ i < n, (ws1[i]?.getD 0#32).toNat < cv) :
    ∀ i < n, ((ws1.set k v)[i]?.getD 0#32).toNat < cv := by
  intro i hi
  by_cases hik : i = k
  · subst hik; rw [List.getElem?_set_self hkl, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm hik)]; exact hall i hi

theorem fullWstackDefrag_sparse {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wsort' : List (BitVec 32)}
    (hsp : FullSparseInv c F0 s) (hs' : s' = { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 },
      scratch := { s.scratch with wsort := wsort' } })
    (hlen' : s'.LengthsOk c) (hlay' : WatchStackLayout s'.core)
    (hpres : ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) :
    FullSparseInv c F0 s' := by
  obtain ⟨⟨_, F_cur, hw⟩, _⟩ := id hsp
  have hw' : FullWitnessInv c F0 F_cur s'.core := by
    subst hs'; exact {
      hw with
      arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt,
        hw.arena.entails⟩
      watches := fullWstackDefrag_preserves_modeWatchesInv hw.watches hlay' rfl rfl
        (fun _ h => h) hpres }
  exact fullSparseInv_frame hsp hlen' hw' (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs'])
    (by rw [hs']; exact hsp.2.2.2.2) (by rw [hs']) (by rw [hs']) fun r hr => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rwa [hs']

theorem fullBacktrack_sparse {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)} {te' prop' cl' : Nat}
    {unass' : BitVec 64} {sc' : FullScratch} (hsp : FullSparseInv c F0 s) (hs' : s' = { s with
      core := {
        s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp', trail_end := te',
        propagated := prop', cur_level := cl', unassigned := unass' },
      scratch := sc' }) (hlen' : s'.LengthsOk c) (hpr' : FullProbeScratchPres s s')
    (hw' : ∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → 0 ≤ s.core.cur_level →
      FullWitnessInv c F0 F_cur s'.core) : FullSparseInv c F0 s' := by
  obtain ⟨⟨_, F_cur, hw⟩, _⟩ := id hsp
  exact fullSparseInv_frame hsp hlen' (hw' F0 F_cur hw (Nat.zero_le _)) (by rw [hs']) (by rw [hs'])
    (by rw [hs']) (by rw [hs']) (by rw [hs']; exact hsp.2.2.2.2) hpr'.1.1 hpr'.1.2
    fun r hr => by unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rwa [hs']

theorem fullPropagate_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64}
    {sc' : FullScratch}
    (hsp : FullSparseInv c F0 s) (hs' : s' = { s with
      core := {
        s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' },
      scratch := sc' })
    (hpres : FullExtScratchPres s s')
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm' : FullArenaPermEq s.core s'.core) : FullSparseInv c F0 s' := by
  obtain ⟨_, ⟨hm, hlm⟩, hnd0, hsc0, hdm⟩ := hsp
  have hll0 := hsc0.1
  have hdm' : s'.core.dense_mode = 0#64 := by rw [hs']; exact hdm
  have hmrk : ∀ v < c.max_vars, s'.core.mrk[v]?.getD 0#8 = 0#8 := fun v hv => by
    rw [hs']; exact hm v hv
  have hlmk : ∀ l < 2 * c.max_vars, s'.core.lit_mark[l]?.getD 0#8 = 0#8 := fun l hl => by
    rw [hs']; exact hlm l hl
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨hmrk, hlmk⟩, fun r hr hng => ?_,
    hsc0.of_pres hpres (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm'.2.1]; exact hr), hdm'⟩
  have hr0 : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rwa [hperm'.2.1] at hr
  obtain ⟨_, hgb, hpm⟩ := hperm'.2.2 r hr0
  have hng0 : fullArenaClauseGarb s r = false := by
    unfold fullArenaClauseGarb at hng ⊢; exact hgb ▸ hng
  unfold fullArenaClauseLits; exact (hpm.map (· / 2)).nodup_iff.mpr (hnd0 r hr0 hng0)

theorem fullAddUnit_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' unfl' inc' : BitVec 64} {sc' : FullScratch}
    (hsp : FullSparseInv c F0 s) (hs' : s' = { s with
      core := {
        s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unass',
        unflushed := unfl', inconsistent := inc' },
      scratch := sc' })
    (hpres : FullExtScratchPres s s')
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core) :
    FullSparseInv c F0 s' := by
  have har : s'.core.arena = s.core.arena := by rw [hs']
  have hal : s'.core.arena_len = s.core.arena_len := by rw [hs']
  have hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s' := fun r hr => by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rwa [har, hal]
  exact fullSparseInv_frame hsp hlen' hw' (by rw [hs']) (by rw [hs']) har hal
    (by rw [hs']; exact hsp.2.2.2.2) hpres.1 hpres.2 hrefs

end LeanQbe.T.Examples.Kissat.Proof.Transitive
