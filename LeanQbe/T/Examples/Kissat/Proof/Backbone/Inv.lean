/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges

/-!
# Kissat Backbone Invariants & Shared Pure Helpers (`Proof.Backbone.Inv`)

Canonical `Proof.Spec`-only definitions and lemmas shared across `Proof.Backbone.*`:
- `BbTrailInv`: multi-level trail invariant preserving level-0 prefix `0 ..< saved0`
- `BackboneProbeSeg`: active probe-level binary-reason DAG invariant on `saved ..< trail_end`
- Pure bitvector, CNF resolution, watch-slice, and `FullSparseInvW` / `FullSparseInv` helpers
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backbone

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Multi-Level Backbone Invariants -/

/-- Multi-level backbone sweep invariant tracking an upper bound `max_lvl` on all trail levels
(allowing temporary `cur_level = 0` level-0 unit propagation while `max_lvl = old_lvl > 0`). -/
structure BbTrailInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st : FullState) (saved0 max_lvl : Nat) : Prop where
  len_ok : st.LengthsOk c
  s0_l0 : s0.core.cur_level = 0
  same_core : st.core =
    { s0.core with
      vals := st.core.vals, lvl := st.core.lvl, rsns := st.core.rsns,
      trl := st.core.trl, trail_end := st.core.trail_end, cur_level := st.core.cur_level,
      confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1 }
  same_scratch : st.scratch =
    { s0.scratch with
      ant_sz := st.scratch.ant_sz, res_sz := st.scratch.res_sz,
      work_stk1 := st.scratch.work_stk1, work_stk2 := st.scratch.work_stk2 }
  saved0_eq : saved0 = s0.core.trail_end
  saved0_le : saved0 ≤ st.core.trail_end
  cur_le_max : st.core.cur_level ≤ max_lvl
  trl_prefix : ∀ i < saved0, st.core.trl[i]? = s0.core.trl[i]?
  vals_prefix : ∀ l < 2 * s0.core.cur_vars,
    s0.core.vals[l]?.getD 0#8 ≠ 0#8 → st.core.vals[l]?.getD 0#8 = s0.core.vals[l]?.getD 0#8
  vals_hi : ∀ l, 2 * s0.core.cur_vars ≤ l → st.core.vals[l]? = s0.core.vals[l]?
  lvl_prefix : ∀ i < saved0,
    let v := (s0.core.trl[i]?.getD 0#32).toNat / 2
    st.core.lvl[v]? = s0.core.lvl[v]? ∧ st.core.rsns[v]? = s0.core.rsns[v]?
  trl_lits_lt : ∀ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars
  trl_vars_nodup : ∀ i j, i < st.core.trail_end → j < st.core.trail_end →
    (st.core.trl[i]?.getD 0#32).toNat / 2 = (st.core.trl[j]?.getD 0#32).toNat / 2 → i = j
  trl_vals_ok : ∀ i < st.core.trail_end,
    let l := (st.core.trl[i]?.getD 0#32).toNat
    st.core.vals[l]?.getD 0#8 = 1#8 ∧ st.core.vals[l ^^^ 1]?.getD 0#8 = 0xFF#8
  vals_dom : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 0#8 ∨ st.core.vals[l]?.getD 0#8 = 1#8 ∨
    st.core.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_trl : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 1#8 →
    ∃ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat = l
  vals_false_trl : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 0xFF#8 →
    ∃ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le_max : ∀ i < st.core.trail_end,
    (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl
  l0_entails : ∀ i < st.core.trail_end,
    (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(st.core.trl[i]?.getD 0#32).toNat])

/-- Active probe-level binary-reason DAG invariant on `trl[saved ..< st.core.trail_end)`. -/
@[expose] def BackboneProbeSeg (F_cur : List (List Nat)) (st : FullState)
    (saved target_lvl : Nat) : Prop :=
  saved < st.core.trail_end ∧
  (∀ i < saved,
    (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < target_lvl) ∧
  (∀ i, saved ≤ i → i < st.core.trail_end →
    let p := (st.core.trl[i]?.getD 0#32).toNat
    (st.core.lvl[p / 2]?.getD 0#32).toNat = target_lvl ∧
    (saved < i →
      let rsn := st.core.rsns[p / 2]?.getD 0xFFFFFFFF#32
      (rsn &&& 0x80000000#32) ≠ 0#32 ∧
      let not_q := (rsn &&& 0x7FFFFFFF#32).toNat
      not_q < 2 * st.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [p, not_q]) ∧
      ∃ m, saved ≤ m ∧ m < i ∧ (st.core.trl[m]?.getD 0#32).toNat = not_q ^^^ 1))

/-! ## 2. Pure Bitvector, List, and CNF Resolution Helpers -/

theorem m6_getElem_congr {α : Type _} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem m6_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem bb_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bb_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bb_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l := litNeg_litNeg l

theorem bb_sext32_64_1 : BitVec.signExtend 64 1#32 = 1#64 := rfl

theorem bb_bv8_zext32_eq0 : ∀ x : BitVec 8, x.setWidth 32 = 0#32 ↔ x = 0#8 := by decide

theorem bb_bv8_sext32_eq0 : ∀ x : BitVec 8, x.signExtend 32 = 0#32 ↔ x = 0#8 := by decide

theorem bb_bv8_dom_slt0 {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bb_bv8_dom_sgt0 {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).slt (x.signExtend 32) = true ↔ x = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bb_bv64_shl1_nat (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
    Nat.mod_eq_of_lt (by omega)]

theorem bb_bv64_shl1_sext (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< BitVec.signExtend 64 1#32).toNat = 2 * x.toNat := by
  change (x <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat = 2 * x.toNat
  rw [show (BitVec.signExtend 64 1#32).toNat % 64 = 1 from rfl]
  exact bb_bv64_shl1_nat x hx

theorem bb_bv64_shl1_sext_tr (x : BitVec 64) {n : Nat} (hx : x.toNat < n)
    (hn : 2 * n < 2 ^ 32) :
    ((x <<< BitVec.signExtend 64 1#32).truncate 32).toNat < 2 * n := by
  have h1 := bb_bv64_shl1_sext x (by omega)
  rw [BitVec.toNat_setWidth, h1, Nat.mod_eq_of_lt (by omega)]; omega

theorem bb_bv64_shl1_or1_setWidth32 {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 32) :
    ((x <<< (1 : Nat)) ||| 1#64).setWidth 32 = BitVec.ofNat 32 (2 * x.toNat + 1) := by
  have hx' : x.toNat < 2 ^ 63 := by omega
  have hsh : (x <<< (1 : Nat)).toNat = 2 * x.toNat := bb_bv64_shl1_nat x hx'
  have hor : (2 * x.toNat) ||| 1 = 2 * x.toNat + 1 := by
    apply Nat.eq_of_testBit_eq
    intro i; cases i with
    | zero =>
      rw [Nat.testBit_or]
      simp [Nat.testBit_eq_decide_div_mod_eq]
    | succ k =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.zero_testBit, show (2 * x.toNat + 1) / 2 = x.toNat by omega]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, hsh, show (1#64 : BitVec 64).toNat = 1 from rfl,
    hor, Nat.mod_eq_of_lt hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

theorem bb_bv64_shl1_sext_or1_tr (x : BitVec 64) {n : Nat} (hx : x.toNat < n)
    (hn : 2 * n < 2 ^ 32) :
    (((x <<< BitVec.signExtend 64 1#32) ||| 1#64).truncate 32).toNat < 2 * n := by
  change (((x <<< (1 : Nat)) ||| 1#64).setWidth 32).toNat < 2 * n
  rw [bb_bv64_shl1_or1_setWidth32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bb_bv64_shl1_nat_div2_step (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat :=
  bb_bv64_shl1_nat x hx

theorem bb_mask7f_or_bin (x : BitVec 32) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 ∧
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (x &&& 0x7FFFFFFF#32) := by
  constructor
  · intro hz; have hbit := congrArg (fun b : BitVec 32 => b[31]) hz; simp at hbit
  · rw [BitVec.and_or_distrib_right, show (0x80000000#32 &&& 0x7FFFFFFF#32) = 0#32 from rfl,
      BitVec.or_zero, BitVec.and_assoc,
      show (0x7FFFFFFF#32 &&& 0x7FFFFFFF#32) = 0x7FFFFFFF#32 from rfl]

theorem bb_mask7f_eq_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat := by
  have heq : x &&& 0x7FFFFFFF#32 = x := by
    apply BitVec.eq_of_getElem_eq; intro i hi; simp only [BitVec.getElem_and]
    by_cases h31 : i = 31
    · subst h31; have hf : x[31] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
        simp [Nat.div_eq_of_lt h]
      simp [hf]
    · have ht : (0x7FFFFFFF#32)[i] = true := by
        rw [BitVec.getElem_eq_testBit_toNat]; have : i < 31 := by omega
        revert i this; decide
      simp [ht]
  rw [heq]

theorem bb_getD_set2_ne {α : Type} {xs : List α} {a b i : Nat} {x y d : α}
    (ha : i ≠ a) (hb : i ≠ b) : ((xs.set a x).set b y)[i]?.getD d = xs[i]?.getD d := by
  rw [List.getElem?_set_ne hb.symm, List.getElem?_set_ne ha.symm]

theorem bb_var_ne_xor {x y : Nat} (h : x / 2 ≠ y / 2) :
    x ≠ y ∧ x ≠ y ^^^ 1 ∧ x ^^^ 1 ≠ y ∧ x ^^^ 1 ≠ y ^^^ 1 :=
  ⟨fun e => h (by rw [e]), fun e => h (by rw [e, fullInv_var_xor1]),
   fun e => h (by rw [← e, fullInv_var_xor1]),
   fun e => h (by have := congrArg (· / 2) e; simpa only [fullInv_var_xor1] using this)⟩

theorem bb_pigeonhole_le : ∀ n m (f : Nat → Nat), (∀ i < m, f i < n) →
    (∀ i j, i < m → j < m → f i = f j → i = j) → m ≤ n
  | 0, 0, _, _, _ => Nat.le_refl 0
  | 0, m + 1, f, hlt, _ => absurd (hlt 0 (Nat.zero_lt_succ m)) (Nat.not_lt_zero _)
  | n + 1, m, f, hlt, hinj => by
    by_cases hex : ∃ k < m, f k = n
    · obtain ⟨k, hk, hfk⟩ := hex
      let g : Nat → Nat := fun i => if i < k then f i else f (i + 1)
      have hle := bb_pigeonhole_le n (m - 1) g
        (fun i hi => by
          dsimp only [g]; split
          · rename_i h1; have := hlt i (by omega)
            have hne : f i ≠ n := fun h => by
              have := hinj i k (by omega) hk (h.trans hfk.symm); omega
            omega
          · rename_i h1; have := hlt (i + 1) (by omega)
            have hne : f (i + 1) ≠ n := fun h => by
              have := hinj (i + 1) k (by omega) hk (h.trans hfk.symm); omega
            omega)
        (fun i j hi hj heq => by
          dsimp only [g] at heq; split at heq <;> split at heq
          · exact hinj i j (by omega) (by omega) heq
          · have := hinj i (j + 1) (by omega) (by omega) heq; omega
          · have := hinj (i + 1) j (by omega) (by omega) heq; omega
          · have := hinj (i + 1) (j + 1) (by omega) (by omega) heq; omega)
      omega
    · have hlt' : ∀ i < m, f i < n := fun i hi => by
        have := hlt i hi; have hne : f i ≠ n := fun h => hex ⟨i, hi, h⟩; omega
      exact Nat.le_trans (bb_pigeonhole_le n m f hlt' hinj) (Nat.le_succ n)

theorem bb_entails_comm2 {F : CNF Nat} {a b : Nat}
    (h : F.EntailsClause (cnfClause [a, b])) : F.EntailsClause (cnfClause [b, a]) := by
  rw [CNF.entails_clause_def] at h ⊢; intro α hα
  obtain ⟨l, hm, hs⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, by simp [hm.symm], hs⟩

/-- 2-literal resolution for multi-level backbone 1UIP:
resolving `[x ^^^ 1, y ^^^ 1]` with `[x, p ^^^ 1]` gives `[p ^^^ 1, y ^^^ 1]`. -/
theorem backbone_resolve2 {F : CNF Nat} {x y p : Nat}
    (h1 : F.EntailsClause (cnfClause [x ^^^ 1, y ^^^ 1]))
    (h2 : F.EntailsClause (cnfClause [x, p ^^^ 1])) :
    F.EntailsClause (cnfClause [p ^^^ 1, y ^^^ 1]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢
  intro α hα
  obtain ⟨l1, hm1, hs1⟩ := (clause_sat_cnfClause_iff α _).mp (h1 α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
  rcases hm1 with hl1 | hl1
  · obtain ⟨l2, hm2, hs2⟩ := (clause_sat_cnfClause_iff α _).mp (h2 α hα)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with hl2 | hl2
    · exfalso
      rw [hl1] at hs1; rw [hl2] at hs2
      exact ((sat_cnfClause_litNeg_iff α x).mp ((sat_cnfClause_singleton α _).mpr hs1))
        ((sat_cnfClause_singleton α _).mpr hs2)
    · rw [hl2] at hs2; exact (clause_sat_cnfClause_iff α _).mpr ⟨p ^^^ 1, by simp, hs2⟩
  · rw [hl1] at hs1; exact (clause_sat_cnfClause_iff α _).mpr ⟨y ^^^ 1, by simp, hs1⟩

/-- Duplicate-literal collapse `[a, a] -> [a]`. -/
theorem backbone_collapse_eq {F : CNF Nat} {a : Nat}
    (h : F.EntailsClause (cnfClause [a, a])) : F.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at h ⊢; intro α hα
  obtain ⟨l, hm, hs⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hm
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, by simp [hm], hs⟩

/-- Level-0 unit resolution `[c0, c1]` with `[c1 ^^^ 1]` gives `[c0]`. -/
theorem backbone_resolve_l0 {F : CNF Nat} {c0 c1 : Nat}
    (h1 : F.EntailsClause (cnfClause [c0, c1]))
    (h2 : F.EntailsClause (cnfClause [c1 ^^^ 1])) :
    F.EntailsClause (cnfClause [c0]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢; intro α hα
  obtain ⟨l, hm, hs⟩ := (clause_sat_cnfClause_iff α _).mp (h1 α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hl | hl
  · rw [hl] at hs; exact (clause_sat_cnfClause_iff α _).mpr ⟨c0, by simp, hs⟩
  · exfalso
    rw [hl] at hs
    exact ((sat_cnfClause_litNeg_iff α c1).mp (h2 α hα)) ((sat_cnfClause_singleton α _).mpr hs)

/-! ## 3. Watch-Slice, `FullSparseInv`, and `BbTrailInv` Lemmas -/

theorem watchSlice_inv_bin {F_cur : List (List Nat)} {k : FullCoreState} {lit p len : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    WatchSliceOk F_cur k lit (p + 1) (len - 1) := by
  cases h with
  | empty => omega
  | bin h0 _ hne hlt hent hrest =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw
    exact ⟨hne, hlt, hent, by simpa using hrest⟩
  | large h0 _ hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hf hflag

theorem watchSlice_inv_large {F_cur : List (List Nat)} {k : FullCoreState} {lit p len : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ len ∧ ∃ cref : BitVec 32, k.wstk[p + 1]? = some cref ∧
      cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
      WatchSliceOk F_cur k lit (p + 2) (len - 2) := by
  cases h with
  | empty => omega
  | bin h0 hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hflag hf
  | large h0 h1 _ hlt href hrest => exact ⟨by omega, _, h1, hlt, href, by simpa using hrest⟩

theorem bb_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := h ▸ hm

theorem fullSparseInv_frame {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlmk : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm' : s'.core.dense_mode = 0#64)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len)
    (hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullSparseInv c F0 s' := by
  obtain ⟨_, ⟨hm, hlm⟩, hnd, ⟨hll0, hel0⟩, _⟩ := hsp
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨fun v hv => by rw [hmrk]; exact hm v hv,
    fun l hl => by rw [hlmk]; exact hlm l hl⟩, ?_, ⟨?_, by rw [hel]; exact hel0⟩, hdm'⟩
  · intro r hr hng; unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [har, hal] at hr; rw [har] at hng ⊢; exact hnd r hr hng
  · intro i hi; dsimp only; unfold FullLastLearnedWf at hll0; rw [hll]
    exact (hll0 i hi).imp id (hrefs _)

theorem fullBacktrack_sparse {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)} {te' prop' cl' : Nat}
    {unass' : BitVec 64} {sc' : FullScratch} (hsp : FullSparseInv c F0 s)
    (hs' : s' = { s with
      core := { s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
      scratch := sc' })
    (hlen' : s'.LengthsOk c) (hpr' : FullProbeScratchPres s s')
    (hw' : ∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → 0 ≤ s.core.cur_level →
      FullWitnessInv c F0 F_cur s'.core) :
    FullSparseInv c F0 s' := by
  obtain ⟨⟨_, F_cur, hw⟩, _⟩ := id hsp
  exact fullSparseInv_frame hsp hlen' (hw' F0 F_cur hw (Nat.zero_le _)) (by rw [hs'])
    (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs']; exact hsp.2.2.2.2) hpr'.1.1
    hpr'.1.2 fun r hr => by unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rwa [hs']

theorem fullSparseInvW_of_prop_state {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := sc' } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hnd' : FullArenaVarsNodup
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' })
    (hpres : FullProbeScratchPres s
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' })
    (hrefs : ∀ ref ∈ fullArenaClauseRefs s,
      ref ∈ fullArenaClauseRefs
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := sc' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' } :=
  ⟨hlen', hw', hsp.2.2.1, hnd',
   ⟨fun i hi => by
     dsimp only [FullLastLearnedWf]
     rw [hpres.1.1]
     rcases hsp.2.2.2.2.1.1 i hi with hff | hmem
     · exact Or.inl hff
     · exact Or.inr (hrefs _ hmem),
    by rw [hpres.1.2]; exact hsp.2.2.2.2.1.2⟩,
   hsp.2.2.2.2.2⟩

theorem bb_sparseW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  ⟨⟨{ hsp.1.core_ok with flags_len := hfl }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem bb_sparseW_with_ws1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {ws1' : List (BitVec 32)}
    (hws1 : ws1'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with work_stk1_len := hws1 }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem bb_sparseW_with_fl_ws1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {fl' ws1' : List (BitVec 32)} (hfl : fl'.length = c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with flags := fl' }
               scratch := { s.scratch with work_stk1 := ws1' } } :=
  bb_sparseW_with_ws1 (bb_sparseW_with_flags hsp hfl) hws1

theorem bb_sparseW_with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (pr' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with probing := pr' } } :=
  ⟨⟨{ hsp.1.core_ok with }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem bb_sparseW_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (asz' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with ant_sz := asz' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem bb_sparseW_with_delayed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (dl' : Nat) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with delayed_len := dl' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem bb_sparseW_of_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hs' : s' = { s with
      core := { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' },
      scratch := { s.scratch with
        search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm' : FullArenaPermEq s.core s'.core) : FullSparseInvW c F0 F_cur s' := by
  obtain ⟨_, _, hlm, hnd0, ⟨hll0, hel0⟩, hdm⟩ := hsp; subst hs'
  refine ⟨hlen', hw', hlm, fun r hr hng => ?_, ⟨fun i hi => ?_, hel0⟩, hdm⟩
  · have hr0 : r ∈ fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs at hr ⊢; rwa [hperm'.2.1] at hr
    obtain ⟨_, hgb, hpm⟩ := hperm'.2.2 r hr0
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb at hng ⊢; exact hgb ▸ hng
    unfold fullArenaClauseLits; exact (hpm.map (· / 2)).nodup_iff.mpr (hnd0 r hr0 hng0)
  · dsimp only; unfold FullLastLearnedWf at hll0; unfold fullArenaClauseRefs
    rw [hperm'.2.1]; exact hll0 i hi

theorem BbTrailInv.init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hsp : FullSparseInvW c F0 F_cur s0) (hl0 : s0.core.cur_level = 0) :
    BbTrailInv c F0 F_cur s0 s0 s0.core.trail_end 0 := by
  have hw := hsp.2.1
  exact
    { len_ok := hsp.1, s0_l0 := hl0, same_core := rfl, same_scratch := rfl,
      saved0_eq := rfl, saved0_le := Nat.le_refl _, cur_le_max := by omega,
      trl_prefix := fun _ _ => rfl, vals_prefix := fun _ _ _ => rfl,
      vals_hi := fun _ _ => rfl, lvl_prefix := fun _ _ => ⟨rfl, rfl⟩,
      trl_lits_lt := hw.trail_lits_lt, trl_vars_nodup := hw.trail_vars_nodup,
      trl_vals_ok := fun i hi => by
        have hlt := hw.trail_lits_lt i hi
        exact ⟨(hw.vals_true_iff _ hlt).mpr ⟨i, hi, rfl⟩,
          (hw.vals_false_iff _ (litNeg_lt_two_mul hlt)).mpr
            ⟨i, hi, (litNeg_litNeg _).symm⟩⟩,
      vals_dom := hw.vals_domain,
      vals_true_trl := fun l hl h1 => (hw.vals_true_iff l hl).mp h1,
      vals_false_trl := fun l hl hff => (hw.vals_false_iff l hl).mp hff,
      lvl_le_max := fun i hi => by have := hw.lvl_le i hi; omega,
      l0_entails := hw.level0_sound }

theorem BbTrailInv.to_fullWitnessInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 0)
    (hte : st.core.trail_end = saved0) (hcl0 : st.core.cur_level = 0) :
    FullWitnessInv c F0 F_cur st.core := by
  have hsc := hbt.same_core; have hs0l0 := hbt.s0_l0
  have hcv : st.core.cur_vars = s0.core.cur_vars := by rw [hsc]
  have hte0 : st.core.trail_end = s0.core.trail_end := hte.trans hbt.saved0_eq
  have hvals_eq : ∀ l < 2 * s0.core.cur_vars,
      st.core.vals[l]?.getD 0#8 = s0.core.vals[l]?.getD 0#8 := by
    intro l hl
    rcases hw0.vals_domain l hl with h0 | h1 | hff
    · by_cases hcur : st.core.vals[l]?.getD 0#8 = 0#8
      · exact hcur.trans h0.symm
      · exfalso
        rcases hbt.vals_dom l hl with hz | hp | hn
        · exact hcur hz
        · obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl l hl hp
          rw [hte] at hi; rw [hbt.trl_prefix i hi] at heq
          have := (hw0.vals_true_iff l hl).mpr ⟨i, hbt.saved0_eq ▸ hi, heq⟩
          rw [h0] at this; cases this
        · obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl l hl hn
          rw [hte] at hi; rw [hbt.trl_prefix i hi] at heq
          have := (hw0.vals_false_iff l hl).mpr ⟨i, hbt.saved0_eq ▸ hi, heq⟩
          rw [h0] at this; cases this
    · exact hbt.vals_prefix l hl (by rw [h1]; decide)
    · exact hbt.vals_prefix l hl (by rw [hff]; decide)
  have htrl_eq : ∀ i < st.core.trail_end, st.core.trl[i]? = s0.core.trl[i]? :=
    fun i hi => hbt.trl_prefix i (hte ▸ hi)
  have hlvl_eq : ∀ i < st.core.trail_end,
      let v := (st.core.trl[i]?.getD 0#32).toNat / 2
      st.core.lvl[v]? = s0.core.lvl[v]? ∧ st.core.rsns[v]? = s0.core.rsns[v]? := by
    intro i hi; rw [htrl_eq i hi]; exact hbt.lvl_prefix i (hte ▸ hi)
  have harena_eq : st.core.arena = s0.core.arena ∧ st.core.arena_len = s0.core.arena_len :=
    ⟨by rw [hsc], by rw [hsc]⟩
  have hwat_eq : st.core.wvec = s0.core.wvec ∧ st.core.wstk = s0.core.wstk ∧
      st.core.wlen = s0.core.wlen ∧ st.core.dense_mode = s0.core.dense_mode :=
    ⟨by rw [hsc], by rw [hsc], by rw [hsc], by rw [hsc]⟩
  refine
    { ext_sound := hcv ▸ hw0.ext_sound
      inconsistent_sound := by rw [show st.core.inconsistent = s0.core.inconsistent by rw [hsc]]
                               exact hw0.inconsistent_sound
      arena := by
        have har := hw0.arena
        exact
          ⟨by rw [harena_eq.2]; exact har.len_ok,
           fun r hr => by
             rw [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] at hr
             simpa [fullArenaClauseSizeCore, fullArenaNextOff, harena_eq.1, harena_eq.2] using
               har.refs_wf r hr,
           fun r hr hsh => by
             rw [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] at hr
             simpa [fullArenaClauseSizeCore, fullArenaHdrCore, harena_eq.1, harena_eq.2] using
               har.shrk_term r hr (by simpa [fullArenaHdrCore, harena_eq.1] using hsh),
           fun r hr hng l hl => by
             rw [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] at hr
             rw [hcv]
             exact har.lits_lt r hr
               (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, harena_eq.1] using hng) l
               (by simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, harena_eq.1] using hl),
           fun r hr hng => by
             rw [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] at hr
             simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, harena_eq.1] using
               har.entails r hr (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore,
               harena_eq.1] using hng)⟩
      watches := hw0.watches.with_wstk hwat_eq.2.2.2 hcv hwat_eq.1 hwat_eq.2.1 hwat_eq.2.2.1
        (fun r hr => by simpa [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] using hr)
      cur_level_le := by omega
      trail_lits_lt := fun i hi => by rw [hcv]; exact hbt.trl_lits_lt i hi
      trail_vars_nodup := hbt.trl_vars_nodup
      vals_domain := fun l hl => hbt.vals_dom l (hcv ▸ hl)
      vals_true_iff := fun l hl => by
        rw [hvals_eq l (hcv ▸ hl), hw0.vals_true_iff l (hcv ▸ hl)]
        constructor
        · rintro ⟨i, hi, heq⟩; exact ⟨i, hte0 ▸ hi, by rw [htrl_eq i (hte0 ▸ hi), heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_eq i hi] at heq; exact ⟨i, hte0 ▸ hi, heq⟩
      vals_false_iff := fun l hl => by
        rw [hvals_eq l (hcv ▸ hl), hw0.vals_false_iff l (hcv ▸ hl)]
        constructor
        · rintro ⟨i, hi, heq⟩; exact ⟨i, hte0 ▸ hi, by rw [htrl_eq i (hte0 ▸ hi), heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_eq i hi] at heq; exact ⟨i, hte0 ▸ hi, heq⟩
      lvl_le := fun i hi => by
        rw [(hlvl_eq i hi).1, htrl_eq i hi, hcl0]
        have := hw0.lvl_le i (hte0 ▸ hi); rw [hs0l0] at this; exact this
      dec_earliest := fun i j hi hj _ hdec => by
        have hlv := hw0.lvl_le j (hte0 ▸ hj)
        rw [hs0l0] at hlv
        rw [(hlvl_eq j hj).1, htrl_eq j hj] at hdec; omega
      levels_inhabited := fun L _ _ => by omega
      level0_sound := fun i hi _ => by
        rw [htrl_eq i hi]
        exact hw0.level0_sound i (hte0 ▸ hi)
          (by have := hw0.lvl_le i (hte0 ▸ hi); rw [hs0l0] at this; omega)
      trail_pos_inv := fun i hi => by
        rw [show st.core.trail_pos = s0.core.trail_pos by rw [hsc], htrl_eq i hi]
        exact hw0.trail_pos_inv i (hte0 ▸ hi)
      level0_rsn_none := fun idx hidx _ => by
        rw [(hlvl_eq idx hidx).2, htrl_eq idx hidx]
        exact hw0.level0_rsn_none idx (hte0 ▸ hidx)
          (by have := hw0.lvl_le idx (hte0 ▸ hidx); rw [hs0l0] at this; omega)
      frame_trail_lt := fun L hL => by
        obtain rfl : L = 0 := by omega
        rw [show st.core.frame_trail = s0.core.frame_trail by rw [hsc], hte0]
        exact hw0.frame_trail_lt 0 (Nat.zero_le _)
      frame_trail_mono := fun L1 L2 h12 h2 => by
        obtain rfl : L2 = 0 := by omega
        obtain rfl : L1 = 0 := by omega
        exact Nat.le_refl _
      frame_trail_before_lt := fun L h1 h2 => by omega
      frame_dec_lt := fun L h1 h2 => by omega
      reason_inv := fun idx hidx hne => by
        have hr0 := hw0.level0_rsn_none idx (hte0 ▸ hidx)
          (by have := hw0.lvl_le idx (hte0 ▸ hidx); rw [hs0l0] at this; omega)
        rw [(hlvl_eq idx hidx).2, htrl_eq idx hidx] at hne; exact absurd hr0 hne
      reason_lit_mem := fun idx hidx hne _ => by
        have hr0 := hw0.level0_rsn_none idx (hte0 ▸ hidx)
          (by have := hw0.lvl_le idx (hte0 ▸ hidx); rw [hs0l0] at this; omega)
        rw [(hlvl_eq idx hidx).2, htrl_eq idx hidx] at hne; exact absurd hr0 hne }

theorem BbTrailInv.to_fullSparseInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 : Nat} (hsp0 : FullSparseInvW c F0 F_cur s0)
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 0)
    (hte : st.core.trail_end = saved0) (hcl0 : st.core.cur_level = 0) :
    FullSparseInvW c F0 F_cur st := by
  have hw' := hbt.to_fullWitnessInv hsp0.2.1 hte hcl0
  have hmrk_eq : st.core.mrk = s0.core.mrk := by rw [hbt.same_core]
  have hlm_eq : st.core.lit_mark = s0.core.lit_mark := by rw [hbt.same_core]
  have har_eq : st.core.arena = s0.core.arena := by rw [hbt.same_core]
  have hal_eq : st.core.arena_len = s0.core.arena_len := by rw [hbt.same_core]
  have hdm_eq : st.core.dense_mode = s0.core.dense_mode := by rw [hbt.same_core]
  have hll_eq : st.scratch.last_learned = s0.scratch.last_learned := by rw [hbt.same_scratch]
  have hex_eq : st.scratch.extend_len = s0.scratch.extend_len := by rw [hbt.same_scratch]
  have href_eq : fullArenaClauseRefs st = fullArenaClauseRefs s0 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har_eq, hal_eq]
  refine ⟨hbt.len_ok, hw',
    ⟨fun v hv => by rw [hmrk_eq]; exact hsp0.2.2.1.1 v hv,
     fun l hl => by rw [hlm_eq]; exact hsp0.2.2.1.2 l hl⟩,
    fun r hr hng => by
      rw [href_eq] at hr
      have hg : fullArenaClauseGarb s0 r = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
        rwa [← har_eq]
      have hl : fullArenaClauseLits st r = fullArenaClauseLits s0 r := by
        unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har_eq]
      rw [hl]; exact hsp0.2.2.2.1 r hr hg,
    ⟨fun i hi => by
      change st.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨ _
      rw [hll_eq, href_eq]; exact hsp0.2.2.2.2.1.1 i hi,
     by change st.scratch.extend_len ≤ c.extend_cap; rw [hex_eq]; exact hsp0.2.2.2.2.1.2⟩,
    hdm_eq.trans hsp0.2.2.2.2.2⟩

theorem BbTrailInv.var_unassigned {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl l : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (_hl : l < 2 * s0.core.cur_vars) (h0 : st.core.vals[l]?.getD 0#8 = 0#8) :
    ∀ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  intro i hi heq
  obtain ⟨hv1, hvff⟩ := hbt.trl_vals_ok i hi
  rcases (litVar_eq_iff _ _).mp heq with hl1 | hl2
  · rw [hl1, h0] at hv1; cases hv1
  · change (st.core.trl[i]?.getD 0#32).toNat = l ^^^ 1 at hl2
    rw [show (st.core.trl[i]?.getD 0#32).toNat ^^^ 1 = l by
      rw [hl2]; exact litNeg_litNeg l, h0] at hvff
    cases hvff

theorem BbTrailInv.push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl new_max : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hmax : max_lvl ≤ new_max) {lit rsn : BitVec 32} {lv_bv : BitVec 32} {cl' : Nat}
    (hlit : lit.toNat < 2 * s0.core.cur_vars) (h0 : st.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hte_lt : st.core.trail_end < c.max_vars) (hlv_le : lv_bv.toNat ≤ new_max)
    (hcl_le : cl' ≤ new_max)
    (hl0_ent : lv_bv.toNat = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := st.core.lvl.set v lv_bv
        rsns := st.core.rsns.set v rsn
        trl := st.core.trl.set st.core.trail_end lit
        trail_end := st.core.trail_end + 1
        cur_level := cl' } }
    BbTrailInv c F0 F_cur s0 st' saved0 new_max := by
  intro v st'
  have hcl := hbt.len_ok.core_ok
  have hcv_eq : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_eq ▸ hcl.cur_vars_le
  have hmiss := hbt.var_unassigned hlit h0
  have hne_lit : lit.toNat ≠ lit.toNat ^^^ 1 := (litNeg_ne_self lit.toNat).symm
  have hnot_lt : lit.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hlit
  have h0_s0 : s0.core.vals[lit.toNat]?.getD 0#8 = 0#8 :=
    Classical.byContradiction fun hnz => by rw [hbt.vals_prefix _ hlit hnz] at h0; exact hnz h0
  have h0_not : st.core.vals[lit.toNat ^^^ 1]?.getD 0#8 = 0#8 := by
    rcases hbt.vals_dom _ hnot_lt with hz | h1 | hff
    · exact hz
    · obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl _ hnot_lt h1
      exact absurd (by rw [heq, fullInv_var_xor1]) (hmiss i hi)
    · obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl _ hnot_lt hff
      rw [show (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat from litNeg_litNeg _] at heq
      exact absurd (by rw [heq]) (hmiss i hi)
  have h0_not_s0 : s0.core.vals[lit.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
    Classical.byContradiction fun hnz => by
      rw [hbt.vals_prefix _ hnot_lt hnz] at h0_not; exact hnz h0_not
  have hv_len := hcl.vals_len; have hl_len := hcl.lvl_len
  have hr_len := hcl.rsns_len; have ht_len := hcl.trl_len
  have hv_lt : v < c.max_vars := by omega
  have hte_lt_cv : st.core.trail_end < s0.core.cur_vars := by
    let f (i : Nat) : Nat :=
      if i < st.core.trail_end then (st.core.trl[i]?.getD 0#32).toNat / 2 else v
    have hle := bb_pigeonhole_le s0.core.cur_vars (st.core.trail_end + 1) f
      (fun i hi => by
        dsimp only [f]; split
        · rename_i hlt; have := hbt.trl_lits_lt i hlt; omega
        · omega)
      (fun i j hi hj heq => by
        dsimp only [f] at heq; split at heq <;> split at heq
        · exact hbt.trl_vars_nodup i j ‹_› ‹_› heq
        · exact absurd heq (hmiss i ‹_›)
        · exact absurd heq.symm (hmiss j ‹_›)
        · omega)
    omega
  have hte_eq_len : st.core.trail_end < st.core.trl.length := by omega
  exact
    { len_ok := ⟨{ hcl with
        vals_len := by simp [st', hv_len], lvl_len := by simp [st', hl_len]
        rsns_len := by simp [st', hr_len], trl_len := by simp [st', ht_len]
        trail_end_le := by simp [st', hcv_eq]; omega
        propagated_le := by simp [st']; have := hcl.propagated_le; omega }, hbt.len_ok.scratch_ok⟩
      s0_l0 := hbt.s0_l0
      same_core := by dsimp only [st']; rw [hbt.same_core]
      same_scratch := hbt.same_scratch
      saved0_eq := hbt.saved0_eq
      saved0_le := by dsimp only [st']; have := hbt.saved0_le; omega
      cur_le_max := hcl_le
      trl_prefix := fun i hi => by
        dsimp only [st']; rw [List.getElem?_set_ne (by have := hbt.saved0_le; omega)]
        exact hbt.trl_prefix i hi
      vals_prefix := fun l hl hnz => by
        dsimp only [st']
        rw [bb_getD_set2_ne (fun e => hnz (by rw [e]; exact h0_s0))
          (fun e => hnz (by rw [e]; exact h0_not_s0))]
        exact hbt.vals_prefix l hl hnz
      vals_hi := fun l hl => by
        dsimp only [st']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hbt.vals_hi l hl
      lvl_prefix := fun i hi => by
        have hti := hbt.trl_prefix i hi
        have hne_v : (s0.core.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
          rw [← hti]; exact hmiss i (by have := hbt.saved0_le; omega)
        dsimp only [st']
        rw [List.getElem?_set_ne hne_v.symm, List.getElem?_set_ne hne_v.symm]
        exact hbt.lvl_prefix i hi
      trl_lits_lt := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some]; exact hlit
        · rw [List.getElem?_set_ne (Ne.symm he)]; exact hbt.trl_lits_lt i (by omega)
      trl_vars_nodup := fun i j hi hj heq => by
        dsimp only [st'] at hi hj heq
        by_cases hie : i = st.core.trail_end <;> by_cases hje : j = st.core.trail_end
        · omega
        · subst hie; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_ne (Ne.symm hje)] at heq
          exact absurd heq.symm (hmiss j (by omega))
        · subst hje; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_ne (Ne.symm hie)] at heq
          exact absurd heq (hmiss i (by omega))
        · rw [List.getElem?_set_ne (Ne.symm hie), List.getElem?_set_ne (Ne.symm hje)] at heq
          exact hbt.trl_vars_nodup i j (by omega) (by omega) heq
      trl_vals_ok := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some]
          refine ⟨by rw [List.getElem?_set_ne hne_lit.symm,
                       List.getElem?_set_self (by omega), Option.getD_some],
                  by rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some]⟩
        · rw [List.getElem?_set_ne (Ne.symm he)]
          obtain ⟨h1, h2, h3, h4⟩ := bb_var_ne_xor (hmiss i (by omega))
          rw [bb_getD_set2_ne h1 h2, bb_getD_set2_ne h3 h4]
          exact hbt.trl_vals_ok i (by omega)
      vals_dom := fun l hl => by
        dsimp only [st']
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; right; right
          rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm h1)]
          by_cases h2 : l = lit.toNat
          · subst h2; right; left
            rw [List.getElem?_set_self (by omega), Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hbt.vals_dom l hl
      vals_true_trl := fun l hl hv1 => by
        dsimp only [st'] at hv1 ⊢
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some] at hv1
          cases hv1
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hv1
          by_cases h2 : l = lit.toNat
          · subst h2; exact ⟨st.core.trail_end, by omega, by
              rw [List.getElem?_set_self hte_eq_len, Option.getD_some]⟩
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hv1
            obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl l hl hv1
            exact ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact heq⟩
      vals_false_trl := fun l hl hvff => by
        dsimp only [st'] at hvff ⊢
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; exact ⟨st.core.trail_end, by omega, by
            rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
              show (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat from litNeg_litNeg _]⟩
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hvff
          by_cases h2 : l = lit.toNat
          · subst h2; rw [List.getElem?_set_self (by omega), Option.getD_some] at hvff; cases hvff
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hvff
            obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl l hl hvff
            exact ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact heq⟩
      lvl_le_max := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_self (by omega), Option.getD_some]; exact hlv_le
        · rw [List.getElem?_set_ne (Ne.symm he),
            List.getElem?_set_ne (Ne.symm (hmiss i (by omega)))]
          exact Nat.le_trans (hbt.lvl_le_max i (by omega)) hmax
      l0_entails := fun i hi hlv0 => by
        dsimp only [st'] at hi hlv0 ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some] at hlv0 ⊢
          rw [List.getElem?_set_self (by omega), Option.getD_some] at hlv0
          exact hl0_ent hlv0
        · rw [List.getElem?_set_ne (Ne.symm he)] at hlv0 ⊢
          rw [List.getElem?_set_ne (Ne.symm (hmiss i (by omega)))] at hlv0
          exact hbt.l0_entails i (by omega) hlv0 }

theorem BbTrailInv.pop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hsp0 : FullSparseInvW c F0 F_cur s0)
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hgt : saved0 < st.core.trail_end) :
    let te' := st.core.trail_end - 1
    let ul := st.core.trl[te']?.getD 0#32
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set ul.toNat 0#8).set (ul.toNat ^^^ 1) 0#8
        trail_end := te' } }
    ul.toNat < 2 * s0.core.cur_vars ∧ BbTrailInv c F0 F_cur s0 st' saved0 max_lvl := by
  intro te' ul st'
  have hw0 := hsp0.2.1
  have hcl := hbt.len_ok.core_ok
  have hcv_eq : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_eq ▸ hcl.cur_vars_le
  have hult : ul.toNat < 2 * s0.core.cur_vars := hbt.trl_lits_lt te' (by omega)
  have hnot_lt : ul.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hult
  have hne_ul : ul.toNat ≠ ul.toNat ^^^ 1 := (litNeg_ne_self ul.toNat).symm
  have hv_len := hcl.vals_len
  have hmiss : ∀ i < te', (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ ul.toNat / 2 :=
    fun i hi heq => by have := hbt.trl_vars_nodup i te' (by omega) (by omega) heq; omega
  have h0_s0_of : ∀ q < 2 * s0.core.cur_vars, q / 2 = ul.toNat / 2 →
      s0.core.vals[q]?.getD 0#8 = 0#8 := fun q hq hqv =>
    (hw0.vals_zero_iff hq).mpr fun k hk heq => by
      have hk_s : k < saved0 := hbt.saved0_eq ▸ hk
      have hkt := hbt.trl_prefix k hk_s
      exact hmiss k (by omega) (by rw [hkt, heq, hqv])
  have h0_ul : s0.core.vals[ul.toNat]?.getD 0#8 = 0#8 := h0_s0_of ul.toNat hult rfl
  have h0_not : s0.core.vals[ul.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
    h0_s0_of (ul.toNat ^^^ 1) hnot_lt (fullInv_var_xor1 ul.toNat)
  have hprop_le : st.core.propagated ≤ te' := by
    have hp0 : st.core.propagated = s0.core.propagated := by rw [hbt.same_core]
    have hle0 := hsp0.1.core_ok.propagated_le
    have hs0 := hbt.saved0_eq; omega
  refine ⟨hult,
    { len_ok := ⟨{ hcl with
        vals_len := by simp [st', hv_len]
        trail_end_le := by simp [st']; have := hcl.trail_end_le; omega
        propagated_le := by simp [st']; exact hprop_le }, hbt.len_ok.scratch_ok⟩
      s0_l0 := hbt.s0_l0
      same_core := by dsimp only [st']; rw [hbt.same_core]
      same_scratch := hbt.same_scratch
      saved0_eq := hbt.saved0_eq
      saved0_le := by dsimp only [st']; omega
      cur_le_max := hbt.cur_le_max
      trl_prefix := hbt.trl_prefix
      vals_prefix := fun l hl hnz => by
        dsimp only [st']
        rw [bb_getD_set2_ne (fun e => hnz (by rw [e]; exact h0_ul))
          (fun e => hnz (by rw [e]; exact h0_not))]
        exact hbt.vals_prefix l hl hnz
      vals_hi := fun l hl => by
        dsimp only [st']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hbt.vals_hi l hl
      lvl_prefix := hbt.lvl_prefix
      trl_lits_lt := fun i hi => hbt.trl_lits_lt i (by dsimp only [st'] at hi; omega)
      trl_vars_nodup := fun i j hi hj heq =>
        hbt.trl_vars_nodup i j (by dsimp only [st'] at hi; omega)
          (by dsimp only [st'] at hj; omega) heq
      trl_vals_ok := fun i hi => by
        dsimp only [st'] at hi ⊢
        obtain ⟨h1, h2, h3, h4⟩ := bb_var_ne_xor (hmiss i hi)
        rw [bb_getD_set2_ne h1 h2, bb_getD_set2_ne h3 h4]
        exact hbt.trl_vals_ok i (by omega)
      vals_dom := fun l hl => by
        dsimp only [st']
        by_cases h1 : l = ul.toNat ^^^ 1
        · subst h1; left
          rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm h1)]
          by_cases h2 : l = ul.toNat
          · subst h2; left
            rw [List.getElem?_set_self (by omega), Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hbt.vals_dom l hl
      vals_true_trl := fun l hl hv1 => by
        dsimp only [st'] at hv1 ⊢
        by_cases h1 : l = ul.toNat ^^^ 1
        · subst h1; rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some] at hv1
          cases hv1
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hv1
          by_cases h2 : l = ul.toNat
          · subst h2; rw [List.getElem?_set_self (by omega), Option.getD_some] at hv1; cases hv1
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hv1
            obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl l hl hv1
            have hne : i ≠ te' := fun he => by subst he; exact h2 heq.symm
            exact ⟨i, by omega, heq⟩
      vals_false_trl := fun l hl hvff => by
        dsimp only [st'] at hvff ⊢
        by_cases h1 : l = ul.toNat ^^^ 1
        · subst h1; rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some] at hvff
          cases hvff
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hvff
          by_cases h2 : l = ul.toNat
          · subst h2; rw [List.getElem?_set_self (by omega), Option.getD_some] at hvff; cases hvff
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hvff
            obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl l hl hvff
            have hne : i ≠ te' := fun he => by
              subst he
              have := congrArg (· ^^^ 1) heq
              rw [bb_xor1_xor1] at this
              exact h1 this.symm
            exact ⟨i, by omega, heq⟩
      lvl_le_max := fun i hi => hbt.lvl_le_max i (by dsimp only [st'] at hi; omega)
      l0_entails := fun i hi hlv0 => hbt.l0_entails i (by dsimp only [st'] at hi; omega) hlv0 }⟩

theorem BbTrailInv.with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl) (asz' : BitVec 64) :
    BbTrailInv c F0 F_cur s0
      { st with scratch := { st.scratch with ant_sz := asz' } } saved0 max_lvl :=
  { hbt with
    len_ok := ⟨hbt.len_ok.core_ok, { hbt.len_ok.scratch_ok with }⟩
    same_scratch := by dsimp only; rw [hbt.same_scratch] }

theorem BbTrailInv.with_ws1_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    {ws1' ws2' : List (BitVec 32)} {rsz' : BitVec 64}
    (h1 : ws1'.length = 2 * c.max_vars) (h2 : ws2'.length = 2 * c.max_vars) :
    BbTrailInv c F0 F_cur s0
      { st with scratch := { st.scratch with
        work_stk1 := ws1', work_stk2 := ws2', res_sz := rsz' } } saved0 max_lvl :=
  { hbt with
    len_ok := ⟨hbt.len_ok.core_ok,
      { hbt.len_ok.scratch_ok with work_stk1_len := h1, work_stk2_len := h2 }⟩
    same_scratch := by dsimp only; rw [hbt.same_scratch] }

theorem BbTrailInv.with_confl_asz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl) (c0' c1' asz' : BitVec 64) :
    BbTrailInv c F0 F_cur s0
      { st with
        core := { st.core with confl_lit0 := c0', confl_lit1 := c1' }
        scratch := { st.scratch with ant_sz := asz' } } saved0 max_lvl :=
  { hbt with
    len_ok := ⟨{ hbt.len_ok.core_ok with }, { hbt.len_ok.scratch_ok with }⟩
    same_core := by dsimp only; rw [hbt.same_core]
    same_scratch := by dsimp only; rw [hbt.same_scratch] }

theorem BbTrailInv.with_cur_level {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl new_max cl' : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hcl : cl' ≤ new_max)
    (hlvl : ∀ i < st.core.trail_end,
      (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ new_max) :
    BbTrailInv c F0 F_cur s0
      { st with core := { st.core with cur_level := cl' } } saved0 new_max :=
  { hbt with
    len_ok := ⟨{ hbt.len_ok.core_ok with }, hbt.len_ok.scratch_ok⟩
    same_core := by dsimp only; rw [hbt.same_core]
    cur_le_max := hcl
    lvl_le_max := hlvl }

theorem BbTrailInv.with_mrk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (_hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hsp0 : FullSparseInvW c F0 F_cur s0) {mrk' : List (BitVec 8)}
    (hmrk_len : mrk'.length = c.max_vars)
    (hmrk0 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) :
    mrk' = s0.core.mrk := by
  have hlen0 := hsp0.1.core_ok.mrk_len
  refine List.ext_getElem (by omega) fun v hv1 _ => ?_
  have h1 := hmrk0 v (by omega)
  have h2 := hsp0.2.2.1.1 v (by omega)
  rw [List.getElem?_eq_getElem hv1, Option.getD_some] at h1
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h2
  exact h1.trans h2.symm

theorem bb_probeSeg_push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl saved target_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hseg : BackboneProbeSeg F_cur st saved target_lvl)
    {ot not_lit : BitVec 32} {lv_bv : BitVec 32} {idx_p : Nat}
    (hot_lt : ot.toNat < 2 * s0.core.cur_vars)
    (h0 : st.core.vals[ot.toNat]?.getD 0#8 = 0#8)
    (hte_lt : st.core.trail_end < c.max_vars)
    (hlv_eq : lv_bv.toNat = target_lvl)
    (hnl_lt : not_lit.toNat < 2 * s0.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [ot.toNat, not_lit.toNat]))
    (hidx_ge : saved ≤ idx_p) (hidx_lt : idx_p < st.core.trail_end)
    (hidx_eq : (st.core.trl[idx_p]?.getD 0#32).toNat = not_lit.toNat ^^^ 1) :
    let v := ot.toNat / 2
    let rsn := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set ot.toNat 1#8).set (ot.toNat ^^^ 1) 0xFF#8
        lvl := st.core.lvl.set v lv_bv
        rsns := st.core.rsns.set v rsn
        trl := st.core.trl.set st.core.trail_end ot
        trail_end := st.core.trail_end + 1 } }
    BackboneProbeSeg F_cur st' saved target_lvl := by
  intro v rsn st'
  have hcl := hbt.len_ok.core_ok
  have hcv_eq : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_eq ▸ hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hmiss := hbt.var_unassigned hot_lt h0
  have hte_trl : st.core.trail_end < st.core.trl.length := by rw [hcl.trl_len]; omega
  have hv_lvl : v < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hv_rsn : v < st.core.rsns.length := by rw [hcl.rsns_len]; omega
  refine ⟨by dsimp only [st']; have := hseg.1; omega, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · have hi_te : i < st.core.trail_end := by have := hseg.1; omega
    dsimp only [st']
    have hti : (st.core.trl.set st.core.trail_end ot)[i]? = st.core.trl[i]? :=
      List.getElem?_set_ne (by omega)
    rw [hti, List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
    exact hseg.2.1 i hi
  · dsimp only [st'] at hi2 ⊢
    by_cases he : i = st.core.trail_end
    · subst he
      rw [List.getElem?_set_self hte_trl, Option.getD_some]
      refine ⟨by rw [List.getElem?_set_self hv_lvl, Option.getD_some]; exact hlv_eq, fun _ => ?_⟩
      rw [List.getElem?_set_self hv_rsn, Option.getD_some]
      obtain ⟨hbf, hm7⟩ := bb_mask7f_or_bin not_lit
      have hm7_nat : (rsn &&& 0x7FFFFFFF#32).toNat = not_lit.toNat := by
        dsimp only [rsn]; rw [hm7]; exact bb_mask7f_eq_of_lt (by omega)
      refine ⟨hbf, by rw [hm7_nat, hcv_eq]; exact hnl_lt, by rw [hm7_nat]; exact hent,
        idx_p, hidx_ge, hidx_lt, by rw [hm7_nat, List.getElem?_set_ne (by omega)]; exact hidx_eq⟩
    · have hi_te : i < st.core.trail_end := by omega
      rw [List.getElem?_set_ne (Ne.symm he), List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
      obtain ⟨hlv_i, hrsn_i⟩ := hseg.2.2 i hi1 hi_te
      refine ⟨hlv_i, fun hgt => ?_⟩
      rw [List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
      obtain ⟨hbf, hnq, hent_i, m, hm1, hm2, hmeq⟩ := hrsn_i hgt
      exact ⟨hbf, hnq, hent_i, m, hm1, hm2, by rw [List.getElem?_set_ne (by omega)]; exact hmeq⟩

theorem bb_probeSeg_with_confl_asz {F_cur : List (List Nat)} {st : FullState}
    {saved target_lvl : Nat} (hseg : BackboneProbeSeg F_cur st saved target_lvl)
    (c0' c1' asz' : BitVec 64) :
    BackboneProbeSeg F_cur
      { st with core := { st.core with confl_lit0 := c0', confl_lit1 := c1' }
                scratch := { st.scratch with ant_sz := asz' } } saved target_lvl := hseg

end LeanQbe.T.Examples.Kissat.Proof.Backbone
