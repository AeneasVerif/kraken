/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Substitute
public import LeanQbe.T.Examples.Kissat.Ref.Sweep
public import LeanQbe.T.Logic.C0Agrees
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Shared BIG, Watch-Slice, Arena, and Sparse-Invariant Helpers (`Proof.Substitute.Helpers`)

Provides canonical (`0` legacy `Full*` imports, `0` `import all`):
1. Scoped index-0 array accessors and `bv_c0` rewrites (`SubstArenaTactics`).
2. BIG implication-graph, equivalence, and `WatchSliceOk` scanning/compaction lemmas.
3. Arena sentinel-skip / ref-scan helpers and `FullSparseInvW` / `FullReprEquiv` preservation.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Scoped Index-0 Array & `bv_c0` Helpers (`SubstArenaTactics`) -/

namespace SubstArenaTactics

open Proof.Spec.FullArenaTactics
open scoped Proof.Spec.FullArenaTactics

@[scoped c0_load] theorem load_full_work_stk10 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] :=
  fullArr_load0 .work_stk1 hi hm

@[scoped c0_store] theorem store_full_work_stk10 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
      (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
        ⋆ R) (storeMem m i32 c.pWorkStk1 v) :=
  fullArr_store0 .work_stk1 v hi hm

@[scoped c0_load] theorem load_full_work_stk20 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWorkStk2 = some s.scratch.work_stk2[0] :=
  fullArr_load0 .work_stk2 hi hm

@[scoped c0_store] theorem store_full_work_stk20 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk2 ∧
      (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
        ⋆ R) (storeMem m i32 c.pWorkStk2 v) :=
  fullArr_store0 .work_stk2 v hi hm

@[scoped bv_c0] theorem subst_bv64_sext1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := rfl

@[scoped bv_c0] theorem subst_bv64_shl_1bv (x : BitVec 64) :
    (x <<< (1#64 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem subst_bv64_ushr_1bv (x : BitVec 64) :
    (x >>> (1#64 : BitVec 64)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem subst_bv32_ushr_1bv (x : BitVec 32) :
    (x >>> (1#32 : BitVec 32)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem subst_bv64_one_toNat : ((1 : BitVec 64)).toNat = 1 := rfl
@[scoped bv_c0] theorem subst_bv64_two_toNat : ((2 : BitVec 64)).toNat = 2 := rfl

@[scoped bv_c0] theorem subst_bv64_shl_one (x : BitVec 64) :
    (x <<< (BitVec.ofNat 64 1)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

end SubstArenaTactics

/-! ## 2. BitVec, BIG Graph, and Arena Pure Helpers -/

theorem litNeg_eq_xor1 (l : Nat) : litNeg l = l ^^^ 1 := rfl

theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bv32_trunc_toNat {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem bv32_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv64_add_toNat {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 :=
  (bv64_add_toNat (y := 1#64) (by simpa using h)).trans (by simp)

theorem bv32_add1_toNat {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv32_add2_toNat {x : BitVec 32} (h : x.toNat + 2 < 2 ^ 32) :
    (x + 2#32).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#32 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

theorem bv_ult_false_ge {w : Nat} {x y : BitVec w} (h : x.ult y = false) :
    y.toNat ≤ x.toNat :=
  Nat.le_of_not_lt fun hlt => by
    have := BitVec.ult_iff_lt.mpr (BitVec.lt_def.mpr hlt)
    rw [this] at h
    cases h

theorem nat_two_mul_xor_one (n : Nat) : (2 * n) ^^^ 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ k => simp [Nat.testBit_succ, Nat.mul_add_div (by decide : 0 < 2)]

theorem bv32_and_litMask_lt (w0 : BitVec 32) : (w0 &&& 0x7FFFFFFF#32).toNat < 0x80000000 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem bv32_bit31_eq_zero_of_lt {x : BitVec 32} (h : x.toNat < 0x80000000) :
    (x &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
    show (0#32).toNat = 0 from rfl]
  have hlt : x.toNat < 2 ^ 31 := h
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : i = 31
  · subst hi; rw [Nat.testBit_lt_two_pow hlt]; rfl
  · simp [Ne.symm hi]

theorem bv8_trunc_or1 (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x ||| 1#32) = x ||| 1#8 := by
  revert x; decide

theorem bv8_trunc_or2 (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x ||| 2#32) = x ||| 2#8 := by
  revert x; decide

theorem bv8_or1_ne0 (x : BitVec 8) : (x ||| 1#8) ≠ 0#8 := by revert x; decide
theorem bv8_or2_ne0 (x : BitVec 8) : (x ||| 2#8) ≠ 0#8 := by revert x; decide

theorem bv8_setWidth32_eq_zero {x : BitVec 8}
    (h : BitVec.setWidth 32 x = 0#32) : x = 0#8 :=
  BitVec.eq_of_toNat_eq (by
    have h1 := congrArg BitVec.toNat h; have hx := x.isLt
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
      show (0#32).toNat = 0 from rfl] at h1
    exact h1)

theorem bit23_or_shrk (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[23]) h; simp at this

theorem bit19_or_shrk (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h19 : (0x00080000#32)[i] = true → (0x00800000#32)[i] = false := by revert i hi; decide
  cases h : (0x00080000#32)[i] <;> simp [h19, h]

theorem bit23_or_garb (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h23 : (0x00800000#32)[i] = true → (0x00080000#32)[i] = false := by revert i hi; decide
  cases h : (0x00800000#32)[i] <;> simp [h23, h]

theorem bit19_or_garb_ne0 (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[19]) h; simp at this

theorem list_drop_take_map_toNat_eq_range {ar : List (BitVec 32)} {off n : Nat}
    (hbd : off + n ≤ ar.length) :
    ((ar.drop off).take n).map BitVec.toNat =
      (List.range n).map fun j => (ar[off + j]?.getD 0#32).toNat := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro j hj1 _
    simp only [List.length_map, List.length_take, List.length_drop] at hj1
    have hj : j < n := by omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem nodup_range_map_of_pairwise {n : Nat} {f : Nat → Nat}
    (hpw : ∀ i j, i < j → j < n → f i ≠ f j) : ((List.range n).map f).Nodup := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨ih fun i j hij hj => hpw i j hij (by omega), (by simp), fun x hx y hy => ?_⟩
    simp only [List.mem_map, List.mem_range, List.mem_singleton] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx; subst hy; exact hpw i k hi (Nat.lt_succ_self k)

theorem fullSubst_off3_toNat {p : BitVec 64} {k : BitVec 32}
    (hbd : p.toNat + 3 + k.toNat < 2 ^ 64) :
    (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat := by
  have hk := k.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
    show (3#64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem fullSubst_add_u32_toNat {k : BitVec 32} (hlt : k.toNat + 1 < 2 ^ 32) :
    (k + 1#32).toNat = k.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt]

theorem bv8_getElem_congr {xs : List (BitVec 8)} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (hij : i = j) :
    (xs[i]'hi) = (xs[j]'hj) := by subst hij; rfl

theorem bv32_getElem_congr {xs : List (BitVec 32)} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (hij : i = j) :
    (xs[i]'hi) = (xs[j]'hj) := by subst hij; rfl

theorem getElem_congr_idx {α : Type} {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (h : i = j) : xs[i] = xs[j] := by
  subst h; rfl

theorem list_set_getElem_self_eq {α : Type} {xs : List α} {i : Nat}
    (hi : i < xs.length) : xs.set i (xs[i]'hi) = xs := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _; by_cases hji : j = i
    · subst hji; rw [List.getElem_set_self (by omega)]
    · rw [List.getElem_set_ne (Ne.symm hji)]

theorem binReach_failed_of_pair {f : CNF Nat} {r x : Nat}
    (h1 : BinReach f r x) (h2 : BinReach f r (litNeg x)) :
    f.EntailsClause (cnfClause [litNeg r]) := by
  have e1 := binReach_sound h1; have e2 := binReach_sound h2
  rw [CNF.entails_clause_def] at e1 e2 ⊢; intro α hα
  have s1 := (clauseEvalVal_iff α _).mpr (e1 α hα)
  have s2 := (clauseEvalVal_iff α _).mpr (e2 α hα); rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg]
    at s1 s2 ⊢
  cases hr : evalLitVal α r <;> cases hx : evalLitVal α x <;> simp_all

theorem litEquiv_contra_unsat {f : CNF Nat} {a b : Nat}
    (h1 : LitEquiv f a b) (h2 : LitEquiv f (litNeg a) b) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have e1 := litEquiv_eval hα h1; have e2 := litEquiv_eval hα h2
  rw [evalLitVal_litNeg] at e2; cases ha : evalLitVal α a <;> simp_all

theorem FullReprEquiv.litEquiv {F_cur : List (List Nat)} {s : FullState}
    (h : FullReprEquiv F_cur s) {l : Nat} (hl : l < 2 * s.core.cur_vars) :
    LitEquiv (cnfOfClauses F_cur) l (s.core.repr[l]?.getD 0#32).toNat :=
  ⟨(h l hl).2.2, (h l hl).2.1⟩

theorem FullReprEquiv.lt {F_cur : List (List Nat)} {s : FullState}
    (h : FullReprEquiv F_cur s) {l : Nat} (hl : l < 2 * s.core.cur_vars) :
    (s.core.repr[l]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
  (h l hl).1

theorem entails_bin_subst {f : CNF Nat} {a b a' b' : Nat}
    (ha : LitEquiv f a a') (hb : LitEquiv f b b')
    (hc : f.EntailsClause (cnfClause [a, b])) :
    f.EntailsClause (cnfClause [a', b']) := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  rw [← litEquiv_eval hα ha, ← litEquiv_eval hα hb]; exact h1

theorem entails_unit_of_dup {f : CNF Nat} {a : Nat}
    (hc : f.EntailsClause (cnfClause [a, a])) :
    f.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  simpa using h1

theorem entails_clause_subst {f : CNF Nat} {cs cs' : List Nat}
    (hmap : ∀ l ∈ cs, ∃ l' ∈ cs', LitEquiv f l l')
    (hc : f.EntailsClause (cnfClause cs)) :
    f.EntailsClause (cnfClause cs') := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  rw [clauseEvalVal, List.any_eq_true] at h1 ⊢
  obtain ⟨l, hl, hsat⟩ := h1
  obtain ⟨l', hl', heq⟩ := hmap l hl
  exact ⟨l', hl', by rw [← litEquiv_eval hα heq]; exact hsat⟩

theorem entails_taut {f : CNF Nat} {l : Nat} :
    f.EntailsClause (cnfClause [l, l ^^^ 1]) := by
  rw [CNF.entails_clause_def]
  intro τ _
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false]
  by_cases hp : l % 2 = 0
  · have hle : l = 2 * (l / 2) := by omega
    have hx : l ^^^ 1 = 2 * (l / 2) + 1 :=
      (congrArg (· ^^^ 1) hle).trans (nat_two_mul_xor_one (l / 2))
    rw [hx, hle]
    simp only [evalLitVal, litVar, litSign, Nat.mul_mod_right,
      Nat.mul_div_right _ (by decide : 0 < 2), Nat.mul_add_mod,
      Nat.mul_add_div (by decide : 0 < 2)]
    cases τ (l / 2) <;> decide
  · have hlo : l = 2 * (l / 2) + 1 := by omega
    have h0 := nat_two_mul_xor_one (l / 2)
    have hx : l ^^^ 1 = 2 * (l / 2) := by
      have h1 : (2 * (l / 2) + 1) ^^^ 1 = 2 * (l / 2) := by
        rw [← h0, Nat.xor_assoc]; simp
      exact (congrArg (· ^^^ 1) hlo).trans h1
    rw [hx, hlo]
    simp only [evalLitVal, litVar, litSign, Nat.mul_mod_right,
      Nat.mul_div_right _ (by decide : 0 < 2), Nat.mul_add_mod,
      Nat.mul_add_div (by decide : 0 < 2)]
    cases τ (l / 2) <;> decide

/-! ## 3. Watch-Slice Binary Scanning & Compaction Helpers -/

/-- Zero-initialized `tarjan_mark[0 ..< cur_vars)` predicate. -/
@[expose] def TmkZero (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0#32

theorem TmkZero.congr {s s' : FullState} (h : TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

/-- Extract all binary-watch target literals from a `WatchSliceOk` watch slice. -/
@[expose] def sliceBinsFrom (wstk : List (BitVec 32)) : Nat → Nat → List Nat
  | _, 0 => []
  | p, rem + 1 =>
    let w0 := wstk[p]?.getD 0#32
    if (w0 &&& 0x80000000#32) ≠ 0#32 then
      (w0 &&& 0x7FFFFFFF#32).toNat :: sliceBinsFrom wstk (p + 1) rem
    else match rem with
      | 0 => []
      | rem' + 1 => sliceBinsFrom wstk (p + 2) rem'

theorem watchSlice_step_nonbin {F_cur : List (List Nat)} {k : FullCoreState} {nl p rem : Nat}
    (h : WatchSliceOk F_cur k nl p rem) (hpos : 0 < rem)
    (hflag : (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) = 0#32) :
    ∃ w0 cref, 2 ≤ rem ∧ k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cref ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cref.toNat < 0x80000000 ∧
      cref.toNat ∈ fullArenaClauseRefsCore k ∧ WatchSliceOk F_cur k nl (p + 2) (rem - 2) ∧
      sliceBinsFrom k.wstk p rem = sliceBinsFrom k.wstk (p + 2) (rem - 2) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf => rw [hp, Option.getD_some] at hflag; exact absurd hflag hf
  | @large _ r w0 cref hp hp1 hf hlt href hrest =>
    refine ⟨w0, cref, by omega, hp, hp1, hf, hlt, href, by simpa using hrest, ?_⟩
    change sliceBinsFrom k.wstk p (r + 1 + 1) = sliceBinsFrom k.wstk (p + 2) (r + 2 - 2)
    conv => lhs; unfold sliceBinsFrom
    simp [hp, hf]

theorem watchSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState} {nl p rem : Nat}
    (h : WatchSliceOk F_cur k nl p rem) (hpos : 0 < rem)
    (hflag : (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    ∃ w0, k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [nl, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k nl (p + 1) (rem - 1) ∧
      sliceBinsFrom k.wstk p rem =
        (w0 &&& 0x7FFFFFFF#32).toNat :: sliceBinsFrom k.wstk (p + 1) (rem - 1) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf hne hlt hent hrest =>
    refine ⟨w0, hp, hf, hne, hlt, hent, by simpa using hrest, ?_⟩
    conv => lhs; unfold sliceBinsFrom
    simp [hp, hf]
  | @large _ _ w0 _ hp _ hf => rw [hp, Option.getD_some] at hflag; exact absurd hf hflag

theorem watchSlice_mem_sliceBinsFrom {F_cur : List (List Nat)} {k : FullCoreState}
    {nl p rem : Nat} (h : WatchSliceOk F_cur k nl p rem) :
    ∀ ot ∈ sliceBinsFrom k.wstk p rem,
      ot < 2 * k.cur_vars ∧ BinEdge (cnfOfClauses F_cur) (nl ^^^ 1) ot := by
  induction h with
  | empty => intro _ hm; simp [sliceBinsFrom] at hm
  | @bin p r w0 hp hf _ hlt hent _ ih =>
    intro ot hm
    have heq : sliceBinsFrom k.wstk p (r + 1) =
        (w0 &&& 0x7FFFFFFF#32).toNat :: sliceBinsFrom k.wstk (p + 1) r := by
      conv => lhs; unfold sliceBinsFrom
      simp [hp, hf]
    rw [heq, List.mem_cons] at hm; rcases hm with rfl | hm'
    · refine ⟨hlt, ?_⟩; unfold BinEdge; have hnn : litNeg (nl ^^^ 1) = nl := litNeg_litNeg nl
      rwa [hnn]
    · exact ih ot hm'
  | @large p r w0 _ hp _ hf _ _ _ ih =>
    intro ot hm
    have heq : sliceBinsFrom k.wstk p (r + 2) = sliceBinsFrom k.wstk (p + 2) r := by
      change sliceBinsFrom k.wstk p (r + 1 + 1) = _; conv => lhs; unfold sliceBinsFrom
      simp [hp, hf]
    rw [heq] at hm; exact ih ot hm

theorem wsStepNonbin {F_cur : List (List Nat)} {k : FullCoreState} {nl p rem : Nat}
    (h : WatchSliceOk F_cur k nl p rem) (hpos : 0 < rem)
    (hflag : (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) = 0#32) :
    ∃ w0 cref,
      2 ≤ rem ∧ k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cref ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cref.toNat < 0x80000000 ∧
      cref.toNat ∈ fullArenaClauseRefsCore k ∧
      WatchSliceOk F_cur k nl (p + 2) (rem - 2) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf => rw [hp, Option.getD_some] at hflag; exact absurd hflag hf
  | @large _ r w0 cref hp hp1 hf hlt href hrest =>
    exact ⟨w0, cref, by omega, hp, hp1, hf, hlt, href, by simpa using hrest⟩

theorem wsStepBin {F_cur : List (List Nat)} {k : FullCoreState} {nl p rem : Nat}
    (h : WatchSliceOk F_cur k nl p rem) (hpos : 0 < rem)
    (hflag : (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    ∃ w0,
      k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [nl, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k nl (p + 1) (rem - 1) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf hne hlt hent hrest =>
    exact ⟨w0, hp, hf, hne, hlt, hent, by simpa using hrest⟩
  | @large _ _ w0 _ hp _ hf => rw [hp, Option.getD_some] at hflag; exact absurd hf hflag

theorem wsRelocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem wsAppendBin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @large p rem w cref hp hp1 hf hl href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ href) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

theorem wsAppendLarge {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .large (by simpa using hw0) (by simpa using hw1) hflag hlt href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem wsBinLtOfFlag {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceOk F_cur k lit p rem) :
    ∀ c, p ≤ c → c < p + rem →
      (k.wstk[c]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 →
      (k.wstk[c]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars := by
  induction h with
  | empty => intro c hc1 hc2; omega
  | @bin p r w0 hp _ _ hlt _ _ ih =>
    intro c hc1 hc2 hf
    by_cases hcp : c = p
    · subst hcp; rw [hp, Option.getD_some]; exact hlt
    · exact ih c (by omega) (by omega) hf
  | @large p r w0 cr hp hp1 hfw hlt _ _ ih =>
    intro c hc1 hc2 hf
    by_cases hcp : c = p
    · subst hcp; rw [hp, Option.getD_some] at hf; exact absurd hfw hf
    · by_cases hcp1 : c = p + 1
      · subst hcp1; rw [hp1, Option.getD_some] at hf
        exact absurd (bv32_bit31_eq_zero_of_lt hlt) hf
      · exact ih c (by omega) (by omega) hf

/-! ## 4. Arena Sentinel, Mask & Sparse-Invariant Transition Helpers -/

theorem arenaVarsNodup_of_arena_eq {s s' : FullState}
    (ha : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FullArenaVarsNodup s) : FullArenaVarsNodup s' := fun r hr hng => by
  unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr
  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng
  unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
  rw [ha, hal] at hr; rw [ha] at hng ⊢; exact h r hr hng

theorem fullArenaSkipShrk_of_first_sentinel {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 →
      (∀ i, p ≤ i → i < t → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      t - p + 1 ≤ fuel → fullArenaSkipShrk ar alen p fuel = t + 1
  | 0, _, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hne_lt, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]
    by_cases hpeq : p = t
    · subst p; simp [hsent]
    · have hne : ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
        hne_lt p (Nat.le_refl p) (by omega)
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      exact fullArenaSkipShrk_of_first_sentinel (by omega) hta hsent
        (fun i hi1 hi2 => hne_lt i (by omega) hi2) (by omega)

theorem fullArenaSkipShrk_first_sentinel {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 →
      t - p + 1 ≤ fuel →
      ∃ t0, p ≤ t0 ∧ t0 ≤ t ∧ fullArenaSkipShrk ar alen p fuel = t0 + 1 ∧
        ar[t0]? = some 0xFFFFFFFF#32 ∧
        (∀ i, p ≤ i → i < t0 → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
  | 0, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]; split
    · rename_i hne
      have hp_ne : p ≠ t := by rintro rfl; simp [hsent] at hne
      obtain ⟨t0, h1, h2, h3, h4, h5⟩ := fullArenaSkipShrk_first_sentinel (ar := ar)
        (alen := alen) (t := t) (fuel := fuel) (p := p + 1) (by omega) hta hsent (by omega)
      refine ⟨t0, by omega, h2, h3, h4, fun i hi1 hi2 => ?_⟩
      by_cases hip : i = p
      · subst i; exact hne
      · exact h5 i (by omega) hi2
    · rename_i heq
      have heqv : ar[p]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
        Classical.byContradiction fun hn => heq hn
      have hlen_t : t < ar.length := (List.getElem?_eq_some_iff.mp hsent).1
      have hp_some : ar[p]? = some (ar[p]'(by omega)) := List.getElem?_eq_getElem (by omega)
      rw [hp_some, Option.getD_some] at heqv
      exact ⟨p, Nat.le_refl p, hpt, rfl, by rw [hp_some, heqv], fun _ h1 h2 => by omega⟩

theorem fullArenaScanRefs_next {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos p : Nat}, alen - pos ≤ fuel →
      (∀ r ∈ fullArenaScanRefs ar alen pos fuel,
        fullArenaNextOff ar alen r = alen ∨ fullArenaNextOff ar alen r + 3 ≤ alen) →
      p ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen p = alen ∨
        fullArenaNextOff ar alen p ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, _, hp => by simp [fullArenaScanRefs] at hp
  | fuel + 1, pos, p, hfl, hch, hp => by
    unfold fullArenaScanRefs at hp hch ⊢; split at hp
    · rename_i hle
      have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hp hch ⊢
      rcases hp with rfl | hrest
      · rcases hch p (Or.inl rfl) with hend | hmore
        · exact Or.inl hend
        · right; right
          cases hfuel : fuel with
          | zero => omega
          | succ f' =>
            have hle' : alen - fullArenaNextOff ar alen p ≤ f' + 1 := by omega
            unfold fullArenaScanRefs; simp [hmore]
      · exact (fullArenaScanRefs_next (by omega)
          (fun r hr => hch r (Or.inr hr)) hrest).elim Or.inl fun hm => Or.inr (Or.inr hm)
    · simp at hp

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) :
    0 = k.arena_len ∨ 0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · exact Or.inl hz.symm
  · right; cases hal : k.arena_len with
    | zero => omega
    | succ f =>
      rw [hal] at h3
      unfold fullArenaClauseRefsCore; rw [hal]; unfold fullArenaScanRefs; simp [h3]

theorem fullArenaClauseRefs_next_or_end {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) {p : Nat}
    (hp : p ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len p = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len p ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next (Nat.sub_le _ _) (fun r hr => (ha.refs_wf r hr).2.2.2.2) hp

/-- State mask covering all fields mutated by `full_tarjan_scc`. -/
@[expose] def tarjanSccMask (s : FullState) : FullState :=
  { s with
    core := { s.core with repr := [], tmp_cnt := 0, inconsistent := 0#64 }
    scratch := { s.scratch with
      tarjan_mark := [], tarjan_reach := [], work_stk1 := [], work_stk2 := [],
      wsort := [], shrink_stk := [], res_sz := 0#64 } }

theorem agrees_popScc_to_tarjan {s st st' : FullState}
    (h1 : AgreesExcept tarjanSccMask s st) (h2 : AgreesExcept fullPopSccMask st st') :
    AgreesExcept tarjanSccMask s st' := by
  unfold AgreesExcept at h1 h2 ⊢
  have heq : ∀ t, tarjanSccMask (fullPopSccMask t) = tarjanSccMask t := fun _ => rfl
  rw [← heq st', h2, heq st, h1]

theorem agrees_tarjanSccMask_eq {s0 st : FullState}
    (hag : AgreesExcept tarjanSccMask s0 st) :
    ({ s0 with
        core := { s0.core with
          repr := st.core.repr, tmp_cnt := st.core.tmp_cnt
          inconsistent := st.core.inconsistent }
        scratch := { s0.scratch with
          tarjan_mark := st.scratch.tarjan_mark, tarjan_reach := st.scratch.tarjan_reach
          work_stk1 := st.scratch.work_stk1, work_stk2 := st.scratch.work_stk2
          wsort := st.scratch.wsort, shrink_stk := st.scratch.shrink_stk
          res_sz := st.scratch.res_sz } } : FullState) = st := by
  rcases s0 with ⟨c0, sc0⟩; rcases st with ⟨c1, sc1⟩
  cases c0; cases c1; cases sc0; cases sc1
  simp only [AgreesExcept, tarjanSccMask] at hag
  injection hag with hc hsc; cases hc; cases hsc; rfl

theorem tarjanScc_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hag : AgreesExcept tarjanSccMask s0 st)
    (hinc : st.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur st.core := by
  have hcv := hag.get (·.core.cur_vars); have hal := hag.get (·.core.arena_len)
  have har := hag.get (·.core.arena); have hwv := hag.get (·.core.wvec)
  have hws := hag.get (·.core.wstk); have hwl := hag.get (·.core.wlen)
  have hdm := hag.get (·.core.dense_mode); have hvl := hag.get (·.core.vals)
  have hlv := hag.get (·.core.lvl); have hrs := hag.get (·.core.rsns)
  have htr := hag.get (·.core.trl); have htp := hag.get (·.core.trail_pos)
  have hte := hag.get (·.core.trail_end); have hcl := hag.get (·.core.cur_level)
  have hft := hag.get (·.core.frame_trail); have hfd := hag.get (·.core.frame_dec)
  have hrefs : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore s0.core := by
    unfold fullArenaClauseRefsCore; rw [har, hal]
  have hgarb : ∀ r, fullArenaClauseGarbCore st.core r = fullArenaClauseGarbCore s0.core r :=
    fun r => by unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
  have hlits : ∀ r, fullArenaClauseLitsCore st.core r = fullArenaClauseLitsCore s0.core r :=
    fun r => by unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
  have hsz : ∀ r, fullArenaClauseSizeCore st.core r = fullArenaClauseSizeCore s0.core r :=
    fun r => by unfold fullArenaClauseSizeCore; rw [har]
  exact
    { ext_sound := by rw [hcv]; exact hw0.ext_sound, inconsistent_sound := hinc
      arena :=
        { len_ok := by rw [hal]; exact hw0.arena.len_ok
          refs_wf := fun r hr => by
            rw [hrefs] at hr; rw [hal, har, hsz]; exact hw0.arena.refs_wf r hr
          shrk_term := fun r hr hsh => by
            rw [hrefs] at hr; unfold fullArenaHdrCore at hsh; rw [har] at hsh
            rw [hsz, hal, har]; exact hw0.arena.shrk_term r hr hsh
          lits_lt := fun r hr hg l hl => by
            rw [hrefs] at hr; rw [hgarb] at hg; rw [hlits] at hl; rw [hcv]
            exact hw0.arena.lits_lt r hr hg l hl
          entails := fun r hr hg => by
            rw [hrefs] at hr; rw [hgarb] at hg; rw [hlits]; exact hw0.arena.entails r hr hg }
      watches := hw0.watches.with_wstk hdm hcv hwv hws hwl (fun r hr => by rw [hrefs]; exact hr)
      cur_level_le := by rw [hcl, hte]; exact hw0.cur_level_le
      trail_lits_lt := fun i hi => by rw [htr, hcv]; exact hw0.trail_lits_lt i (hte ▸ hi)
      trail_vars_nodup := fun i j hi hj h => by
        rw [htr] at h; exact hw0.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj) h
      vals_domain := fun l hl => by rw [hvl]; exact hw0.vals_domain l (hcv ▸ hl)
      vals_true_iff := fun l hl => by rw [hvl, hte, htr]; exact hw0.vals_true_iff l (hcv ▸ hl)
      vals_false_iff := fun l hl => by rw [hvl, hte, htr]; exact hw0.vals_false_iff l (hcv ▸ hl)
      lvl_le := fun i hi => by rw [hlv, htr, hcl]; exact hw0.lvl_le i (hte ▸ hi)
      dec_earliest := fun i j hi hj h1 h2 => by
        rw [hlv, htr] at h1; rw [hlv, hrs, htr] at h2
        exact hw0.dec_earliest i j (hte ▸ hi) (hte ▸ hj) h1 h2
      levels_inhabited := fun L h1 h2 => by
        rw [hte, hlv, htr]; exact hw0.levels_inhabited L h1 (hcl ▸ h2)
      level0_sound := fun i hi hl0 => by
        rw [hlv, htr] at hl0; rw [htr]; exact hw0.level0_sound i (hte ▸ hi) hl0
      trail_pos_inv := fun i hi => by rw [htp, htr]; exact hw0.trail_pos_inv i (hte ▸ hi)
      level0_rsn_none := fun i hi hl0 => by
        rw [hlv, htr] at hl0; rw [hrs, htr]; exact hw0.level0_rsn_none i (hte ▸ hi) hl0
      frame_trail_lt := fun L hL => by rw [hft, hte]; exact hw0.frame_trail_lt L (hcl ▸ hL)
      frame_trail_mono := fun L1 L2 h1 h2 => by
        rw [hft]; exact hw0.frame_trail_mono L1 L2 h1 (hcl ▸ h2)
      frame_trail_before_lt := fun L h1 h2 i hi => by
        rw [hft] at hi; rw [hlv, htr]; exact hw0.frame_trail_before_lt L h1 (hcl ▸ h2) i hi
      frame_dec_lt := fun L h1 h2 => by rw [hfd, hcv]; exact hw0.frame_dec_lt L h1 (hcl ▸ h2)
      reason_inv := fun i hi hne => by
        rw [hrs, htr] at hne ⊢; rw [hlv, hcv, hrefs]
        have hr := hw0.reason_inv i (hte ▸ hi) hne
        by_cases hb : (s0.core.rsns[(s0.core.trl[i]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hb] at hr ⊢; exact hr
        · rw [ite_eq_right hb] at hr ⊢; rw [hgarb, hlits]; exact hr
      reason_lit_mem := fun i hi hne hlg => by
        rw [hrs, htr] at hne hlg ⊢; rw [hlits]; exact hw0.reason_lit_mem i (hte ▸ hi) hne hlg }

theorem tarjanScc_preserves_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (hsp0 : FullSparseInvW c F0 F_cur s0)
    (hag : AgreesExcept tarjanSccMask s0 st) (hlen : st.LengthsOk c)
    (hinc : st.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullSparseInvW c F0 F_cur st :=
  ⟨hlen, tarjanScc_preserves_witness hsp0.2.1 hag hinc,
   ⟨fun v hv => by rw [hag.get (·.core.mrk)]; exact hsp0.2.2.1.1 v hv,
    fun l hl => by rw [hag.get (·.core.lit_mark)]; exact hsp0.2.2.1.2 l hl⟩,
   arenaVarsNodup_of_arena_eq (hag.get (·.core.arena)) (hag.get (·.core.arena_len))
     hsp0.2.2.2.1,
   ⟨fun i hi => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore
      rw [hag.get (·.core.arena), hag.get (·.core.arena_len), hag.get (·.scratch.last_learned)]
      exact hsp0.2.2.2.2.1.1 i hi,
    by rw [hag.get (·.scratch.extend_len)]; exact hsp0.2.2.2.2.1.2⟩,
   by rw [hag.get (·.core.dense_mode)]; exact hsp0.2.2.2.2.2⟩

theorem fullWitnessInv_with_oom {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (oom' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullSparseInvW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (oom' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with oom := oom' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    fullWitnessInv_with_oom hsp.2.1 oom',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem fullWitnessInv_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with inconsistent := inc' } :=
  { hw with
    inconsistent_sound := fun _ => hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullSparseInvW_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    fullWitnessInv_with_inc hsp.2.1 hu inc',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem rewriteBins_slice_preserves_fullSparse {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) {l q : Nat}
    (hl : l < 2 * s.core.cur_vars)
    (hq_lo : fullWatchOff s l ≤ q) (hq_hi : q ≤ fullWatchOff s l + fullWatchSize s l)
    {wstk' : List (BitVec 32)} {lm' : List (BitVec 8)} {wu' nb' : BitVec 64}
    {ws1' ws2' : List (BitVec 32)}
    (hwstk_len : wstk'.length = c.wcap)
    (hlm_len : lm'.length = 2 * c.max_vars)
    (hws1_len : ws1'.length = 2 * c.max_vars)
    (hws2_len : ws2'.length = 2 * c.max_vars)
    (hlm_zero : ∀ x < 2 * c.max_vars, lm'[x]?.getD 0#8 = 0#8)
    (hwstk_out : ∀ idx, (idx < fullWatchOff s l ∨ fullWatchOff s l + fullWatchSize s l ≤ idx) →
      wstk'[idx]? = s.core.wstk[idx]?)
    (hwstk_slice : WatchSliceOk F_cur
      { s.core with wstk := wstk' } l (fullWatchOff s l) (q - fullWatchOff s l)) :
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            lit_mark := lm'
            wvec := s.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - fullWatchOff s l))
            wstk := wstk', wusable := wu', num_binary := nb' }
        scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2' } }
    FullSparseInvW c F0 F_cur s' := by
  intro s'
  dsimp only [fullWatchOff, fullWatchSize] at *
  have hcl := hsp.1.core_ok; have hsl := hsp.1.scratch_ok
  have hw := c.hwcap; have hmx := c.hmaxv; unfold dimacsBound at hw hmx
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len; have hwle := hcl.wlen_le
  have hwat : WatchesInv F_cur s.core := by
    have hm := hsp.2.1.watches; unfold ModeWatchesInv at hm
    simp only [hsp.2.2.2.2.2, ↓reduceIte] at hm; exact hm
  have hbound_l := hwat.layout.bounds l hl
  have hsz_lt32 : fullWatchSizeCore s.core l < 2 ^ 32 := (s.core.wvec[2 * l + 1]?.getD 0#32).isLt
  have hq_lt32 : q - fullWatchOffCore s.core l < 2 ^ 32 := by omega
  have hsz_l' : fullWatchSizeCore s'.core l = q - fullWatchOffCore s.core l := by
    unfold fullWatchSizeCore; dsimp only [s']
    rw [List.getElem?_set_self (by omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq_lt32]
  have hoff_l' : fullWatchOffCore s'.core l = fullWatchOffCore s.core l := by
    unfold fullWatchOffCore; dsimp only [s']
    rw [List.getElem?_set_ne (by omega)]
  have hother_w : ∀ l' ≠ l,
      fullWatchOffCore s'.core l' = fullWatchOffCore s.core l' ∧
      fullWatchSizeCore s'.core l' = fullWatchSizeCore s.core l' := by
    intro l' hne
    unfold fullWatchOffCore fullWatchSizeCore; dsimp only [s']
    exact ⟨by rw [List.getElem?_set_ne (by omega)],
           by rw [List.getElem?_set_ne (by omega)]⟩
  have hcv' : s'.core.cur_vars = s.core.cur_vars := rfl
  have hwle' : s'.core.wlen = s.core.wlen := rfl
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hwat' : ModeWatchesInv F_cur s'.core := by
    unfold ModeWatchesInv
    simp only [show s'.core.dense_mode = 0#64 from hsp.2.2.2.2.2, ↓reduceIte]
    refine WatchesInv.of_slices (fun l' hl' => ?_) (fun l' hl' hp => ?_)
      (fun l1 l2 h1 h2 hne hp1 hp2 => ?_) (fun l' hl' => ?_)
    · rw [hcv'] at hl'; rw [hwle']
      by_cases hll : l' = l
      · rw [hll, hoff_l', hsz_l']; omega
      · obtain ⟨ho, hs⟩ := hother_w l' hll; rw [ho, hs]; exact hwat.layout.bounds l' hl'
    · rw [hcv'] at hl'
      by_cases hll : l' = l
      · rw [hll, hoff_l']; rw [hll, hsz_l'] at hp
        exact hwat.layout.pos_off l hl (by omega)
      · obtain ⟨ho, hs⟩ := hother_w l' hll; rw [ho]; rw [hs] at hp
        exact hwat.layout.pos_off l' hl' hp
    · rw [hcv'] at h1 h2
      have hle1 : fullWatchOffCore s'.core l1 = fullWatchOffCore s.core l1 ∧
          fullWatchSizeCore s'.core l1 ≤ fullWatchSizeCore s.core l1 ∧
          0 < fullWatchSizeCore s.core l1 := by
        by_cases h1l : l1 = l
        · rw [h1l, hoff_l', hsz_l']; rw [h1l, hsz_l'] at hp1
          exact ⟨rfl, by omega, by omega⟩
        · obtain ⟨ho, hs⟩ := hother_w l1 h1l; rw [ho, hs]
          exact ⟨rfl, by omega, by omega⟩
      have hle2 : fullWatchOffCore s'.core l2 = fullWatchOffCore s.core l2 ∧
          fullWatchSizeCore s'.core l2 ≤ fullWatchSizeCore s.core l2 ∧
          0 < fullWatchSizeCore s.core l2 := by
        by_cases h2l : l2 = l
        · rw [h2l, hoff_l', hsz_l']; rw [h2l, hsz_l'] at hp2
          exact ⟨rfl, by omega, by omega⟩
        · obtain ⟨ho, hs⟩ := hother_w l2 h2l; rw [ho, hs]
          exact ⟨rfl, by omega, by omega⟩
      have hd := hwat.layout.disjoint l1 l2 h1 h2 hne hle1.2.2 hle2.2.2
      omega
    · rw [hcv'] at hl'
      by_cases hll : l' = l
      · rw [hll, hoff_l', hsz_l']
        exact wsRelocate (k := { s.core with wstk := wstk' }) (k' := s'.core)
          hrefl (Nat.le_refl _) (fun _ hr => hr) (fun _ _ => rfl) hwstk_slice
      · obtain ⟨ho, hs⟩ := hother_w l' hll; rw [ho, hs]
        by_cases hsz0 : fullWatchSizeCore s.core l' = 0
        · rw [hsz0]; exact .empty
        · by_cases hszl0 : fullWatchSizeCore s.core l = 0
          · exact (hwat.slices l' hl').mono (k := s.core) (k' := s'.core) hrefl (Nat.le_refl _)
              (fun _ hr => hr) fun idx hi1 hi2 => hwstk_out idx (by omega)
          · have hszl : 0 < fullWatchSizeCore s.core l := by omega
            have hd := hwat.layout.disjoint l' l hl' hl hll (by omega) hszl
            exact (hwat.slices l' hl').mono (k := s.core) (k' := s'.core) hrefl (Nat.le_refl _)
              (fun _ hr => hr) fun idx hi1 hi2 =>
                hwstk_out idx (by rcases hd with hlt | hgt <;> omega)
  exact ⟨⟨{ hcl with lit_mark_len := hlm_len, wvec_len := by simp [s', hwvl],
                      wstk_len_arr := hwstk_len },
           { hsl with work_stk1_len := hws1_len, work_stk2_len := hws2_len }⟩,
    { hsp.2.1 with
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hwat' },
    ⟨hsp.2.2.1.1, hlm_zero⟩,
    arenaVarsNodup_of_arena_eq rfl rfl hsp.2.2.2.1,
    hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem watchSliceOk_congr_core {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hcv : k'.cur_vars = k.cur_vars) (hw : k'.wstk = k.wstk)
    (hal : k'.arena_len = k.arena_len) (ha : k'.arena = k.arena) :
    ∀ {lit p rem}, WatchSliceOk F_cur k lit p rem → WatchSliceOk F_cur k' lit p rem := by
  intro lit p rem h
  induction h with
  | empty => exact .empty
  | bin h0 h1 h2 h3 h4 _ ih => exact .bin (hw ▸ h0) h1 h2 (hcv ▸ h3) h4 ih
  | large h0 h1 h2 h3 h4 _ ih =>
    exact .large (hw ▸ h0) (hw ▸ h1) h2 h3
      (by unfold fullArenaClauseRefsCore; rw [hal, ha]; exact h4) ih

theorem denseWatchSliceOk_congr_core {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hcv : k'.cur_vars = k.cur_vars) (hw : k'.wstk = k.wstk)
    (hal : k'.arena_len = k.arena_len) (ha : k'.arena = k.arena) :
    ∀ {lit p rem},
      DenseWatchSliceOk F_cur k lit p rem → DenseWatchSliceOk F_cur k' lit p rem := by
  intro lit p rem h
  induction h with
  | empty => exact .empty
  | bin h0 h1 h2 h3 h4 _ ih => exact .bin (hw ▸ h0) h1 h2 (hcv ▸ h3) h4 ih
  | occ h0 h1 h2 h3 h4 h5 _ ih =>
    exact .occ (hw ▸ h0) (hw ▸ h1) h2 h3 h4
      (by unfold fullArenaClauseRefsCore; rw [hal, ha]; exact h5) ih

theorem fullWitnessInv_of_fields {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (fl' rp' : List (BitVec 32)) (unass' unfl' : BitVec 64) :
    FullWitnessInv c F0 F_cur
      { k with flags := fl', repr := rp', unassigned := unass', unflushed := unfl' } := by
  let k' : FullCoreState :=
    { k with flags := fl', repr := rp', unassigned := unass', unflushed := unfl' }
  have har : FullArenaClausesInv c F_cur k' :=
    ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt, hw.arena.entails⟩
  have hwt : ModeWatchesInv F_cur k' := by
    by_cases hdm : k.dense_mode = 0#64
    · have hdm' : k'.dense_mode = 0#64 := hdm
      have hw0 := hw.watches; unfold ModeWatchesInv at hw0 ⊢
      simp only [hdm, ↓reduceIte] at hw0; simp only [hdm', ↓reduceIte]
      exact ⟨⟨hw0.layout.bounds, hw0.layout.pos_off, hw0.layout.disjoint, hw0.layout.no_sentinel⟩,
        fun l hl => watchSliceOk_congr_core (k := k) (k' := k')
          rfl rfl rfl rfl (hw0.slices l hl)⟩
    · have hdm' : k'.dense_mode ≠ 0#64 := hdm
      have hw0 := hw.watches; unfold ModeWatchesInv at hw0 ⊢
      simp only [hdm, ↓reduceIte] at hw0; simp only [hdm', ↓reduceIte]
      exact ⟨⟨hw0.layout.bounds, hw0.layout.pos_off, hw0.layout.disjoint, hw0.layout.no_sentinel⟩,
        fun l hl => denseWatchSliceOk_congr_core (k := k) (k' := k')
          rfl rfl rfl rfl (hw0.slices l hl)⟩
  exact ⟨hw.ext_sound, hw.inconsistent_sound, har, hwt, hw.cur_level_le, hw.trail_lits_lt,
    hw.trail_vars_nodup, hw.vals_domain, hw.vals_true_iff, hw.vals_false_iff, hw.lvl_le,
    hw.dec_earliest, hw.levels_inhabited, hw.level0_sound, hw.trail_pos_inv,
    hw.level0_rsn_none, hw.frame_trail_lt, hw.frame_trail_mono, hw.frame_trail_before_lt,
    hw.frame_dec_lt, hw.reason_inv, hw.reason_lit_mem⟩

theorem fullSparseInvW_of_bcp {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch} :
    let s' : FullState :=
      { core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
          confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    FullArenaPermEq s.core s'.core →
    FullProbeScratchPres { core := s.core, scratch :=
      { s.scratch with
        search_ticks := sc'.search_ticks, phases := sc'.phases,
        wsort := sc'.wsort, delayed := sc'.delayed } } s' →
    FullSparseInvW c F0 F_cur s' := by
  intro s' hlen' hw' hperm hsc
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hperm.2.1
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    obtain ⟨_, hgb, hpm⟩ := hperm.2.2 r hr
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgb] at hng
    exact (hsp.2.2.2.1 r hr hng).perm (hpm.map (· / 2)).symm
  have hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s' := fun r hr => by
    change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  have hext : FullExtScratchOk c s' := hsp.2.2.2.2.1.of_pres hsc.1 hrefs
  exact ⟨hlen', hw', hsp.2.2.1, hnd', hext, hsp.2.2.2.2.2⟩

theorem fullSparseInvW_afterExtPush2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hsok : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len ≤ c.extend_cap) :
    FullSparseInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [heq]
  exact ⟨hsok, heq ▸ hsp.2.1,
    ⟨fun v hv => by rw [heq]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [heq]; exact hsp.2.2.1.2 l hl⟩,
    arenaVarsNodup_of_arena_eq (by rw [heq]) (by rw [heq]) hsp.2.2.2.1,
    ⟨fun i hi => by dsimp only; rw [hll, hrefs]; exact hsp.2.2.2.2.1.1 i hi, hext⟩,
    by rw [heq]; exact hsp.2.2.2.2.2⟩

theorem fullSparseInvW_setInact {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {flags' : List (BitVec 32)} {unass' : BitVec 64} {sc' : FullScratch} :
    let s' : FullState := { core := { s.core with flags := flags', unassigned := unass' }
                            scratch := sc' }
    s'.LengthsOk c → FullProbeScratchPres s s' → FullSparseInvW c F0 F_cur s' := by
  intro s' hlen' hpr
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => hsp.2.2.2.1 r hr hng
  have hw' := fullWitnessInv_of_fields hsp.2.1 flags' s.core.repr unass' s.core.unflushed
  have hext' : FullExtScratchOk c s' := hsp.2.2.2.2.1.of_pres hpr.1 (fun _ hr => hr)
  exact ⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩

theorem fullReprEquiv_reset_pair {F_cur : List (List Nat)} {s : FullState}
    (hr : FullReprEquiv F_cur s) (hrep_len : 2 * s.core.cur_vars ≤ s.core.repr.length)
    {v : Nat} (hv : v < s.core.cur_vars) (hlim : 2 * s.core.cur_vars < 2 ^ 32) :
    let r' := (s.core.repr.set (2 * v) (BitVec.ofNat 32 (2 * v))).set
      (2 * v + 1) (BitVec.ofNat 32 (2 * v + 1))
    FullReprEquiv F_cur { s with core := { s.core with repr := r' } } := by
  intro r' l hl
  have hlt1 : 2 * v < s.core.repr.length := by omega
  have hlt2 : 2 * v + 1 < (s.core.repr.set (2 * v) (BitVec.ofNat 32 (2 * v))).length := by
    rw [List.length_set]; omega
  have hxv0 : (2 * v) ^^^ 1 = 2 * v + 1 := nat_two_mul_xor_one v
  have hxv1 : (2 * v + 1) ^^^ 1 = 2 * v := by rw [← hxv0, Nat.xor_assoc]; simp
  dsimp only
  by_cases h1 : l = 2 * v + 1
  · subst h1
    have hget : r'[2 * v + 1]?.getD 0#32 = BitVec.ofNat 32 (2 * v + 1) := by
      dsimp only [r']; rw [List.getElem?_set_self hlt2, Option.getD_some]
    have hto : (BitVec.ofNat 32 (2 * v + 1)).toNat = 2 * v + 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
    rw [hget, hto]
    refine ⟨hl, ?_, ?_⟩
    · simpa [hxv0, hxv1] using (entails_taut (f := cnfOfClauses F_cur) (l := 2 * v + 1))
    · simpa [hxv0, hxv1] using (entails_taut (f := cnfOfClauses F_cur) (l := 2 * v))
  · by_cases h0 : l = 2 * v
    · subst h0
      have hget : r'[2 * v]?.getD 0#32 = BitVec.ofNat 32 (2 * v) := by
        dsimp only [r']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hlt1, Option.getD_some]
      have hto : (BitVec.ofNat 32 (2 * v)).toNat = 2 * v := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
      rw [hget, hto]
      refine ⟨hl, ?_, ?_⟩
      · simpa [hxv0, hxv1] using (entails_taut (f := cnfOfClauses F_cur) (l := 2 * v))
      · simpa [hxv0, hxv1] using (entails_taut (f := cnfOfClauses F_cur) (l := 2 * v + 1))
    · have hget : r'[l]? = s.core.repr[l]? := by
        dsimp only [r']; rw [List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h0)]
      rw [hget]; exact hr l hl

theorem fullSparseInvW_repr_set2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hrep_len : 2 * c.max_vars = s.core.repr.length) {v : Nat} (_hv : v < s.core.cur_vars) :
    let r' := (s.core.repr.set (2 * v) (BitVec.ofNat 32 (2 * v))).set
      (2 * v + 1) (BitVec.ofNat 32 (2 * v + 1))
    FullSparseInvW c F0 F_cur { s with core := { s.core with repr := r' } } := by
  intro r'
  have hlen : ({ s with core := { s.core with repr := r' } } : FullState).LengthsOk c :=
    ⟨{ hsp.1.core_ok with repr_len := by dsimp only [r']; simp [← hrep_len] }, hsp.1.scratch_ok⟩
  have hw := fullWitnessInv_of_fields hsp.2.1 s.core.flags r' s.core.unassigned s.core.unflushed
  have hnd : FullArenaVarsNodup { s with core := { s.core with repr := r' } } :=
    fun r hr hng => hsp.2.2.2.1 r hr hng
  exact ⟨hlen, hw, hsp.2.2.1, hnd,
    ⟨fun i hi => hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩

theorem fullSparseInvW_afterAddUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss'}
    (hsok : ({ s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', target_assigned := ta',
                                    best_assigned := ba', phases_target := pt',
                                    phases_best := pb', heap := hp', pos := ps',
                                    heap_len := hl', q_search_idx := qsi',
                                    q_search_stamp := qss' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', cur_level := cl', unassigned := unass',
                    unflushed := unfl', inconsistent := inc' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', target_assigned := ta',
                                    best_assigned := ba', phases_target := pt',
                                    phases_best := pb', heap := hp', pos := ps',
                                    heap_len := hl', q_search_idx := qsi',
                                    q_search_stamp := qss' } } :=
  ⟨hsok, hw', hsp.2.2.1, arenaVarsNodup_of_arena_eq rfl rfl hsp.2.2.2.1,
    ⟨fun i hi => hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩

theorem fullSparseInvW_afterAddBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort'}
    (hsok : ({ s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                              oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } } :
          FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    unassigned := unass', unflushed := unfl', wvec := wvec',
                    wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                    oom := oom', inconsistent := inc' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                              oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } } :=
  ⟨hsok, hw', hsp.2.2.1, arenaVarsNodup_of_arena_eq rfl rfl hsp.2.2.2.1,
    ⟨fun i hi => hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩

theorem fullSparseInvW_after_bt0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hpres : FullExtScratchPres s s') (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm : s'.core.dense_mode = s.core.dense_mode) :
    FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
      change r ∈ fullArenaClauseRefsCore s'.core at hr
      unfold fullArenaClauseRefsCore at hr ⊢; rw [har, hal] at hr; exact hr
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
      rwa [har] at hng
    have hl : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hl]; exact hsp.2.2.2.1 r hr0 hng0
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

theorem fullSparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by rw [← hperm.2.1]; exact hr
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 r hr0
    exact (hsp.2.2.2.1 r hr0 (hgb.symm.trans hng)).perm (hp.symm.map (· / 2))
  · exact hsp.2.2.2.2.1.of_pres hpres fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr

theorem fullSparseInvW_after_sweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hnd' : FullArenaVarsNodup s') (hll' : FullLastLearnedWf s')
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) : FullSparseInvW c F0 F_cur s' :=
  ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩,
    hnd', ⟨hll', hext' ▸ hsp.2.2.2.2.1.2⟩, hdm.trans hsp.2.2.2.2.2⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
