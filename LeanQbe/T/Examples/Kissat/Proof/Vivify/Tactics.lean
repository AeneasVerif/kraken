/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public meta import LeanQbe.T.Logic.C0Step
public meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Scoped Stepping Tactics & Pure BV/List Helpers (`Proof.Vivify.Tactics`)

Provides shared `VivTactics` macros, `[c0_load]`/`[c0_store]` constant-offset scratch accessors,
bitvector bitmask/shift lemmas, and list permutation/equality utilities used across `Vivify`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

public section

namespace VivTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "viv_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "viv_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "viv_step" : tactic =>
  `(tactic| ((try viv_unmdata); (repeat viv_strip); c0_step))
scoped macro "viv_steps" : tactic =>
  `(tactic| (
      (try viv_unmdata)
      (repeat viv_strip)
      c0_steps
      repeat (any_goals (viv_strip; repeat viv_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "viv_to_group" : tactic => do
  evalTactic (← `(tactic| ((try viv_unmdata); (repeat viv_strip))))
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1)
        out := out ++ (← getUnsolvedGoals)
      else
        out := out.push g
    setGoals out.toList
  go 500

scoped elab "viv_hsteps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps {} 10000

scoped elab "viv_hsteps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false } 10000

scoped elab "viv_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

scoped elab "viv_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

scoped macro "viv_hsplit" : tactic => `(tactic| c0_hsplit)

scoped macro "viv_call " h:term : tactic => `(tactic| c0_call $h)

@[scoped c0_load] theorem c0_load_ws1_z {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk1 + 0#64) = some s.scratch.work_stk1[0] :=
  FullArenaTactics.load_full_work_stk1 hi hm

@[scoped c0_load] theorem c0_load_ws1_b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using FullArenaTactics.load_full_work_stk1 hi hm

@[scoped c0_store] theorem c0_store_ws1_z {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk1 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk1 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm

@[scoped c0_store] theorem c0_store_ws1_b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk1 v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm

@[scoped c0_load] theorem c0_load_ws2_z {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk2 + 0#64) = some s.scratch.work_stk2[0] :=
  FullArenaTactics.load_full_work_stk2 hi hm

@[scoped c0_load] theorem c0_load_ws2_b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk2 = some s.scratch.work_stk2[0] := by
  simpa using FullArenaTactics.load_full_work_stk2 hi hm

@[scoped c0_load] theorem c0_load_ws2_4 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk2 + 4#64) = some s.scratch.work_stk2[1] :=
  FullArenaTactics.load_full_work_stk2 hi hm

@[scoped c0_store] theorem c0_store_ws2_z {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk2 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk2 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

@[scoped c0_store] theorem c0_store_ws2_b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk2 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk2 v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

@[scoped c0_store] theorem c0_store_ws2_4 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 1 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk2 + 4#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 1 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk2 + 4#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk2 (i := 1) v hi hm

@[scoped c0_load] theorem c0_load_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 0#64) = some s.core.tmp[0] :=
  FullArenaTactics.load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem c0_store_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
    (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
      (storeMem m i32 (c.pTmp + 0#64) v) :=
  FullArenaTactics.store_full_tmp (i := 0) v hi hm

end VivTactics

/-! ## Pure BitVector, List & `M6HdrExt` Helpers -/

abbrev fvOp {as bs : List Ty} (c : OpCode as bs) (args : Tup (Arg Val) as)
    {ret : List Ty} (k : Tup Val bs → Expr Val Cont ret) : Expr Val Cont ret :=
  Expr.let_ ⟨c, args⟩ k

theorem bv8_sext32_eq0_iff : ∀ x : BitVec 8, x.signExtend 32 = 0#32 ↔ x = 0#8 := by decide

theorem bv8_zext32_eq0_iff : ∀ x : BitVec 8, x.setWidth 32 = 0#32 ↔ x = 0#8 := by decide

theorem bv8_dom_sgt0_iff {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).slt (x.signExtend 32) = true ↔ x = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bv8_dom_slt0_iff {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bv32_lshr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]

theorem bv32_xor1_xor1 (x : BitVec 32) : (x ^^^ 1#32) ^^^ 1#32 = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem bv64_trunc32_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x.truncate 32).toNat = x.toNat := by
  change (x.setWidth 32).toNat = x.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

private theorem mask19_bit : ∀ i : Fin 32, (0x00080000#32)[i.val] = decide (i.val = 19) := by
  decide
private theorem mask20_bit : ∀ i : Fin 32, (0x00100000#32)[i.val] = decide (i.val = 20) := by
  decide
private theorem mask22_bit : ∀ i : Fin 32, (0x00400000#32)[i.val] = decide (i.val = 22) := by
  decide
private theorem mask23_bit : ∀ i : Fin 32, (0x00800000#32)[i.val] = decide (i.val = 23) := by
  decide
private theorem maskN20_bit : ∀ i : Fin 32, (0xFFEFFFFF#32)[i.val] = decide (i.val ≠ 20) := by
  decide
private theorem maskN22_bit : ∀ i : Fin 32, (0xFFBFFFFF#32)[i.val] = decide (i.val ≠ 22) := by
  decide
private theorem mask31_bit : ∀ i : Fin 32, (0x80000000#32)[i.val] = decide (i.val = 31) := by
  decide
private theorem maskLo31_bit : ∀ i : Fin 32, (0x7FFFFFFF#32)[i.val] = decide (i.val < 31) := by
  decide

theorem bv32_or_viv_garb (h : BitVec 32) :
    ((h ||| 0x00100000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or, mask19_bit ⟨i, hi⟩,
    mask20_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_or_viv_shrk (h : BitVec 32) :
    ((h ||| 0x00100000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or, mask23_bit ⟨i, hi⟩,
    mask20_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_clr_viv_garb (h : BitVec 32) :
    ((h &&& ~~~0x00100000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  rw [show (~~~0x00100000#32 : BitVec 32) = 0xFFEFFFFF#32 from rfl]
  ext i hi; simp only [BitVec.getElem_and, mask19_bit ⟨i, hi⟩, maskN20_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_clr_viv_shrk (h : BitVec 32) :
    ((h &&& ~~~0x00100000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  rw [show (~~~0x00100000#32 : BitVec 32) = 0xFFEFFFFF#32 from rfl]
  ext i hi; simp only [BitVec.getElem_and, mask23_bit ⟨i, hi⟩, maskN20_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_clr_red_garb (h : BitVec 32) :
    ((h &&& ~~~0x00400000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  rw [show (~~~0x00400000#32 : BitVec 32) = 0xFFBFFFFF#32 from rfl]
  ext i hi; simp only [BitVec.getElem_and, mask19_bit ⟨i, hi⟩, maskN22_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_clr_red_shrk (h : BitVec 32) :
    ((h &&& ~~~0x00400000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  rw [show (~~~0x00400000#32 : BitVec 32) = 0xFFBFFFFF#32 from rfl]
  ext i hi; simp only [BitVec.getElem_and, mask23_bit ⟨i, hi⟩, maskN22_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_or_shrk_garb (h : BitVec 32) :
    ((h ||| 0x00800000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or, mask19_bit ⟨i, hi⟩,
    mask23_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_or_garb_shrk (h : BitVec 32) :
    ((h ||| 0x00080000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or, mask19_bit ⟨i, hi⟩,
    mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_or_shrk_ne0 (h : BitVec 32) :
    ((h ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := by
  intro heq; have h23 := congrArg (·[23]) heq
  revert h23; simp [show (0x00800000#32)[23] = true from rfl]

theorem bv32_mask_lo31_props (x : BitVec 32) :
    ((x &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧ (x &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  constructor
  · ext i hi; simp only [BitVec.getElem_and, mask31_bit ⟨i, hi⟩, maskLo31_bit ⟨i, hi⟩,
      BitVec.getElem_zero hi]
    by_cases h31 : i = 31 <;> simp [h31]
  · intro heq; have h31 := congrArg (·[31]) heq
    revert h31; simp [show (0x7FFFFFFF#32)[31] = false from rfl,
      show (0xFFFFFFFF#32)[31] = true from rfl]

theorem bv32_ne_sentinel_of_lt {x : BitVec 32} (hlt : x.toNat < 0x80000000) :
    x ≠ 0xFFFFFFFF#32 := by
  intro heq; subst heq; revert hlt; decide

private theorem viv_perm_middle {α : Type} (x : α) (l₁ l₂ : List α) :
    (l₁ ++ x :: l₂).Perm (x :: (l₁ ++ l₂)) := by
  induction l₁ with
  | nil => exact .refl _
  | cons b bs ih =>
    simpa [List.cons_append] using (List.Perm.cons b ih).trans (List.Perm.swap x b _)

theorem viv_list_swap_perm_lt {α : Type} (xs : List α) {i j : Nat}
    (hij : i < j) (hj : j < xs.length) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'(by omega))).Perm xs := by
  have hi : i < xs.length := by omega
  have heq : xs = xs.take i ++ xs[i] ::
      ((xs.drop (i + 1)).take (j - i - 1) ++ xs[j] :: xs.drop (j + 1)) := by
    have hs1 := List.take_append_drop i xs
    have hd1 : xs.drop i = xs[i] :: xs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hs2 := List.take_append_drop (j - i - 1) (xs.drop (i + 1))
    have hd2 : (xs.drop (i + 1)).drop (j - i - 1) = xs[j] :: xs.drop (j + 1) := by
      rw [List.drop_drop, show i + 1 + (j - i - 1) = j by omega]
      exact List.drop_eq_getElem_cons hj
    rw [← hs2, hd2] at hd1
    conv => lhs; rw [← hs1, hd1]
  have hsw : ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)) =
      xs.take i ++ xs[j] ::
        ((xs.drop (i + 1)).take (j - i - 1) ++ xs[i] :: xs.drop (j + 1)) := by
    apply List.ext_getElem (by simp; omega)
    intro k hk1 _
    have hmid_len : ((xs.drop (i + 1)).take (j - i - 1)).length = j - i - 1 := by simp; omega
    have hti_len : (xs.take i).length = i := by simp; omega
    by_cases hki : k < i
    · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega),
        List.getElem_append_left (by omega), List.getElem_take]
    · have hti_le : (xs.take i).length ≤ k := by rw [hti_len]; omega
      by_cases hkei : k = i
      · subst hkei
        rw [List.getElem_set_ne (by omega), List.getElem_set_self]
        simp only [List.getElem_append_right hti_le, hti_len, Nat.sub_self, List.getElem_cons_zero]
      · simp only [List.getElem_append_right hti_le, hti_len]
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : k - i ≠ 0) with ⟨d0, hd0⟩
        simp only [hd0, List.getElem_cons_succ]
        by_cases hkj : k = j
        · subst k; rw [List.getElem_set_self]
          have hmid_le : ((xs.drop (i + 1)).take (j - i - 1)).length ≤ d0 := by
            rw [hmid_len]; omega
          simp only [List.getElem_append_right hmid_le, hmid_len,
            show d0 - (j - i - 1) = 0 by omega, List.getElem_cons_zero]
        · rw [List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hkei)]
          by_cases hk_lt_j : k < j
          · have hmid_lt : d0 < ((xs.drop (i + 1)).take (j - i - 1)).length := by
              rw [hmid_len]; omega
            simp only [List.getElem_append_left hmid_lt, List.getElem_take, List.getElem_drop]
            congr 1; omega
          · have hmid_le : ((xs.drop (i + 1)).take (j - i - 1)).length ≤ d0 := by
              rw [hmid_len]; omega
            simp only [List.getElem_append_right hmid_le, hmid_len,
              show d0 - (j - i - 1) = k - j by omega]
            rcases Nat.exists_eq_succ_of_ne_zero (by omega : k - j ≠ 0) with ⟨d, hd⟩
            simp only [hd, List.getElem_cons_succ, List.getElem_drop]
            congr 1; omega
  rw [hsw]; conv => rhs; rw [heq]
  apply List.Perm.append_left
  let mid := (xs.drop (i + 1)).take (j - i - 1)
  have hp1 : (xs[j]'hj :: (mid ++ xs[i]'hi :: xs.drop (j + 1))).Perm
      (xs[j]'hj :: xs[i]'hi :: (mid ++ xs.drop (j + 1))) :=
    List.Perm.cons _ (viv_perm_middle (xs[i]'hi) mid (xs.drop (j + 1)))
  have hp2 : (xs[j]'hj :: xs[i]'hi :: (mid ++ xs.drop (j + 1))).Perm
      (xs[i]'hi :: xs[j]'hj :: (mid ++ xs.drop (j + 1))) :=
    List.Perm.swap _ _ _
  have hp3 : (xs[i]'hi :: xs[j]'hj :: (mid ++ xs.drop (j + 1))).Perm
      (xs[i]'hi :: (mid ++ xs[j]'hj :: xs.drop (j + 1))) :=
    List.Perm.cons _ (viv_perm_middle (xs[j]'hj) mid (xs.drop (j + 1))).symm
  exact hp1.trans (hp2.trans hp3)

theorem viv_list_swap_perm {α : Type} (xs : List α) {a b : Nat}
    (ha : a < xs.length) (hb : b < xs.length) :
    ((xs.set a (xs[b]'hb)).set b (xs[a]'ha)).Perm xs := by
  by_cases hab : a = b
  · subst hab
    have hid : (xs.set a (xs[a]'ha)).set a (xs[a]'ha) = xs := by
      refine List.ext_getElem? fun i => ?_
      by_cases hi : i = a
      · subst hi; rw [List.getElem?_set_self (by simp; omega), List.getElem?_eq_getElem ha]
      · rw [List.getElem?_set_ne (Ne.symm hi), List.getElem?_set_ne (Ne.symm hi)]
    rw [hid]
  · rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
    · exact viv_list_swap_perm_lt xs hlt hb
    · have hcm : (xs.set a (xs[b]'hb)).set b (xs[a]'ha) =
          (xs.set b (xs[a]'ha)).set a (xs[b]'hb) := by
        refine List.ext_getElem? fun i => ?_
        by_cases hia : i = a
        · subst hia; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self ha,
            List.getElem?_set_self (by simp; omega)]
        · by_cases hib : i = b
          · subst hib; rw [List.getElem?_set_self (by simp; omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_self hb]
          · rw [List.getElem?_set_ne (Ne.symm hib), List.getElem?_set_ne (Ne.symm hia),
              List.getElem?_set_ne (Ne.symm hia), List.getElem?_set_ne (Ne.symm hib)]
      rw [hcm]
      exact viv_list_swap_perm_lt xs hgt ha

theorem bv32_and_not_red_garb (x : BitVec 32) :
    ((x &&& ~~~0x00400000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00400000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]

theorem bv32_and_not_red_shrk (x : BitVec 32) :
    ((x &&& ~~~0x00400000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00400000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl]

theorem bv32_set_glue_garb (x g : BitVec 32) (hg : (g &&& 0x00080000#32) = 0#32) :
    (((x &&& ~~~0x7FFFF#32) ||| g) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right, hg, BitVec.or_zero, BitVec.and_assoc,
    show (~~~0x7FFFF#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]

theorem bv32_set_glue_shrk (x g : BitVec 32) (hg : (g &&& 0x00800000#32) = 0#32) :
    (((x &&& ~~~0x7FFFF#32) ||| g) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right, hg, BitVec.or_zero, BitVec.and_assoc,
    show (~~~0x7FFFF#32 &&& 0x00800000#32) = 0x00800000#32 from rfl]

theorem bv32_glue_mask_garb (y : BitVec 32) :
    ((y &&& 0x7FFFF#32) &&& 0x00080000#32) = 0#32 := by
  rw [BitVec.and_assoc, show (0x7FFFF#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.and_zero]

theorem bv32_glue_mask_shrk (y : BitVec 32) :
    ((y &&& 0x7FFFF#32) &&& 0x00800000#32) = 0#32 := by
  rw [BitVec.and_assoc, show (0x7FFFF#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.and_zero]

theorem viv_bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem viv_bv32_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  rw [viv_bv32_xor1_toNat]; exact litNeg_lt_two_mul hx

theorem viv_bv32_xor1_div2 (x : BitVec 32) : (x ^^^ 1#32).toNat / 2 = x.toNat / 2 := by
  rw [viv_bv32_xor1_toNat]; exact litVar_litNeg x.toNat

theorem viv_list_eq_of_getElem?_eq {α : Type} {l1 l2 : List α} (hl : l1.length = l2.length)
    (he : ∀ i < l1.length, l1[i]? = l2[i]?) : l1 = l2 := by
  refine List.ext_getElem hl fun i hi1 hi2 => ?_
  have h := he i hi1
  rwa [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, Option.some.injEq] at h

theorem viv_take_snoc {α : Type} {xs : List α} {n : Nat} (hn : 0 < n) (hle : n ≤ xs.length) :
    xs.take n = xs.take (n - 1) ++ [xs[n - 1]'(by omega)] := by
  refine List.ext_getElem? fun k => ?_
  by_cases hk1 : k < n - 1
  · rw [List.getElem?_take, ite_eq_left (by omega),
      List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take,
      ite_eq_left hk1]
  · by_cases hk2 : k = n - 1
    · subst hk2
      rw [List.getElem?_take, ite_eq_left (by omega),
        List.getElem?_append_right (by rw [List.length_take]; omega)]
      have hlen : (xs.take (n - 1)).length = n - 1 := by rw [List.length_take]; omega
      rw [hlen, Nat.sub_self, List.getElem?_cons_zero, List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_take, ite_eq_right (by omega),
        List.getElem?_append_right (by rw [List.length_take]; omega)]
      have hlen : (xs.take (n - 1)).length = n - 1 := by rw [List.length_take]; omega
      rw [hlen, show k - (n - 1) = (k - n) + 1 by omega, List.getElem?_cons_succ, List.getElem?_nil]

theorem viv_entails_of_perm {F : CNF Nat} {xs ys : List Nat}
    (hp : xs.Perm ys) (h : F.EntailsClause (cnfClause ys)) :
    F.EntailsClause (cnfClause xs) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hsat
  rw [clause_sat_cnfClause_iff]
  obtain ⟨l, hl, hls⟩ := (clause_sat_cnfClause_iff α ys).mp (h α hsat)
  exact ⟨l, hp.mem_iff.mpr hl, hls⟩

theorem viv_take_eq_of_copy {ws2 tmp : List (BitVec 32)} {n : Nat}
    (hcp : ∀ j < n, ws2[j]? = tmp[j]?) : ws2.take n = tmp.take n := by
  refine List.ext_getElem? fun j => ?_
  by_cases hj : j < n
  · rw [List.getElem?_take, ite_eq_left hj, List.getElem?_take, ite_eq_left hj]; exact hcp j hj
  · rw [List.getElem?_take, ite_eq_right hj, List.getElem?_take, ite_eq_right hj]

theorem viv_nodup_prefix_of_perm {xs : List (BitVec 32)} {lits : List Nat} {sz : Nat}
    (hsz : 1 ≤ sz) (hperm : ((xs.take sz).map BitVec.toNat).Perm lits)
    (hnd : (lits.map (· / 2)).Nodup) :
    ((xs.take (sz - 1)).map fun x => x.toNat / 2).Nodup := by
  have hnd_sz : (((xs.take sz).map BitVec.toNat).map (· / 2)).Nodup :=
    (hperm.map (· / 2)).nodup_iff.mpr hnd
  rw [List.map_map] at hnd_sz
  have htake : xs.take (sz - 1) = (xs.take sz).take (sz - 1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [htake, List.map_take]
  exact hnd_sz.sublist (List.take_sublist _ _)

theorem viv_ext_pres_trans {ext0 ext1 ext2 : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (h2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    M6HdrExtInitOk ext0 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext0 ext2 := fun hi =>
  ⟨(h2 (h1 hi).1).1, (h1 hi).2.trans (h2 (h1 hi).1).2⟩

theorem viv_ext_pres_refl (ext : List (BitVec 64)) :
    M6HdrExtInitOk ext → M6HdrExtInitOk ext ∧ M6ExtW2bPres ext ext := fun hi =>
  ⟨hi, M6ExtW2bPres.refl ext⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
