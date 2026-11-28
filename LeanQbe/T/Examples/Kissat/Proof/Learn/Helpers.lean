/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public meta import Lean.Elab.Tactic
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Shared Tactics, BitVec & Witness Preservation Helpers (`Proof.Learn.Helpers`)

Self-contained helpers for `LeanQbe.T.Examples.Kissat.Proof.Learn` built exclusively on
`Proof.Spec.*` (`0` legacy `Full*` imports, `0` `import all`, `0` `@[expose]` on theorems).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Scoped `bv_c0`, Arena Load/Store Wrappers & Group/Split Tactics -/

attribute [scoped bv_c0] List.length_set

@[scoped bv_c0] theorem bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

@[scoped bv_c0] theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[scoped bv_c0] theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl
@[scoped bv_c0] theorem bv64_seven_toNat : (7 : BitVec 64).toNat = 7 := rfl
@[scoped bv_c0] theorem bv64_eight_toNat : (8 : BitVec 64).toNat = 8 := rfl

section ArenaLoadStore
open scoped FullArenaTactics

@[scoped c0_load] theorem load_full_tmp0_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 0#64) = some s.core.tmp[0] := by
  simpa using FullArenaTactics.load_full_tmp (i := 0) hi hm

@[scoped c0_load] theorem load_full_tmp0_base {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using FullArenaTactics.load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_full_tmp0_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

@[scoped c0_store] theorem store_full_tmp0_base {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

@[scoped c0_load] theorem load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 4#64) = some s.core.tmp[1] := by
  simpa using FullArenaTactics.load_full_tmp (i := 1) hi hm

@[scoped c0_store] theorem store_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 1) v hi hm

@[scoped c0_load] theorem load_full_ll0_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.last_learned.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pLastLearned + 0#64) = some s.scratch.last_learned[0] := by
  simpa using FullArenaTactics.load_full_last_learned (i := 0) hi hm

@[scoped c0_load] theorem load_full_ll0_base {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.last_learned.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pLastLearned = some s.scratch.last_learned[0] := by
  simpa using FullArenaTactics.load_full_last_learned (i := 0) hi hm

@[scoped c0_store] theorem store_full_ll0_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.last_learned.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pLastLearned + 0#64) ∧
      (FullMem c { s with scratch :=
        { s.scratch with last_learned := s.scratch.last_learned.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pLastLearned + 0#64) v) := by
  simpa using FullArenaTactics.store_full_last_learned (i := 0) v hi hm

@[scoped c0_store] theorem store_full_ll0_base {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.last_learned.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pLastLearned ∧
      (FullMem c { s with scratch :=
        { s.scratch with last_learned := s.scratch.last_learned.set 0 v } } ⋆ R)
        (storeMem m i32 c.pLastLearned v) := by
  simpa using FullArenaTactics.store_full_last_learned (i := 0) v hi hm

end ArenaLoadStore

open Lean Elab Tactic in
/-- Strip outer `Expr.mdata` wrappers from all unsolved goals so `c0_step` inspects heads. -/
scoped elab "c0_clean" : tactic => do
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    let ty ← Lean.instantiateMVars (← g.getType)
    if ty.isMData then
      out := out.push (← g.change ty.consumeMData (checkDefEq := false))
    else out := out.push g
  setGoals out.toList

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
scoped elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

/-! ## 2. Pure BitVec & List Helpers -/

theorem bv64_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n :=
  Proof.Spec.bv64_ofNat_toNat hn

theorem i8_sext32_eq0 (v : BitVec 8) : v.signExtend 32 = 0#32 ↔ v = 0#8 := by
  revert v; decide

theorem i8_eq1_slt0_sext32 : BitVec.slt 0#32 ((1#8 : BitVec 8).signExtend 32) := by
  decide

private theorem mask31_bit : ∀ i : Fin 32, (0x80000000#32)[i.val] = decide (i.val = 31) := by
  decide

private theorem maskLo31_bit : ∀ i : Fin 32, (0x7FFFFFFF#32)[i.val] = decide (i.val < 31) := by
  decide

theorem bin_rsn_mask_props {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    let rsn : BitVec 32 := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) ≠ 0#32 ∧
      (rsn &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  intro rsn
  have hbit31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by omega : l.toNat < 2 ^ 31)]; rfl
  have hand_hi : (rsn &&& 0x80000000#32) = 0x80000000#32 := by
    ext i hi
    simp only [rsn, BitVec.getElem_and, BitVec.getElem_or, mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31 <;> simp [h31]
  have hand_lo : (rsn &&& 0x7FFFFFFF#32) = l := by
    ext i hi
    simp only [rsn, BitVec.getElem_and, BitVec.getElem_or,
      mask31_bit ⟨i, hi⟩, maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hbit31]
    · simp [h31, show i < 31 by omega]
  refine ⟨?_, ?_, congrArg BitVec.toNat hand_lo⟩
  · intro heq
    have := congrArg (fun x => x &&& 0x7FFFFFFF#32) heq
    rw [hand_lo] at this
    have hnat := congrArg BitVec.toNat this
    have hff : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := rfl
    rw [hff] at hnat; omega
  · rw [hand_hi]; decide

theorem bv32_lit_lo31_props {l : BitVec 32} (hl : l.toNat < 2 ^ 31) :
    (l &&& 0x7FFFFFFF#32) = l ∧ ((l &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
      (l &&& 0x80000000#32) = 0#32 := by
  have hb31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt hl]; rfl
  have hlo : (l &&& 0x7FFFFFFF#32) = l := by
    ext i hi; simp only [BitVec.getElem_and, maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hb31]
    · simp [show i < 31 by omega]
  have hhi : (l &&& 0x80000000#32) = 0#32 := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero, mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hb31]
    · simp [h31]
  exact ⟨hlo, by rw [hlo]; exact hhi, hhi⟩

theorem bv32_lit_neq_ff {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    l ≠ 0xFFFFFFFF#32 := by
  intro heq; have h := congrArg BitVec.toNat heq
  have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl
  rw [hff] at h; omega

theorem ofNat64_pos {n : Nat} (h : ¬ BitVec.ofNat 64 n = 0#64) : 0 < n :=
  Nat.pos_of_ne_zero fun h0 => h (by simp [h0])

theorem ofNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) (h : BitVec.ofNat 64 n = 0#64) : n = 0 := by
  have := congrArg BitVec.toNat h
  rw [Proof.Spec.bv64_ofNat_toNat hn] at this; exact this

theorem getElem_eq_of_idx {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (heq : i = j) :
    xs[i]'hi = xs[j]'hj := by
  subst heq; rfl

theorem nodup_map_getElem_inj {α β : Type} (f : α → β) :
    ∀ {xs : List α} {j1 j2 : Nat} (h1 : j1 < xs.length) (h2 : j2 < xs.length),
      (xs.map f).Nodup → f (xs[j1]'h1) = f (xs[j2]'h2) → j1 = j2
  | [], _, _, h1, _, _, _ => by simp at h1
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | _ :: xs, 0, j2 + 1, _, h2, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact absurd (List.mem_map.mpr ⟨xs[j2]'(by simpa using h2), List.getElem_mem .., heq.symm⟩)
      hnd.1
  | _ :: xs, j1 + 1, 0, h1, _, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact absurd (List.mem_map.mpr ⟨xs[j1]'(by simpa using h1), List.getElem_mem .., heq⟩) hnd.1
  | _ :: xs, j1 + 1, j2 + 1, h1, h2, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_map_getElem_inj f (by simpa using h1) (by simpa using h2)
      hnd.2 heq)

private theorem count_set_add {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length) (v a : α),
      (xs.set i v).count a + (if xs[i] = a then 1 else 0) = xs.count a + (if v = a then 1 else 0)
  | _ :: _, 0, _, v, a => by simp [List.set, List.count_cons, beq_iff_eq]; omega
  | _ :: xs, i + 1, hi, v, a => by
    have ih := count_set_add xs i (by simp at hi; omega) v a
    simp only [List.set, List.count_cons, List.getElem_cons_succ, beq_iff_eq] at ih ⊢; omega

private theorem take_set_of_lt {α : Type} :
    ∀ (xs : List α) (i n : Nat) (v : α), i < n → (xs.set i v).take n = (xs.take n).set i v
  | [], _, _, _, _ => by simp
  | _ :: _, 0, _ + 1, _, _ => by simp [List.take_succ_cons]
  | _ :: xs, i + 1, n + 1, v, hi => by
    simp [List.set, List.take_succ_cons, take_set_of_lt xs i n v (by omega)]

theorem swap_tmp_perm {α : Type} (tmp : List α) {tl max_idx : Nat}
    (hm1 : 1 ≤ max_idx) (hmlt : max_idx < tl) (hle : tl ≤ tmp.length) :
    let w1 := tmp[1]'(by omega); let wm := tmp[max_idx]'(by omega)
    (((tmp.set 1 wm).set max_idx w1).take tl).Perm (tmp.take tl) := by
  classical
  intro w1 wm; let ys := tmp.take tl
  have hyl : ys.length = tl := by simp [ys, Nat.min_eq_left hle]
  have hys_sw : (((tmp.set 1 wm).set max_idx w1).take tl) = (ys.set 1 wm).set max_idx w1 := by
    dsimp only [ys]; rw [take_set_of_lt _ max_idx tl w1 hmlt, take_set_of_lt tmp 1 tl wm (by omega)]
  have hw1 : ys[1]'(by omega) = w1 := by simp [ys, w1]
  have hwm : ys[max_idx]'(by omega) = wm := by simp [ys, wm]
  rw [hys_sw, List.perm_iff_count]; intro a
  change List.count a ((ys.set 1 wm).set max_idx w1) = List.count a ys
  have h1 := count_set_add ys 1 (by omega) wm a
  have h2 := count_set_add (ys.set 1 wm) max_idx (by simp [hyl]; omega) w1 a
  by_cases hm_eq : max_idx = 1
  · subst hm_eq; have hself : (ys.set 1 wm)[1]'(by simp [hyl]; omega) = wm := by simp
    have heqw : wm = w1 := rfl
    rw [hself] at h2; rw [heqw] at h1 h2 ⊢; rw [hw1] at h1; omega
  · have hne : (ys.set 1 wm)[max_idx]'(by simp [hyl]; omega) = ys[max_idx]'(by omega) :=
      List.getElem_set_ne (by omega : 1 ≠ max_idx) (by simp [hyl]; omega)
    rw [hne, hwm] at h2; rw [hw1] at h1; omega

theorem swap_tmp_props_full {tmp : List (BitVec 32)} {tl max_idx : Nat} {uip : BitVec 32}
    (h2 : 2 ≤ tl) (hle : tl ≤ tmp.length) (hm1 : 1 ≤ max_idx) (hmlt : max_idx < tl)
    (h0 : tmp[0]? = some uip) (hnd : ((tmp.take tl).map fun x => x.toNat / 2).Nodup) :
    let w1 := tmp[1]'(by omega); let wm := tmp[max_idx]'(by omega)
    let tmp_sw := (tmp.set 1 wm).set max_idx w1
    (∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat) ∧
    (∀ l ∈ (tmp_sw.take tl).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l) ∧
    ((tmp_sw.take tl).map fun x => x.toNat / 2).Nodup ∧
    tmp_sw[0]? = some uip ∧ tmp_sw[1]? = some wm := by
  intro w1 wm tmp_sw
  have hperm := swap_tmp_perm tmp hm1 hmlt hle
  have hiff : ∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat :=
    fun l => by
      simp only [List.mem_map]
      exact ⟨fun ⟨x, hx, he⟩ => ⟨x, hperm.mem_iff.mp hx, he⟩,
             fun ⟨x, hx, he⟩ => ⟨x, hperm.mem_iff.mpr hx, he⟩⟩
  have hnd_sw : ((tmp_sw.take tl).map fun x => x.toNat / 2).Nodup := (hperm.map _).nodup_iff.mpr hnd
  have hmem_take : ∀ l ∈ (tmp.take tl).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l := by
    intro l hl; rw [List.mem_map] at hl; rcases hl with ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    have hjlt : j < tl := by rw [List.length_take] at hj; omega
    rw [List.getElem_take] at hget; cases j with
    | zero =>
      rw [← hget]; have h0e := List.getElem?_eq_getElem (by omega : 0 < tmp.length)
      rw [h0] at h0e; exact Or.inl (congrArg BitVec.toNat (Option.some.inj h0e.symm))
    | succ k =>
      refine Or.inr ⟨k + 1, by omega, hjlt, ?_⟩
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  refine ⟨hiff, fun l hl => hmem_take l ((hiff l).mp hl), hnd_sw, ?_, ?_⟩
  · dsimp only [tmp_sw]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), h0]
  · dsimp only [tmp_sw]; by_cases hm1' : max_idx = 1
    · subst hm1'; rw [List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]

theorem eagerSub_lm_step {tmp : List (BitVec 32)} {lm : List (BitVec 8)} {i nmax : Nat}
    (hinv : ∀ l < nmax, lm[l]?.getD 0#8 ≠ 0#8 → ∃ j < i, (tmp[j]?.getD 0#32).toNat = l) :
    ∀ l < nmax, (lm.set (tmp[i]?.getD 0#32).toNat 1#8)[l]?.getD 0#8 ≠ 0#8 →
      ∃ j < i + 1, (tmp[j]?.getD 0#32).toNat = l := by
  intro l hl hnz; by_cases hli : l = (tmp[i]?.getD 0#32).toNat
  · exact ⟨i, by omega, hli.symm⟩
  · rw [List.getElem?_set_ne (Ne.symm hli)] at hnz
    obtain ⟨j, hj, hje⟩ := hinv l hl hnz; exact ⟨j, by omega, hje⟩

theorem eagerSub_lm_clear_step {tmp : List (BitVec 32)} {lm : List (BitVec 8)}
    {tlen i nmax : Nat} (hlm_len : lm.length = nmax) (hlt : (tmp[i]?.getD 0#32).toNat < nmax)
    (hinv : ∀ l < nmax, lm[l]?.getD 0#8 ≠ 0#8 →
      (∃ j < tlen, (tmp[j]?.getD 0#32).toNat = l) ∧ (∀ j < i, (tmp[j]?.getD 0#32).toNat ≠ l)) :
    ∀ l < nmax, (lm.set (tmp[i]?.getD 0#32).toNat 0#8)[l]?.getD 0#8 ≠ 0#8 →
      (∃ j < tlen, (tmp[j]?.getD 0#32).toNat = l) ∧
      (∀ j < i + 1, (tmp[j]?.getD 0#32).toNat ≠ l) := by
  intro l hl hnz; by_cases hli : l = (tmp[i]?.getD 0#32).toNat
  · rw [hli, List.getElem?_set_self (by omega), Option.getD_some] at hnz; exact absurd rfl hnz
  · rw [List.getElem?_set_ne (Ne.symm hli)] at hnz
    obtain ⟨hex, hprev⟩ := hinv l hl hnz; refine ⟨hex, fun j hj => ?_⟩
    by_cases hji : j = i; · subst hji; exact Ne.symm hli
    · exact hprev j (by omega)

/-- Binary resolution: from `(not_lit ^ 1, ot)` and `(not_lit, blk)`, derive `(blk, ot)`. -/
theorem s13_bin_resolve {F : CNF Nat} {not_lit ot blk : Nat}
    (h1 : F.EntailsClause (cnfClause [not_lit ^^^ 1, ot]))
    (h2 : F.EntailsClause (cnfClause [not_lit, blk])) :
    F.EntailsClause (cnfClause [blk, ot]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢
  intro α hα
  have hs1 := h1 α hα; have hs2 := h2 α hα
  simp only [clause_sat_cnfClause_iff, List.mem_cons, List.not_mem_nil, or_false] at hs1 hs2 ⊢
  rcases hs1 with ⟨l1, hl1_eq, hl1⟩ <;> rcases hs2 with ⟨l2, hl2_eq, hl2⟩
  rcases hl1_eq with hl1_eq | hl1_eq <;> rcases hl2_eq with hl2_eq | hl2_eq <;>
    (try rw [hl1_eq] at hl1) <;> (try rw [hl2_eq] at hl2)
  · exfalso
    have hsat1 : (cnfClause [litNeg not_lit]).Sat α := by
      change (cnfClause [not_lit ^^^ 1]).Sat α
      exact (sat_cnfClause_singleton α (not_lit ^^^ 1)).mpr hl1
    have hsat2 : (cnfClause [not_lit]).Sat α :=
      (sat_cnfClause_singleton α not_lit).mpr hl2
    exact absurd hsat2 ((sat_cnfClause_litNeg_iff α not_lit).mp hsat1)
  · exact ⟨_, Or.inl rfl, hl2⟩
  · exact ⟨_, Or.inr rfl, hl1⟩
  · exact ⟨_, Or.inl rfl, hl2⟩

/-! ## 3. Canonical Invariant, Arena, Watch & Witness Preservation Lemmas -/

/-- Set-membership invariant for `last_learned[0..8)` across `full_eager_subsume` updates. -/
@[expose] def FullLastLearnedIn (refs : List Nat) (ll : List (BitVec 32)) : Prop :=
  ∀ i < 8, let cr := ll[i]?.getD 0xFFFFFFFF#32; cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ refs

theorem fullLastLearnedIn_set_sentinel {refs : List Nat} {ll : List (BitVec 32)}
    (h : FullLastLearnedIn refs ll) (idx : Nat) :
    FullLastLearnedIn refs (ll.set idx 0xFFFFFFFF#32) := by
  intro i hi; dsimp only; by_cases hie : i = idx
  · subst hie; by_cases hlt : i < ll.length
    · rw [List.getElem?_set_self hlt]; exact Or.inl rfl
    · rw [List.getElem?_eq_none (by simp [List.length_set]; omega)]; exact Or.inl rfl
  · rw [List.getElem?_set_ne (Ne.symm hie)]; exact h i hi

theorem fullLastLearnedIn_shift_step {refs : List Nat} {ll : List (BitVec 32)}
    (h : FullLastLearnedIn refs ll) {k : Nat} (hk1 : 1 ≤ k) (hk8 : k < 8)
    (hlen : 8 ≤ ll.length) : FullLastLearnedIn refs (ll.set k (ll[k - 1]'(by omega))) := by
  intro i hi; dsimp only; by_cases hik : i = k
  · subst hik; rw [List.getElem?_set_self (by omega), Option.getD_some]
    simpa [List.getElem?_eq_getElem (by omega : i - 1 < ll.length)] using h (i - 1) (by omega)
  · rw [List.getElem?_set_ne (Ne.symm hik)]; exact h i hi

theorem fullLastLearnedIn_set0 {refs : List Nat} {ll : List (BitVec 32)}
    (h : FullLastLearnedIn refs ll) (v : BitVec 32) (hv : v.toNat ∈ refs) (hlen : 8 ≤ ll.length) :
    FullLastLearnedIn refs (ll.set 0 v) := by
  intro i hi; dsimp only; cases i with
  | zero => rw [List.getElem?_set_self (by omega), Option.getD_some]; exact Or.inr hv
  | succ j => rw [List.getElem?_set_ne (by omega)]; exact h (j + 1) hi

theorem fullLastLearnedWf_of_refs_subset {s s' : FullState}
    (h : FullLastLearnedWf s) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullLastLearnedWf s' := by
  intro i hi; dsimp only; rw [hll]
  exact (h i hi).elim Or.inl fun hr => Or.inr (hsub _ hr)

theorem fullExtScratchOk_of_pres {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullExtScratchOk c s' := by
  refine ⟨fullLastLearnedWf_of_refs_subset h.1 hpres.1 hsub, ?_⟩
  rw [hpres.2]; exact h.2

private theorem markGarb_lits_ne {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hlen : s.LengthsOk c)
    {cref r : Nat} (href : cref ∈ fullArenaClauseRefs s) (hr : r ∈ fullArenaClauseRefs s)
    (hne : r ≠ cref) (ag' : BitVec 64) :
    fullArenaClauseLitsCore
      { s.core with
        arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
        arena_garbage := ag' } r = fullArenaClauseLitsCore s.core r := by
  have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hw.arena.disjoint hr href hlt)
    · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2

theorem fullArenaVarsNodup_of_markGarb_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hlen : s.LengthsOk c)
    (hnd : FullArenaVarsNodup s) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullArenaVarsNodup s' := by
  intro s' r hr hng
  have hmg := hw.arena.markGarb hlen.core_ok href ag'
  have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rwa [hmg.1] at hr
  have har_len : cref < s.core.arena.length := by
    have := (hw.arena.refs_wf cref href).1; have := hlen.core_ok.arena_len_le
    have := hlen.core_ok.arena_len_arr; omega
  have hne : r ≠ cref := by
    rintro rfl
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore s' at hng
    rw [List.getElem?_set_self har_len, Option.getD_some] at hng
    have hbit : ((fullArenaHdr s r ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
      intro h; have := congrArg (·[19]) h; simp at this
    exact hbit (by simpa using hng)
  have hng0 : fullArenaClauseGarb s r = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
    simpa [s', List.getElem?_set_ne hne.symm] using hng
  unfold fullArenaClauseLits; rw [markGarb_lits_ne hw hlen href hr0 hne ag']; exact hnd r hr0 hng0

theorem fullOtfsWitnessInv_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) (tmp' : List (BitVec 32)) :
    FullOtfsWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem fullOtfsInvW_of_safetySlice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullOtfsInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullOtfsInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · exact fullExtScratchOk_of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [heq]

theorem fullOtfsInvW_with_conflicts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) (k' : BitVec 64) :
    FullOtfsInvW c F0 F_cur { s with scratch := { s.scratch with conflicts := k' } } :=
  fullOtfsInvW_of_safetySlice h ⟨h.1.core_ok, { h.1.scratch_ok with }⟩ rfl ⟨rfl, rfl⟩

theorem fullConflictOkW_with_scratch {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflictOkW F_cur s) (sc' : FullScratch) :
    FullConflictOkW F_cur { s with scratch := sc' } := h

theorem fullWstackDefrag_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wsort' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hpres : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l =
        fullWatchSizeCore s.core l ∧
      ∀ k < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l + k]? =
          s.core.wstk[fullWatchOffCore s.core l + k]?) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } } := by
  let hw := h.2.1
  let k' : FullCoreState :=
    { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
  have hwat : ModeWatchesInv F_cur k' :=
    fullWstackDefrag_preserves_modeWatchesInv hw.watches hlay' rfl rfl (fun _ r => r) hpres
  exact ⟨hlen',
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullBacktrack_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hs : FullOtfsInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hdm' : s'.core.dense_mode = s.core.dense_mode) (hpres : FullExtScratchPres s s') :
    FullSparseInvW c F0 F_cur s' := by
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har', hal']
  refine ⟨hlen', hw', ?_, ?_, fullExtScratchOk_of_pres hs.2.2.2.2.1 hpres fun _ h => hrefs ▸ h,
    hdm' ▸ hs.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hmrk', hlm']; exact hs.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
      fullArenaClauseGarbCore fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      fullArenaHdrCore
    rw [har', hal']; exact hs.2.2.2.1

theorem markGarb_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hlen : s.LengthsOk c)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64)
    (hnonact : ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hmg := hw.arena.markGarb hlen.core_ok href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  refine ⟨{ hw with
    arena := hmg.2
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
      · have hlg' := Classical.byContradiction fun hn => hbin hn
        rw [ite_eq_right hbin] at hrs ⊢
        have hne_cref := hnonact idx hidx hne hlg'
        have hgarb' : fullArenaClauseGarbCore s'.core (s.core.rsns[
            (s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = false := by
          unfold fullArenaClauseGarbCore fullArenaHdrCore
          rw [show s'.core.arena = s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
              from rfl, List.getElem?_set_ne hne_cref.symm]; exact hrs.2.1
        have hlits_eq := markGarb_lits_ne hw hlen href hrs.1 hne_cref ag'
        exact ⟨hrefs ▸ hrs.1, hgarb', fun q hq => hrs.2.2 q (hlits_eq ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      rw [ite_eq_right (fun h => absurd hlg h)] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact markGarb_lits_ne hw hlen href hrs.1 (hnonact idx hidx hne hlg) ag' ▸
        hw.reason_lit_mem idx hidx hne hlg }, hrefs⟩

theorem markGarb_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64)
    (hnonact : ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hlen' : s'.LengthsOk c :=
    ⟨{ h.1.core_ok with arena_len_arr := by simp [s', h.1.core_ok.arena_len_arr] }, h.1.scratch_ok⟩
  obtain ⟨hw', hrefs⟩ := markGarb_preserves_fullWitness h.2.1 h.1 href ag' hnonact
  have hnd' := fullArenaVarsNodup_of_markGarb_w h.2.1 h.1 h.2.2.2.1 href ag'
  refine ⟨⟨hlen', hw', h.2.2.1, hnd',
    fullExtScratchOk_of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr => hrefs ▸ hr, h.2.2.2.2.2⟩,
    hrefs⟩

theorem chronoAssign_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hw : FullWitnessInv c F0 F_cur s.core) (hlen : s.LengthsOk c)
    {lit rsn : BitVec 32} {alvl : Nat}
    {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64}
    {scratch' : FullScratch}
    (hsok' : scratch'.LengthsOk c) (hfll : flags'.length = c.max_vars)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (halvl_le : alvl ≤ s.core.cur_level)
    (hpos_rsn : 0 < alvl → rsn ≠ 0xFFFFFFFF#32)
    (hl0 : alvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hrsn : 0 < alvl → rsn ≠ 0xFFFFFFFF#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot]) ∧
        ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
          q = lit.toNat ∨ ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ alvl)
    (hrsn_mem : 0 < alvl → rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      lit.toNat ∈ fullArenaClauseLitsCore s.core rsn.toNat) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0 then 0xFFFFFFFF#32 else rsn
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
            rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            trail_end := s.core.trail_end + 1
            unassigned := unassigned', unflushed := unflushed' }
        scratch := scratch' }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core := by
  intro v rsn' s'
  have hcl := hlen.core_ok
  have hte_lt := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var := (hw.vals_zero_iff hlit).mp hun
  have hnlit_lt := litNeg_lt_two_mul hlit
  have hne_lit := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have halvl_lt32 : alvl < 2 ^ 32 := by
    have := fullInv_max_vars_lt32 c; have := hw.cur_level_le
    have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat =
      if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = s.core.trail_end
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars, (s'.core.lvl[w]?.getD 0#32).toNat =
      if w = v then alvl else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
        bv32_ofNat_toNat halvl_lt32]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars, s'.core.vals[l]?.getD 0#8 =
      if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
      else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars, s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
      if w = v then rsn' else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
      vals_len := (by simp [s', hcl.vals_len]), flags_len := hfll,
      lvl_len := (by simp [s', hcl.lvl_len]), rsns_len := (by simp [s', hcl.rsns_len]),
      trl_len := (by simp [s', hcl.trl_len]),
      trail_pos_len := (by simp [s', hcl.trail_pos_len]),
      trail_end_le := (by dsimp [s']; omega),
      propagated_le := (by have := hcl.propagated_le; dsimp [s']; omega) }, hsok'⟩
  refine ⟨hlen', {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := by dsimp [s']; have := hw.cur_level_le; omega
    trail_lits_lt := fun i hi => by
      dsimp only [s'] at hi ⊢; rw [htrl_get i hi]; split
      · exact hlit
      · exact hw.trail_lits_lt i (by omega)
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp only [s'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      rw [hvals_get l hl]; split; exact Or.inr (Or.inr rfl); split; exact Or.inr (Or.inl rfl)
      exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp only [s']; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq
          rw [ite_eq_right (show lit.toNat ≠ lit.toNat ^^^ 1 from hne_lit.symm)]; simp
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp only [s']; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨s.core.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq
          have hl_eq : l = lit.toNat ^^^ 1 := by
            have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
            rw [h1] at h; exact h.symm
          simp [hl_eq]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by
            have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
    lvl_le := fun i hi => by
      dsimp only [s'] at hi ⊢; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simpa using halvl_le
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]; rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
        rw [ite_eq_right (hnot_var i hilt)]; exact hw.lvl_le i hilt
    dec_earliest := fun i j hi hj hleq hdec => by
      dsimp only [s'] at hi hj; rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
      by_cases hje : j = s.core.trail_end
      · subst hje; simp only [↓reduceIte] at hleq hdec
        rw [hlvl_get v (by omega), hrsn_get v (by omega)] at hdec; simp only [↓reduceIte] at hdec
        have hal0 : alvl ≠ 0 := by omega
        exact absurd (by simpa [rsn', hal0] using hdec.2) (hpos_rsn hdec.1)
      · by_cases hie : i = s.core.trail_end
        · omega
        · have hilt : i < s.core.trail_end := by omega
          have hjlt : j < s.core.trail_end := by omega
          simp only [hie, hje, ↓reduceIte] at hleq hdec
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega),
            hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
          rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega),
            hrsn_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
          rw [ite_eq_right (hnot_var i hilt)] at hleq
          rw [ite_eq_right (hnot_var j hjlt)] at hleq hdec
          rw [ite_eq_right (hnot_var j hjlt)] at hdec
          exact hw.dec_earliest i j hilt hjlt hleq hdec
    levels_inhabited := fun L hL1 hLle => by
      dsimp only [s'] at hLle ⊢; obtain ⟨i, hi, hli⟩ := hw.levels_inhabited L hL1 hLle
      refine ⟨i, by omega, ?_⟩; rw [htrl_get i (by omega)]
      simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hw.trail_lits_lt i hi; omega),
        ite_eq_right (hnot_var i hi)]; exact hli
    level0_sound := fun i hi hli => by
      dsimp only [s'] at hi; rw [htrl_get i hi] at hli ⊢; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; exact hl0 hli
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hli
        rw [ite_eq_right (hnot_var i hilt)] at hli; exact hw.level0_sound i hilt hli
    trail_pos_inv := fun i hi => by
      dsimp only [s'] at hi; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [s']
        rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        have hnv := hnot_var i hilt; dsimp only [s']
        rw [List.getElem?_set_ne (Ne.symm hnv)]; exact hw.trail_pos_inv i hilt
    level0_rsn_none := fun idx hidx hli => by
      dsimp only [s'] at hidx; rw [htrl_get idx hidx] at hli ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; rw [hrsn_get v (by omega)]; simp [rsn', hli]
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢; have hnv := hnot_var idx hilt
        rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega), ite_eq_right hnv] at hli
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega), ite_eq_right hnv]
        exact hw.level0_rsn_none idx hilt hli
    frame_trail_lt := fun L hL => Nat.le_trans (hw.frame_trail_lt L hL) (by dsimp [s']; omega)
    frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := fun L hL1 hLle i hi => by
      have hi_le := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle)
      have hb := hw.frame_trail_before_lt L hL1 hLle i hi; change _ < L at ⊢
      rw [htrl_get i (by omega)]; simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hw.trail_lits_lt i hi_le; omega), ite_eq_right (hnot_var i hi_le)]
      exact hb
    frame_dec_lt := hw.frame_dec_lt
    reason_inv := fun idx hidx hne => by
      dsimp only [s'] at hidx; rw [htrl_get idx hidx] at hne ⊢
      have hrsn_step : ∀ {p : Nat} {rsn_i : BitVec 32} {lim : Nat},
          lim ≤ idx → p < 2 * s.core.cur_vars → rsn_i ≠ 0xFFFFFFFF#32 →
          (if (rsn_i &&& 0x80000000#32) ≠ 0#32 then
            let ot := (rsn_i &&& 0x7FFFFFFF#32).toNat
            ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
            ∃ m < lim, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
              (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ (s'.core.lvl[p / 2]?.getD 0#32).toNat
          else
            rsn_i.toNat ∈ fullArenaClauseRefsCore s.core ∧
            fullArenaClauseGarbCore s.core rsn_i.toNat = false ∧
            ∀ q ∈ fullArenaClauseLitsCore s.core rsn_i.toNat,
              q = p ∨ ∃ m < lim, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ (s'.core.lvl[p / 2]?.getD 0#32).toNat) →
          if (rsn_i &&& 0x80000000#32) ≠ 0#32 then
            let ot := (rsn_i &&& 0x7FFFFFFF#32).toNat
            ot < 2 * s'.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
            ∃ m < idx, (s'.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
              (s'.core.lvl[ot / 2]?.getD 0#32).toNat ≤ (s'.core.lvl[p / 2]?.getD 0#32).toNat
          else
            rsn_i.toNat ∈ fullArenaClauseRefsCore s'.core ∧
            fullArenaClauseGarbCore s'.core rsn_i.toNat = false ∧
            ∀ q ∈ fullArenaClauseLitsCore s'.core rsn_i.toNat,
              q = p ∨ ∃ m < idx, (s'.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                (s'.core.lvl[q / 2]?.getD 0#32).toNat ≤ (s'.core.lvl[p / 2]?.getD 0#32).toNat := by
        intro p rsn_i lim hlim hp _ hsrc
        have hm_le : lim ≤ s.core.trail_end := by omega
        by_cases hbin : (rsn_i &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hsrc ⊢; obtain ⟨hot, hent, m, hm, hmeq, hle⟩ := hsrc
          have hot_v : (rsn_i &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
            intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
            exact hme (by simpa [fullInv_var_xor1] using heqv)
          refine ⟨hot, hent, m, by omega, ?_, ?_⟩
          · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
          · rw [hlvl_get _ (by omega)]; rw [ite_eq_right hot_v]; exact hle
        · rw [ite_eq_right hbin] at hsrc ⊢
          refine ⟨hsrc.1, hsrc.2.1, fun q hq => ?_⟩
          have hq' : q ∈ fullArenaClauseLitsCore s.core rsn_i.toNat := by
            simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using hq
          refine (hsrc.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hle⟩ => Or.inr ⟨m, by omega, ?_, ?_⟩
          · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
          · have hq_lt : q < 2 * s.core.cur_vars := hw.arena.lits_lt _ hsrc.1 hsrc.2.1 q hq'
            have hqv : q / 2 ≠ v := by
              intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
              exact hme (by simpa [fullInv_var_xor1] using heqv)
            rw [hlvl_get _ (by omega)]; rw [ite_eq_right hqv]; exact hle
      by_cases hie : idx = s.core.trail_end
      · subst hie; simp only [↓reduceIte] at hne ⊢
        rw [hrsn_get v (by omega)] at hne ⊢; simp only [↓reduceIte] at hne ⊢
        by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · have halpos : 0 < alvl := Nat.zero_lt_of_ne_zero hal0
          have hrs := hrsn halpos (by simpa [rsn', hal0] using hne)
          simp only [rsn', hal0, ↓reduceIte] at hne hrs ⊢
          refine hrsn_step (lim := s.core.trail_end) (Nat.le_refl _) hlit hne ?_
          rw [hlvl_get v (by omega), ite_eq_left rfl]; exact hrs
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne ⊢; have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne ⊢
        rw [ite_eq_right hnv] at hne ⊢
        have hlt_p := hw.trail_lits_lt idx hilt
        refine hrsn_step (lim := idx) (Nat.le_refl _) hlt_p hne ?_
        rw [hlvl_get _ (by omega), ite_eq_right hnv]; exact hw.reason_inv idx hilt hne
    reason_lit_mem := fun idx hidx hne hlg => by
      dsimp only [s'] at hidx; rw [htrl_get idx hidx] at hne hlg ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne hlg ⊢
        rw [hrsn_get v (by omega)] at hne hlg ⊢; simp only [↓reduceIte] at hne hlg ⊢
        by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · simp only [rsn', hal0, ↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
            hrsn_mem (Nat.zero_lt_of_ne_zero hal0) hne hlg
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne hlg ⊢; have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne hlg ⊢
        rw [ite_eq_right hnv] at hne hlg ⊢
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
          hw.reason_lit_mem idx hilt hne hlg }⟩

theorem unsat_of_level0_bin_conflict {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k) {l0 l1 : Nat}
    (h0lt : l0 < 2 * k.cur_vars) (h1lt : l1 < 2 * k.cur_vars)
    (hl0 : (k.lvl[l0 / 2]?.getD 0#32).toNat = 0)
    (hl1 : (k.lvl[l1 / 2]?.getD 0#32).toNat = 0)
    (hf0 : k.vals[l0]?.getD 0#8 = 0xFF#8) (hf1 : k.vals[l1]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0, l1])) : F0.Unsat := by
  refine hw.ext_sound.2
    (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l h0lt).mp hf0
    have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hl0)
    rwa [hieq] at hs
  · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l h1lt).mp hf1
    have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hl1)
    rwa [hieq] at hs

theorem unsat_of_level0_conflict {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (hg : fullArenaClauseGarbCore k cref = false)
    (hfals : ∀ l ∈ fullArenaClauseLitsCore k cref,
      k.vals[l]?.getD 0#8 = 0xFF#8 ∧ (k.lvl[l / 2]?.getD 0#32).toNat = 0) : F0.Unsat := by
  refine hw.ext_sound.2 (unsat_of_entails_nil
    (entails_of_mem_or_false (hw.arena.entails cref href hg) fun l hl => Or.inr ?_))
  obtain ⟨hf, hlv⟩ := hfals l hl
  obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt cref href hg l hl)).mp hf
  have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hlv)
  rwa [hieq] at hs

private theorem arenaUpdate_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {arena' : List (BitVec 32)} {ag' ni' nr' : BitVec 64}
    (harena : FullArenaClausesInv c F_cur
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' })
    (hrefs : fullArenaClauseRefsCore
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' } =
      fullArenaClauseRefsCore k)
    (hact : ∀ idx < k.trail_end,
      (idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      fullArenaClauseGarbCore
        { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' }
        rsn.toNat = false ∧
      List.Perm
        (fullArenaClauseLitsCore
          { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' }
          rsn.toNat)
        (fullArenaClauseLitsCore k rsn.toNat)) :
    FullWitnessCutInv c F0 F_cur cut
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' } :=
  { hw with
    arena := harena
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv_below := fun idx hidx hlv hne => by
      have hrs := hw.reason_inv_below idx hidx hlv hne
      by_cases hlg : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32
      · rw [ite_eq_right (fun h => h hlg)] at hrs ⊢
        have ha := hact idx hidx (.inr hlv) hne hlg
        exact ⟨hrefs ▸ hrs.1, ha.1, fun q hq => hrs.2.2 q (ha.2.mem_iff.mp hq)⟩
      · rw [ite_eq_left (fun h => absurd h hlg)] at hrs ⊢; exact hrs
    reason_lit_mem_below := fun idx hidx hlv hne hlg => by
      have ha := hact idx hidx (.inr hlv) hne hlg
      exact ha.2.symm.mem_iff.mp (hw.reason_lit_mem_below idx hidx hlv hne hlg)
    reason_inv_cut := fun idx hidx hne => by
      have hrs := hw.reason_inv_cut idx hidx hne
      by_cases hlg : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32
      · rw [ite_eq_right (fun h => h hlg)] at hrs ⊢
        have ha := hact idx (Nat.lt_of_lt_of_le hidx hw.cut_le) (.inl hidx) hne hlg
        exact ⟨hrefs ▸ hrs.1, ha.1, fun q hq => hrs.2.2 q (ha.2.mem_iff.mp hq)⟩
      · rw [ite_eq_left (fun h => absurd h hlg)] at hrs ⊢; exact hrs
    reason_lit_mem_cut := fun idx hidx hne hlg => by
      have ha := hact idx (Nat.lt_of_lt_of_le hidx hw.cut_le) (.inl hidx) hne hlg
      exact ha.2.symm.mem_iff.mp (hw.reason_lit_mem_cut idx hidx hne hlg) }

private theorem list_countP_set {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (i : Nat) (y : α) (_ : i < xs.length),
      (xs.set i y).countP p + (if p xs[i] then 1 else 0) = xs.countP p + (if p y then 1 else 0)
  | [], _, _, hi => by simp at hi
  | x :: xs, 0, y, _ => by
    simp only [List.set_cons_zero, List.countP_cons, List.getElem_cons_zero]
    by_cases hpx : p x <;> by_cases hpy : p y <;> simp [hpx, hpy] <;> omega
  | x :: xs, i + 1, y, hi => by
    have ih := list_countP_set p xs i y (by simpa using hi)
    simp only [List.set_cons_succ, List.countP_cons, List.getElem_cons_succ]
    by_cases hpx : p x <;> simp [hpx] <;> omega

private theorem list_swap_perm {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)).Perm xs := by
  by_cases hij : j = i
  · subst hij; simp [List.set_getElem_self]
  · rw [List.perm_iff_count]; intro a
    have hc1 := list_countP_set (· == a) (xs.set i (xs[j]'hj)) j (xs[i]'hi) (by simpa using hj)
    have hc2 := list_countP_set (· == a) xs i (xs[j]'hj) hi
    simp only [List.count] at hc1 hc2 ⊢
    rw [List.getElem_set_ne (Ne.symm hij)] at hc1; omega

theorem swapCl_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k) {cref i j : Nat}
    (hcref : cref ∈ fullArenaClauseRefsCore k)
    (hi : i < fullArenaClauseSizeCore k cref) (hj : j < fullArenaClauseSizeCore k cref) :
    let lits := k.arena
    let li := lits[cref + 3 + i]?.getD 0#32
    let lj := lits[cref + 3 + j]?.getD 0#32
    let arena' := (lits.set (cref + 3 + i) lj).set (cref + 3 + j) li
    let k' := { k with arena := arena' }
    FullWitnessCutInv c F0 F_cur cut k' ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref ∧
    fullArenaClauseGarbCore k' cref = fullArenaClauseGarbCore k cref ∧
    (fullArenaClauseLitsCore k' cref).Perm (fullArenaClauseLitsCore k cref) ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro lits li lj arena' k'
  have ha := hw.arena
  have hwf := ha.refs_wf cref hcref
  have hlen_ar : lits.length = c.arena_cap := hlen.arena_len_arr
  have hle_ar : k.arena_len ≤ c.arena_cap := hlen.arena_len_le
  have hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ lits.length := by omega
  have har'_len : arena'.length = c.arena_cap := by simp [arena', lits, hlen_ar]
  have hout : ∀ idx, idx < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ idx →
      arena'[idx]? = lits[idx]? := fun idx hidx => by
    dsimp [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' k.arena_len r = fullArenaNextOff lits k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      exact fullArenaNextOff_congr_block (hout _ (Or.inl (by omega)))
        (hout _ (Or.inl (by omega))) (fun q hq1 _ => hout q (Or.inr hq1))
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := ha.disjoint hr hcref hlt
        have hdn : fullArenaNextOff lits k.arena_len r ≤ cref :=
          fullArenaScanRefs_disjoint hr hcref hlt
        have hr_wf := ha.refs_wf r hr
        have hr_sz := hr_wf.2.1
        have hr_bd := hr_wf.2.2.1
        exact fullArenaNextOff_congr_block (hout _ (Or.inl (by omega)))
          (hout _ (Or.inl (by omega))) fun q _ hq2 => hout q (Or.inl (by omega))
      · have hgt_d := ha.disjoint hcref hr hgt
        exact fullArenaNextOff_congr_block (hout _ (Or.inr hgt_d))
          (hout _ (Or.inr (by omega))) fun q hq1 _ => hout q (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_c : fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref := by
    unfold fullArenaClauseSizeCore k'; rw [hout (cref + 2) (Or.inl (by omega))]
  have hng_c : fullArenaClauseGarbCore k' cref = fullArenaClauseGarbCore k cref := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [hout cref (Or.inl (by omega))]
  have hperm : (fullArenaClauseLitsCore k' cref).Perm (fullArenaClauseLitsCore k cref) := by
    let xs := (lits.drop (cref + 3)).take (fullArenaClauseSizeCore k cref)
    have hxs_len : xs.length = fullArenaClauseSizeCore k cref := by
      simp [xs, List.length_take, List.length_drop]; omega
    have hli : li = xs[i]'(by omega) := by
      dsimp only [li]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [xs, List.getElem_take, List.getElem_drop]
    have hlj : lj = xs[j]'(by omega) := by
      dsimp only [lj]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [xs, List.getElem_take, List.getElem_drop]
    have hswap : (arena'.drop (cref + 3)).take (fullArenaClauseSizeCore k cref) =
        (xs.set i lj).set j li := by
      apply List.ext_getElem
      · simp [xs, arena', List.length_take, List.length_drop]
      · intro p hp1 hp2
        have hplt : p < fullArenaClauseSizeCore k cref := by
          simp [List.length_take, List.length_drop] at hp1; omega
        rw [List.getElem_take, List.getElem_drop]
        have hopt : arena'[cref + 3 + p]? = some (((xs.set i lj).set j li)[p]'hp2) := by
          dsimp only [arena']
          by_cases hpj : p = j
          · subst p; rw [List.getElem?_set_self (by simp [List.length_set, hlen_ar]; omega),
              List.getElem_set_self (by simp [List.length_set, hxs_len]; omega), hli]
          · rw [List.getElem?_set_ne (by omega), List.getElem_set_ne (Ne.symm hpj)]
            by_cases hpi : p = i
            · subst p; rw [List.getElem?_set_self (by rw [hlen_ar]; omega),
                List.getElem_set_self (by rw [List.length_set, hxs_len]; exact hi), hlj]
            · rw [List.getElem?_set_ne (by omega), List.getElem_set_ne (Ne.symm hpi),
                List.getElem?_eq_getElem (by omega)]
              simp [xs, List.getElem_take, List.getElem_drop]
        have hopt0 := List.getElem?_eq_getElem (show cref + 3 + p < arena'.length by
          rw [har'_len]; omega)
        rw [hopt0] at hopt; exact Option.some.inj hopt
    unfold fullArenaClauseLitsCore k'; rw [hsz_c, hswap]
    have hsw : ((xs.set i lj).set j li).Perm xs := by
      simpa only [hli, hlj] using list_swap_perm xs (hxs_len ▸ hi) (hxs_len ▸ hj)
    exact hsw.map BitVec.toNat
  have hother : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr hne
    have hdisj : r + 3 + fullArenaClauseSizeCore k r ≤ cref ∨
        cref + 3 + fullArenaClauseSizeCore k cref ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (ha.disjoint hr hcref hlt)
      · exact Or.inr (ha.disjoint hcref hr hgt)
    have hrwf := ha.refs_wf r hr
    have hr_3 := hrwf.2.1
    have hr_bd := hrwf.2.2.1
    have hr_nx := hrwf.2.2.2.1
    have hszr : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
      unfold fullArenaClauseSizeCore k'
      rcases hdisj with h1 | h2
      · rw [hout (r + 2) (Or.inl (by omega))]
      · rw [hout (r + 2) (Or.inr (by omega))]
    have hgar : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore k'
      rcases hdisj with h1 | h2
      · rw [hout r (Or.inl (by omega))]
      · rw [hout r (Or.inr h2)]
    have hk_ar := hlen.arena_len_arr
    have hk_le := hlen.arena_len_le
    refine ⟨hszr, hgar, fullArenaClauseLitsCore_eq_of_hold (by omega)
      (by dsimp [k']; rw [har'_len]; omega) hszr fun q hq => ?_⟩
    rcases hdisj with h1 | h2
    · exact hout (r + 3 + q) (Or.inl (by omega))
    · exact hout (r + 3 + q) (Or.inr (by omega))
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp [k']; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_c]; exact ha.refs_wf cref hr
      · rw [(hother r hr hrc).1]; exact ha.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hr_out : r < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ r := by
        by_cases hrc : r = cref
        · subst r; exact Or.inl (by omega)
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := ha.disjoint hr hcref hlt; exact Or.inl (by omega)
          · exact Or.inr (ha.disjoint hcref hr hgt)
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh; rwa [hout r hr_out] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
      by_cases hrc : r = cref
      · subst r; rw [hsz_c]; exact ⟨t, ht1, ht2, by dsimp [k']; rwa [hout t (Or.inr ht1)]⟩
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have hdisj := ha.disjoint hr hcref hlt
          have hnxt_lt := fullArenaScanRefs_disjoint hr hcref hlt
          have hr3 := (ha.refs_wf r hr).1
          have hget_r : lits[r]? = some (fullArenaHdrCore k r) := by
            unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsh_ar : (lits[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
            rw [hget_r, Option.getD_some]; exact hsh0
          obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
            fullArenaNextOff_hits_sentinel hr3 hsh_ar ht1 ht2 hsent
          dsimp only [lits] at ht0_nxt
          rw [(hother r hr hrc).1]
          exact ⟨t0, ht0_lo, by dsimp [k']; omega,
            by dsimp [k']; rw [hout t0 (Or.inl (by omega))]; exact ht0_sent⟩
        · have hdisj := ha.disjoint hcref hr hgt
          rw [(hother r hr hrc).1]
          exact ⟨t, ht1, ht2, by dsimp [k']; rw [hout t (Or.inr (by omega))]; exact hsent⟩
    · intro r hr hng l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hng_c] at hng; exact ha.lits_lt cref hr hng l (hperm.mem_iff.mp hl)
      · rw [(hother r hr hrc).2.1] at hng; rw [(hother r hr hrc).2.2] at hl
        exact ha.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hng_c] at hng
        exact entails_of_mem_or_false (ha.entails cref hr hng) fun l hl =>
          Or.inl (hperm.symm.mem_iff.mp hl)
      · rw [(hother r hr hrc).2.1] at hng; rw [(hother r hr hrc).2.2]
        exact ha.entails r hr hng
  refine ⟨arenaUpdate_preserves_fullWitnessCut hw harena' hrefs fun idx hidx hc hne hlg => ?_,
    hrefs, hsz_c, hng_c, hperm, hother⟩
  have hrs := hc.elim (fun hcut => hw.reason_inv_cut idx hcut hne)
    (fun hlv => hw.reason_inv_below idx hidx hlv hne)
  rw [ite_eq_right (fun h => absurd hlg h)] at hrs
  by_cases hrc : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = cref
  · rw [hrc] at hrs ⊢; exact ⟨hng_c.trans hrs.2.1, hperm⟩
  · have ho := hother _ hrs.1 hrc; exact ⟨ho.2.1.trans hrs.2.1, ho.2.2 ▸ List.Perm.refl _⟩

theorem watchPush_large_preserves {F_cur : List (List Nat)} {k : FullCoreState}
    {lit : Nat} {w0 cref : BitVec 32}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' oom' : BitVec 64}
    (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    (hlit : lit < 2 * k.cur_vars)
    (hlay : WatchStackLayout
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' })
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore { k with wvec := wvec' } l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec' } l + idx]? =
          k.wstk[fullWatchOffCore k l + idx]?)
    (hsz : fullWatchSizeCore { k with wvec := wvec' } lit = fullWatchSizeCore k lit + 2)
    (hsame : ∀ idx < fullWatchSizeCore k lit,
      wstk'[fullWatchOffCore { k with wvec := wvec' } lit + idx]? =
        k.wstk[fullWatchOffCore k lit + idx]?)
    (hw0 : wstk'[fullWatchOffCore { k with wvec := wvec' } lit + fullWatchSizeCore k lit]? =
      some w0)
    (hw1 : wstk'[fullWatchOffCore { k with wvec := wvec' } lit + fullWatchSizeCore k lit + 1]? =
      some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k) :
    ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' } := by
  let k' : FullCoreState := { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := wu', oom := oom' }
  have hw0_sp : WatchesInv F_cur k := by
    unfold ModeWatchesInv at hw; rw [ite_eq_left hdm] at hw; exact hw
  change ModeWatchesInv F_cur k'
  unfold ModeWatchesInv; rw [ite_eq_left (by simp [k', hdm])]
  refine ⟨hlay, fun l hl => ?_⟩
  by_cases hll : l = lit
  · subst hll; change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l + 2 from hsz]
    refine fullWatchSlice_append_large (k := k) (k' := k') (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsame idx hi)
      (hw0_sp.slices l hl) ?_ ?_ hflag hlt href
    · simpa only [k', fullWatchOffCore] using hw0
    · simpa only [k', fullWatchOffCore] using hw1
  · obtain ⟨hszl, hsl⟩ := hother l hl hll
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l from hszl]
    exact fullWatchSlice_relocate (k := k) (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsl idx hi) (hw0_sp.slices l hl)

theorem watchPush_fail_preserves {F_cur : List (List Nat)} {k : FullCoreState}
    (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' oom' : BitVec 64}
    (hlay : WatchStackLayout
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' })
    (hsame : ∀ l < 2 * k.cur_vars,
      fullWatchSizeCore { k with wvec := wvec' } l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec' } l + idx]? =
          k.wstk[fullWatchOffCore k l + idx]?) :
    ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' } := by
  let k' : FullCoreState := { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := wu', oom := oom' }
  have hw0_sp : WatchesInv F_cur k := by
    unfold ModeWatchesInv at hw; rw [ite_eq_left hdm] at hw; exact hw
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  change ModeWatchesInv F_cur k'
  unfold ModeWatchesInv; rw [ite_eq_left (by simp [k', hdm])]
  refine ⟨hlay, fun l hl => ?_⟩
  obtain ⟨hszl, hsl⟩ := hsame l hl
  change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
  rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l from hszl]
  exact fullWatchSlice_relocate (k := k) (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
    (fun idx hi => by simpa only [k', fullWatchOffCore] using hsl idx hi) (hw0_sp.slices l hl)

end

end LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
