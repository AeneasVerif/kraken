/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.MemLemmas
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Scoped Tactics & `FullMemArenaOut` Accessors (`Proof.Collect.Tactics`)

Provides strictly scoped WP stepping macros/elaborators (`M6Tactics1`), `FullMemArenaOut`
splitting/focusing lemmas, and `@[scoped c0_load]` / `@[scoped c0_store]` rules (`M6Tactics2a`)
under `public section`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Stripping & Symbolic Stepping Tactics (`M6Tactics1`) -/

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

namespace M6Tactics1

@[scoped bv_c0 high] private theorem bv64_and255_toNat (x : BitVec 64) :
    (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

scoped macro "m6_strip" : tactic =>
  `(tactic| first
    | apply LeanQbe.T.Examples.Kissat.Proof.Collect.strip_le_32_64
    | apply LeanQbe.T.Examples.Kissat.Proof.Collect.strip_le_8_32
    | apply LeanQbe.T.Examples.Kissat.Proof.Collect.strip_le_8_64)

scoped macro "m6_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _)

scoped macro "m6_steps" : tactic =>
  `(tactic| (
    (try m6_unmdata)
    (repeat m6_strip)
    c0_steps
    repeat (any_goals (m6_strip; repeat m6_strip); c0_steps)))

scoped macro "fr_strip" : tactic => `(tactic| m6_strip)
scoped macro "fr_unmdata" : tactic => `(tactic| m6_unmdata)
scoped macro "fr_steps" : tactic => `(tactic| m6_steps)

scoped elab "m6_to_group" : tactic => do
  let mut stk : List Lean.MVarId := ← Lean.Elab.Tactic.getUnsolvedGoals
  let mut out : Array Lean.MVarId := #[]
  for _ in [:5000] do
    match stk with
    | [] => break
    | g :: rest =>
      stk := rest
      if ← g.isAssigned then continue
      Lean.Elab.Tactic.setGoals [g]
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
      let g ← Lean.Elab.Tactic.getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
        let _ ← Lean.Elab.Tactic.evalTactic
          (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
        let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
      let g ← Lean.Elab.Tactic.getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← (try LeanQbe.T.C0Step.stepOnce catch _ => pure false) then
        stk := (← Lean.Elab.Tactic.getUnsolvedGoals) ++ stk
      else out := out.push g
  Lean.Elab.Tactic.setGoals (out.toList ++ stk)

scoped elab "m6_c0_steps" : tactic => do
  let mut stk : List Lean.MVarId := ← Lean.Elab.Tactic.getUnsolvedGoals
  let mut out : Array Lean.MVarId := #[]
  for _ in [:5000] do
    match stk with
    | [] => break
    | g :: rest =>
      stk := rest
      if ← g.isAssigned then continue
      Lean.Elab.Tactic.setGoals [g]
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
      let g ← Lean.Elab.Tactic.getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
        let _ ← Lean.Elab.Tactic.evalTactic
          (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
        let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| repeat m6_strip))
      if ← (try LeanQbe.T.C0Step.stepOnce catch _ => pure false) then
        stk := (← Lean.Elab.Tactic.getUnsolvedGoals) ++ stk
      else out := out.push g
  Lean.Elab.Tactic.setGoals (out.toList ++ stk)

scoped elab "m6_split" : tactic => do
  for _ in [:100] do
    let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

scoped elab "m6_split_fast" : tactic => do
  for _ in [:100] do
    let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let hc := Lean.mkIdent `hc
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals
        ((try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at $hc:ident)
         c0_cond $hc; try (exfalso; c0_bound))))
      break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

scoped elab "m6_to_jnz" : tactic => do
  for _ in [:100] do
    let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

scoped elab "m6_usteps" : tactic => do
  for _ in [:100] do
    let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        (((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.store ∨
         ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz) then break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

scoped elab "m6_nojoin" : tactic => do
  let mut stk : List Lean.MVarId := ← Lean.Elab.Tactic.getUnsolvedGoals
  let mut out : Array Lean.MVarId := #[]
  for _ in [:5000] do
    match stk with
    | [] => break
    | g :: rest =>
      stk := rest
      if ← g.isAssigned then continue
      Lean.Elab.Tactic.setGoals [g]
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
      let ty := (← Lean.instantiateMVars
        (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
      if ty.getAppFn.isFVar then
        out := out.push g
      else
        if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
            ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
          let _ ← Lean.Elab.Tactic.evalTactic
            (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
          let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
        let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| repeat m6_strip))
        if ← (try LeanQbe.T.C0Step.stepOnce catch _ => pure false) then
          stk := (← Lean.Elab.Tactic.getUnsolvedGoals) ++ stk
        else out := out.push g
  Lean.Elab.Tactic.setGoals (out.toList ++ stk)

scoped macro "m6_tiny_simp" : tactic =>
  `(tactic| simp only [
      LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk,
      LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_sub_eq, LeanQbe.T.wp_let_mul_eq,
      LeanQbe.T.wp_let_and_eq, LeanQbe.T.wp_let_or_eq,
      LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_zext_eq, LeanQbe.T.wp_let_sext_eq,
      LeanQbe.T.wp_let_trunc_eq,
      LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule,
      LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.sgt,
      LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
      LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
      LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne,
      LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq, LeanQbe.T.evalBits_ugt_eq,
      LeanQbe.T.evalBits_sgt_eq,
      LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp,
      cast_eq, Bool.false_eq_true, ite_false, ite_true,
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul])

scoped macro "m6_tiny_lets" : tactic =>
  `(tactic| (
    try m6_unmdata
    try repeat (first | (m6_strip; try m6_tiny_simp) | m6_tiny_simp)))

scoped macro "m6_tiny_jump" : tactic =>
  `(tactic| (
    m6_tiny_lets
    try repeat (first | (refine ⟨by decide, ?_⟩; m6_tiny_lets) | m6_strip)
    try simp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]
    try rw [LeanQbe.T.wp_jump]
    try simp only [LeanQbe.T.wp_ret]))

scoped elab "m6_jnz" : tactic => do
  for _ in [:100] do
    let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let hc := Lean.mkIdent `hc
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals
        (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at $hc:ident)
        c0_cond $hc
        try m6_tiny_lets
        try repeat m6_strip
        try rw [LeanQbe.T.wp_jump]))
      break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

scoped macro "m6_fast" : tactic => `(tactic| (m6_tiny_lets; m6_steps))

end M6Tactics1

/-! ## 2. `FullMemArenaOut` Footprint & Scoped Accessors (`M6Tactics2a`) -/

theorem bv64_mul4_eq_ofNat (i : BitVec 64) :
    i * 4#64 = BitVec.ofNat 64 ((32 + 7) / 8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp [Nat.mul_comm]

theorem fullMem_eq_arenaOut (c : FullCfg) (s : FullState) :
    FullMem c s = (array (t := i32) c.pArena s.core.arena ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ FullMemArenaOut c s) := by
  funext m; apply propext
  unfold FullMem FullCoreArrays FullCoreDynArrs FullScratchArrays FullScrDynArrs FullMemArenaOut
  constructor <;> intro hm <;> ecancel

theorem array32_split_at {a : BitVec 64} {xs : List (BitVec 32)} {k : Nat}
    (hk : k ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) a (xs.take k) ⋆
       array (t := i32) (a + BitVec.ofNat 64 (4 * k)) (xs.drop k)) := by
  have h1 : xs.take k ++ xs.drop k = xs := List.take_append_drop k xs
  have h2 : array (t := i32) a (xs.take k ++ xs.drop k) = array (t := i32) a xs := by rw [h1]
  rw [← h2, array_append (t := i32)]
  have hlen : (xs.take k).length = k := by simp [List.length_take, hk]
  simp [Ty.bytes, Ty.size, i32, hlen, Nat.mul_comm]

theorem full_hdr_tail_words_first_red (c : FullCfg) (s : FullState) (fr' : BitVec 64) :
    hdrTailWords c { s with core := { s.core with first_reducible := fr' } } =
      (hdrTailWords c s).set 56 fr' := by
  simp [hdrTailWords, HdrWordField.tailChunk0, HdrWordField.tailChunk1,
    HdrWordField.tailChunk2, HdrWordField.tailChunk3]

private def FullCoreU32ANoRsns (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i32) c.pFlags k.flags ⋆ array (t := i32) c.pLevel k.lvl ⋆
  array (t := i32) c.pTrail k.trl ⋆ array (t := i32) c.pTrailPos k.trail_pos ⋆
  array (t := i32) c.pTmp k.tmp ⋆ array (t := i32) c.pMinClr k.min_clr

private def FullMemArenaNoRsns (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
  FullCoreU32ANoRsns c s.core ⋆ FullCoreU32B c s.core ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

private theorem fullMemArenaOut_eq_rsns (c : FullCfg) (s : FullState) :
    FullMemArenaOut c s = (array (t := i32) c.pReason s.core.rsns ⋆ FullMemArenaNoRsns c s) := by
  funext m; apply propext
  unfold FullMemArenaOut FullMemArenaNoRsns FullCoreU32A FullCoreU32ANoRsns
  constructor <;> intro hm <;> ecancel

theorem fullMemArenaOut_congr_arena_buf (c : FullCfg) (s : FullState)
    (ar' rsns' : List (BitVec 32)) (fred' : BitVec 64) (buf' : List (BitVec 32)) :
    FullMemArenaOut c
        { s with
          core := { s.core with arena := ar', rsns := rsns', first_reducible := fred' }
          scratch := { s.scratch with scratch_buf := buf' } } =
      FullMemArenaOut c
        { s with core := { s.core with rsns := rsns', first_reducible := fred' } } := by
  unfold FullMemArenaOut; rfl

private def FullCoreByteNoVals (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i8) c.pLitMark k.lit_mark ⋆ array (t := i8) c.pMark k.mrk

private def FullMemArenaNoVals (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreByteNoVals c s.core ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

private theorem fullMemArenaOut_eq_vals (c : FullCfg) (s : FullState) :
    FullMemArenaOut c s = (array (t := i8) c.pVals s.core.vals ⋆ FullMemArenaNoVals c s) := by
  funext m; apply propext
  unfold FullMemArenaOut FullMemArenaNoVals FullCoreByteArrs FullCoreByteNoVals
  constructor <;> intro hm <;> ecancel

private def FullMemArenaNoHdrTail (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆
  array (t := i32) c.pWstk s.core.wstk ⋆ FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

private theorem fullMemArenaOut_eq_hdrTail (c : FullCfg) (s : FullState) :
    FullMemArenaOut c s =
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullMemArenaNoHdrTail c s) := by
  funext m; apply propext
  unfold FullMemArenaOut FullMemArenaNoHdrTail
  constructor <;> intro hm <;> ecancel

private theorem outHdrTailGet {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((hdrTailWords c s)[i]'(by simpa using hi)) := by
  rw [fullMemArenaOut_eq_hdrTail, sep_assoc] at hm
  have h1 := loadVal_array64 (i := i) (by simp; exact hi) hm
  simpa [BitVec.add_assoc, ← BitVec.ofNat_add] using h1

namespace M6Tactics2a

open scoped M6Tactics1

@[scoped c0_load] theorem out_load_vals_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 64) = some c.pVals := outHdrTailGet 4 (by decide) hm

@[scoped c0_load] theorem out_load_reason_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 88) = some c.pReason := outHdrTailGet 7 (by decide) hm

@[scoped c0_load] theorem out_load_arena_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 112) = some c.pArena := outHdrTailGet 10 (by decide) hm

@[scoped c0_load] theorem out_load_cur_vars {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 776) = some (BitVec.ofNat 64 s.core.cur_vars) :=
  outHdrTailGet 93 (by decide) hm

@[scoped c0_load] theorem out_load_vals {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.vals.length)
    (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat] := by
  rw [fullMemArenaOut_eq_vals, sep_assoc] at hm
  have h1 := loadVal_array (t := i8) (by decide) hi hm
  simpa [Ty.bytes, Ty.size, i8, bv_ofNat_toNat_eq] using h1

@[scoped c0_load] theorem out_load_rsns {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.rsns.length)
    (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i32 (c.pReason + i * 4) = some s.core.rsns[i.toNat] := by
  rw [fullMemArenaOut_eq_rsns, sep_assoc] at hm
  have h1 := loadVal_array (t := i32) (by decide) hi hm
  simp only [Ty.bytes, Ty.size, i32] at h1
  rwa [← bv64_mul4_eq_ofNat i] at h1

@[scoped c0_store] theorem out_store_rsns {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} {v : BitVec 32}
    (hi : i.toNat < s.core.rsns.length) (hm : (FullMemArenaOut c s ⋆ R) m) :
    storeOk m i32 (c.pReason + i * 4) ∧
      (FullMemArenaOut c { s with core := { s.core with rsns := s.core.rsns.set i.toNat v } } ⋆
        R) (storeMem m i32 (c.pReason + i * 4) v) := by
  rw [fullMemArenaOut_eq_rsns, sep_assoc] at hm
  obtain ⟨h1, h2⟩ := store_array (t := i32) v (by decide) hi hm
  simp only [Ty.bytes, Ty.size, i32] at h1 h2
  rw [← bv64_mul4_eq_ofNat i] at h1 h2
  refine ⟨h1, ?_⟩
  rw [fullMemArenaOut_eq_rsns, sep_assoc]
  rwa [show FullMemArenaNoRsns c
      { s with core := { s.core with rsns := s.core.rsns.set i.toNat v } } =
      FullMemArenaNoRsns c s by
    dsimp only [FullMemArenaNoRsns, hdrTailWords, HdrWordField.tailChunk0,
      HdrWordField.tailChunk1, HdrWordField.tailChunk2, HdrWordField.tailChunk3,
      FullCoreByteArrs, FullCoreU32ANoRsns, FullCoreU32B,
      FullScrByteArrs, FullScrU32A, FullScrWksArrs, FullScrMetaArrs]]

@[scoped c0_store] theorem out_store_first_red {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (fr' : BitVec 64) (hm : (FullMemArenaOut c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 480) ∧
      (FullMemArenaOut c { s with core := { s.core with first_reducible := fr' } } ⋆ R)
        (storeMem m i64 (c.hdr + 480) fr') := by
  rw [fullMemArenaOut_eq_hdrTail, sep_assoc] at hm
  obtain ⟨h1, h2⟩ := store_array64 fr' (i := 56) (by simp) hm
  have hoff : c.hdr + 32 + BitVec.ofNat 64 (8 * 56) = c.hdr + 480 := by
    rw [BitVec.add_assoc]; rfl
  refine ⟨hoff ▸ h1, ?_⟩
  rw [fullMemArenaOut_eq_hdrTail, sep_assoc, full_hdr_tail_words_first_red]
  rwa [hoff] at h2

@[scoped c0_load] theorem out_load_arr32 {ptr : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < xs.length)
    (hm : (array (t := i32) ptr xs ⋆ R) m) :
    loadVal m i32 (ptr + i * 4) = some xs[i.toNat] := by
  have h1 := loadVal_array (t := i32) (by decide) hi hm
  simp only [Ty.bytes, Ty.size, i32] at h1; rwa [← bv64_mul4_eq_ofNat i] at h1

@[scoped c0_load] theorem out_load_arena_cap {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 32) = some (BitVec.ofNat 64 c.arena_cap) :=
  outHdrTailGet 0 (by decide) hm

@[scoped c0_load] theorem out_load_scratch_buf {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := outHdrTailGet 111 (by decide) hm

@[scoped c0_load] theorem out_load_scratch_cap {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemArenaOut c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) :=
  outHdrTailGet 112 (by decide) hm

@[scoped c0_store] theorem out_store_arr32 {ptr : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} {v : BitVec 32} (hi : i.toNat < xs.length)
    (hm : (array (t := i32) ptr xs ⋆ R) m) :
    storeOk m i32 (ptr + i * 4) ∧
      (array (t := i32) ptr (xs.set i.toNat v) ⋆ R) (storeMem m i32 (ptr + i * 4) v) := by
  obtain ⟨h1, h2⟩ := store_array (t := i32) v (by decide) hi hm
  simp only [Ty.bytes, Ty.size, i32] at h1 h2
  rw [← bv64_mul4_eq_ofNat i] at h1 h2; exact ⟨h1, h2⟩

scoped elab "m6_to_group_strip" : tactic => do
  for _ in [:100] do
    let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]))
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars
      (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then break
    let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| repeat m6_strip))
    if !(← LeanQbe.T.C0Step.stepOnce) then break

end M6Tactics2a

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
