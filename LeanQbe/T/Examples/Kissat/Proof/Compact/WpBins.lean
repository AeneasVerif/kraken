/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Compact.Inv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical WP Proof for `Kissat.Src.Compact.full_compact_bins`

Proves `Func.wp` against `fullCompactBinsSpec` (`Proof.Compact.Spec`) on flat `CanonicalEnv`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Compact
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem bv64_shl1_toNat {v : BitVec 64} (h : 2 * v.toNat < 2 ^ 64) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  bv_omega

private theorem bv64_shr1_toNat {v : BitVec 64} :
    (v >>> (1 : Nat)).toNat = v.toNat / 2 := by
  bv_omega

namespace WpBinsBvC0
@[scoped bv_c0] theorem bv64_shl2_nat (x : BitVec 64) :
    (x <<< (2 : Nat)).toNat = (4 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
end WpBinsBvC0
open scoped WpBinsBvC0

private def binsPostPExpr (h l off64 end64 keptP q wvecP wstkP : Val i64)
    (J1 : Cont [i64, i64]) : Expr Val Cont [] :=
  Expr.group (sig := [[i64]]) (fun Js_3 =>
  Blocks.cons (fun p_25 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_25.fst, Arg.var end64, ())⟩
    fun p_26 =>
  Expr.jnz (Arg.var p_26.fst)
  (Expr.let_ ⟨OpCode.mul i64, (Arg.var p_25.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstkP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_25.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js_3.fst (Arg.var p.fst, ())))
  (Expr.group (sig := [[]]) (fun _Js_4 =>
  Blocks.cons (fun _ =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 464, ())⟩ fun p_28 =>
  Expr.load i64 (Arg.var p_28.fst) fun ld =>
  Expr.let_ ⟨OpCode.sub i64, (Arg.var end64, Arg.var q, ())⟩ fun p_29 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var ld, Arg.var p_29.fst, ())⟩ fun p_30 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 464, ())⟩ fun p =>
  Expr.store (Arg.var p_30.fst) (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var l, Arg.imm 1, ())⟩ fun p =>
  Expr.jump J1 (Arg.var keptP, Arg.var p.fst, ()))) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var q, Arg.var off64,
    ())⟩ fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var l, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var l, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
  (Expr.jump Js.fst ())))
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var l, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.sub i64, (Arg.var q, Arg.var off64, ())⟩ fun p_27 =>
  Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var p_27.fst, ())⟩ fun p_28 =>
  Expr.store (Arg.var p_28.fst) (Arg.var p.fst)
  (Expr.jump Js.fst ())))) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.var q, ())

private def binsPLoopExpr (h kept l off64 end64 wvecP wstkP mapP valsP nlits : Val i64)
    (keep_l : Val .bool) (J1 : Cont [i64, i64]) : Expr Val Cont [] :=
  Expr.group (sig := [[i64, i64, i64]]) (fun Js_2 =>
  Blocks.cons (fun p_23 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_23.snd.fst, Arg.var end64,
    ())⟩ fun p_24 =>
  Expr.jnz (Arg.var p_24.fst)
  (Expr.let_ ⟨OpCode.mul i64, (Arg.var p_23.snd.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstkP, Arg.var p.fst, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld_6 =>
  Expr.group (sig := [[i64, i64, i64]]) (fun _Js =>
  Blocks.cons (fun p =>
  Expr.jump Js_2.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
    Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var ld_6, Arg.imm 2147483648, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p.fst, Arg.imm 0, ())⟩ fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.and i32, (Arg.var ld_6, Arg.imm 2147483647, ())⟩ fun p =>
  Expr.group (sig := [[i64, i64]]) (fun _Js_3 =>
  Blocks.cons (fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_23.snd.fst, Arg.imm 1, ())⟩ fun p_25 =>
  Expr.jump Js.fst (Arg.var p.fst, Arg.var p_25.fst, Arg.var p.snd.fst, ())) Blocks.nil)
    fun Js =>
  Expr.jnz (Arg.var keep_l)
  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p_25 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_25.fst, Arg.var nlits, ())⟩
    fun p_26 =>
  Expr.jnz (Arg.var p_26.fst)
  (Expr.let_ ⟨OpCode.lshr i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p_27 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p_27.fst, ())⟩ fun p_28 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_28.fst, Arg.imm 4, ())⟩ fun p_29 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var mapP, Arg.var p_29.fst, ())⟩ fun p_30 =>
  Expr.load i32 (Arg.var p_30.fst) fun ld_7 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var ld_7, Arg.imm 4294967295, ())⟩
    fun p_31 =>
  Expr.jnz (Arg.var p_31.fst)
  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p_32 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var valsP, Arg.var p_32.fst, ())⟩ fun p_33 =>
  Expr.load i8 (Arg.var p_33.fst) fun ld =>
  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p_34 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld, ())⟩ fun p_35 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p_34.fst, ())⟩ fun p_36 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var p_35.fst, Arg.var p_36.fst, ())⟩
    fun p_37 =>
  Expr.jnz (Arg.var p_37.fst)
  (Expr.let_ ⟨OpCode.lshr i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p_38 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p_38.fst, ())⟩ fun p_39 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_39.fst, Arg.imm 4, ())⟩ fun p_40 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var mapP, Arg.var p_40.fst, ())⟩ fun p_41 =>
  Expr.load i32 (Arg.var p_41.fst) fun ld =>
  Expr.let_ ⟨OpCode.shl i32, (Arg.var ld, Arg.imm 1, ())⟩ fun p_42 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var p_42.fst, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_23.snd.snd.fst, Arg.imm 4, ())⟩ fun p_43 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstkP, Arg.var p_43.fst, ())⟩ fun p_44 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var p.fst, Arg.imm 2147483647, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var p.fst, Arg.imm 2147483648, ())⟩ fun p =>
  Expr.store (Arg.var p.fst) (Arg.var p_44.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_23.snd.snd.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_23.fst, Arg.imm 1, ())⟩ fun p_45 =>
  Expr.jump Js.fst (Arg.var p_45.fst, Arg.var p.fst, ())))
  (Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p_23.snd.snd.fst, ())))
  (Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p_23.snd.snd.fst, ())))
  (Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p_23.snd.snd.fst, ())))
  (Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p_23.snd.snd.fst, ())))
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_23.snd.fst, Arg.imm 2, ())⟩ fun p =>
  Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p.fst, Arg.var p_23.snd.snd.fst, ())))
    ((binsPostPExpr h l off64 end64 p_23.fst p_23.snd.snd.fst wvecP wstkP J1))) Blocks.nil)
    fun Js =>
  Expr.jump Js.fst (Arg.var kept, Arg.var off64, Arg.var off64, ())

private def binsTailExpr (h old_cv ncv kept mapP wvecP : Val i64) :
    Expr Val Cont [] :=
  Expr.store (t := i64) (Arg.var (kept >>> (1 : Nat))) (Arg.var (h + (504 : BitVec 64)))
  (Expr.group (sig := [[i64]]) (fun Js =>
  Blocks.cons (fun p_12 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_12.fst, Arg.var old_cv, ())⟩
    fun p_13 =>
  Expr.jnz (Arg.var p_13.fst)
  (Expr.let_ ⟨OpCode.mul i64, (Arg.var p_12.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var mapP, Arg.var p.fst, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld =>
  Expr.group (sig := [[]]) (fun _Js_1 =>
  Blocks.cons (fun _ =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_12.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var ld, Arg.imm 4294967295, ())⟩ fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var p.fst, Arg.var p_12.fst, ())⟩
    fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 2, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var p_12.fst, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld, ())⟩ fun p_14 =>
  Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 2, ())⟩ fun p_15 =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var p_14.fst, Arg.var p_15.fst, ())⟩ fun p_16 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_16.fst, Arg.imm 4, ())⟩ fun p_17 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_17.fst, ())⟩ fun p_18 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p_19 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_19.fst, ())⟩ fun p_20 =>
  Expr.load i32 (Arg.var p_20.fst) fun ld =>
  Expr.store (Arg.var ld) (Arg.var p_18.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_16.fst, Arg.imm 1, ())⟩ fun p_21 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_21.fst, Arg.imm 4, ())⟩ fun p_22 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_22.fst, ())⟩ fun p_23 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p_24 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_24.fst, Arg.imm 4, ())⟩ fun p_25 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_25.fst, ())⟩ fun p_26 =>
  Expr.load i32 (Arg.var p_26.fst) fun ld =>
  Expr.store (Arg.var ld) (Arg.var p_23.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_16.fst, Arg.imm 2, ())⟩ fun p_27 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_27.fst, Arg.imm 4, ())⟩ fun p_28 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_28.fst, ())⟩ fun p_29 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 2, ())⟩ fun p_30 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_30.fst, Arg.imm 4, ())⟩ fun p_31 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_31.fst, ())⟩ fun p_32 =>
  Expr.load i32 (Arg.var p_32.fst) fun ld =>
  Expr.store (Arg.var ld) (Arg.var p_29.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_16.fst, Arg.imm 3, ())⟩ fun p_33 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_33.fst, Arg.imm 4, ())⟩ fun p_34 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_34.fst, ())⟩ fun p_35 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 3, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld =>
  Expr.store (Arg.var ld) (Arg.var p_35.fst)
  (Expr.jump Js.fst ())))))
  (Expr.jump Js.fst ()))
  (Expr.jump Js.fst ()))
  (Expr.group (sig := [[i64]]) (fun Js =>
  Blocks.cons (fun p_14 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_14.fst, Arg.var old_cv, ())⟩
    fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 2, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var p_14.fst, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p_15 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_15.fst, ())⟩ fun p_16 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_16.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p_17 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_17.fst, Arg.imm 4, ())⟩ fun p_18 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_18.fst, ())⟩ fun p_19 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_19.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 2, ())⟩ fun p_20 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_20.fst, Arg.imm 4, ())⟩ fun p_21 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_21.fst, ())⟩ fun p_22 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_22.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 3, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_14.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js.fst (Arg.var p.fst, ()))))))
  (Expr.ret ())) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.var ncv, ()))) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.imm 0, ()))

private theorem full_compact_bins_post_p {Γ : Env} {Q : Post []} {X : XPost}
    {J1 : Cont [i64, i64]} {c : FullCfg} {F_cur : List (List Nat)} {ncv : BitVec 64}
    {inv : List (BitVec 32)} {s : FullState} {kL : FullCoreState} {R : Mem 64 → Prop}
    {old_cv l keptP q off64 end64 : BitVec 64} {off0 sz0 : Nat}
    {wvecL wstkL wstkP : List (BitVec 32)} {wuL : BitVec 64} {mP : Mem 64}
    (hkL : kL = { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL })
    (hoff_def : off0 = fullWatchOffCore kL l.toNat)
    (hsz_def : sz0 = fullWatchSizeCore kL l.toNat)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hwc_lt : c.wcap < 2 * 2 ^ 28) (hmax_lt : c.max_vars < 2 * 2 ^ 28)
    (hold : s.core.cur_vars = old_cv.toNat) (hckL : FullCoreState.LengthsOk c kL)
    (hlayL : WatchStackLayout kL) (hwvL : wvecL.length = 4 * c.max_vars)
    (hl_lt : l.toNat < 2 * old_cv.toNat) (hoff64 : off64.toNat = off0)
    (hend64 : end64.toNat = off0 + sz0) (hbd_l : off0 + sz0 ≤ kL.wlen)
    (hsz_pos : 0 < sz0) (hq_ge : off0 ≤ q.toNat) (hq_le : q.toNat ≤ off0 + sz0)
    (hkept_end : keptP.toNat ≤ (l.toNat + 1) * c.wcap) (hwsP : wstkP.length = c.wcap)
    (houtP : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstkP[i]? = wstkL[i]?)
    (hpreP : CompactPreBinSliceOk ncv.toNat inv F_cur { kL with wstk := wstkP }
      l.toNat off0 (q.toNat - off0))
    (hpreL : ∀ ol < l.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur kL ol
      (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hwatL : ∀ ol, l.toNat ≤ ol → ol < 2 * old_cv.toNat →
      WatchSliceOk F_cur kL ol (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hmP : (FullMem c { s with core := { kL with wstk := wstkP } } ⋆ R) mP)
    (hLoop1 : ∀ (ys : Tup Val [i64, i64]) (m' : Mem 64),
      2 * old_cv.toNat - ys.2.1.toNat < 2 * old_cv.toNat - l.toNat →
      (ys.2.1.toNat ≤ 2 * old_cv.toNat ∧ ys.1.toNat ≤ ys.2.1.toNat * c.wcap ∧
        ∃ (wvecL wstkL : List (BitVec 32)) (wuL : BitVec 64),
          wvecL.length = 4 * c.max_vars ∧ wstkL.length = c.wcap ∧
          let k1 : FullCoreState := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL }
          WatchStackLayout k1 ∧
          (∀ ol < ys.2.1.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur k1 ol
            (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) ∧
          (∀ ol, ys.2.1.toNat ≤ ol → ol < 2 * old_cv.toNat →
            WatchSliceOk F_cur k1 ol (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) ∧
          (FullMem c { s with core := k1 } ⋆ R) m') →
      J1 ys m') :
    wp Γ Q X (binsPostPExpr c.hdr l off64 end64 keptP q c.pWvec c.pWstk J1) mP := by
  subst hoff_def; subst hsz_def
  let off0 := fullWatchOffCore kL l.toNat
  let sz0 := fullWatchSizeCore kL l.toNat
  have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := cmp_bv64_add1 (by omega)
  have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
  have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
    rw [cmp_bv64_add1 (by rw [h2l_eq]; omega), h2l_eq]
  have h2l_lt : 2 * l.toNat < wvecL.length := by omega
  have h2l1_lt : 2 * l.toNat + 1 < wvecL.length := by omega
  have h2l_lt' : (l <<< (1 : Nat)).toNat < wvecL.length := by rw [h2l_eq]; omega
  have h2l1_lt' : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wvecL.length := by
    rw [h2l1_eq]; omega
  have hbd_cap : off0 + sz0 ≤ c.wcap := by have := hckL.wlen_le; omega
  have hend_bv : end64 = BitVec.ofNat 64 (off0 + sz0) :=
    BitVec.eq_of_toNat_eq (by rw [hend64, bv64_ofNat_toNat (by omega)])
  unfold binsPostPExpr
  c0_hsteps
  refine wp_loop_inv
    (fun (k, ()) mK =>
      q.toNat ≤ k.toNat ∧ k.toNat ≤ off0 + sz0 ∧
      ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
        (∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstkK[i]? = wstkL[i]?) ∧
        (∀ i, off0 ≤ i → i < q.toNat → wstkK[i]? = wstkP[i]?) ∧
        (FullMem c { s with core := { kL with wstk := wstkK } } ⋆ R) mK)
    (fun (k, ()) _ => off0 + sz0 - k.toNat)
    (fun Jk hLoopK => ?_) ?_
  · c0_hsteps
    exact hLoopK (q, ()) mP ⟨Nat.le_refl _, hq_le, wstkP, hwsP, houtP, fun _ _ _ => rfl, hmP⟩
  · rintro Jk ⟨k, ⟨⟩⟩ mK ⟨hqk, hke, wstkK, hwsK, houtK, hpreK, hmK⟩ hLoopK
    c0_hsplit
    · have hk_lt : k.toNat < off0 + sz0 := by
        have h1 : k.toNat < end64.toNat := by c0_bound
        omega
      have hk_ws : k.toNat < wstkK.length := by omega
      have hk1_eq : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := cmp_bv64_add1 (by omega)
      c0_hsteps
      refine hLoopK (k + (1 : BitVec 64), ()) _ (by dsimp only; rw [hk1_eq]; omega)
        ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega, wstkK.set k.toNat 0xFFFFFFFF#32,
         by simp [hwsK], fun i hi => by
           rw [List.getElem?_set_ne (by omega)]; exact houtK i hi,
         fun i h1 h2 => by
           rw [List.getElem?_set_ne (by omega)]; exact hpreK i h1 h2,
         compactMem_cast (by assumption) rfl⟩
    · have hpreK_ok : CompactPreBinSliceOk ncv.toNat inv F_cur { kL with wstk := wstkK }
          l.toNat (fullWatchOffCore kL l.toNat) (q.toNat - fullWatchOffCore kL l.toNat) :=
        hpreP.relocate (k' := { kL with wstk := wstkK })
          (fun idx hi => hpreK (fullWatchOffCore kL l.toNat + idx) (by omega) (by omega))
      have hl_cv : l.toNat < 2 * kL.cur_vars := by rw [hkL]; exact hold ▸ hl_lt
      have houtK' : ∀ i,
          i < fullWatchOffCore kL l.toNat ∨
            fullWatchOffCore kL l.toNat + fullWatchSizeCore kL l.toNat ≤ i →
          wstkK[i]? = kL.wstk[i]? := fun i hi => by rw [hkL]; exact houtK i hi
      have hfin := compactBins_finish_lit (c := c) (ncv := ncv.toNat) (inv := inv)
        (F_cur := F_cur) hckL hlayL hl_cv hq_ge hq_le hwsK houtK' hpreK_ok
        (wu' := wuL + (BitVec.ofNat 64 (fullWatchOffCore kL l.toNat +
          fullWatchSizeCore kL l.toNat) - q))
        (nb' := kL.num_binary)
      let wvecG : List (BitVec 32) :=
        if q.toNat = off0 then (kL.wvec.set (2 * l.toNat) 0#32).set (2 * l.toNat + 1) 0#32
        else kL.wvec.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - off0))
      let wuG : BitVec 64 := wuL + (BitVec.ofNat 64 (off0 + sz0) - q)
      let kG : FullCoreState :=
        { kL with wvec := wvecG, wstk := wstkK, wusable := wuG, num_binary := kL.num_binary }
      have hkG_s : kG = { s.core with wvec := wvecG, wstk := wstkK, wusable := wuG } := by
        dsimp only [kG]; rw [hkL]
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun _ mG =>
          (FullMem c { s with core := { kL with wvec := wvecG, wstk := wstkK } } ⋆ R) mG)
        ?_ ?_
      · rintro _ ⟨⟩ mG hmG
        c0_hsteps
        refine hLoop1 (keptP, l + (1 : BitVec 64), ()) _ (by dsimp only; rw [hl1_eq]; omega)
          ⟨by rw [hl1_eq]; omega, by rw [hl1_eq]; exact hkept_end,
           wvecG, wstkK, wuG, hfin.1.wvec_len, hwsK, hkG_s ▸ hfin.2.1, fun ol hol => ?_,
           fun ol hlo hol => ?_,
           compactMem_cast (by assumption)
             (by rw [← hkG_s]; dsimp only [kG, wuG]; rw [hkL, hend_bv])⟩
        · rw [hl1_eq] at hol
          by_cases hol_eq : ol = l.toNat
          · subst hol_eq; rw [← hkG_s]; exact hfin.2.2.2
          · have hol_cv : ol < 2 * kL.cur_vars := by
              rw [hkL]; change ol < 2 * s.core.cur_vars; omega
            obtain ⟨hs_eq, hws_eq⟩ := hfin.2.2.1 ol hol_cv hol_eq
            rw [← hkG_s]
            change CompactPreBinSliceOk ncv.toNat inv F_cur kG ol
              (fullWatchOffCore kG ol) (fullWatchSizeCore kG ol)
            rw [hs_eq.1, hs_eq.2]
            exact CompactPreBinSliceOk.relocate (k := kL)
              (fun idx hidx => hws_eq idx hidx) (hpreL ol (by omega))
        · rw [hl1_eq] at hlo
          have hol_cv : ol < 2 * kL.cur_vars := by rw [hkL]; change ol < 2 * s.core.cur_vars; omega
          obtain ⟨hs_eq, hws_eq⟩ := hfin.2.2.1 ol hol_cv (by omega)
          rw [← hkG_s]
          change WatchSliceOk F_cur kG ol (fullWatchOffCore kG ol) (fullWatchSizeCore kG ol)
          rw [hs_eq.1, hs_eq.2]
          exact watchSliceOk_relocate_cmp (k := kL) (k' := kG)
            (p' := fullWatchOffCore kL ol) (by simp [kG]) (by simp [kG]) (by simp [kG])
            (fun idx hi => hws_eq idx hi) (hwatL ol (by omega) hol)
      · intro Jg hJg
        clear hLoop1 hpreL hwatL hlayL hckL hfin hpreK_ok hLoopK Jk hpreK houtK hpreP hkG_s
        have h2l_st : (l <<< (1 : Nat)).toNat <
            ({ s with core := { kL with wstk := wstkK } } : FullState).core.wvec.length := by
          change (l <<< (1 : Nat)).toNat < kL.wvec.length; rw [hkL]; exact h2l_lt'
        have h2l1_st : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
            ({ s with core := { kL with wstk := wstkK } } : FullState).core.wvec.length := by
          change ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < kL.wvec.length
          rw [hkL]; exact h2l1_lt'
        let kL0 := { kL with wvec := kL.wvec.set (l <<< (1 : Nat)).toNat 0, wstk := wstkK }
        have h2l1_st_set : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
            ({ s with core := kL0 } : FullState).core.wvec.length := by
          change _ < (kL.wvec.set _ 0).length; rw [List.length_set, hkL]; exact h2l1_lt'
        c0_hsplit
        · have hq_off : q.toNat = off0 := by
            have hbv : q = off64 := by c0_bound
            rw [hbv, hoff64]
          c0_hsteps
          exact hJg () _ (compactMem_cast (by assumption) (by
            dsimp only [wvecG]; rw [ite_eq_left hq_off, h2l_eq, h2l1_eq]; rfl))
        · have hq_ne : q.toNat ≠ off0 := by
            have hbv : q ≠ off64 := by c0_bound
            intro heq; apply hbv; apply BitVec.eq_of_toNat_eq; rw [hoff64, heq]
          have hqsub64 : (q - off64).toNat = q.toNat - off0 := by
            rw [BitVec.toNat_sub, hoff64,
              show 2 ^ 64 - off0 + q.toNat = (q.toNat - off0) + 2 ^ 64 by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hq_diff : q.toNat - off0 < 2 ^ 32 := by omega
          have hsub32 : (q - off64).setWidth 32 = BitVec.ofNat 32 (q.toNat - off0) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, hqsub64, bv32_ofNat_toNat hq_diff,
              Nat.mod_eq_of_lt hq_diff]
          c0_hsteps
          exact hJg () _ (compactMem_cast (by assumption) (by
            dsimp only [wvecG]; rw [ite_eq_right hq_ne, h2l1_eq, hsub32]))

private theorem compactPreBinSliceOk_append_bin {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {olit off off' rem : Nat}
    {w0 : BitVec 32} (h : CompactPreBinSliceOk ncv inv F_cur k olit off rem)
    (hpre : ∀ idx < rem, k'.wstk[off' + idx]? = k.wstk[off + idx]?)
    (hw0 : k'.wstk[off' + rem]? = some w0)
    (hfl : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * ncv)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [olit, compactUnmapLit inv (w0 &&& 0x7FFFFFFF#32).toNat])) :
    CompactPreBinSliceOk ncv inv F_cur k' olit off' (rem + 1) := by
  induction h generalizing off' with
  | empty =>
    rw [Nat.add_zero] at hw0
    exact .bin hw0 hfl hne hlt hent .empty
  | @bin p rem0 w1 hp hfl1 hne1 hlt1 hent1 _ ih =>
    have hp0 : k'.wstk[off']? = some w1 := by simpa using (hpre 0 (by omega)).trans hp
    have hw0' : k'.wstk[(off' + 1) + rem0]? = some w0 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0
    have hpre' : ∀ idx < rem0, k'.wstk[(off' + 1) + idx]? = k.wstk[(p + 1) + idx]? := by
      intro idx hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpre (idx + 1) (by omega)
    exact .bin hp0 hfl1 hne1 hlt1 hent1 (ih hpre' hw0')

private theorem full_compact_bins_ploop {Γ : Env} {Q : Post []} {X : XPost}
    {J1 : Cont [i64, i64]} {c : FullCfg} {F_cur : List (List Nat)} {ncv : BitVec 64}
    {inv : List (BitVec 32)} {s : FullState} {kL : FullCoreState} {R : Mem 64 → Prop}
    {old_cv kept l off64 end64 nlits : BitVec 64} {keep_l : Bool} {off0 sz0 : Nat}
    {wvecL wstkL : List (BitVec 32)} {wuL : BitVec 64} {mL : Mem 64}
    (hkL : kL = { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL })
    (hoff_def : off0 = fullWatchOffCore kL l.toNat)
    (hsz_def : sz0 = fullWatchSizeCore kL l.toNat)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hv_len : s.core.vals.length = 2 * c.max_vars)
    (hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hwc_lt : c.wcap < 2 * 2 ^ 28) (hmax_lt : c.max_vars < 2 * 2 ^ 28)
    (hkl_mul_lt : 2 * c.max_vars * c.wcap < 2 ^ 60)
    (hold : s.core.cur_vars = old_cv.toNat) (_hncv_le : ncv.toNat ≤ old_cv.toNat)
    (hbij : CompactBijOk old_cv.toNat ncv.toNat s.core.vals s.scratch.work_stk1 inv)
    (hckL : FullCoreState.LengthsOk c kL) (hlayL : WatchStackLayout kL)
    (hwvL : wvecL.length = 4 * c.max_vars) (hwsL : wstkL.length = c.wcap)
    (hl_lt : l.toNat < 2 * old_cv.toNat) (hkept_le : kept.toNat ≤ l.toNat * c.wcap)
    (hoff64 : off64.toNat = off0) (hend64 : end64.toNat = off0 + sz0)
    (hnlits : nlits.toNat = 2 * old_cv.toNat)
    (hbd_l : off0 + sz0 ≤ kL.wlen) (hsz_pos : 0 < sz0)
    (hslice_l : WatchSliceOk F_cur kL l.toNat off0 sz0)
    (hpreL : ∀ ol < l.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur kL ol
      (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hwatL : ∀ ol, l.toNat ≤ ol → ol < 2 * old_cv.toNat →
      WatchSliceOk F_cur kL ol (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hmL : (FullMem c { s with core := kL } ⋆ R) mL)
    (hLoop1 : ∀ (ys : Tup Val [i64, i64]) (m' : Mem 64),
      2 * old_cv.toNat - ys.2.1.toNat < 2 * old_cv.toNat - l.toNat →
      (ys.2.1.toNat ≤ 2 * old_cv.toNat ∧ ys.1.toNat ≤ ys.2.1.toNat * c.wcap ∧
        ∃ (wvecL wstkL : List (BitVec 32)) (wuL : BitVec 64),
          wvecL.length = 4 * c.max_vars ∧ wstkL.length = c.wcap ∧
          let k1 : FullCoreState := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL }
          WatchStackLayout k1 ∧
          (∀ ol < ys.2.1.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur k1 ol
            (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) ∧
          (∀ ol, ys.2.1.toNat ≤ ol → ol < 2 * old_cv.toNat →
            WatchSliceOk F_cur k1 ol (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) ∧
          (FullMem c { s with core := k1 } ⋆ R) m') →
      J1 ys m') :
    wp Γ Q X (binsPLoopExpr c.hdr kept l off64 end64 c.pWvec c.pWstk c.pWorkStk1 c.pVals nlits
      keep_l J1) mL := by
  have hbd_cap : off0 + sz0 ≤ c.wcap := by have := hckL.wlen_le; omega
  have hkL_wstk : ({ kL with wstk := wstkL } : FullCoreState) = kL := by rw [hkL]
  unfold binsPLoopExpr
  refine wp_loop_inv
    (fun (keptP, p, q, ()) mP =>
      off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧
      keptP.toNat ≤ l.toNat * c.wcap + (q.toNat - off0) ∧
      ∃ wstkP : List (BitVec 32), wstkP.length = c.wcap ∧
        (∀ i, (i < off0 ∨ p.toNat ≤ i) → wstkP[i]? = wstkL[i]?) ∧
        CompactPreBinSliceOk ncv.toNat inv F_cur { kL with wstk := wstkP } l.toNat
          off0 (q.toNat - off0) ∧
        WatchSliceOk F_cur { kL with wstk := wstkP } l.toNat
          p.toNat (off0 + sz0 - p.toNat) ∧
        (FullMem c { s with core := { kL with wstk := wstkP } } ⋆ R) mP)
    (fun (_, p, _, ()) _ => off0 + sz0 - p.toNat)
    (fun Jp hLoopP => ?_) ?_
  · c0_hsteps
    refine hLoopP (kept, off64, off64, ()) mL
      ⟨by rw [hoff64]; exact Nat.le_refl _, by exact Nat.le_refl _,
       by rw [hoff64]; omega, by rw [hoff64, Nat.sub_self, Nat.add_zero]; exact hkept_le,
       wstkL, hwsL, fun _ _ => rfl, by rw [hoff64, Nat.sub_self]; exact .empty,
       by rw [hoff64, Nat.add_sub_cancel_left, hkL_wstk]; exact hslice_l,
       by rw [hkL_wstk]; exact hmL⟩
  · rintro Jp ⟨keptP, p, q, ⟨⟩⟩ mP
      ⟨hq_ge, hqp, hpe, hkp_le, wstkP, hwsP, houtP, hpreP, hremP, hmP⟩ hLoopP
    have hkp_bd : keptP.toNat ≤ (l.toNat + 1) * c.wcap := by
      have hq1 : q.toNat - off0 ≤ sz0 := by omega
      have hq2 : sz0 ≤ c.wcap := by omega
      rw [Nat.add_mul, Nat.one_mul]; omega
    c0_hsplit
    · clear hLoop1 J1 hpreL hwatL hlayL hckL
      have hp_lt : p.toNat < off0 + sz0 := by
        have h1 : p.toNat < end64.toNat := by c0_bound
        omega
      have hp_wstk : p.toNat < wstkP.length := by omega
      let w0 := wstkP[p.toNat]'hp_wstk
      have hw0_some : wstkP[p.toNat]? = some w0 := List.getElem?_eq_getElem hp_wstk
      have hstep := watchSliceOk_step hremP (by omega) hw0_some
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsplit
      · have hbin0 : (w0 &&& 0x80000000#32) ≠ 0#32 := by c0_bound
        have ⟨_, _, hent, htail⟩ := hstep.1 hbin0
        have hrem' : WatchSliceOk F_cur { kL with wstk := wstkP } l.toNat
            (p.toNat + 1) (off0 + sz0 - (p.toNat + 1)) := by
          simpa [Nat.sub_sub] using htail
        have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := cmp_bv64_add1 (by omega)
        let ot := w0 &&& 0x7FFFFFFF#32
        c0_hsteps_nogrp
        refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
        c0_hsplit
        · c0_hsplit
          · have hot_lt : ot.toNat < 2 * old_cv.toNat := by
              have h1 : ot.toNat < nlits.toNat := by dsimp only [ot, w0]; c0_bound
              omega
            have hot_vals : ot.toNat < s.core.vals.length := by omega
            have hot_vals_64 :
                (((wstkP[p.toNat]'hp_wstk &&& 0x7FFFFFFF#32)).setWidth 64).toNat <
                  ({ s with core := { kL with wstk := wstkP } } : FullState).core.vals.length :=
              by change (ot.setWidth 64).toNat < kL.vals.length
                 rw [hkL, zext_toNat _ (by decide)]; exact hot_vals
            have hot_ws1 : (ot >>> (1 : Nat)).toNat < s.scratch.work_stk1.length := by
              rw [bv32_lshr_1]; omega
            have hot_ws1_64 :
                ((ot >>> (1 : Nat)).setWidth 64).toNat < s.scratch.work_stk1.length := by
              rw [zext_toNat _ (by decide), bv32_lshr_1]; omega
            c0_hsplit
            · have hneq : (s.scratch.work_stk1[((ot >>> (1 : Nat)).setWidth 64).toNat]'
                    hot_ws1_64) ≠ 0xFFFFFFFF#32 := by dsimp only [ot, w0]; c0_bound
              have hmap_ot : s.scratch.work_stk1[ot.toNat / 2]? ≠ some 0xFFFFFFFF#32 := by
                intro heq
                rw [List.getElem?_eq_getElem
                  (by omega : ot.toNat / 2 < s.scratch.work_stk1.length)] at heq
                have hidx : ((ot >>> (1 : Nat)).setWidth 64).toNat = ot.toNat / 2 := by
                  rw [zext_toNat _ (by decide), bv32_lshr_1]
                simp only [hidx] at hneq
                exact hneq (Option.some.inj heq)
              c0_hsplit
              · rcases hbij.map_ok (ot.toNat / 2) (by omega) with
                    hff | ⟨nv', hnv', _, _, hm_ot, hi_ot⟩
                · exact absurd hff hmap_ot
                · have hnv'_30 : nv' < 2 ^ 30 := by omega
                  have hpack := cmp_bv32_lit_pack hnv'_30 ot
                  have hnot_lt : ((BitVec.ofNat 32 nv' <<< 1#32) ||| (ot &&& 1#32)).toNat <
                      0x7FFFFFFF := by rw [hpack]; omega
                  have hbw := cmp_bv32_bin_word_props hnot_lt
                  let wnew := (((BitVec.ofNat 32 nv' <<< 1#32) ||| (ot &&& 1#32)) &&&
                    0x7FFFFFFF#32) ||| 0x80000000#32
                  have hq_wstk : q.toNat < wstkP.length := by omega
                  have hq1_eq : (q + (1 : BitVec 64)).toNat = q.toNat + 1 :=
                    cmp_bv64_add1 (by omega)
                  have hkp1_eq : (keptP + (1 : BitVec 64)).toNat = keptP.toNat + 1 := by
                    have : keptP.toNat + 1 < 2 ^ 64 := by
                      have : (l.toNat + 1) * c.wcap ≤ 2 * c.max_vars * c.wcap :=
                        Nat.mul_le_mul_right _ (by omega)
                      omega
                    exact cmp_bv64_add1 this
                  let wstkP' := wstkP.set q.toNat wnew
                  have hun : compactUnmapLit inv (wnew &&& 0x7FFFFFFF#32).toNat = ot.toNat := by
                    rw [hbw.2.2, hpack]
                    rw [compactUnmapLit_pair (ov := ot.toNat / 2)
                      (by rw [hi_ot, Option.getD_some, bv32_ofNat_toNat (by omega)])
                      (Nat.mod_lt _ (by decide))]
                    omega
                  have hpre' : CompactPreBinSliceOk ncv.toNat inv F_cur
                      { kL with wstk := wstkP' } l.toNat off0 (q.toNat + 1 - off0) := by
                    rw [show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
                    exact compactPreBinSliceOk_append_bin hpreP
                      (fun idx hi => by dsimp only [wstkP']; rw [List.getElem?_set_ne (by omega)])
                      (by dsimp only [wstkP']
                          rw [show off0 + (q.toNat - off0) = q.toNat by omega,
                            List.getElem?_set_self hq_wstk])
                      hbw.1 hbw.2.1 (by rw [hbw.2.2, hpack]; omega) (hun ▸ hent)
                  have hrem_set : WatchSliceOk F_cur { kL with wstk := wstkP' } l.toNat
                      (p.toNat + 1) (off0 + sz0 - (p.toNat + 1)) := by
                    refine watchSliceOk_relocate_cmp (k := { kL with wstk := wstkP })
                      (p := p.toNat + 1) (p' := p.toNat + 1) rfl rfl rfl ?_ hrem'
                    intro idx _; dsimp only [wstkP']; rw [List.getElem?_set_ne (by omega)]
                  c0_hsteps
                  refine hLoopP (keptP + (1 : BitVec 64), p + (1 : BitVec 64),
                      q + (1 : BitVec 64), ()) _ (by dsimp only; rw [hp1_eq]; omega)
                    ⟨by rw [hq1_eq]; omega, by rw [hq1_eq, hp1_eq]; omega,
                     by rw [hp1_eq]; omega, by rw [hkp1_eq, hq1_eq]; omega,
                     wstkP', by simp [wstkP', hwsP], fun i hi => ?_,
                     by rw [hq1_eq]; exact hpre', by rw [hp1_eq]; exact hrem_set,
                     compactMem_cast (by assumption) (by
                       dsimp only [wstkP', wnew, ot]
                       refine congrArg (fun x : BitVec 32 =>
                         ({ core := { kL with wstk := (wstkP.set q.toNat
                              (((x <<< 1#32 ||| (w0 &&& 0x7FFFFFFF#32) &&& 1#32) &&&
                                0x7FFFFFFF#32) ||| 0x80000000#32)) },
                            scratch := s.scratch } : FullState)) ?_
                       rw [← Option.some_inj]
                       change some (s.scratch.work_stk1[((ot >>> (1 : Nat)).setWidth
                         64).toNat]'hot_ws1_64) = some (BitVec.ofNat 32 nv')
                       rw [← List.getElem?_eq_getElem hot_ws1_64, zext_toNat _ (by decide),
                         bv32_lshr_1]
                       exact hm_ot)⟩
                  dsimp only [wstkP']
                  rw [List.getElem?_set_ne (by rw [hp1_eq] at hi; omega)]
                  exact houtP i
                    (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega))
              · c0_hsteps
                refine hLoopP (keptP, p + (1 : BitVec 64), q, ()) mP
                  (by dsimp only; rw [hp1_eq]; omega)
                  ⟨hq_ge, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hkp_le,
                   wstkP, hwsP, fun i hi => houtP i
                     (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega)),
                   hpreP, by rw [hp1_eq]; exact hrem', hmP⟩
            · c0_hsteps
              refine hLoopP (keptP, p + (1 : BitVec 64), q, ()) mP
                (by dsimp only; rw [hp1_eq]; omega)
                ⟨hq_ge, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hkp_le,
                 wstkP, hwsP, fun i hi => houtP i
                   (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega)),
                 hpreP, by rw [hp1_eq]; exact hrem', hmP⟩
          · c0_hsteps
            refine hLoopP (keptP, p + (1 : BitVec 64), q, ()) mP
              (by dsimp only; rw [hp1_eq]; omega)
              ⟨hq_ge, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hkp_le,
               wstkP, hwsP, fun i hi => houtP i
                 (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega)),
               hpreP, by rw [hp1_eq]; exact hrem', hmP⟩
        · c0_hsteps
          refine hLoopP (keptP, p + (1 : BitVec 64), q, ()) mP
            (by dsimp only; rw [hp1_eq]; omega)
            ⟨hq_ge, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hkp_le,
             wstkP, hwsP, fun i hi => houtP i
               (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega)),
             hpreP, by rw [hp1_eq]; exact hrem', hmP⟩
      · have hlg0 : (w0 &&& 0x80000000#32) = 0#32 := by c0_bound
        have ⟨_, hrem'⟩ := hstep.2 hlg0
        have hp2_eq : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := cmp_bv64_add2 (by omega)
        have hrem_p2 : WatchSliceOk F_cur { kL with wstk := wstkP } l.toNat
            (p.toNat + 2) (off0 + sz0 - (p.toNat + 2)) := by
          simpa [Nat.sub_sub] using hrem'
        c0_hsteps
        refine hLoopP (keptP, p + (2 : BitVec 64), q, ()) mP (by dsimp only; rw [hp2_eq]; omega)
          ⟨hq_ge, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, hkp_le,
           wstkP, hwsP, fun i hi => houtP i
             (hi.elim Or.inl fun h2 => Or.inr (by rw [hp2_eq] at h2; omega)),
           hpreP, by rw [hp2_eq]; exact hrem_p2, hmP⟩
    · have hp_eq : p.toNat = off0 + sz0 := by
        have h1 : ¬ p.toNat < end64.toNat := by c0_bound
        omega
      rw [hp_eq] at houtP
      clear hLoopP Jp
      exact full_compact_bins_post_p hkL hoff_def hsz_def hcv_le hwc_lt hmax_lt hold hckL hlayL
        hwvL hl_lt hoff64 hend64 hbd_l hsz_pos hq_ge (by dsimp only; omega) hkp_bd hwsP houtP
        hpreP hpreL hwatL hmP hLoop1

private theorem full_compact_bins_tail {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {ncv : BitVec 64}
    {inv : List (BitVec 32)} {s : FullState} {kL : FullCoreState} {R : Mem 64 → Prop}
    {old_cv kept : BitVec 64} {wvecL wstkL : List (BitVec 32)} {wuL : BitVec 64} {mL : Mem 64}
    (hkL : kL = { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL })
    (hlen : FullState.LengthsOk c s) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hmax_lt : c.max_vars < 2 * 2 ^ 28) (hold : s.core.cur_vars = old_cv.toNat)
    (hncv_le : ncv.toNat ≤ old_cv.toNat)
    (hbij : CompactBijOk old_cv.toNat ncv.toNat s.core.vals s.scratch.work_stk1 inv)
    (hckL : FullCoreState.LengthsOk c kL) (hlayL : WatchStackLayout kL)
    (hwvL : wvecL.length = 4 * c.max_vars) (_hwsL : wstkL.length = c.wcap)
    (hpreL : ∀ ol < 2 * old_cv.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur kL ol
      (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hmL : (FullMem c { s with core := kL } ⋆ R) mL)
    (hQ : ∀ (wvec' wstk' : List (BitVec 32)) (wusable' num_bin' : BitVec 64) (m' : Mem 64),
      let k' : FullCoreState :=
        { s.core with wvec := wvec', wstk := wstk', wusable := wusable', num_binary := num_bin' }
      FullState.LengthsOk c { s with core := k' } →
      CompactUnmapBinsOk ncv.toNat inv F_cur k' →
      (FullMem c { s with core := k' } ⋆ R) m' → Q () m') :
    wp Γ Q X (binsTailExpr c.hdr old_cv ncv kept c.pWorkStk1 c.pWvec) mL := by
  let k1 : FullCoreState := { kL with num_binary := kept >>> (1 : Nat) }
  have hk1_mem : ({ s with core := k1 } : FullState) =
      { s with core := { kL with num_binary := kept >>> (1 : Nat) } } := rfl
  unfold binsTailExpr
  c0_hsteps
  refine wp_loop_inv
    (fun (v, ()) m2 =>
      v.toNat ≤ old_cv.toNat ∧
      ∃ wvec2 : List (BitVec 32), wvec2.length = 4 * c.max_vars ∧
        (∀ w, v.toNat ≤ w → w < old_cv.toNat → ∀ d < 4, wvec2[4 * w + d]? = wvecL[4 * w + d]?) ∧
        (∀ nv < ncv.toNat, ∀ ov, (inv[nv]?.getD 0#32).toNat = ov → ov < v.toNat →
          ∀ d < 4, wvec2[4 * nv + d]? = wvecL[4 * ov + d]?) ∧
        (FullMem c { s with core := { k1 with wvec := wvec2 } } ⋆ R) m2)
    (fun (v, ()) _ => old_cv.toNat - v.toNat)
    (fun J2 hLoop2 => ?_) ?_
  · c0_hsteps
    exact hLoop2 (0#64, ()) _ ⟨Nat.zero_le _, wvecL, hwvL, fun _ _ _ _ _ => rfl,
      fun _ _ _ _ hlt => by simp at hlt,
      compactMem_cast (by assumption) (by dsimp only [k1]; rw [hkL])⟩
  · rintro J2 ⟨v, ⟨⟩⟩ m2 ⟨hv_le, wvec2, hwv2, hhi2, hmap2, hm2⟩ hLoop2
    c0_hsplit
    · have hv_lt : v.toNat < old_cv.toNat := by c0_bound
      have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := cmp_bv64_add1 (by omega)
      have hv_ws1 : v.toNat < s.scratch.work_stk1.length := by omega
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsplit
      · have hneq_ff : (s.scratch.work_stk1[v.toNat]'hv_ws1) ≠ 0xFFFFFFFF#32 := by c0_bound
        rcases hbij.map_ok v.toNat hv_lt with hff | ⟨nv, hnv_lt, hnv_le, _, hm_v, hi_v⟩
        · rw [List.getElem?_eq_getElem hv_ws1] at hff
          exact absurd (Option.some.inj hff) hneq_ff
        · have hnv32 : (s.scratch.work_stk1[v.toNat]'hv_ws1) = BitVec.ofNat 32 nv := by
            rw [List.getElem?_eq_getElem hv_ws1] at hm_v; exact Option.some.inj hm_v
          have hnv_to : (s.scratch.work_stk1[v.toNat]'hv_ws1).toNat = nv := by
            rw [hnv32, bv32_ofNat_toNat (by omega)]
          c0_hsplit
          · have hnv_lt_v : nv < v.toNat := by
              have hne_v : (s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 ≠ v := by c0_bound
              refine Nat.lt_of_le_of_ne hnv_le fun he => ?_
              apply hne_v; apply BitVec.eq_of_toNat_eq
              rw [zext_toNat _ (by decide), hnv_to]; exact he
            have h4v_eq : (v <<< (2 : Nat)).toNat = 4 * v.toNat :=
              cmp_bv64_shl2_toNat (by omega)
            have h4v1 : ((v <<< (2 : Nat)) + (1 : BitVec 64)).toNat = 4 * v.toNat + 1 := by
              rw [cmp_bv64_add1 (by rw [h4v_eq]; omega), h4v_eq]
            have h4v2 : ((v <<< (2 : Nat)) + (2 : BitVec 64)).toNat = 4 * v.toNat + 2 := by
              rw [cmp_bv64_add2 (by rw [h4v_eq]; omega), h4v_eq]
            have h4v3 : ((v <<< (2 : Nat)) + (3 : BitVec 64)).toNat = 4 * v.toNat + 3 := by
              rw [cmp_bv64_add3 (by rw [h4v_eq]; omega), h4v_eq]
            have h4nv_eq :
                ((s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 <<< (2 : Nat)).toNat =
                4 * nv := by
              rw [cmp_bv64_shl2_toNat (by rw [zext_toNat _ (by decide), hnv_to]; omega),
                zext_toNat _ (by decide), hnv_to]
            have h4nv1 :
                (((s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 <<< (2 : Nat)) +
                  (1 : BitVec 64)).toNat = 4 * nv + 1 := by
              rw [cmp_bv64_add1 (by rw [h4nv_eq]; omega), h4nv_eq]
            have h4nv2 :
                (((s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 <<< (2 : Nat)) +
                  (2 : BitVec 64)).toNat = 4 * nv + 2 := by
              rw [cmp_bv64_add2 (by rw [h4nv_eq]; omega), h4nv_eq]
            have h4nv3 :
                (((s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 <<< (2 : Nat)) +
                  (3 : BitVec 64)).toNat = 4 * nv + 3 := by
              rw [cmp_bv64_add3 (by rw [h4nv_eq]; omega), h4nv_eq]
            have h4v_bds : 4 * v.toNat < wvec2.length ∧ 4 * v.toNat + 1 < wvec2.length ∧
                4 * v.toNat + 2 < wvec2.length ∧ 4 * v.toNat + 3 < wvec2.length := by omega
            have h4nv_bds : 4 * nv < wvec2.length ∧ 4 * nv + 1 < wvec2.length ∧
                4 * nv + 2 < wvec2.length ∧ 4 * nv + 3 < wvec2.length := by omega
            c0_hsteps!
            let w0 := wvec2[4 * v.toNat]'h4v_bds.1
            let w1 := wvec2[4 * v.toNat + 1]'h4v_bds.2.1
            let w2 := wvec2[4 * v.toNat + 2]'h4v_bds.2.2.1
            let w3 := wvec2[4 * v.toNat + 3]'h4v_bds.2.2.2
            let wvec2' := (((wvec2.set (4 * nv) w0).set (4 * nv + 1) w1).set
              (4 * nv + 2) w2).set (4 * nv + 3) w3
            obtain ⟨hwv2', hhi2', hmap2'⟩ :=
              compactBins_loop2_step hbij hwv2 hv_lt (by omega) hncv_le hnv_lt hnv_lt_v hi_v hhi2
                hmap2 h4v_bds.1 h4v_bds.2.1 h4v_bds.2.2.1 h4v_bds.2.2.2
            refine hLoop2 (v + (1 : BitVec 64), ()) _ (by dsimp only; rw [hv1_eq]; omega)
              ⟨by rw [hv1_eq]; omega, wvec2', hwv2',
               fun w hw1 hw2 d hd => hhi2' w (by rw [hv1_eq] at hw1; exact hw1) hw2 d hd,
               fun nv' hnv' ov hov1 hov2 d hd =>
                 hmap2' nv' hnv' ov hov1 (by rw [hv1_eq] at hov2; exact hov2) d hd, ?_⟩
            · refine compactMem_cast (by assumption) (by
                 dsimp only [wvec2', w0, w1, w2, w3]
                 try simp only [h4v_eq, h4v1, h4v2, h4v3, h4nv_eq, h4nv1, h4nv2, h4nv3]
                 try simp only [
                   List.getElem_set_ne (by omega : 4 * nv ≠ 4 * v.toNat + 1),
                   List.getElem_set_ne (by omega : 4 * nv + 1 ≠ 4 * v.toNat + 2),
                   List.getElem_set_ne (by omega : 4 * nv ≠ 4 * v.toNat + 2),
                   List.getElem_set_ne (by omega : 4 * nv + 2 ≠ 4 * v.toNat + 3),
                   List.getElem_set_ne (by omega : 4 * nv + 1 ≠ 4 * v.toNat + 3),
                   List.getElem_set_ne (by omega : 4 * nv ≠ 4 * v.toNat + 3)]
                 try rfl)
          · have hnv_eq_v : nv = v.toNat := by
              have h0 : (s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 = v := by c0_bound
              have ht := congrArg BitVec.toNat h0
              rwa [zext_toNat _ (by decide), hnv_to] at ht
            c0_hsteps
            refine hLoop2 (v + (1 : BitVec 64), ()) m2 (by dsimp only; rw [hv1_eq]; omega)
              ⟨by rw [hv1_eq]; omega, wvec2, hwv2,
               fun w hw1 hw2 d hd => hhi2 w (by omega) hw2 d hd,
               fun nv' hnv' ov hov1 hov2 d hd => ?_, hm2⟩
            rw [hv1_eq] at hov2
            by_cases heq : ov = v.toNat
            · subst heq
              have hnv_eq : nv' = nv := hbij.inv_inj (nv1 := nv') (nv2 := nv) hnv' hnv_lt
                (by rw [hov1, hi_v, Option.getD_some, bv32_ofNat_toNat (by omega)])
              rw [hnv_eq, hnv_eq_v]; exact hhi2 v.toNat (Nat.le_refl _) hv_lt d hd
            · exact hmap2 nv' hnv' ov hov1 (by omega) d hd
      · have heq_ff : (s.scratch.work_stk1[v.toNat]'hv_ws1) = 0xFFFFFFFF#32 := by c0_bound
        c0_hsteps
        refine hLoop2 (v + (1 : BitVec 64), ()) m2 (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, wvec2, hwv2, fun w hw1 hw2 d hd => hhi2 w (by omega) hw2 d hd,
           fun nv' hnv' ov hov1 hov2 d hd => ?_, hm2⟩
        rw [hv1_eq] at hov2
        by_cases heq : ov = v.toNat
        · subst heq
          obtain ⟨ov', _, _, _, hi_v, hm_v⟩ := hbij.inv_ok nv' hnv'
          have hov'_eq : ov' = v.toNat := by
            rw [hi_v, Option.getD_some, bv32_ofNat_toNat (by omega)] at hov1; exact hov1
          subst hov'_eq
          rw [List.getElem?_eq_getElem hv_ws1, heq_ff] at hm_v
          have hto := congrArg BitVec.toNat (Option.some.inj hm_v)
          rw [show (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF from rfl,
            bv32_ofNat_toNat (by omega)] at hto
          have := hbij.old_cv_lt; omega
        · exact hmap2 nv' hnv' ov hov1 (by omega) d hd
    · have hv_eq : v.toNat = old_cv.toNat := by c0_bound
      rw [hv_eq] at hmap2
      clear hLoop2 J2
      c0_hsteps
      refine wp_loop_inv
        (fun (v3, ()) m3 =>
          ncv.toNat ≤ v3.toNat ∧ v3.toNat ≤ old_cv.toNat ∧
          ∃ wvec3 : List (BitVec 32), wvec3.length = 4 * c.max_vars ∧
            (∀ w, ncv.toNat ≤ w → w < v3.toNat → ∀ d < 4, wvec3[4 * w + d]? = some 0#32) ∧
            (∀ nv < ncv.toNat, ∀ d < 4, wvec3[4 * nv + d]? = wvec2[4 * nv + d]?) ∧
            (FullMem c { s with core := { k1 with wvec := wvec3 } } ⋆ R) m3)
        (fun (v3, ()) _ => old_cv.toNat - v3.toNat)
        (fun J3 hLoop3 => ?_) ?_
      · c0_hsteps; exact hLoop3 (ncv, ()) m2 ⟨Nat.le_refl _, hncv_le, wvec2, hwv2,
          fun _ h1 h2 => by omega, fun _ _ _ _ => rfl, hm2⟩
      · rintro J3 ⟨v3, ⟨⟩⟩ m3 ⟨hv3_ge, hv3_le, wvec3, hwv3, hzero3, hpres3, hm3⟩ hLoop3
        c0_hsplit
        · have hv3_lt : v3.toNat < old_cv.toNat := by c0_bound
          have hv3_1_eq : (v3 + (1 : BitVec 64)).toNat = v3.toNat + 1 := cmp_bv64_add1 (by omega)
          have h4v3_eq : (v3 <<< (2 : Nat)).toNat = 4 * v3.toNat :=
            cmp_bv64_shl2_toNat (by omega)
          have h4v3_1 : ((v3 <<< (2 : Nat)) + (1 : BitVec 64)).toNat = 4 * v3.toNat + 1 := by
            rw [cmp_bv64_add1 (by rw [h4v3_eq]; omega), h4v3_eq]
          have h4v3_2 : ((v3 <<< (2 : Nat)) + (2 : BitVec 64)).toNat = 4 * v3.toNat + 2 := by
            rw [cmp_bv64_add2 (by rw [h4v3_eq]; omega), h4v3_eq]
          have h4v3_3 : ((v3 <<< (2 : Nat)) + (3 : BitVec 64)).toNat = 4 * v3.toNat + 3 := by
            rw [cmp_bv64_add3 (by rw [h4v3_eq]; omega), h4v3_eq]
          let wvec3' := (((wvec3.set (4 * v3.toNat) 0#32).set (4 * v3.toNat + 1) 0#32).set
            (4 * v3.toNat + 2) 0#32).set (4 * v3.toNat + 3) 0#32
          obtain ⟨hwv3', hzero3', hpres3'⟩ :=
            compactBins_loop3_step hwv3 hv3_ge hv3_lt (by omega) hzero3 hpres3
          c0_hsteps!
          refine hLoop3 (v3 + (1 : BitVec 64), ()) _ (by dsimp only; rw [hv3_1_eq]; omega)
            ⟨by rw [hv3_1_eq]; omega, by rw [hv3_1_eq]; omega, wvec3', hwv3',
             fun w hw1 hw2 d hd => hzero3' w hw1 (by rw [hv3_1_eq] at hw2; exact hw2) d hd,
             hpres3', ?_⟩
          · refine compactMem_cast (by assumption) (by
              dsimp only [wvec3']; try simp only [h4v3_eq, h4v3_1, h4v3_2, h4v3_3]; rfl)
        · have hv3_eq : v3.toNat = old_cv.toNat := by c0_bound
          rw [hv3_eq] at hzero3
          c0_hsteps
          let k3 : FullCoreState := { k1 with wvec := wvec3 }
          obtain ⟨hhi3, hmap3⟩ :=
            compactBins_loop3_done (kL := kL) (k3 := k3) rfl (by simp [hkL]) hzero3 hpres3 hmap2
          have hck3 : FullState.LengthsOk c { s with core := k3 } :=
            ⟨{ hckL with wvec_len := hwv3 }, hlen.scratch_ok⟩
          have hpre1 : ∀ ol < 2 * old_cv.toNat,
              CompactPreBinSliceOk ncv.toNat inv F_cur k1 ol
                (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol) := fun ol hol => by
            simpa only [fullWatchOffCore, fullWatchSizeCore] using
              (hpreL ol hol).relocate (k := kL) (k' := k1) (fun _ _ => rfl)
          have hcv1 : k1.cur_vars = old_cv.toNat := by dsimp only [k1]; rw [hkL]; exact hold
          have hcv3 : k3.cur_vars = old_cv.toNat := by dsimp only [k3, k1]; rw [hkL]; exact hold
          have hlay1 : WatchStackLayout k1 := by
            refine ⟨fun j hj => ?_, fun j hj hp => ?_,
              fun j1 j2 h1 h2 hne hp1 hp2 => ?_, fun j hj idx hi => ?_⟩ <;>
              dsimp only [fullWatchOffCore, fullWatchSizeCore, k1] at *
            · exact hlayL.bounds j hj
            · exact hlayL.pos_off j hj hp
            · exact hlayL.disjoint j1 j2 h1 h2 hne hp1 hp2
            · exact hlayL.no_sentinel j hj idx hi
          have hbin3 := compactBins_finalize (c := c) (k1 := k1) (k2 := k3)
            hcv1 hcv3 hbij hlay1 hwv3 rfl rfl hhi3 hmap3 hpre1
          let nb3 := kept >>> (1 : Nat)
          have hk3_eq : k3 = { s.core with
              wvec := wvec3, wstk := wstkL, wusable := wuL, num_binary := nb3 } := by
            simp only [k3, k1, hkL, nb3]
          rw [hk3_eq] at hck3 hbin3
          exact hQ wvec3 wstkL wuL (kept >>> (1 : Nat)) m3 hck3 hbin3
            (compactMem_cast hm3 (by simp only [k1, hkL]))

public section

/-- Canonical WP proof for `full_compact_bins`. -/
theorem full_compact_bins_wp (Γ : Env) :
    ∀ a m Q X, compactBinsSpec a m Q X → Func.wp Γ full_compact_bins_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨F0, F_cur⟩, R, rfl, _, ⟨hsp, hold, hncv_le, hbij⟩, hm, hQ0⟩ :=
    FullContract.elim hs
  let hQ : ∀ wvec' wstk' wu' nb' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk',
                                         wusable := wu', num_binary := nb' } }
      s'.LengthsOk c → CompactUnmapBinsOk ncv.toNat s.scratch.work_stk2 F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m' :=
    fun wvec' wstk' wu' nb' m' hlen' hbin' hm' =>
      hQ0 () _ m' hlen' ⟨rfl, hbin'⟩ hm'
  have hlen := hsp.1
  have hw := hsp.2.1
  have hdm := hsp.2.2.2.2.2
  have hwat : WatchesInv F_cur s.core := by
    have hm' := hw.watches; unfold ModeWatchesInv at hm'; rwa [ite_eq_left hdm] at hm'
  have hck0 := hlen.core_ok
  have hcv_le := hck0.cur_vars_le
  have hv_len := hck0.vals_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hwc_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hnlits_eq : (old_cv <<< (1 : Nat)).toNat = 2 * old_cv.toNat := bv64_shl1_toNat (by omega)
  have hov_lt32 : old_cv.toNat < 0x7FFFFFFF := hbij.old_cv_lt
  let inv := s.scratch.work_stk2
  unfold Func.wp full_compact_bins_body
  c0_hsteps
  refine wp_loop_inv
    (fun (kept, l, ()) mL =>
      l.toNat ≤ 2 * old_cv.toNat ∧ kept.toNat ≤ l.toNat * c.wcap ∧
      ∃ (wvecL wstkL : List (BitVec 32)) (wuL : BitVec 64),
        wvecL.length = 4 * c.max_vars ∧ wstkL.length = c.wcap ∧
        let kL : FullCoreState := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL }
        WatchStackLayout kL ∧
        (∀ ol < l.toNat,
          CompactPreBinSliceOk ncv.toNat inv F_cur kL ol
            (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol)) ∧
        (∀ ol, l.toNat ≤ ol → ol < 2 * old_cv.toNat →
          WatchSliceOk F_cur kL ol (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol)) ∧
        (FullMem c { s with core := kL } ⋆ R) mL)
    (fun (_, l, ()) _ => 2 * old_cv.toNat - l.toNat)
    (fun J1 hLoop1 => ?_) ?_
  · c0_hsteps
    refine hLoop1 (0#64, 0#64, ()) m ⟨Nat.zero_le _, Nat.zero_le _, s.core.wvec, s.core.wstk,
      s.core.wusable, hck0.wvec_len, hck0.wstk_len_arr, hwat.layout,
      fun _ h => by simp at h, fun ol _ hol => hwat.slices ol (hold ▸ hol), hm⟩
  · rintro J1 ⟨kept, l, ⟨⟩⟩ mL
      ⟨hl_le, hkept_le, wvecL, wstkL, wuL, hwvL, hwsL, hlayL, hpreL, hwatL, hmL⟩ hLoop1
    let kL : FullCoreState := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL }
    have hckL : FullCoreState.LengthsOk c kL :=
      { hck0 with wvec_len := hwvL, wstk_len_arr := hwsL }
    have hkl_mul_lt : 2 * c.max_vars * c.wcap < 2 ^ 60 := by
      have h1 : 2 * c.max_vars ≤ 2 ^ 30 := by omega
      have h2 : c.wcap < 2 ^ 29 := by omega
      have : 2 * c.max_vars * c.wcap < 2 ^ 30 * 2 ^ 29 :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h1) (Nat.mul_lt_mul_of_pos_left h2 (by decide))
      omega
    c0_hsplit
    · have hl_lt : l.toNat < 2 * old_cv.toNat := by c0_bound
      have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := cmp_bv64_add1 (by omega)
      have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
      have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        rw [cmp_bv64_add1 (by rw [h2l_eq]; omega), h2l_eq]
      have h2l_lt : 2 * l.toNat < wvecL.length := by omega
      have h2l1_lt : 2 * l.toNat + 1 < wvecL.length := by omega
      have h2l_lt' : (l <<< (1 : Nat)).toNat < wvecL.length := by rw [h2l_eq]; omega
      have h2l1_lt' : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wvecL.length := by
        rw [h2l1_eq]; omega
      let off0 := fullWatchOffCore kL l.toNat
      let sz0 := fullWatchSizeCore kL l.toNat
      have hoff_eq : (wvecL[2 * l.toNat]'h2l_lt).toNat = off0 := by
        unfold off0 fullWatchOffCore kL; rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
      have hsz_eq : (wvecL[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
        unfold sz0 fullWatchSizeCore kL; rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
      have hbd_l : off0 + sz0 ≤ kL.wlen := hlayL.bounds l.toNat (hold ▸ hl_lt)
      have hwl_le := hck0.wlen_le
      have hslice_l : WatchSliceOk F_cur kL l.toNat off0 sz0 :=
        hwatL l.toNat (Nat.le_refl _) hl_lt
      c0_hsplit
      · have hsz0_zero : sz0 = 0 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          have hidx_mod : (2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * l.toNat + 1 := by
            rw [h1]; exact Nat.mod_eq_of_lt (by omega)
          have hbv : (wvecL[(2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
              rw [hidx_mod]; exact h2l1_lt)).setWidth 64 = 0#64 := by c0_bound
          have ht0 := congrArg BitVec.toNat hbv
          simp only [BitVec.toNat_setWidth, hidx_mod] at ht0
          rw [Nat.mod_eq_of_lt (by omega)] at ht0
          exact hsz_eq.symm.trans ht0
        let wvec' := wvecL.set (2 * l.toNat) 0#32
        let k' : FullCoreState := { kL with wvec := wvec' }
        obtain ⟨_, hsz'_l, hne_eq, hlay'⟩ :=
          compactBins_zero_slice_layout (kL := kL) rfl hwvL (by omega) (hold ▸ hl_lt) hsz0_zero
            hlayL
        c0_hsteps
        refine hLoop1 (kept, l + (1 : BitVec 64), ()) _ (by dsimp only; rw [hl1_eq]; omega)
          ⟨by rw [hl1_eq]; omega, by rw [hl1_eq, Nat.add_mul, Nat.one_mul]; omega,
           wvec', wstkL, wuL, by simp [wvec', hwvL], hwsL, hlay', fun ol hol => ?_,
           fun ol hlo hol => ?_,
           compactMem_cast (by assumption) (by dsimp only [wvec', k', kL]; rw [h2l_eq]; rfl)⟩
        · rw [hl1_eq] at hol
          by_cases hol_eq : ol = l.toNat
          · subst hol_eq; rw [hsz'_l]; exact .empty
          · obtain ⟨ho, hs⟩ := hne_eq ol hol_eq; rw [ho, hs]
            exact CompactPreBinSliceOk.relocate (k := kL) (k' := k') (fun _ _ => rfl)
              (hpreL ol (by omega))
        · rw [hl1_eq] at hlo
          obtain ⟨ho, hs⟩ := hne_eq ol (by omega); rw [ho, hs]
          exact watchSliceOk_relocate_cmp (k := kL) (k' := k') rfl rfl rfl (fun _ _ => rfl)
            (hwatL ol (by omega) hol)
      · have hsz_pos : 0 < sz0 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          have hidx_mod : (2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * l.toNat + 1 := by
            rw [h1]; exact Nat.mod_eq_of_lt (by omega)
          have hne : (wvecL[(2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
              rw [hidx_mod]; exact h2l1_lt)).setWidth 64 ≠ 0#64 := by c0_bound
          refine Nat.pos_of_ne_zero fun hz => ?_
          have h2 : (wvecL[(2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
              rw [hidx_mod]; exact h2l1_lt)).toNat = 0 := by simp only [hidx_mod, hsz_eq]; exact hz
          apply hne; apply BitVec.eq_of_toNat_eq; rw [zext_toNat _ (by decide), h2]; rfl
        have hbd_cap : off0 + sz0 ≤ c.wcap := by
          have h1 : off0 + sz0 ≤ s.core.wlen := hbd_l
          omega
        have hl2_ws1 : (l >>> (1 : Nat)).toNat < s.scratch.work_stk1.length := by
          rw [bv64_shr1_toNat]; omega
        have hl_vals : l.toNat < s.core.vals.length := by omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [.bool]) (fun _ mK => mL = mK) ?_ ?_
        · rintro _ ⟨keep_l, ⟨⟩⟩ mK hm_eq
          rw [← hm_eq] at *; clear hm_eq mK
          c0_hsteps
          have hoff64 :
              ((wvecL[(l <<< (1 : Nat)).toNat]'h2l_lt').setWidth 64).toNat = off0 := by
            rw [zext_toNat _ (by decide)]; simp only [h2l_eq, hoff_eq]
          have hsz64 :
              ((wvecL[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'h2l1_lt').setWidth 64).toNat =
                sz0 := by
            rw [zext_toNat _ (by decide)]; simp only [h2l1_eq, hsz_eq]
          have hend64 :
              ((wvecL[(l <<< (1 : Nat)).toNat]'h2l_lt').setWidth 64 +
                (wvecL[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'h2l1_lt').setWidth
                  64).toNat = off0 + sz0 := by
            rw [BitVec.toNat_add, hoff64, hsz64, Nat.mod_eq_of_lt (by omega)]
          refine full_compact_bins_ploop rfl rfl rfl hcv_le hv_len hws1_len hwc_lt hmax_lt
            hkl_mul_lt hold hncv_le hbij hckL hlayL hwvL hwsL hl_lt hkept_le hoff64 hend64 ?_
            hbd_l hsz_pos hslice_l hpreL hwatL hmL hLoop1
          simpa [bv_c0] using hnlits_eq
        · intro Jk hJk
          clear hpreL hwatL hlayL hckL hsp hw hwat
          c0_hsplit
          · c0_hsteps <;> exact hJk _ mL rfl
          · c0_hsteps <;> exact hJk _ mL rfl
    · have hl_eq : l.toNat = 2 * old_cv.toNat := by c0_bound
      rw [hl_eq] at hpreL
      clear hLoop1 J1 hwatL hck0 hsp hw hwat
      c0_hstep; c0_hstep; c0_hstep
      exact full_compact_bins_tail rfl hlen hcv_le hws1_len hmax_lt hold hncv_le hbij hckL
        hlayL hwvL hwsL hpreL hmL hQ

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
