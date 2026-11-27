/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.WpM7Xor0

/-!
# Kissat Gates WP Proofs — M7 XOR (`full_bve_find_xor_m7`)

`CanonicalEnv`-clean `Func.wp` proof for `full_bve_find_xor_m7`
(`0` legacy `Full*` imports; every decl `<= 450` LOC; total file `<= 1,500` LOC).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Gates
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "gates_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

private def m7XorPosStepExpr (h pScr : Val i64) (pl i0 k etgt pmask j : Val i32)
    (cj : Val i32) (lpLbl : Cont [i32, i32]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32]]) (fun _Js =>
    Blocks.cons (fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var j, Arg.imm 1, ()) } fun p_44
    =>
    Expr.jump lpLbl (Arg.var p.fst, Arg.var p_44.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var j, Arg.var i0, ()) } fun p_44
    =>
    Expr.jnz (Arg.var p_44.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var cj, Arg.imm 2147483648, ()) }
    fun p_45 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_45.fst, Arg.imm 0, ()) }
    fun p_46 =>
    Expr.jnz (Arg.var p_46.fst) (Expr.call (as := [i64, i32, i32, i32]) (bs := [i32])
    "full_bve_xor_pat_m7" (Arg.var h, Arg.var pl, Arg.var cj, Arg.var k, ()) fun p =>
    Expr.group (sig := [[i32]]) (fun _Js_6 =>
    Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p.fst, Arg.imm 16, ()) } fun
    p_47 =>
    Expr.jnz (Arg.var p_47.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var etgt, Arg.var p.fst, ()) }
    fun p_48 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var p_48.fst, Arg.imm 1, ()) }
    fun p_49 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var p_49.fst, Arg.imm 0, ()) }
    fun p_50 =>
    Expr.jnz (Arg.var p_50.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var pmask, Arg.var p.fst, ()) }
    fun p_51 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var p_51.fst, Arg.imm 1, ()) }
    fun p_52 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_52.fst, Arg.imm 0, ()) }
    fun p_53 =>
    Expr.jnz (Arg.var p_53.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.shl i32, args := (Arg.imm 1, Arg.var p.fst, ()) } fun
    p_54 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.or i32, args := (Arg.var pmask, Arg.var p_54.fst, ()) }
    fun p_55 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.imm 1060, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.store (Arg.var j) (Arg.var p.fst) (Expr.jump Js.fst (Arg.var p_55.fst, ())))
    (Expr.jump Js.fst (Arg.var pmask, ()))) (Expr.jump Js.fst (Arg.var pmask, ()))) (Expr.jump
    Js.fst (Arg.var pmask, ()))) (Expr.jump Js.fst (Arg.var pmask, ()))) (Expr.jump Js.fst
    (Arg.var pmask, ()))

private def m7XorPosScanExpr (h pScr pLm : Val i64) (np nn pl nl i0 k etgt otgt : Val i32)
    (onRejectLbl : Cont []) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, i32]]) (fun Js_5 =>
    Blocks.cons (fun p_38 =>
    Expr.group (sig := [[]]) (fun _Js_6 =>
    Blocks.cons (fun _p_39 =>
    Expr.group (sig := [[i32]]) (fun _Js_7 =>
    Blocks.cons (fun p =>
    Expr.group (sig := [[i32]]) (fun Js_8 =>
    Blocks.cons (fun p_40 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p_40.fst, Arg.var k, ()) }
    fun p_41 =>
    Expr.jnz (Arg.var p_41.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.imm 1092, Arg.var p_40.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLm, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_42 =>
    Expr.store (Arg.var p_42.fst) (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.xor i32, args := (Arg.var ld, Arg.imm 1, ()) } fun p
    =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLm, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_43 =>
    Expr.store (Arg.var p_43.fst) (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_40.fst, Arg.imm 1, ()) }
    fun p =>
    Expr.jump Js_8.fst (Arg.var p.fst, ())))) (Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_38.fst, Arg.var etgt, ()) }
    fun p_42 =>
    Expr.jnz (Arg.var p_42.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p.fst, Arg.var otgt, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.shl i32, args := (Arg.imm 1, Arg.var k, ()) } fun p =>
    Expr.group (sig := [[i32]]) (fun Js =>
    Blocks.cons (fun p_43 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p_43.fst, Arg.var p.fst, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst)
    (Expr.group (sig := [[]]) (fun _Js_9 =>
    Blocks.cons (fun _p =>
    Expr.group (sig := [[]]) (fun _Js_10 =>
    Blocks.cons (fun _p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_43.fst, Arg.imm 1, ()) }
    fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var otgt, Arg.var p_43.fst, ()) }
    fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var p.fst, Arg.imm 1, ()) } fun
    p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var p.fst, Arg.imm 0, ()) } fun p
    =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.imm 1076, Arg.var p_43.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var ld, Arg.imm 5, ()) } fun p
    =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.imm 1040, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun
    p_44 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_44.fst, Arg.imm 4, ()) }
    fun p_45 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p_45.fst, ()) }
    fun p_46 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld_6 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld, Arg.imm 31, ()) } fun p
    =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.shl i32, args := (Arg.imm 1, Arg.var p.fst, ()) } fun
    p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.or i32, args := (Arg.var ld_6, Arg.var p.fst, ()) }
    fun p =>
    Expr.store (Arg.var p.fst) (Arg.var p_46.fst) (Expr.jump Js.fst ())) (Expr.jump Js.fst
    ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var etgt, Arg.var p_43.fst, ()) }
    fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var p.fst, Arg.imm 1, ()) } fun
    p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var p.fst, Arg.imm 0, ()) } fun p
    =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.imm 1060, Arg.var p_43.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var ld, Arg.imm 5, ()) } fun p
    =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.imm 1024, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun
    p_44 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_44.fst, Arg.imm 4, ()) }
    fun p_45 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p_45.fst, ()) }
    fun p_46 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld_6 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld, Arg.imm 31, ()) } fun p
    =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.shl i32, args := (Arg.imm 1, Arg.var p.fst, ()) } fun
    p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.or i32, args := (Arg.var ld_6, Arg.var p.fst, ()) }
    fun p =>
    Expr.store (Arg.var p.fst) (Arg.var p_46.fst) (Expr.jump Js.fst ())) (Expr.jump Js.fst
    ())) (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1056, ()) }
    fun p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.store (Arg.imm (t := i32) 1) (Arg.var p.fst) (Expr.let_
    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1057, ()) } fun p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.store (Arg.imm (t := i32) 0) (Arg.var p.fst) (Expr.ret (Arg.imm true, ())))))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, ())) (Expr.jump onRejectLbl ())) (Expr.jump onRejectLbl ())))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_38.fst, Arg.var etgt, ()) }
    fun p_40 =>
    Expr.jnz (Arg.var p_40.fst)
    (Expr.group (sig := [[i32, i32]]) (fun Js_7 =>
    Blocks.cons (fun p_41 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p_41.snd.fst, Arg.var nn, ()) }
    fun p_42 =>
    Expr.jnz (Arg.var p_42.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var p_41.fst, Arg.var otgt, ()) }
    fun p_43 =>
    Expr.jnz (Arg.var p_43.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.imm 512, Arg.var p_41.snd.fst, ()) }
    fun p_44 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_44.fst, ()) } fun
    p_45 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_45.fst, Arg.imm 4, ()) }
    fun p_46 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p_46.fst, ()) }
    fun p_47 =>
    Expr.load i32 (Arg.var p_47.fst) fun ld =>
    Expr.group (sig := [[i32]]) (fun _Js =>
    Blocks.cons (fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_41.snd.fst, Arg.imm 1, ()) }
    fun p_48 =>
    Expr.jump Js_7.fst (Arg.var p.fst, Arg.var p_48.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld, Arg.imm 2147483648, ()) }
    fun p_48 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_48.fst, Arg.imm 0, ()) }
    fun p_49 =>
    Expr.jnz (Arg.var p_49.fst) (Expr.call (as := [i64, i32, i32, i32]) (bs := [i32])
    "full_bve_xor_pat_m7" (Arg.var h, Arg.var nl, Arg.var ld, Arg.var k, ()) fun p =>
    Expr.group (sig := [[i32]]) (fun _Js_8 =>
    Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p.fst, Arg.imm 16, ()) } fun
    p_50 =>
    Expr.jnz (Arg.var p_50.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var otgt, Arg.var p.fst, ()) }
    fun p_51 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var p_51.fst, Arg.imm 1, ()) }
    fun p_52 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var p_52.fst, Arg.imm 0, ()) }
    fun p_53 =>
    Expr.jnz (Arg.var p_53.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var p_41.fst, Arg.var p.fst, ()) }
    fun p_54 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var p_54.fst, Arg.imm 1, ()) }
    fun p_55 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_55.fst, Arg.imm 0, ()) }
    fun p_56 =>
    Expr.jnz (Arg.var p_56.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.shl i32, args := (Arg.imm 1, Arg.var p.fst, ()) } fun
    p_57 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.or i32, args := (Arg.var p_41.fst, Arg.var p_57.fst, ()) }
    fun p_58 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.imm 1076, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.store (Arg.var p_41.snd.fst) (Arg.var p.fst) (Expr.jump Js.fst (Arg.var p_58.fst,
    ()))) (Expr.jump Js.fst (Arg.var p_41.fst, ()))) (Expr.jump Js.fst (Arg.var p_41.fst,
    ()))) (Expr.jump Js.fst (Arg.var p_41.fst, ()))) (Expr.jump Js.fst (Arg.var p_41.fst,
    ()))) (Expr.jump Js.fst (Arg.var p_41.fst, ()))) (Expr.jump Js.fst (Arg.var p_41.fst,
    ())))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())) (Expr.jump Js.fst (Arg.imm 0, ())))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p_38.snd.fst, Arg.var np, ()) }
    fun p_39 =>
    Expr.jnz (Arg.var p_39.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var p_38.fst, Arg.var etgt, ()) }
    fun p_40 =>
    Expr.jnz (Arg.var p_40.fst) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_38.snd.fst, ()) } fun p_41
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_41.fst, Arg.imm 4, ()) }
    fun p_42 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p_42.fst, ()) }
    fun p_43 =>
    Expr.load i32 (Arg.var p_43.fst) fun ld => (m7XorPosStepExpr h pScr pl i0 k etgt p_38.fst
    p_38.snd.fst ld Js_5.fst)) (Expr.jump Js.fst ())) (Expr.jump Js.fst ()))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 1, Arg.imm 0, ())

private def m7XorBreakExpr (h pScr pLm : Val i64) (np nn pl nl i0 k : Val i32)
    (onDoneLbl : Cont []) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32]]) (fun _Js_3 =>
    Blocks.cons (fun p_33 =>
    Expr.group (sig := [[i32]]) (fun _Js_4 =>
    Blocks.cons (fun p_34 =>
    Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1060, ()) } fun p_35
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_35.fst, Arg.imm 4, ()) }
    fun p_36 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p_36.fst, ()) }
    fun p_37 =>
    Expr.store (Arg.var i0) (Arg.var p_37.fst) (m7XorPosScanExpr h pScr pLm np nn pl nl i0 k
    p_33.fst p_34.fst onDoneLbl))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var k, Arg.imm 2, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 6, ()))
    (Expr.group (sig := [[i32]]) (fun _Js_4 =>
    Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var k, Arg.imm 3, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 150, ())) (Expr.jump Js.fst (Arg.imm
    27030, ()))))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var k, Arg.imm 2, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 9, ()))
    (Expr.group (sig := [[i32]]) (fun _Js_3 =>
    Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var k, Arg.imm 3, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 105, ())) (Expr.jump Js.fst (Arg.imm
    38505, ())))

private theorem m7_xor_pos_step_wp (Γ : Env) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (lmc : List (BitVec 8))
    (scrc scrp : List (BitVec 32)) (R : Mem 64 → Prop)
    (np pl i0 k_b etgt pmask j cj : BitVec 32)
    (mp : Mem 64) (Q : Post [.bool]) (X : XPost) (lpLbl : Cont [i32, i32])
    (hXorPat : Γ.Has "full_bve_xor_pat_m7" fullBveXorPatM7Spec)
    (hdw0 : FullDenseInvW c F0 F_cur s)
    (hlmc_len : lmc.length = 2 * c.max_vars)
    (hscrp_len : scrp.length = c.scratch_cap)
    (hsc1096 : 1096 ≤ c.scratch_cap)
    (hnp512 : np.toNat ≤ 512) (hk2 : 2 ≤ k_b.toNat) (hk4 : k_b.toNat ≤ 4)
    (hj_lt : j.toNat < np.toNat) (hcj_orig : cj = s.scratch.scratch_buf[j.toNat]'(by
      rw [hdw0.1.scratch_ok.scratch_buf_len]; omega))
    (hp_ok : ∀ i < np.toNat, FullBveEntryOkW F_cur s pl.toNat
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hscrp_o : ∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) →
      scrp[idx]? = scrc[idx]?)
    (_hscrp_out : ∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
      scrp[idx]? = s.scratch.scratch_buf[idx]?)
    (hpm_ok : XorMaskEntriesOk scrp 1060 np.toNat pmask)
    (hmp : (FullMem c (m7XorState s lmc scrp) ⋆ R) mp)
    (hlp : ∀ (pm' : BitVec 32) (scr_k : List (BitVec 32)) (mp' : Mem 64),
      scr_k.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) → scr_k[idx]? = scrc[idx]?) →
      XorMaskEntriesOk scr_k 1060 np.toNat pm' →
      (FullMem c (m7XorState s lmc scr_k) ⋆ R) mp' →
      lpLbl (pm', j + 1#32, ()) mp') :
    wp Γ Q X (m7XorPosStepExpr c.hdr c.pScratchBuf pl i0 k_b etgt pmask j cj lpLbl) mp := by
  have hscr_len0 := hdw0.1.scratch_ok.scratch_buf_len
  have hscr_lt := c.hscr; unfold dimacsBound at hscr_lt
  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
  unfold m7XorPosStepExpr
  refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun pm' mp' =>
      ∃ scr_k : List (BitVec 32),
        scr_k.length = c.scratch_cap ∧
        (∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) → scr_k[idx]? = scrc[idx]?) ∧
        XorMaskEntriesOk scr_k 1060 np.toNat pm' ∧
        (FullMem c (m7XorState s lmc scr_k) ⋆ R) mp')
    (fun _ pm' mp' ⟨scr_k, h1, h2, h3, h4⟩ => by
      c0_hsteps!; exact hlp pm' scr_k mp' h1 h2 h3 h4)
    (fun Jpm hJpm => by
      c0_hsplit
      rotate_left
      · c0_hsteps!; exact hJpm pmask mp ⟨scrp, hscrp_len, hscrp_o, hpm_ok, hmp⟩
      c0_hsplit
      rotate_left
      · c0_hsteps!; exact hJpm pmask mp ⟨scrp, hscrp_len, hscrp_o, hpm_ok, hmp⟩
      have hcj_and : cj &&& 0x80000000#32 = 0#32 := hc
      have hent_j := hp_ok j.toNat hj_lt
      rw [List.getElem?_eq_getElem (by rw [hscr_len0]; omega), Option.getD_some,
        ← hcj_orig] at hent_j
      unfold FullBveEntryOkW at hent_j
      rw [ite_eq_right fun h => h hcj_and] at hent_j
      have ⟨hlen_p, hw_p⟩ := lengths_witness_lm_scr hdw0 hlmc_len hscrp_len
      have hk1 : 1 ≤ k_b.toNat := by omega
      c0_hsteps_nogrp
      gates_call hXorPat
      refine fullBveXorPatM7Spec_intro rfl hlen_p hw_p hent_j.1 hent_j.2 hk1 hk4 hmp ?_
      intro pat hpat
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
        (fun pm' mp' =>
          ∃ scr_k : List (BitVec 32),
            scr_k.length = c.scratch_cap ∧
            (∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) → scr_k[idx]? = scrc[idx]?) ∧
            XorMaskEntriesOk scr_k 1060 np.toNat pm' ∧
            (FullMem c (m7XorState s lmc scr_k) ⋆ R) mp')
        (fun _ pm' mp' ⟨scr_k, h1, h2, h3, h4⟩ => by
          c0_hsteps!; exact hJpm pm' mp' ⟨scr_k, h1, h2, h3, h4⟩)
        (fun Jp1 hJp1 => by
          c0_hsplit
          · have hpat_lt : pat.toNat < 16 := hc
            c0_hsplit
            · c0_hsplit
              · have hst : (1060#64 + pat.setWidth 64).toNat < scrp.length := by
                  rw [hscrp_len]; c0_bound
                have hpm_s := xorMaskEntriesOk_set hpm_ok (by rw [hscrp_len]; omega) hpat_lt hj_lt
                have hscr_o_s : ∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) →
                    (scrp.set (1060 + pat.toNat) j)[idx]? = scrc[idx]? := fun idx hi hor => by
                  rw [List.getElem?_set_ne (by omega)]
                  exact hscrp_o idx hi hor
                c0_hsteps!
                dsimp only [m7XorState] at hm ⊢
                rw [show scrp.set _ j = scrp.set (1060 + pat.toNat) j from
                  congrArg (fun k => scrp.set k j) (by c0_bound)] at hm
                have hsh : (1 : BitVec 32) <<< (pat.toNat % 32) = 1#32 <<< pat := by
                  change 1#32 <<< (pat.toNat % 32) = 1#32 <<< pat.toNat
                  rw [Nat.mod_eq_of_lt (by omega)]
                rw [hsh]
                exact hJp1 (pmask ||| (1#32 <<< pat)) _
                  ⟨scrp.set (1060 + pat.toNat) j, by rw [List.length_set, hscrp_len],
                    hscr_o_s, hpm_s, hm⟩
              · c0_hsteps!; exact hJp1 pmask mp ⟨scrp, hscrp_len, hscrp_o, hpm_ok, hmp⟩
            · c0_hsteps!; exact hJp1 pmask mp ⟨scrp, hscrp_len, hscrp_o, hpm_ok, hmp⟩
          · c0_hsteps!; exact hJp1 pmask mp ⟨scrp, hscrp_len, hscrp_o, hpm_ok, hmp⟩))

private theorem m7_xor_pos_scan_wp (Γ : Env) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (lmc : List (BitVec 8))
    (scrc scr0 : List (BitVec 32)) (R : Mem 64 → Prop)
    (np nn pl nl i0 k_b full_pm full_nm : BitVec 32) (m0 : Mem 64)
    (Q : Post [.bool]) (X : XPost) (onRejectLbl : Cont [])
    (hXorPat : Γ.Has "full_bve_xor_pat_m7" fullBveXorPatM7Spec)
    (hdw0 : FullDenseInvW c F0 F_cur s) (hlmc_len : lmc.length = 2 * c.max_vars)
    (_hscrc_len : scrc.length = c.scratch_cap) (hscr0_len : scr0.length = c.scratch_cap)
    (hsc1096 : 1096 ≤ c.scratch_cap) (hnp512 : np.toNat ≤ 512) (hnn512 : nn.toNat ≤ 512)
    (hk2 : 2 ≤ k_b.toNat) (hk4 : k_b.toNat ≤ 4)
    (hp_ok : ∀ i < np.toNat, FullBveEntryOkW F_cur s pl.toNat
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn_ok : ∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hscrc_out : ∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
      scrc[idx]? = s.scratch.scratch_buf[idx]?)
    (hscr0_o : ∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) → scr0[idx]? = scrc[idx]?)
    (hpm0 : XorMaskEntriesOk scr0 1060 np.toNat 1#32)
    (h1092_bd : ∀ j < k_b.toNat, (scrc[1092 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnz_c : ∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
      ∃ j < k_b.toNat, y = (scrc[1092 + j]?.getD 0#32).toNat ∨
        y = ((scrc[1092 + j]?.getD 0#32) ^^^ 1#32).toNat)
    (hm0 : (FullMem c (m7XorState s lmc scr0) ⋆ R) m0)
    (honReject : ∀ (lmf : List (BitVec 8)) (scrf : List (BitVec 32)) (mf : Mem 64),
      lmf.length = 2 * c.max_vars → (∀ y < lmf.length, lmf[y]?.getD 0#8 = 0#8) →
      scrf.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
        scrf[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c (m7XorState s lmf scrf) ⋆ R) mf → onRejectLbl () mf)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      FullDenseInvW c F0 F_cur (m7XorState s lm' scr') → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c (m7XorState s lm' scr') ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (m7XorPosScanExpr c.hdr c.pScratchBuf c.pLitMark
      np nn pl nl i0 k_b full_pm full_nm onRejectLbl) m0 := by
  have hscr_len0 := hdw0.1.scratch_ok.scratch_buf_len
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  unfold m7XorPosScanExpr
  refine wp_loop_group (ts := [i32, i32])
    (fun remp (pmask, j, ()) mp =>
      ∃ scrp : List (BitVec 32),
        j.toNat ≤ np.toNat ∧ remp = np.toNat - j.toNat ∧ scrp.length = c.scratch_cap ∧
        (∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) → scrp[idx]? = scrc[idx]?) ∧
        XorMaskEntriesOk scrp 1060 np.toNat pmask ∧
        (FullMem c (m7XorState s lmc scrp) ⋆ R) mp)
    ?_ ?_
  · rintro Lp remp ⟨pmask, j, ⟨⟩⟩ mp hLp ⟨scrp, hj_le, rfl, hscrp_len, hscrp_o, hpm_ok, hmp⟩
    have h1092_p : ∀ j < k_b.toNat,
        (scrp[1092 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars := fun j hj => by
      rw [hscrp_o (1092 + j) (by omega) (Or.inr (by omega))]; exact h1092_bd j hj
    have hnz_p : ∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
        ∃ j < k_b.toNat, y = (scrp[1092 + j]?.getD 0#32).toNat ∨
          y = ((scrp[1092 + j]?.getD 0#32) ^^^ 1#32).toNat := fun y hy hyn => by
      obtain ⟨jj, hjj, hyeq⟩ := hnz_c y hy hyn; refine ⟨jj, hjj, ?_⟩
      rwa [hscrp_o (1092 + jj) (by omega) (Or.inr (by omega))]
    have hscrp_out : ∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
        scrp[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi hor =>
      (hscrp_o idx hi (by rcases hor with h | h <;> omega)).trans (hscrc_out idx hi hor)
    c0_hsteps_nogrp
    refine wp_join0
      (P := fun mp' =>
        ∃ scrp' : List (BitVec 32),
          scrp'.length = c.scratch_cap ∧
          (∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) → scrp'[idx]? = scrc[idx]?) ∧
          XorMaskEntriesOk scrp' 1060 np.toNat pmask ∧
          (FullMem c (m7XorState s lmc scrp') ⋆ R) mp')
      (fun _ mp' ⟨scrp', hscrp'_len, hscrp'_o, hpm_ok', hmp'⟩ => by
        have h1092_p' : ∀ j < k_b.toNat,
            (scrp'[1092 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars := fun j hj => by
          rw [hscrp'_o (1092 + j) (by omega) (Or.inr (by omega))]; exact h1092_bd j hj
        have hnz_p' : ∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
            ∃ j < k_b.toNat, y = (scrp'[1092 + j]?.getD 0#32).toNat ∨
              y = ((scrp'[1092 + j]?.getD 0#32) ^^^ 1#32).toNat := fun y hy hyn => by
          obtain ⟨jj, hjj, hyeq⟩ := hnz_c y hy hyn; refine ⟨jj, hjj, ?_⟩
          rwa [hscrp'_o (1092 + jj) (by omega) (Or.inr (by omega))]
        have hscrp'_out : ∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
            scrp'[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi hor =>
          (hscrp'_o idx hi (by rcases hor with h | h <;> omega)).trans (hscrc_out idx hi hor)
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
          (fun nmask' mv =>
            ∃ scr_v : List (BitVec 32),
              scr_v.length = c.scratch_cap ∧
              (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                scr_v[idx]? = s.scratch.scratch_buf[idx]?) ∧
              (∀ j < k_b.toNat, (scr_v[1092 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
              (∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
                ∃ j < k_b.toNat, y = (scr_v[1092 + j]?.getD 0#32).toNat ∨
                  y = ((scr_v[1092 + j]?.getD 0#32) ^^^ 1#32).toNat) ∧
              (∀ t < 16, (pmask &&& (1#32 <<< t)) ≠ 0#32 →
                (scr_v[1060 + t]?.getD 0#32).toNat < np.toNat) ∧
              XorMaskEntriesOk scr_v 1076 nn.toNat nmask' ∧
              (FullMem c (m7XorState s lmc scr_v) ⋆ R) mv)
          (fun _ nmask' mv ⟨scr_v, hscrv_len, hscrv_out, h1092_v, hnz_v, hpm_bd_v, hnm_ok_v,
              hmv⟩ =>
            m7_xor_clean_lm_wp Γ c s lmc scr_v R k_b mv Q X _ hlmc_len hscrv_len hsc1096 hk4
              hcv_le h1092_v (fun y hy => hnz_v y (by rw [hlmc_len]; exact hy)) hmv
              (fun lm_cl hlm_cl_len hlm_cl_z m_cl hm_cl => by
                c0_hsplit
                · have hpm_f : pmask = full_pm := hc
                  c0_hsplit
                  · have hnm_f : nmask' = full_nm := hc
                    let s_cl : FullState := { s with core := { s.core with lit_mark := lm_cl } }
                    refine m7_xor_commit_wp Γ c s_cl scr_v R k_b full_pm full_nm m_cl Q X
                      hscrv_len hscrv_out hsc1096 (by omega) hk4
                      (fun b hb hbit => lt_of_lt_of_le
                        (hpm_bd_v b hb (by rw [hpm_f]; exact hbit)) hnp512)
                      (fun b hb hbit => lt_of_lt_of_le
                        (hnm_ok_v.2 b hb (by rw [hnm_f]; exact hbit)) hnn512)
                      hm_cl (fun ok scr' m' hsc' hout' hm' =>
                        hQ ok lm_cl scr' m'
                          (fullDenseInvW_lm_scr hdw0 hlm_cl_len hlm_cl_z hsc')
                          hsc' hout' hm')
                  · c0_hsteps!
                    exact honReject lm_cl scr_v m_cl hlm_cl_len
                      (fun y hy => hlm_cl_z y (hlm_cl_len ▸ hy)) hscrv_len hscrv_out hm_cl
                · c0_hsteps!
                  exact honReject lm_cl scr_v m_cl hlm_cl_len
                    (fun y hy => hlm_cl_z y (hlm_cl_len ▸ hy)) hscrv_len hscrv_out hm_cl))
          (fun J60 hJ60 => by
            c0_hsplit
            · c0_hsteps_nogrp
              refine m7_xor_neg_scan_wp Γ c F0 F_cur s lmc scrp' R nn nl k_b full_nm mp' Q X
                (fun x => Expr.jump J60 (Arg.var x, ())) hXorPat hdw0 hlmc_len hscrp'_len
                hnn512 hsc1096 (by omega) hk4 hn_ok
                (fun j hj => hscrp'_out (512 + j) (by omega) (Or.inl (by omega)))
                hmp' (fun nmask scrn mn hscrn_len hscrn_o hnm_ok hmn => by
                  have h1092_n : ∀ j < k_b.toNat,
                      (scrn[1092 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars := fun j hj => by
                    rw [hscrn_o (1092 + j) (by omega) (Or.inr (by omega))]; exact h1092_p' j hj
                  have hnz_n : ∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
                      ∃ j < k_b.toNat, y = (scrn[1092 + j]?.getD 0#32).toNat ∨
                        y = ((scrn[1092 + j]?.getD 0#32) ^^^ 1#32).toNat := fun y hy hyn => by
                    obtain ⟨jj, hjj, hyeq⟩ := hnz_p' y hy hyn; refine ⟨jj, hjj, ?_⟩
                    rwa [hscrn_o (1092 + jj) (by omega) (Or.inr (by omega))]
                  have hscrn_out : ∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                      scrn[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi hor =>
                    (hscrn_o idx hi (by rcases hor with h | h <;> omega)).trans
                      (hscrp'_out idx hi hor)
                  have hpm_bd_n : ∀ t < 16, (pmask &&& (1#32 <<< t)) ≠ 0#32 →
                      (scrn[1060 + t]?.getD 0#32).toNat < np.toNat := fun t ht hb => by
                    rw [hscrn_o (1060 + t) (by omega) (Or.inl (by omega))]
                    exact hpm_ok'.2 t ht hb
                  c0_hsteps!
                  exact hJ60 nmask mn
                    ⟨scrn, hscrn_len, hscrn_out, h1092_n, hnz_n, hpm_bd_n, hnm_ok, hmn⟩)
            · c0_hsteps!
              exact hJ60 0#32 mp'
                ⟨scrp', hscrp'_len, hscrp'_out, h1092_p', hnz_p', hpm_ok'.2,
                  xorMaskEntriesOk_zero _ _ _, hmp'⟩))
      (fun Jex1 hJex1 => by
        c0_hsplit
        · have hj_lt : j.toNat < np.toNat := hc
          c0_hsplit
          · have hj_sc : (j.setWidth 64).toNat < scrp.length := by
              rw [hscrp_len, zext32_toNat]; omega
            let cj := scrp[(j.setWidth 64).toNat]'hj_sc
            have hcj_orig : cj = s.scratch.scratch_buf[j.toNat]'(by rw [hscr_len0]; omega) := by
              have := hscrp_out j.toNat (by omega) (Or.inl (by omega))
              rw [List.getElem?_eq_getElem (by rw [hscrp_len]; omega),
                List.getElem?_eq_getElem (by rw [hscr_len0]; omega)] at this
              exact (getElem_congr (zext32_toNat j) (by rw [hscrp_len, zext32_toNat]; omega)
                (by rw [hscrp_len]; omega)).trans (Option.some.inj this)
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            refine m7_xor_pos_step_wp Γ c F0 F_cur s lmc scrc scrp R np pl i0 k_b full_pm
              pmask j cj mp Q X _ hXorPat hdw0 hlmc_len hscrp_len hsc1096 hnp512 hk2 hk4
              hj_lt hcj_orig hp_ok hscrp_o hscrp_out hpm_ok hmp
              (fun pm' scr_k mp' h1 h2 h3 h4 =>
                hLp (np.toNat - (j + 1#32).toNat) (pm', j + 1#32, ()) mp' (by omega)
                  ⟨scr_k, by omega, rfl, h1, h2, h3, h4⟩)
          · c0_hsteps!; exact hJex1 mp ⟨scrp, hscrp_len, hscrp_o, hpm_ok, hmp⟩
        · c0_hsteps!; exact hJex1 mp ⟨scrp, hscrp_len, hscrp_o, hpm_ok, hmp⟩)
  · intro Lp hLp; c0_hsteps!
    exact hLp np.toNat (1#32, 0#32, ()) m0
      ⟨scr0, Nat.zero_le _, by simp, hscr0_len, hscr0_o, hpm0, hm0⟩

private theorem m7_xor_break_wp (Γ : Env) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (lmc : List (BitVec 8))
    (scrc : List (BitVec 32)) (R : Mem 64 → Prop)
    (np nn pl nl i0 k_b : BitVec 32) (mc : Mem 64)
    (Q : Post [.bool]) (X : XPost) (onDoneLbl : Cont [])
    (hXorPat : Γ.Has "full_bve_xor_pat_m7" fullBveXorPatM7Spec)
    (hdw0 : FullDenseInvW c F0 F_cur s) (hlmc_len : lmc.length = 2 * c.max_vars)
    (hscrc_len : scrc.length = c.scratch_cap) (hsc1096 : 1096 ≤ c.scratch_cap)
    (hnp512 : np.toNat ≤ 512) (hnn512 : nn.toNat ≤ 512)
    (hi0_lt : i0.toNat < np.toNat) (hk2 : 2 ≤ k_b.toNat) (hk4 : k_b.toNat ≤ 4)
    (hp_ok : ∀ i < np.toNat, FullBveEntryOkW F_cur s pl.toNat
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn_ok : ∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hscrc_out : ∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
      scrc[idx]? = s.scratch.scratch_buf[idx]?)
    (h1092_bd : ∀ j < k_b.toNat, (scrc[1092 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnz_c : ∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
      ∃ j < k_b.toNat, y = (scrc[1092 + j]?.getD 0#32).toNat ∨
        y = ((scrc[1092 + j]?.getD 0#32) ^^^ 1#32).toNat)
    (hmc : (FullMem c (m7XorState s lmc scrc) ⋆ R) mc)
    (honDone : ∀ (lmf : List (BitVec 8)) (scrf : List (BitVec 32)) (mf : Mem 64),
      lmf.length = 2 * c.max_vars → (∀ y < lmf.length, lmf[y]?.getD 0#8 = 0#8) →
      scrf.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
        scrf[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c (m7XorState s lmf scrf) ⋆ R) mf → onDoneLbl () mf)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      FullDenseInvW c F0 F_cur (m7XorState s lm' scr') → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c (m7XorState s lm' scr') ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (m7XorBreakExpr c.hdr c.pScratchBuf c.pLitMark
      np nn pl nl i0 k_b onDoneLbl) mc := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  unfold m7XorBreakExpr
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun full_pm => full_pm =
      if k_b = 2#32 then 9#32 else if k_b = 3#32 then 105#32 else 38505#32)
    ?_ ?_
  · rintro _ full_pm _
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun full_nm => full_nm =
        if k_b = 2#32 then 6#32 else if k_b = 3#32 then 150#32 else 27030#32)
      ?_ ?_
    · rintro _ full_nm _
      have h1060 : (1060#64 : BitVec 64).toNat < scrc.length := by rw [hscrc_len]; c0_bound
      c0_hsteps_nogrp
      have hxmi := xorMaskEntriesOk_init (base := 1060) (lim := np.toNat)
        (by rw [hscrc_len]; omega) hi0_lt
      have hscr_i_o : ∀ idx < c.scratch_cap, (idx < 1060 ∨ 1076 ≤ idx) →
          (scrc.set 1060 i0)[idx]? = scrc[idx]? := fun idx hi hor => by
        rw [List.getElem?_set_ne (by omega)]
      dsimp only [m7XorState] at hm ⊢
      rw [show scrc.set (1060#64).toNat i0 = scrc.set 1060 i0 from rfl] at hm
      exact m7_xor_pos_scan_wp Γ c F0 F_cur s lmc scrc (scrc.set 1060 i0) R
        np nn pl nl i0 k_b full_pm full_nm _ Q X onDoneLbl hXorPat hdw0 hlmc_len hscrc_len
        (by rw [List.length_set, hscrc_len]) hsc1096 hnp512 hnn512 hk2 hk4 hp_ok hn_ok
        hscrc_out hscr_i_o hxmi h1092_bd hnz_c hm honDone hQ
    · intro Jfn hJfn
      c0_hsplit
      · c0_hsteps!; exact hJfn 6#32 (by simp [hc])
      · have hk2_ne : k_b ≠ 2#32 := hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
          (fun x => x = if k_b = 3#32 then 150#32 else 27030#32)
          (fun _ x hx => by c0_hsteps!; exact hJfn x (by simp [hk2_ne, hx]))
          (fun Jfn2 hJfn2 => by
            c0_hsplit
            · c0_hsteps!; exact hJfn2 150#32 (by simp [hc])
            · c0_hsteps!; exact hJfn2 27030#32 (by simp [show k_b ≠ 3#32 from hc]))
  · intro Jfp hJfp
    c0_hsplit
    · c0_hsteps!; exact hJfp 9#32 (by simp [hc])
    · have hk2_ne : k_b ≠ 2#32 := hc
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
        (fun x => x = if k_b = 3#32 then 105#32 else 38505#32)
        (fun _ x hx => by c0_hsteps!; exact hJfp x (by simp [hk2_ne, hx]))
        (fun Jfp2 hJfp2 => by
          c0_hsplit
          · c0_hsteps!; exact hJfp2 105#32 (by simp [hc])
          · c0_hsteps!; exact hJfp2 38505#32 (by simp [show k_b ≠ 3#32 from hc]))

/-- Canonical `Func.wp` proof for `full_bve_find_xor_m7`. -/
theorem full_bve_find_xor_m7_wp (Γ : Env)
    (hXorPat : Γ.Has "full_bve_xor_pat_m7" fullBveXorPatM7Spec) :
    ∀ a m0 Q X, fullBveFindXorM7Spec a m0 Q X →
      Func.wp Γ full_bve_find_xor_m7_body a m0 Q X := by
  rintro ⟨hp, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s, R, rfl, hdw0, hsc1088, hv_lt, hnp512, hnn512,
    hp_ok, hn_ok, hm0, hQ⟩ := fullBveFindXorM7Spec_elim hSpec
  have hlen0 := hdw0.1
  have hw0 := hdw0.2.1
  have hlm0_clr := hdw0.2.2.1
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_lt := c.hscr; unfold dimacsBound at hscr_lt
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hscr_len0 := hlen0.scratch_ok.scratch_buf_len
  have har_len0 := hlen0.core_ok.arena_len_arr
  have hval_len0 := hlen0.core_ok.vals_len
  have hlm_len0 := hlen0.core_ok.lit_mark_len
  unfold Func.wp full_bve_find_xor_m7_body
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0 (fun _ _ _ => rfl) hm0
  · have hsc1096 : 1096 ≤ c.scratch_cap := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc
      change ¬c.scratch_cap < 1096 at hc; omega
    c0_hsteps_nogrp
    refine wp_loop_group (ts := [i32, i32])
      (fun rem (lp, i, ()) mi => mi = m0 ∧ i.toNat ≤ np.toNat ∧ rem = np.toNat - i.toNat)
      ?_ ?_
    · rintro L rem ⟨lp, i, ⟨⟩⟩ mi hL ⟨hm_eq, hi_le, rfl⟩
      subst mi
      c0_hsplit
      · have hi_lt : i.toNat < np.toNat := hc
        have hi_sc : (i.setWidth 64).toNat < s.scratch.scratch_buf.length := by
          rw [hscr_len0, zext32_toNat]; omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun x => (x, ())) (fun _ => True)
          (fun _ lp' _ => by
            c0_hsteps!
            exact hL (np.toNat - (i + 1#32).toNat) (lp', i + 1#32, ()) m0 (by omega)
              ⟨rfl, by omega, rfl⟩)
          (fun J hJ => by
            c0_hsplit
            · c0_hsteps!; exact hJ (lp + 1#32) trivial
            · c0_hsteps!; exact hJ lp trivial)
      · c0_hsteps_nogrp
        refine wp_loop_group (ts := [i32, i32])
          (fun rem2 (ln, j, ()) mj => mj = m0 ∧ j.toNat ≤ nn.toNat ∧ rem2 = nn.toNat - j.toNat)
          ?_ ?_
        · rintro L2 rem2 ⟨ln, j, ⟨⟩⟩ mj hL2 ⟨hm_eq2, hj_le, rfl⟩
          subst mj
          c0_hsplit
          · have hj_lt : j.toNat < nn.toNat := hc
            have hj_sc : (512#64 + j.setWidth 64).toNat < s.scratch.scratch_buf.length := by
              rw [hscr_len0]; c0_bound
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
              (fun x => (x, ())) (fun _ => True)
              (fun _ ln' _ => by
                c0_hsteps!
                exact hL2 (nn.toNat - (j + 1#32).toNat) (ln', j + 1#32, ()) m0 (by omega)
                  ⟨rfl, by omega, rfl⟩)
              (fun J2 hJ2 => by
                c0_hsplit
                · c0_hsteps!; exact hJ2 (ln + 1#32) trivial
                · c0_hsteps!; exact hJ2 ln trivial)
          · c0_hsplit
            · c0_hsteps!
              exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
                (fun _ _ _ => rfl) hm0
            · c0_hsplit
              · c0_hsteps!
                exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
                  (fun _ _ _ => rfl) hm0
              · c0_hsplit
                · c0_hsteps!
                  exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
                    (fun _ _ _ => rfl) hm0
                · have ⟨hpl_val, hnl_val⟩ := pl_nl_eq v (by omega)
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i32])
                    (fun rem3 (i, ()) mi =>
                      ∃ (lmi : List (BitVec 8)) (scri : List (BitVec 32)),
                        lmi.length = 2 * c.max_vars ∧
                        (∀ y < lmi.length, lmi[y]?.getD 0#8 = 0#8) ∧
                        scri.length = c.scratch_cap ∧
                        (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                          scri[idx]? = s.scratch.scratch_buf[idx]?) ∧
                        i.toNat ≤ np.toNat ∧ rem3 = np.toNat - i.toNat ∧
                        (FullMem c (m7XorState s lmi scri) ⋆ R) mi)
                    ?_ ?_
                  · rintro L3 rem3 ⟨i, ⟨⟩⟩ mi hL3 ⟨lmi, scri, hlmi_len, hlmi_z, hscri_len,
                      hscri_out, hi_le, rfl, hmi⟩
                    have hdw_i := fullDenseInvW_lm_scr hdw0 hlmi_len
                      (fun l hl => hlmi_z l (by rw [hlmi_len]; exact hl)) hscri_len
                    c0_hsplit
                    · have hi_lt : i.toNat < np.toNat := hc
                      have hi_sc : (i.setWidth 64).toNat < scri.length := by
                        rw [hscri_len, zext32_toNat]; omega
                      let cr := scri[(i.setWidth 64).toNat]'hi_sc
                      have hcr_orig :
                          cr = s.scratch.scratch_buf[i.toNat]'(by rw [hscr_len0]; omega) := by
                        have := hscri_out i.toNat (by omega) (Or.inl (by omega))
                        rw [List.getElem?_eq_getElem (by rw [hscri_len]; omega),
                          List.getElem?_eq_getElem (by rw [hscr_len0]; omega)] at this
                        have hcr_eq := getElem_congr (zext32_toNat i)
                          (by rw [hscri_len, zext32_toNat]; omega) (by rw [hscri_len]; omega)
                        exact hcr_eq.trans (Option.some.inj this)
                      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                      c0_hsteps_nogrp
                      refine wp_join0
                        (P := fun mn =>
                          ∃ (lmn : List (BitVec 8)) (scrn : List (BitVec 32)),
                            lmn.length = 2 * c.max_vars ∧
                            (∀ y < lmn.length, lmn[y]?.getD 0#8 = 0#8) ∧
                            scrn.length = c.scratch_cap ∧
                            (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                              scrn[idx]? = s.scratch.scratch_buf[idx]?) ∧
                            (FullMem c (m7XorState s lmn scrn) ⋆ R) mn)
                        (fun _ mn ⟨lmn, scrn, hlmn_len, hlmn_z, hscrn_len, hscrn_out, hmn⟩ => by
                          c0_hsteps!
                          exact hL3 (np.toNat - (i + 1#32).toNat) (i + 1#32, ()) mn (by omega)
                            ⟨lmn, scrn, hlmn_len, hlmn_z, hscrn_len, hscrn_out, by omega, rfl, hmn⟩)
                        (fun J34 hJ34 => by
                          c0_hsplit
                          · have hcr_and : cr &&& 0x80000000#32 = 0#32 := by
                              dsimp only [cr]
                              rw [getElem_congr (zext32_toNat i)
                                (by rw [hscri_len, zext32_toNat]; omega)
                                (by rw [hscri_len]; omega)]
                              exact hc
                            have hent_i := hp_ok i.toNat hi_lt
                            rw [List.getElem?_eq_getElem (by rw [hscr_len0]; omega),
                              Option.getD_some, ← hcr_orig] at hent_i
                            unfold FullBveEntryOkW at hent_i
                            rw [ite_eq_right fun h => h hcr_and] at hent_i
                            obtain ⟨href_cr, hng_cr⟩ := hent_i
                            have harena_lt := c.harena; unfold dimacsBound at harena_lt
                            have hal_le := hlen0.core_ok.arena_len_le
                            have hwf_cr := hw0.arena.refs_wf cr.toNat href_cr
                            have hcr_bd := hwf_cr.1
                            have hsz_ge3 := hwf_cr.2.1
                            have hcr3_bd :
                                cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                                  s.core.arena_len := by
                              have h1 := hwf_cr.2.2.1; have h2 := hwf_cr.2.2.2.1; omega
                            have har_len_cr2 :
                                (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by
                              rw [har_len0]; c0_bound
                            let sz := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'har_len_cr2
                            have hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                              unfold sz fullArenaClauseSizeCore
                              rw [List.getElem?_eq_getElem (by rw [har_len0]; omega),
                                Option.getD_some]
                              exact congrArg BitVec.toNat (getElem_congr (by c0_bound) _ _)
                            c0_hsteps_nogrp
                            refine wp_while_break_state
                              (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
                              (β := Bool × BitVec 32 × BitVec 32)
                              (fun x => (x.1, x.2.1, x.2.2, ()))
                              (fun (_ok_b, k_b, ci_b) mb => XorCollectInv c s R sz k_b ci_b mb)
                              (α := BitVec 32 × BitVec 32) (fun p => (p.1, p.2, ()))
                              (fun p => sz.toNat - p.2.toNat)
                              (fun (k_c, ci_c) mc => XorCollectInv c s R sz k_c ci_c mc)
                              ?_ ?_ ?_
                            · rintro B42 ⟨ok_b, k_b, ci_b⟩ mb
                                ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len, hscrc_out,
                                  h1092_bd, hnz_c, hmb⟩
                              c0_hsteps_nogrp
                              refine wp_join0
                                (P := fun mf =>
                                  ∃ (lmf : List (BitVec 8)) (scrf : List (BitVec 32)),
                                    lmf.length = 2 * c.max_vars ∧
                                    (∀ y < lmf.length, lmf[y]?.getD 0#8 = 0#8) ∧
                                    scrf.length = c.scratch_cap ∧
                                    (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                                      scrf[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                    (FullMem c (m7XorState s lmf scrf) ⋆ R) mf)
                                (fun _ mf ⟨lmf, scrf, h1, h2, h3, h4, hm⟩ => by
                                  c0_hsteps!; exact hJ34 mf ⟨lmf, scrf, h1, h2, h3, h4, hm⟩)
                                (fun J46 hJ46 => by
                                  c0_hsteps_nogrp
                                  refine wp_join0
                                    (P := fun mc' =>
                                      ∃ (lmc' : List (BitVec 8)) (scrc' : List (BitVec 32)),
                                        lmc'.length = 2 * c.max_vars ∧
                                        k_b.toNat ≤ 4 ∧ scrc'.length = c.scratch_cap ∧
                                        (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                                          scrc'[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                        (∀ j < k_b.toNat,
                                          (scrc'[1092 + j]?.getD 0#32).toNat <
                                            2 * s.core.cur_vars) ∧
                                        (∀ y < lmc'.length, lmc'[y]?.getD 0#8 ≠ 0#8 →
                                          ∃ j < k_b.toNat,
                                            y = (scrc'[1092 + j]?.getD 0#32).toNat ∨
                                            y = ((scrc'[1092 + j]?.getD 0#32) ^^^
                                              1#32).toNat) ∧
                                        (FullMem c (m7XorState s lmc' scrc') ⋆ R) mc')
                                    (fun _ mc' ⟨lmc', scrc', hlmc', hk', hscrc', hscrc_o',
                                        hbd', hnz', hmc'⟩ =>
                                      m7_xor_clean_lm_wp Γ c s lmc' scrc' R k_b mc' Q X _
                                        hlmc' hscrc' hsc1096 hk' hcv_le hbd'
                                        (fun y hy => hnz' y (by rw [hlmc']; exact hy)) hmc'
                                        (fun lm_cl hlm_cl_len hlm_cl_z m_cl hm_cl => by
                                          c0_hsteps!
                                          exact hJ46 m_cl ⟨lm_cl, scrc', hlm_cl_len,
                                            fun y hy => hlm_cl_z y (hlm_cl_len ▸ hy),
                                            hscrc', hscrc_o', hm_cl⟩))
                                    (fun J47 hJ47 => by
                                      c0_hsplit
                                      · c0_hsplit
                                        · have hk2 : 2 ≤ k_b.toNat := hc
                                          c0_hsplit
                                          · exact m7_xor_break_wp Γ c F0 F_cur s lmc scrc R
                                              np nn (v <<< 1#32) ((v <<< 1#32) ||| 1#32) i k_b mb
                                              Q X _ hXorPat hdw0 hlmc_len hscrc_len hsc1096 hnp512
                                              hnn512 hi_lt hk2 hk_le
                                              (fun i hi => by
                                                change FullBveEntryOkW F_cur s
                                                  (v <<< (1 : Nat)).toNat _
                                                rw [hpl_val]; exact hp_ok i hi)
                                              (fun j hj => by
                                                change FullBveEntryOkW F_cur s
                                                  ((v <<< (1 : Nat)) ||| 1#32).toNat _
                                                rw [hnl_val]; exact hn_ok j hj)
                                              hscrc_out h1092_bd hnz_c hmb
                                              (fun lmf scrf mf h1 h2 h3 h4 hm =>
                                                hJ46 mf ⟨lmf, scrf, h1, h2, h3, h4, hm⟩)
                                              hQ
                                          · c0_hsteps!; exact hJ47 mb ⟨lmc, scrc, hlmc_len, hk_le,
                                              hscrc_len, hscrc_out, h1092_bd, hnz_c, hmb⟩
                                        · c0_hsteps!; exact hJ47 mb ⟨lmc, scrc, hlmc_len, hk_le,
                                            hscrc_len, hscrc_out, h1092_bd, hnz_c, hmb⟩
                                      · c0_hsteps!; exact hJ47 mb ⟨lmc, scrc, hlmc_len, hk_le,
                                          hscrc_len, hscrc_out, h1092_bd, hnz_c, hmb⟩))
                            · rintro B42 L43 ⟨k_c, ci_c⟩ mc hB42 hL43
                                ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len, hscrc_out,
                                  h1092_bd, hnz_c, hmc⟩
                              c0_hsplit
                              · have hci_lt : ci_c.toNat < sz.toNat := hc
                                have hcri : (cr.setWidth 64 + 3#64 + ci_c.setWidth 64).toNat <
                                    s.core.arena.length := by
                                  rw [har_len0]; c0_bound
                                let l := s.core.arena[(cr.setWidth 64 + 3#64 +
                                  ci_c.setWidth 64).toNat]'hcri
                                have hl_mem :
                                    l.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat := by
                                  rw [mem_fullArenaClauseLitsCore_iff (by rw [har_len0]; omega)]
                                  exact ⟨ci_c.toNat, by omega,
                                    congrArg BitVec.toNat (getElem_congr (by c0_bound) _ _)⟩
                                have hl_lt : l.toNat < 2 * s.core.cur_vars :=
                                  hw0.arena.lits_lt cr.toNat href_cr hng_cr _ hl_mem
                                have hl_v : (l.setWidth 64).toNat < s.core.vals.length := by
                                  rw [hval_len0, zext32_toNat]; omega
                                have hl_lm : (l.setWidth 64).toNat < lmc.length := by
                                  rw [hlmc_len, zext32_toNat]; omega
                                have hci1 : (ci_c + 1#32).toNat = ci_c.toNat + 1 := by c0_bound
                                c0_hsteps_nogrp
                                refine wp_join_state (ts := [.bool, i32]) (α := Bool × BitVec 32)
                                  (fun x => (x.1, x.2, ()))
                                  (fun (_ok_s, k') ms => XorCollectInv c s R sz k' ci_c ms)
                                  (fun _ ⟨ok_s, k'⟩ ms hk_s => by
                                    c0_hsteps!
                                    obtain ⟨l_s, s_s, _, hks, h1s, h2s, h3s, h4s, h5s, hms⟩ := hk_s
                                    exact hL43 (k', ci_c + 1#32) ms
                                      (by dsimp only; rw [hci1]; omega)
                                      ⟨l_s, s_s, by rw [hci1]; omega, hks, h1s, h2s, h3s, h4s, h5s,
                                        hms⟩)
                                  (fun J54 hJ54 => by
                                    c0_hsplit
                                    · c0_hsplit
                                      · c0_hsteps!; exact hB42 (false, k_c, ci_c) mc
                                          ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len,
                                            hscrc_out, h1092_bd, hnz_c, hmc⟩
                                      · c0_hsteps_nogrp
                                        refine wp_join_state (ts := [.bool, i32])
                                          (α := Bool × BitVec 32) (fun x => (x.1, x.2, ()))
                                          (fun (_ok_s, k') ms => XorCollectInv c s R sz k' ci_c ms)
                                          (fun _ ⟨ok_s, k'⟩ ms hk_s => by
                                            c0_hsteps!; exact hJ54 (ok_s, k') ms hk_s)
                                          (fun J55 hJ55 => by
                                            c0_hsplit
                                            rotate_left
                                            · c0_hsteps!; exact hJ55 (true, k_c) mc
                                                ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len,
                                                  hscrc_out, h1092_bd, hnz_c, hmc⟩
                                            · c0_hsplit
                                              · c0_hsteps!; exact hB42 (false, k_c, ci_c) mc
                                                  ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len,
                                                    hscrc_out, h1092_bd, hnz_c, hmc⟩
                                              · c0_hsplit
                                                · c0_hsteps!; exact hB42 (false, k_c, ci_c) mc
                                                    ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len,
                                                      hscrc_out, h1092_bd, hnz_c, hmc⟩
                                                · c0_hsplit
                                                  · c0_hsteps!; exact hB42 (false, k_c, ci_c) mc
                                                      ⟨lmc, scrc, hci_le, hk_le, hlmc_len,
                                                        hscrc_len, hscrc_out, h1092_bd, hnz_c, hmc⟩
                                                  · have hk_lt4 : k_c.toNat < 4 := by c0_bound
                                                    have hl1_lt :
                                                        (l ^^^ 1#32).toNat < 2 * s.core.cur_vars :=
                                                      xor1_lt l hl_lt
                                                    have hl1_lm :
                                                        ((l ^^^ 1#32).setWidth 64).toNat <
                                                          lmc.length := by
                                                      rw [hlmc_len, zext32_toNat]; omega
                                                    have hl_sc :
                                                        (l.setWidth 64).toNat < lmc.length := hl_lm
                                                    have h1092_k :
                                                        ((1092#32 + k_c).setWidth 64).toNat <
                                                          scrc.length := by
                                                      rw [hscrc_len]; c0_bound
                                                    have hk1 :
                                                        (k_c + 1#32).toNat = k_c.toNat + 1 := by
                                                      c0_bound
                                                    c0_hsteps_nogrp
                                                    have hl1_set :
                                                        ((l ^^^ 1#32).setWidth 64).toNat <
                                                          (lmc.set (l.setWidth 64).toNat
                                                            (BitVec.setWidth 8
                                                              (2#32 + (k_c <<< 1#32)))).length := by
                                                      rw [List.length_set]; exact hl1_lm
                                                    c0_hsteps!
                                                    have hm_n :
                                                        (FullMem c (m7XorState s
                                                          ((lmc.set (l.setWidth 64).toNat
                                                              (BitVec.setWidth 8
                                                                (2#32 + (k_c <<< 1#32)))).set
                                                            ((l ^^^ 1#32).setWidth 64).toNat
                                                            (BitVec.setWidth 8
                                                              (3#32 + (k_c <<< 1#32))))
                                                          (scrc.set
                                                            ((1092#32 + k_c).setWidth 64).toNat l))
                                                            ⋆ R) _ := hm
                                                    refine hJ55 (true, k_c + 1#32) _
                                                      ⟨_, _, hci_le, by omega,
                                                        by rw [List.length_set, List.length_set,
                                                             hlmc_len],
                                                        by rw [List.length_set, hscrc_len],
                                                        fun idx hi hor => by
                                                          rw [List.getElem?_set_ne (by c0_bound)]
                                                          exact hscrc_out idx hi hor,
                                                        fun j hj => by
                                                          by_cases hjk : j = k_c.toNat
                                                          · subst hjk
                                                            rw [show 1092 + k_c.toNat =
                                                                ((1092#32 + k_c).setWidth 64).toNat
                                                                  by c0_bound,
                                                              List.getElem?_set_self h1092_k,
                                                              Option.getD_some]
                                                            exact hl_lt
                                                          · rw [List.getElem?_set_ne (by c0_bound)]
                                                            exact h1092_bd j (by omega),
                                                        fun y hy hyn => ?_, hm_n⟩
                                                    by_cases hyl : y = l.toNat
                                                    · refine ⟨k_c.toNat, by omega, Or.inl ?_⟩
                                                      rw [show 1092 + k_c.toNat =
                                                          ((1092#32 + k_c).setWidth 64).toNat by
                                                            c0_bound,
                                                        List.getElem?_set_self h1092_k,
                                                        Option.getD_some]
                                                      exact hyl
                                                    · by_cases hyl1 : y = (l ^^^ 1#32).toNat
                                                      · refine ⟨k_c.toNat, by omega, Or.inr ?_⟩
                                                        rw [show 1092 + k_c.toNat =
                                                            ((1092#32 + k_c).setWidth 64).toNat by
                                                              c0_bound,
                                                          List.getElem?_set_self h1092_k,
                                                          Option.getD_some]
                                                        exact hyl1
                                                      · rw [List.getElem?_set_ne (by
                                                            rw [zext32_toNat]; exact Ne.symm hyl1),
                                                          List.getElem?_set_ne (by
                                                            rw [zext32_toNat]; exact Ne.symm hyl)]
                                                          at hyn
                                                        obtain ⟨jj, hjj, hyeq⟩ := hnz_c y
                                                          (by rw [List.length_set, List.length_set]
                                                                at hy
                                                              exact hy)
                                                          hyn
                                                        refine ⟨jj, by omega, ?_⟩
                                                        have h1092_ne :
                                                            ((1092#32 + k_c).setWidth 64).toNat ≠
                                                              1092 + jj := by
                                                          rw [show ((1092#32 + k_c).setWidth 64
                                                                ).toNat = 1092 + k_c.toNat by
                                                                c0_bound]
                                                          omega
                                                        rwa [List.getElem?_set_ne h1092_ne])
                                    · c0_hsteps!; exact hJ54 (true, k_c) mc
                                        ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len, hscrc_out,
                                          h1092_bd, hnz_c, hmc⟩)
                              · c0_hsteps!; exact hB42 (true, k_c, ci_c) mc
                                  ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len, hscrc_out,
                                    h1092_bd, hnz_c, hmc⟩
                            · intro B42 L43 hB42 hL43
                              c0_hsteps!
                              exact hL43 (0#32, 0#32) mi
                                ⟨lmi, scri, Nat.zero_le _, Nat.zero_le _, hlmi_len, hscri_len,
                                  hscri_out, fun _ hj => False.elim (Nat.not_lt_zero _ hj),
                                  fun y hy hyn => False.elim (hyn (by
                                    simpa [List.getElem?_eq_getElem hy] using hlmi_z y hy)),
                                  hmi⟩
                          · c0_hsteps!
                            exact hJ34 mi ⟨lmi, scri, hlmi_len, hlmi_z, hscri_len, hscri_out, hmi⟩)
                    · c0_hsteps!
                      exact hQ false lmi scri mi hdw_i hscri_len hscri_out hmi
                  · intro L3 hL3; c0_hsteps!
                    exact hL3 np.toNat (0#32, ()) m0
                      ⟨s.core.lit_mark, s.scratch.scratch_buf, hlm_len0,
                        fun y hy => hlm0_clr.2 y (by rw [hlm_len0] at hy; exact hy),
                        hscr_len0, fun _ _ _ => rfl, Nat.zero_le _, by simp, hm0⟩
        · intro L2 hL2; c0_hsteps!
          exact hL2 nn.toNat (0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp⟩
    · intro L hL; c0_hsteps!
      exact hL np.toNat (0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Gates
