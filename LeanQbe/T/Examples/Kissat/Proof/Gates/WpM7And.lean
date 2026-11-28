/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.WpHelpers
import LeanQbe.T.Logic.C0Grind

/-!
# Kissat Gates WP Proofs — M7 AND (`full_bve_find_and_m7`)

`CanonicalEnv`-clean `Func.wp` proof for `full_bve_find_and_m7`
(`0` legacy `Full*` imports; every decl `<= 450` LOC; total file `<= 1,500` LOC).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.C0Grind LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Gates
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

public section

private theorem m7_xor1_zext64_inv (l : BitVec 32) :
    ((l ^^^ 1#32).setWidth 64).toNat ^^^ 1 = l.toNat := by
  have h : (l ^^^ 1#32) ^^^ 1#32 = l := by c0_bv_bit_grind
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl] at this
  rwa [zext32_toNat]

private theorem m7_xor1_zext64_lt {lm : List (BitVec 8)} {mv : Nat} {l : BitVec 32}
    (hlm : lm.length = 2 * mv) (hlt : l.toNat ^^^ 1 < 2 * mv) :
    ((l ^^^ 1#32).setWidth 64).toNat < lm.length := by
  rw [hlm, zext32_toNat, BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
  exact hlt

private theorem m7_and_pol_cases (lit : BitVec 32) :
    (((lit &&& 1#32) <<< 9).toNat = 0 ∧ (512#32 - ((lit &&& 1#32) <<< 9)).toNat = 512 ∧
      (1024#32 + ((lit &&& 1#32) <<< 4)).toNat = 1024 ∧
      (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))).toNat = 1040) ∨
    (((lit &&& 1#32) <<< 9).toNat = 512 ∧ (512#32 - ((lit &&& 1#32) <<< 9)).toNat = 0 ∧
      (1024#32 + ((lit &&& 1#32) <<< 4)).toNat = 1040 ∧
      (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))).toNat = 1024) := by
  have h : lit &&& 1#32 = 0#32 ∨ lit &&& 1#32 = 1#32 := by
    have hlt : (lit &&& 1#32).toNat < 2 := by
      rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h0 | h1
    · left; apply BitVec.eq_of_toNat_eq
      rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega
    · right; apply BitVec.eq_of_toNat_eq; exact h1
  rcases h with h0 | h1
  · left; rw [h0]; exact ⟨by decide, by decide, by decide, by decide⟩
  · right; rw [h1]; exact ⟨by decide, by decide, by decide, by decide⟩

private def m7AndClearOppExpr (pScr pLm : Val i64) (oppOff oppN : Val i32)
    (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32]]) (fun Js =>
    Blocks.cons (fun p_14 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p_14.fst, Arg.var oppN, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var oppOff, Arg.var p_14.fst, ()) }
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
    Expr.group (sig := [[]]) (fun _Js_1 =>
    Blocks.cons (fun _p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_14.fst, Arg.imm 1, ()) }
    fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld, Arg.imm 2147483648, ()) }
    fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var p.fst, Arg.imm 0, ()) } fun p
    =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld, Arg.imm 2147483647, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLm, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_15 =>
    Expr.store (Arg.var p_15.fst) (Arg.var p.fst) (Expr.jump Js.fst ())) (Expr.jump Js.fst
    ())) (k))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, ())

private def m7AndUnmarkTailExpr (pAr pScr pLm : Val i64)
    (litMask oppMask foundI wf fsz lit matched uniqNeed : Val i32) :
    Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32]]) (fun Js =>
    Blocks.cons (fun p_30 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p_30.fst, Arg.var fsz, ()) }
    fun p_31 =>
    Expr.jnz (Arg.var p_31.fst) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var wf, ()) } fun p_32 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.fst, Arg.imm 3, ()) }
    fun p_33 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_30.fst, ()) } fun
    p_34 =>
    Expr.let_
    { sig := [i64, i64],
      code := OpCode.add i64,
      args := (Arg.var p_33.fst, Arg.var p_34.fst, ()) }
     fun p_35 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_35.fst, Arg.imm 4, ()) }
    fun p_36 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pAr, Arg.var p_36.fst, ()) }
    fun p_37 =>
    Expr.load i32 (Arg.var p_37.fst) fun ld =>
    Expr.group (sig := [[]]) (fun _Js_1 =>
    Blocks.cons (fun _p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_30.fst, Arg.imm 1, ()) }
    fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var ld, Arg.var lit, ()) } fun p
    =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.xor i32, args := (Arg.var ld, Arg.imm 1, ()) } fun p
    =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLm, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_38 =>
    Expr.store (Arg.var p_38.fst) (Arg.var p.fst) (Expr.jump Js.fst ())) (Expr.jump Js.fst
    ()))
    (Expr.group (sig := [[]]) (fun _Js =>
    Blocks.cons (fun __ =>
    Expr.group (sig := [[i32]]) (fun Js =>
    Blocks.cons (fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p.fst, Arg.imm 16, ()) } fun
    p_32 =>
    Expr.jnz (Arg.var p_32.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var oppMask, Arg.var p.fst, ()) }
    fun p_33 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_33.fst, ()) } fun
    p_34 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_34.fst, Arg.imm 4, ()) }
    fun p_35 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p_35.fst, ()) }
    fun p_36 =>
    Expr.store (Arg.imm (t := i32) 0) (Arg.var p_36.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p.fst, Arg.imm 1, ()) } fun
    p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))) (Expr.ret (Arg.imm false, ())))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var matched, Arg.var uniqNeed, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.uge i32, args := (Arg.var uniqNeed, Arg.imm 1, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var foundI, Arg.imm 5, ()) }
    fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var litMask, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun
    p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var foundI, Arg.imm 31, ()) }
    fun p_32 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.shl i32, args := (Arg.imm 1, Arg.var p_32.fst, ()) }
    fun p_33 =>
    Expr.store (Arg.var p_33.fst) (Arg.var p.fst) (Expr.let_
    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1056, ()) } fun p =>
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
    (Expr.jump Js.fst ())) (Expr.jump Js.fst ())))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, ())

private def m7AndCandExpr (pAr pScr pLm pVals : Val i64)
    (oppOff oppN litMask oppMask foundI wf fsz lit : Val i32) :
    Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, i32]]) (fun Js =>
    Blocks.cons (fun p_26 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p_26.snd.fst, Arg.var fsz, ()) }
    fun p_27 =>
    Expr.jnz (Arg.var p_27.fst) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var wf, ()) } fun p_28 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_28.fst, Arg.imm 3, ()) }
    fun p_29 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_26.snd.fst, ()) }
    fun p_30 =>
    Expr.let_
    { sig := [i64, i64],
      code := OpCode.add i64,
      args := (Arg.var p_29.fst, Arg.var p_30.fst, ()) }
     fun p_31 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_31.fst, Arg.imm 4, ()) }
    fun p_32 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pAr, Arg.var p_32.fst, ()) }
    fun p_33 =>
    Expr.load i32 (Arg.var p_33.fst) fun ld =>
    Expr.group (sig := [[i32]]) (fun _Js_1 =>
    Blocks.cons (fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_26.snd.fst, Arg.imm 1, ()) }
    fun p_34 =>
    Expr.jump Js.fst (Arg.var p.fst, Arg.var p_34.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var ld, Arg.var lit, ()) } fun p
    =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pVals, Arg.var p.fst, ()) }
    fun p =>
    Expr.load i8 (Arg.var p.fst) fun ld_6 =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p =>
    Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld_6, ()) } fun p_34
    =>
    Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var p.fst, ()) } fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_34.fst, Arg.var p.fst, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.xor i32, args := (Arg.var ld, Arg.imm 1, ()) } fun p
    =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLm, Arg.var p.fst, ()) }
    fun p =>
    Expr.load i8 (Arg.var p.fst) fun ld_7 =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p =>
    Expr.let_ { sig := [i8], code := OpCode.zext 8 32, args := (Arg.var ld_7, ()) } fun p_35
    =>
    Expr.let_ { sig := [i8], code := OpCode.zext 8 32, args := (Arg.var p.fst, ()) } fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_35.fst, Arg.var p.fst, ()) }
    fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.xor i32, args := (Arg.var ld, Arg.imm 1, ()) } fun p
    =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p
    =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLm, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 1, ()) } fun p_36 =>
    Expr.store (Arg.var p_36.fst) (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_26.fst, Arg.imm 1, ()) }
    fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))) (Expr.jump Js.fst (Arg.var p_26.fst, ())))
    (Expr.jump Js.fst (Arg.var p_26.fst, ()))) (Expr.jump Js.fst (Arg.var p_26.fst, ())))
    (Expr.group (sig := [[i32, i32]]) (fun Js =>
    Blocks.cons (fun p_28 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ult i32, args := (Arg.var p_28.fst, Arg.var oppN, ()) }
    fun p_29 =>
    Expr.jnz (Arg.var p_29.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var oppOff, Arg.var p_28.fst, ()) }
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
    Expr.group (sig := [[i32]]) (fun _Js_1 =>
    Blocks.cons (fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_28.fst, Arg.imm 1, ()) }
    fun p_30 =>
    Expr.jump Js.fst (Arg.var p_30.fst, Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld, Arg.imm 2147483648, ()) }
    fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.ne i32, args := (Arg.var p.fst, Arg.imm 0, ()) } fun p
    =>
    Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld, Arg.imm 2147483647, ()) }
    fun p =>
    Expr.group (sig := [[i32]]) (fun _Js_1 =>
    Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun
    p_30 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLm, Arg.var p_30.fst, ()) }
    fun p_31 =>
    Expr.load i8 (Arg.var p_31.fst) fun ld =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 1, ()) } fun p_32 =>
    Expr.let_ { sig := [i8], code := OpCode.zext 8 32, args := (Arg.var ld, ()) } fun p_33 =>
    Expr.let_ { sig := [i8], code := OpCode.zext 8 32, args := (Arg.var p_32.fst, ()) } fun
    p_34 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.eq i32, args := (Arg.var p_33.fst, Arg.var p_34.fst, ()) }
    fun p_35 =>
    Expr.jnz (Arg.var p_35.fst) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLm, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_36 =>
    Expr.store (Arg.var p_36.fst) (Arg.var p.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var p_28.fst, Arg.imm 5, ()) }
    fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var oppMask, Arg.var p.fst, ()) }
    fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun
    p_37 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_37.fst, Arg.imm 4, ()) }
    fun p_38 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pScr, Arg.var p_38.fst, ()) }
    fun p_39 =>
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
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var p_28.fst, Arg.imm 31, ()) }
    fun p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.shl i32, args := (Arg.imm 1, Arg.var p.fst, ()) } fun
    p =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.or i32, args := (Arg.var ld, Arg.var p.fst, ()) } fun
    p =>
    Expr.store (Arg.var p.fst) (Arg.var p_39.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_28.snd.fst, Arg.imm 1, ()) }
    fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ())))) (Expr.jump Js.fst (Arg.var p_28.snd.fst, ())))
    (Expr.jump Js.fst (Arg.var p_28.snd.fst, ()))) (m7AndUnmarkTailExpr pAr pScr pLm litMask
    oppMask foundI wf fsz lit p_28.snd.fst p_26.fst))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())

private theorem m7_and_clear_opp_wp (Γ : Env) (c : FullCfg) (F_cur : List (List Nat))
    (s0 : FullState) (R : Mem 64 → Prop) (opp_off opp_n lit : BitVec 32)
    (lm1 : List (BitVec 8)) (m1 : Mem 64) (Q : Post [.bool]) (X : XPost)
    (k : Expr Val Cont [.bool])
    (_hmx : c.max_vars < 2 * 2 ^ 28) (hsc : c.scratch_cap < 2 ^ 28)
    (hsc1088 : 1088 ≤ c.scratch_cap) (hsb : s0.scratch.scratch_buf.length = c.scratch_cap)
    (hlm1 : lm1.length = 2 * c.max_vars)
    (hoo : opp_off.toNat + opp_n.toNat ≤ 1024) (hon : opp_n.toNat ≤ 512)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hn_ok : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s0 (lit.toNat ^^^ 1)
      (s0.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32))
    (hmk1 : ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
      ∃ u < opp_n.toNat, let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat)
    (hm1 : (FullMem c { s0 with core := { s0.core with lit_mark := lm1 } } ⋆ R) m1)
    (hk : ∀ (lm2 : List (BitVec 8)) (m2 : Mem 64),
      lm2.length = 2 * c.max_vars →
      (∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 = 0#8) →
      (FullMem c { s0 with core := { s0.core with lit_mark := lm2 } } ⋆ R) m2 →
      wp Γ Q X k m2) :
    wp Γ Q X (m7AndClearOppExpr c.pScratchBuf c.pLitMark opp_off opp_n k) m1 := by
  unfold m7AndClearOppExpr
  refine wp_loop_group (ts := [i32])
    (fun rem2 (jc, ()) m2 => ∃ lm2 : List (BitVec 8),
      let s2 : FullState := { s0 with core := { s0.core with lit_mark := lm2 } }
      lm2.length = 2 * c.max_vars ∧ jc.toNat ≤ opp_n.toNat ∧ rem2 = opp_n.toNat - jc.toNat ∧
      (∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 ≠ 0#8 →
        ∃ u, jc.toNat ≤ u ∧ u < opp_n.toNat ∧
          let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
          (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
      (FullMem c s2 ⋆ R) m2)
    ?_ ?_
  · rintro L2 rem2 ⟨jc, ⟨⟩⟩ m2 hL2 ⟨lm2, hlm2, hjc_le, rfl, hrem2, hm2⟩
    c0_hsplit
    · have hjc_lt : jc.toNat < opp_n.toNat := hc
      have hoj_sc : ((opp_off + jc).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
        rw [hsb, zext32_toNat]; c0_bound
      have hoj_eq : ((opp_off + jc).setWidth 64).toNat = opp_off.toNat + jc.toNat := by
        rw [zext32_toNat]; c0_bound
      let wc := s0.scratch.scratch_buf[((opp_off + jc).setWidth 64).toNat]'hoj_sc
      have hwc_get : s0.scratch.scratch_buf[opp_off.toNat + jc.toNat]?.getD 0#32 = wc := by
        rw [List.getElem?_eq_getElem (by rw [hsb]; omega), Option.getD_some]
        exact getElem_congr hoj_eq.symm _ hoj_sc
      have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun _ m2' => ∃ lm2' : List (BitVec 8),
          let s2' : FullState := { s0 with core := { s0.core with lit_mark := lm2' } }
          lm2'.length = 2 * c.max_vars ∧
          (∀ x < 2 * c.max_vars, lm2'[x]?.getD 0#8 ≠ 0#8 →
            ∃ u, jc.toNat + 1 ≤ u ∧ u < opp_n.toNat ∧
              let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
              (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
          (FullMem c s2' ⋆ R) m2')
        (fun _ _ m2' ⟨lm2', hlm2', hrem2', hm2'⟩ => by
          c0_hsteps!
          exact hL2 (opp_n.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) m2' (by omega)
            ⟨lm2', hlm2', by omega, rfl, fun y hy hnz => by
              obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2' y hy hnz
              exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm2'⟩)
        (fun _ hJ2 => by
          c0_hsplit
          · have hwc_bin : (wc &&& 0x80000000#32) ≠ 0#32 := hc
            have hot_lt : (wc &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
              have h1 := hn_ok jc.toNat hjc_lt; rw [hwc_get] at h1
              unfold FullBveEntryOkW at h1; rw [ite_eq_left hwc_bin] at h1; exact h1.1
            have hot_lm : ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm2.length := by
              rw [hlm2, zext32_toNat]; omega
            c0_hsteps!
            refine hJ2 () _
              ⟨lm2.set ((wc &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8, by simp [hlm2],
               lm_clear_step_maxv hlm2 (by rw [zext32_toNat]; omega) (fun y hy hnz => by
                 obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2 y hy hnz
                 rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                 · left; rw [zext32_toNat, hyeq, hwc_get]
                 · right; exact ⟨u, by omega, hu2, hwu, hyeq⟩), hm⟩
          · c0_hsteps!
            refine hJ2 () m2
              ⟨lm2, hlm2, fun y hy hnz => by
                obtain ⟨u, hu1, hu2, hwu, hyeq⟩ := hrem2 y hy hnz
                rcases Nat.eq_or_lt_of_le hu1 with rfl | hgt
                · have hwc_c0 :
                      s0.scratch.scratch_buf[(opp_off.toNat + jc.toNat) % 2 ^ 32]'(by
                        rw [hsb, Nat.mod_eq_of_lt (by omega)]; omega) = wc := by
                    rw [← hwc_get, List.getElem?_eq_getElem (by rw [hsb]; omega),
                      Option.getD_some]
                    exact getElem_congr (Nat.mod_eq_of_lt (by omega)) _ _
                  have h0 := hc; rw [hwc_c0] at h0; rw [hwc_get] at hwu
                  exact absurd h0 hwu
                · exact ⟨u, by omega, hu2, hwu, hyeq⟩, hm2⟩)
    · have hclr2 : ∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 = 0#8 := fun x hx =>
        Classical.byContradiction fun hnz => by
          obtain ⟨u, hu1, hu2, _⟩ := hrem2 x hx hnz; omega
      exact hk lm2 m2 hlm2 hclr2 hm2
  · intro L2 hL2; c0_hsteps!
    exact hL2 opp_n.toNat (0#32, ()) m1
      ⟨lm1, hlm1, Nat.zero_le _, by simp, fun x hx hnz => by
        obtain ⟨u, hu, hw⟩ := hmk1 x hx hnz; exact ⟨u, Nat.zero_le _, by omega, hw⟩, hm1⟩

private theorem m7_and_unmark_tail_wp (Γ : Env) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s0 : FullState) (R : Mem 64 → Prop)
    (litMask oppMask foundI wf fsz lit matched uniqNeed : BitVec 32)
    (lm4 : List (BitVec 8)) (scr4 : List (BitVec 32)) (m4 : Mem 64)
    (Q : Post [.bool]) (X : XPost)
    (_hmx : c.max_vars < 2 * 2 ^ 28) (hsc : c.scratch_cap < 2 ^ 28)
    (harc : c.arena_cap < 2 * 2 ^ 28) (hdw0 : FullDenseInvW c F0 F_cur s0)
    (hsc1088 : 1088 ≤ c.scratch_cap) (hfi_lt : foundI.toNat < 512)
    (hlm1 : 1024 ≤ litMask.toNat) (hlm2 : litMask.toNat + 16 ≤ 1056)
    (hom1 : 1024 ≤ oppMask.toNat) (hom2 : oppMask.toNat + 16 ≤ 1056)
    (hwf_f : wf.toNat ∈ fullArenaClauseRefs s0)
    (hwf_ng : fullArenaClauseGarb s0 wf.toNat = false)
    (hfsz_eq : fsz.toNat = fullArenaClauseSizeCore s0.core wf.toNat)
    (hlm4 : lm4.length = 2 * c.max_vars) (hsc4 : scr4.length = c.scratch_cap)
    (hmk4 : ∀ x < 2 * c.max_vars, lm4[x]?.getD 0#8 ≠ 0#8 →
      (x ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧ (x ^^^ 1) ≠ lit.toNat)
    (hout4 : ∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
      scr4[i]? = s0.scratch.scratch_buf[i]?)
    (hm4 : (FullMem c { s0 with
        core := { s0.core with lit_mark := lm4 }
        scratch := { s0.scratch with scratch_buf := scr4 } } ⋆ R) m4)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s0 with
          core := { s0.core with lit_mark := lm' }
          scratch := { s0.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
        scr'[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (m7AndUnmarkTailExpr c.pArena c.pScratchBuf c.pLitMark
      litMask oppMask foundI wf fsz lit matched uniqNeed) m4 := by
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hwf_wf := hdw0.2.1.arena.refs_wf wf.toNat hwf_f
  have hwf_bd : wf.toNat + 3 + fullArenaClauseSizeCore s0.core wf.toNat ≤ c.arena_cap := by
    have := hwf_wf.2.2.1; have := hwf_wf.2.2.2.1; omega
  unfold m7AndUnmarkTailExpr
  refine wp_loop_group (ts := [i32])
    (fun rem5 (ku, ()) m5 => ∃ lm5 : List (BitVec 8),
      let s5 : FullState :=
        { s0 with core := { s0.core with lit_mark := lm5 }
                  scratch := { s0.scratch with scratch_buf := scr4 } }
      lm5.length = 2 * c.max_vars ∧ ku.toNat ≤ fsz.toNat ∧ rem5 = fsz.toNat - ku.toNat ∧
      (∀ x < 2 * c.max_vars, lm5[x]?.getD 0#8 ≠ 0#8 →
        ∃ t, ku.toNat ≤ t ∧ t < fsz.toNat ∧
          (x ^^^ 1) = (s0.core.arena[wf.toNat + 3 + t]?.getD 0#32).toNat ∧
          (x ^^^ 1) ≠ lit.toNat) ∧
      (FullMem c s5 ⋆ R) m5)
    ?_ ?_
  · rintro L5 rem5 ⟨ku, ⟨⟩⟩ m5 hL5 ⟨lm5, hlm5, hku_le, rfl, hrem5, hm5⟩
    c0_hsplit
    · have hku_lt : ku.toNat < fsz.toNat := hc
      have hwk_eq : (wf.setWidth 64 + 3#64 + ku.setWidth 64).toNat =
          wf.toNat + 3 + ku.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, zext32_toNat, zext32_toNat,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hwk : (wf.setWidth 64 + 3#64 + ku.setWidth 64).toNat < s0.core.arena.length := by
        rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
      let lu := s0.core.arena[(wf.setWidth 64 + 3#64 + ku.setWidth 64).toNat]'hwk
      have hlu_get : s0.core.arena[wf.toNat + 3 + ku.toNat]?.getD 0#32 = lu := by
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
          Option.getD_some]
        exact getElem_congr hwk_eq.symm _ hwk
      have hlu_mem : lu.toNat ∈ fullArenaClauseLitsCore s0.core wf.toNat := by
        rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
        exact ⟨ku.toNat, by omega, congrArg BitVec.toNat (getElem_congr hwk_eq.symm _ _)⟩
      have hlu_lt : lu.toNat < 2 * s0.core.cur_vars :=
        hdw0.2.1.arena.lits_lt wf.toNat hwf_f hwf_ng _ hlu_mem
      have hlun_lt : lu.toNat ^^^ 1 < 2 * s0.core.cur_vars := by
        have := fullInv_var_xor1 lu.toNat; omega
      have hlun_lm : ((lu ^^^ 1#32).setWidth 64).toNat < lm5.length :=
        m7_xor1_zext64_lt hlm5 (by omega)
      have hlun_inv : ((lu ^^^ 1#32).setWidth 64).toNat ^^^ 1 = lu.toNat :=
        m7_xor1_zext64_inv lu
      have hku1 : (ku + 1#32).toNat = ku.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun _ m5' => ∃ lm5' : List (BitVec 8),
          let s5' : FullState :=
            { s0 with core := { s0.core with lit_mark := lm5' }
                      scratch := { s0.scratch with scratch_buf := scr4 } }
          lm5'.length = 2 * c.max_vars ∧
          (∀ x < 2 * c.max_vars, lm5'[x]?.getD 0#8 ≠ 0#8 →
            ∃ t, ku.toNat + 1 ≤ t ∧ t < fsz.toNat ∧
              (x ^^^ 1) = (s0.core.arena[wf.toNat + 3 + t]?.getD 0#32).toNat ∧
              (x ^^^ 1) ≠ lit.toNat) ∧
          (FullMem c s5' ⋆ R) m5')
        (fun _ _ m5' ⟨lm5', hlm5', hrem5', hm5'⟩ => by
          c0_hsteps!
          exact hL5 (fsz.toNat - (ku + 1#32).toNat) (ku + 1#32, ()) m5' (by omega)
            ⟨lm5', hlm5', by omega, rfl, fun y hy hnz => by
              obtain ⟨t, ht1, ht2, hyeq, hne⟩ := hrem5' y hy hnz
              exact ⟨t, by omega, ht2, hyeq, hne⟩, hm5'⟩)
        (fun _ hJ5 => by
          c0_hsplit
          · c0_hsteps!
            refine hJ5 () _
              ⟨lm5.set ((lu ^^^ 1#32).setWidth 64).toNat 0#8, by simp [hlm5],
               lm_clear_step_maxv hlm5 (by rw [← hlm5]; exact hlun_lm)
                 (fun y hy hnz => by
                   obtain ⟨t, ht1, ht2, hyeq, hne⟩ := hrem5 y hy hnz
                   rcases Nat.eq_or_lt_of_le ht1 with rfl | hgt
                   · left
                     have hbv : (BitVec.ofNat 32 y) ^^^ 1#32 = lu := by
                       apply BitVec.eq_of_toNat_eq
                       rw [BitVec.toNat_xor, BitVec.toNat_ofNat,
                         Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
                         show (1 : Nat) % 2 ^ 32 = 1 from rfl, hyeq, hlu_get]
                     have hbv2 : BitVec.ofNat 32 y = lu ^^^ 1#32 := by
                       rw [← hbv, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
                     have hbv3 := congrArg BitVec.toNat hbv2
                     rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hbv3
                     rw [zext32_toNat, hbv3]
                   · right; exact ⟨t, by omega, ht2, hyeq, hne⟩), hm⟩
          · c0_hsteps!
            refine hJ5 () m5
              ⟨lm5, hlm5, fun y hy hnz => by
                obtain ⟨t, ht1, ht2, hyeq, hne⟩ := hrem5 y hy hnz
                rcases Nat.eq_or_lt_of_le ht1 with rfl | hgt
                · have hlu_eq : lu = lit :=
                    (getElem_congr (by
                      have h3 : BitVec.toNat (3 : BitVec 64) = 3 := rfl
                      rw [hwk_eq, h3, Nat.mod_eq_of_lt (by omega)]) _ _).trans hc
                  have hc0 : (y ^^^ 1) = lit.toNat := by rw [hyeq, hlu_get, hlu_eq]
                  exact absurd hc0 hne
                · exact ⟨t, by omega, ht2, hyeq, hne⟩, hm5⟩)
    · have hfsz_le_ku : fsz.toNat ≤ ku.toNat := by omega
      have hclr5 : ∀ x < 2 * c.max_vars, lm5[x]?.getD 0#8 = 0#8 :=
        fun x hx => Classical.byContradiction fun hnz => by
          obtain ⟨t, ht1, ht2, _⟩ := hrem5 x hx hnz; omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ mf => mf = m5)
        (fun _ _ mf hmf => by
          subst mf
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem6 (kc, ()) m6 => ∃ scr6 : List (BitVec 32),
              let s6 : FullState :=
                { s0 with core := { s0.core with lit_mark := lm5 }
                          scratch := { s0.scratch with scratch_buf := scr6 } }
              scr6.length = c.scratch_cap ∧ kc.toNat ≤ 16 ∧ rem6 = 16 - kc.toNat ∧
              (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
                scr6[i]? = s0.scratch.scratch_buf[i]?) ∧
              (FullMem c s6 ⋆ R) m6)
            ?_ ?_
          · rintro L6 rem6 ⟨kc, ⟨⟩⟩ m6 hL6 ⟨scr6, hsc6, hkc_le, rfl, hout6, hm6⟩
            c0_hsplit
            · have hkc_lt : kc.toNat < 16 := hc
              have hokc : ((oppMask + kc).setWidth 64).toNat < scr6.length := by
                rw [hsc6, zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
              have hokc_b : 1024 ≤ ((oppMask + kc).setWidth 64).toNat ∧
                  ((oppMask + kc).setWidth 64).toNat < 1056 := by
                rw [zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
              have hkc1 : (kc + 1#32).toNat = kc.toNat + 1 := by c0_bound
              c0_hsteps!
              exact hL6 (16 - (kc + 1#32).toNat) (kc + 1#32, ()) _ (by omega)
                ⟨scr6.set ((oppMask + kc).setWidth 64).toNat 0#32,
                 by simp [hsc6], by omega, rfl, fun idx hidx hor => by
                   rw [List.getElem?_set_ne (by
                     rw [zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega)]
                   exact hout6 idx hidx hor, hm⟩
            · have hdw6 := fullDenseInvW_lm_scr hdw0 hlm5 hclr5 hsc6
              c0_hsteps!
              exact hQ false lm5 scr6 m6 hdw6 hsc6 hout6 hm6
          · intro L6 hL6; c0_hsteps!
            exact hL6 16 (0#32, ()) m5 ⟨scr4, hsc4, Nat.zero_le _, by simp, hout4, hm5⟩)
        (fun _ hJfin => by
          c0_hsplit
          · c0_hsplit
            · have hfim : (litMask + (foundI >>> (5 : Nat))).toNat < scr4.length := by
                have h1 := m7_mask_lt_16 foundI (by omega)
                rw [hsc4, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
              have hfim_idx :
                  ((litMask + (foundI >>> (5 : Nat))).setWidth 64).toNat =
                    litMask.toNat + foundI.toNat / 32 := by
                have h1 := m7_mask_lt_16 foundI (by omega)
                rw [zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight,
                  Nat.shiftRight_eq_div_pow, show 2 ^ 5 = 32 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              have hfim_bd : litMask.toNat + foundI.toNat / 32 < 1056 := by
                have := m7_mask_lt_16 foundI (by omega); omega
              have h1056 : 1056 < scr4.length := by rw [hsc4]; omega
              have h1057 : 1057 < scr4.length := by rw [hsc4]; omega
              c0_hsteps!
              refine hQ true lm5 ?_ m ?_ ?_ ?_ ?_
              rotate_left 4
              · exact hm
              · exact fullDenseInvW_lm_scr hdw0 hlm5 hclr5 (by simp [hsc4])
              · simp [hsc4]
              · intro idx hidx hor
                rw [hfim_idx,
                  List.getElem?_set_ne (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                  List.getElem?_set_ne (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                  List.getElem?_set_ne (by omega)]
                exact hout4 idx hidx hor
            · c0_hsteps!; exact hJfin () m5 rfl
          · c0_hsteps!; exact hJfin () m5 rfl)
  · intro L5 hL5; c0_hsteps!
    exact hL5 fsz.toNat (0#32, ()) m4
      ⟨lm4, hlm4, Nat.zero_le _, by simp, fun x hx hnz => by
        obtain ⟨hm_mem, hm_ne⟩ := hmk4 x hx hnz
        rw [mem_fullArenaClauseLitsCore_iff (by
          rw [hdw0.1.core_ok.arena_len_arr]; omega)] at hm_mem
        obtain ⟨t, ht, hxt⟩ := hm_mem
        exact ⟨t, Nat.zero_le _, by omega, by
          rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
            Option.getD_some]
          exact hxt.symm, hm_ne⟩, hm4⟩

private theorem m7_and_cand_wp (Γ : Env) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (R : Mem 64 → Prop)
    (opp_off opp_n lit_mask opp_mask found_i wf fsz lit : BitVec 32)
    (lm2 : List (BitVec 8)) (m2 : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hmx : c.max_vars < 2 * 2 ^ 28) (hsc : c.scratch_cap < 2 ^ 28)
    (harc : c.arena_cap < 2 * 2 ^ 28) (hdw0 : FullDenseInvW c F0 F_cur s0)
    (hsc1088 : 1088 ≤ c.scratch_cap)
    (hoo : opp_off.toNat + opp_n.toNat ≤ 1024) (hon : opp_n.toNat ≤ 512)
    (hlm1_b : 1024 ≤ lit_mask.toNat) (hlm2_b : lit_mask.toNat + 16 ≤ 1056)
    (hom1_b : 1024 ≤ opp_mask.toNat) (hom2_b : opp_mask.toNat + 16 ≤ 1056)
    (hfi_lt : found_i.toNat < 512)
    (hwf_f : wf.toNat ∈ fullArenaClauseRefs s0)
    (hwf_ng : fullArenaClauseGarb s0 wf.toNat = false)
    (hfsz_eq : fsz.toNat = fullArenaClauseSizeCore s0.core wf.toNat)
    (hn_ok : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s0 (lit.toNat ^^^ 1)
      (s0.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32))
    (hlm2 : lm2.length = 2 * c.max_vars)
    (hclr2 : ∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 = 0#8)
    (hm2 : (FullMem c { s0 with core := { s0.core with lit_mark := lm2 } } ⋆ R) m2)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s0 with core := { s0.core with lit_mark := lm' }
                  scratch := { s0.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
        scr'[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (m7AndCandExpr c.pArena c.pScratchBuf c.pLitMark c.pVals
      opp_off opp_n lit_mask opp_mask found_i wf fsz lit) m2 := by
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hwf_wf := hdw0.2.1.arena.refs_wf wf.toNat hwf_f
  have hwf_bd : wf.toNat + 3 + fullArenaClauseSizeCore s0.core wf.toNat ≤ c.arena_cap := by
    have := hwf_wf.2.2.1; have := hwf_wf.2.2.2.1; omega
  unfold m7AndCandExpr
  refine wp_loop_group (ts := [i32, i32])
    (fun rem3 (uniq_need, k, ()) m3 => ∃ lm3 : List (BitVec 8),
      let s3 : FullState := { s0 with core := { s0.core with lit_mark := lm3 } }
      lm3.length = 2 * c.max_vars ∧ k.toNat ≤ fsz.toNat ∧ rem3 = fsz.toNat - k.toNat ∧
      (∀ x < 2 * c.max_vars, lm3[x]?.getD 0#8 ≠ 0#8 →
        (x ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧ (x ^^^ 1) ≠ lit.toNat) ∧
      (FullMem c s3 ⋆ R) m3)
    ?_ ?_
  · rintro L3 rem3 ⟨uniq_need, k, ⟨⟩⟩ m3 hL3 ⟨lm3, hlm3, hk_le, rfl, hmk3, hm3⟩
    c0_hsplit
    · have hk_lt : k.toNat < fsz.toNat := hc
      have hwk_eq : (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat = wf.toNat + 3 + k.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, zext32_toNat, zext32_toNat,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hwk : (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat < s0.core.arena.length := by
        rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
      let lf := s0.core.arena[(wf.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hwk
      have hlf_mem : lf.toNat ∈ fullArenaClauseLitsCore s0.core wf.toNat := by
        rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
        exact ⟨k.toNat, by omega, congrArg BitVec.toNat (getElem_congr hwk_eq.symm _ _)⟩
      have hlf_lt : lf.toNat < 2 * s0.core.cur_vars :=
        hdw0.2.1.arena.lits_lt wf.toNat hwf_f hwf_ng _ hlf_mem
      have hlf_v : (lf.setWidth 64).toNat < s0.core.vals.length := by
        rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
      have hlfn_lt : lf.toNat ^^^ 1 < 2 * s0.core.cur_vars := by
        have := fullInv_var_xor1 lf.toNat; omega
      have hlfn_lm : ((lf ^^^ 1#32).setWidth 64).toNat < lm3.length :=
        m7_xor1_zext64_lt hlm3 (by omega)
      have hlfn_inv : ((lf ^^^ 1#32).setWidth 64).toNat ^^^ 1 = lf.toNat :=
        m7_xor1_zext64_inv lf
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
      have hlf_c0_idx :
          (wf.toNat + BitVec.toNat (3 : BitVec 64) + k.toNat) % 2 ^ 64 =
            (wf.setWidth 64 + 3#64 + k.setWidth 64).toNat := by
        rw [hwk_eq, show BitVec.toNat (3 : BitVec 64) = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hlf_c0 : s0.core.arena[
          (wf.toNat + BitVec.toNat (3 : BitVec 64) + k.toNat) % 2 ^ 64]'(by
          rw [hlf_c0_idx]; exact hwk) = lf :=
        getElem_congr hlf_c0_idx _ hwk
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
        (fun x => (x.1, ()))
        (fun ⟨_, lm⟩ mj => lm.length = 2 * c.max_vars ∧
          (∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 →
            (y ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧ (y ^^^ 1) ≠ lit.toNat) ∧
          (FullMem c { s0 with core := { s0.core with lit_mark := lm } } ⋆ R) mj)
        (fun _ ⟨un', lm'⟩ mj ⟨hlm', hmk', hmj⟩ => by
          c0_hsteps!
          exact hL3 (fsz.toNat - (k + 1#32).toNat) (un', k + 1#32, ()) mj
            (by omega) ⟨lm', hlm', by omega, rfl, hmk', hmj⟩)
        (fun _ hJ3 => by
          c0_hsplit
          · have hlf_ne : lf.toNat ≠ lit.toNat := by
              intro h; exact hc (by rw [hlf_c0]; exact BitVec.eq_of_toNat_eq h)
            c0_hsplit
            · c0_hsplit
              · c0_hsteps!
                exact hJ3 (uniq_need + 1#32, lm3.set ((lf ^^^ 1#32).setWidth 64).toNat 1#8) _
                  ⟨by simp [hlm3],
                   lm_set_at hlm3 (by rw [← hlm3]; exact hlfn_lm) hmk3
                     ⟨by rw [hlfn_inv]; exact hlf_mem, by rw [hlfn_inv]; exact hlf_ne⟩, hm⟩
              · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3, hmk3, hm3⟩
            · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3, hmk3, hm3⟩
          · c0_hsteps!; exact hJ3 (uniq_need, lm3) m3 ⟨hlm3, hmk3, hm3⟩)
    · c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32, i32])
        (fun rem4 (j, matched, ()) m4 =>
          ∃ (lm4 : List (BitVec 8)) (scr4 : List (BitVec 32)),
            let s4 : FullState :=
              { s0 with core := { s0.core with lit_mark := lm4 }
                        scratch := { s0.scratch with scratch_buf := scr4 } }
            lm4.length = 2 * c.max_vars ∧ scr4.length = c.scratch_cap ∧
            j.toNat ≤ opp_n.toNat ∧ rem4 = opp_n.toNat - j.toNat ∧
            (∀ x < 2 * c.max_vars, lm4[x]?.getD 0#8 ≠ 0#8 →
              (x ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧ (x ^^^ 1) ≠ lit.toNat) ∧
            (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
              scr4[i]? = s0.scratch.scratch_buf[i]?) ∧
            (FullMem c s4 ⋆ R) m4)
        ?_ ?_
      · rintro L4 rem4 ⟨j, matched, ⟨⟩⟩ m4 hL4
          ⟨lm4, scr4, hlm4, hsc4, hj_le, rfl, hmk4, hout4, hm4⟩
        c0_hsplit
        · have hj_lt : j.toNat < opp_n.toNat := hc
          have hoj_sc : ((opp_off + j).setWidth 64).toNat < scr4.length := by
            rw [hsc4, zext32_toNat]; c0_bound
          have hoj_eq : ((opp_off + j).setWidth 64).toNat = opp_off.toNat + j.toNat := by
            rw [zext32_toNat]; c0_bound
          let wo := scr4[((opp_off + j).setWidth 64).toNat]'hoj_sc
          have hwo_get : s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 = wo := by
            have hg := hout4 (opp_off.toNat + j.toNat) (by omega) (Or.inl (by omega))
            have hoj' : opp_off.toNat + j.toNat < scr4.length := by omega
            rw [List.getElem?_eq_getElem hoj'] at hg
            rw [← hg, Option.getD_some]
            exact getElem_congr hoj_eq.symm hoj' hoj_sc
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state (ts := [i32])
            (α := BitVec 32 × List (BitVec 8) × List (BitVec 32)) (fun x => (x.1, ()))
            (fun ⟨_, lm, scr⟩ mj => lm.length = 2 * c.max_vars ∧ scr.length = c.scratch_cap ∧
              (∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 →
                (y ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                (y ^^^ 1) ≠ lit.toNat) ∧
              (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
                scr[i]? = s0.scratch.scratch_buf[i]?) ∧
              (FullMem c { s0 with core := { s0.core with lit_mark := lm }
                                   scratch := { s0.scratch with scratch_buf := scr } } ⋆ R) mj)
            (fun _ ⟨mt', lm', scr'⟩ mj ⟨hlm', hsc', hmk', hout', hmj⟩ => by
              c0_hsteps!
              exact hL4 (opp_n.toNat - (j + 1#32).toNat) (j + 1#32, mt', ()) mj (by omega)
                ⟨lm', scr', hlm', hsc', by omega, rfl, hmk', hout', hmj⟩)
            (fun _ hJ4 => by
              c0_hsplit
              · have hwo_bin : (wo &&& 0x80000000#32) ≠ 0#32 := hc
                have hot_lt : (wo &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
                  have h1 := hn_ok j.toNat hj_lt; rw [hwo_get] at h1
                  unfold FullBveEntryOkW at h1; rw [ite_eq_left hwo_bin] at h1; exact h1.1
                have hot_v : ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                    s0.core.vals.length := by
                  rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
                have hot_lm : ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm4.length := by
                  rw [hlm4, zext32_toNat]; omega
                c0_hsteps_nogrp
                refine wp_join_state (ts := [i32])
                  (α := BitVec 32 × List (BitVec 8) × List (BitVec 32)) (fun x => (x.1, ()))
                  (fun ⟨_, lm, scr⟩ mj => lm.length = 2 * c.max_vars ∧
                    scr.length = c.scratch_cap ∧
                    (∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 →
                      (y ^^^ 1) ∈ fullArenaClauseLitsCore s0.core wf.toNat ∧
                      (y ^^^ 1) ≠ lit.toNat) ∧
                    (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
                      scr[i]? = s0.scratch.scratch_buf[i]?) ∧
                    (FullMem c { s0 with core := { s0.core with lit_mark := lm }
                                         scratch := { s0.scratch with scratch_buf := scr } } ⋆
                      R) mj)
                  (fun _ p mj h => by c0_hsteps!; exact hJ4 p mj h)
                  (fun _ hJ4i => by
                    have hjm : (opp_mask + (j >>> (5 : Nat))).toNat < scr4.length := by
                      have h1 := m7_mask_lt_16 j (by omega)
                      rw [hsc4, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
                    have hjm_idx :
                        ((opp_mask + (j >>> (5 : Nat))).setWidth 64).toNat =
                          opp_mask.toNat + j.toNat / 32 := by
                      have h1 := m7_mask_lt_16 j (by omega)
                      rw [zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight,
                        Nat.shiftRight_eq_div_pow, show 2 ^ 5 = 32 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    have hjm_64 :
                        ((opp_mask + (j >>> (5 : Nat))).setWidth 64).toNat < scr4.length := by
                      rw [zext32_toNat]; exact hjm
                    c0_hsplit
                    · c0_hsteps!
                      dsimp only at hm
                      exact hJ4i (matched + 1#32,
                        lm4.set ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat 0#8,
                        scr4.set ((opp_mask + (j >>> (5 : Nat))).setWidth 64).toNat _) _
                        ⟨by simp [hlm4], by simp [hsc4],
                         fun y hy hnz => by
                           by_cases hy_eq : y = ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat
                           · subst hy_eq
                             rw [List.getElem?_set_self hot_lm, Option.getD_some] at hnz
                             exact absurd rfl hnz
                           · rw [List.getElem?_set_ne (Ne.symm hy_eq)] at hnz
                             exact hmk4 y hy hnz,
                         fun idx hidx hor => by
                           rw [List.getElem?_set_ne (by
                             rw [hjm_idx]; have := m7_mask_lt_16 j (by omega); omega)]
                           exact hout4 idx hidx hor, hm⟩
                    · c0_hsteps!
                      exact hJ4i (matched, lm4, scr4) m4 ⟨hlm4, hsc4, hmk4, hout4, hm4⟩)
              · c0_hsteps!; exact hJ4 (matched, lm4, scr4) m4 ⟨hlm4, hsc4, hmk4, hout4, hm4⟩)
        · exact m7_and_unmark_tail_wp Γ c F0 F_cur s0 R lit_mask opp_mask found_i wf fsz lit
            matched uniq_need lm4 scr4 m4 Q X hmx hsc harc hdw0 hsc1088 hfi_lt hlm1_b hlm2_b
            hom1_b hom2_b hwf_f hwf_ng hfsz_eq hlm4 hsc4 hmk4 hout4 hm4 hQ
      · intro L4 hL4; c0_hsteps!
        exact hL4 opp_n.toNat (0#32, 0#32, ()) m3
          ⟨lm3, s0.scratch.scratch_buf, hlm3, hdw0.1.scratch_ok.scratch_buf_len,
           Nat.zero_le _, by simp, hmk3, fun _ _ _ => rfl, hm3⟩
  · intro L3 hL3; c0_hsteps!
    exact hL3 fsz.toNat (0#32, 0#32, ()) m2
      ⟨lm2, hlm2, Nat.zero_le _, by simp, fun x hx hnz => absurd (hclr2 x hx) hnz, hm2⟩

/-- Canonical `Func.wp` proof for `full_bve_find_and_m7`. -/
theorem full_bve_find_and_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveFindAndM7Spec a m Q X →
      Func.wp Γ full_bve_find_and_m7_body a m Q X := by
  rintro ⟨h, lit, lit_n, opp_n, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1088, hlit_lt, hln, hon, hp_ok, hn_ok, hm0, hQ⟩ :=
    fullBveFindAndM7Spec_elim hSpec
  have hcases := m7_and_pol_cases lit
  have hlo : ((lit &&& 1#32) <<< 9).toNat + lit_n.toNat ≤ 1024 := by
    rcases hcases with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have hoo : (512#32 - ((lit &&& 1#32) <<< 9)).toNat + opp_n.toNat ≤ 1024 := by
    rcases hcases with ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> omega
  have hlm1_b : 1024 ≤ (1024#32 + ((lit &&& 1#32) <<< 4)).toNat := by
    rcases hcases with ⟨_, _, h3, _⟩ | ⟨_, _, h3, _⟩ <;> omega
  have hlm2_b : (1024#32 + ((lit &&& 1#32) <<< 4)).toNat + 16 ≤ 1056 := by
    rcases hcases with ⟨_, _, h3, _⟩ | ⟨_, _, h3, _⟩ <;> omega
  have hom1_b : 1024 ≤ (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))).toNat := by
    rcases hcases with ⟨_, _, _, h4⟩ | ⟨_, _, _, h4⟩ <;> omega
  have hom2_b : (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))).toNat + 16 ≤ 1056 := by
    rcases hcases with ⟨_, _, _, h4⟩ | ⟨_, _, _, h4⟩ <;> omega
  clear hcases
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  unfold Func.wp full_bve_find_and_m7_body
  c0_hsteps_nogrp
  generalize (2064#32 - (1024#32 + ((lit &&& 1#32) <<< 4))) = opp_mask at *
  generalize (1024#32 + ((lit &&& 1#32) <<< 4)) = lit_mask at *
  generalize (512#32 - ((lit &&& 1#32) <<< 9)) = opp_off at *
  generalize ((lit &&& 1#32) <<< 9) = lit_off at *
  refine wp_loop_group (ts := [i32, i32])
    (fun rem1 (bin_cnt, j, ()) m1 => ∃ lm1 : List (BitVec 8),
      let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
      lm1.length = 2 * c.max_vars ∧ j.toNat ≤ opp_n.toNat ∧ rem1 = opp_n.toNat - j.toNat ∧
      bin_cnt.toNat ≤ j.toNat ∧
      (bin_cnt = 0#32 → ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 = 0#8) ∧
      (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
        ∃ u < j.toNat, let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
          (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat) ∧
      (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro L1 rem1 ⟨bin_cnt, j, ⟨⟩⟩ m1 hL1 ⟨lm1, hlm1, hj_le, rfl, hbc_le, hbc0, hmk1, hm1⟩
    c0_hsplit
    · have hj_lt : j.toNat < opp_n.toNat := hc
      have hoj_sc : ((opp_off + j).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
        rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; c0_bound
      have hoj_eq : ((opp_off + j).setWidth 64).toNat = opp_off.toNat + j.toNat := by
        rw [zext32_toNat]; c0_bound
      let wo := s0.scratch.scratch_buf[((opp_off + j).setWidth 64).toNat]'hoj_sc
      have hwo_get : s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 = wo := by
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
          Option.getD_some]
        exact getElem_congr hoj_eq.symm _ hoj_sc
      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8)) (fun x => (x.1, ()))
        (fun ⟨bc, lm⟩ mj => lm.length = 2 * c.max_vars ∧ bc.toNat ≤ j.toNat + 1 ∧
          (bc = 0#32 → ∀ z < 2 * c.max_vars, lm[z]?.getD 0#8 = 0#8) ∧
          (∀ z < 2 * c.max_vars, lm[z]?.getD 0#8 ≠ 0#8 →
            ∃ u < j.toNat + 1, let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
              (w &&& 0x80000000#32) ≠ 0#32 ∧ z = (w &&& 0x7FFFFFFF#32).toNat) ∧
          (FullMem c { s0 with core := { s0.core with lit_mark := lm } } ⋆ R) mj)
        (fun _ ⟨bc', lm'⟩ mj ⟨hlm', hbc', hbc0', hmk', hmj⟩ => by
          c0_hsteps!
          exact hL1 (opp_n.toNat - (j + 1#32).toNat) (bc', j + 1#32, ()) mj (by omega)
            ⟨lm', hlm', by omega, rfl, by omega, hbc0', fun z hz hnz => by
              obtain ⟨u, hu, hw⟩ := hmk' z hz hnz; exact ⟨u, by omega, hw⟩, hmj⟩)
        (fun J1 hJ1 => by
          have hkeep : J1 (bin_cnt, ()) m1 := by
            refine hJ1 (bin_cnt, lm1) m1 ⟨hlm1, by omega, hbc0, fun z hz hnz => ?_, hm1⟩
            obtain ⟨u, hu, hw⟩ := hmk1 z hz hnz; exact ⟨u, by omega, hw⟩
          c0_hsplit
          · have hwo_bin : (wo &&& 0x80000000#32) ≠ 0#32 := hc
            have hot_lt : (wo &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
              have h1 := hn_ok j.toNat hj_lt; rw [hwo_get] at h1
              unfold FullBveEntryOkW at h1; rw [ite_eq_left hwo_bin] at h1; exact h1.1
            have hot_v : ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat < s0.core.vals.length := by
              rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
              (fun x => (x.1, ()))
              (fun ⟨bc, lm⟩ mj => lm.length = 2 * c.max_vars ∧ bc.toNat ≤ j.toNat + 1 ∧
                (bc = 0#32 → ∀ z < 2 * c.max_vars, lm[z]?.getD 0#8 = 0#8) ∧
                (∀ z < 2 * c.max_vars, lm[z]?.getD 0#8 ≠ 0#8 →
                  ∃ u < j.toNat + 1, let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
                    (w &&& 0x80000000#32) ≠ 0#32 ∧ z = (w &&& 0x7FFFFFFF#32).toNat) ∧
                (FullMem c { s0 with core := { s0.core with lit_mark := lm } } ⋆ R) mj)
              (fun _ ⟨bc', lm'⟩ mj ⟨hlm', hbc', hbc0', hmk', hmj⟩ => by
                c0_hsteps!; exact hJ1 (bc', lm') mj ⟨hlm', hbc', hbc0', hmk', hmj⟩)
              (fun J1i hJ1i => by
                c0_hsplit
                · have hot_lm : ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat < lm1.length := by
                    rw [hlm1, zext32_toNat]; omega
                  c0_hsteps_nogrp
                  · have hbc1 : (bin_cnt + 1#32).toNat = bin_cnt.toNat + 1 := by c0_bound
                    let lm_n := lm1.set ((wo &&& 0x7FFFFFFF#32).setWidth 64).toNat 1#8
                    have hbc_ne : ∀ h : bin_cnt + 1#32 = 0#32, False := fun h => by
                      have h0 : (bin_cnt + 1#32).toNat = 0 := congrArg BitVec.toNat h
                      rw [hbc1] at h0; omega
                    c0_hsteps!
                    exact hJ1i (bin_cnt + 1#32, lm_n) _
                      ⟨by simp [lm_n, hlm1], by omega,
                        fun h => False.elim (hbc_ne h),
                        lm_set_at hlm1 (by rw [zext32_toNat]; omega)
                          (fun z hz hnz => by
                            obtain ⟨u, hu, hw⟩ := hmk1 z hz hnz; exact ⟨u, by omega, hw⟩)
                          ⟨j.toNat, Nat.lt_succ_self _, by
                            rw [zext32_toNat, hwo_get]; exact ⟨hwo_bin, rfl⟩⟩, hm⟩
                  · c0_hsteps!
                    exact hJ1i (bin_cnt, lm1) m1
                      ⟨hlm1, by omega, hbc0, fun z hz hnz => by
                        obtain ⟨u, hu, hw⟩ := hmk1 z hz hnz; exact ⟨u, by omega, hw⟩, hm1⟩
                · c0_hsteps!
                  exact hJ1i (bin_cnt, lm1) m1
                    ⟨hlm1, by omega, hbc0, fun z hz hnz => by
                      obtain ⟨u, hu, hw⟩ := hmk1 z hz hnz; exact ⟨u, by omega, hw⟩, hm1⟩)
          · exact hkeep)
    · have hmk1' : ∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
          ∃ u < opp_n.toNat, let w := s0.scratch.scratch_buf[opp_off.toNat + u]?.getD 0#32;
            (w &&& 0x80000000#32) ≠ 0#32 ∧ x = (w &&& 0x7FFFFFFF#32).toNat := by
        intro x hx hnz; obtain ⟨u, hu, hw⟩ := hmk1 x hx hnz; exact ⟨u, by omega, hw⟩
      c0_hsplit
      · c0_hsteps_nogrp
        refine m7_and_clear_opp_wp Γ c F_cur s0 R opp_off opp_n lit lm1 m1 Q X _ hmx hsc
          hsc1088 hdw0.1.scratch_ok.scratch_buf_len hlm1 hoo hon hcv_le hn_ok hmk1' hm1
          (fun lm2 m2 hlm2 hclr2 hm2 => by
            have hdw2 := fullDenseInvW_lm_scr hdw0 hlm2 hclr2
              hdw0.1.scratch_ok.scratch_buf_len
            c0_hsteps!
            exact hQ false lm2 s0.scratch.scratch_buf m2 hdw2
              hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm2)
      · c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32])
          (fun (found_i, _i_b, ()) mb => mb = m1 ∧
            (found_i = 0xFFFFFFFF#32 ∨ (found_i.toNat < lit_n.toNat ∧
              let wf := s0.scratch.scratch_buf[lit_off.toNat + found_i.toNat]?.getD 0#32;
              (wf &&& 0x80000000#32) = 0#32)))
          (fun rem_i (i, ()) mi => mi = m1 ∧ i.toNat ≤ lit_n.toNat ∧ rem_i = lit_n.toNat - i.toNat)
          ?_ ?_ ?_
        · rintro _ ⟨found_i, _ib, ⟨⟩⟩ mb ⟨hmb, hfound⟩
          subst mb
          c0_hsteps_nogrp
          refine m7_and_clear_opp_wp Γ c F_cur s0 R opp_off opp_n lit lm1 _ Q X _ hmx hsc
            hsc1088 hdw0.1.scratch_ok.scratch_buf_len hlm1 hoo hon hcv_le hn_ok hmk1' hm1
            (fun lm2 m2 hlm2 hclr2 hm2 => by
              have hdw2 := fullDenseInvW_lm_scr hdw0 hlm2 hclr2
                hdw0.1.scratch_ok.scratch_buf_len
              c0_hsplit
              · c0_hsteps!
                exact hQ false lm2 s0.scratch.scratch_buf m2 hdw2
                  hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm2
              · have hfi_ne : found_i ≠ 0xFFFFFFFF#32 := hc
                obtain ⟨hfi_lt, hw_bin0⟩ := hfound.resolve_left hfi_ne
                have hfi_sc : ((lit_off + found_i).setWidth 64).toNat <
                    s0.scratch.scratch_buf.length := by
                  rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; c0_bound
                have hfi_eq : ((lit_off + found_i).setWidth 64).toNat =
                    lit_off.toNat + found_i.toNat := by
                  rw [zext32_toNat]; c0_bound
                let wf := s0.scratch.scratch_buf[((lit_off + found_i).setWidth 64).toNat]'hfi_sc
                have hwf_get : s0.scratch.scratch_buf[lit_off.toNat + found_i.toNat]?.getD 0#32 =
                    wf := by
                  rw [List.getElem?_eq_getElem (by
                    rw [hdw0.1.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
                  exact getElem_congr hfi_eq.symm _ hfi_sc
                have hent_f := hp_ok found_i.toNat hfi_lt
                dsimp only at hent_f hw_bin0; rw [hwf_get] at hent_f hw_bin0
                unfold FullBveEntryOkW at hent_f; rw [ite_eq_right (fun h => h hw_bin0)] at hent_f
                have hwf_f := hdw0.2.1.arena.refs_wf wf.toNat hent_f.1
                have hwf_bd : wf.toNat + 3 + fullArenaClauseSizeCore s0.core wf.toNat ≤
                    c.arena_cap := by
                  have := hwf_f.2.2.1; have := hwf_f.2.2.2.1; omega
                have hwf2_ar : (wf.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                  rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, zext32_toNat,
                    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                let fsz := s0.core.arena[(wf.setWidth 64 + 2#64).toNat]'hwf2_ar
                have hfsz_eq : fsz.toNat = fullArenaClauseSizeCore s0.core wf.toNat := by
                  unfold fsz fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                    Option.getD_some]
                  exact congrArg BitVec.toNat (getElem_congr (by
                    rw [BitVec.toNat_add, zext32_toNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega)]) _ _)
                c0_hsteps_nogrp
                exact m7_and_cand_wp Γ c F0 F_cur s0 R opp_off opp_n lit_mask opp_mask found_i
                  wf fsz lit lm2 m2 Q X hmx hsc harc hdw0 hsc1088 hoo hon hlm1_b hlm2_b hom1_b
                  hom2_b (by omega) hent_f.1 hent_f.2 hfsz_eq hn_ok hlm2 hclr2 hm2 hQ)
        · rintro Bi Li rem_i ⟨i, ⟨⟩⟩ mi hBi hLi ⟨hmi, hi_le, rfl⟩
          subst mi; c0_hsplit
          · have hi_lt : i.toNat < lit_n.toNat := hc
            have hli_sc : ((lit_off + i).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
              rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; c0_bound
            have hli_eq : ((lit_off + i).setWidth 64).toNat = lit_off.toNat + i.toNat := by
              rw [zext32_toNat]; c0_bound
            let wi := s0.scratch.scratch_buf[((lit_off + i).setWidth 64).toNat]'hli_sc
            have hwi_get : s0.scratch.scratch_buf[lit_off.toNat + i.toNat]?.getD 0#32 = wi := by
              rw [List.getElem?_eq_getElem (by rw [hdw0.1.scratch_ok.scratch_buf_len]; omega),
                Option.getD_some]
              exact getElem_congr hli_eq.symm _ hli_sc
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32]) (fun _ mi' => mi' = m1)
              (fun _ _ mi' hmi' => by
                subst mi'; c0_hsteps!
                exact hLi (lit_n.toNat - (i + 1#32).toNat) (i + 1#32, ()) m1 (by omega)
                  ⟨rfl, by omega, rfl⟩)
              (fun _ hJi => by
                c0_hstep; c0_hstep; c0_hsplit
                · have hwi_bin0 : (wi &&& 0x80000000#32) = 0#32 := hc
                  have hent_i := hp_ok i.toNat hi_lt; rw [hwi_get] at hent_i
                  unfold FullBveEntryOkW at hent_i
                  rw [ite_eq_right (fun h => h hwi_bin0)] at hent_i
                  have hwf_i := hdw0.2.1.arena.refs_wf wi.toNat hent_i.1
                  have hwi_bd : wi.toNat + 3 + fullArenaClauseSizeCore s0.core wi.toNat ≤
                      c.arena_cap := by
                    have := hwf_i.2.2.1; have := hwf_i.2.2.2.1; omega
                  have hwi2_ar : (wi.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                    rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, zext32_toNat,
                      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                  let sz := s0.core.arena[(wi.setWidth 64 + 2#64).toNat]'hwi2_ar
                  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core wi.toNat := by
                    unfold sz fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                      Option.getD_some]
                    exact congrArg BitVec.toNat (getElem_congr (by
                      rw [BitVec.toNat_add, zext32_toNat, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by omega)]) _ _)
                  have hsz_ge : 3 ≤ fullArenaClauseSizeCore s0.core wi.toNat := hwf_i.2.1
                  c0_hsteps_nogrp
                  refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
                    (fun _ mb => mb = m1)
                    (fun rem_k (need, k, ()) mk => mk = m1 ∧ k.toNat ≤ sz.toNat ∧
                      rem_k = sz.toNat - k.toNat)
                    ?_ ?_ ?_
                  · rintro _ ⟨ok_b, need_b, _, ⟨⟩⟩ mb hmb
                    subst mb; c0_hsplit
                    · c0_hsplit
                      · c0_hsteps!; exact hBi (i, i, ()) m1
                          ⟨rfl, Or.inr ⟨hi_lt, by rw [hwi_get]; exact hwi_bin0⟩⟩
                      · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl
                    · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl
                  · rintro Bk Lk rem_k ⟨need, k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                    subst mk; c0_hsplit
                    · have hk_lt : k.toNat < sz.toNat := hc
                      have hwk_eq : (wi.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                          wi.toNat + 3 + k.toNat := by
                        rw [BitVec.toNat_add, BitVec.toNat_add, zext32_toNat, zext32_toNat,
                          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                          Nat.mod_eq_of_lt (by omega)]
                      have hwk : (wi.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                          s0.core.arena.length := by
                        rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                      let l := s0.core.arena[(wi.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hwk
                      have hl_lt : l.toNat < 2 * s0.core.cur_vars := by
                        have hmem : l.toNat ∈ fullArenaClauseLitsCore s0.core wi.toNat := by
                          rw [mem_fullArenaClauseLitsCore_iff (by
                            rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                          exact ⟨k.toNat, by omega,
                            congrArg BitVec.toNat (getElem_congr hwk_eq.symm _ _)⟩
                        exact hdw0.2.1.arena.lits_lt wi.toNat hent_i.1 hent_i.2 _ hmem
                      have hl_v : (l.setWidth 64).toNat < s0.core.vals.length := by
                        rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
                      have hln_lm : ((l ^^^ 1#32).setWidth 64).toNat < lm1.length := by
                        rw [hlm1, zext32_toNat]; change l.toNat ^^^ 1 < 2 * c.max_vars
                        have := fullInv_var_xor1 l.toNat; omega
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      c0_hsteps_nogrp
                      refine wp_join_state_pure (ts := [.bool, i32]) (α := BitVec 32)
                        (fun nd' => (true, nd', ())) (fun _ => True)
                        (fun _ nd' _ => by
                          c0_hsteps!
                          exact hLk (sz.toNat - (k + 1#32).toNat) (nd', k + 1#32, ()) m1
                            (by omega) ⟨rfl, by omega, rfl⟩)
                        (fun _ hJk => by
                          c0_hsplit
                          · c0_hsteps_nogrp
                            · c0_hsteps!; exact hBk (false, need, k, ()) m1 rfl
                            · refine wp_join_state_pure (ts := [.bool, i32]) (α := BitVec 32)
                                (fun nd' => (true, nd', ())) (fun _ => True)
                                (fun _ nd' _ => by c0_hsteps!; exact hJk nd' trivial)
                                (fun _ hJkn => by
                                  c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps!; exact hBk (false, need, k, ()) m1 rfl
                                    · c0_hsteps!; exact hJkn (need + 1#32) trivial
                                  · c0_hsteps!; exact hJkn need trivial)
                          · c0_hsteps!; exact hJk need trivial)
                    · c0_hsteps!; exact hBk (true, need, k, ()) m1 rfl
                  · intro _ Lk _ hLk; c0_hsteps!
                    exact hLk sz.toNat (0#32, 0#32, ()) m1 ⟨rfl, Nat.zero_le _, by simp⟩
                · c0_hsteps!; exact hJi (0xFFFFFFFF#32, ()) m1 rfl)
          · c0_hsteps!; exact hBi (0xFFFFFFFF#32, i, ()) m1 ⟨rfl, Or.inl rfl⟩
        · intro _ Li _ hLi; c0_hsteps!
          exact hLi lit_n.toNat (0#32, ()) m1 ⟨rfl, Nat.zero_le _, by simp⟩
  · intro L1 hL1; c0_hsteps!
    exact hL1 opp_n.toNat (0#32, 0#32, ()) m0
      ⟨s0.core.lit_mark, hdw0.1.core_ok.lit_mark_len, Nat.zero_le _, by simp,
       Nat.zero_le _, fun _ => hdw0.2.2.1.2, fun x hx hnz =>
         absurd (hdw0.2.2.1.2 x hx) hnz, hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Gates
