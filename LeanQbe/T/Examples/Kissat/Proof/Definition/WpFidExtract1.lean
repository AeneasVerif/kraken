/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidExtract0

/-!
# Kissat Fidelity BVE WP Proofs — K6c Extraction Init/Solve (`Proof.Definition.WpFidExtract1`)

`CanonicalEnv`-clean helpers for `full_k6_extract_and_solve_fid` (`0` legacy imports; zero
`@[expose]` on theorems; every decl `<= 450` LOC; `<= 100` cols):
1. `fid_k6c_tmk_clear_wp`: clears `tmk[wsort[0..nv)]`.
2. `fid_k6c_triv_unit_wp`: trivial-unit mask write (`4002..4131`) returning `true`.
3. `fid_k6c_init_vars_wp`: initializes K6c variable arrays (`4224..4224+9*mv`).
4. `fid_k6c_init_lits_wp`: initializes K6c literal watch arrays (`4224+9*mv..4224+29*mv`).
5. `fid_k6c_init_solve_wp`: post-loop setup (`4192..4216`) + K6c watch/solve/core/bitmap pass.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open FidK6cTactics

public section

abbrev fidK6cTmkClearExpr (c : FullCfg) (nv : BitVec 32)
    (K_after : Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun k : Tup Val [i32] =>
    Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var k.fst, Arg.var nv, ()))
      fun p_1 =>
    Expr.jnz (Arg.var p_1.fst)
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var k.fst, ())) fun p_2 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_2.fst, Arg.imm 4, ())) fun p_3 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWsort, Arg.var p_3.fst, ())) fun p_4 =>
      Expr.load i32 (Arg.var p_4.fst) fun ld =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_5 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p_6.fst, ()))
        fun p_7 =>
      Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var k.fst, Arg.imm 1, ())) fun p_8 =>
        Expr.jump Js.fst (Arg.var p_8.fst, ())))
      K_after) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 0, ())

abbrev fidK6cTrivMaskBody (c : FullCfg) (eid pm : BitVec 32) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pk : Tup Val [i32] =>
    Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pk.fst, Arg.imm 128, ()))
      fun p_1 =>
    Expr.jnz (Arg.var p_1.fst)
      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4002, Arg.var pk.fst, ())) fun p_2 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
        fun p_5 =>
      Expr.store (t := i32) (Arg.imm 0) (Arg.var p_5.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pk.fst, Arg.imm 1, ())) fun p_6 =>
        Expr.jump Js_1.fst (Arg.var p_6.fst, ())))
      (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var eid, Arg.imm 5, ())) fun p_2 =>
      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pm, Arg.var p_2.fst, ())) fun p_3 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_3.fst, ())) fun p_4 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
        fun p_6 =>
      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var eid, Arg.imm 31, ())) fun p_7 =>
      Expr.let_ (Op.mk (OpCode.shl i32) (Arg.imm 1, Arg.var p_7.fst, ())) fun p_8 =>
      Expr.store (Arg.var p_8.fst) (Arg.var p_6.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4130, ())) fun p_9 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_9.fst, Arg.imm 4, ())) fun p_10 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_10.fst, ()))
          fun p_11 =>
        Expr.store (t := i32) (Arg.imm 1) (Arg.var p_11.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4131, ())) fun p_12 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_12.fst, Arg.imm 4, ())) fun p_13 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_13.fst, ()))
            fun p_14 =>
          Expr.store (t := i32) (Arg.imm 1) (Arg.var p_14.fst)
            (Expr.ret (Arg.imm true, ())))))
    ) Blocks.nil)
  fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())

abbrev fidK6cTrivUnitExpr (c : FullCfg) (triv_unit : BitVec 32) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var triv_unit, Arg.imm 2047, ())) fun eid =>
  Expr.group (fun _ : Tup Cont [[i32]] =>
    Blocks.cons (fun pm : Tup Val [i32] => fidK6cTrivMaskBody c eid.fst pm.fst) Blocks.nil)
  fun Js =>
  Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var triv_unit, Arg.imm 11, ())) fun p_1 =>
  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var p_1.fst, Arg.imm 0, ())) fun p_2 =>
  Expr.jnz (Arg.var p_2.fst)
    (Expr.jump Js.fst (Arg.imm 4002, ())) (Expr.jump Js.fst (Arg.imm 4066, ()))

abbrev fidK6cInitVarsExpr (c : FullCfg) (nv o_vals o_lvl o_next o_prev o_phase : BitVec 32)
    (K_after : Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pi : Tup Val [i32] =>
    Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pi.fst, Arg.var nv, ()))
      fun p_1 =>
    Expr.jnz (Arg.var p_1.fst)
      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4224, Arg.var pi.fst, ())) fun p_2 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
        fun p_5 =>
      Expr.store (t := i32) (Arg.imm 0) (Arg.var p_5.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_vals, Arg.var pi.fst, ())) fun p_6 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_6.fst, ())) fun p_7 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_7.fst, Arg.imm 4, ())) fun p_8 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_8.fst, ()))
          fun p_9 =>
        Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p_9.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_phase, Arg.var pi.fst, ())) fun p_10 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_10.fst, ())) fun p_11 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_11.fst, Arg.imm 4, ())) fun p_12 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_12.fst, ()))
            fun p_13 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p_13.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_prev, Arg.var pi.fst, ()))
              fun p_14 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_14.fst, ())) fun p_15 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_15.fst, Arg.imm 4, ())) fun p_16 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_16.fst, ()))
              fun p_17 =>
            Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p_18 =>
            Expr.store (Arg.var p_18.fst) (Arg.var p_17.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_lvl, Arg.var pi.fst, ()))
                fun p_19 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_20 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ())) fun p_21 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_21.fst, ()))
                fun p_22 =>
              Expr.group (fun _ : Tup Cont [[i32]] => Blocks.cons (fun pv : Tup Val [i32] =>
                Expr.store (Arg.var pv.fst) (Arg.var p_22.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_next, Arg.var pi.fst, ()))
                    fun p_23 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_23.fst, ())) fun p_24 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_24.fst, Arg.imm 4, ()))
                    fun p_25 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pScratchBuf, Arg.var p_25.fst, ())) fun p_26 =>
                  Expr.group (fun _ : Tup Cont [[i32]] => Blocks.cons (fun pn : Tup Val [i32] =>
                    Expr.store (Arg.var pn.fst) (Arg.var p_26.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ()))
                        fun p_27 => Expr.jump Js.fst (Arg.var p_27.fst, ())))
                    Blocks.nil)
                  fun Js_2 =>
                  Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p_27 =>
                  Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                    (Arg.var p_27.fst, Arg.var nv, ())) fun p_28 =>
                  Expr.jnz (Arg.var p_28.fst)
                    (Expr.jump Js_2.fst (Arg.imm 4294967295, ()))
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ()))
                      fun p_29 => Expr.jump Js_2.fst (Arg.var p_29.fst, ()))))
                Blocks.nil)
              fun Js_1 =>
              Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var pi.fst, Arg.imm 0, ()))
                fun p_23 =>
              Expr.jnz (Arg.var p_23.fst)
                (Expr.jump Js_1.fst (Arg.imm 4294967295, ()))
                (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p_24 =>
                  Expr.jump Js_1.fst (Arg.var p_24.fst, ())))))))
      K_after) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 0, ())

abbrev fidK6cInitLitsExpr (c : FullCfg) (nv o_whead o_wtail : BitVec 32)
    (K_after : Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pl : Tup Val [i32] =>
    Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var nv, Arg.imm 1, ())) fun p_1 =>
    Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pl.fst, Arg.var p_1.fst, ()))
      fun p_2 =>
    Expr.jnz (Arg.var p_2.fst)
      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_whead, Arg.var pl.fst, ())) fun p_3 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_3.fst, ())) fun p_4 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
        fun p_6 =>
      Expr.store (t := i32) (Arg.imm 0) (Arg.var p_6.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_wtail, Arg.var pl.fst, ())) fun p_7 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_7.fst, ())) fun p_8 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_8.fst, Arg.imm 4, ())) fun p_9 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_9.fst, ()))
          fun p_10 =>
        Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p_10.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.fst, Arg.imm 1, ())) fun p_11 =>
          Expr.jump Js.fst (Arg.var p_11.fst, ()))))
      K_after) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 0, ())

abbrev fidK6cWatchSolveExpr (c : FullCfg)
    (nc tick_lim o_cl_off o_cl_meta o_cl_aux o_arena : BitVec 32) :
    Expr Val Cont [Ty.bool] :=
  Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun p : Tup Val [i32] =>
    Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var nc, ())) fun p_1 =>
    Expr.jnz (Arg.var p_1.fst)
      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var p.fst, ())) fun p_2 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
        fun p_5 =>
      Expr.load i32 (Arg.var p_5.fst) fun ld =>
      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 65535, ())) fun p_6 =>
      Expr.group (fun _ : Tup Cont [[]] => Blocks.cons (fun _ =>
        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_7 =>
        Expr.jump Js.fst (Arg.var p_7.fst, ())) Blocks.nil) fun Js_1 =>
      Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var p_6.fst, Arg.imm 2, ()))
        fun p_7 =>
      Expr.jnz (Arg.var p_7.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var p.fst, ())) fun p_8 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_8.fst, ())) fun p_9 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_9.fst, Arg.imm 4, ())) fun p_10 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_10.fst, ()))
          fun p_11 =>
        Expr.load i32 (Arg.var p_11.fst) fun ld_1 =>
        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var ld_1, ())) fun p_12 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_12.fst, ())) fun p_13 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_13.fst, Arg.imm 4, ())) fun p_14 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_14.fst, ()))
          fun p_15 =>
        Expr.load i32 (Arg.var p_15.fst) fun ld_2 =>
        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var ld_1, ())) fun p_16 =>
        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_16.fst, Arg.imm 1, ())) fun p_17 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_17.fst, ())) fun p_18 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_18.fst, Arg.imm 4, ())) fun p_19 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_19.fst, ()))
          fun p_20 =>
        Expr.load i32 (Arg.var p_20.fst) fun ld_3 =>
        Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_fid"
          (Arg.var c.hdr, Arg.var p.fst, Arg.var ld_2, Arg.var ld_3, Arg.var p_6.fst, ())
          fun _ : Tup Val [] => Expr.jump Js_1.fst ())
        (Expr.jump Js_1.fst ()))
      (Expr.call (as := [i64, i32]) (bs := [i64]) "full_k6_solve_fid"
        (Arg.var c.hdr, Arg.var tick_lim, ()) fun ret : Tup Val [i64] =>
      Expr.let_ (Op.mk (OpCode.cmp .ne i64 .bool rfl) (Arg.var ret.fst, Arg.imm 20, ()))
        fun p_2 =>
      Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.imm false, ()))
        (Expr.call (as := [i64]) (bs := []) "full_k6_core_fid" (Arg.var c.hdr, ())
          fun _ : Tup Val [] =>
        Expr.group (fun Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pz : Tup Val [i32] =>
          Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pz.fst, Arg.imm 128, ()))
            fun p_3 =>
          Expr.jnz (Arg.var p_3.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4002, Arg.var pz.fst, ())) fun p_4 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_4.fst, ())) fun p_5 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_6.fst, ()))
              fun p_7 =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pz.fst, Arg.imm 1, ())) fun p_8 =>
              Expr.jump Js_1.fst (Arg.var p_8.fst, ())))
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p_4 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
              fun p_6 =>
            Expr.load i32 (Arg.var p_6.fst) fun onc =>
            Expr.group (fun Js_2 : Tup Cont [[i32, Ty.bool]] =>
              Blocks.cons (fun pc : Tup Val [i32, Ty.bool] =>
                Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pc.fst, Arg.var onc, ()))
                  fun p_7 =>
                Expr.jnz (Arg.var p_7.fst)
                  (Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
                    Blocks.cons (fun pn : Tup Val [Ty.bool] =>
                      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pc.fst, Arg.imm 1, ())) fun p_8 =>
                      Expr.jump Js_2.fst (Arg.var p_8.fst, Arg.var pn.fst, ())) Blocks.nil)
                    fun Js_3 =>
                  Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var pc.fst, ()))
                    fun p_8 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_8.fst, ())) fun p_9 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_9.fst, Arg.imm 4, ())) fun p_10 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pScratchBuf, Arg.var p_10.fst, ())) fun p_11 =>
                  Expr.load i32 (Arg.var p_11.fst) fun cm =>
                  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var cm, Arg.imm 2147483648, ()))
                    fun p_12 =>
                  Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                    (Arg.var p_12.fst, Arg.imm 0, ())) fun p_13 =>
                  Expr.jnz (Arg.var p_13.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var pc.fst, ()))
                      fun p_14 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_14.fst, ())) fun p_15 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_15.fst, Arg.imm 4, ()))
                      fun p_16 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p_16.fst, ())) fun p_17 =>
                    Expr.load i32 (Arg.var p_17.fst) fun raw =>
                    Expr.let_ (Op.mk (OpCode.and i32) (Arg.var raw, Arg.imm 2047, ())) fun eid =>
                    Expr.group (fun _ : Tup Cont [[i32]] => Blocks.cons (fun pm =>
                      Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var eid.fst, Arg.imm 5, ()))
                        fun p_18 =>
                      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pm.fst, Arg.var p_18.fst, ()))
                        fun p_19 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_20 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ()))
                        fun p_21 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p_21.fst, ())) fun p_22 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_23 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ()))
                        fun p_24 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p_24.fst, ())) fun p_25 =>
                      Expr.load i32 (Arg.var p_25.fst) fun cur =>
                      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var eid.fst, Arg.imm 31, ()))
                        fun p_26 =>
                      Expr.let_ (Op.mk (OpCode.shl i32) (Arg.imm 1, Arg.var p_26.fst, ()))
                        fun p_27 =>
                      Expr.let_ (Op.mk (OpCode.or i32) (Arg.var cur, Arg.var p_27.fst, ()))
                        fun p_28 =>
                      Expr.store (Arg.var p_28.fst) (Arg.var p_22.fst)
                        (Expr.jump Js_3.fst (Arg.imm true, ()))) Blocks.nil)
                    fun Js_4 =>
                    Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var raw, Arg.imm 11, ())) fun p_18 =>
                    Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                      (Arg.var p_18.fst, Arg.imm 0, ())) fun p_19 =>
                    Expr.jnz (Arg.var p_19.fst)
                      (Expr.jump Js_4.fst (Arg.imm 4002, ()))
                      (Expr.jump Js_4.fst (Arg.imm 4066, ())))
                    (Expr.jump Js_3.fst (Arg.var pc.snd.fst, ())))
                  (Expr.group (fun _ : Tup Cont [[]] =>
                    Blocks.cons (fun _ => Expr.ret (Arg.var pc.snd.fst, ())) Blocks.nil)
                    fun Js_3 =>
                  Expr.jnz (Arg.var pc.snd.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4130, ())) fun p_8 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_8.fst, Arg.imm 4, ())) fun p_9 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p_9.fst, ())) fun p_10 =>
                    Expr.store (t := i32) (Arg.imm 1) (Arg.var p_10.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4131, ())) fun p_11 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_11.fst, Arg.imm 4, ()))
                        fun p_12 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p_12.fst, ())) fun p_13 =>
                      Expr.store (t := i32) (Arg.imm 1) (Arg.var p_13.fst)
                        (Expr.jump Js_3.fst ())))
                    (Expr.jump Js_3.fst ()))) Blocks.nil)
              fun Js_2 => Expr.jump Js_2.fst (Arg.imm 0, Arg.imm false, ()))) Blocks.nil)
          fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())))) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 0, ())

abbrev fidK6cScalarsExpr (c : FullCfg)
    (mv_s mv4 mv2 acap_s nv nc alen n_units tick_lim : BitVec 32)
    (K_after : Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4192, ())) fun p_76 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_76.fst, Arg.imm 4, ())) fun p_77 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_77.fst, ())) fun p_78 =>
  Expr.store (t := i32) (Arg.var nv) (Arg.var p_78.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4193, ())) fun p_79 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_79.fst, Arg.imm 4, ())) fun p_80 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_80.fst, ())) fun p_81 =>
  Expr.store (t := i32) (Arg.var nc) (Arg.var p_81.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p_82 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_82.fst, Arg.imm 4, ())) fun p_83 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_83.fst, ())) fun p_84 =>
  Expr.store (t := i32) (Arg.var nc) (Arg.var p_84.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4195, ())) fun p_85 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_85.fst, Arg.imm 4, ())) fun p_86 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_86.fst, ())) fun p_87 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_87.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4196, ())) fun p_88 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_88.fst, Arg.imm 4, ())) fun p_89 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_89.fst, ())) fun p_90 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_90.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4197, ())) fun p_91 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_91.fst, Arg.imm 4, ())) fun p_92 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_92.fst, ())) fun p_93 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_93.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4198, ())) fun p_94 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_94.fst, Arg.imm 4, ())) fun p_95 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_95.fst, ())) fun p_96 =>
  Expr.store (t := i32) (Arg.var nv) (Arg.var p_96.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4199, ())) fun p_97 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_97.fst, Arg.imm 4, ())) fun p_98 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_98.fst, ())) fun p_99 =>
  Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p_99.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4200, ())) fun p_100 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_100.fst, Arg.imm 4, ())) fun p_101 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_101.fst, ())) fun p_102 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_102.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4201, ())) fun p_103 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_103.fst, Arg.imm 4, ())) fun p_104 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_104.fst, ())) fun p_105 =>
  Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p_106 =>
  Expr.store (t := i32) (Arg.var p_106.fst) (Arg.var p_105.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4202, ())) fun p_107 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_107.fst, Arg.imm 4, ())) fun p_108 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_108.fst, ())) fun p_109 =>
  Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p_110 =>
  Expr.store (t := i32) (Arg.var p_110.fst) (Arg.var p_109.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4203, ())) fun p_111 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_111.fst, Arg.imm 4, ())) fun p_112 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_112.fst, ())) fun p_113 =>
  Expr.store (t := i32) (Arg.var nv) (Arg.var p_113.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4204, ())) fun p_114 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_114.fst, Arg.imm 4, ())) fun p_115 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_115.fst, ())) fun p_116 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_116.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4205, ())) fun p_117 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_117.fst, Arg.imm 4, ())) fun p_118 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_118.fst, ())) fun p_119 =>
  Expr.store (t := i32) (Arg.var tick_lim) (Arg.var p_119.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4206, ())) fun p_120 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_120.fst, Arg.imm 4, ())) fun p_121 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_121.fst, ())) fun p_122 =>
  Expr.store (t := i32) (Arg.var alen) (Arg.var p_122.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4207, ())) fun p_123 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_123.fst, Arg.imm 4, ())) fun p_124 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_124.fst, ())) fun p_125 =>
  Expr.store (t := i32) (Arg.var acap_s) (Arg.var p_125.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4208, ())) fun p_126 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_126.fst, Arg.imm 4, ())) fun p_127 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_127.fst, ())) fun p_128 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_128.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4209, ())) fun p_129 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_129.fst, Arg.imm 4, ())) fun p_130 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_130.fst, ())) fun p_131 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_131.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4210, ())) fun p_132 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_132.fst, Arg.imm 4, ())) fun p_133 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_133.fst, ())) fun p_134 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_134.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4211, ())) fun p_135 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_135.fst, Arg.imm 4, ())) fun p_136 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_136.fst, ())) fun p_137 =>
  Expr.store (t := i32) (Arg.var n_units) (Arg.var p_137.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4212, ())) fun p_138 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_138.fst, Arg.imm 4, ())) fun p_139 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_139.fst, ())) fun p_140 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_140.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4213, ())) fun p_141 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_141.fst, Arg.imm 4, ())) fun p_142 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_142.fst, ())) fun p_143 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_143.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4214, ())) fun p_144 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_144.fst, Arg.imm 4, ())) fun p_145 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_145.fst, ())) fun p_146 =>
  Expr.store (t := i32) (Arg.var mv_s) (Arg.var p_146.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4215, ())) fun p_147 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_147.fst, Arg.imm 4, ())) fun p_148 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_148.fst, ())) fun p_149 =>
  Expr.store (t := i32) (Arg.var mv4) (Arg.var p_149.fst)
  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4216, ())) fun p_150 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_150.fst, Arg.imm 4, ())) fun p_151 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_151.fst, ())) fun p_152 =>
  Expr.store (t := i32) (Arg.var mv2) (Arg.var p_152.fst) K_after))))))))))))))))))))))))

theorem fid_k6c_tmk_clear_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_after : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {nv : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s)
    (htmp : tmp.length = c.max_vars)
    (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars)
    (hscr : scr.length = c.scratch_cap)
    (hreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hK : ∀ (tmk' : List (BitVec 32)) (m' : Mem 64),
      tmk'.length = 2 * c.max_vars →
      TmkZero (FidP6Work s tmp wsort tmk' scr) →
      (FullMem c (FidP6Work s tmp wsort tmk' scr) ⋆ R) m' →
      wp Γ Q X K_after m') :
    wp Γ Q X (fidK6cTmkClearExpr c nv K_after) m := by
  have hcur_le : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hmaxv_lt : c.max_vars < 2 ^ 30 := by
    have := c.hmaxv
    have hdb : dimacsBound = 2 ^ 28 := rfl
    omega
  apply wp_loop_inv
    (Inv := fun (p : BitVec 32 × Unit) m1 => ∃ tmk1 : List (BitVec 32),
      p.1.toNat ≤ nv.toNat ∧ tmk1.length = 2 * c.max_vars ∧
      FidK6cTmkClearInv p.1.toNat nv.toNat s.core.cur_vars wsort tmk1 ∧
      (FullMem c (FidP6Work s tmp wsort tmk1 scr) ⋆ R) m1)
    (μ := fun (p : BitVec 32 × Unit) _ => nv.toNat - p.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ _ _ ⟨tmk, Nat.zero_le _, htmk, fid_k6c_tmkClear_init hreg, hm⟩
  · intro J p m1 ⟨tmk1, hp_le, htmk1_len, hclr1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    have hlok1 : FullState.LengthsOk c (FidP6Work s tmp wsort tmk1 scr) :=
      fid_k6c_work_lengthsOk hinv.1 htmp hwsort htmk1_len hscr
    c0_hsteps
    · have hp_lt : p.fst.toNat < nv.toNat := by bv_omega
      have hw_lt : p.fst.toNat < wsort.length := by have := hreg.1; omega
      have hreg_p := hclr1.2.1 p.fst.toNat (Nat.le_refl _) hp_lt
      rw [List.getElem?_eq_getElem hw_lt, Option.getD_some] at hreg_p
      have he_lt : wsort[p.fst.toNat].toNat < s.core.cur_vars := hreg_p.1
      have ht_lt : wsort[p.fst.toNat].toNat < tmk1.length := by omega
      have hmod_p : p.fst.toNat % 2 ^ 64 = p.fst.toNat := by
        have := BitVec.isLt p.fst; exact Nat.mod_eq_of_lt (by omega)
      have hw_mod : p.fst.toNat % 2 ^ 64 <
          (FidP6Work s tmp wsort tmk1 scr).scratch.wsort.length := by
        dsimp only [FidP6Work]; omega
      have hw_el : wsort[p.fst.toNat % 2 ^ 64] = wsort[p.fst.toNat] := by
        congr 1
      have ht_mod : wsort[p.fst.toNat % 2 ^ 64].toNat % 2 ^ 64 <
          (FidP6Work s tmp wsort tmk1 scr).scratch.tarjan_mark.length := by
        dsimp only [FidP6Work]; rw [hw_el]
        have := BitVec.isLt wsort[p.fst.toNat]; rw [Nat.mod_eq_of_lt (by omega)]; exact ht_lt
      c0_hsteps
      have hclr2 := fid_k6c_tmkClear_step hclr1 hp_lt hw_lt (by omega)
      have hp1_toNat : (p.fst + 1).toNat = p.fst.toNat + 1 := by
        simpa using fid_k6c_add1_toNat hp_lt (by omega)
      have htmk2_len : (tmk1.set wsort[p.fst.toNat].toNat 0#32).length = 2 * c.max_vars := by
        rw [List.length_set]; exact htmk1_len
      have hidx_e :
          (BitVec.setWidth 64 wsort[(BitVec.setWidth 64 p.fst).toNat]).toNat =
          wsort[p.fst.toNat].toNat := by
        rw [fid_zext32_toNat]
        have hzw : (BitVec.setWidth 64 p.fst).toNat = p.fst.toNat := fid_zext32_toNat p.fst
        congr 1
      rw [hidx_e] at hm
      refine hcont _ m (by dsimp only; rw [hp1_toNat]; omega)
        ⟨tmk1.set wsort[p.fst.toNat].toNat 0#32, by dsimp only; rw [hp1_toNat]; omega,
          htmk2_len, ?_, hm⟩
      dsimp only; rw [hp1_toNat]; exact hclr2
    · have hp_eq : p.fst.toNat = nv.toNat := by bv_omega
      rw [hp_eq] at hclr1
      exact hK tmk1 m1 htmk1_len (fid_k6c_tmkClear_done hclr1) hm1

private theorem fid_k6c_triv_mask_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr scr0 : List (BitVec 32)}
    {eid mbase : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s) (hcap : 16384 ≤ c.scratch_cap)
    (hscr : scr.length = c.scratch_cap)
    (hmbase : mbase = 4002#32 ∨ mbase = 4066#32) (heid : eid.toNat < 2001)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i, i < 4002 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidK6cTrivMaskBody c eid mbase) m := by
  apply wp_loop_inv
    (Inv := fun (pk : BitVec 32 × Unit) m1 => ∃ scr1 : List (BitVec 32),
      pk.1.toNat ≤ 128 ∧ scr1.length = c.scratch_cap ∧
      (∀ i, i < 4002 → scr1[i]? = scr0[i]?) ∧
      (∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = scr0[i]?) ∧
      (FullMem c (FidP6Scr s scr1) ⋆ R) m1)
    (μ := fun (pk : BitVec 32 × Unit) _ => 128 - pk.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ _ _ ⟨scr, Nat.zero_le _, hscr, hpre0, hpre1, hm⟩
  · intro J pk m1 ⟨scr1, hk_le, hlen1, hp0, hp1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps
    · have hk_lt : pk.fst.toNat < 128 := by bv_omega
      have h4002 : (4002 + pk.fst).toNat = 4002 + pk.fst.toNat := by bv_omega
      have hk_idx : (BitVec.setWidth 64 (4002 + pk.fst)).toNat = 4002 + pk.fst.toNat := by
        rw [fid_zext32_toNat, h4002]
      have hk_mod : (4002 + pk.fst).toNat % 2 ^ 64 <
          (FidP6Scr s scr1).scratch.scratch_buf.length := by
        dsimp only [FidP6Scr]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      c0_hsteps
      have hk1_toNat : (pk.fst + 1).toNat = pk.fst.toNat + 1 := by
        simpa using fid_k6c_add1_toNat hk_lt (by omega)
      rw [hk_idx] at hm
      let scr2 := scr1.set (4002 + pk.fst.toNat) 0#32
      have hp0' : ∀ i, i < 4002 → scr2[i]? = scr0[i]? := fun i hi => by
        rw [List.getElem?_set_ne (by omega)]; exact hp0 i hi
      have hp1' : ∀ i, 4132 ≤ i → i < 4192 → scr2[i]? = scr0[i]? := fun i h1 h2 => by
        rw [List.getElem?_set_ne (by omega)]; exact hp1 i h1 h2
      refine hcont _ m (by dsimp only; rw [hk1_toNat]; omega)
        ⟨scr2, by dsimp only; rw [hk1_toNat]; omega, by simp [scr2, hlen1], hp0', hp1', hm⟩
    · have mw := fid_k6c_mask_widx hmbase heid
      have hw_lo : 4002 ≤ (mbase + eid >>> 5#32).toNat := mw.1
      have hw_hi : (mbase + eid >>> 5#32).toNat < 4130 := mw.2.1
      have hw_zext : (BitVec.setWidth 64 (mbase + eid >>> 5)).toNat <
          (FidP6Scr s scr1).scratch.scratch_buf.length := by
        dsimp only [FidP6Scr]; rw [fid_zext32_toNat]; exact Nat.lt_of_lt_of_le hw_hi (by omega)
      have hw_eq : (BitVec.setWidth 64 (mbase + eid >>> 5)).toNat =
          (mbase + eid >>> 5#32).toNat := fid_zext32_toNat _
      c0_hsteps
      rw [hw_eq] at hm
      let scr2 := scr1.set (mbase + eid >>> 5#32).toNat
        ((1 : BitVec 32) <<< ((eid &&& 31).toNat % 32))
      have hlen2 : scr2.length = c.scratch_cap := by simp [scr2, hlen1]
      have hm2 : (FullMem c (FidP6Scr s scr2) ⋆ R) m := by
        simpa only [FidP6Scr, scr2] using hm
      have h4130 : (4130 : Nat) < (FidP6Scr s scr2).scratch.scratch_buf.length := by
        dsimp only [FidP6Scr]; omega
      c0_hsteps
      let scr3 := scr2.set 4130 (1 : BitVec 32)
      have hlen3 : scr3.length = c.scratch_cap := by simp [scr3, hlen2]
      have hm3 : (FullMem c (FidP6Scr s scr3) ⋆ R) m := by
        have m4130 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4130)).toNat = 4130 := rfl
        simpa only [FidP6Scr, scr3, m4130] using hm
      have h4131 : (4131 : Nat) < (FidP6Scr s scr3).scratch.scratch_buf.length := by
        dsimp only [FidP6Scr]; omega
      c0_hsteps
      let scr4 := scr3.set 4131 (1 : BitVec 32)
      have hlen4 : scr4.length = c.scratch_cap := by simp [scr4, hlen3]
      have hinv4 : FullDenseInvW c F0 F_cur (FidP6Scr s scr4) :=
        m8_fullDenseInvW_scr hinv hlen4
      have hpre0_4 : ∀ i, i < 4002 → (FidP6Scr s scr4).scratch.scratch_buf[i]? = scr0[i]? :=
        fun i hi => by
          dsimp only [FidP6Scr, scr4, scr3, scr2]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
          exact hp0 i hi
      have hpre1_4 : ∀ i, 4132 ≤ i → i < 4192 →
          (FidP6Scr s scr4).scratch.scratch_buf[i]? = scr0[i]? := fun i h1 h2 => by
        dsimp only [FidP6Scr, scr4, scr3, scr2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]
        exact hp1 i h1 h2
      have m4131 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4131)).toNat = 4131 := rfl
      rw [m4131] at hm
      exact hQ true (FidP6Scr s scr4) _ hinv4 htmk rfl rfl rfl (Nat.le_refl _)
        hpre0_4 hpre1_4 hm

theorem fid_k6c_triv_unit_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr scr0 : List (BitVec 32)} {triv_unit : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s) (hcap : 16384 ≤ c.scratch_cap)
    (hscr : scr.length = c.scratch_cap)
    (heid : (triv_unit &&& 2047#32).toNat < 2001)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i, i < 4002 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidK6cTrivUnitExpr c triv_unit) m := by
  dsimp only [fidK6cTrivUnitExpr]
  c0_hsteps
  · exact fid_k6c_triv_mask_wp hinv htmk hcap hscr (Or.inl rfl) heid hpre0 hpre1 hm hQ
  · exact fid_k6c_triv_mask_wp hinv htmk hcap hscr (Or.inr rfl) heid hpre0 hpre1 hm hQ

private theorem fid_k6c_init_vars_suffix {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {Js : Cont [i32]} {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr scr2 : List (BitVec 32)} {pi_v nv mv_s o_lvl o_next : BitVec 32} {pv : Val i32}
    (hscr : scr.length = c.scratch_cap) (hmv_hi : mv_s.toNat ≤ 8192)
    (hcap : 4224 + 45 * mv_s.toNat ≤ scr.length) (_hscr_lt : scr.length < 2 ^ 30)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (hpi_lt : pi_v.toNat < nv.toNat)
    (ho2 : o_lvl = 4224#32 + 2#32 * mv_s) (ho3 : o_next = 4224#32 + 3#32 * mv_s)
    (hlen2 : scr2.length = c.scratch_cap)
    (hag2 : ∀ idx, idx < scr.length → (idx < 4224 ∨ 4224 + 9 * mv_s.toNat ≤ idx) →
      scr2[idx]? = scr[idx]?)
    (hm2 : (FullMem c (FidP6Scr s scr2) ⋆ R) m)
    (hcont : ∀ (ys : Tup Val [i32]) (m' : Mem 64),
      nv.toNat - ys.fst.toNat < nv.toNat - pi_v.toNat →
      (∃ scr1, ys.fst.toNat ≤ nv.toNat ∧ scr1.length = c.scratch_cap ∧
        (∀ idx, idx < scr.length → (idx < 4224 ∨ 4224 + 9 * mv_s.toNat ≤ idx) →
          scr1[idx]? = scr[idx]?) ∧
        (FullMem c (FidP6Scr s scr1) ⋆ R) m') → Js ys m') :
    wp Γ Q X
      (Expr.store (Arg.var pv)
        (Arg.var (c.pScratchBuf + BitVec.setWidth 64 (o_lvl + pi_v) * 4, ()).fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_next, Arg.var pi_v, ())) fun p_23 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_23.fst, ())) fun p_24 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_24.fst, Arg.imm 4, ())) fun p_25 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_25.fst, ()))
          fun p_26 =>
        Expr.group (fun _ : Tup Cont [[i32]] => Blocks.cons (fun pn : Tup Val [i32] =>
          Expr.store (Arg.var pn.fst) (Arg.var p_26.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi_v, Arg.imm 1, ())) fun p_27 =>
            Expr.jump Js (Arg.var p_27.fst, ()))) Blocks.nil)
        fun Js_2 =>
        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi_v, Arg.imm 1, ())) fun p_27 =>
        Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var p_27.fst, Arg.var nv, ()))
          fun p_28 =>
        Expr.jnz (Arg.var p_28.fst)
          (Expr.jump Js_2.fst (Arg.imm 4294967295, ()))
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi_v, Arg.imm 1, ())) fun p_29 =>
          Expr.jump Js_2.fst (Arg.var p_29.fst, ())))) m := by
  have hpi_mv : pi_v.toNat < mv_s.toNat := by omega
  have hidx2 : (o_lvl + pi_v).toNat = 4224 + 2 * mv_s.toNat + pi_v.toNat := by
    rw [← fid_zext32_toNat (o_lvl + pi_v), ho2]
    exact fid_k6_off_add (k := 2) hmv_hi (by omega) (by omega)
  have hidx3 : (o_next + pi_v).toNat = 4224 + 3 * mv_s.toNat + pi_v.toNat := by
    rw [← fid_zext32_toNat (o_next + pi_v), ho3]
    exact fid_k6_off_add (k := 3) hmv_hi (by omega) (by omega)
  have hidx2' : (BitVec.setWidth 64 (o_lvl + pi_v)).toNat =
      4224 + 2 * mv_s.toNat + pi_v.toNat := by rw [fid_zext32_toNat, hidx2]
  have hidx3' : (BitVec.setWidth 64 (o_next + pi_v)).toNat =
      4224 + 3 * mv_s.toNat + pi_v.toNat := by rw [fid_zext32_toNat, hidx3]
  have hi1_toNat : (pi_v + 1).toNat = pi_v.toNat + 1 := by
    simpa using fid_k6c_add1_toNat hpi_lt (by omega)
  have hb2 : (o_lvl + pi_v).toNat % 2 ^ 64 <
      (FidP6Scr s scr2).scratch.scratch_buf.length := by
    dsimp only [FidP6Scr]; have := BitVec.isLt (o_lvl + pi_v)
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hb3 : (o_next + pi_v).toNat % 2 ^ 64 <
      (scr2.set (BitVec.setWidth 64 (o_lvl + pi_v)).toNat pv).length := by
    rw [List.length_set]; have := BitVec.isLt (o_next + pi_v)
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  c0_hsteps
  · let scr4 := (scr2.set (4224 + 2 * mv_s.toNat + pi_v.toNat) pv).set
      (4224 + 3 * mv_s.toNat + pi_v.toNat) (4294967295 : BitVec 32)
    rw [hidx2', hidx3'] at hm
    exact hcont (pi_v + 1, ()) m (by rw [hi1_toNat]; omega)
      ⟨scr4, by rw [hi1_toNat]; omega, by simp [scr4, hlen2],
        fun idx hidx hr => by
          dsimp only [scr4]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact hag2 idx hidx hr,
        hm⟩
  · let scr4 := (scr2.set (4224 + 2 * mv_s.toNat + pi_v.toNat) pv).set
      (4224 + 3 * mv_s.toNat + pi_v.toNat) (pi_v + 1)
    rw [hidx2', hidx3'] at hm
    exact hcont (pi_v + 1, ()) m (by rw [hi1_toNat]; omega)
      ⟨scr4, by rw [hi1_toNat]; omega, by simp [scr4, hlen2],
        fun idx hidx hr => by
          dsimp only [scr4]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact hag2 idx hidx hr,
        hm⟩

theorem fid_k6c_init_vars_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_after : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr : List (BitVec 32)} {nv mv_s o_vals o_lvl o_next o_prev o_phase : BitVec 32}
    (_hlen : FullState.LengthsOk c s) (hscr : scr.length = c.scratch_cap)
    (hmv_hi : mv_s.toNat ≤ 8192)
    (hcap : 4224 + 45 * mv_s.toNat ≤ scr.length)
    (hscr_lt : scr.length < 2 ^ 30)
    (hnv_le : nv.toNat ≤ mv_s.toNat)
    (ho1 : o_vals = 4224#32 + mv_s) (ho2 : o_lvl = 4224#32 + 2#32 * mv_s)
    (ho3 : o_next = 4224#32 + 3#32 * mv_s) (ho4 : o_prev = 4224#32 + 4#32 * mv_s)
    (ho5 : o_phase = 4224#32 + 6#32 * mv_s)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hK : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ idx, idx < scr.length → (idx < 4224 ∨ 4224 + 9 * mv_s.toNat ≤ idx) →
        scr'[idx]? = scr[idx]?) →
      (FullMem c (FidP6Scr s scr') ⋆ R) m' → wp Γ Q X K_after m') :
    wp Γ Q X (fidK6cInitVarsExpr c nv o_vals o_lvl o_next o_prev o_phase K_after) m := by
  apply wp_loop_inv
    (Inv := fun (pi : BitVec 32 × Unit) m1 => ∃ scr1 : List (BitVec 32),
      pi.1.toNat ≤ nv.toNat ∧ scr1.length = c.scratch_cap ∧
      (∀ idx, idx < scr.length → (idx < 4224 ∨ 4224 + 9 * mv_s.toNat ≤ idx) →
        scr1[idx]? = scr[idx]?) ∧
      (FullMem c (FidP6Scr s scr1) ⋆ R) m1)
    (μ := fun (pi : BitVec 32 × Unit) _ => nv.toNat - pi.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ (0#32, ()) m ⟨scr, Nat.zero_le _, hscr, fun _ _ _ => rfl, hm⟩
  · intro J pi m1 ⟨scr1, hi_le, hlen1, hag1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps
    · have hi_lt : pi.fst.toNat < nv.toNat := by bv_omega
      have hi_mv : pi.fst.toNat < mv_s.toNat := by omega
      have hidx0 : (4224#32 + pi.fst).toNat = 4224 + pi.fst.toNat := by bv_omega
      have hidx1 : (o_vals + pi.fst).toNat = 4224 + mv_s.toNat + pi.fst.toNat := by
        rw [← fid_zext32_toNat (o_vals + pi.fst), ho1]
        exact fid_k6_off_add1 hmv_hi (by omega)
      have hidx5 : (o_phase + pi.fst).toNat = 4224 + 6 * mv_s.toNat + pi.fst.toNat := by
        rw [← fid_zext32_toNat (o_phase + pi.fst), ho5]
        exact fid_k6_off_add (k := 6) hmv_hi (by omega) (by omega)
      have hidx4 : (o_prev + pi.fst).toNat = 4224 + 4 * mv_s.toNat + pi.fst.toNat := by
        rw [← fid_zext32_toNat (o_prev + pi.fst), ho4]
        exact fid_k6_off_add (k := 4) hmv_hi (by omega) (by omega)
      have hb0 : (4224#32 + pi.fst).toNat % 2 ^ 64 <
          (FidP6Scr s scr1).scratch.scratch_buf.length := by
        dsimp only [FidP6Scr]
        rw [Nat.mod_eq_of_lt (by have := BitVec.isLt (4224#32 + pi.fst); omega)]; omega
      have hb1 : (o_vals + pi.fst).toNat % 2 ^ 64 <
          (scr1.set ((4224#32 + pi.fst).toNat % 2 ^ 64) 0#32).length := by
        rw [List.length_set, Nat.mod_eq_of_lt (by have := BitVec.isLt (o_vals + pi.fst); omega)]
        omega
      have hb5 : (o_phase + pi.fst).toNat % 2 ^ 64 <
          ((scr1.set ((4224#32 + pi.fst).toNat % 2 ^ 64) 0#32).set
            ((o_vals + pi.fst).toNat % 2 ^ 64) 4294967295#32).length := by
        simp only [List.length_set]
        rw [Nat.mod_eq_of_lt (by have := BitVec.isLt (o_phase + pi.fst); omega)]; omega
      have hb4 : (o_prev + pi.fst).toNat % 2 ^ 64 <
          (((scr1.set ((4224#32 + pi.fst).toNat % 2 ^ 64) 0#32).set
            ((o_vals + pi.fst).toNat % 2 ^ 64) 4294967295#32).set
            ((o_phase + pi.fst).toNat % 2 ^ 64) 0#32).length := by
        simp only [List.length_set]
        rw [Nat.mod_eq_of_lt (by have := BitVec.isLt (o_prev + pi.fst); omega)]; omega
      have m0 : (BitVec.setWidth 64 (4224 + pi.fst)).toNat = 4224 + pi.fst.toNat := by
        rw [fid_zext32_toNat]; simpa using hidx0
      have m1' : (BitVec.setWidth 64 (o_vals + pi.fst)).toNat =
          4224 + mv_s.toNat + pi.fst.toNat := by rw [fid_zext32_toNat, hidx1]
      have m5 : (BitVec.setWidth 64 (o_phase + pi.fst)).toNat =
          4224 + 6 * mv_s.toNat + pi.fst.toNat := by rw [fid_zext32_toNat, hidx5]
      have m4 : (BitVec.setWidth 64 (o_prev + pi.fst)).toNat =
          4224 + 4 * mv_s.toNat + pi.fst.toNat := by rw [fid_zext32_toNat, hidx4]
      let scr2 :=
        ((((scr1.set (4224 + pi.fst.toNat) (0 : BitVec 32)).set
          (4224 + mv_s.toNat + pi.fst.toNat) (4294967295 : BitVec 32)).set
          (4224 + 6 * mv_s.toNat + pi.fst.toNat) (0 : BitVec 32)).set
          (4224 + 4 * mv_s.toNat + pi.fst.toNat) (pi.fst + 1))
      have hlen2 : scr2.length = c.scratch_cap := by simp [scr2, hlen1]
      have hag2 : ∀ idx, idx < scr.length → (idx < 4224 ∨ 4224 + 9 * mv_s.toNat ≤ idx) →
          scr2[idx]? = scr[idx]? := fun idx hidx hr => by
        dsimp only [scr2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hag1 idx hidx hr
      c0_hsteps
      · have hm2 : (FullMem c (FidP6Scr s scr2) ⋆ R) m := by
          simpa only [FidP6Scr, scr2, m0, m1', m5, m4] using hm
        exact fid_k6c_init_vars_suffix hscr hmv_hi hcap hscr_lt hnv_le hi_lt ho2 ho3
          hlen2 hag2 hm2 hcont
      · have hm2 : (FullMem c (FidP6Scr s scr2) ⋆ R) m := by
          simpa only [FidP6Scr, scr2, m0, m1', m5, m4] using hm
        exact fid_k6c_init_vars_suffix hscr hmv_hi hcap hscr_lt hnv_le hi_lt ho2 ho3
          hlen2 hag2 hm2 hcont
    · exact hK scr1 m1 hlen1 hag1 hm1

theorem fid_k6c_init_lits_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_after : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr : List (BitVec 32)} {nv mv_s o_whead o_wtail : BitVec 32}
    (_hlen : FullState.LengthsOk c s) (hscr : scr.length = c.scratch_cap)
    (hmv_hi : mv_s.toNat ≤ 8192)
    (hcap : 4224 + 45 * mv_s.toNat ≤ scr.length)
    (hscr_lt : scr.length < 2 ^ 30)
    (hnv_le : nv.toNat ≤ mv_s.toNat)
    (ho9 : o_whead = 4224#32 + 9#32 * mv_s)
    (ho11 : o_wtail = 4224#32 + 11#32 * mv_s)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hK : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ idx, idx < scr.length → (idx < 4224 + 9 * mv_s.toNat ∨ 4224 + 29 * mv_s.toNat ≤ idx) →
        scr'[idx]? = scr[idx]?) →
      (FullMem c (FidP6Scr s scr') ⋆ R) m' → wp Γ Q X K_after m') :
    wp Γ Q X (fidK6cInitLitsExpr c nv o_whead o_wtail K_after) m := by
  apply wp_loop_inv
    (Inv := fun (pl : BitVec 32 × Unit) m1 => ∃ scr1 : List (BitVec 32),
      pl.1.toNat ≤ 2 * nv.toNat ∧ scr1.length = c.scratch_cap ∧
      (∀ idx, idx < scr.length → (idx < 4224 + 9 * mv_s.toNat ∨ 4224 + 29 * mv_s.toNat ≤ idx) →
        scr1[idx]? = scr[idx]?) ∧
      (FullMem c (FidP6Scr s scr1) ⋆ R) m1)
    (μ := fun (pl : BitVec 32 × Unit) _ => 2 * nv.toNat - pl.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ (0#32, ()) m ⟨scr, Nat.zero_le _, hscr, fun _ _ _ => rfl, hm⟩
  · intro J pl m1 ⟨scr1, hl_le, hlen1, hag1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps
    · have hshl1 : (nv <<< (1 : BitVec 32)).toNat = 2 * nv.toNat :=
        (fid_k6c_bv32_shl1_add1_lt (x := nv) (n := 8193) (by omega) (by decide)).1
      have hc' : pl.fst.toNat < (nv <<< (1 : BitVec 32)).toNat := hc
      have hl_lt : pl.fst.toNat < 2 * nv.toNat := by rw [hshl1] at hc'; exact hc'
      have hl_2mv : pl.fst.toNat < 2 * mv_s.toNat := by omega
      have hidx9 : (o_whead + pl.fst).toNat = 4224 + 9 * mv_s.toNat + pl.fst.toNat := by
        rw [← fid_zext32_toNat (o_whead + pl.fst), ho9]
        exact fid_k6_off_add (k := 9) hmv_hi (by omega) (by omega)
      have hidx11 : (o_wtail + pl.fst).toNat = 4224 + 11 * mv_s.toNat + pl.fst.toNat := by
        rw [← fid_zext32_toNat (o_wtail + pl.fst), ho11]
        exact fid_k6_off_add (k := 11) hmv_hi (by omega) (by omega)
      have hb9 : (o_whead + pl.fst).toNat % 2 ^ 64 <
          (FidP6Scr s scr1).scratch.scratch_buf.length := by
        dsimp only [FidP6Scr]; have := BitVec.isLt (o_whead + pl.fst)
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hb11 : (o_wtail + pl.fst).toNat % 2 ^ 64 <
          (scr1.set ((o_whead + pl.fst).toNat % 2 ^ 64) 0#32).length := by
        rw [List.length_set]; have := BitVec.isLt (o_wtail + pl.fst)
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      c0_hsteps
      let scr2 := (scr1.set (4224 + 9 * mv_s.toNat + pl.fst.toNat) (0 : BitVec 32)).set
        (4224 + 11 * mv_s.toNat + pl.fst.toNat) (4294967295 : BitVec 32)
      have hlen2 : scr2.length = c.scratch_cap := by simp [scr2, hlen1]
      have hag2 : ∀ idx, idx < scr.length →
          (idx < 4224 + 9 * mv_s.toNat ∨ 4224 + 29 * mv_s.toNat ≤ idx) →
          scr2[idx]? = scr[idx]? := fun idx hidx hr => by
        dsimp only [scr2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hag1 idx hidx hr
      have hl1_toNat : (pl.fst + 1).toNat = pl.fst.toNat + 1 := by
        simpa using fid_k6c_add1_toNat hl_lt (by omega)
      have m9 : (BitVec.setWidth 64 (o_whead + pl.fst)).toNat =
          4224 + 9 * mv_s.toNat + pl.fst.toNat := by
        rw [fid_zext32_toNat, hidx9]
      have m11 : (BitVec.setWidth 64 (o_wtail + pl.fst)).toNat =
          4224 + 11 * mv_s.toNat + pl.fst.toNat := by
        rw [fid_zext32_toNat, hidx11]
      have hm2 : (FullMem c (FidP6Scr s scr2) ⋆ R) m := by
        simpa only [FidP6Scr, scr2, m9, m11] using hm
      exact hcont _ _ (by dsimp only; rw [hl1_toNat]; omega)
        ⟨scr2, by dsimp only; rw [hl1_toNat]; omega, hlen2, hag2, hm2⟩
    · exact hK scr1 m1 hlen1 hag1 hm1

private theorem fid_k6c_sc_var {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr : List (BitVec 32)} {k v : BitVec 32} {K : Expr Val Cont [Ty.bool]}
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hscr : scr.length = c.scratch_cap) (hk : k.toNat < c.scratch_cap)
    (hK : ∀ m', (scr.set k.toNat v).length = c.scratch_cap →
      (FullMem c (FidP6Scr s (scr.set k.toNat v)) ⋆ R) m' → wp Γ Q X K m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm k, ())) fun p1 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ())) fun p2 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p2.fst, ()))
         fun p3 =>
       Expr.store (t := i32) (Arg.var v) (Arg.var p3.fst) K) m := by
  have hk' : (BitVec.setWidth 64 k).toNat % 2 ^ 64 <
      (FidP6Scr s scr).scratch.scratch_buf.length := by
    dsimp only [FidP6Scr]; rw [fid_zext32_toNat]
    rw [Nat.mod_eq_of_lt (by have := BitVec.isLt k; omega)]; omega
  c0_hsteps; rw [fid_zext32_toNat] at hm
  exact hK m (by simp [hscr]) hm

private theorem fid_k6c_sc_imm {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr : List (BitVec 32)} {k v : BitVec 32} {K : Expr Val Cont [Ty.bool]}
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hscr : scr.length = c.scratch_cap) (hk : k.toNat < c.scratch_cap)
    (hK : ∀ m', (scr.set k.toNat v).length = c.scratch_cap →
      (FullMem c (FidP6Scr s (scr.set k.toNat v)) ⋆ R) m' → wp Γ Q X K m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm k, ())) fun p1 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ())) fun p2 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p2.fst, ()))
         fun p3 =>
       Expr.store (t := i32) (Arg.imm v) (Arg.var p3.fst) K) m := by
  have hk' : (BitVec.setWidth 64 k).toNat % 2 ^ 64 <
      (FidP6Scr s scr).scratch.scratch_buf.length := by
    dsimp only [FidP6Scr]; rw [fid_zext32_toNat]
    rw [Nat.mod_eq_of_lt (by have := BitVec.isLt k; omega)]; omega
  c0_hsteps; rw [fid_zext32_toNat] at hm
  exact hK m (by simp [hscr]) hm

private theorem fid_k6c_sc_sub1 {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr : List (BitVec 32)} {k nv : BitVec 32} {K : Expr Val Cont [Ty.bool]}
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hscr : scr.length = c.scratch_cap) (hk : k.toNat < c.scratch_cap)
    (hK : ∀ m', (scr.set k.toNat (nv - 1)).length = c.scratch_cap →
      (FullMem c (FidP6Scr s (scr.set k.toNat (nv - 1))) ⋆ R) m' → wp Γ Q X K m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm k, ())) fun p1 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ())) fun p2 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p2.fst, ()))
         fun p3 =>
       Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p4 =>
       Expr.store (t := i32) (Arg.var p4.fst) (Arg.var p3.fst) K) m := by
  have hk' : (BitVec.setWidth 64 k).toNat % 2 ^ 64 <
      (FidP6Scr s scr).scratch.scratch_buf.length := by
    dsimp only [FidP6Scr]; rw [fid_zext32_toNat]
    rw [Nat.mod_eq_of_lt (by have := BitVec.isLt k; omega)]; omega
  c0_hsteps
  rw [fid_zext32_toNat] at hm
  exact hK m (by simp [hscr]) hm

private theorem fid_k6c_scalars_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_after : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr : List (BitVec 32)}
    {mv_s mv4 mv2 acap_s nv nc alen n_units tick_lim : BitVec 32}
    (_hlen : FullState.LengthsOk c s) (hscr : scr.length = c.scratch_cap)
    (hcap : 16384 ≤ c.scratch_cap)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hK : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ i, i < 4192 → scr'[i]? = scr[i]?) →
      (∀ i, 4224 ≤ i → scr'[i]? = scr[i]?) →
      scr'[4193]? = some nc → scr'[4194]? = some nc →
      scr'[4206]? = some alen → scr'[4207]? = some acap_s → scr'[4214]? = some mv_s →
      (FullMem c (FidP6Scr s scr') ⋆ R) m' → wp Γ Q X K_after m') :
    wp Γ Q X (fidK6cScalarsExpr c mv_s mv4 mv2 acap_s nv nc alen n_units tick_lim K_after) m := by
  dsimp only [fidK6cScalarsExpr]
  have hlen_cur : scr.length = c.scratch_cap := hscr
  iterate 25
    (first
      | (apply fid_k6c_sc_var
         · exact hm
         · exact hlen_cur
         · exact Nat.lt_of_lt_of_le (m := 16384) (by decide) hcap
         clear hm hlen_cur; intro m hlen_cur hm)
      | (apply fid_k6c_sc_imm
         · exact hm
         · exact hlen_cur
         · exact Nat.lt_of_lt_of_le (m := 16384) (by decide) hcap
         clear hm hlen_cur; intro m hlen_cur hm)
      | (apply fid_k6c_sc_sub1
         · exact hm
         · exact hlen_cur
         · exact Nat.lt_of_lt_of_le (m := 16384) (by decide) hcap
         clear hm hlen_cur; intro m hlen_cur hm))
  refine hK _ _ hlen_cur ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
  · intro i hi
    repeat rw [List.getElem?_set_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le (m := 4192) hi (by decide)))]
  · intro i hi
    repeat rw [List.getElem?_set_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (m := 4224) (by decide) hi))]
  · repeat' first | rw [List.getElem?_set_ne (by decide)] |
      rw [← show (4193 : BitVec 32).toNat = 4193 from rfl,
        List.getElem?_set_self (by
          simp only [List.length_set, hscr]
          exact Nat.lt_of_lt_of_le (m := 16384) (by decide) hcap)]
  · repeat' first | rw [List.getElem?_set_ne (by decide)] |
      rw [← show (4194 : BitVec 32).toNat = 4194 from rfl,
        List.getElem?_set_self (by
          simp only [List.length_set, hscr]
          exact Nat.lt_of_lt_of_le (m := 16384) (by decide) hcap)]
  · repeat' first | rw [List.getElem?_set_ne (by decide)] |
      rw [← show (4206 : BitVec 32).toNat = 4206 from rfl,
        List.getElem?_set_self (by
          simp only [List.length_set, hscr]
          exact Nat.lt_of_lt_of_le (m := 16384) (by decide) hcap)]
  · repeat' first | rw [List.getElem?_set_ne (by decide)] |
      rw [← show (4207 : BitVec 32).toNat = 4207 from rfl,
        List.getElem?_set_self (by
          simp only [List.length_set, hscr]
          exact Nat.lt_of_lt_of_le (m := 16384) (by decide) hcap)]
  · repeat' first | rw [List.getElem?_set_ne (by decide)] |
      rw [← show (4214 : BitVec 32).toNat = 4214 from rfl,
        List.getElem?_set_self (by
          simp only [List.length_set, hscr]
          exact Nat.lt_of_lt_of_le (m := 16384) (by decide) hcap)]

theorem fid_k6c_init_solve_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    (hwatch : ∀ a m Q X, fidK6WatchSpec a m Q X →
      Γ "full_k6_watch_fid" [i64, i32, i32, i32, i32] [] a m Q X)
    (hsolve : ∀ a m Q X, fidK6SolveSpec a m Q X →
      Γ "full_k6_solve_fid" [i64, i32] [i64] a m Q X)
    (hcore : ∀ a m Q X, fidK6CoreSpec a m Q X → Γ "full_k6_core_fid" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr scr0 : List (BitVec 32)}
    {mv_s mv4 mv2 o_vals o_lvl o_next o_prev o_phase o_whead o_wtail o_cl_off o_cl_meta
      o_cl_aux o_arena acap_s nv nc alen n_units triv_unit tick_lim : BitVec 32}
    {abort : Bool}
    (hinv : FullDenseInvW c F0 F_cur s) (hcap : 16384 ≤ c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hacap : 4224 + 45 * mv_s.toNat + acap_s.toNat ≤ c.scratch_cap)
    (ho1 : o_vals = 4224#32 + mv_s) (ho2 : o_lvl = 4224#32 + 2#32 * mv_s)
    (ho3 : o_next = 4224#32 + 3#32 * mv_s) (ho4 : o_prev = 4224#32 + 4#32 * mv_s)
    (ho5 : o_phase = 4224#32 + 6#32 * mv_s) (ho9 : o_whead = 4224#32 + 9#32 * mv_s)
    (ho11 : o_wtail = 4224#32 + 11#32 * mv_s) (ho29 : o_cl_off = 4224#32 + 29#32 * mv_s)
    (ho33 : o_cl_meta = 4224#32 + 33#32 * mv_s) (ho37 : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (ho45 : o_arena = 4224#32 + 45#32 * mv_s)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (_hnv_vars : nv.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : nc.toNat ≤ 2 * mv_s.toNat) (halen_le : alen.toNat ≤ acap_s.toNat)
    (_hnu_le : n_units.toNat ≤ nc.toNat)
    (htreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (htriv : triv_unit ≠ 4294967295#32 → (triv_unit &&& 2047#32).toNat < 2001)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i, i < 4002 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (fidK6cTmkClearExpr c nv
        (Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
          (Arg.var triv_unit, Arg.imm 4294967295, ())) fun p_73 =>
        Expr.jnz (Arg.var p_73.fst) (fidK6cTrivUnitExpr c triv_unit)
          (Expr.jnz (Arg.var abort) (Expr.ret (Arg.imm false, ()))
            (Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var nv, Arg.imm 0, ()))
              fun p_74 =>
            Expr.jnz (Arg.var p_74.fst) (Expr.ret (Arg.imm false, ()))
              (Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var nc, Arg.imm 2, ()))
                fun p_75 =>
              Expr.jnz (Arg.var p_75.fst) (Expr.ret (Arg.imm false, ()))
                (fidK6cScalarsExpr c mv_s mv4 mv2 acap_s nv nc alen n_units tick_lim
                  (fidK6cInitVarsExpr c nv o_vals o_lvl o_next o_prev o_phase
                    (fidK6cInitLitsExpr c nv o_whead o_wtail
                      (fidK6cWatchSolveExpr c nc tick_lim o_cl_off o_cl_meta o_cl_aux o_arena))
                    ))))))) m := by
  apply fid_k6c_tmk_clear_wp hinv htmp hwsort htmk hscr htreg hm
  intro tmk1 m1 htmk1_len htmk1_z hm1
  let s1 := FidP6Work s tmp wsort tmk1 scr
  have hinv1 : FullDenseInvW c F0 F_cur s1 :=
    fid_k6c_fullDenseInvW_work hinv htmp hwsort htmk1_len hscr
  have hm1' : (FullMem c (FidP6Scr s1 scr) ⋆ R) m1 := by
    rw [← fid_k6c_work_to_scr]; exact hm1
  c0_hsteps
  · exact fid_k6c_triv_unit_wp hinv1 htmk1_z hcap hscr (htriv (by bv_omega)) hpre0 hpre1 hm1' hQ
  · exact hQ false s1 m1 hinv1 htmk1_z rfl rfl rfl (Nat.le_refl _) hpre0 hpre1 hm1
  · exact hQ false s1 m1 hinv1 htmk1_z rfl rfl rfl (Nat.le_refl _) hpre0 hpre1 hm1
  · exact hQ false s1 m1 hinv1 htmk1_z rfl rfl rfl (Nat.le_refl _) hpre0 hpre1 hm1
  · have hscr_lt : scr.length < 2 ^ 30 := by
      have := c.hscr; have : dimacsBound = 2 ^ 28 := rfl; omega
    apply fid_k6c_scalars_wp hinv1.1 hscr hcap hm1'
    intro scr_sc m_sc hlen_sc hpre_sc hhi_sc
      h4193_sc h4194_sc h4206_sc h4207_sc h4214_sc hm_sc
    apply fid_k6c_init_vars_wp hinv1.1 hlen_sc hmv_hi (by omega) (by omega) hnv_le
      ho1 ho2 ho3 ho4 ho5 hm_sc
    intro scr_v m_v hlen_v hag_v hm_v
    apply fid_k6c_init_lits_wp hinv1.1 hlen_v hmv_hi (by omega) (by omega) hnv_le
      ho9 ho11 hm_v
    intro scr_l m_l hlen_l hag_l hm_l
    have hag_top : ∀ idx, 4224 + 29 * mv_s.toNat ≤ idx → idx < scr.length →
        scr_l[idx]? = scr[idx]? := fun idx h1 h2 => by
      rw [hag_l idx (by omega) (Or.inr h1), hag_v idx (by omega) (Or.inr (by omega)),
        hhi_sc idx (by omega)]
    have hcls_l : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr_l :=
      fid_k6c_clsOk_frame hcls fun idx h1 h2 => hag_top idx (by omega) (by omega)
    have h4193_l : scr_l[4193]? = some nc := by
      rw [hag_l 4193 (by omega) (Or.inl (by omega)),
        hag_v 4193 (by omega) (Or.inl (by omega)), h4193_sc]
    have h4194_l : scr_l[4194]? = some nc := by
      rw [hag_l 4194 (by omega) (Or.inl (by omega)),
        hag_v 4194 (by omega) (Or.inl (by omega)), h4194_sc]
    have h4206_l : scr_l[4206]? = some alen := by
      rw [hag_l 4206 (by omega) (Or.inl (by omega)),
        hag_v 4206 (by omega) (Or.inl (by omega)), h4206_sc]
    have h4207_l : scr_l[4207]? = some acap_s := by
      rw [hag_l 4207 (by omega) (Or.inl (by omega)),
        hag_v 4207 (by omega) (Or.inl (by omega)), h4207_sc]
    have h4214_l : scr_l[4214]? = some mv_s := by
      rw [hag_l 4214 (by omega) (Or.inl (by omega)),
        hag_v 4214 (by omega) (Or.inl (by omega)), h4214_sc]
    have hok_l : FidK6BufOk scr_l :=
      fid_k6c_bufOk_of_init hmv_lo hmv_hi (by omega) (by omega)
        h4193_l h4206_l h4207_l h4214_l (by omega) halen_le hcls_l
    have hpre0_l : ∀ i, i < 4002 → scr_l[i]? = scr0[i]? := fun i hi => by
      rw [hag_l i (by omega) (Or.inl (by omega)), hag_v i (by omega) (Or.inl (by omega)),
        hpre_sc i (by omega), hpre0 i hi]
    have hpre1_l : ∀ i, 4132 ≤ i → i < 4192 → scr_l[i]? = scr0[i]? := fun i h1 h2 => by
      rw [hag_l i (by omega) (Or.inl (by omega)), hag_v i (by omega) (Or.inl (by omega)),
        hpre_sc i (by omega), hpre1 i h1 h2]
    have haux_l : ∀ cid, cid < nc.toNat →
        let raw := scr_l[4224 + 37 * mv_s.toNat + cid]?.getD 0#32
        raw.toNat < 4096 ∧ (raw &&& 2047#32).toNat < 2001 := fun cid hcid => by
      have hc' := hcls_l.2.1 cid hcid
      exact ⟨hc'.2.2.1, hc'.2.2.2⟩
    exact fid_k6c_watch_solve_wp hwatch hsolve hcore hinv1 htmk1_z hcap hlen_l hmv_lo hmv_hi
      ho29 ho33 ho37 ho45 hok_l h4193_l h4194_l h4214_l haux_l hpre0_l hpre1_l hm_l hQ

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
