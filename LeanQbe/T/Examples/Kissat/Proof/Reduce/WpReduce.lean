/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reduce
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpReduceShared
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpReduceTail
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3

/-!
# Main WP Proof for `full_reduce_m6` (`Proof.Reduce.WpReduce`)

Proves `full_reduce_m6_wp` for `Src.Reduce.full_reduce_m6_body` against
`Spec.fullReduceM6Spec`, composing `WpReduceShared` and `WpReduceTail` with
zero legacy imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Reduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped FullArenaTactics

local macro "c0_hsteps_ng" : tactic => `(tactic| c0_hsteps_nogrp)

private def redCollectJrExpr (hdr pArena pRedRefs rc pos : BitVec 64) (next32 ld_6 : BitVec 32)
    (tier1 tier2 : BitVec 64) (Js_lp : Cont [i64, i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
      Expr.let_ {
          sig := [i32], code := OpCode.zext 32 64,
          args := (Arg.var next32, ()) } fun p_26 =>
      Expr.jump Js_lp (Arg.var p.fst, Arg.var p_26.fst, ())) Blocks.nil)
    fun Js_n =>
  Expr.let_ {
      sig := [i32, i32], code := OpCode.and i32,
      args := (Arg.var ld_6, Arg.imm 4194304, ()) } fun p_26 =>
  Expr.let_ {
      sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32,
      args := (Arg.var p_26.fst, Arg.imm 0, ()) } fun p_27 =>
  Expr.jnz (Arg.var p_27.fst)
    (Expr.let_ {
        sig := [i32, i32], code := OpCode.and i32,
        args := (Arg.var ld_6, Arg.imm 524288, ()) } fun p_28 =>
      Expr.let_ {
          sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32,
          args := (Arg.var p_28.fst, Arg.imm 0, ()) } fun p_29 =>
      Expr.jnz (Arg.var p_29.fst)
        (Expr.let_ {
            sig := [i32, i32], code := OpCode.lshr i32,
            args := (Arg.var ld_6, Arg.imm 27, ()) } fun p_30 =>
          Expr.let_ {
              sig := [i32, i32], code := OpCode.and i32,
              args := (Arg.var p_30.fst, Arg.imm 31, ()) } fun p_31 =>
          Expr.group (fun _Js_3 => Blocks.cons (fun (_ : Tup Val []) =>
              Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
                  Expr.jump Js_n.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_f =>
              Expr.let_ {
                  sig := [i32, i32], code := OpCode.and i32,
                  args := (Arg.var ld_6, Arg.imm 2097152, ()) } fun p_33 =>
              Expr.let_ {
                  sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32,
                  args := (Arg.var p_33.fst, Arg.imm 0, ()) } fun p_34 =>
              Expr.jnz (Arg.var p_34.fst)
                (Expr.let_ {
                    sig := [i32, i32], code := OpCode.and i32,
                    args := (Arg.var ld_6, Arg.imm 524287, ()) } fun p_35 =>
                  Expr.let_ {
                      sig := [i32], code := OpCode.zext 32 64,
                      args := (Arg.var p_35.fst, ()) } fun p_36 =>
                  Expr.group (fun _ => Blocks.cons (fun (p_37 : Tup Val [.bool]) =>
                      Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
                          Expr.jump Js_f.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_i =>
                      Expr.jnz (Arg.var p_37.fst) (Expr.jump Js_i.fst (Arg.var rc, ()))
                        (Expr.let_ {
                            sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var hdr, Arg.imm 440, ()) } fun p_cap =>
                          Expr.load i64 (Arg.var p_cap.fst) fun ld_cap =>
                          Expr.let_ {
                              sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
                              args := (Arg.var rc, Arg.var ld_cap, ()) } fun p_lt =>
                          Expr.jnz (Arg.var p_lt.fst)
                            (Expr.let_ {
                                sig := [i64, i64], code := OpCode.mul i64,
                                args := (Arg.var rc, Arg.imm 4, ()) } fun p_off =>
                              Expr.let_ {
                                  sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var pRedRefs, Arg.var p_off.fst, ()) } fun p_addr =>
                              Expr.let_ {
                                  sig := [i64], code := OpCode.trunc 64 32,
                                  args := (Arg.var pos, ()) } fun p_tr =>
                              Expr.store (Arg.var p_tr.fst) (Arg.var p_addr.fst)
                                (Expr.let_ {
                                    sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var rc, Arg.imm 1, ()) } fun p_rc1 =>
                                  Expr.jump Js_i.fst (Arg.var p_rc1.fst, ())))
                            (Expr.jump Js_i.fst (Arg.var rc, ())))) Blocks.nil)
                    (fun Js_k =>
                      Expr.group (fun _Js_4 => Blocks.cons (fun (_ : Tup Val []) =>
                          Expr.let_ {
                              sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64,
                              args := (Arg.var p_36.fst, Arg.var tier2, ()) } fun p_u1 =>
                          Expr.jnz (Arg.var p_u1.fst)
                            (Expr.let_ {
                                sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32,
                                args := (Arg.var p_31.fst, Arg.imm 30, ()) } fun p_u2 =>
                              Expr.jnz (Arg.var p_u2.fst)
                                (Expr.jump Js_k.fst (Arg.imm true, ()))
                                (Expr.jump Js_k.fst (Arg.imm false, ())))
                            (Expr.jump Js_k.fst (Arg.imm false, ()))) Blocks.nil)
                        (fun Js_4 =>
                          Expr.let_ {
                              sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64,
                              args := (Arg.var p_36.fst, Arg.var tier1, ()) } fun p_u1 =>
                          Expr.jnz (Arg.var p_u1.fst)
                            (Expr.let_ {
                                sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32,
                                args := (Arg.var p_31.fst, Arg.imm 0, ()) } fun p_u2 =>
                              Expr.jnz (Arg.var p_u2.fst)
                                (Expr.jump Js_k.fst (Arg.imm true, ()))
                                (Expr.jump Js_4.fst ()))
                            (Expr.jump Js_4.fst ()))))
                (Expr.jump Js_f.fst (Arg.var rc, ()))) Blocks.nil)
            (fun Js_3 =>
              Expr.let_ {
                  sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32,
                  args := (Arg.var p_31.fst, Arg.imm 0, ()) } fun p_ug =>
              Expr.jnz (Arg.var p_ug.fst)
                (Expr.let_ {
                    sig := [i64, i64], code := OpCode.mul i64,
                    args := (Arg.var pos, Arg.imm 4, ()) } fun p_off =>
                  Expr.let_ {
                      sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var pArena, Arg.var p_off.fst, ()) } fun p_addr =>
                  Expr.let_ {
                      sig := [i32, i32], code := OpCode.and i32,
                      args := (Arg.var ld_6, Arg.imm 134217727, ()) } fun p_lo =>
                  Expr.let_ {
                      sig := [i32, i32], code := OpCode.sub i32,
                      args := (Arg.var p_31.fst, Arg.imm 1, ()) } fun p_dec =>
                  Expr.let_ {
                      sig := [i32, i32], code := OpCode.shl i32,
                      args := (Arg.var p_dec.fst, Arg.imm 27, ()) } fun p_hi =>
                  Expr.let_ {
                      sig := [i32, i32], code := OpCode.or i32,
                      args := (Arg.var p_lo.fst, Arg.var p_hi.fst, ()) } fun p_nv =>
                  Expr.store (Arg.var p_nv.fst) (Arg.var p_addr.fst)
                    (Expr.jump Js_3.fst ()))
                (Expr.jump Js_3.fst ())))
        (Expr.jump Js_n.fst (Arg.var rc, ())))
    (Expr.jump Js_n.fst (Arg.var rc, ()))

private def redMarkGarbExpr (hdr pArena pRedRefs rc target : BitVec 64) (J4 : Cont []) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun Js_5 => Blocks.cons (fun (p_33 : Tup Val [i64]) =>
      Expr.let_ {
          sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
          args := (Arg.var p_33.fst, Arg.var target, ()) } fun p_34 =>
      Expr.jnz (Arg.var p_34.fst)
        (Expr.let_ {
            sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
            args := (Arg.var p_33.fst, Arg.var rc, ()) } fun p_35 =>
          Expr.jnz (Arg.var p_35.fst)
            (Expr.let_ {
                sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p_33.fst, Arg.imm 4, ()) } fun p_36 =>
              Expr.let_ {
                  sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var pRedRefs, Arg.var p_36.fst, ()) } fun p_37 =>
              Expr.load i32 (Arg.var p_37.fst) fun ld_6 =>
              Expr.let_ {
                  sig := [i32], code := OpCode.zext 32 64,
                  args := (Arg.var ld_6, ()) } fun p_38 =>
              Expr.let_ {
                  sig := [i64, i64], code := OpCode.mul i64,
                  args := (Arg.var p_38.fst, Arg.imm 4, ()) } fun p_39 =>
              Expr.let_ {
                  sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var pArena, Arg.var p_39.fst, ()) } fun p_40 =>
              Expr.load i32 (Arg.var p_40.fst) fun ld_7 =>
              Expr.group
                (fun _Js => Blocks.cons (fun (_ : Tup Val []) =>
                    Expr.let_ {
                        sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var p_33.fst, Arg.imm 1, ()) } fun p =>
                    Expr.jump Js_5.fst (Arg.var p.fst, ())) Blocks.nil)
                fun Js =>
              Expr.let_ {
                  sig := [i32, i32], code := OpCode.and i32,
                  args := (Arg.var ld_7, Arg.imm 524288, ()) } fun p_41 =>
              Expr.let_ {
                  sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32,
                  args := (Arg.var p_41.fst, Arg.imm 0, ()) } fun p_42 =>
              Expr.jnz (Arg.var p_42.fst)
                (Expr.let_ {
                    sig := [i64, i64], code := OpCode.mul i64,
                    args := (Arg.var p_38.fst, Arg.imm 4, ()) } fun p_43 =>
                  Expr.let_ {
                      sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var pArena, Arg.var p_43.fst, ()) } fun p_44 =>
                  Expr.let_ {
                      sig := [i32, i32], code := OpCode.or i32,
                      args := (Arg.var ld_7, Arg.imm 524288, ()) } fun p_45 =>
                  Expr.store (Arg.var p_45.fst) (Arg.var p_44.fst)
                    (Expr.let_ {
                        sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var hdr, Arg.imm 472, ()) } fun p_46 =>
                      Expr.load i64 (Arg.var p_46.fst) fun ld_8 =>
                      Expr.let_ {
                          sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var ld_8, Arg.imm 3, ()) } fun p_47 =>
                      Expr.let_ {
                          sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var p_38.fst, Arg.imm 2, ()) } fun p_48 =>
                      Expr.let_ {
                          sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var p_48.fst, Arg.imm 4, ()) } fun p_49 =>
                      Expr.let_ {
                          sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var pArena, Arg.var p_49.fst, ()) } fun p_50 =>
                      Expr.load i32 (Arg.var p_50.fst) fun ld =>
                      Expr.let_ {
                          sig := [i32], code := OpCode.zext 32 64,
                          args := (Arg.var ld, ()) } fun p_51 =>
                      Expr.let_ {
                          sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var p_47.fst, Arg.var p_51.fst, ()) } fun p_52 =>
                      Expr.let_ {
                          sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var hdr, Arg.imm 472, ()) } fun p =>
                      Expr.store (Arg.var p_52.fst) (Arg.var p.fst) (Expr.jump Js.fst ())))
                (Expr.jump Js.fst ()))
            (Expr.jump J4 ()))
        (Expr.jump J4 ())) Blocks.nil)
    (fun Js_5 => Expr.jump Js_5.fst (Arg.imm 0, ()))

private def redSortDropExpr (hdr pArena pRedRefs : BitVec 64) (J4 : Cont []) (rc : BitVec 64) :
    Expr Val Cont [i64] :=
  Expr.let_ {
      sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64,
      args := (Arg.var rc, Arg.imm 0, ()) } fun p_22 =>
  Expr.jnz (Arg.var p_22.fst)
    (Expr.call (as := [i64, i64]) (bs := []) "full_sort_reds"
      (Arg.var hdr, Arg.var rc, ()) fun _ =>
    Expr.group
      (fun _Js_3 => Blocks.cons (fun (p_24 : Tup Val [i64]) =>
          Expr.call (as := [i64]) (bs := [i64]) "f64u_log10_u64"
            (Arg.var p_24.fst, ()) fun p_25 =>
          Expr.group
            (fun _Js_4 => Blocks.cons (fun (p_26 : Tup Val [i64]) =>
                Expr.call (as := [i64, i64]) (bs := [i64]) "f64u_div"
                  (Arg.imm 4630826316843712512, Arg.var p_26.fst, ()) fun p_27 =>
                Expr.call (as := [i64, i64]) (bs := [i64]) "f64u_sub"
                  (Arg.imm 4636033603912859648, Arg.var p_27.fst, ()) fun p_28 =>
                Expr.call (as := [i64, i64]) (bs := [i64]) "f64u_div"
                  (Arg.var p_28.fst, Arg.imm 4636737291354636288, ()) fun p_29 =>
                Expr.call (as := [i64]) (bs := [i64]) "f64u_from_u64"
                  (Arg.var rc, ()) fun p_30 =>
                Expr.call (as := [i64, i64]) (bs := [i64]) "f64u_mul"
                  (Arg.var p_30.fst, Arg.var p_29.fst, ()) fun p_31 =>
                Expr.call (as := [i64]) (bs := [i64]) "f64u_to_u64"
                  (Arg.var p_31.fst, ()) fun p_32 =>
                redMarkGarbExpr hdr pArena pRedRefs rc p_32.fst J4) Blocks.nil)
            fun Js_4 =>
            Expr.let_ {
                sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
                args := (Arg.var p_25.fst, Arg.imm 4607182418800017408, ()) } fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.jump Js_4.fst (Arg.imm 4607182418800017408, ()))
              (Expr.jump Js_4.fst (Arg.var p_25.fst, ()))) Blocks.nil)
      fun Js_3 =>
      Expr.let_ {
          sig := [i64, i64], code := OpCode.add i64,
          args := (Arg.var hdr, Arg.imm 688, ()) } fun p_24 =>
      Expr.load i64 (Arg.var p_24.fst) fun ld =>
      Expr.let_ {
          sig := [i64], code := OpCode.not i64,
          args := (Arg.imm 0, ()) } fun p_25 =>
      Expr.let_ {
          sig := [i64, i64], code := OpCode.sub i64,
          args := (Arg.var p_25.fst, Arg.imm 9, ()) } fun p_26 =>
      Expr.let_ {
          sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64,
          args := (Arg.var ld, Arg.var p_26.fst, ()) } fun p_27 =>
      Expr.jnz (Arg.var p_27.fst)
        (Expr.let_ {
            sig := [i64], code := OpCode.not i64,
            args := (Arg.imm 0, ()) } fun p =>
          Expr.jump Js_3.fst (Arg.var p.fst, ()))
        (Expr.let_ {
            sig := [i64, i64], code := OpCode.add i64,
            args := (Arg.var hdr, Arg.imm 688, ()) } fun p =>
          Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.let_ {
              sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var ld, Arg.imm 9, ()) } fun p =>
          Expr.jump Js_3.fst (Arg.var p.fst, ())))
    (Expr.jump J4 ())

private def redCompactExpr (hdr : BitVec 64) (Js_exit : Cont [i64, Ty.bool]) (do_compact : Bool)
    (r_u : BitVec 64) : Expr Val Cont [i64] :=
  Expr.group (fun _Js_5 => Blocks.cons (fun (p : Tup Val [i64]) =>
      Expr.jump Js_exit (Arg.var p.fst, Arg.imm do_compact, ())) Blocks.nil)
    fun Js =>
    Expr.let_ {
        sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
        args := (Arg.var r_u, Arg.imm 1, ()) } fun p_24 =>
    Expr.jnz (Arg.var p_24.fst)
      (Expr.jnz (Arg.var do_compact)
        (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var hdr, ()) fun p =>
        Expr.group (fun _Js_5 => Blocks.cons (fun (p : Tup Val [i64]) =>
            Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_in =>
        Expr.let_ {
            sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
            args := (Arg.var p.fst, Arg.imm 20, ()) } fun p_25 =>
        Expr.jnz (Arg.var p_25.fst)
          (Expr.jump Js_in.fst (Arg.imm 20, ()))
          (Expr.group (fun _Js_5 => Blocks.cons (fun (p : Tup Val [i64]) =>
              Expr.jump Js_in.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_in2 =>
          Expr.let_ {
              sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64,
              args := (Arg.var p.fst, Arg.imm 1, ()) } fun p_26 =>
          Expr.jnz (Arg.var p_26.fst)
            (Expr.jump Js_in2.fst (Arg.imm 0, ()))
            (Expr.jump Js_in2.fst (Arg.var r_u, ()))))
        (Expr.jump Js.fst (Arg.var r_u, ())))
      (Expr.jump Js.fst (Arg.var r_u, ()))

private def redSweepTailExpr (hdr : BitVec 64) (Js_ret : Cont [i64]) (force do_compact : Bool)
    (r_unfl : BitVec 64) : Expr Val Cont [i64] :=
  Expr.group
    (fun _Js_4 => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.group (fun _Js_x => Blocks.cons (fun (p : Tup Val [i64]) =>
          Expr.jump Js_ret (Arg.var p.fst, ())) Blocks.nil)
        fun Js_ex =>
        Expr.group
          (fun Js_5 => Blocks.cons (fun (_ : Tup Val []) =>
            Expr.jnz (Arg.imm true)
              (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep"
                (Arg.var hdr, ()) fun p_25 =>
                Expr.let_ {
                    sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                    args := (Arg.var p_25.fst, Arg.imm 2, ()) } fun p_26 =>
                Expr.jnz (Arg.var p_26.fst) (Expr.jump Js_ex.fst (Arg.imm 20, ()))
                  (Expr.let_ {
                      sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                      args := (Arg.var p_25.fst, Arg.imm 3, ()) } fun p_27 =>
                    Expr.jnz (Arg.var p_27.fst) (Expr.jump Js_ex.fst (Arg.imm 0, ()))
                      (Expr.let_ {
                          sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                          args := (Arg.var p_25.fst, Arg.imm 0, ()) } fun p_28 =>
                        Expr.jnz (Arg.var p_28.fst) (Expr.jump Js_ex.fst (Arg.var r_unfl, ()))
                          (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                            (Arg.var hdr, ()) fun p_29 =>
                            Expr.let_ {
                                sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                                args := (Arg.var p_29.fst, Arg.imm 1, ()) } fun p_30 =>
                            Expr.jnz (Arg.var p_30.fst) (Expr.jump Js_ex.fst (Arg.imm 20, ()))
                              (Expr.let_ {
                                  sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64,
                                  args := (Arg.var p_29.fst, Arg.imm 0, ()) } fun p_31 =>
                                Expr.jnz (Arg.var p_31.fst)
                                  (Expr.jump Js_ex.fst (Arg.imm 0, ()))
                                  (Expr.let_ {
                                      sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var hdr, Arg.imm 512, ()) } fun p_u =>
                                    Expr.store (Arg.imm (t := i64) 0) (Arg.var p_u.fst)
                                      (Expr.jump Js_5.fst ())))))))
              (Expr.jump Js_ex.fst (Arg.var r_unfl, ()))) Blocks.nil)
          (fun Js_5 => Expr.jump Js_5.fst ())) Blocks.nil)
    (fun Js_4 =>
      Expr.jnz (Arg.var force) (Expr.jump Js_4.fst ())
        (Expr.jnz (Arg.var do_compact) (Expr.jump Js_4.fst ())
          (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
              Expr.call (as := [i64, .bool]) (bs := []) "full_mark_reasons"
                (Arg.var hdr, Arg.imm false, ()) fun _ =>
                Expr.jump Js_ret (Arg.var r_unfl, ())) Blocks.nil)
            fun Js_el =>
            Expr.let_ {
                sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var hdr, Arg.imm 512, ()) } fun p_23 =>
            Expr.load i64 (Arg.var p_23.fst) fun ld =>
            Expr.let_ {
                sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                args := (Arg.var ld, Arg.imm 0, ()) } fun p_24 =>
            Expr.jnz (Arg.var p_24.fst)
              (Expr.let_ {
                  sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var hdr, Arg.imm 472, ()) } fun p_25 =>
                Expr.load i64 (Arg.var p_25.fst) fun ld =>
                Expr.let_ {
                    sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64,
                    args := (Arg.var ld, Arg.imm 0, ()) } fun p_26 =>
                Expr.jnz (Arg.var p_26.fst) (Expr.jump Js_4.fst ())
                  (Expr.let_ {
                      sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var hdr, Arg.imm 160, ()) } fun p_cl =>
                    Expr.load i64 (Arg.var p_cl.fst) fun ld =>
                    Expr.let_ {
                        sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                        args := (Arg.var ld, Arg.imm 0, ()) } fun p_cl0 =>
                    Expr.jnz (Arg.var p_cl0.fst) (Expr.jump Js_4.fst ())
                      (Expr.jump Js_el.fst ())))
              (Expr.jump Js_el.fst ()))))

private def redCollectLoopExpr (hdr pArena pRedRefs arLen64 tier1 tier2 : BitVec 64)
    (doneK : BitVec 64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun Js_2 => Blocks.cons (fun (p_20 : Tup Val [i64, i64]) =>
      Expr.let_ {
          sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
          args := (Arg.var p_20.snd.fst, Arg.var arLen64, ()) } fun p_21 =>
      Expr.jnz (Arg.var p_21.fst)
        (Expr.let_ {
            sig := [i64, i64], code := OpCode.mul i64,
            args := (Arg.var p_20.snd.fst, Arg.imm 4, ()) } fun p_22 =>
          Expr.let_ {
              sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var pArena, Arg.var p_22.fst, ()) } fun p_23 =>
          Expr.load i32 (Arg.var p_23.fst) fun ld_6 =>
          Expr.let_ {
              sig := [i64], code := OpCode.trunc 64 32,
              args := (Arg.var p_20.snd.fst, ()) } fun p_24 =>
          Expr.call (as := [i64, i32]) (bs := [i32]) "full_arena_next"
            (Arg.var hdr, Arg.var p_24.fst, ()) fun p_25 =>
          redCollectJrExpr hdr pArena pRedRefs p_20.fst p_20.snd.fst p_25.fst ld_6 tier1 tier2
            Js_2.fst)
        (doneK p_20.fst)) Blocks.nil)
    (fun Js_2 => Expr.jump Js_2.fst (Arg.imm 0, Arg.imm 0, ()))

private def redDcBodyExpr (hdr : BitVec 64) (Js_exit : Cont [i64, Ty.bool])
    (force do_compact : Bool) (r_u : BitVec 64) : Expr Val Cont [i64] :=
  Expr.call (as := [i64]) (bs := []) "m6_hdr_recompute_tiers" (Arg.var hdr, ()) fun _ =>
  Expr.call (as := [i64, Ty.bool]) (bs := []) "full_mark_reasons"
    (Arg.var hdr, Arg.imm true, ()) fun _ =>
  Expr.let_ {
      sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var hdr, Arg.imm 112, ()) } fun p_15 =>
  Expr.load i64 (Arg.var p_15.fst) fun ld =>
  Expr.let_ {
      sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var hdr, Arg.imm 424, ()) } fun p_16 =>
  Expr.load i64 (Arg.var p_16.fst) fun ld_2 =>
  Expr.let_ {
      sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var hdr, Arg.imm 48, ()) } fun p_17 =>
  Expr.load i64 (Arg.var p_17.fst) fun ld_3 =>
  Expr.let_ {
      sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var hdr, Arg.imm 696, ()) } fun p_18 =>
  Expr.load i64 (Arg.var p_18.fst) fun ld_4 =>
  Expr.let_ {
      sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var hdr, Arg.imm 704, ()) } fun p_19 =>
  Expr.load i64 (Arg.var p_19.fst) fun ld_5 =>
  redCollectLoopExpr hdr ld ld_2 ld_3 ld_4 ld_5 fun rc =>
    Expr.group
      (fun _Js_3 => Blocks.cons (fun (_ : Tup Val []) =>
          Expr.group
            (fun _Js_4 => Blocks.cons (fun (p_23 : Tup Val [i64]) =>
                redCompactExpr hdr Js_exit do_compact p_23.fst) Blocks.nil)
            fun Js_4 => redSweepTailExpr hdr Js_4.fst force do_compact r_u) Blocks.nil)
      fun Js_3 => redSortDropExpr hdr ld ld_2 Js_3.fst rc

private theorem full_reduce_next_pos_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {pos : Nat} (hst : RedSt c F0 F_cur s R ext st ml) (hpos : pos ∈ fullArenaClauseRefs st) :
    let nextOff := fullArenaNextOff st.core.arena st.core.arena_len pos
    pos < nextOff ∧ nextOff ≤ st.core.arena_len ∧ nextOff < 2 ^ 32 ∧
      (nextOff = st.core.arena_len ∨ nextOff ∈ fullArenaClauseRefs st) := by
  have hsp := hst.inv.toInv.2.2
  unfold FullSparseInv at hsp
  have hlen := hsp.1.lengths
  obtain ⟨_, hwit⟩ := hsp.1.witness
  have hwf := hwit.arena.refs_wf pos hpos
  have hmem := fullArenaClauseRefs_next_mem hwit.arena hpos
  have h_le : fullArenaNextOff st.core.arena st.core.arena_len pos ≤ st.core.arena_len :=
    hwf.2.2.2.1
  have h_lt32 : fullArenaNextOff st.core.arena st.core.arena_len pos < 2 ^ 32 := by
    have := hlen.core_ok.arena_len_le
    have := c.harena
    have : 2 * Ref.dimacsBound < 2 ^ 32 := by decide
    omega
  exact ⟨by omega, h_le, h_lt32, hmem⟩

private theorem reduce_collect_loop_wp {Γ : Env}
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : FullState}
    {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Q : Post [i64]} {X : XPost} {arLen64 tier1 tier2 : BitVec 64}
    (doneK : BitVec 64 → Expr Val Cont [i64])
    (hst : RedSt c F0 F_cur s R ext st ml) (hrm : FullReasonsMarked st)
    (harLen : arLen64.toNat = st.core.arena_len)
    (_ht1 : tier1 = st.scratch.tier1) (_ht2 : tier2 = st.scratch.tier2)
    (hDone : ∀ (rc : BitVec 64) st' ml',
      RedSt c F0 F_cur s R ext st' ml' → FullReasonsMarked st' →
      RedRefsOk st' rc.toNat → rc.toNat ≤ c.red_cap →
      st'.core.cur_level = st.core.cur_level → st'.core.oom = st.core.oom →
      st'.core.unflushed = st.core.unflushed → wp Γ Q X (doneK rc) ml') :
    wp Γ Q X (redCollectLoopExpr c.hdr c.pArena c.pRedRefs arLen64 tier1 tier2 doneK) ml := by
  unfold redCollectLoopExpr redCollectJrExpr
  let St := BitVec 64 × BitVec 64 × FullState
  refine wp_while_state (ts := [i64, i64]) (α := St)
    (fun x => (x.1, x.2.1, ()))
    (fun x => st.core.arena_len - x.2.1.toNat)
    (fun x m =>
      RedSt c F0 F_cur s R ext x.2.2 m ∧ FullReasonsMarked x.2.2 ∧
      RedRefsOk x.2.2 x.1.toNat ∧ x.1.toNat ≤ c.red_cap ∧
      (x.2.1.toNat ∈ fullArenaClauseRefs x.2.2 ∨ x.2.1.toNat = x.2.2.core.arena_len) ∧
      x.2.2.core.arena_len = st.core.arena_len ∧ x.2.2.core.cur_level = st.core.cur_level ∧
      x.2.2.core.oom = st.core.oom ∧ x.2.2.core.unflushed = st.core.unflushed ∧
      x.2.2.scratch.tier1 = st.scratch.tier1 ∧ x.2.2.scratch.tier2 = st.scratch.tier2)
    (fun J hJ => by
      c0_hsteps_ng
      have h0_mem : (0#64 : BitVec 64).toNat ∈ fullArenaClauseRefs st ∨
          (0#64 : BitVec 64).toNat = st.core.arena_len := by
        rw [show (0#64 : BitVec 64).toNat = 0 from rfl]
        rcases Nat.eq_zero_or_pos st.core.arena_len with h0 | hpos
        · exact Or.inr h0.symm
        · have hsp := hst.inv.toInv.2.2
          unfold FullSparseInv at hsp
          obtain ⟨_, hwit⟩ := hsp.1.witness
          exact Or.inl (fullArenaClauseRefs_zero_mem hwit.arena hpos)
      have hrr0 : RedRefsOk st (0#64 : BitVec 64).toNat := fun j hj => by
        rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at hj; omega
      exact hJ (0#64, 0#64, st) ml ⟨hst, hrm, hrr0, Nat.zero_le _, h0_mem,
        rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (fun J (rc, pos, stI) mI ⟨hstI, hrmI, hrrI, hrcI, hpI, halI, hclI, hoomI, hufI, ht1I, ht2I⟩
        hL => by
      have hspI := hstI.inv.toInv.2.2
      unfold FullSparseInv at hspI
      have hlenI := hspI.1.lengths
      c0_hsteps_ng
      · dsimp only at *
        have hp_lt_arlen : pos.toNat < stI.core.arena_len := by
          have : pos.toNat < arLen64.toNat := by assumption
          omega
        have hp_mem : pos.toNat ∈ fullArenaClauseRefs stI := by
          rcases hpI with hmem | heq
          · exact hmem
          · omega
        have hp_ar : pos.toNat < stI.core.arena.length := red_pos_lt_arena hstI hp_mem
        have hp_lt32 : pos.toNat < 2 ^ 32 := by
          have := hlenI.core_ok.arena_len_le; have := c.harena
          have : 2 * Ref.dimacsBound < 2 ^ 32 := by decide
          omega
        have hp_64 : 4 * pos.toNat < 2 ^ 64 := by
          have := c.havail_fit; have := c.hsize; have := hlenI.core_ok.arena_len_arr; omega
        obtain ⟨hp_lt_nxt, hnxt_le, hnxt_lt32, hnxt_mem⟩ := full_reduce_next_pos_ok hstI hp_mem
        refine wp_m6Hdr_focus_frame hstI.mem fun hmF => ?_
        c0_hsteps_ng
        refine wp_call_of_spec _ _ (hNext _ _ _ X ?_)
        refine ⟨c, stI, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlenI, hmF, ?_⟩
        dsimp only [Arg.val]
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hp_lt32]
        let next32 : BitVec 32 :=
          BitVec.ofNat 32 (fullArenaNextOff stI.core.arena stI.core.arena_len pos.toNat)
        have hnxt32_eq : (BitVec.zeroExtend 64 next32).toNat =
            fullArenaNextOff stI.core.arena stI.core.arena_len pos.toNat := by
          rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
          dsimp [next32]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnxt_lt32, Nat.mod_eq_of_lt (by omega)]
        have hnxt_mem64 : (BitVec.zeroExtend 64 next32).toNat ∈ fullArenaClauseRefs stI ∨
            (BitVec.zeroExtend 64 next32).toNat = stI.core.arena_len := by
          rw [hnxt32_eq]; exact hnxt_mem.symm
        refine reduce_collect_jr_wp (Js_lp := J) hstI hrmI hrrI hrcI hp_mem (fun rc' st' ml'
            hst' hrm' hrr' hrc' hnx' hal' hcl' hoom' huf' ht1' ht2' => by
          refine hL (rc', BitVec.zeroExtend 64 next32, st') ml' ?_
            ⟨hst', hrm', hrr', hrc', hnx', hal'.trans halI, hcl'.trans hclI, hoom'.trans hoomI,
              huf'.trans hufI, ht1'.trans ht1I, ht2'.trans ht2I⟩
          dsimp only; rw [hnxt32_eq]; omega)
          hnxt_mem64
      · exact hDone rc stI mI hstI hrmI hrrI hrcI hclI hoomI hufI)

private theorem reduce_sort_and_drop_wp {Γ : Env}
    (hSort : Γ.Has "full_sort_reds" Spec.fullSortRedsSpec)
    (hLog10 : Γ.Has "f64u_log10_u64" Float64.Spec.f64uPure1Spec)
    (hDiv : Γ.Has "f64u_div" Float64.Spec.f64uPure2Spec)
    (hSub : Γ.Has "f64u_sub" Float64.Spec.f64uPure2Spec)
    (hFromU : Γ.Has "f64u_from_u64" Float64.Spec.f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec)
    (hToU : Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : FullState}
    {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {J4 : Cont []} {Q : Post [i64]} {X : XPost} {rc : BitVec 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (hrm : FullReasonsMarked st)
    (hrr : RedRefsOk st rc.toNat) (hrc_cap : rc.toNat ≤ c.red_cap)
    (hJ4 : ∀ st' ml', RedSt c F0 F_cur s R ext st' ml' → FullReasonsMarked st' →
      st'.core.cur_level = st.core.cur_level → st'.core.oom = st.core.oom →
      st'.core.unflushed = st.core.unflushed → J4 () ml') :
    wp Γ Q X (redSortDropExpr c.hdr c.pArena c.pRedRefs J4 rc) ml := by
  unfold redSortDropExpr redMarkGarbExpr
  have hsp := hst.inv.toInv.2.2
  unfold FullSparseInv at hsp
  have hlen := hsp.1.lengths
  obtain ⟨_, hwit⟩ := hsp.1.witness
  c0_hsteps_ng
  · have h_in_cap : ∀ k < rc.toNat,
        (st.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap := by
      intro k hk
      obtain ⟨hmem, _⟩ := hrr k hk
      have hwf := hwit.arena.refs_wf _ hmem
      have hale := hlen.core_ok.arena_len_le
      omega
    refine wp_m6Hdr_focus_frame hst.mem fun hmF => ?_
    refine wp_call_of_spec _ _ (hSort _ _ _ X ?_)
    refine ⟨c, st, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hrc_cap, h_in_cap, hmF,
      fun rr' sb' m' hrr_len hsb_len hrr_perm hm' => ?_⟩
    let sc' : FullScratch := { st.scratch with red_refs := rr', scratch_buf := sb' }
    let st' : FullState := { core := st.core, scratch := sc' }
    have hsc_ok : FullScratch.LengthsOk c sc' := by
      have hso := hlen.scratch_ok
      exact { hso with red_refs_len := hrr_len, scratch_buf_len := hsb_len }
    have hst' : RedSt c F0 F_cur s R ext st' m' :=
      redSt_with_scratch hst hsc_ok rfl rfl rfl rfl (fullM6HdrMem_unfocus_full hm')
    have hrm' : FullReasonsMarked st' := hrm
    have hrr' : RedRefsOk st' rc.toNat := by
      intro j hj
      obtain ⟨k, hk, hjk⟩ := hrr_perm j hj
      have hreq : (sc'.red_refs[j]?.getD 0#32).toNat =
          (st.scratch.red_refs[k]?.getD 0#32).toNat := by
        dsimp [sc']; rw [hjk]
      change (sc'.red_refs[j]?.getD 0#32).toNat ∈ fullArenaClauseRefs st' ∧
        fullArenaHdr st' (sc'.red_refs[j]?.getD 0#32).toNat &&& 2097152#32 = 0#32
      rw [hreq]
      exact hrr k hk
    refine wp_join_group (fun (_ : Tup Val [i64]) ma =>
        RedSt c F0 F_cur s R ext st' ma)
      (fun _ (p_24 : Tup Val [i64]) ma hstA => by
        refine wp_call_of_spec _ _ (hLog10 _ _ _ X fun r_lg => ?_)
        refine wp_join_group (fun (_ : Tup Val [i64]) mb =>
            RedSt c F0 F_cur s R ext st' mb)
          (fun _ (p_26 : Tup Val [i64]) mb hstB => by
            refine wp_call_of_spec _ _ (hDiv _ _ _ X fun r_d1 => ?_)
            refine wp_call_of_spec _ _ (hSub _ _ _ X fun r_sb => ?_)
            refine wp_call_of_spec _ _ (hDiv _ _ _ X fun r_d2 => ?_)
            refine wp_call_of_spec _ _ (hFromU _ _ _ X fun r_fr => ?_)
            refine wp_call_of_spec _ _ (hMul _ _ _ X fun r_ml => ?_)
            refine wp_call_of_spec _ _ (hToU _ _ _ X fun target => ?_)
            exact reduce_mark_garb_loop_wp hstB hrm' hrr' hrc_cap
              (fun st'' ml'' hst'' hrm'' hcl'' hoom'' huf'' => by
                c0_hsteps_ng
                exact hJ4 st'' ml'' hst'' hrm'' hcl'' hoom'' huf''))
          (fun _ hJ4_in => by
            c0_hsteps_ng <;> exact hJ4_in _ _ hstA))
      (fun _ hJ3 => by
        refine wp_m6Hdr_focus_frame hst'.mem fun _hmF' => ?_
        c0_hsteps_ng
        · exact hJ3 (_, ()) m' hst'
        · exact hJ3 (_, ()) m' hst')
  · exact hJ4 st ml hst hrm rfl rfl rfl

private theorem reduce_compact_wp {Γ : Env}
    (hCmp : Γ.Has "full_compact" Compact.Spec.fullCompactSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : FullState}
    {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js_exit : Cont [i64, Ty.bool]} {Q : Post [i64]} {X : XPost}
    {force do_compact : Bool} {r_u : BitVec 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (h_nf : do_compact = true → force = false)
    (hr_u : r_u = 0#64 ∨ r_u = 1#64 ∨ r_u = 20#64) (huns_u : r_u = 20#64 → F0.Unsat)
    (hoom_u : r_u = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64)
    (hExit : ∀ r c' ext' s' ml',
      RedEndSt c F0 F_cur s R force r c' ext' s' ml' → Js_exit (r, do_compact, ()) ml') :
    wp Γ Q X (redCompactExpr c.hdr Js_exit do_compact r_u) ml := by
  unfold redCompactExpr
  have hEnd_u : RedEndSt c F0 F_cur s R force r_u c ext st ml :=
    redEndSt_of_redSt hst hr_u huns_u hoom_u
  have h20_ne1 : (20#64 : BitVec 64) ≠ 1#64 := by decide
  have h0_ne20 : (0#64 : BitVec 64) ≠ 20#64 := by decide
  have h0_ne1 : (0#64 : BitVec 64) ≠ 1#64 := by decide
  refine wp_join_group (fun (p : Tup Val [i64]) ma =>
      ∃ c' ext' s', RedEndSt c F0 F_cur s R force p.fst c' ext' s' ma)
    (fun _ (p : Tup Val [i64]) ma ⟨c', ext', s', hEnd⟩ => by
      c0_hsteps_ng; exact hExit p.fst c' ext' s' ma hEnd)
    (fun _ hJs => by
      c0_hsteps_ng
      · have hr_eq1 : r_u = 1#64 := by assumption
        have hdc : do_compact = true := by assumption
        have hforce : force = false := h_nf hdc
        refine wp_call_of_spec _ _ (hCmp _ _ _ X ?_)
        refine ⟨c, F0, ext, st, R, rfl, hst.inv.toInv, hst.mem,
          fun r_c c' ext' s' m' hcompat hinv' hr_c hcv' hfu' huns' hcl' hm' => ?_⟩
        have hcv_s : s'.core.cur_vars ≤ s.core.cur_vars := hst.cv ▸ hcv'
        have hfu_s : s'.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu' hst.fu
        have hnf_vac : ∀ (r0 : BitVec 64), force = true →
            c' = c ∧ RedSt c F0 F_cur s R ext' s' m' ∧
              (r0 = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) :=
          fun _ hf => False.elim (by cases (hf ▸ hforce))
        refine wp_join_group (fun (p : Tup Val [i64]) ma =>
            ∃ c0 ext0 s0, RedEndSt c F0 F_cur s R force p.fst c0 ext0 s0 ma)
          (fun _ (p : Tup Val [i64]) ma ⟨c0, ext0, s0, hEnd⟩ => by
            c0_hsteps_ng; exact hJs p ma ⟨c0, ext0, s0, hEnd⟩)
          (fun _ hJin => by
            c0_hsteps_ng
            · exact hJin (20#64, ()) m' ⟨c', ext', s',
                ⟨hcompat, hinv', Or.inr (Or.inr rfl), hcv_s, hfu_s,
                  fun _ => huns' (by assumption), fun h => absurd h h20_ne1,
                  hnf_vac 20#64, hm'⟩⟩
            · refine wp_join_group (fun (p : Tup Val [i64]) ma =>
                  ∃ c0 ext0 s0, RedEndSt c F0 F_cur s R force p.fst c0 ext0 s0 ma)
                (fun _ (p : Tup Val [i64]) ma ⟨c0, ext0, s0, hEnd⟩ => by
                  c0_hsteps_ng; exact hJin p ma ⟨c0, ext0, s0, hEnd⟩)
                (fun _ hJin2 => by
                  c0_hsteps_ng
                  · exact hJin2 (0#64, ()) m' ⟨c', ext', s',
                      ⟨hcompat, hinv', Or.inl rfl, hcv_s, hfu_s,
                        fun h => absurd h h0_ne20, fun h => absurd h h0_ne1,
                        hnf_vac 0#64, hm'⟩⟩
                  · have hrc1 : r_c = 1#64 := by assumption
                    have hcl0 : s'.core.cur_level ≤ s.core.cur_level := by
                      have := hcl' hrc1; omega
                    exact hJin2 (r_u, ()) m' ⟨c', ext', s',
                      ⟨hcompat, hinv', hr_u, hcv_s, hfu_s, huns_u,
                        fun _ => hcl0, hnf_vac r_u, hm'⟩⟩))
      · exact hJs (r_u, ()) ml ⟨c, ext, st, hEnd_u⟩
      · exact hJs (r_u, ()) ml ⟨c, ext, st, hEnd_u⟩)

private theorem reduce_dc_body_wp {Γ : Env}
    (hRec : Γ.Has "m6_hdr_recompute_tiers" (m6HdrW2aSpec [] []))
    (hMark : Γ.Has "full_mark_reasons" fullMarkReasonsSpec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hSort : Γ.Has "full_sort_reds" Spec.fullSortRedsSpec)
    (hLog10 : Γ.Has "f64u_log10_u64" Float64.Spec.f64uPure1Spec)
    (hDiv : Γ.Has "f64u_div" Float64.Spec.f64uPure2Spec)
    (hSub : Γ.Has "f64u_sub" Float64.Spec.f64uPure2Spec)
    (hFromU : Γ.Has "f64u_from_u64" Float64.Spec.f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec)
    (hToU : Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec)
    (hSweep : Γ.Has "full_arena_sweep" Collect.Spec.step13ArenaSweepSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hCmp : Γ.Has "full_compact" Compact.Spec.fullCompactSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : FullState}
    {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js_exit : Cont [i64, Ty.bool]} {Q : Post [i64]} {X : XPost}
    {force do_compact : Bool} {r_u : BitVec 64}
    (hr_u : r_u = 1#64) (hst : RedSt c F0 F_cur s R ext st ml)
    (hoom_st : s.core.oom = 0#64 → st.core.oom = 0#64)
    (h_nf : do_compact = true → force = false)
    (hExit : ∀ r c' ext' s' ml',
      RedEndSt c F0 F_cur s R force r c' ext' s' ml' → Js_exit (r, do_compact, ()) ml') :
    wp Γ Q X (redDcBodyExpr c.hdr Js_exit force do_compact r_u) ml := by
  unfold redDcBodyExpr
  have hsp := hst.inv.toInv.2.2
  unfold FullSparseInv at hsp
  have hlen := hsp.1.lengths
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ hS => hRec _ _ _ _ hS)
    hst.inv.toInv.1 hst.inv.toInv.2.1 hlen hst.mem
    (fun _ ext1 s1 m1 hcore1 hlen1 hsp1 hext1 _ hm1 => ?_)
  have hst1 := redSt_w2a hst hcore1 hlen1 hsp1 hext1 hm1
  refine red_call_mark_reasons rfl hMark hst1 fun s2 m2 hst2 hrm2 hoom2 => ?_
  have hrm2' : FullReasonsMarked s2 := hrm2 rfl
  have hsp2 := hst2.inv.toInv.2.2
  unfold FullSparseInv at hsp2
  have hlen2 := hsp2.1.lengths
  have hal64 : (BitVec.ofNat 64 s2.core.arena_len).toNat = s2.core.arena_len := by
    have := hlen2.core_ok.arena_len_le
    have := c.harena
    have : 2 * Ref.dimacsBound < 2 ^ 64 := by decide
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine wp_m6Hdr_focus_frame hst2.mem fun _hmF2 => ?_
  c0_hsteps_ng
  refine reduce_collect_loop_wp hNext _ hst2 hrm2' hal64 rfl rfl
    (fun rc st3 ml3 hst3 hrm3 hrr3 hrc3 hcl3 hoom3 _huf3 => ?_)
  refine wp_join_group (fun (_ : Tup Val []) ma =>
      ∃ st4 : FullState, RedSt c F0 F_cur s R ext1 st4 ma ∧ FullReasonsMarked st4 ∧
        st4.core.cur_level = st3.core.cur_level ∧ st4.core.oom = st3.core.oom ∧
        st4.core.unflushed = st3.core.unflushed)
    (fun _ _ ma ⟨st4, hst4, hrm4, hcl4, hoom4, huf4⟩ => by
      refine wp_join_group (fun (xs : Tup Val [i64]) mb =>
          ∃ ext5 st5, RedSt c F0 F_cur s R ext5 st5 mb ∧
            (xs.fst = 0#64 ∨ xs.fst = 1#64 ∨ xs.fst = 20#64) ∧
            (xs.fst = 20#64 → F0.Unsat) ∧ (xs.fst = 1#64 → s.core.oom = 0#64 → st5.core.oom = 0#64))
        (fun _ (p_23 : Tup Val [i64]) mb ⟨ext5, st5, hst5, hr5, huns5, hoom5⟩ =>
          reduce_compact_wp hCmp hst5 h_nf hr5 huns5 hoom5 hExit)
        (fun _ hJ4 => by
          unfold redSweepTailExpr
          exact reduce_sweep_tail_wp hSweep hProp hMark hr_u hst4 (fun _ => hrm4)
            (fun hs => hoom4.trans (hoom3.trans (hoom2.trans (hcore1 ▸ hoom_st hs))))
            (fun r ext5 st5 ml5 hst5 hr5 huns5 hoom5 =>
              hJ4 (r, ()) ml5 ⟨ext5, st5, hst5, hr5, huns5, hoom5⟩)))
    (fun _ hJ3 =>
      reduce_sort_and_drop_wp hSort hLog10 hDiv hSub hFromU hMul hToU hst3 hrm3 hrr3 hrc3
        (fun st4 ml4 hst4 hrm4 hcl4 hoom4 huf4 =>
          hJ3 () ml4 ⟨st4, hst4, hrm4, hcl4, hoom4, huf4⟩))

private theorem reduce_core_wp {Γ : Env}
    (hCmpNeed : Γ.Has "full_compact_needed" Compact.Spec.fullCompactNeededSpec)
    (hRec : Γ.Has "m6_hdr_recompute_tiers" (m6HdrW2aSpec [] []))
    (hMark : Γ.Has "full_mark_reasons" fullMarkReasonsSpec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hSort : Γ.Has "full_sort_reds" Spec.fullSortRedsSpec)
    (hLog10 : Γ.Has "f64u_log10_u64" Float64.Spec.f64uPure1Spec)
    (hDiv : Γ.Has "f64u_div" Float64.Spec.f64uPure2Spec)
    (hSub : Γ.Has "f64u_sub" Float64.Spec.f64uPure2Spec)
    (hFromU : Γ.Has "f64u_from_u64" Float64.Spec.f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec)
    (hToU : Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec)
    (hSweep : Γ.Has "full_arena_sweep" Collect.Spec.step13ArenaSweepSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hCmp : Γ.Has "full_compact" Compact.Spec.fullCompactSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : FullState}
    {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js_exit : Cont [i64, Ty.bool]} {Q : Post [i64]} {X : XPost}
    {force : Bool} {r_u : BitVec 64}
    (hr_u : r_u = 1#64) (hst : RedSt c F0 F_cur s R ext st ml)
    (hoom_st : s.core.oom = 0#64 → st.core.oom = 0#64)
    (hExit : ∀ r dc c' ext' s' ml',
      RedEndSt c F0 F_cur s R force r c' ext' s' ml' → Js_exit (r, dc, ()) ml') :
    wp Γ Q X
      (Expr.group
        (fun _Js_1 => Blocks.cons (fun (p_12 : Tup Val [Ty.bool]) =>
            redDcBodyExpr c.hdr Js_exit force p_12.fst r_u) Blocks.nil)
        fun Js =>
        Expr.jnz (Arg.var force)
          (Expr.jump Js.fst (Arg.imm false, ()))
          (Expr.let_ {
              sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm 160, ()) } fun p_12 =>
          Expr.load i64 (Arg.var p_12.fst) fun ld =>
          Expr.let_ {
              sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
              args := (Arg.var ld, Arg.imm 0, ()) } fun p_13 =>
          Expr.jnz (Arg.var p_13.fst)
            (Expr.call (as := [i64]) (bs := [Ty.bool]) "full_compact_needed" (Arg.var c.hdr, ())
              fun p =>
              Expr.jnz (Arg.var p.fst)
                (Expr.jump Js.fst (Arg.imm true, ()))
                (Expr.jump Js.fst (Arg.imm false, ())))
            (Expr.jump Js.fst (Arg.imm false, ())))) ml := by
  have hsp := hst.inv.toInv.2.2
  unfold FullSparseInv at hsp
  have hlen := hsp.1.lengths
  obtain ⟨_, hwit⟩ := hsp.1.witness
  have hcl_lt : st.core.cur_level < 2 ^ 64 := by
    have := hwit.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; have := c.hmaxv
    have : 2 * Ref.dimacsBound < 2 ^ 32 := by decide
    omega
  refine wp_join_group (fun (p_12 : Tup Val [Ty.bool]) ma =>
      RedSt c F0 F_cur s R ext st ma ∧ (p_12.fst = true → force = false))
    (fun _ (p_12 : Tup Val [Ty.bool]) ma ⟨hstA, hnfA⟩ =>
      reduce_dc_body_wp hRec hMark hNext hSort hLog10 hDiv hSub hFromU hMul hToU hSweep hProp hCmp
        hr_u hstA hoom_st hnfA (fun r c' ext' s' ml' hEnd => hExit r p_12.fst c' ext' s' ml' hEnd))
    (fun _ hJs => by
      c0_hsteps_ng
      · exact hJs (false, ()) ml ⟨hst, fun h => by cases h⟩
      · have hfnf : force = false := by assumption
        refine wp_m6Hdr_focus_frame hst.mem fun hmF => ?_
        c0_hsteps_ng
        · refine wp_call_of_spec _ _ (hCmpNeed _ _ _ X ?_)
          refine ⟨c, st, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hcl_lt, hmF,
            fun res _ => ?_⟩
          c0_hsteps_ng
          · exact hJs (true, ()) ml ⟨hst, fun _ => hfnf⟩
          · exact hJs (false, ()) ml ⟨hst, fun h => by cases h⟩
        · exact hJs (false, ()) ml ⟨hst, fun h => by cases h⟩)

/-- `full_reduce_m6` satisfies `Spec.fullReduceM6Spec`. -/
public theorem full_reduce_m6_wp (Γ : Env)
    (hIsqrt : Γ.Has "full_isqrt" fullIsqrtSpec)
    (hBtk : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hCmpNeed : Γ.Has "full_compact_needed" Compact.Spec.fullCompactNeededSpec)
    (hRec : Γ.Has "m6_hdr_recompute_tiers" (m6HdrW2aSpec [] []))
    (hMark : Γ.Has "full_mark_reasons" fullMarkReasonsSpec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hSort : Γ.Has "full_sort_reds" Spec.fullSortRedsSpec)
    (hLog10 : Γ.Has "f64u_log10_u64" Float64.Spec.f64uPure1Spec)
    (hDiv : Γ.Has "f64u_div" Float64.Spec.f64uPure2Spec)
    (hSub : Γ.Has "f64u_sub" Float64.Spec.f64uPure2Spec)
    (hFromU : Γ.Has "f64u_from_u64" Float64.Spec.f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec)
    (hToU : Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec)
    (hSweep : Γ.Has "full_arena_sweep" Collect.Spec.step13ArenaSweepSpec)
    (hCmp : Γ.Has "full_compact" Compact.Spec.fullCompactSpec)
    (hWm : Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hFid : Γ.Has "full_update_classify_fid" (m6HdrW2aSpec [] [])) :
    ∀ a m Q X, Spec.fullReduceM6Spec a m Q X → Func.wp Γ full_reduce_m6_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext0, s, R, rfl, hinv0, hm0, hQ⟩
  unfold Func.wp full_reduce_m6_body
  dsimp only
  have hst0 := redSt_refl hinv0 hm0
  have hsp0 := hinv0.toInv.2.2
  unfold FullSparseInv at hsp0
  have hlen0 := hsp0.1.lengths
  refine wp_m6Hdr_focus_frame hst0.mem fun _hmF0 => ?_
  c0_hsteps_ng
  refine wp_call_of_spec _ _ (hIsqrt _ _ _ X fun r_isq _ _ _ => ?_)
  c0_hsteps_ng
  have hm2 := fullM6HdrMem_unfocus_full (by assumption)
  let sc2 : FullScratch :=
    { s.scratch with
      reductions := s.scratch.reductions + 1#64,
      reduce_limit := s.scratch.conflicts + r_isq }
  let s2 : FullState := { core := s.core, scratch := sc2 }
  have hsc2 : FullScratch.LengthsOk c sc2 :=
    { hlen0.scratch_ok with walk_vals_len := hlen0.scratch_ok.walk_vals_len }
  have hst2 : RedSt c F0 F_cur s R ext0 s2 _ :=
    redSt_with_scratch hst0 hsc2 rfl rfl rfl rfl hm2
  refine wp_join_group (fun (p_10 : Tup Val [i64]) ma =>
      ∃ ext1 s1, RedSt c F0 F_cur s R ext1 s1 ma ∧
        (p_10.fst = 0#64 ∨ p_10.fst = 1#64 ∨ p_10.fst = 20#64) ∧
        (p_10.fst = 20#64 → F0.Unsat) ∧ (p_10.fst = 1#64 → s1.core.unflushed = 0#64) ∧
        (p_10.fst = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64))
    (fun _ (p_10 : Tup Val [i64]) ma ⟨ext1, s1, hst1, hr1, huns1, _huf1, hoom1⟩ => by
      refine wp_join_group (fun (p_11 : Tup Val [i64, Ty.bool]) mb =>
          ∃ c' ext' s', RedEndSt c F0 F_cur s R force p_11.fst c' ext' s' mb)
        (fun _ (p_11 : Tup Val [i64, Ty.bool]) mb ⟨c', ext', s', hEnd⟩ =>
          reduce_ret_wm_wp hWm hFid hEnd hQ)
        (fun _ hExit => by
          c0_hsteps_ng
          · exact reduce_core_wp hCmpNeed hRec hMark hNext hSort hLog10 hDiv hSub hFromU hMul
              hToU hSweep hProp hCmp (by assumption) hst1 (hoom1 (by assumption))
              (fun r dc c' ext' s' ml' hEnd => hExit (r, dc, ()) ml' ⟨c', ext', s', hEnd⟩)
          · exact hExit (p_10.fst, false, ()) ma
              ⟨c, ext1, s1, redEndSt_of_redSt hst1 hr1 huns1 (fun h => absurd h (by assumption))⟩))
    (fun _ hJoin =>
      reduce_unflushed_wp hBtk hProp hst2 rfl (fun r ext1 s1 ml1 hst1 hr1 huns1 huf1 hoom1 =>
        hJoin (r, ()) ml1 ⟨ext1, s1, hst1, hr1, huns1, huf1, hoom1⟩))

end LeanQbe.T.Examples.Kissat.Proof.Reduce
