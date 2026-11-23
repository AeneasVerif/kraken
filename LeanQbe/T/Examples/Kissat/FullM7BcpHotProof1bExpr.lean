/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1a

/-!
# Kissat M7 Hot-Path Fused BCP Proofs — Part 1b AST Builders

Zero `import all`, plain `public section` (`@[expose]`
ONLY on non-recursive concrete AST `Expr` defs).
Defines `m7LpLoopExpr` and sub-expression AST builders used by `FullM7BcpHotProof1b`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "m7_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "m7_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "m7_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

@[expose] def m7LpAssignTailExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (lvl rsns trl tpos flags phases : V i64) (rec_ph : V Ty.bool)
    (not_lit : V i32) (te un uf tk_next p_next q_next : V i64)
    (v_idx : V i64) (new_lit alvl : V i32) (rsn_cref : Option (V i32))
    (J_lp : L [i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.group (sig := [[i64]])
    (fun J_un => Blocks.cons
      (fun unp => Expr.group (sig := [[]])
        (fun J_ph => Blocks.cons
          (fun _ =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o1 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var lvl, Arg.var o1.fst, ())⟩ fun a1 =>
            Expr.store (Arg.var alvl) (Arg.var a1.fst)
              (Expr.group (sig := [[i64]])
                (fun J_uf => Blocks.cons
                  (fun ufp =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o2 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var tpos, Arg.var o2.fst, ())⟩ fun a2 =>
                    Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var te, ())⟩ fun te32 =>
                    Expr.store (Arg.var te32.fst) (Arg.var a2.fst)
                      (Expr.let_ ⟨OpCode.mul i64, (Arg.var te, Arg.imm 4, ())⟩ fun o3 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var trl, Arg.var o3.fst, ())⟩ fun a3 =>
                      Expr.store (Arg.var new_lit) (Arg.var a3.fst)
                        (Expr.let_ ⟨OpCode.add i64, (Arg.var te, Arg.imm 1, ())⟩ fun te1 =>
                        Expr.jump J_lp (Arg.var te1.fst, Arg.var unp.fst, Arg.var ufp.fst,
                          Arg.var tk_next, Arg.var p_next, Arg.var q_next, ()))))
                  Blocks.nil)
                (fun J_uf =>
                  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32, (Arg.var alvl, Arg.imm 0, ())⟩ fun z =>
                  Expr.jnz (Arg.var z.fst)
                    (Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o4 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var rsns, Arg.var o4.fst, ())⟩ fun a4 =>
                    Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var a4.fst)
                      (Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o5 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var flags, Arg.var o5.fst, ())⟩ fun a5 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o6 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var flags, Arg.var o6.fst, ())⟩ fun a6 =>
                      Expr.load i32 (Arg.var a6.fst) fun fl =>
                      Expr.let_ ⟨OpCode.not i32, (Arg.imm 1, ())⟩ fun nm =>
                      Expr.let_ ⟨OpCode.and i32, (Arg.var fl, Arg.var nm.fst, ())⟩ fun fl' =>
                      Expr.store (Arg.var fl'.fst) (Arg.var a5.fst)
                        (Expr.let_ ⟨OpCode.add i64, (Arg.var uf, Arg.imm 1, ())⟩ fun uf1 =>
                        Expr.jump J_uf.fst (Arg.var uf1.fst, ()))))
                    (Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o4 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var rsns, Arg.var o4.fst, ())⟩ fun a4 =>
                    match rsn_cref with
                    | none =>
                      Expr.let_ ⟨OpCode.or i32, (Arg.imm 2147483648, Arg.var not_lit, ())⟩ fun rb =>
                      Expr.store (Arg.var rb.fst) (Arg.var a4.fst)
                        (Expr.jump J_uf.fst (Arg.var uf, ()))
                    | some cref =>
                      Expr.store (Arg.var cref) (Arg.var a4.fst)
                        (Expr.jump J_uf.fst (Arg.var uf, ()))))))
          Blocks.nil)
        (fun J_ph =>
          Expr.jnz (Arg.var rec_ph)
            (Expr.group (sig := [[]])
              (fun J_p2 => Blocks.cons (fun _ => Expr.jump J_ph.fst ()) Blocks.nil)
              (fun J_p2 =>
                Expr.let_ ⟨OpCode.and i32, (Arg.var new_lit, Arg.imm 1, ())⟩ fun b1 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var b1.fst, Arg.imm 0, ())⟩ fun c1 =>
                Expr.jnz (Arg.var c1.fst)
                  (Expr.let_ ⟨OpCode.add i64, (Arg.var phases, Arg.var v_idx, ())⟩ fun pa =>
                  Expr.let_ ⟨OpCode.neg i32, (Arg.imm 1, ())⟩ fun m1 =>
                  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.var m1.fst, ())⟩ fun b =>
                  Expr.store (Arg.var b.fst) (Arg.var pa.fst) (Expr.jump J_p2.fst ()))
                  (Expr.let_ ⟨OpCode.add i64, (Arg.var phases, Arg.var v_idx, ())⟩ fun pa =>
                  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 1, ())⟩ fun b =>
                  Expr.store (Arg.var b.fst) (Arg.var pa.fst) (Expr.jump J_p2.fst ()))))
            (Expr.jump J_ph.fst ())))
      Blocks.nil)
    (fun J_un =>
      Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var flags, Arg.var o.fst, ())⟩ fun a =>
      Expr.load i32 (Arg.var a.fst) fun fl =>
      Expr.let_ ⟨OpCode.and i32, (Arg.var fl, Arg.imm 1, ())⟩ fun fl1 =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var fl1.fst, Arg.imm 0, ())⟩ fun c1 =>
      Expr.jnz (Arg.var c1.fst)
        (Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64, (Arg.var un, Arg.imm 0, ())⟩ fun c2 =>
        Expr.jnz (Arg.var c2.fst)
          (Expr.let_ ⟨OpCode.sub i64, (Arg.var un, Arg.imm 1, ())⟩ fun un1 =>
          Expr.jump J_un.fst (Arg.var un1.fst, ()))
          (Expr.jump J_un.fst (Arg.var un, ())))
        (Expr.jump J_un.fst (Arg.var un, ())))

@[expose] def m7LpReplScanExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (vals arena : V i64) (cbase bound_v : V i64) (init_idx : Arg V i64)
    (exit_lit : Arg V i32) (exit_found : Arg V Ty.bool)
    (J_out : L [i64, i32, Ty.bool]) : Expr V L rs :=
  Expr.group (sig := [[i64]])
    (fun J_sc => Blocks.cons
      (fun idx =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var idx.fst, Arg.var bound_v, ())⟩ fun c =>
        Expr.jnz (Arg.var c.fst)
          (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.var idx.fst, ())⟩ fun a1 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun o1 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o1.fst, ())⟩ fun p1 =>
          Expr.load i32 (Arg.var p1.fst) fun w =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w, ())⟩ fun w64 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var w64.fst, ())⟩ fun vp =>
          Expr.load i8 (Arg.var vp.fst) fun vb =>
          Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8 =>
          Expr.let_ ⟨OpCode.sext 8 32, (Arg.var vb, ())⟩ fun s1 =>
          Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8.fst, ())⟩ fun s2 =>
          Expr.let_ ⟨OpCode.cmp CmpOp.sge i32, (Arg.var s1.fst, Arg.var s2.fst, ())⟩ fun ge =>
          Expr.jnz (Arg.var ge.fst)
            (Expr.jump J_out (Arg.var idx.fst, Arg.var w, Arg.imm true, ()))
            (Expr.let_ ⟨OpCode.add i64, (Arg.var idx.fst, Arg.imm 1, ())⟩ fun i1 =>
            Expr.jump J_sc.fst (Arg.var i1.fst, ())))
          (Expr.jump J_out (Arg.var idx.fst, exit_lit, exit_found, ())))
      Blocks.nil)
    (fun J_sc => Expr.jump J_sc.fst (init_idx, ()))

@[expose] def m7LpMaxLvlExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (arena lvl : V i64) (cbase csz64 : V i64) (other : V i32)
    (J_alvl : L [i32]) : Expr V L rs :=
  Expr.group (sig := [[i32, i64]])
    (fun J_ml => Blocks.cons
      (fun mp =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var mp.snd.fst, Arg.var csz64, ())⟩ fun c =>
        Expr.jnz (Arg.var c.fst)
          (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.var mp.snd.fst, ())⟩ fun a1 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun o1 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o1.fst, ())⟩ fun p1 =>
          Expr.load i32 (Arg.var p1.fst) fun lit =>
          Expr.group (sig := [[i32]])
            (fun J_step => Blocks.cons
              (fun mx =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var mp.snd.fst, Arg.imm 1, ())⟩ fun k1 =>
                Expr.jump J_ml.fst (Arg.var mx.fst, Arg.var k1.fst, ()))
              Blocks.nil)
            (fun J_step =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var lit, Arg.var other, ())⟩ fun ne =>
              Expr.jnz (Arg.var ne.fst)
                (Expr.let_ ⟨OpCode.lshr i32, (Arg.var lit, Arg.imm 1, ())⟩ fun v1 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var v1.fst, ())⟩ fun v64 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var v64.fst, Arg.imm 4, ())⟩ fun lo =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var lvl, Arg.var lo.fst, ())⟩ fun lp =>
                Expr.load i32 (Arg.var lp.fst) fun lv =>
                Expr.group (sig := [[i32]])
                  (fun J_mx => Blocks.cons
                    (fun mx => Expr.jump J_step.fst (Arg.var mx.fst, ()))
                    Blocks.nil)
                  (fun J_mx =>
                    Expr.let_ ⟨OpCode.cmp CmpOp.ugt i32, (Arg.var lv, Arg.var mp.fst, ())⟩ fun gt =>
                    Expr.jnz (Arg.var gt.fst)
                      (Expr.jump J_mx.fst (Arg.var lv, ()))
                      (Expr.jump J_mx.fst (Arg.var mp.fst, ()))))
                (Expr.jump J_step.fst (Arg.var mp.fst, ()))))
          (Expr.jump J_alvl (Arg.var mp.fst, ())))
      Blocks.nil)
    (fun J_ml => Expr.jump J_ml.fst (Arg.imm 0, Arg.imm 0, ()))

@[expose] def m7LpReplPushExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr wstk arena : V i64) (not_lit other cref : V i32)
    (te un uf tk' p2 q brk0 cbase ri : V i64) (repl : V i32)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    (J_lp : L [i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.group (sig := [[i64, Ty.bool, i32, i32, i32, i64]])
    (fun J_ret => Blocks.cons
      (fun r =>
        Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk',
          Arg.var p2, Arg.var r.fst, ()))
      Blocks.nil)
    (fun J_ret =>
      Expr.let_ ⟨OpCode.cmp CmpOp.eq i32, (Arg.var repl, Arg.var not_lit, ())⟩ fun ce =>
      Expr.jnz (Arg.var ce.fst)
        (Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase, Arg.imm 4, ())⟩ fun o0 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o0.fst, ())⟩ fun a0 =>
        Expr.store (Arg.var other) (Arg.var a0.fst)
          (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.imm 1, ())⟩ fun i1 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var i1.fst, Arg.imm 4, ())⟩ fun o1 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o1.fst, ())⟩ fun a1 =>
          Expr.store (Arg.var repl) (Arg.var a1.fst)
            (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.var ri, ())⟩ fun ir =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var ir.fst, Arg.imm 4, ())⟩ fun or1 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var or1.fst, ())⟩ fun ar1 =>
            Expr.store (Arg.var not_lit) (Arg.var ar1.fst)
              (Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun q0 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q0.fst, ())⟩ fun qp0 =>
              Expr.store (Arg.var other) (Arg.var qp0.fst)
                (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun q1 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q1.fst, ())⟩ fun qp1 =>
                Expr.store (Arg.var cref) (Arg.var qp1.fst)
                  (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
                  Expr.jump J_ret.fst (Arg.var q2.fst, Arg.imm false, Arg.imm 0,
                    Arg.imm 0, Arg.imm 0, Arg.imm 0, ())))))))
        (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 104, ())⟩ fun p_wv =>
        Expr.load i64 (Arg.var p_wv.fst) fun wvec =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 40, ())⟩ fun p_wc =>
        Expr.load i64 (Arg.var p_wc.fst) fun wcap =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 56, ())⟩ fun p_wl =>
        Expr.load i64 (Arg.var p_wl.fst) fun wlen =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var repl, ())⟩ fun r64 =>
        Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun s1 =>
        Expr.let_ ⟨OpCode.shl i64, (Arg.var r64.fst, Arg.var s1.fst, ())⟩ fun ridx =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var ridx.fst, Arg.imm 4, ())⟩ fun ro =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var wvec, Arg.var ro.fst, ())⟩ fun rp =>
        Expr.load i32 (Arg.var rp.fst) fun off32 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var off32, ())⟩ fun off =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var ridx.fst, Arg.imm 1, ())⟩ fun ridx1 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var ridx1.fst, Arg.imm 4, ())⟩ fun ro1 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var wvec, Arg.var ro1.fst, ())⟩ fun rp1 =>
        Expr.load i32 (Arg.var rp1.fst) fun len32 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var len32, ())⟩ fun len =>
        Expr.group (sig := [[Ty.bool, i32, i32, i32, i64]])
          (fun J_e1 => Blocks.cons
            (fun r1 =>
              Expr.jump J_ret.fst (Arg.var q, Arg.var r1.fst, Arg.var r1.snd.fst,
                Arg.var r1.snd.snd.fst, Arg.var r1.snd.snd.snd.fst,
                Arg.var r1.snd.snd.snd.snd.fst, ()))
            Blocks.nil)
          (fun J_e1 =>
            Expr.group (sig := [[]])
              (fun J_e2 => Blocks.cons
                (fun _ => Expr.group (sig := [[Ty.bool, i32, i32, i32, i64]])
                  (fun J_e3 => Blocks.cons
                    (fun r3 => Expr.jump J_e1.fst (Arg.var r3.fst, Arg.var r3.snd.fst,
                      Arg.var r3.snd.snd.fst, Arg.var r3.snd.snd.snd.fst,
                      Arg.var r3.snd.snd.snd.snd.fst, ()))
                    Blocks.nil)
                  (fun J_e3 =>
                    Expr.group (sig := [[]])
                      (fun J_snt => Blocks.cons
                        (fun _ =>
                          Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64, (Arg.var len.fst, Arg.imm 0,
                              ())⟩ fun g0 =>
                          Expr.jnz (Arg.var g0.fst)
                            (Expr.let_ ⟨OpCode.add i64, (Arg.var off.fst, Arg.var len.fst,
                                ())⟩ fun s1 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var s1.fst, Arg.imm 2, ())⟩ fun s2 =>
                            Expr.let_ ⟨OpCode.cmp CmpOp.ule i64, (Arg.var s2.fst, Arg.var wlen,
                                ())⟩ fun lew =>
                            Expr.jnz (Arg.var lew.fst)
                              (Expr.let_ ⟨OpCode.add i64, (Arg.var off.fst, Arg.var len.fst,
                                  ())⟩ fun e0 =>
                              Expr.let_ ⟨OpCode.mul i64, (Arg.var e0.fst, Arg.imm 4, ())⟩ fun eo0 =>
                              Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var eo0.fst,
                                  ())⟩ fun ep0 =>
                              Expr.load i32 (Arg.var ep0.fst) fun w0 =>
                              Expr.let_ ⟨OpCode.cmp CmpOp.eq i32, (Arg.var w0, Arg.imm 4294967295,
                                  ())⟩ fun c0 =>
                              Expr.jnz (Arg.var c0.fst)
                                (Expr.let_ ⟨OpCode.add i64, (Arg.var off.fst, Arg.var len.fst,
                                    ())⟩ fun e1 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var e1.fst, Arg.imm 1,
                                    ())⟩ fun e1p =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var e1p.fst, Arg.imm 4,
                                    ())⟩ fun eo1 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var eo1.fst,
                                    ())⟩ fun ep1 =>
                                Expr.load i32 (Arg.var ep1.fst) fun w1 =>
                                Expr.let_ ⟨OpCode.cmp CmpOp.eq i32,
                                    (Arg.var w1, Arg.imm 4294967295, ())⟩ fun c1 =>
                                Expr.jnz (Arg.var c1.fst)
                                  (Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase, Arg.imm 4,
                                      ())⟩ fun ao0 =>
                                  Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao0.fst,
                                      ())⟩ fun ap0 =>
                                  Expr.store (Arg.var other) (Arg.var ap0.fst)
                                    (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.imm 1,
                                        ())⟩ fun ci1 =>
                                    Expr.let_ ⟨OpCode.mul i64, (Arg.var ci1.fst, Arg.imm 4,
                                        ())⟩ fun ao1 =>
                                    Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao1.fst,
                                        ())⟩ fun ap1 =>
                                    Expr.store (Arg.var repl) (Arg.var ap1.fst)
                                      (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.var ri,
                                          ())⟩ fun cir =>
                                      Expr.let_ ⟨OpCode.mul i64, (Arg.var cir.fst, Arg.imm 4,
                                          ())⟩ fun aor =>
                                      Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var aor.fst,
                                          ())⟩ fun apr =>
                                      Expr.store (Arg.var not_lit) (Arg.var apr.fst)
                                        (Expr.let_ ⟨OpCode.add i64,
                                            (Arg.var off.fst, Arg.var len.fst, ())⟩ fun ow0 =>
                                        Expr.let_ ⟨OpCode.mul i64, (Arg.var ow0.fst, Arg.imm 4,
                                            ())⟩ fun owo0 =>
                                        Expr.let_ ⟨OpCode.add i64,
                                            (Arg.var wstk, Arg.var owo0.fst, ())⟩ fun owp0 =>
                                        Expr.store (Arg.var other) (Arg.var owp0.fst)
                                          (Expr.let_ ⟨OpCode.add i64,
                                              (Arg.var off.fst, Arg.var len.fst, ())⟩ fun ow1 =>
                                          Expr.let_ ⟨OpCode.add i64, (Arg.var ow1.fst, Arg.imm 1,
                                              ())⟩ fun ow1p =>
                                          Expr.let_ ⟨OpCode.mul i64, (Arg.var ow1p.fst, Arg.imm 4,
                                              ())⟩ fun owo1 =>
                                          Expr.let_ ⟨OpCode.add i64,
                                              (Arg.var wstk, Arg.var owo1.fst, ())⟩ fun owp1 =>
                                          Expr.store (Arg.var cref) (Arg.var owp1.fst)
                                            (Expr.let_ ⟨OpCode.add i64,
                                                (Arg.var ridx.fst, Arg.imm 1, ())⟩ fun rx1 =>
                                            Expr.let_ ⟨OpCode.mul i64,
                                                (Arg.var rx1.fst, Arg.imm 4, ())⟩ fun rxo =>
                                            Expr.let_ ⟨OpCode.add i64,
                                                (Arg.var wvec, Arg.var rxo.fst, ())⟩ fun rxp =>
                                            Expr.let_ ⟨OpCode.add i64,
                                                (Arg.var len.fst, Arg.imm 2, ())⟩ fun ln2 =>
                                            Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var ln2.fst,
                                                ())⟩ fun ln232 =>
                                            Expr.store (Arg.var ln232.fst) (Arg.var rxp.fst)
                                              (Expr.let_ ⟨OpCode.add i64,
                                                  (Arg.var hdr, Arg.imm 464, ())⟩ fun pwu =>
                                              Expr.load i64 (Arg.var pwu.fst) fun wu =>
                                              Expr.group (sig := [[]])
                                                (fun J_wu => Blocks.cons
                                                  (fun _ => Expr.jump J_e3.fst (Arg.imm false,
                                                    Arg.imm 0, Arg.imm 0, Arg.imm 0, Arg.imm 0, ()))
                                                  Blocks.nil)
                                                (fun J_wu =>
                                                  Expr.let_ ⟨OpCode.cmp CmpOp.uge i64,
                                                      (Arg.var wu, Arg.imm 2, ())⟩
                                                      fun ge2 =>
                                                  Expr.jnz (Arg.var ge2.fst)
                                                    (Expr.let_ ⟨OpCode.sub i64,
                                                        (Arg.var wu, Arg.imm 2, ())⟩ fun wu' =>
                                                    Expr.let_ ⟨OpCode.add i64,
                                                        (Arg.var hdr, Arg.imm 464, ())⟩ fun pw2 =>
                                                    Expr.store (Arg.var wu'.fst) (Arg.var pw2.fst)
                                                      (Expr.jump J_wu.fst ()))
                                                    (Expr.jump J_wu.fst ())))))))))
                                  (Expr.jump J_ovf (Arg.var te, Arg.var un, Arg.var uf,
                                    Arg.var tk', Arg.var p2, Arg.var q, Arg.var brk0,
                                    Arg.imm true, Arg.var repl, Arg.var other,
                                    Arg.var cref, Arg.var ri, ())))
                                (Expr.jump J_ovf (Arg.var te, Arg.var un, Arg.var uf,
                                  Arg.var tk', Arg.var p2, Arg.var q, Arg.var brk0,
                                  Arg.imm true, Arg.var repl, Arg.var other,
                                  Arg.var cref, Arg.var ri, ())))
                              (Expr.jump J_ovf (Arg.var te, Arg.var un, Arg.var uf,
                                Arg.var tk', Arg.var p2, Arg.var q, Arg.var brk0,
                                Arg.imm true, Arg.var repl, Arg.var other,
                                Arg.var cref, Arg.var ri, ())))
                            (Expr.jump J_ovf (Arg.var te, Arg.var un, Arg.var uf,
                              Arg.var tk', Arg.var p2, Arg.var q, Arg.var brk0,
                              Arg.imm true, Arg.var repl, Arg.var other,
                              Arg.var cref, Arg.var ri, ())))
                        Blocks.nil)
                      (fun J_snt =>
                        Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64, (Arg.var len.fst, Arg.imm 0,
                            ())⟩ fun g0 =>
                        Expr.jnz (Arg.var g0.fst)
                          (Expr.let_ ⟨OpCode.add i64, (Arg.var off.fst, Arg.var len.fst,
                              ())⟩ fun sm =>
                          Expr.let_ ⟨OpCode.cmp CmpOp.eq i64, (Arg.var sm.fst, Arg.var wlen,
                              ())⟩ fun eqw =>
                          Expr.jnz (Arg.var eqw.fst)
                            (Expr.let_ ⟨OpCode.add i64, (Arg.var wlen, Arg.imm 2, ())⟩ fun wl2 =>
                            Expr.let_ ⟨OpCode.cmp CmpOp.ule i64, (Arg.var wl2.fst, Arg.var wcap,
                                ())⟩ fun le =>
                            Expr.jnz (Arg.var le.fst)
                              (Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase, Arg.imm 4, ())⟩ fun ao0 =>
                              Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao0.fst,
                                  ())⟩ fun ap0 =>
                              Expr.store (Arg.var other) (Arg.var ap0.fst)
                                (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.imm 1,
                                    ())⟩ fun ci1 =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var ci1.fst, Arg.imm 4,
                                    ())⟩ fun ao1 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao1.fst,
                                    ())⟩ fun ap1 =>
                                Expr.store (Arg.var repl) (Arg.var ap1.fst)
                                  (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.var ri,
                                      ())⟩ fun cir =>
                                  Expr.let_ ⟨OpCode.mul i64, (Arg.var cir.fst, Arg.imm 4,
                                      ())⟩ fun aor =>
                                  Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var aor.fst,
                                      ())⟩ fun apr =>
                                  Expr.store (Arg.var not_lit) (Arg.var apr.fst)
                                    (Expr.let_ ⟨OpCode.mul i64, (Arg.var wlen, Arg.imm 4,
                                        ())⟩ fun wo0 =>
                                    Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var wo0.fst,
                                        ())⟩ fun wp0 =>
                                    Expr.store (Arg.var other) (Arg.var wp0.fst)
                                      (Expr.let_ ⟨OpCode.add i64, (Arg.var wlen, Arg.imm 1,
                                          ())⟩ fun wl1 =>
                                      Expr.let_ ⟨OpCode.mul i64, (Arg.var wl1.fst, Arg.imm 4,
                                          ())⟩ fun wo1 =>
                                      Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var wo1.fst,
                                          ())⟩ fun wp1 =>
                                      Expr.store (Arg.var cref) (Arg.var wp1.fst)
                                        (Expr.let_ ⟨OpCode.add i64, (Arg.var wlen, Arg.imm 2,
                                            ())⟩ fun wl2' =>
                                        Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 56,
                                            ())⟩ fun pwl2 =>
                                        Expr.store (Arg.var wl2'.fst) (Arg.var pwl2.fst)
                                          (Expr.let_ ⟨OpCode.add i64,
                                              (Arg.var ridx.fst, Arg.imm 1, ())⟩ fun rx1 =>
                                          Expr.let_ ⟨OpCode.mul i64, (Arg.var rx1.fst, Arg.imm 4,
                                              ())⟩ fun rxo =>
                                          Expr.let_ ⟨OpCode.add i64,
                                              (Arg.var wvec, Arg.var rxo.fst, ())⟩ fun rxp =>
                                          Expr.let_ ⟨OpCode.add i64, (Arg.var len.fst, Arg.imm 2,
                                              ())⟩ fun ln2 =>
                                          Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var ln2.fst,
                                              ())⟩ fun ln232 =>
                                          Expr.store (Arg.var ln232.fst) (Arg.var rxp.fst)
                                            (Expr.jump J_e3.fst
                                                (Arg.imm false, Arg.imm 0, Arg.imm 0,
                                              Arg.imm 0, Arg.imm 0, ())))))))))
                              (Expr.jump J_snt.fst ()))
                            (Expr.jump J_snt.fst ()))
                          (Expr.jump J_snt.fst ()))))
                Blocks.nil)
              (fun J_e2 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.eq i64, (Arg.var len.fst, Arg.imm 0, ())⟩ fun z0 =>
                Expr.jnz (Arg.var z0.fst)
                  (Expr.let_ ⟨OpCode.add i64, (Arg.var wlen, Arg.imm 2, ())⟩ fun wl2 =>
                  Expr.let_ ⟨OpCode.cmp CmpOp.ule i64, (Arg.var wl2.fst, Arg.var wcap,
                      ())⟩ fun le =>
                  Expr.jnz (Arg.var le.fst)
                    (Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase, Arg.imm 4, ())⟩ fun ao0 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao0.fst, ())⟩ fun ap0 =>
                    Expr.store (Arg.var other) (Arg.var ap0.fst)
                      (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.imm 1, ())⟩ fun ci1 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var ci1.fst, Arg.imm 4, ())⟩ fun ao1 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao1.fst, ())⟩ fun ap1 =>
                      Expr.store (Arg.var repl) (Arg.var ap1.fst)
                        (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.var ri, ())⟩ fun cir =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var cir.fst, Arg.imm 4, ())⟩ fun aor =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var aor.fst, ())⟩ fun apr =>
                        Expr.store (Arg.var not_lit) (Arg.var apr.fst)
                          (Expr.let_ ⟨OpCode.mul i64, (Arg.var ridx.fst, Arg.imm 4, ())⟩ fun rxo =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var wvec, Arg.var rxo.fst, ())⟩ fun rxp =>
                          Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var wlen, ())⟩ fun wl32 =>
                          Expr.store (Arg.var wl32.fst) (Arg.var rxp.fst)
                            (Expr.let_ ⟨OpCode.add i64, (Arg.var ridx.fst, Arg.imm 1,
                                ())⟩ fun rx1 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var rx1.fst, Arg.imm 4, ())⟩ fun rxo1 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var wvec, Arg.var rxo1.fst,
                                ())⟩ fun rxp1 =>
                            Expr.store (Arg.imm (t := i32) 2) (Arg.var rxp1.fst)
                              (Expr.let_ ⟨OpCode.mul i64, (Arg.var wlen, Arg.imm 4, ())⟩ fun wo0 =>
                              Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var wo0.fst,
                                  ())⟩ fun wp0 =>
                              Expr.store (Arg.var other) (Arg.var wp0.fst)
                                (Expr.let_ ⟨OpCode.add i64, (Arg.var wlen, Arg.imm 1,
                                    ())⟩ fun wl1 =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var wl1.fst, Arg.imm 4,
                                    ())⟩ fun wo1 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var wo1.fst,
                                    ())⟩ fun wp1 =>
                                Expr.store (Arg.var cref) (Arg.var wp1.fst)
                                  (Expr.let_ ⟨OpCode.add i64, (Arg.var wlen, Arg.imm 2,
                                      ())⟩ fun wl2' =>
                                  Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 56,
                                      ())⟩ fun pwl2 =>
                                  Expr.store (Arg.var wl2'.fst) (Arg.var pwl2.fst)
                                    (Expr.jump J_e1.fst (Arg.imm false, Arg.imm 0, Arg.imm 0,
                                      Arg.imm 0, Arg.imm 0, ()))))))))))
                    (Expr.jump J_e2.fst ()))
                  (Expr.jump J_e2.fst ())))))

@[expose] def m7LpBinStepExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr vals wstk lvl rsns trl tpos flags phases : V i64) (rec_ph : V Ty.bool)
    (not_lit w0 : V i32) (te un uf tk p q : V i64)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    (J_lp : L [i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 1, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var w0, Arg.imm 2147483647, ())⟩ fun blk =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var blk.fst, ())⟩ fun blk64 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var blk64.fst, ())⟩ fun vp =>
  Expr.load i8 (Arg.var vp.fst) fun vb =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun qo =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var qo.fst, ())⟩ fun qp =>
  Expr.store (Arg.var w0) (Arg.var qp.fst)
    (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun q1 =>
    Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8 =>
    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var vb, ())⟩ fun s1 =>
    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8.fst, ())⟩ fun s2 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32, (Arg.var s1.fst, Arg.var s2.fst, ())⟩ fun gt =>
    Expr.jnz (Arg.var gt.fst)
      (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk,
        Arg.var p1.fst, Arg.var q1.fst, ()))
      (Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8' =>
      Expr.let_ ⟨OpCode.sext 8 32, (Arg.var vb, ())⟩ fun s1' =>
      Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8'.fst, ())⟩ fun s2' =>
      Expr.let_ ⟨OpCode.cmp CmpOp.slt i32, (Arg.var s1'.fst, Arg.var s2'.fst, ())⟩ fun lt =>
      Expr.jnz (Arg.var lt.fst)
        (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 528, ())⟩ fun pct =>
        Expr.store (Arg.imm (t := i64) 1) (Arg.var pct.fst)
          (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var not_lit, ())⟩ fun nl64 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 536, ())⟩ fun pcl0 =>
          Expr.store (Arg.var nl64.fst) (Arg.var pcl0.fst)
            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var blk.fst, ())⟩ fun bl64 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 544, ())⟩ fun pcl1 =>
            Expr.store (Arg.var bl64.fst) (Arg.var pcl1.fst)
              (Expr.jump J_ovf (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk,
                Arg.var p1.fst, Arg.var q1.fst, Arg.imm 1, Arg.imm false,
                Arg.imm 0, Arg.imm 0, Arg.imm 0, Arg.imm 0, ())))))
        (Expr.let_ ⟨OpCode.add i64, (Arg.var tk, Arg.imm 1, ())⟩ fun tk1 =>
        Expr.let_ ⟨OpCode.lshr i32, (Arg.var not_lit, Arg.imm 1, ())⟩ fun nv =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var nv.fst, ())⟩ fun nv64 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var nv64.fst, Arg.imm 4, ())⟩ fun nvo =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var lvl, Arg.var nvo.fst, ())⟩ fun nvp =>
        Expr.load i32 (Arg.var nvp.fst) fun nl_lvl0 =>
        Expr.let_ ⟨OpCode.lshr i32, (Arg.var blk.fst, Arg.imm 1, ())⟩ fun bv =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var bv.fst, ())⟩ fun bv64 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var blk.fst, ())⟩ fun bl64' =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var bl64'.fst, ())⟩ fun vp1 =>
        Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 1, ())⟩ fun bpos =>
        Expr.store (Arg.var bpos.fst) (Arg.var vp1.fst)
          (Expr.let_ ⟨OpCode.xor i32, (Arg.var blk.fst, Arg.imm 1, ())⟩ fun nblk =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var nblk.fst, ())⟩ fun nb64 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var nb64.fst, ())⟩ fun vp2 =>
          Expr.let_ ⟨OpCode.neg i32, (Arg.imm 1, ())⟩ fun m1 =>
          Expr.let_ ⟨OpCode.trunc 32 8, (Arg.var m1.fst, ())⟩ fun bneg =>
          Expr.store (Arg.var bneg.fst) (Arg.var vp2.fst)
            (m7LpAssignTailExpr lvl rsns trl tpos flags phases rec_ph not_lit
              te un uf tk1.fst p1.fst q1.fst bv64.fst blk.fst nl_lvl0 none J_lp)))))

@[expose] def m7LpLargeStepExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr ignore_ref vals wstk arena lvl rsns trl tpos flags phases : V i64)
    (two_cv : V i64) (cur_lvl32 not_lit w0 : V i32) (rec_ph : V Ty.bool)
    (te un uf tk p q brk0 : V i64)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    (J_lp : L [i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.group (sig := [[]])
    (fun J_c => Blocks.cons
      (fun _ =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 1, ())⟩ fun p1 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun po1 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var po1.fst, ())⟩ fun pp1 =>
        Expr.load i32 (Arg.var pp1.fst) fun cref =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 2, ())⟩ fun p2 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var tk, Arg.imm 1, ())⟩ fun tk1 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var cr64.fst, Arg.imm 4, ())⟩ fun fo =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var fo.fst, ())⟩ fun fp =>
        Expr.load i32 (Arg.var fp.fst) fun fl =>
        Expr.let_ ⟨OpCode.and i32, (Arg.var fl, Arg.imm 524288, ())⟩ fun flg =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var flg.fst, Arg.imm 0, ())⟩ fun gar =>
        Expr.jnz (Arg.var gar.fst)
          (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1.fst,
            Arg.var p2.fst, Arg.var q, ()))
          (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64' =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var cr64'.fst, Arg.imm 3, ())⟩ fun cbase =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase.fst, Arg.imm 4, ())⟩ fun o0 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o0.fst, ())⟩ fun a0 =>
          Expr.load i32 (Arg.var a0.fst) fun l0 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var cbase.fst, Arg.imm 1, ())⟩ fun i1 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var i1.fst, Arg.imm 4, ())⟩ fun o1 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o1.fst, ())⟩ fun a1 =>
          Expr.load i32 (Arg.var a1.fst) fun l1 =>
          Expr.group (sig := [[]])
            (fun J_chk => Blocks.cons
              (fun _ =>
                Expr.let_ ⟨OpCode.xor i32, (Arg.var l0, Arg.var l1, ())⟩ fun x1 =>
                Expr.let_ ⟨OpCode.xor i32, (Arg.var x1.fst, Arg.var not_lit, ())⟩ fun other =>
                Expr.group (sig := [[]])
                  (fun J_sw => Blocks.cons
                    (fun _ =>
                      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var other.fst, ())⟩ fun o64 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var o64.fst, ())⟩ fun vp =>
                      Expr.load i8 (Arg.var vp.fst) fun ov =>
                      Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8 =>
                      Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ov, ())⟩ fun s1 =>
                      Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8.fst, ())⟩ fun s2 =>
                      Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32, (Arg.var s1.fst, Arg.var s2.fst,
                          ())⟩ fun gt =>
                      Expr.jnz (Arg.var gt.fst)
                        (Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun q0 =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q0.fst, ())⟩ fun qp0 =>
                        Expr.store (Arg.var other.fst) (Arg.var qp0.fst)
                          (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
                          Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun q1 =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q1.fst, ())⟩ fun qp1 =>
                          Expr.store (Arg.var cref) (Arg.var qp1.fst)
                            (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
                            Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf,
                              Arg.var tk1.fst, Arg.var p2.fst, Arg.var q2.fst, ()))))
                        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64a =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var cr64a.fst, Arg.imm 2, ())⟩ fun szi =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var szi.fst, Arg.imm 4, ())⟩ fun szo =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var szo.fst, ())⟩ fun szp =>
                        Expr.load i32 (Arg.var szp.fst) fun csz32 =>
                        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var csz32, ())⟩ fun csz =>
                        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64b =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var cr64b.fst, Arg.imm 1, ())⟩ fun psi =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var psi.fst, Arg.imm 4, ())⟩ fun pso =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var pso.fst, ())⟩ fun psp =>
                        Expr.load i32 (Arg.var psp.fst) fun pos32 =>
                        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var pos32, ())⟩ fun pos =>
                        Expr.group (sig := [[i64]])
                          (fun J_st => Blocks.cons
                            (fun st =>
                              Expr.group (sig := [[i64, i32, Ty.bool]])
                                (fun J_r1 => Blocks.cons
                                  (fun s1p =>
                                    Expr.group (sig := [[i64, i32, Ty.bool]])
                                      (fun J_r2 => Blocks.cons
                                        (fun s2p =>
                                          Expr.jnz (Arg.var s2p.snd.snd.fst)
                                            (Expr.let_ ⟨OpCode.add i64,
                                                (Arg.var tk1.fst, Arg.imm 1, ())⟩
                                                fun tk2 =>
                                            Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref,
                                                ())⟩ fun cr64c =>
                                            Expr.let_ ⟨OpCode.add i64,
                                                (Arg.var cr64c.fst, Arg.imm 1, ())⟩
                                                fun psi2 =>
                                            Expr.let_ ⟨OpCode.mul i64,
                                                (Arg.var psi2.fst, Arg.imm 4, ())⟩
                                                fun pso2 =>
                                            Expr.let_ ⟨OpCode.add i64,
                                                (Arg.var arena, Arg.var pso2.fst, ())⟩
                                                fun psp2 =>
                                            Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var s2p.fst,
                                                ())⟩ fun ri32 =>
                                            Expr.store (Arg.var ri32.fst) (Arg.var psp2.fst)
                                              (m7LpReplPushExpr hdr wstk arena not_lit other.fst
                                                cref te un uf tk2.fst p2.fst q brk0 cbase.fst
                                                s2p.fst s2p.snd.fst J_ovf J_lp))
                                            (Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4,
                                                ())⟩ fun q0 =>
                                            Expr.let_ ⟨OpCode.add i64,
                                                (Arg.var wstk, Arg.var q0.fst, ())⟩
                                                fun qp0 =>
                                            Expr.store (Arg.var other.fst) (Arg.var qp0.fst)
                                              (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1,
                                                  ())⟩ fun qi1 =>
                                              Expr.let_ ⟨OpCode.mul i64,
                                                  (Arg.var qi1.fst, Arg.imm 4, ())⟩
                                                  fun q1 =>
                                              Expr.let_ ⟨OpCode.add i64,
                                                  (Arg.var wstk, Arg.var q1.fst, ())⟩
                                                  fun qp1 =>
                                              Expr.store (Arg.var cref) (Arg.var qp1.fst)
                                                (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2,
                                                    ())⟩ fun q2 =>
                                                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref,
                                                    ())⟩ fun cr64d =>
                                                Expr.let_ ⟨OpCode.cmp CmpOp.eq i64,
                                                    (Arg.var cr64d.fst, Arg.var ignore_ref,
                                                        ())⟩ fun eqig =>
                                                Expr.jnz (Arg.var eqig.fst)
                                                  (Expr.jump J_lp (Arg.var te, Arg.var un,
                                                    Arg.var uf, Arg.var tk1.fst, Arg.var p2.fst,
                                                    Arg.var q2.fst, ()))
                                                  (Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0,
                                                      ())⟩ fun z8' =>
                                                  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ov,
                                                      ())⟩ fun s1' =>
                                                  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8'.fst,
                                                      ())⟩ fun s2' =>
                                                  Expr.let_ ⟨OpCode.cmp CmpOp.slt i32,
                                                      (Arg.var s1'.fst, Arg.var s2'.fst,
                                                          ())⟩ fun lt =>
                                                  Expr.jnz (Arg.var lt.fst)
                                                    (Expr.let_ ⟨OpCode.add i64,
                                                        (Arg.var hdr, Arg.imm 528, ())⟩
                                                        fun pct =>
                                                    Expr.store (Arg.imm (t := i64) 2)
                                                        (Arg.var pct.fst)
                                                      (Expr.let_ ⟨OpCode.zext 32 64,
                                                          (Arg.var cref, ())⟩
                                                          fun cr64e =>
                                                      Expr.let_ ⟨OpCode.add i64,
                                                          (Arg.var hdr, Arg.imm 176, ())⟩
                                                          fun pcr =>
                                                      Expr.store (Arg.var cr64e.fst)
                                                          (Arg.var pcr.fst)
                                                        (Expr.jump J_ovf (Arg.var te, Arg.var un,
                                                          Arg.var uf, Arg.var tk1.fst,
                                                          Arg.var p2.fst, Arg.var q2.fst,
                                                          Arg.imm 1, Arg.imm false, Arg.imm 0,
                                                          Arg.imm 0, Arg.imm 0, Arg.imm 0, ()))))
                                                    (Expr.let_ ⟨OpCode.add i64,
                                                        (Arg.var tk1.fst, Arg.imm 1, ())⟩
                                                        fun tk2 =>
                                                    Expr.let_ ⟨OpCode.lshr i32,
                                                        (Arg.var not_lit, Arg.imm 1, ())⟩
                                                        fun nv =>
                                                    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var nv.fst,
                                                        ())⟩ fun nv64 =>
                                                    Expr.let_ ⟨OpCode.mul i64,
                                                        (Arg.var nv64.fst, Arg.imm 4, ())⟩
                                                        fun nvo =>
                                                    Expr.let_ ⟨OpCode.add i64,
                                                        (Arg.var lvl, Arg.var nvo.fst, ())⟩
                                                        fun nvp =>
                                                    Expr.load i32 (Arg.var nvp.fst) fun nl_lvl =>
                                                    Expr.group (sig := [[i32]])
                                                      (fun J_alvl => Blocks.cons
                                                        (fun alvlp =>
                                                          Expr.let_ ⟨OpCode.lshr i32,
                                                              (Arg.var other.fst, Arg.imm 1,
                                                                  ())⟩ fun ovv =>
                                                          Expr.let_ ⟨OpCode.zext 32 64,
                                                              (Arg.var ovv.fst, ())⟩
                                                              fun ov64 =>
                                                          Expr.let_ ⟨OpCode.zext 32 64,
                                                              (Arg.var other.fst, ())⟩
                                                              fun ot64 =>
                                                          Expr.let_ ⟨OpCode.add i64,
                                                              (Arg.var vals, Arg.var ot64.fst,
                                                                  ())⟩ fun vp1 =>
                                                          Expr.let_ ⟨OpCode.trunc 32 8,
                                                              (Arg.imm 1, ())⟩ fun bpos =>
                                                          Expr.store (Arg.var bpos.fst)
                                                              (Arg.var vp1.fst)
                                                            (Expr.let_ ⟨OpCode.xor i32,
                                                                (Arg.var other.fst, Arg.imm 1,
                                                                    ())⟩ fun noth =>
                                                            Expr.let_ ⟨OpCode.zext 32 64,
                                                                (Arg.var noth.fst, ())⟩
                                                                fun no64 =>
                                                            Expr.let_ ⟨OpCode.add i64,
                                                                (Arg.var vals, Arg.var no64.fst,
                                                                    ())⟩ fun vp2 =>
                                                            Expr.let_ ⟨OpCode.neg i32, (Arg.imm 1,
                                                                ())⟩ fun m1 =>
                                                            Expr.let_ ⟨OpCode.trunc 32 8,
                                                                (Arg.var m1.fst, ())⟩
                                                                fun bneg =>
                                                            Expr.store (Arg.var bneg.fst)
                                                                (Arg.var vp2.fst)
                                                              (m7LpAssignTailExpr lvl rsns trl tpos
                                                                flags phases rec_ph not_lit te un uf
                                                                tk2.fst p2.fst q2.fst ov64.fst
                                                                other.fst alvlp.fst (some cref)
                                                                J_lp)))
                                                        Blocks.nil)
                                                      (fun J_alvl =>
                                                        Expr.let_ ⟨OpCode.cmp CmpOp.ult i32,
                                                            (Arg.var nl_lvl, Arg.var cur_lvl32,
                                                                ())⟩ fun lt =>
                                                        Expr.jnz (Arg.var lt.fst)
                                                          (m7LpMaxLvlExpr arena lvl cbase.fst
                                                            csz.fst other.fst J_alvl.fst)
                                                          (Expr.jump J_alvl.fst
                                                            (Arg.var nl_lvl, ())))))))))
                                        Blocks.nil)
                                      (fun J_r2 =>
                                        Expr.jnz (Arg.var s1p.snd.snd.fst)
                                          (Expr.jump J_r2.fst (Arg.var s1p.fst,
                                            Arg.var s1p.snd.fst, Arg.var s1p.snd.snd.fst, ()))
                                          (Expr.group (sig := [[i64, i32, Ty.bool]])
                                            (fun J_w => Blocks.cons
                                              (fun wp => Expr.jump J_r2.fst (Arg.var wp.fst,
                                                Arg.var wp.snd.fst, Arg.var wp.snd.snd.fst, ()))
                                              Blocks.nil)
                                            (fun J_w => m7LpReplScanExpr vals arena cbase.fst st.fst
                                              (Arg.imm 2) (Arg.var s1p.snd.fst)
                                              (Arg.var s1p.snd.snd.fst) J_w.fst))))
                                  Blocks.nil)
                                (fun J_r1 =>
                                  m7LpReplScanExpr vals arena cbase.fst csz.fst (Arg.var st.fst)
                                    (Arg.imm 0) (Arg.imm false) J_r1.fst))
                            Blocks.nil)
                          (fun J_st =>
                            Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var pos.fst, Arg.imm 2,
                                ())⟩ fun lt2 =>
                            Expr.jnz (Arg.var lt2.fst)
                              (Expr.jump J_st.fst (Arg.imm 2, ()))
                              (Expr.let_ ⟨OpCode.cmp CmpOp.uge i64,
                                  (Arg.var pos.fst, Arg.var csz.fst, ())⟩
                                  fun gec =>
                              Expr.jnz (Arg.var gec.fst)
                                (Expr.jump J_st.fst (Arg.imm 2, ()))
                                (Expr.jump J_st.fst (Arg.var pos.fst, ()))))))
                  Blocks.nil)
                (fun J_sw =>
                  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32, (Arg.var l0, Arg.var not_lit, ())⟩ fun eq0 =>
                  Expr.jnz (Arg.var eq0.fst)
                    (Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase.fst, Arg.imm 4, ())⟩ fun ao0 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao0.fst, ())⟩ fun ap0 =>
                    Expr.store (Arg.var other.fst) (Arg.var ap0.fst)
                      (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase.fst, Arg.imm 1, ())⟩ fun ci1 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var ci1.fst, Arg.imm 4, ())⟩ fun ao1 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao1.fst, ())⟩ fun ap1 =>
                      Expr.store (Arg.var not_lit) (Arg.var ap1.fst)
                        (Expr.jump J_sw.fst ())))
                    (Expr.jump J_sw.fst ())))
              Blocks.nil)
            (fun J_chk =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var l0, Arg.var not_lit, ())⟩ fun ne0 =>
              Expr.jnz (Arg.var ne0.fst)
                (Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var l1, Arg.var not_lit, ())⟩ fun ne1 =>
                Expr.jnz (Arg.var ne1.fst)
                  (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1.fst,
                    Arg.var p2.fst, Arg.var q, ()))
                  (Expr.jump J_chk.fst ()))
                (Expr.jump J_chk.fst ()))))
      Blocks.nil)
    (fun J_c =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w0, ())⟩ fun w64 =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var w64.fst, Arg.var two_cv, ())⟩ fun ltv =>
      Expr.jnz (Arg.var ltv.fst)
        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w0, ())⟩ fun w64' =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var w64'.fst, ())⟩ fun vp =>
        Expr.load i8 (Arg.var vp.fst) fun vw =>
        Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8 =>
        Expr.let_ ⟨OpCode.sext 8 32, (Arg.var vw, ())⟩ fun s1 =>
        Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8.fst, ())⟩ fun s2 =>
        Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32, (Arg.var s1.fst, Arg.var s2.fst, ())⟩ fun gt =>
        Expr.jnz (Arg.var gt.fst)
          (Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 1, ())⟩ fun p1 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun po1 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var po1.fst, ())⟩ fun pp1 =>
          Expr.load i32 (Arg.var pp1.fst) fun cref =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 2, ())⟩ fun p2 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun qo0 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var qo0.fst, ())⟩ fun qp0 =>
          Expr.store (Arg.var w0) (Arg.var qp0.fst)
            (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun qo1 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var qo1.fst, ())⟩ fun qp1 =>
            Expr.store (Arg.var cref) (Arg.var qp1.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
              Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk,
                Arg.var p2.fst, Arg.var q2.fst, ()))))
          (Expr.jump J_c.fst ()))
        (Expr.jump J_c.fst ()))

@[expose] def m7LpLoopExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr ignore_ref vals wstk arena lvl rsns trl tpos flags phases : V i64)
    (two_cv : V i64) (cur_lvl32 not_lit : V i32) (rec_ph : V Ty.bool)
    (end0 brk0 te0 un0 uf0 tk0 p0 q0 : V i64)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    : Expr V L rs :=
  Expr.group (sig := [[i64, i64, i64, i64, i64, i64]])
    (fun J_lp => Blocks.cons
      (fun lp =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var lp.snd.snd.snd.snd.fst, Arg.var end0, ())⟩
            fun c =>
        Expr.jnz (Arg.var c.fst)
          (Expr.let_ ⟨OpCode.mul i64, (Arg.var lp.snd.snd.snd.snd.fst, Arg.imm 4, ())⟩ fun po =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var po.fst, ())⟩ fun pp =>
          Expr.load i32 (Arg.var pp.fst) fun w0 =>
          Expr.let_ ⟨OpCode.and i32, (Arg.var w0, Arg.imm 2147483648, ())⟩ fun bin =>
          Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var bin.fst, Arg.imm 0, ())⟩ fun isbin =>
          Expr.jnz (Arg.var isbin.fst)
            (m7LpBinStepExpr hdr vals wstk lvl rsns trl tpos flags phases rec_ph
              not_lit w0 lp.fst lp.snd.fst lp.snd.snd.fst lp.snd.snd.snd.fst
              lp.snd.snd.snd.snd.fst lp.snd.snd.snd.snd.snd.fst J_ovf J_lp.fst)
            (m7LpLargeStepExpr hdr ignore_ref vals wstk arena lvl rsns trl tpos
              flags phases two_cv cur_lvl32 not_lit w0 rec_ph lp.fst lp.snd.fst
              lp.snd.snd.fst lp.snd.snd.snd.fst lp.snd.snd.snd.snd.fst
              lp.snd.snd.snd.snd.snd.fst brk0 J_ovf J_lp.fst))
          (Expr.jump J_ovf (Arg.var lp.fst, Arg.var lp.snd.fst,
            Arg.var lp.snd.snd.fst, Arg.var lp.snd.snd.snd.fst,
            Arg.var lp.snd.snd.snd.snd.fst, Arg.var lp.snd.snd.snd.snd.snd.fst,
            Arg.var brk0, Arg.imm false, Arg.imm 0, Arg.imm 0, Arg.imm 0,
            Arg.imm 0, ())))
      Blocks.nil)
    (fun J_lp =>
      Expr.jump J_lp.fst (Arg.var te0, Arg.var un0, Arg.var uf0, Arg.var tk0,
        Arg.var p0, Arg.var q0, ()))

end LeanQbe.T.Examples.Kissat.FullM7BcpHot
