/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1b0
public import LeanQbe.T.Examples.Kissat.FullFidelityBcp

/-!
# Kissat Fidelity Delayed-Watch BCP Proofs — Part 2b (Inner-Loop AST Builders)

Plain `public section` (`@[expose]` ONLY on non-recursive concrete AST `Expr` builders, `0`
`import all`). Mirrors the inner `while (p < end)` watch loop of `full_propagate_ignore_fid`
(hoisted `nl_lvl`, delayed-watch buffer `del[di ..< di + 3]`) and proves the inline assignment
tail, arena swap, and binary-watch step against the exact AST builders.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "fid_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "fid_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "fid_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. Inner-Loop AST Builders -/


@[expose] def fidLpAssignTailExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (lvl rsns trl tpos flags phases : V i64) (rec_ph : V Ty.bool)
    (not_lit : V i32) (te un uf tk_next p_next q_next di_next : V i64)
    (v_idx : V i64) (new_lit alvl : V i32) (rsn_cref : Option (V i32))
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
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
                          Arg.var tk_next, Arg.var p_next, Arg.var q_next, Arg.var di_next,
                          ()))))
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

@[expose] def fidLpBinStepExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr vals wstk lvl rsns trl tpos flags phases : V i64) (rec_ph : V Ty.bool)
    (not_lit w0 nl_lvl : V i32) (te un uf tk p q di : V i64)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
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
        Arg.var p1.fst, Arg.var q1.fst, Arg.var di, ()))
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
                Arg.var p1.fst, Arg.var q1.fst, Arg.var di, Arg.imm 1, Arg.imm false,
                Arg.imm 0, Arg.imm 0, Arg.imm 0, Arg.imm 0, ())))))
        (Expr.let_ ⟨OpCode.add i64, (Arg.var tk, Arg.imm 1, ())⟩ fun tk1 =>
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
            (fidLpAssignTailExpr lvl rsns trl tpos flags phases rec_ph not_lit
              te un uf tk1.fst p1.fst q1.fst di bv64.fst blk.fst nl_lvl none J_lp)))))

/-- Arena watch swap `ar[cbase] = other; ar[cbase + 1] = repl; ar[cbase + ri] = not_lit`. -/
@[expose] def fidLpArSwapExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (arena : V i64) (not_lit other repl : V i32) (cbase ri : V i64) (k : Expr V L rs) :
    Expr V L rs :=
  Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase, Arg.imm 4, ())⟩ fun o0 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o0.fst, ())⟩ fun a0 =>
  Expr.store (Arg.var other) (Arg.var a0.fst)
    (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.imm 1, ())⟩ fun i1 =>
    Expr.let_ ⟨OpCode.mul i64, (Arg.var i1.fst, Arg.imm 4, ())⟩ fun o1 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o1.fst, ())⟩ fun a1 =>
    Expr.store (Arg.var repl) (Arg.var a1.fst)
      (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase, Arg.var ri, ())⟩ fun ir =>
      Expr.let_ ⟨OpCode.mul i64, (Arg.var ir.fst, Arg.imm 4, ())⟩ fun or1 =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var or1.fst, ())⟩ fun ar1 =>
      Expr.store (Arg.var not_lit) (Arg.var ar1.fst) k))

/-- Found-replacement tail: keep (`repl == not_lit`), delayed buffer store (`di < dlim`), or
overflow exit. -/
@[expose] def fidLpReplDelExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (wstk arena del dlim : V i64) (not_lit other cref : V i32)
    (te un uf tk' p2 q di brk0 cbase ri : V i64) (repl : V i32)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.group (sig := [[i64, i64, Ty.bool, i32, i32, i32, i64]])
    (fun J_ret => Blocks.cons
      (fun r =>
        Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk',
          Arg.var p2, Arg.var r.fst, Arg.var r.snd.fst, ()))
      Blocks.nil)
    (fun J_ret =>
      Expr.let_ ⟨OpCode.cmp CmpOp.eq i32, (Arg.var repl, Arg.var not_lit, ())⟩ fun ce =>
      Expr.jnz (Arg.var ce.fst)
        (fidLpArSwapExpr arena not_lit other repl cbase ri
          (Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun q0 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q0.fst, ())⟩ fun qp0 =>
          Expr.store (Arg.var other) (Arg.var qp0.fst)
            (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun q1 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q1.fst, ())⟩ fun qp1 =>
            Expr.store (Arg.var cref) (Arg.var qp1.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
              Expr.jump J_ret.fst (Arg.var q2.fst, Arg.var di, Arg.imm false, Arg.imm 0,
                Arg.imm 0, Arg.imm 0, Arg.imm 0, ())))))
        (Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var di, Arg.var dlim, ())⟩ fun cd =>
        Expr.jnz (Arg.var cd.fst)
          (fidLpArSwapExpr arena not_lit other repl cbase ri
            (Expr.let_ ⟨OpCode.mul i64, (Arg.var di, Arg.imm 4, ())⟩ fun d0 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var del, Arg.var d0.fst, ())⟩ fun dp0 =>
            Expr.store (Arg.var repl) (Arg.var dp0.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var di, Arg.imm 1, ())⟩ fun di1 =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var di1.fst, Arg.imm 4, ())⟩ fun d1 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var del, Arg.var d1.fst, ())⟩ fun dp1 =>
              Expr.store (Arg.var other) (Arg.var dp1.fst)
                (Expr.let_ ⟨OpCode.add i64, (Arg.var di, Arg.imm 2, ())⟩ fun di2 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var di2.fst, Arg.imm 4, ())⟩ fun d2 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var del, Arg.var d2.fst, ())⟩ fun dp2 =>
                Expr.store (Arg.var cref) (Arg.var dp2.fst)
                  (Expr.let_ ⟨OpCode.add i64, (Arg.var di, Arg.imm 3, ())⟩ fun di3 =>
                  Expr.jump J_ret.fst (Arg.var q, Arg.var di3.fst, Arg.imm false, Arg.imm 0,
                    Arg.imm 0, Arg.imm 0, Arg.imm 0, ()))))))
          (Expr.jump J_ovf (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk', Arg.var p2,
            Arg.var q, Arg.var di, Arg.var brk0, Arg.imm true, Arg.var repl, Arg.var other,
            Arg.var cref, Arg.var ri, ()))))

/-- No-replacement tail: keep watch, then ignore / conflict / unit-assign (hoisted `nl_lvl`). -/
@[expose] def fidLpNoReplExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr ignore_ref vals wstk arena lvl rsns trl tpos flags phases : V i64)
    (cur_lvl32 not_lit nl_lvl other cref : V i32) (ov : V i8) (rec_ph : V Ty.bool)
    (te un uf tk1 p2 q di cbase csz : V i64)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun q0 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q0.fst, ())⟩ fun qp0 =>
  Expr.store (Arg.var other) (Arg.var qp0.fst)
    (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
    Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun q1 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q1.fst, ())⟩ fun qp1 =>
    Expr.store (Arg.var cref) (Arg.var qp1.fst)
      (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64d =>
      Expr.let_ ⟨OpCode.cmp CmpOp.eq i64, (Arg.var cr64d.fst, Arg.var ignore_ref, ())⟩
        fun eqig =>
      Expr.jnz (Arg.var eqig.fst)
        (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1, Arg.var p2,
          Arg.var q2.fst, Arg.var di, ()))
        (Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8' =>
        Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ov, ())⟩ fun s1' =>
        Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8'.fst, ())⟩ fun s2' =>
        Expr.let_ ⟨OpCode.cmp CmpOp.slt i32, (Arg.var s1'.fst, Arg.var s2'.fst, ())⟩ fun lt =>
        Expr.jnz (Arg.var lt.fst)
          (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 528, ())⟩ fun pct =>
          Expr.store (Arg.imm (t := i64) 2) (Arg.var pct.fst)
            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64e =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 176, ())⟩ fun pcr =>
            Expr.store (Arg.var cr64e.fst) (Arg.var pcr.fst)
              (Expr.jump J_ovf (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1, Arg.var p2,
                Arg.var q2.fst, Arg.var di, Arg.imm 1, Arg.imm false, Arg.imm 0, Arg.imm 0,
                Arg.imm 0, Arg.imm 0, ()))))
          (Expr.let_ ⟨OpCode.add i64, (Arg.var tk1, Arg.imm 1, ())⟩ fun tk2 =>
          Expr.group (sig := [[i32]])
            (fun J_alvl => Blocks.cons
              (fun alvlp =>
                Expr.let_ ⟨OpCode.lshr i32, (Arg.var other, Arg.imm 1, ())⟩ fun ovv =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ovv.fst, ())⟩ fun ov64 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var other, ())⟩ fun ot64 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var ot64.fst, ())⟩ fun vp1 =>
                Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 1, ())⟩ fun bpos =>
                Expr.store (Arg.var bpos.fst) (Arg.var vp1.fst)
                  (Expr.let_ ⟨OpCode.xor i32, (Arg.var other, Arg.imm 1, ())⟩ fun noth =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var noth.fst, ())⟩ fun no64 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var no64.fst, ())⟩ fun vp2 =>
                  Expr.let_ ⟨OpCode.neg i32, (Arg.imm 1, ())⟩ fun m1 =>
                  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.var m1.fst, ())⟩ fun bneg =>
                  Expr.store (Arg.var bneg.fst) (Arg.var vp2.fst)
                    (fidLpAssignTailExpr lvl rsns trl tpos flags phases rec_ph not_lit te un uf
                      tk2.fst p2 q2.fst di ov64.fst other alvlp.fst (some cref) J_lp)))
              Blocks.nil)
            (fun J_alvl =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ult i32, (Arg.var nl_lvl, Arg.var cur_lvl32, ())⟩
                fun lt =>
              Expr.jnz (Arg.var lt.fst)
                (m7LpMaxLvlExpr arena lvl cbase csz other J_alvl.fst)
                (Expr.jump J_alvl.fst (Arg.var nl_lvl, ())))))))

/-- Search-start normalization plus two-phase replacement scan and found/not-found dispatch. -/
@[expose] def fidLpScanExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr ignore_ref vals wstk arena lvl rsns trl tpos flags phases del dlim : V i64)
    (cur_lvl32 not_lit nl_lvl other cref : V i32) (ov : V i8) (rec_ph : V Ty.bool)
    (te un uf tk1 p2 q di brk0 cbase csz pos : V i64)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
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
                      (Expr.let_ ⟨OpCode.add i64, (Arg.var tk1, Arg.imm 1, ())⟩ fun tk2 =>
                      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64c =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var cr64c.fst, Arg.imm 1, ())⟩ fun psi2 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var psi2.fst, Arg.imm 4, ())⟩ fun pso2 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var pso2.fst, ())⟩
                        fun psp2 =>
                      Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var s2p.fst, ())⟩ fun ri32 =>
                      Expr.store (Arg.var ri32.fst) (Arg.var psp2.fst)
                        (fidLpReplDelExpr wstk arena del dlim not_lit other cref te un uf
                          tk2.fst p2 q di brk0 cbase s2p.fst s2p.snd.fst J_ovf J_lp))
                      (fidLpNoReplExpr hdr ignore_ref vals wstk arena lvl rsns trl tpos flags
                        phases cur_lvl32 not_lit nl_lvl other cref ov rec_ph te un uf tk1 p2 q
                        di cbase csz J_ovf J_lp))
                  Blocks.nil)
                (fun J_r2 =>
                  Expr.jnz (Arg.var s1p.snd.snd.fst)
                    (Expr.jump J_r2.fst (Arg.var s1p.fst, Arg.var s1p.snd.fst,
                      Arg.var s1p.snd.snd.fst, ()))
                    (Expr.group (sig := [[i64, i32, Ty.bool]])
                      (fun J_w => Blocks.cons
                        (fun wp => Expr.jump J_r2.fst (Arg.var wp.fst, Arg.var wp.snd.fst,
                          Arg.var wp.snd.snd.fst, ()))
                        Blocks.nil)
                      (fun J_w => m7LpReplScanExpr vals arena cbase st.fst (Arg.imm 2)
                        (Arg.var s1p.snd.fst) (Arg.var s1p.snd.snd.fst) J_w.fst))))
            Blocks.nil)
          (fun J_r1 =>
            m7LpReplScanExpr vals arena cbase csz (Arg.var st.fst) (Arg.imm 0) (Arg.imm false)
              J_r1.fst))
      Blocks.nil)
    (fun J_st =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var pos, Arg.imm 2, ())⟩ fun lt2 =>
      Expr.jnz (Arg.var lt2.fst)
        (Expr.jump J_st.fst (Arg.imm 2, ()))
        (Expr.let_ ⟨OpCode.cmp CmpOp.uge i64, (Arg.var pos, Arg.var csz, ())⟩ fun gec =>
        Expr.jnz (Arg.var gec.fst)
          (Expr.jump J_st.fst (Arg.imm 2, ()))
          (Expr.jump J_st.fst (Arg.var pos, ()))))

/-- Large-clause watch step (delayed-watch replacement, hoisted `nl_lvl`). -/
@[expose] def fidLpLargeStepExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr ignore_ref vals wstk arena lvl rsns trl tpos flags phases del dlim : V i64)
    (two_cv : V i64) (cur_lvl32 not_lit w0 nl_lvl : V i32) (rec_ph : V Ty.bool)
    (te un uf tk p q di brk0 : V i64)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64])
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
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
            Arg.var p2.fst, Arg.var q, Arg.var di, ()))
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
                          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q1.fst, ())⟩
                            fun qp1 =>
                          Expr.store (Arg.var cref) (Arg.var qp1.fst)
                            (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
                            Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf,
                              Arg.var tk1.fst, Arg.var p2.fst, Arg.var q2.fst, Arg.var di,
                              ()))))
                        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64a =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var cr64a.fst, Arg.imm 2, ())⟩ fun szi =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var szi.fst, Arg.imm 4, ())⟩ fun szo =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var szo.fst, ())⟩
                          fun szp =>
                        Expr.load i32 (Arg.var szp.fst) fun csz32 =>
                        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var csz32, ())⟩ fun csz =>
                        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64b =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var cr64b.fst, Arg.imm 1, ())⟩ fun psi =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var psi.fst, Arg.imm 4, ())⟩ fun pso =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var pso.fst, ())⟩
                          fun psp =>
                        Expr.load i32 (Arg.var psp.fst) fun pos32 =>
                        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var pos32, ())⟩ fun pos =>
                        fidLpScanExpr hdr ignore_ref vals wstk arena lvl rsns trl tpos flags
                          phases del dlim cur_lvl32 not_lit nl_lvl other.fst cref ov rec_ph
                          te un uf tk1.fst p2.fst q di brk0 cbase.fst csz.fst pos.fst J_ovf J_lp))
                    Blocks.nil)
                  (fun J_sw =>
                    Expr.let_ ⟨OpCode.cmp CmpOp.eq i32, (Arg.var l0, Arg.var not_lit, ())⟩
                      fun eq0 =>
                    Expr.jnz (Arg.var eq0.fst)
                      (Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase.fst, Arg.imm 4, ())⟩ fun ao0 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao0.fst, ())⟩ fun ap0 =>
                      Expr.store (Arg.var other.fst) (Arg.var ap0.fst)
                        (Expr.let_ ⟨OpCode.add i64, (Arg.var cbase.fst, Arg.imm 1, ())⟩
                          fun ci1 =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var ci1.fst, Arg.imm 4, ())⟩ fun ao1 =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var ao1.fst, ())⟩
                          fun ap1 =>
                        Expr.store (Arg.var not_lit) (Arg.var ap1.fst)
                          (Expr.jump J_sw.fst ())))
                      (Expr.jump J_sw.fst ())))
              Blocks.nil)
            (fun J_chk =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var l0, Arg.var not_lit, ())⟩ fun ne0 =>
              Expr.jnz (Arg.var ne0.fst)
                (Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var l1, Arg.var not_lit, ())⟩
                  fun ne1 =>
                Expr.jnz (Arg.var ne1.fst)
                  (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1.fst,
                    Arg.var p2.fst, Arg.var q, Arg.var di, ()))
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
                Arg.var p2.fst, Arg.var q2.fst, Arg.var di, ()))))
          (Expr.jump J_c.fst ()))
        (Expr.jump J_c.fst ()))

/-- Inner `while (p < end)` watch loop (state `(te, un, uf, tk, p, q, di)`). -/
@[expose] def fidLpLoopExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr ignore_ref vals wstk arena lvl rsns trl tpos flags phases del dlim : V i64)
    (two_cv : V i64) (cur_lvl32 not_lit nl_lvl : V i32) (rec_ph : V Ty.bool)
    (end0 brk0 te0 un0 uf0 tk0 p0 q0 di0 : V i64)
    (J_ovf : L [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]) :
    Expr V L rs :=
  Expr.group (sig := [[i64, i64, i64, i64, i64, i64, i64]])
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
            (fidLpBinStepExpr hdr vals wstk lvl rsns trl tpos flags phases rec_ph
              not_lit w0 nl_lvl lp.fst lp.snd.fst lp.snd.snd.fst lp.snd.snd.snd.fst
              lp.snd.snd.snd.snd.fst lp.snd.snd.snd.snd.snd.fst lp.snd.snd.snd.snd.snd.snd.fst
              J_ovf J_lp.fst)
            (fidLpLargeStepExpr hdr ignore_ref vals wstk arena lvl rsns trl tpos
              flags phases del dlim two_cv cur_lvl32 not_lit w0 nl_lvl rec_ph lp.fst
              lp.snd.fst lp.snd.snd.fst lp.snd.snd.snd.fst lp.snd.snd.snd.snd.fst
              lp.snd.snd.snd.snd.snd.fst lp.snd.snd.snd.snd.snd.snd.fst brk0 J_ovf J_lp.fst))
          (Expr.jump J_ovf (Arg.var lp.fst, Arg.var lp.snd.fst,
            Arg.var lp.snd.snd.fst, Arg.var lp.snd.snd.snd.fst,
            Arg.var lp.snd.snd.snd.snd.fst, Arg.var lp.snd.snd.snd.snd.snd.fst,
            Arg.var lp.snd.snd.snd.snd.snd.snd.fst,
            Arg.var brk0, Arg.imm false, Arg.imm 0, Arg.imm 0, Arg.imm 0,
            Arg.imm 0, ())))
      Blocks.nil)
    (fun J_lp =>
      Expr.jump J_lp.fst (Arg.var te0, Arg.var un0, Arg.var uf0, Arg.var tk0,
        Arg.var p0, Arg.var q0, Arg.var di0, ()))

/-! ## 2. Delayed-Buffer `PropLitInv` Rebase -/

/-- `PropLitInv` pins the scratch `delayed` buffer to that of its base state. -/
theorem fid_pi_delayed_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat}
    (h : PropLitInv c F0 F_cur s st not_lit off q p end_v) :
    st.scratch.delayed = s.scratch.delayed := by
  rw [h.sc_eq]

/-- Rebase a `PropLitInv` over a delayed-swapped base onto the post-state's own buffer. -/
theorem fid_pi_rebase {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_base st : FullState} {d : List (BitVec 32)} {not_lit off q p end_v : Nat}
    (h : PropLitInv c F0 F_cur { s_base with scratch := { s_base.scratch with delayed := d } }
      st not_lit off q p end_v) :
    PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := st.scratch.delayed } }
      st not_lit off q p end_v := by
  have hd : st.scratch.delayed = d := fid_pi_delayed_eq h
  rw [hd]; exact h

/-! ## 3. Inline Assignment Tail, Arena Swap, \& Binary Step -/


theorem fid_lp_assign_tail_wp {Γ : Env} {rs : List Ty} {c : FullCfg}
    {s_disk sem : FullState} {vals' : List (BitVec 8)} {not_lit new_lit alvl : BitVec 32}
    {rec_ph : Bool} {te un uf tk_next p_next q_next di_next v_idx : BitVec 64}
    {rsn_cref : Option (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen_sem : sem.LengthsOk c)
    (_hvals' : vals'.length = 2 * c.max_vars)
    (hte_lt : sem.core.trail_end < sem.core.cur_vars)
    (hte_eq : te.toNat = sem.core.trail_end)
    (hnew_lt : new_lit.toNat < 2 * sem.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hvidx : v_idx.toNat = new_lit.toNat / 2)
    (hm : (FullMem c { fastPropMem s_disk sem with
        core := { (fastPropMem s_disk sem).core with vals := vals' } } ⋆ R) m)
    (hJ : ∀ (flags' : List (BitVec 32)) (ph' : List (BitVec 8))
        (un_n uf_n : BitVec 64) (m' : Mem 64),
      flags'.length = c.max_vars → ph'.length = c.max_vars →
      let rsn_val := match rsn_cref with
        | none => (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
        | some cref => cref
      let sem' : FullState :=
        { core :=
            { sem.core with
              vals := vals', flags := flags'
              lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
              rsns := sem.core.rsns.set (new_lit.toNat / 2)
                (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_val)
              trl := sem.core.trl.set sem.core.trail_end new_lit
              trail_pos := sem.core.trail_pos.set (new_lit.toNat / 2)
                (BitVec.ofNat 32 sem.core.trail_end)
              trail_end := sem.core.trail_end + 1
              unassigned := un_n, unflushed := uf_n }
          scratch := { sem.scratch with phases := ph' } }
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var (te + 1#64), (.var un_n, (.var uf_n,
        (.var tk_next, (.var p_next, (.var q_next, (.var di_next, ())))))))) m') :
    wp Γ Q X (fidLpAssignTailExpr c.pLevel c.pReason c.pTrail c.pTrailPos c.pFlags c.pPhases
      rec_ph not_lit te un uf tk_next p_next q_next di_next v_idx new_lit alvl rsn_cref J_lp) m :=
    by
  unfold dimacsBound at hmaxv
  have hcv := hlen_sem.core_ok.cur_vars_le
  have hfl_len := hlen_sem.core_ok.flags_len
  have hph_len := hlen_sem.scratch_ok.phases_len
  have hlvl_len := hlen_sem.core_ok.lvl_len
  have hrsn_len := hlen_sem.core_ok.rsns_len
  have htp_len := hlen_sem.core_ok.trail_pos_len
  have htrl_len := hlen_sem.core_ok.trl_len
  have hv_mv : new_lit.toNat / 2 < c.max_vars := by omega
  have hte_mv : sem.core.trail_end < c.max_vars := by omega
  have h2cv_31 : not_lit.toNat < 2 ^ 31 := by omega
  have hm_v : (FullMem c (fastPropMem s_disk { sem with
      core := { sem.core with vals := vals' } }) ⋆ R) m := by
    simpa only [m7_fastPropMem_with_vals] using hm
  have htpos32 : te.setWidth 32 = BitVec.ofNat 32 sem.core.trail_end := by
    apply BitVec.eq_of_toNat_eq
    have hte32 : sem.core.trail_end < 2 ^ 32 := by omega
    rw [BitVec.toNat_setWidth, hte_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte32]
  unfold fidLpAssignTailExpr
  refine wp_join_group (fun (un_n, ()) mu => mu = m) ?_ ?_
  · rintro _ ⟨un_n, ⟨⟩⟩ mu hmu
    dsimp only at hmu
    rw [hmu]
    clear hmu
    refine wp_join_group (fun _ mph => ∃ ph' : List (BitVec 8), ph'.length = c.max_vars ∧
        (FullMem c (fastPropMem s_disk { sem with
          core := { sem.core with vals := vals' }
          scratch := { sem.scratch with phases := ph' } }) ⋆ R) mph) ?_ ?_
    · rintro _ ⟨⟩ mph ⟨ph', hph', hmph⟩
      have hlvl_m : (fastPropMem s_disk { sem with
          core := { sem.core with vals := vals' }
          scratch := { sem.scratch with phases := ph' } }).core.lvl.length =
          c.max_vars := by
        rw [fastPropMem_lvl]; exact hlvl_len
      fid_hsteps_nogrp
      have hml : (FullMem c (fastPropMem s_disk { sem with
          core :=
            { sem.core with
              vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl }
          scratch := { sem.scratch with phases := ph' } }) ⋆ R) m := by
        simpa only [fastPropMem_lvl, hvidx, m7_fastPropMem_with_lvl] using hm
      clear hm
      let rsn_v : BitVec 32 := match rsn_cref with
        | none => (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
        | some cref => cref
      have hrsn_bin : 2147483648#32 ||| not_lit =
          (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32 := by
        rw [m7_bv32_mask7f_eq h2cv_31, BitVec.or_comm]
      refine wp_join_group (fun (uf_n, ()) maf =>
          ∃ flags' : List (BitVec 32), flags'.length = c.max_vars ∧
          (FullMem c (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v) }
            scratch := { sem.scratch with phases := ph' } }) ⋆ R) maf) ?_ ?_
      · rintro _ ⟨uf_n, ⟨⟩⟩ maf ⟨flags', hfl', hmaf⟩
        have htp_m : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v) }
            scratch := { sem.scratch with phases := ph' } }).core.trail_pos.length =
            c.max_vars := by
          rw [fastPropMem_trail_pos]; exact htp_len
        have htrl_m : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v)
                trail_pos := sem.core.trail_pos.set (new_lit.toNat / 2)
                  (BitVec.ofNat 32 sem.core.trail_end) }
            scratch := { sem.scratch with phases := ph' } }).core.trl.length =
            c.max_vars := by
          rw [fastPropMem_trl]; exact htrl_len
        fid_hsteps
        refine wp_store_sep (FullArenaTactics.c0_store_full_trl new_lit
          (by rw [fastPropMem_trl, hte_eq, htrl_len]; exact hte_mv) hm) ?_
        intro mtr hmtr'; clear hm
        fid_hsteps
        have hmtr :
            (FullMem c (fastPropMem s_disk {
              core :=
                { sem.core with
                  vals := vals', flags := flags'
                  lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                  rsns := sem.core.rsns.set (new_lit.toNat / 2)
                    (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v)
                  trl := sem.core.trl.set sem.core.trail_end new_lit
                  trail_pos := sem.core.trail_pos.set (new_lit.toNat / 2)
                    (BitVec.ofNat 32 sem.core.trail_end)
                  trail_end := sem.core.trail_end + 1
                  unassigned := un_n, unflushed := uf_n }
              scratch := { sem.scratch with phases := ph' } }) ⋆ R) mtr := by
          refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) mtr) ?_) hmtr'
          unfold fastPropMem
          dsimp only
          simp only [hvidx, htpos32, hte_eq]
        rcases rsn_cref with _ | rsn_c <;> dsimp only [rsn_v] at hmtr
        · exact hJ flags' ph' un_n uf_n mtr hfl' hph' hmtr
        · exact hJ flags' ph' un_n uf_n mtr hfl' hph' hmtr
      · intro Junfl hJunfl
        have hrsn_m : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl }
            scratch := { sem.scratch with phases := ph' } }).core.rsns.length =
            c.max_vars := by
          rw [fastPropMem_rsns]; exact hrsn_len
        have hfl_m' : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set v_idx.toNat 0xFFFFFFFF#32 }
            scratch := { sem.scratch with phases := ph' } }).core.flags.length =
            c.max_vars := by
          rw [fastPropMem_flags]; exact hfl_len
        fid_hsplit
        · have hal0 : alvl = 0#32 := hc
          fid_hsteps_nogrp
          simp only [fastPropMem_rsns, m7_fastPropMem_with_rsns] at hm
          fid_hsteps
          refine hJunfl (uf + 1#64, ()) m
            ⟨sem.core.flags.set (new_lit.toNat / 2) ?fv_al0,
              by rw [List.length_set, hfl_len], ?hm_al0⟩
          case hm_al0 =>
            rw [show (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v) = 0xFFFFFFFF#32 from
              by simp only [hal0, ↓reduceIte]]
            refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) m) ?_) hm
            unfold fastPropMem; dsimp only; simp only [hvidx]; rfl
        · have hal_ne0 : alvl ≠ 0#32 := hc
          cases rsn_cref with
          | none =>
            fid_hsteps
            have hrsn_bin' : BitVec.ofNat 32 2147483648 ||| not_lit =
                (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32 := hrsn_bin
            have hmrs : (FullMem c (fastPropMem s_disk { sem with
                core :=
                  { sem.core with
                    vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                    rsns := sem.core.rsns.set (new_lit.toNat / 2)
                      ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) }
                scratch := { sem.scratch with phases := ph' } }) ⋆ R) m := by
              refine Eq.mp ?_ hm
              congr 2
              unfold fastPropMem
              simp only [hvidx, show (2147483648 : BitVec 32) ||| not_lit =
                (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32 from hrsn_bin']
            exact hJunfl (uf, ()) m ⟨sem.core.flags, hfl_len, by
              simpa only [hal_ne0, ↓reduceIte, rsn_v] using hmrs⟩
          | some cref =>
            fid_hsteps
            have hmrs : (FullMem c (fastPropMem s_disk { sem with
                core :=
                  { sem.core with
                    vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                    rsns := sem.core.rsns.set (new_lit.toNat / 2) cref }
                scratch := { sem.scratch with phases := ph' } }) ⋆ R) m := by
              simpa only [fastPropMem_rsns, hvidx, m7_fastPropMem_with_rsns] using hm
            exact hJunfl (uf, ()) m ⟨sem.core.flags, hfl_len, by
              simpa only [hal_ne0, ↓reduceIte, rsn_v] using hmrs⟩
    · intro Jph hJph
      have hph_m : (fastPropMem s_disk { sem with
          core := { sem.core with vals := vals' } }).scratch.phases.length = c.max_vars := by
        rw [fastPropMem_phases]; exact hph_len
      fid_hsplit
      · refine wp_join_group (fun _ mph => ∃ ph' : List (BitVec 8), ph'.length = c.max_vars ∧
            (FullMem c (fastPropMem s_disk { sem with
              core := { sem.core with vals := vals' }
              scratch := { sem.scratch with phases := ph' } }) ⋆ R) mph) ?_ ?_
        · rintro _ ⟨⟩ mph ⟨ph', hph', hmph⟩
          fid_hsteps
          exact hJph () mph ⟨ph', hph', hmph⟩
        · intro Jp2 hJp2
          fid_hsplit
          · fid_hsteps
            rw [fastPropMem_phases, hvidx, m7_fastPropMem_with_phases] at hm
            exact hJp2 () m ⟨_, by rw [List.length_set, hph_len], hm⟩
          · fid_hsteps
            rw [fastPropMem_phases, hvidx, m7_fastPropMem_with_phases] at hm
            exact hJp2 () m ⟨_, by rw [List.length_set, hph_len], hm⟩
      · fid_hsteps
        exact hJph () m ⟨sem.scratch.phases, hph_len, hm_v⟩
  · intro Jun hJun
    have hfl_m : (fastPropMem s_disk { sem with
        core := { sem.core with vals := vals' } }).core.flags.length = c.max_vars := by
      rw [fastPropMem_flags]; exact hfl_len
    fid_hsteps
    · exact hJun (un - 1#64, ()) m rfl
    · exact hJun (un, ()) m rfl
    · exact hJun (un, ()) m rfl

private theorem fid_lp_ar_swap_wp0 {Γ : Env} {rs : List Ty} {c : FullCfg}
    {s_disk sem1 : FullState} {not_lit other repl : BitVec 32} {cbase ri : BitVec 64}
    {cref : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {k : Expr Val Cont rs}
    (haren1 : sem1.core.arena.length = c.arena_cap)
    (hc0 : cbase.toNat = cref + 3) (hc1 : (cbase + 1#64).toNat = cref + 4)
    (hcri : (cbase + ri).toNat = cref + 3 + ri.toNat)
    (h0_lt : cref + 3 < c.arena_cap) (h1_lt : cref + 4 < c.arena_cap)
    (hri_lt : cref + 3 + ri.toNat < c.arena_cap)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hk : ∀ m3,
      let ar3 := ((sem1.core.arena.set (cref + 3) other).set (cref + 4) repl).set
        (cref + 3 + ri.toNat) not_lit
      (FullMem c (fastPropMem s_disk { sem1 with core := { sem1.core with arena := ar3 } }) ⋆
        R) m3 →
      wp Γ Q X k m3) :
    wp Γ Q X
      (.let_ (Op.mk (.mul i64) (.var cbase, (.imm 4#64, ()))) fun o0 =>
       .let_ (Op.mk (.add i64) (.var c.pArena, (.var o0.1, ()))) fun a0 =>
       .store (Arg.var (t := i32) other) (.var a0.1)
         (.let_ (Op.mk (.add i64) (.var cbase, (.imm 1#64, ()))) fun i1 =>
          .let_ (Op.mk (.mul i64) (.var i1.1, (.imm 4#64, ()))) fun o1 =>
          .let_ (Op.mk (.add i64) (.var c.pArena, (.var o1.1, ()))) fun a1 =>
          .store (Arg.var (t := i32) repl) (.var a1.1)
            (.let_ (Op.mk (.add i64) (.var cbase, (.var ri, ()))) fun ir =>
             .let_ (Op.mk (.mul i64) (.var ir.1, (.imm 4#64, ()))) fun or1 =>
             .let_ (Op.mk (.add i64) (.var c.pArena, (.var or1.1, ()))) fun ar1 =>
             .store (Arg.var (t := i32) not_lit) (.var ar1.1) k))) m := by
  have hm_ar : (fastPropMem s_disk sem1).core.arena.length = c.arena_cap := by
    rw [fastPropMem_arena]; exact haren1
  fid_hsteps_nogrp
  refine wp_store_sep (FullArenaTactics.c0_store_full_arena other
    (by rw [hm_ar, hc0]; exact h0_lt) hm) ?_
  intro m1 hm1; clear hm; dsimp only at hm1
  rw [hc0, fastPropMem_with_arena, fastPropMem_arena] at hm1
  fid_hsteps_nogrp
  have hm1_ar : (fastPropMem s_disk { sem1 with core :=
      { sem1.core with arena := sem1.core.arena.set (cref + 3) other } }).core.arena.length =
      c.arena_cap := by
    rw [fastPropMem_arena, List.length_set]; exact haren1
  refine wp_store_sep (FullArenaTactics.c0_store_full_arena repl
    (by rw [hm1_ar, hc1]; exact h1_lt) hm1) ?_
  intro m2 hm2; clear hm1; dsimp only at hm2
  rw [hc1, fastPropMem_with_arena, fastPropMem_arena] at hm2
  fid_hsteps_nogrp
  let sem_ar2 : FullState := { sem1 with core :=
    { sem1.core with arena := (sem1.core.arena.set (cref + 3) other).set (cref + 4) repl } }
  have hm2_ar : (fastPropMem s_disk sem_ar2).core.arena.length = c.arena_cap := by
    rw [fastPropMem_arena, List.length_set, List.length_set]; exact haren1
  refine wp_store_sep (FullArenaTactics.c0_store_full_arena not_lit
    (by rw [hm2_ar, hcri]; exact hri_lt) hm2) ?_
  intro m3 hm3; clear hm2; dsimp only at hm3
  rw [hcri, fastPropMem_with_arena, fastPropMem_arena] at hm3
  exact hk m3 hm3

theorem fid_lp_ar_swap_wp {Γ : Env} {rs : List Ty} {c : FullCfg}
    {s_disk sem1 : FullState} {not_lit other repl : BitVec 32} {cbase ri : BitVec 64}
    {cref : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {k : Expr Val Cont rs}
    (haren1 : sem1.core.arena.length = c.arena_cap)
    (hc0 : cbase.toNat = cref + 3) (hc1 : (cbase + 1#64).toNat = cref + 4)
    (hcri : (cbase + ri).toNat = cref + 3 + ri.toNat)
    (h0_lt : cref + 3 < c.arena_cap) (h1_lt : cref + 4 < c.arena_cap)
    (hri_lt : cref + 3 + ri.toNat < c.arena_cap)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hk : ∀ m3,
      let ar3 := ((sem1.core.arena.set (cref + 3) other).set (cref + 4) repl).set
        (cref + 3 + ri.toNat) not_lit
      (FullMem c (fastPropMem s_disk { sem1 with core := { sem1.core with arena := ar3 } }) ⋆
        R) m3 →
      wp Γ Q X k m3) :
    wp Γ Q X (fidLpArSwapExpr c.pArena not_lit other repl cbase ri k) m :=
  fid_lp_ar_swap_wp0 haren1 hc0 hc1 hcri h0_lt h1_lt hri_lt hm hk

private theorem fid_bv8_sgt0_iff (x : BitVec 8) :
    (0#32).slt (BitVec.signExtend 32 x) =
      decide ((BitVec.signExtend 32 x).toInt > 0) := by
  rw [BitVec.slt_eq_decide, show (0#32 : BitVec 32).toInt = 0 from by decide]

private theorem fid_bv8_slt0_iff (x : BitVec 8) :
    (BitVec.signExtend 32 x).slt 0#32 =
      decide ((BitVec.signExtend 32 x).toInt < 0) := by
  rw [BitVec.slt_eq_decide, show (0#32 : BitVec 32).toInt = 0 from by decide]

theorem fid_xor_cancel_l (a b : BitVec 32) : a ^^^ b ^^^ a = b := by
  rw [BitVec.xor_comm a b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem fid_xor_cancel_r (a b : BitVec 32) : a ^^^ b ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem fid_fastPropMem_with_bin_confl (s0 sem : FullState) (l0 l1 : BitVec 64) :
    { fastPropMem s0 sem with
      core :=
        { (fastPropMem s0 sem).core with
          confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1 } } =
      fastPropMem s0 { sem with
        core := { sem.core with confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1 } } := by
  unfold fastPropMem; rfl

theorem fid_fastPropMem_with_wstk_large_confl (s0 sem : FullState)
    (ws : List (BitVec 32)) (cr : BitVec 64) :
    { fastPropMem s0 sem with
      core :=
        { (fastPropMem s0 sem).core with
          confl_ref := cr, confl_type := 2#64, wstk := ws } } =
      fastPropMem s0 { sem with
        core := { sem.core with confl_ref := cr, confl_type := 2#64, wstk := ws } } := by
  unfold fastPropMem; rfl

theorem fid_lp_bin_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_base s_disk sem : FullState} {not_lit w0 nl_lvl : BitVec 32}
    {te un uf tk p q di end_v off_v ignore_ref : BitVec 64} {rec_ph : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hwc : c.wcap < 2 * dimacsBound)
    (hpi : PropLitInv c F0 F_cur s_base sem not_lit.toNat off_v.toNat q.toNat p.toNat end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hp_lt : p.toNat < end_v.toNat)
    (hw0_get : sem.core.wstk[p.toNat]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hte_eq : te.toNat = sem.core.trail_end)
    (hun_eq : un = sem.core.unassigned) (huf_eq : uf = sem.core.unflushed)
    (hoom : sem.core.oom = 0#64)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ_ovf : ∀ {sem' : FullState} {p' q' brk' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur s_base sem' not_lit.toNat off_v.toNat q'.toNat p'.toNat end_v.toNat →
      p.toNat ≤ p'.toNat → te.toNat = sem'.core.trail_end → sem'.core.oom = 0#64 →
      sem'.core.unassigned = sem.core.unassigned → sem'.core.unflushed = sem.core.unflushed →
      brk' = 1#64 → PropLitConfl F_cur ignore_ref sem'.core →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_ovf (.var te, (.var un, (.var uf, (.var tk, (.var p', (.var q',
        (.var di, (.var brk', (.imm false, (.imm 0#32, (.imm 0#32, (.imm 0#32,
        (.imm 0#64, ()))))))))))))))
        m')
    (hJ_lp : ∀ {sem' : FullState} {te' un' uf' tk' p' q' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur s_base sem' not_lit.toNat off_v.toNat q'.toNat p'.toNat end_v.toNat →
      p.toNat < p'.toNat → p'.toNat ≤ end_v.toNat →
      sem.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned → uf' = sem'.core.unflushed →
      sem'.core.oom = sem.core.oom → sem'.core.confl_type = sem.core.confl_type →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var te', (.var un', (.var uf', (.var tk', (.var p', (.var q',
        (.var di, ())))))))) m') :
    wp Γ Q X (fidLpBinStepExpr c.hdr c.pVals c.pWstk c.pLevel c.pReason c.pTrail c.pTrailPos
      c.pFlags c.pPhases rec_ph not_lit w0 nl_lvl te un uf tk p q di J_ovf J_lp) m := by
  unfold dimacsBound at hmaxv hwc
  have hcv := hpi.len.core_ok.cur_vars_le
  have hfl_len := hpi.len.core_ok.flags_len
  have hph_len := hpi.len.scratch_ok.phases_len
  have hvals_len := hpi.len.core_ok.vals_len
  have hlvl_len := hpi.len.core_ok.lvl_len
  have hwstk_len := hpi.len.core_ok.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hp_rem_pos : 0 < end_v.toNat - p.toNat := Nat.sub_pos_of_lt hp_lt
  have hp1_n : (p + 1#64).toNat = p.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hq1_n : (q + 1#64).toNat = q.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hq_lt_ws : q.toNat < sem.core.wstk.length := by rw [hwstk_len]; omega
  obtain ⟨hother_lt, hent, hrem1⟩ :=
    watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
  have hsw1 := (hpi.sw.advance_rem (p' := p.toNat + 1) (Nat.le_succ _) hp_lt
    (by simpa [Nat.sub_sub] using hrem1)).write_bin
    (c := c) hcv hnot_lt hq_le hq_lt_ws hflag hother_lt hent
  let blk := w0 &&& 2147483647#32
  have hblk_eq : blk = w0 &&& 0x7FFFFFFF#32 := rfl
  let wstk1 := sem.core.wstk.set q.toNat w0
  let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
  have hlen1 : sem1.LengthsOk c :=
    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
     hpi.len.scratch_ok⟩
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
    fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hblk_vals_m : (blk.setWidth 64).toNat < (fastPropMem s_disk sem).core.vals.length := by
    rw [fastPropMem_vals, hvals_len, bv_c0_zext32_64, hblk_eq]; omega
  have hblk_vals_raw : blk.toNat < sem.core.vals.length := by rw [hvals_len, hblk_eq]; omega
  have hm_ws : q.toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [fastPropMem_wstk]; exact hq_lt_ws
  let vb := (fastPropMem s_disk sem).core.vals[blk.toNat]'(by
    rw [← bv_c0_zext32_64 blk]; exact hblk_vals_m)
  have hvb_eq : vb = sem.core.vals[blk.toNat]'hblk_vals_raw :=
    (fc_getElem_vals s_disk sem).trans (fc_getElem_eq_of_idx rfl _ hblk_vals_raw)
  have hvb_1 : vb = sem1.core.vals[blk.toNat]'(by simp [sem1]; exact hblk_vals_raw) := hvb_eq
  have hpi1 : PropLitInv c F0 F_cur s_base sem1 not_lit.toNat off_v.toNat
      (q + 1#64).toNat (p + 1#64).toNat end_v.toNat := by
    rw [hq1_n, hp1_n]
    exact ⟨hlen1, hnw1, hsw1, hpi.ag.update (fun k => { k with wstk := wstk1 }),
      hpi.tr.congr rfl rfl rfl, hpi.perm, hpi.sc_eq, hpi.not_f⟩
  have hp1_n' : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := hp1_n
  unfold fidLpBinStepExpr
  fid_hsplit
  · rw [fastPropMem_with_wstk, fastPropMem_wstk] at hm
    fid_hsteps
    exact hJ_lp hpi1 (by rw [hp1_n']; omega) (by rw [hp1_n']; omega) (Nat.le_refl _) hte_eq
      hun_eq huf_eq rfl rfl hm
  · rw [fastPropMem_with_wstk, fastPropMem_wstk] at hm
    have hnsgt : (0#32).slt (BitVec.signExtend 32 vb) = false := by
      simpa only [vb, blk, show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
        show (0 : BitVec 32) = 0#32 from rfl] using hc
    fid_hsplit
    · have hslt : (BitVec.signExtend 32 vb).slt 0#32 = true := by
        simpa only [vb, blk, show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
          show (0 : BitVec 32) = 0#32 from rfl] using hc
      have hov_f : sem.core.vals[blk.toNat]?.getD 0#8 = 0xFF#8 :=
        propLit_vals_neg hpi.nw hother_lt hblk_vals_raw (by rw [← hvb_eq]; exact hslt)
      have ⟨hpi_c, hcf_c⟩ := propLit_bin_confl (ignore_ref := ignore_ref) hpi hsw1
        hnot_lt hother_lt hent hov_f hp1_n hq1_n
      let sem_c : FullState :=
        { sem with core := { sem.core with
          wstk := wstk1, confl_type := 1#64, confl_lit0 := not_lit.setWidth 64,
          confl_lit1 := blk.setWidth 64 } }
      have hpi_c' : PropLitInv c F0 F_cur s_base sem_c not_lit.toNat off_v.toNat
          (q + 1#64).toNat (p + 1#64).toNat end_v.toNat := by
        have hlen_c : sem_c.LengthsOk c :=
          ⟨{ hpi_c.len.core_ok with wstk_len_arr := by simp [sem_c, wstk1, hwstk_len] },
           hpi_c.len.scratch_ok⟩
        exact ⟨hlen_c,
          fullWitnessInv_nw_congr hlen_c.core_ok.cur_vars_le hpi_c.nw rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl,
          hpi_c.sw.with_nonwatch rfl rfl rfl rfl rfl,
          hpi.ag.update (fun k => { k with
            wstk := wstk1, confl_type := 1#64, confl_lit0 := not_lit.setWidth 64,
            confl_lit1 := blk.setWidth 64 }),
          hpi_c.tr.congr rfl rfl rfl, hpi_c.perm, hpi_c.sc_eq, hpi_c.not_f⟩
      have hcf_c' : PropLitConfl F_cur ignore_ref sem_c.core := by
        rcases hcf_c with hbad | ⟨h1 | h2, _⟩
        · exact Or.inl hbad
        · exact Or.inr ⟨Or.inl h1, fun hc2 => by change (1#64) = 2#64 at hc2; cases hc2⟩
        · exfalso; have ht2 := h2.1; dsimp only at ht2; cases ht2
      fid_hsteps
      exact hJ_ovf hpi_c' (by rw [hp1_n']; omega) hte_eq hoom rfl rfl rfl hcf_c'
        (by
          simpa only [sem_c, sem1, fid_fastPropMem_with_bin_confl,
            show (1 : BitVec 64) = 1#64 from rfl,
            show (2147483647 : BitVec 32) = 2147483647#32 from rfl] using hm)
    · have hnslt : (BitVec.signExtend 32 vb).slt 0#32 = false := by
        simpa only [vb, blk, show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
          show (0 : BitVec 32) = 0#32 from rfl] using hc
      have hov_un : sem1.core.vals[blk.toNat]?.getD 0#8 = 0#8 :=
        propLit_vals_un hnw1 hother_lt (by simp [sem1]; exact hblk_vals_raw)
          (by rw [← hvb_1]; exact hnsgt) (by rw [← hvb_1]; exact hnslt)
      have hte_lt : sem1.core.trail_end < sem1.core.cur_vars :=
        m7_trail_end_lt_of_unassigned hnw1 hother_lt hov_un
      fid_hsteps_nogrp
      have hblk_m : (blk.setWidth 64).toNat < (fastPropMem s_disk sem1).core.vals.length := by
        rw [fastPropMem_vals, hvals_len, bv_c0_zext32_64, hblk_eq]; omega
      refine wp_store_sep (FullArenaTactics.c0_store_full_vals ((1#32).setWidth 8) hblk_m hm) ?_
      intro mv1 hmv1; clear hm; dsimp only at hmv1
      rw [bv_c0_zext32_64, fastPropMem_vals, show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
        show BitVec.setWidth 8 (1#32) = 1#8 from rfl, m7_fastPropMem_with_vals] at hmv1
      fid_hsteps_nogrp
      have hnblk_m : ((blk ^^^ 1#32).setWidth 64).toNat <
          (fastPropMem s_disk { sem1 with core :=
            { sem1.core with vals := sem1.core.vals.set blk.toNat 1#8 } }).core.vals.length := by
        rw [fastPropMem_vals, List.length_set, hvals_len, bv_c0_zext32_64, BitVec.toNat_xor,
          show (1#32 : BitVec 32).toNat = 1 from rfl, fc_nat_xor_one, hblk_eq]
        split <;> omega
      refine wp_store_sep (FullArenaTactics.c0_store_full_vals ((-1#32).setWidth 8) hnblk_m hmv1)
        ?_
      intro mv2 hmv2; clear hmv1; dsimp only at hmv2
      have hnblk_n : ((blk ^^^ 1#32).setWidth 64).toNat = blk.toNat ^^^ 1 := by
        rw [bv_c0_zext32_64, BitVec.toNat_xor]; rfl
      have hm1_8 : (-1#32 : BitVec 32).setWidth 8 = 0xFF#8 := by decide
      rw [show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
        show (1 : BitVec 32) = 1#32 from rfl,
        show (w0 &&& 2147483647#32) ^^^ 1#32 = blk ^^^ 1#32 from rfl,
        hnblk_n, hm1_8, fastPropMem_vals, m7_fastPropMem_with_vals] at hmv2
      let vals' := (sem1.core.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 0xFF#8
      have hvals'_len : vals'.length = 2 * c.max_vars := by
        simpa [vals', List.length_set, sem1] using hvals_len
      fid_hsteps_nogrp
      refine fid_lp_assign_tail_wp hmaxv hlen1 hvals'_len hte_lt hte_eq hother_lt hnot_lt
        (m7_bv32_rshift1_toNat blk) (by simpa only [← m7_fastPropMem_with_vals] using hmv2) ?_
      intro flags' ph' un_n uf_n m' hfl' hph' _rsn_val sem_n hm'
      have hws1_len : sem1.core.wstk.length = c.wcap := by
        simpa [sem1, wstk1, List.length_set] using hwstk_len
      have hstep := m7_bin_assign_step hpi hsw1 hws1_len hfl' hph' hnot_lt hother_lt hov_un
        (by simpa [sem1] using hnl) hent hp1_n hq1_n (unas' := un_n) (unfl' := uf_n)
      have hte_lt' : sem.core.trail_end < sem.core.cur_vars := hte_lt
      have hcv_le := hpi.len.core_ok.cur_vars_le
      have hte1_n : (te + 1#64).toNat = sem.core.trail_end + 1 := by
        rw [m7_bv64_add1_toNat (by rw [hte_eq]; omega), hte_eq]
      have hte_le_inc : sem.core.trail_end ≤ sem.core.trail_end + 1 := Nat.le_succ _
      have hq1_n' : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := hq1_n
      have hinv_n := hstep.1
      rw [hq1_n, hp1_n] at hinv_n
      exact hJ_lp (sem' := sem_n) (by dsimp only; rw [hq1_n', hp1_n']; exact hinv_n)
        (by dsimp only; rw [hp1_n']; omega) (by dsimp only; rw [hp1_n']; omega)
        hte_le_inc hte1_n rfl rfl rfl rfl hm'

end LeanQbe.T.Examples.Kissat.FullFidelityBcp
