/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reorder
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.WpMem
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Wp0
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proofs for `Src.Reorder` Part 1 (`Proof.Reorder.Wp1`)

Sub-expression projections of `full_reorder_queue_m7_body` and the stable-mode reorder branch
proofs (`reorder_sift_inner_wp` and `reorder_stable_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reorder

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Reorder
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Reorder.ReorderTactics
open Kraken.Bedrock2.Test

/-! ## 1. Sub-Expression Projections of `full_reorder_queue_m7_body` -/

@[expose] def rDummyVal : (t : Ty) → Val t
  | .bool => false
  | .bits n => BitVec.zero n
  | .float f => BitVec.zero f.width
  | .pair a b => (rDummyVal a, rDummyVal b)

@[expose] def rDummyTup : (ts : List Ty) → Tup Val ts
  | [] => ()
  | t :: ts => (rDummyVal t, rDummyTup ts)

@[expose] def rSkipLets {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | fuel + 1, .let_ (ts := ts) _ k => rSkipLets fuel (k (rDummyTup ts))
  | _, e => e

@[expose] def rSkip {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | fuel + 1, .let_ (ts := ts) _ k => rSkip fuel (k (rDummyTup ts))
  | fuel + 1, .load t _ k => rSkip fuel (k (rDummyVal t))
  | _, e => e

@[expose] def rLoad64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v
  | _ => .hlt

@[expose] def rLet64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 64]) _ k => k (v, ())
  | _ => .hlt

@[expose] def rGrp1Exit {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64]]) bodies _ =>
    match bodies (fun _ _ => False, ()) with
    | .cons f .nil => f (0#64, ())
  | _ => .hlt

@[expose] def rElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e
  | _ => .hlt

@[expose] def rNextLoad64 {rs : List Ty} (v : Val i64) (e : Expr Val Cont rs) :
    Expr Val Cont rs :=
  rLoad64 v (rSkipLets 10 e)

@[expose] def rNextLoad64Let64 {rs : List Ty} (v lv : Val i64) (e : Expr Val Cont rs) :
    Expr Val Cont rs :=
  rLet64 lv (rSkipLets 1 (rNextLoad64 v e))

@[expose] def rSkipWhile1 {rs : List Ty} (e : Expr Val Cont rs) : Expr Val Cont rs :=
  rElse (rSkip 16 (rGrp1Exit (rSkip 16 e)))

@[expose] def rLoop34Expr (h cv nlits wlen vl fl wvec wstk ws qp qn qs wl wr : Val i64) :
    Expr Val Cont [i64] :=
  full_reorder_queue_m7_body Val Cont (h, ())
    |> rNextLoad64Let64 cv nlits
    |> rNextLoad64 0#64 |> rNextLoad64 wlen |> rNextLoad64 vl
    |> rNextLoad64 fl
    |> rNextLoad64 0#64 |> rNextLoad64 wvec |> rNextLoad64 wstk
    |> rNextLoad64 ws |> rNextLoad64 qp |> rNextLoad64 qn |> rNextLoad64 qs
    |> rNextLoad64 wl |> rNextLoad64 wr
    |> rSkipWhile1
    |> (fun e => rGrp1Exit (rSkip 16 e))

@[expose] def rSiftInnerExpr {V : Ty → Type} {C : List Ty → Type}
    (pWs pWl pSc bound : V i64) (B L : C [i64]) (root : V i64) : Expr V C [i64] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .jnz (.imm true)
    (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun s1 =>
     .let_ (op64 (.shl i64) (.var root) (.var s1.fst)) fun s2 =>
     .let_ (op64 (.add i64) (.var s2.fst) (.imm 1)) fun ch =>
     .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var ch.fst, .var bound, ())) fun c0 =>
     .jnz (.var c0.fst) (.jump B (.var root, ()))
       (.let_ (op64 (.mul i64) (.var root) (.imm 4)) fun a1 =>
        .let_ (op64 (.add i64) (.var pWs) (.var a1.fst)) fun a2 =>
        .load i32 (.var a2.fst) fun bv =>
        .let_ (Op.mk (.zext 32 64) (.var bv, ())) fun a3 =>
        .let_ (op64 (.mul i64) (.var a3.fst) (.imm 8)) fun a4 =>
        .let_ (op64 (.add i64) (.var pWl) (.var a4.fst)) fun a5 =>
        .load i64 (.var a5.fst) fun bw =>
        .let_ (Op.mk (.zext 32 64) (.var bv, ())) fun a6 =>
        .let_ (op64 (.mul i64) (.var a6.fst) (.imm 8)) fun a7 =>
        .let_ (op64 (.add i64) (.var pSc) (.var a7.fst)) fun a8 =>
        .load i64 (.var a8.fst) fun bs =>
        .let_ (op64 (.mul i64) (.var ch.fst) (.imm 4)) fun b1 =>
        .let_ (op64 (.add i64) (.var pWs) (.var b1.fst)) fun b2 =>
        .load i32 (.var b2.fst) fun cv1 =>
        .let_ (Op.mk (.zext 32 64) (.var cv1, ())) fun b3 =>
        .let_ (op64 (.mul i64) (.var b3.fst) (.imm 8)) fun b4 =>
        .let_ (op64 (.add i64) (.var pWl) (.var b4.fst)) fun b5 =>
        .load i64 (.var b5.fst) fun cw =>
        .let_ (Op.mk (.zext 32 64) (.var cv1, ())) fun b6 =>
        .let_ (op64 (.mul i64) (.var b6.fst) (.imm 8)) fun b7 =>
        .let_ (op64 (.add i64) (.var pSc) (.var b7.fst)) fun b8 =>
        .load i64 (.var b8.fst) fun cs =>
        .group (sig := [[i64, i32, i64, i64]]) (fun _ =>
          .cons (fun (xs : Tup V [i64, i32, i64, i64]) =>
            let best1 := xs.fst; let bv1 := xs.snd.fst
            let bw1 := xs.snd.snd.fst; let bs1 := xs.snd.snd.snd.fst
            .let_ (op64 (.add i64) (.var ch.fst) (.imm 1)) fun rch =>
            .group (sig := [[i64, i32]]) (fun _ =>
              .cons (fun (ys : Tup V [i64, i32]) =>
                let best2 := ys.fst; let bv2 := ys.snd.fst
                .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var best2, .var root, ())) fun eqr =>
                .jnz (.var eqr.fst) (.jump B (.var root, ()))
                  (.let_ (op64 (.mul i64) (.var root) (.imm 4)) fun t1 =>
                   .let_ (op64 (.add i64) (.var pWs) (.var t1.fst)) fun t2 =>
                   .load i32 (.var t2.fst) fun tv =>
                   .let_ (op64 (.mul i64) (.var root) (.imm 4)) fun t3 =>
                   .let_ (op64 (.add i64) (.var pWs) (.var t3.fst)) fun t4 =>
                   .store (.var bv2) (.var t4.fst)
                     (.let_ (op64 (.mul i64) (.var best2) (.imm 4)) fun t5 =>
                      .let_ (op64 (.add i64) (.var pWs) (.var t5.fst)) fun t6 =>
                      .store (.var tv) (.var t6.fst) (.jump L (.var best2, ()))))) .nil)
              fun J2 =>
                .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var rch.fst, .var bound, ())) fun cr =>
                .jnz (.var cr.fst)
                  (.let_ (op64 (.mul i64) (.var rch.fst) (.imm 4)) fun d1 =>
                   .let_ (op64 (.add i64) (.var pWs) (.var d1.fst)) fun d2 =>
                   .load i32 (.var d2.fst) fun rv1 =>
                   .let_ (Op.mk (.zext 32 64) (.var rv1, ())) fun d3 =>
                   .let_ (op64 (.mul i64) (.var d3.fst) (.imm 8)) fun d4 =>
                   .let_ (op64 (.add i64) (.var pWl) (.var d4.fst)) fun d5 =>
                   .load i64 (.var d5.fst) fun rw =>
                   .let_ (Op.mk (.zext 32 64) (.var rv1, ())) fun d6 =>
                   .let_ (op64 (.mul i64) (.var d6.fst) (.imm 8)) fun d7 =>
                   .let_ (op64 (.add i64) (.var pSc) (.var d7.fst)) fun d8 =>
                   .load i64 (.var d8.fst) fun rs =>
                   .group (sig := [[i64, i32]]) (fun _ =>
                     .cons (fun (zs : Tup V [i64, i32]) =>
                       .jump J2.fst (.var zs.fst, .var zs.snd.fst, ())) .nil)
                     fun J3 =>
                       .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var rw, .var bw1, ())) fun g1 =>
                       .jnz (.var g1.fst) (.jump J3.fst (.var rch.fst, .var rv1, ()))
                         (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var rw, .var bw1, ())) fun g2 =>
                          .jnz (.var g2.fst)
                            (.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var rs, .var bs1, ()))
                               fun g3 =>
                             .jnz (.var g3.fst) (.jump J3.fst (.var rch.fst, .var rv1, ()))
                               (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var rs, .var bs1, ()))
                                 fun g4 =>
                                .jnz (.var g4.fst)
                                  (.let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var rv1, .var bv1, ()))
                                    fun g5 =>
                                   .jnz (.var g5.fst) (.jump J3.fst (.var rch.fst, .var rv1, ()))
                                     (.jump J3.fst (.var best1, .var bv1, ())))
                                  (.jump J3.fst (.var best1, .var bv1, ()))))
                            (.jump J3.fst (.var best1, .var bv1, ()))))
                  (.jump J2.fst (.var best1, .var bv1, ()))) .nil)
          fun J1 =>
            .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var cw, .var bw, ())) fun f1 =>
            .jnz (.var f1.fst) (.jump J1.fst (.var ch.fst, .var cv1, .var cw, .var cs, ()))
              (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var cw, .var bw, ())) fun f2 =>
               .jnz (.var f2.fst)
                 (.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var cs, .var bs, ())) fun f3 =>
                  .jnz (.var f3.fst) (.jump J1.fst (.var ch.fst, .var cv1, .var cw, .var cs, ()))
                    (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var cs, .var bs, ())) fun f4 =>
                     .jnz (.var f4.fst)
                       (.let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var cv1, .var bv, ())) fun f5 =>
                        .jnz (.var f5.fst)
                          (.jump J1.fst (.var ch.fst, .var cv1, .var cw, .var cs, ()))
                          (.jump J1.fst (.var root, .var bv, .var bw, .var bs, ())))
                       (.jump J1.fst (.var root, .var bv, .var bw, .var bs, ()))))
                 (.jump J1.fst (.var root, .var bv, .var bw, .var bs, ())))))
    (.jump B (.var root, ()))

@[expose] def rStableExpr (h cv _vl fl ws _qp _qn _qs wl _wr : Val i64) : Expr Val Cont [i64] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .call "full_rescale" (as := [i64]) (bs := []) (.var h, ()) fun _ =>
  .let_ (op64 (.add i64) (.var h) (.imm 216)) fun psc =>
  .load i64 (.var psc.fst) fun sc =>
  .group (sig := [[i64, i64]]) (fun Js => .cons (fun (p : Tup Val [i64, i64]) =>
    let n_s := p.fst; let sv := p.snd.fst
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var sv, .var cv, ())) fun c1 =>
    .jnz (.var c1.fst)
      (.group (sig := [[i64]]) (fun _ => .cons (fun (q : Tup Val [i64]) =>
        .let_ (op64 (.add i64) (.var sv) (.imm 1)) fun sv1 =>
        .jump Js.fst (.var q.fst, .var sv1.fst, ())) .nil)
        fun Jn =>
          .let_ (op64 (.mul i64) (.var sv) (.imm 4)) fun pf0 =>
          .let_ (op64 (.add i64) (.var fl) (.var pf0.fst)) fun pf =>
          .load i32 (.var pf.fst) fun flv =>
          .let_ (Op.mk (.and i32) (.var flv, .imm 1, ())) fun fa =>
          .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var fa.fst, .imm 0, ())) fun fc =>
          .jnz (.var fc.fst)
            (.let_ (op64 (.mul i64) (.var n_s) (.imm 4)) fun w1 =>
             .let_ (op64 (.add i64) (.var ws) (.var w1.fst)) fun w2 =>
             .let_ (Op.mk (.trunc 64 32) (.var sv, ())) fun sv32 =>
             .store (.var sv32.fst) (.var w2.fst)
               (.let_ (op64 (.add i64) (.var n_s) (.imm 1)) fun ns1 =>
                .jump Jn.fst (.var ns1.fst, ())))
            (.jump Jn.fst (.var n_s, ())))
      (.group (sig := [[]]) (fun _ => .cons (fun _ =>
        .group (sig := [[i64]]) (fun Jr => .cons (fun (r : Tup Val [i64]) =>
          let rem := r.fst
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var rem, .imm 0, ())) fun cr =>
          .jnz (.var cr.fst)
            (.let_ (op64 (.sub i64) (.var rem) (.imm 1)) fun rem1 =>
             .let_ (op64 (.mul i64) (.var rem1.fst) (.imm 4)) fun r1 =>
             .let_ (op64 (.add i64) (.var ws) (.var r1.fst)) fun r2 =>
             .load i32 (.var r2.fst) fun idx =>
             .let_ (Op.mk (.zext 32 64) (.var idx, ())) fun r3 =>
             .let_ (op64 (.mul i64) (.var r3.fst) (.imm 8)) fun r4 =>
             .let_ (op64 (.add i64) (.var sc) (.var r4.fst)) fun r5 =>
             .let_ (Op.mk (.zext 32 64) (.var idx, ())) fun r6 =>
             .let_ (op64 (.mul i64) (.var r6.fst) (.imm 8)) fun r7 =>
             .let_ (op64 (.add i64) (.var sc) (.var r7.fst)) fun r8 =>
             .load i64 (.var r8.fst) fun sci =>
             .let_ (Op.mk (.zext 32 64) (.var idx, ())) fun r9 =>
             .let_ (op64 (.mul i64) (.var r9.fst) (.imm 8)) fun r10 =>
             .let_ (op64 (.add i64) (.var wl) (.var r10.fst)) fun r11 =>
             .load i64 (.var r11.fst) fun wli =>
             .call "f64u_add" (as := [i64, i64]) (bs := [i64]) (.var sci, .var wli, ()) fun sum =>
             .store (.var sum.fst) (.var r5.fst)
               (.call "full_heap_up" (as := [i64, i32]) (bs := []) (.var h, .var idx, ()) fun _ =>
                .jump Jr.fst (.var rem1.fst, ())))
            (.ret (.var n_s, ()))) .nil)
          fun Jr => .jump Jr.fst (.var n_s, ())) .nil)
        fun J6 =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var n_s, .imm 1, ())) fun cn =>
          .jnz (.var cn.fst)
            (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun sh =>
             .let_ (op64 (.lshr i64) (.var n_s) (.var sh.fst)) fun s0 =>
             .group (sig := [[i64]]) (fun Jb => .cons (fun (sb : Tup Val [i64]) =>
               .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var sb.fst, .imm 0, ())) fun cb =>
               .jnz (.var cb.fst)
                 (.let_ (op64 (.sub i64) (.var sb.fst) (.imm 1)) fun sb1 =>
                  .group (sig := [[i64]]) (fun _ => .cons (fun _ =>
                    .jump Jb.fst (.var sb1.fst, ())) .nil)
                    fun JB =>
                      .group (sig := [[i64]]) (fun JL => .cons (fun (rt : Tup Val [i64]) =>
                        rSiftInnerExpr ws wl sc n_s JB.fst JL.fst rt.fst) .nil)
                        fun JL => .jump JL.fst (.var sb1.fst, ()))
                 (.group (sig := [[i64]]) (fun Jp => .cons (fun (ep : Tup Val [i64]) =>
                   .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var ep.fst, .imm 1, ())) fun cp =>
                   .jnz (.var cp.fst)
                     (.let_ (op64 (.sub i64) (.var ep.fst) (.imm 1)) fun e1 =>
                      .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun z0 =>
                      .let_ (op64 (.mul i64) (.var z0.fst) (.imm 4)) fun z1 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z1.fst)) fun z2 =>
                      .load i32 (.var z2.fst) fun sw =>
                      .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun z3 =>
                      .let_ (op64 (.mul i64) (.var z3.fst) (.imm 4)) fun z4 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z4.fst)) fun z5 =>
                      .let_ (op64 (.mul i64) (.var e1.fst) (.imm 4)) fun z6 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z6.fst)) fun z7 =>
                      .load i32 (.var z7.fst) fun wse =>
                      .store (.var wse) (.var z5.fst)
                        (.let_ (op64 (.mul i64) (.var e1.fst) (.imm 4)) fun z8 =>
                         .let_ (op64 (.add i64) (.var ws) (.var z8.fst)) fun z9 =>
                         .store (.var sw) (.var z9.fst)
                           (.group (sig := [[i64]]) (fun _ => .cons (fun _ =>
                             .jump Jp.fst (.var e1.fst, ())) .nil)
                             fun JBp =>
                               .group (sig := [[i64]])
                                 (fun JLp => .cons (fun (rt : Tup Val [i64]) =>
                                   rSiftInnerExpr ws wl sc e1.fst JBp.fst JLp.fst rt.fst) .nil)
                                 fun JLp => .jump JLp.fst (.imm 0, ()))))
                     (.jump J6.fst ())) .nil)
                   fun Jp => .jump Jp.fst (.var n_s, ()))) .nil)
               fun Jb => .jump Jb.fst (.var s0.fst, ()))
            (.jump J6.fst ()))) .nil)
    fun Js => .jump Js.fst (.imm 0, .imm 0, ())

@[expose] def rPhase2Expr (h n cv vl _fl ws qp qn qs _wl _wr : Val i64) : Expr Val Cont [i64] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Jrv => .cons (fun (p : Tup Val [i64]) =>
    let rv := p.fst
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var rv, .var cv, ())) fun c1 =>
    .jnz (.var c1.fst)
      (.let_ (op64 (.mul i64) (.var rv) (.imm 4)) fun a1 =>
       .let_ (op64 (.add i64) (.var qp) (.var a1.fst)) fun a2 =>
       .store (t := i32) (.imm 4294967295) (.var a2.fst)
         (.let_ (op64 (.mul i64) (.var rv) (.imm 4)) fun a3 =>
          .let_ (op64 (.add i64) (.var qn) (.var a3.fst)) fun a4 =>
          .store (t := i32) (.imm 4294967295) (.var a4.fst)
            (.let_ (op64 (.mul i64) (.var rv) (.imm 4)) fun a5 =>
             .let_ (op64 (.add i64) (.var qs) (.var a5.fst)) fun a6 =>
             .store (t := i32) (.imm 0) (.var a6.fst)
               (.let_ (op64 (.add i64) (.var rv) (.imm 1)) fun rv1 =>
                .jump Jrv.fst (.var rv1.fst, ())))))
      (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var n, .imm 0, ())) fun cz =>
       .jnz (.var cz.fst)
         (.let_ (op64 (.add i64) (.var h) (.imm 608)) fun f1 =>
          .store (t := i64) (.imm 4294967295) (.var f1.fst)
            (.let_ (op64 (.add i64) (.var h) (.imm 616)) fun f2 =>
             .store (t := i64) (.imm 4294967295) (.var f2.fst)
               (.let_ (op64 (.add i64) (.var h) (.imm 624)) fun f3 =>
                .store (t := i64) (.imm 4294967295) (.var f3.fst)
                  (.let_ (op64 (.add i64) (.var h) (.imm 640)) fun f4 =>
                   .store (t := i64) (.imm 0) (.var f4.fst)
                     (.let_ (op64 (.add i64) (.var h) (.imm 632)) fun f5 =>
                      .store (t := i64) (.imm 0) (.var f5.fst) (.ret (.imm 0, ())))))))
         (.group (sig := [[i64, i64, i64]]) (fun Jq => .cons (fun (q : Tup Val [i64, i64, i64]) =>
           let sidx := q.fst; let sstamp := q.snd.fst; let qi := q.snd.snd.fst
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var qi, .var n, ())) fun cq =>
           .jnz (.var cq.fst)
             (.let_ (op64 (.mul i64) (.var qi) (.imm 4)) fun b1 =>
              .let_ (op64 (.add i64) (.var ws) (.var b1.fst)) fun b2 =>
              .load i32 (.var b2.fst) fun cur =>
              .let_ (Op.mk (.zext 32 64) (.var cur, ())) fun b3 =>
              .let_ (op64 (.mul i64) (.var b3.fst) (.imm 4)) fun b4 =>
              .let_ (op64 (.add i64) (.var qp) (.var b4.fst)) fun b5 =>
              .group (sig := [[i32]]) (fun _ => .cons (fun (pv : Tup Val [i32]) =>
                .store (.var pv.fst) (.var b5.fst)
                  (.let_ (Op.mk (.zext 32 64) (.var cur, ())) fun c2 =>
                   .let_ (op64 (.mul i64) (.var c2.fst) (.imm 4)) fun c3 =>
                   .let_ (op64 (.add i64) (.var qn) (.var c3.fst)) fun c4 =>
                   .group (sig := [[i32]]) (fun _ => .cons (fun (nv : Tup Val [i32]) =>
                     .store (.var nv.fst) (.var c4.fst)
                       (.let_ (Op.mk (.zext 32 64) (.var cur, ())) fun d1 =>
                        .let_ (op64 (.mul i64) (.var d1.fst) (.imm 4)) fun d2 =>
                        .let_ (op64 (.add i64) (.var qs) (.var d2.fst)) fun d3 =>
                        .let_ (op64 (.add i64) (.var qi) (.imm 1)) fun qi1 =>
                        .let_ (Op.mk (.trunc 64 32) (.var qi1.fst, ())) fun qs32 =>
                        .store (.var qs32.fst) (.var d3.fst)
                          (.group (sig := [[i64, i64]]) (fun _ =>
                            .cons (fun (ss : Tup Val [i64, i64]) =>
                              .let_ (op64 (.add i64) (.var qi) (.imm 1)) fun qn1 =>
                              .jump Jq.fst (.var ss.fst, .var ss.snd.fst, .var qn1.fst, ())) .nil)
                            fun Js =>
                              .let_ (Op.mk (.zext 32 64) (.var cur, ())) fun e1 =>
                              .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun e2 =>
                              .let_ (op64 (.shl i64) (.var e1.fst) (.var e2.fst)) fun e3 =>
                              .let_ (op64 (.add i64) (.var vl) (.var e3.fst)) fun e4 =>
                              .load i8 (.var e4.fst) fun v0 =>
                              .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun e5 =>
                              .let_ (Op.mk (.sext 8 32) (.var v0, ())) fun e6 =>
                              .let_ (Op.mk (.sext 8 32) (.var e5.fst, ())) fun e7 =>
                              .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var e6.fst, .var e7.fst, ()))
                                fun e8 =>
                              .jnz (.var e8.fst)
                                (.let_ (Op.mk (.zext 32 64) (.var cur, ())) fun e9 =>
                                 .let_ (op64 (.add i64) (.var qi) (.imm 1)) fun e10 =>
                                 .jump Js.fst (.var e9.fst, .var e10.fst, ()))
                                (.jump Js.fst (.var sidx, .var sstamp, ()))))) .nil)
                     fun Jn =>
                       .let_ (op64 (.add i64) (.var qi) (.imm 1)) fun n1 =>
                       .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var n1.fst, .var n, ())) fun n2 =>
                       .jnz (.var n2.fst)
                         (.let_ (op64 (.add i64) (.var qi) (.imm 1)) fun n3 =>
                          .let_ (op64 (.mul i64) (.var n3.fst) (.imm 4)) fun n4 =>
                          .let_ (op64 (.add i64) (.var ws) (.var n4.fst)) fun n5 =>
                          .load i32 (.var n5.fst) fun wn =>
                          .jump Jn.fst (.var wn, ()))
                         (.jump Jn.fst (.imm 4294967295, ())))) .nil)
                fun Jp =>
                  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var qi, .imm 0, ())) fun p1 =>
                  .jnz (.var p1.fst)
                    (.let_ (op64 (.sub i64) (.var qi) (.imm 1)) fun p2 =>
                     .let_ (op64 (.mul i64) (.var p2.fst) (.imm 4)) fun p3 =>
                     .let_ (op64 (.add i64) (.var ws) (.var p3.fst)) fun p4 =>
                     .load i32 (.var p4.fst) fun wp =>
                     .jump Jp.fst (.var wp, ()))
                    (.jump Jp.fst (.imm 4294967295, ())))
             (.let_ (op64 (.add i64) (.var h) (.imm 608)) fun g1 =>
              .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun g2 =>
              .let_ (op64 (.mul i64) (.var g2.fst) (.imm 4)) fun g3 =>
              .let_ (op64 (.add i64) (.var ws) (.var g3.fst)) fun g4 =>
              .load i32 (.var g4.fst) fun w0 =>
              .let_ (Op.mk (.zext 32 64) (.var w0, ())) fun g5 =>
              .store (.var g5.fst) (.var g1.fst)
                (.let_ (op64 (.add i64) (.var h) (.imm 616)) fun g6 =>
                 .let_ (op64 (.sub i64) (.var n) (.imm 1)) fun g7 =>
                 .let_ (op64 (.mul i64) (.var g7.fst) (.imm 4)) fun g8 =>
                 .let_ (op64 (.add i64) (.var ws) (.var g8.fst)) fun g9 =>
                 .load i32 (.var g9.fst) fun wl1 =>
                 .let_ (Op.mk (.zext 32 64) (.var wl1, ())) fun g10 =>
                 .store (.var g10.fst) (.var g6.fst)
                   (.let_ (op64 (.add i64) (.var h) (.imm 640)) fun g11 =>
                    .store (.var n) (.var g11.fst)
                      (.group (sig := [[i64, i64]]) (fun _ =>
                        .cons (fun (sf : Tup Val [i64, i64]) =>
                          .let_ (op64 (.add i64) (.var h) (.imm 624)) fun h1 =>
                          .store (.var sf.fst) (.var h1.fst)
                            (.let_ (op64 (.add i64) (.var h) (.imm 632)) fun h2 =>
                             .store (.var sf.snd.fst) (.var h2.fst) (.ret (.var n, ())))) .nil)
                        fun Jf =>
                          .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var sidx, .var cv, ())) fun h3 =>
                          .jnz (.var h3.fst)
                            (.let_ (op64 (.sub i64) (.var n) (.imm 1)) fun h4 =>
                             .let_ (op64 (.mul i64) (.var h4.fst) (.imm 4)) fun h5 =>
                             .let_ (op64 (.add i64) (.var ws) (.var h5.fst)) fun h6 =>
                             .load i32 (.var h6.fst) fun wl2 =>
                             .let_ (Op.mk (.zext 32 64) (.var wl2, ())) fun h7 =>
                             .jump Jf.fst (.var h7.fst, .var n, ()))
                            (.jump Jf.fst (.var sidx, .var sstamp, ()))))))) .nil)
           fun Jq => .jump Jq.fst (.imm 4294967295, .imm 0, .imm 0, ())))) .nil)
    fun Jrv => .jump Jrv.fst (.imm 0, ())

@[expose] def rFocusExpr (h cv vl fl ws qp qn qs wl wr : Val i64) : Expr Val Cont [i64] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64]]) (fun Jf => .cons (fun (p : Tup Val [i64, i64]) =>
    let n := p.fst; let av := p.snd.fst
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var av, .var cv, ())) fun c1 =>
    .jnz (.var c1.fst)
      (.group (sig := [[i64]]) (fun _ => .cons (fun (q : Tup Val [i64]) =>
        .let_ (op64 (.add i64) (.var av) (.imm 1)) fun av1 =>
        .jump Jf.fst (.var q.fst, .var av1.fst, ())) .nil)
        fun Jn =>
          .let_ (op64 (.mul i64) (.var av) (.imm 4)) fun pf0 =>
          .let_ (op64 (.add i64) (.var fl) (.var pf0.fst)) fun pf =>
          .load i32 (.var pf.fst) fun flv =>
          .let_ (Op.mk (.and i32) (.var flv, .imm 1, ())) fun fa =>
          .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var fa.fst, .imm 0, ())) fun fc =>
          .jnz (.var fc.fst)
            (.let_ (op64 (.mul i64) (.var n) (.imm 4)) fun w1 =>
             .let_ (op64 (.add i64) (.var ws) (.var w1.fst)) fun w2 =>
             .let_ (Op.mk (.trunc 64 32) (.var av, ())) fun av32 =>
             .store (.var av32.fst) (.var w2.fst)
               (.let_ (op64 (.add i64) (.var n) (.imm 1)) fun n1 =>
                .jump Jn.fst (.var n1.fst, ())))
            (.jump Jn.fst (.var n, ())))
      (.group (sig := [[]]) (fun _ => .cons (fun _ =>
        rPhase2Expr h n cv vl fl ws qp qn qs wl wr) .nil)
        fun J6 =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var n, .imm 1, ())) fun cn =>
          .jnz (.var cn.fst)
            (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun sh =>
             .let_ (op64 (.lshr i64) (.var n) (.var sh.fst)) fun s0 =>
             .group (sig := [[i64]]) (fun Jb => .cons (fun (sb : Tup Val [i64]) =>
               .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var sb.fst, .imm 0, ())) fun cb =>
               .jnz (.var cb.fst)
                 (.let_ (op64 (.sub i64) (.var sb.fst) (.imm 1)) fun sb1 =>
                  .call "full_reorder_sift_fid" (as := [i64, i64, i64]) (bs := [])
                    (.var h, .var sb1.fst, .var n, ()) fun _ =>
                  .jump Jb.fst (.var sb1.fst, ()))
                 (.group (sig := [[i64]]) (fun Jp => .cons (fun (ep : Tup Val [i64]) =>
                   .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var ep.fst, .imm 1, ())) fun cp =>
                   .jnz (.var cp.fst)
                     (.let_ (op64 (.sub i64) (.var ep.fst) (.imm 1)) fun e1 =>
                      .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun z0 =>
                      .let_ (op64 (.mul i64) (.var z0.fst) (.imm 4)) fun z1 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z1.fst)) fun z2 =>
                      .load i32 (.var z2.fst) fun sw =>
                      .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun z3 =>
                      .let_ (op64 (.mul i64) (.var z3.fst) (.imm 4)) fun z4 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z4.fst)) fun z5 =>
                      .let_ (op64 (.mul i64) (.var e1.fst) (.imm 4)) fun z6 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z6.fst)) fun z7 =>
                      .load i32 (.var z7.fst) fun wse =>
                      .store (.var wse) (.var z5.fst)
                        (.let_ (op64 (.mul i64) (.var e1.fst) (.imm 4)) fun z8 =>
                         .let_ (op64 (.add i64) (.var ws) (.var z8.fst)) fun z9 =>
                         .store (.var sw) (.var z9.fst)
                           (.call "full_reorder_sift_fid" (as := [i64, i64, i64]) (bs := [])
                             (.var h, .imm 0, .var e1.fst, ()) fun _ =>
                            .jump Jp.fst (.var e1.fst, ()))))
                     (.jump J6.fst ())) .nil)
                   fun Jp => .jump Jp.fst (.var n, ()))) .nil)
               fun Jb => .jump Jb.fst (.var s0.fst, ()))
            (.jump J6.fst ()))) .nil)
    fun Jf => .jump Jf.fst (.imm 0, .imm 0, ())

/-! ## 2. Stable-Mode Reorder Branch (`reorder_sift_inner_wp` & `reorder_stable_wp`) -/

private theorem reorder_sift_inner_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s sF1 sb : FullState} {R : Mem 64 → Prop} {wl1 wr1 : Arr64 c.max_vars}
    {n_s bound root : BitVec 64} {B L : Cont [i64]} {mb : Mem 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars)
    (hsc1_len : sF1.scratch.score.length = c.max_vars)
    (hn_cv : n_s.toNat ≤ s.core.cur_vars) (hbd_le : bound.toNat ≤ n_s.toNat)
    (hroot : root.toNat < bound.toNat)
    (hsb_eq : RWsortEq sF1 sb) (hwsb : sb.scratch.wsort.length = 2 * c.max_vars)
    (hwb_b : WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars)
    (hmb : (ReorderMem c sb wl1 wr1 ⋆ R) mb)
    (hB : ∀ r m', (∃ sb' : FullState, RWsortEq sF1 sb' ∧
      sb'.scratch.wsort.length = 2 * c.max_vars ∧
      WsortBounded sb'.scratch.wsort n_s.toNat s.core.cur_vars ∧
      (ReorderMem c sb' wl1 wr1 ⋆ R) m') → B (r, ()) m')
    (hL : ∀ r' m', bound.toNat - r'.toNat < bound.toNat - root.toNat →
      (r'.toNat < bound.toNat ∧ ∃ sb' : FullState, RWsortEq sF1 sb' ∧
        sb'.scratch.wsort.length = 2 * c.max_vars ∧
        WsortBounded sb'.scratch.wsort n_s.toNat s.core.cur_vars ∧
        (ReorderMem c sb' wl1 wr1 ⋆ R) m') → L (r', ()) m') :
    wp Γ Q X (rSiftInnerExpr c.pWsort c.pTarjanMark c.pScore bound B L root) mb := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscb_len : sb.scratch.score.length = c.max_vars := by
    unfold RWsortEq at hsb_eq; rw [hsb_eq]; exact hsc1_len
  have hch_eq : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
  have hrt_ws : root.toNat < sb.scratch.wsort.length := by omega
  have hbv_lt : (sb.scratch.wsort[root.toNat]'hrt_ws).toNat < s.core.cur_vars :=
    wb_get hwb_b (by omega) hrt_ws
  have hbv_mv : (BitVec.setWidth 64 (sb.scratch.wsort[root.toNat]'hrt_ws)).toNat <
      c.max_vars := r_zext64_32_lt (Nat.lt_of_lt_of_le hbv_lt hcv_le)
  have hbv_sc : (BitVec.setWidth 64 (sb.scratch.wsort[root.toNat]'hrt_ws)).toNat <
      sb.scratch.score.length := hscb_len ▸ hbv_mv
  dsimp only [rSiftInnerExpr]
  c0_hsplit
  · c0_hsplit
    · c0_hsteps; exact hB root mb ⟨sb, hsb_eq, hwsb, hwb_b, hmb⟩
    · have hch_nat : ((root <<< 1) + 1#64).toNat < bound.toNat := r_child_nat (by omega) ‹_›
      have hch_ws : ((root <<< 1) + 1#64).toNat < sb.scratch.wsort.length := by omega
      have hcv_lt : (sb.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_ws).toNat <
          s.core.cur_vars := wb_get hwb_b (by omega) hch_ws
      have hcv_mv : (BitVec.setWidth 64
          (sb.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_ws)).toNat < c.max_vars :=
        r_zext64_32_lt (Nat.lt_of_lt_of_le hcv_lt hcv_le)
      have hcv_sc : (BitVec.setWidth 64
          (sb.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_ws)).toNat <
          sb.scratch.score.length := hscb_len ▸ hcv_mv
      have hrch_eq : ((root <<< 1) + 1#64 + 1#64).toNat = 2 * root.toNat + 2 := by bv_omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i32, i64, i64])
        (fun xs m' => m' = mb ∧ (xs.1 = root ∨ xs.1 = (root <<< 1) + 1#64) ∧
          xs.1.toNat < bound.toNat ∧ xs.2.1.toNat < s.core.cur_vars) ?_ ?_
      · rintro _ xs m' ⟨hm_eq, hx_eq, hx_lt, hxv_lt⟩
        subst m'; dsimp only [Blocks.get]; c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i32])
          (fun ys m'' => m'' = mb ∧
            (ys.1 = root ∨ ys.1 = (root <<< 1) + 1#64 ∨ ys.1 = (root <<< 1) + 1#64 + 1#64) ∧
            ys.1.toNat < bound.toNat ∧ ys.2.1.toNat < s.core.cur_vars) ?_ ?_
        · rintro _ ys m'' ⟨hm_eq', hy_eq, hy_lt, hyv_lt⟩
          subst m''; c0_hsplit
          · c0_hsteps; exact hB _ mb ⟨sb, hsb_eq, hwsb, hwb_b, hmb⟩
          · have hgt : root.toNat < ys.1.toNat := by
              rcases hy_eq with h1 | h1 | h1
              · exact absurd h1 ‹_›
              · rw [h1, hch_eq]; omega
              · rw [h1, hrch_eq]; omega
            have hys_ws : ys.1.toNat < sb.scratch.wsort.length := by omega
            have hys_ws' : ys.1.toNat < (sb.scratch.wsort.set root.toNat ys.2.1).length := by
              simpa using hys_ws
            c0_hsteps
            let ws2 := (sb.scratch.wsort.set root.toNat ys.2.1).set ys.1.toNat
              (sb.scratch.wsort[root.toNat]'hrt_ws)
            exact hL ys.1 _ (by omega)
              ⟨hy_lt, { sb with scratch := { sb.scratch with wsort := ws2 } },
               rw_set hsb_eq _, by simp [ws2, hwsb],
               wb_swap hwb_b hyv_lt hbv_lt, by assumption⟩
        · intro J2 hJ2; c0_hsplit
          · have hrch_nat : ((root <<< 1) + 1#64 + 1#64).toNat < bound.toNat := by
              clear hB hL hwb_b hmb hbv_lt hbv_mv hbv_sc hcv_lt hcv_mv hcv_sc hx_eq hx_lt hxv_lt
              have hone : (1 : BitVec 64).toNat = 1 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                hone, Nat.shiftLeft_eq, Nat.pow_one, Nat.reducePow, Nat.reduceMod] at *
              omega
            have hrch_ws : ((root <<< 1) + 1#64 + 1#64).toNat < sb.scratch.wsort.length := by omega
            have hrv_lt : (sb.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws).toNat <
                s.core.cur_vars := wb_get hwb_b (by omega) hrch_ws
            have hrv_mv : (BitVec.setWidth 64
                (sb.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                c.max_vars := r_zext64_32_lt (Nat.lt_of_lt_of_le hrv_lt hcv_le)
            have hrv_sc : (BitVec.setWidth 64
                (sb.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                sb.scratch.score.length := hscb_len ▸ hrv_mv
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i32])
              (fun zs m'' => m'' = mb ∧
                (zs.1 = root ∨ zs.1 = (root <<< 1) + 1#64 ∨ zs.1 = (root <<< 1) + 1#64 + 1#64) ∧
                zs.1.toNat < bound.toNat ∧ zs.2.1.toNat < s.core.cur_vars)
              (fun _ _ m'' ⟨hm_z, hz⟩ => by
                subst m''; dsimp only [Blocks.get]; c0_hsteps; exact hJ2 _ mb ⟨rfl, hz⟩)
              (fun J3 hJ3 => by
                c0_hsteps_nogrp; all_goals
                  refine hJ3 _ mb ⟨rfl, ?_, ?_, ?_⟩
                  · first | exact Or.inr (Or.inr rfl) | exact hx_eq.imp_right Or.inl
                  · first | exact hrch_nat | exact hx_lt
                  · first | exact hrv_lt | exact hxv_lt)
          · c0_hsteps; exact hJ2 _ mb ⟨rfl, hx_eq.imp_right Or.inl, hx_lt, hxv_lt⟩
      · intro J1 hJ1; c0_hsteps_nogrp; all_goals
          refine hJ1 _ mb ⟨rfl, ?_, ?_, ?_⟩
          · first | exact Or.inl rfl | exact Or.inr rfl
          · first | exact hroot | exact hch_nat
          · first | exact hbv_lt | exact hcv_lt
  · exact absurd ‹true = false› (by decide)

theorem reorder_stable_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl4 wr4 : Arr64 c.max_vars}
    {m4 : Mem 64}
    (hFadd : Γ.Has "f64u_add" f64uPure2Spec)
    (hRescale : Γ.Has "full_rescale" fullRescaleSpec)
    (hHeapUp : Γ.Has "full_heap_up" fullHeapUpSpec)
    (hlen : s.LengthsOk c) (hQ' : ∀ r m', RPostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_30 : s.core.cur_vars < 2 ^ 30) (hm4 : (ReorderMem c s wl4 wr4 ⋆ R) m4) :
    wp Γ Q X (rStableExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pVals c.pFlags
      c.pWsort c.pQPrev c.pQNext c.pQStamp c.pTarjanMark c.pTarjanReach) m4 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars :=
    Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide))
  dsimp only [rStableExpr]
  obtain ⟨tmk0, trc0, htmk0, htrc0, hmF0⟩ := fullMem_of_reorderMem hm4
  let sF0 : FullState :=
    { s with scratch := { s.scratch with tarjan_mark := tmk0, tarjan_reach := trc0 } }
  have hlenF0 : sF0.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with tarjan_mark_len := htmk0, tarjan_reach_len := htrc0 }⟩
  c0_call hRescale
  refine ⟨c, sF0, R, rfl, hlenF0, hmF0, fun _ sF1 mF1 hsF1_core hsF1_len hsF1_p hmF1 => ?_⟩
  obtain ⟨wl1, wr1, hm1r⟩ := reorderMem_of_fullMem hsF1_len hmF1
  have hce1 : sF1.core = s.core := hsF1_core
  have hext1 : FullExtScratchPres s sF1 := hsF1_p.1
  have hfl1_len : sF1.core.flags.length = c.max_vars := hsF1_len.core_ok.flags_len
  have hws1_len : sF1.scratch.wsort.length = 2 * c.max_vars := hsF1_len.scratch_ok.wsort_len
  have hsc1_len : sF1.scratch.score.length = c.max_vars := hsF1_len.scratch_ok.score_len
  c0_hsteps_nogrp
  -- Collect active vars into `ws[0 ..< n_s)`
  refine wp_while_state (fun p : BitVec 64 × BitVec 64 × PUnit => p)
    (fun p => s.core.cur_vars - p.2.1.toNat)
    (fun p m5 => p.2.1.toNat ≤ s.core.cur_vars ∧ p.1.toNat ≤ p.2.1.toNat ∧
      ∃ s5 : FullState, RWsortEq sF1 s5 ∧ s5.scratch.wsort.length = 2 * c.max_vars ∧
        WsortBounded s5.scratch.wsort p.1.toNat s.core.cur_vars ∧
        (ReorderMem c s5 wl1 wr1 ⋆ R) m5)
    (fun J5 hJ5 => by
      c0_hsteps; exact hJ5 (0#64, 0#64, ()) mF1 ⟨Nat.zero_le _, Nat.zero_le _, sF1,
        rw_refl sF1, hws1_len, fun _ h => absurd h (Nat.not_lt_zero _), hm1r⟩)
    (fun J5 ⟨n_s, sv, ⟨⟩⟩ m5 ⟨hsv, hn_le, s5, hs5_eq, hws5_len, hwb5, hm5⟩ hJ5 => ?_)
  c0_hsplit
  · have hsv_lt : sv.toNat < s.core.cur_vars := r_bv64_lt_mod hcv_30 ‹_›
    have hsv_fl : sv.toNat < s5.core.flags.length :=
      (rw_flags hs5_eq).symm ▸ hfl1_len.symm ▸ Nat.lt_of_lt_of_le hsv_lt hcv_le
    have hsvp1 := r_add1 hcv_30 hsv_lt
    have hn_lt : n_s.toNat < s.core.cur_vars := Nat.lt_of_le_of_lt hn_le hsv_lt
    have hnp1 := r_add1 hcv_30 hn_lt
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun n' m5' => n'.1.toNat ≤ sv.toNat + 1 ∧ ∃ s5' : FullState,
        RWsortEq sF1 s5' ∧ s5'.scratch.wsort.length = 2 * c.max_vars ∧
        WsortBounded s5'.scratch.wsort n'.1.toNat s.core.cur_vars ∧
        (ReorderMem c s5' wl1 wr1 ⋆ R) m5')
      (fun _ ⟨n', ⟨⟩⟩ m5' ⟨hn', s5', hs5', hlen5', hwb5', hm5'⟩ => by
        dsimp only [Blocks.get]; c0_hsteps
        exact hJ5 (n', sv + 1#64, ()) m5' hsvp1.2.2
          ⟨hsvp1.2.1, hsvp1.1 ▸ hn', s5', hs5', hlen5', hwb5', hm5'⟩)
      (fun Jc hJc => ?_)
    c0_hsplit
    · have hn_ws : n_s.toNat < s5.scratch.wsort.length :=
        hws5_len.symm ▸ Nat.lt_of_lt_of_le hn_lt hcv_ws
      have hsv_cv : (BitVec.setWidth 32 sv).toNat < s.core.cur_vars := by
        have : sv.toNat < 2 ^ 32 := lt_trans hsv_lt (lt_trans hcv_29 (by decide))
        have hz : (BitVec.setWidth 32 sv).toNat = sv.toNat := by bv_omega
        omega
      c0_hsteps
      exact hJc (n_s + 1#64, ()) _
        ⟨Nat.le_trans (Nat.le_of_eq hnp1.1) (Nat.succ_le_succ hn_le),
         { s5 with scratch := { s5.scratch with
             wsort := s5.scratch.wsort.set n_s.toNat (BitVec.setWidth 32 sv) } },
         rw_set hs5_eq _, by simp [hws5_len],
         hnp1.1 ▸ wb_push hwb5 hn_ws hsv_cv, by assumption⟩
    · c0_hsteps; exact hJc (n_s, ()) m5
        ⟨Nat.le_trans hn_le (Nat.le_succ _), s5, hs5_eq, hws5_len, hwb5, hm5⟩
  · have hn_cv : n_s.toNat ≤ s.core.cur_vars := Nat.le_trans hn_le hsv
    have hn_29 : n_s.toNat < 2 ^ 30 := Nat.lt_of_le_of_lt hn_cv (lt_trans hcv_29 (by decide))
    refine wp_join_group (ts := [])
      (fun _ m6 => ∃ s6 : FullState, RWsortEq sF1 s6 ∧
        s6.scratch.wsort.length = 2 * c.max_vars ∧
        WsortBounded s6.scratch.wsort n_s.toNat s.core.cur_vars ∧
        (ReorderMem c s6 wl1 wr1 ⋆ R) m6) ?_ ?_
    · -- Post-heapsort: reverse sweep `rem_s = n_s ..> 0`: update scores & `full_heap_up`
      rintro _ _ m6 ⟨s6, hs6_eq, hws6_len, hwb6, hm6⟩
      dsimp only [Blocks.get]; c0_hsteps_nogrp
      have hlen6 : s6.LengthsOk c :=
        rw_lengthsOk hsF1_len hs6_eq (hws6_len.trans hws1_len.symm)
      have hce6 : s6.core = s.core := by unfold RWsortEq at hs6_eq; rw [hs6_eq]; exact hce1
      have hext6 : FullExtScratchPres s s6 := by
        unfold RWsortEq at hs6_eq; rw [hs6_eq]; exact hext1
      refine wp_while_state1 (fun rem : BitVec 64 => rem) (fun rem => rem.toNat)
        (fun rem m7 => rem.toNat ≤ n_s.toNat ∧ ∃ (sb : FullState) (wlb wrb : Arr64 c.max_vars),
          sb.core = s.core ∧ sb.LengthsOk c ∧ FullExtScratchPres s sb ∧
          WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
          (ReorderMem c sb wlb wrb ⋆ R) m7)
        (fun J7 hJ7 => by
          c0_hsteps; exact hJ7 n_s m6 ⟨le_refl _, s6, wl1, wr1, hce6, hlen6, hext6, hwb6, hm6⟩)
        (fun J7 rem m7 ⟨hrem, sb, wlb, wrb, hsb_core, hsb_len, hsb_ext, hwb_b, hmb⟩ hJ7 => ?_)
      c0_hsplit
      · have hrp := r_sub1 hn_29 hrem ‹_›
        have hr_ws : (rem - 1#64).toNat < sb.scratch.wsort.length :=
          hsb_len.scratch_ok.wsort_len.symm ▸
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hrp.2.2.2 hn_cv) hcv_ws
        have hidx_cv : (sb.scratch.wsort[(rem - 1#64).toNat]'hr_ws).toNat < s.core.cur_vars :=
          wb_get hwb_b hrp.2.2.2 hr_ws
        have hidx_mv : (BitVec.setWidth 64 (sb.scratch.wsort[(rem - 1#64).toNat]'hr_ws)).toNat <
            c.max_vars := r_zext64_32_lt (Nat.lt_of_lt_of_le hidx_cv hcv_le)
        have hidx_sc : (BitVec.setWidth 64 (sb.scratch.wsort[(rem - 1#64).toNat]'hr_ws)).toNat <
            sb.scratch.score.length := hsb_len.scratch_ok.score_len.symm ▸ hidx_mv
        c0_hsteps_nogrp
        c0_call hFadd
        intro nsc
        c0_hsteps_nogrp
        let sb1 : FullState :=
          { sb with scratch := { sb.scratch with
              score := sb.scratch.score.set
                (BitVec.setWidth 64 (sb.scratch.wsort[(rem - 1#64).toNat]'hr_ws)).toNat nsc } }
        have hlen1 : sb1.LengthsOk c := ⟨hsb_len.core_ok, { hsb_len.scratch_ok with
          score_len := by simp [sb1, hsb_len.scratch_ok.score_len] }⟩
        obtain ⟨tmk1, trc1, htmk1, htrc1, hmF1'⟩ :=
          fullMem_of_reorderMem (s := sb1) (wl := wlb) (wr := wrb) (by assumption)
        let sb1F : FullState :=
          { sb1 with scratch := { sb1.scratch with tarjan_mark := tmk1, tarjan_reach := trc1 } }
        have hlen1F : sb1F.LengthsOk c := ⟨hlen1.core_ok, { hlen1.scratch_ok with
          tarjan_mark_len := htmk1, tarjan_reach_len := htrc1 }⟩
        c0_call hHeapUp
        refine ⟨c, sb1F, R, rfl, hlen1F, hmF1',
          fun _ sb2F m_b' hsb2_core hsb2_len hsb2_p hmF2' => ?_⟩
        obtain ⟨wlb2, wrb2, hm_b2⟩ := reorderMem_of_fullMem hsb2_len hmF2'
        have hsb2_ce : sb2F.core = sb.core := hsb2_core
        have hwb2 : WsortBounded sb2F.scratch.wsort n_s.toNat s.core.cur_vars := by
          obtain ⟨_, hp', ps', hscr'⟩ := hsb2_p
          have hws_eq : sb2F.scratch.wsort = sb.scratch.wsort := by rw [hscr']
          rw [hws_eq]; exact hwb_b
        c0_hsteps
        exact hJ7 (rem - 1#64) m_b' hrp.2.1
          ⟨hrp.2.2.1, sb2F, wlb2, wrb2, hsb2_ce.trans hsb_core, hsb2_len,
           ⟨hsb2_p.1.1.1.trans hsb_ext.1, hsb2_p.1.1.2.trans hsb_ext.2⟩, hwb2, hm_b2⟩
      · obtain ⟨tmkF, trcF, htmkF, htrcF, hmFF⟩ := fullMem_of_reorderMem hmb
        let sbF : FullState :=
          { sb with scratch := { sb.scratch with tarjan_mark := tmkF, tarjan_reach := trcF } }
        have hlenF : sbF.LengthsOk c := ⟨hsb_len.core_ok, { hsb_len.scratch_ok with
          tarjan_mark_len := htmkF, tarjan_reach_len := htrcF }⟩
        c0_hsteps; exact hQ' (n_s, ()) _ ⟨sbF, hsb_core, hlenF, hsb_ext, hmFF⟩
    · -- Inline heapsort on `ws[0 ..< n_s)` (`if (n_s > 1)`)
      intro J6 hJ6; c0_hsplit
      · have hn_pos : 0 < n_s.toNat := Nat.lt_trans Nat.zero_lt_one ‹_›
        c0_hsteps_nogrp
        refine wp_while_state1 (fun si : BitVec 64 => si) (fun si => si.toNat)
          (fun si m6 => si.toNat ≤ n_s.toNat ∧ ∃ s6 : FullState, RWsortEq sF1 s6 ∧
            s6.scratch.wsort.length = 2 * c.max_vars ∧
            WsortBounded s6.scratch.wsort n_s.toNat s.core.cur_vars ∧
            (ReorderMem c s6 wl1 wr1 ⋆ R) m6)
          (fun Jb hJb => by
            c0_hsteps; exact hJb (n_s >>> 1#64) m5 ⟨r_ushr1_le (le_refl _),
              s5, hs5_eq, hws5_len, hwb5, hm5⟩)
          (fun Jb si m6 ⟨hsi, s6, hs6_eq, hws6_len, hwb6, hm6⟩ hJb => ?_)
        c0_hsplit
        · have hsip := r_sub1 hn_29 hsi ‹_›
          c0_hsteps_nogrp
          refine wp_while_break_state (fun root : BitVec 64 => (root, ()))
            (fun _ mb => ∃ sb : FullState, RWsortEq sF1 sb ∧
              sb.scratch.wsort.length = 2 * c.max_vars ∧
              WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
              (ReorderMem c sb wl1 wr1 ⋆ R) mb)
            (fun root : BitVec 64 => (root, ())) (fun root => n_s.toNat - root.toNat)
            (fun root mb => root.toNat < n_s.toNat ∧ ∃ sb : FullState, RWsortEq sF1 sb ∧
              sb.scratch.wsort.length = 2 * c.max_vars ∧
              WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
              (ReorderMem c sb wl1 wr1 ⋆ R) mb)
            (fun _ _ mb ⟨sb, hsb_eq, hwsb, hwb_b, hmb⟩ => by
              c0_hsteps
              exact hJb (si - 1#64) mb hsip.2.1 ⟨hsip.2.2.1, sb, hsb_eq, hwsb, hwb_b, hmb⟩)
            (fun B L root mb hB hL ⟨hroot, sb, hsb_eq, hwsb, hwb_b, hmb⟩ => ?_)
            (fun _ _ _ hL => by
              c0_hsteps; exact hL (si - 1#64) m6 ⟨hsip.2.2.2, s6, hs6_eq, hws6_len, hwb6, hm6⟩)
          exact reorder_sift_inner_wp hcv_le hcv_29 hcv_ws hsc1_len hn_cv (le_refl _) hroot
            hsb_eq hwsb hwb_b hmb hB hL
        · -- Pop heap loop (reuses `reorder_sift_inner_wp`)
          refine wp_while_state1 (fun e : BitVec 64 => e) (fun e => e.toNat)
            (fun e m7 => e.toNat ≤ n_s.toNat ∧ ∃ s7 : FullState, RWsortEq sF1 s7 ∧
              s7.scratch.wsort.length = 2 * c.max_vars ∧
              WsortBounded s7.scratch.wsort n_s.toNat s.core.cur_vars ∧
              (ReorderMem c s7 wl1 wr1 ⋆ R) m7)
            (fun Jp hJp => by
              c0_hsteps; exact hJp n_s m6 ⟨le_refl _, s6, hs6_eq, hws6_len, hwb6, hm6⟩)
            (fun Jp e m7 ⟨he, s7, hs7_eq, hws7_len, hwb7, hm7⟩ hJp => ?_)
          c0_hsplit
          · have he_gt1 : 1 < e.toNat := ‹_›
            have he_pos : 0 < e.toNat := Nat.lt_trans Nat.zero_lt_one he_gt1
            have hep := r_sub1 hn_29 he he_pos
            have he1_n : (e - 1#64).toNat < n_s.toNat := Nat.lt_of_lt_of_le hep.2.1 he
            have h0_lt_e1 : (0#64 : BitVec 64).toNat < (e - 1#64).toNat := by
              have h1 := hep.1; simp only [BitVec.toNat_ofNat]; omega
            have h0_ws : 0 < s7.scratch.wsort.length := by omega
            have he_ws : (e - 1#64).toNat < s7.scratch.wsort.length := by omega
            have hv0_lt : (s7.scratch.wsort[0]'h0_ws).toNat < s.core.cur_vars :=
              wb_get hwb7 hn_pos h0_ws
            have hve_lt : (s7.scratch.wsort[(e - 1#64).toNat]'he_ws).toNat < s.core.cur_vars :=
              wb_get hwb7 he1_n he_ws
            have he_ws' : (e - 1#64).toNat <
                (s7.scratch.wsort.set 0 (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).length := by
              simpa using he_ws
            c0_hsteps_nogrp
            let ws_sw := (s7.scratch.wsort.set 0 (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).set
              (e - 1#64).toNat (s7.scratch.wsort[0]'h0_ws)
            let s7_sw : FullState := { s7 with scratch := { s7.scratch with wsort := ws_sw } }
            have hwb_sw : WsortBounded ws_sw n_s.toNat s.core.cur_vars :=
              wb_swap hwb7 hve_lt hv0_lt
            refine wp_while_break_state (fun root : BitVec 64 => (root, ()))
              (fun _ mb => ∃ sb : FullState, RWsortEq sF1 sb ∧
                sb.scratch.wsort.length = 2 * c.max_vars ∧
                WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
                (ReorderMem c sb wl1 wr1 ⋆ R) mb)
              (fun root : BitVec 64 => (root, ())) (fun root => (e - 1#64).toNat - root.toNat)
              (fun root mb => root.toNat < (e - 1#64).toNat ∧ ∃ sb : FullState, RWsortEq sF1 sb ∧
                sb.scratch.wsort.length = 2 * c.max_vars ∧
                WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
                (ReorderMem c sb wl1 wr1 ⋆ R) mb)
              (fun _ _ mb ⟨sb, hsb_eq, hwsb, hwb_b, hmb⟩ => by
                c0_hsteps
                exact hJp (e - 1#64) mb hep.2.1 ⟨Nat.le_of_lt he1_n, sb, hsb_eq, hwsb, hwb_b, hmb⟩)
              (fun B L root mb hB hL ⟨hroot, sb, hsb_eq, hwsb, hwb_b, hmb⟩ =>
                reorder_sift_inner_wp hcv_le hcv_29 hcv_ws hsc1_len hn_cv (le_of_lt he1_n)
                  hroot hsb_eq hwsb hwb_b hmb hB hL)
              (fun _ _ _ hL => by
                c0_hsteps
                exact hL 0#64 _ ⟨h0_lt_e1, s7_sw, rw_set hs7_eq ws_sw,
                  by dsimp only [s7_sw, ws_sw]; rw [List.length_set, List.length_set, hws7_len],
                  hwb_sw, by assumption⟩)
          · c0_hsteps; exact hJ6 () m7 ⟨s7, hs7_eq, hws7_len, hwb7, hm7⟩
      · c0_hsteps; exact hJ6 () m5 ⟨s5, hs5_eq, hws5_len, hwb5, hm5⟩

end LeanQbe.T.Examples.Kissat.Proof.Reorder
