/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul2Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Stage Decomposition for `bv_blast_mul` & `bv_blast_clz` (`Bitblast.Proof.OpsShiftMul2Stages`)

Decomposes `bv_blast_clz_body` (`clzInnerExpr`) and `bv_blast_mul_body` (`mulIteExpr`,
`mulIterExpr`, `mulLoopExpr`) definitionally via `rfl` split equations and proves their stage WP
theorems so every theorem in `OpsShiftMul2Stages` and `OpsShiftMul2` remains `<= 220` lines.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open Std.ExtHashMap
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul

/-! ## 1. Exposed Sub-Expressions (`@[expose]`) -/

@[expose] public section

@[inline] def m2Cmp (c : CmpOp) (ty : Ty) (x y : Arg Val ty)
    (k : Val ty.mask → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [ty, ty], code := OpCode.cmp c ty, args := (x, y, ()) } (fun p => k p.fst)

@[inline] def m2Bin (code : OpCode [i32, i32] [i32]) (x y : Arg Val i32)
    (k : Val i32 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i32, i32], code := code, args := (x, y, ()) } (fun p => k p.fst)

@[inline] def m2Add64 (x y : Arg Val i64)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (x, y, ()) } (fun p => k p.fst)

@[inline] def m2Zext (x : Arg Val i32)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (x, ()) } (fun p => k p.fst)

@[inline] def m2LoadLit (litsPtr : Val i64) (idx : Val i32)
    (k : Val i32 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  m2Zext (Arg.var idx) fun p0 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p0, Arg.imm 4, ()) }
    fun p1 =>
  m2Add64 (Arg.var litsPtr) (Arg.var p1.fst) fun p2 =>
  Expr.load i32 (Arg.var p2) k

@[inline] def m2AddrLit (litsPtr : Val i64) (idx : Val i32)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  m2Zext (Arg.var idx) fun p0 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p0, Arg.imm 4, ()) }
    fun p1 =>
  m2Add64 (Arg.var litsPtr) (Arg.var p1.fst) k

@[inline] def m2LoadOom (h : Val i64) (k : Val i32 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  m2Add64 (Arg.var h) (Arg.imm 120) fun p0 => Expr.load i32 (Arg.var p0) k

/-- Inner `j < w` `bv_aig_ite` loop of `bv_blast_clz` for non-zero `xc`. -/
def clzInnerExpr (h : Val i64) (w out : Val i32) (litsPtr : Val i64)
    (curr xc : Val i32) (J_next : Cont [i32]) : Expr Val Cont [i32] :=
  m2Bin (OpCode.sub i32) (Arg.var w) (Arg.imm 1) fun p18 =>
  m2Bin (OpCode.sub i32) (Arg.var p18) (Arg.var curr) fun p19 =>
  Expr.group (sig := [[i32]])
    (fun Js1 =>
      Blocks.cons
        (fun p20 =>
          m2Cmp .ult i32 (Arg.var p20.fst) (Arg.var w) fun p21 =>
          Expr.jnz (Arg.var p21)
            (Expr.group (sig := [[i32]])
              (fun _ =>
                Blocks.cons
                  (fun p22 =>
                    m2Bin (OpCode.add i32) (Arg.var out) (Arg.var p20.fst) fun p23 =>
                    m2AddrLit litsPtr p23 fun addr =>
                    m2Bin (OpCode.add i32) (Arg.var out) (Arg.var p20.fst) fun p27 =>
                    m2LoadLit litsPtr p27 fun ld =>
                    Expr.call (as := [i64, i32, i32, i32]) (bs := [i32]) "bv_aig_ite"
                      (Arg.var h, Arg.var xc, Arg.var p22.fst, Arg.var ld, ()) fun p31 =>
                    Expr.store (Arg.var p31.fst) (Arg.var addr)
                      (m2LoadOom h fun ld =>
                       m2Cmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p =>
                       Expr.jnz (Arg.var p)
                         (Expr.ret (Arg.imm 4294967295, ()))
                         (m2Bin (OpCode.add i32) (Arg.var p20.fst) (Arg.imm 1) fun p =>
                          Expr.jump Js1.fst (Arg.var p, ()))))
                  Blocks.nil)
              fun Js =>
              m2Cmp .ult i32 (Arg.var p20.fst) (Arg.imm 32) fun p =>
              Expr.jnz (Arg.var p)
                (m2Bin (OpCode.lshr i32) (Arg.var p19) (Arg.var p20.fst) fun p =>
                 m2Bin (OpCode.and i32) (Arg.var p) (Arg.imm 1) fun p =>
                 Expr.jump Js.fst (Arg.var p, ()))
                (Expr.jump Js.fst (Arg.imm 0, ())))
            (Expr.jump J_next (Arg.var p20.fst, ())))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

/-- Inner `bv_aig_ite` + `bv_lits_release(h, iterMark)` tail of a `bv_blast_mul` step. -/
def mulIteExpr (h : Val i64) (w out mark ys added iterMark : Val i32) (litsPtr : Val i64)
    (J_rel : Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i32]])
    (fun Js3 =>
      Blocks.cons
        (fun p35 =>
          m2Cmp .ult i32 (Arg.var p35.fst) (Arg.var w) fun p36 =>
          Expr.jnz (Arg.var p36)
            (m2Bin (OpCode.add i32) (Arg.var out) (Arg.var p35.fst) fun p37 =>
             m2AddrLit litsPtr p37 fun addr =>
             m2Bin (OpCode.add i32) (Arg.var added) (Arg.var p35.fst) fun p41 =>
             m2LoadLit litsPtr p41 fun ld5 =>
             m2Bin (OpCode.add i32) (Arg.var out) (Arg.var p35.fst) fun p45 =>
             m2LoadLit litsPtr p45 fun ld =>
             Expr.call (as := [i64, i32, i32, i32]) (bs := [i32]) "bv_aig_ite"
               (Arg.var h, Arg.var ys, Arg.var ld5, Arg.var ld, ()) fun p49 =>
             Expr.store (Arg.var p49.fst) (Arg.var addr)
               (m2LoadOom h fun ld =>
                m2Cmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p51 =>
                Expr.jnz (Arg.var p51)
                  (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
                    (Arg.var h, Arg.var mark, ()) fun _ =>
                   Expr.ret (Arg.imm 4294967295, ()))
                  (m2Bin (OpCode.add i32) (Arg.var p35.fst) (Arg.imm 1) fun p =>
                   Expr.jump Js3.fst (Arg.var p, ()))))
            (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
              (Arg.var h, Arg.var iterMark, ()) fun _ =>
             Expr.jump J_rel (Arg.var p35.fst, ())))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

/-- Non-zero `ys` iteration body of `bv_blast_mul` (zero + copy + mark + add + `mulIteExpr`). -/
def mulIterExpr (h : Val i64) (aOff w out mark shifted s ys : Val i32) (litsPtr : Val i64)
    (J_next : Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i32]])
    (fun Js1 =>
      Blocks.cons
        (fun p27 =>
          m2Cmp .ult i32 (Arg.var p27.fst) (Arg.var s) fun p28 =>
          Expr.jnz (Arg.var p28)
            (m2Bin (OpCode.add i32) (Arg.var shifted) (Arg.var p27.fst) fun p =>
             m2AddrLit litsPtr p fun addr =>
             Expr.store (Arg.imm (t := i32) 0) (Arg.var addr)
               (m2Bin (OpCode.add i32) (Arg.var p27.fst) (Arg.imm 1) fun p =>
                Expr.jump Js1.fst (Arg.var p, ())))
            (Expr.group (sig := [[i32]])
              (fun Js2 =>
                Blocks.cons
                  (fun p29 =>
                    m2Cmp .ult i32 (Arg.var p29.fst) (Arg.var w) fun p30 =>
                    Expr.jnz (Arg.var p30)
                      (m2Bin (OpCode.add i32) (Arg.var shifted) (Arg.var p29.fst) fun p31 =>
                       m2AddrLit litsPtr p31 fun addr =>
                       m2Bin (OpCode.sub i32) (Arg.var p29.fst) (Arg.var s) fun p35 =>
                       m2Bin (OpCode.add i32) (Arg.var aOff) (Arg.var p35) fun p =>
                       m2LoadLit litsPtr p fun ld =>
                       Expr.store (Arg.var ld) (Arg.var addr)
                         (m2Bin (OpCode.add i32) (Arg.var p29.fst) (Arg.imm 1) fun p =>
                          Expr.jump Js2.fst (Arg.var p, ())))
                      (Expr.call (as := [i64]) (bs := [i32]) "bv_lits_mark" (Arg.var h, ())
                         fun p31 =>
                       Expr.call (as := [i64, i32, i32, i32]) (bs := [i32]) "bv_blast_add"
                         (Arg.var h, Arg.var out, Arg.var shifted, Arg.var w, ()) fun p32 =>
                       m2LoadOom h fun ld4 =>
                       m2Cmp .ne i32 (Arg.var ld4) (Arg.imm 0) fun p34 =>
                       Expr.jnz (Arg.var p34)
                         (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
                           (Arg.var h, Arg.var mark, ()) fun _ =>
                          Expr.ret (Arg.imm 4294967295, ()))
                         (mulIteExpr h w out mark ys p32.fst p31.fst litsPtr J_next)))
                  Blocks.nil)
              fun Js => Expr.jump Js.fst (Arg.var p27.fst, ())))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

/-- Outer `1 ≤ s < w` shift-and-add loop and final `bv_lits_release` of `bv_blast_mul`. -/
def mulLoopExpr (h : Val i64) (aOff bOff w out mark shifted : Val i32)
    (litsPtr : Val i64) (jInit : Val i32) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i32, i32]])
    (fun Js =>
      Blocks.cons
        (fun p20 =>
          m2Cmp .ult i32 (Arg.var p20.snd.fst) (Arg.var w) fun p21 =>
          Expr.jnz (Arg.var p21)
            (m2Bin (OpCode.add i32) (Arg.var bOff) (Arg.var p20.snd.fst) fun p22 =>
             m2LoadLit litsPtr p22 fun ld3 =>
             Expr.group (sig := [[i32]])
               (fun _ =>
                 Blocks.cons
                   (fun p =>
                     m2Bin (OpCode.add i32) (Arg.var p20.snd.fst) (Arg.imm 1) fun p26 =>
                     Expr.jump Js.fst (Arg.var p.fst, Arg.var p26, ()))
                   Blocks.nil)
               fun Js =>
               m2Cmp .ne i32 (Arg.var ld3) (Arg.imm 0) fun p26 =>
               Expr.jnz (Arg.var p26)
                 (mulIterExpr h aOff w out mark shifted p20.snd.fst ld3 litsPtr Js.fst)
                 (Expr.jump Js.fst (Arg.var p20.fst, ())))
            (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
              (Arg.var h, Arg.var mark, ()) fun _ =>
             Expr.ret (Arg.var out, ())))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.var jInit, Arg.imm 1, ())

end

/-! ## 3. Definitional Split Equations & Stage WP Lemmas -/

public section

theorem bv_blast_clz_split_eq (h : Val i64) (aOff w : Val i32) :
    bv_blast_clz_body (V := Val) (L := Cont) (h, aOff, w, ()) =
      Expr.group (sig := [[]])
        (fun _Js =>
          Blocks.cons
            (fun _ =>
              m2Add64 (Arg.var h) (Arg.imm 120) fun p =>
              Expr.store (Arg.imm (t := i32) 1) (Arg.var p) (Expr.ret (Arg.imm 4294967295, ())))
            Blocks.nil)
        fun Js =>
        m2LoadOom h fun ld =>
        m2Cmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p2 =>
        Expr.jnz (Arg.var p2) (Expr.jump Js.fst ())
          (Expr.call (as := [i64, i32, i32]) (bs := [Ty.bool])
            "bv_slice_ok" (Arg.var h, Arg.var aOff, Arg.var w, ()) fun p3 =>
           Expr.jnz (Arg.var p3.fst)
             (Expr.call (as := [i64, i32]) (bs := [i32])
               "bv_lits_alloc" (Arg.var h, Arg.var w, ()) fun p4 =>
              m2LoadOom h fun ld =>
              m2Cmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p6 =>
              Expr.jnz (Arg.var p6) (Expr.ret (Arg.imm 4294967295, ()))
                (m2Cmp .eq i32 (Arg.var w) (Arg.imm 0) fun p7 =>
                 Expr.jnz (Arg.var p7) (Expr.ret (Arg.var p4.fst, ()))
                   (m2Add64 (Arg.var h) (Arg.imm 56) fun p8 =>
                    Expr.load i64 (Arg.var p8) fun ld =>
                    Expr.group (sig := [[i32]])
                      (fun Js =>
                        Blocks.cons
                          (fun p9 =>
                            m2Cmp .ult i32 (Arg.var p9.fst) (Arg.var w) fun p10 =>
                            Expr.jnz (Arg.var p10)
                              (Expr.group (sig := [[i32]])
                                (fun _ =>
                                  Blocks.cons
                                    (fun p =>
                                      m2Bin (OpCode.add i32) (Arg.var p4.fst) (Arg.var p9.fst)
                                        fun p11 =>
                                      m2AddrLit ld p11 fun addr =>
                                      Expr.store (Arg.var p.fst) (Arg.var addr)
                                        (m2Bin (OpCode.add i32) (Arg.var p9.fst) (Arg.imm 1)
                                           fun p =>
                                         Expr.jump Js.fst (Arg.var p, ())))
                                    Blocks.nil)
                                fun Js =>
                                m2Cmp .ult i32 (Arg.var p9.fst) (Arg.imm 32) fun p11 =>
                                Expr.jnz (Arg.var p11)
                                  (m2Bin (OpCode.lshr i32) (Arg.var w) (Arg.var p9.fst) fun p =>
                                   m2Bin (OpCode.and i32) (Arg.var p) (Arg.imm 1) fun p =>
                                   Expr.jump Js.fst (Arg.var p, ()))
                                  (Expr.jump Js.fst (Arg.imm 0, ())))
                              (Expr.group (sig := [[i32, i32]])
                                (fun Js =>
                                  Blocks.cons
                                    (fun p11 =>
                                      m2Cmp .ult i32 (Arg.var p11.snd.fst) (Arg.var w) fun p12 =>
                                      Expr.jnz (Arg.var p12)
                                        (m2Bin (OpCode.add i32) (Arg.var aOff)
                                           (Arg.var p11.snd.fst) fun p13 =>
                                         m2LoadLit ld p13 fun ld1 =>
                                         Expr.group (sig := [[i32]])
                                           (fun _ =>
                                             Blocks.cons
                                               (fun p =>
                                                 m2Bin (OpCode.add i32) (Arg.var p11.snd.fst)
                                                   (Arg.imm 1) fun p17 =>
                                                 Expr.jump Js.fst
                                                   (Arg.var p.fst, Arg.var p17, ()))
                                               Blocks.nil)
                                           fun Js =>
                                           m2Cmp .ne i32 (Arg.var ld1) (Arg.imm 0) fun p17 =>
                                           Expr.jnz (Arg.var p17)
                                             (clzInnerExpr h w p4.fst ld p11.snd.fst ld1 Js.fst)
                                             (Expr.jump Js.fst (Arg.var p11.fst, ())))
                                        (Expr.ret (Arg.var p4.fst, ())))
                                    Blocks.nil)
                                fun Js => Expr.jump Js.fst (Arg.var p9.fst, Arg.imm 0, ())))
                          Blocks.nil)
                      fun Js => Expr.jump Js.fst (Arg.imm 0, ()))))
             (Expr.jump Js.fst ())) := rfl

theorem bv_blast_mul_split_eq (h : Val i64) (aOff bOff w : Val i32) :
    bv_blast_mul_body (V := Val) (L := Cont) (h, aOff, bOff, w, ()) =
      Expr.group (sig := [[]])
        (fun _Js =>
          Blocks.cons
            (fun _ =>
              m2Add64 (Arg.var h) (Arg.imm 120) fun p =>
              Expr.store (Arg.imm (t := i32) 1) (Arg.var p) (Expr.ret (Arg.imm 4294967295, ())))
            Blocks.nil)
        fun Js =>
        m2LoadOom h fun ld =>
        m2Cmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p2 =>
        Expr.jnz (Arg.var p2) (Expr.jump Js.fst ())
          (Expr.call (as := [i64, i32, i32]) (bs := [Ty.bool])
            "bv_slice_ok" (Arg.var h, Arg.var aOff, Arg.var w, ()) fun p3 =>
           Expr.jnz (Arg.var p3.fst)
             (Expr.call (as := [i64, i32, i32]) (bs := [Ty.bool])
               "bv_slice_ok" (Arg.var h, Arg.var bOff, Arg.var w, ()) fun p4 =>
              Expr.jnz (Arg.var p4.fst)
                (Expr.call (as := [i64, i32]) (bs := [i32])
                  "bv_lits_alloc" (Arg.var h, Arg.var w, ()) fun p5 =>
                 m2LoadOom h fun ld =>
                 m2Cmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p7 =>
                 Expr.jnz (Arg.var p7) (Expr.ret (Arg.imm 4294967295, ()))
                   (m2Cmp .eq i32 (Arg.var w) (Arg.imm 0) fun p8 =>
                    Expr.jnz (Arg.var p8) (Expr.ret (Arg.var p5.fst, ()))
                      (m2Add64 (Arg.var h) (Arg.imm 56) fun p9 =>
                       Expr.load i64 (Arg.var p9) fun ld =>
                       m2LoadLit ld bOff fun ld1 =>
                       Expr.group (sig := [[i32]])
                         (fun Js =>
                           Blocks.cons
                             (fun p13 =>
                               m2Cmp .ult i32 (Arg.var p13.fst) (Arg.var w) fun p14 =>
                               Expr.jnz (Arg.var p14)
                                 (m2Bin (OpCode.add i32) (Arg.var p5.fst) (Arg.var p13.fst)
                                    fun p15 =>
                                  m2AddrLit ld p15 fun addr =>
                                  m2Bin (OpCode.add i32) (Arg.var aOff) (Arg.var p13.fst) fun p =>
                                  m2LoadLit ld p fun ld2 =>
                                  Expr.call (as := [i64, i32, i32]) (bs := [i32]) "bv_mk_and"
                                    (Arg.var h, Arg.var ld1, Arg.var ld2, ()) fun p23 =>
                                  Expr.store (Arg.var p23.fst) (Arg.var addr)
                                    (m2LoadOom h fun ld =>
                                     m2Cmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p =>
                                     Expr.jnz (Arg.var p)
                                       (Expr.ret (Arg.imm 4294967295, ()))
                                       (m2Bin (OpCode.add i32) (Arg.var p13.fst) (Arg.imm 1)
                                          fun p =>
                                        Expr.jump Js.fst (Arg.var p, ()))))
                                 (m2Cmp .eq i32 (Arg.var w) (Arg.imm 1) fun p15 =>
                                  Expr.jnz (Arg.var p15) (Expr.ret (Arg.var p5.fst, ()))
                                    (Expr.call (as := [i64]) (bs := [i32]) "bv_lits_mark"
                                       (Arg.var h, ()) fun p16 =>
                                     Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc"
                                       (Arg.var h, Arg.var w, ()) fun p17 =>
                                     m2LoadOom h fun ld2 =>
                                     m2Cmp .ne i32 (Arg.var ld2) (Arg.imm 0) fun p19 =>
                                     Expr.jnz (Arg.var p19)
                                       (Expr.call (as := [i64, i32]) (bs := [])
                                          "bv_lits_release" (Arg.var h, Arg.var p16.fst, ())
                                          fun _ =>
                                        Expr.ret (Arg.imm 4294967295, ()))
                                       (mulLoopExpr h aOff bOff w p5.fst p16.fst p17.fst ld
                                          p13.fst))))
                             Blocks.nil)
                         fun Js => Expr.jump Js.fst (Arg.imm 0, ()))))
                (Expr.jump Js.fst ()))
             (Expr.jump Js.fst ())) := rfl

theorem clz_inner_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {mC : Mem 64}
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {aOff w xc : BitVec 32} {curr : Nat}
    {hdr0 hdrC : BVHdrState} {g0 gC : Aig} {awC : List (BitVec 64)}
    {htC lp0 lpC : List (BitVec 32)} {R : Mem 64 → Prop} {J_next : Cont [i32]}
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat)
    (hcurr : curr < w.toNat) (hcurr32 : (BitVec.ofNat 32 curr).toNat = curr)
    (ha_hi : aOff.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfa0 : SliceLitsWf g0 lp0 aOff.toNat w.toNat)
    (hinvC : ClzOuterInv aOff w hdr0 g0 lp0 R (curr, hdrC, gC, awC, htC, lpC) mC h)
    (hxc_eq : xc = lp0.getD (aOff.toNat + curr) 0#32)
    (hJ_next : ∀ (j : BitVec 32) (mN : Mem 64),
      (∃ hdrN gN awN htN lpN,
        ClzOuterInv aOff w hdr0 g0 lp0 R (curr + 1, hdrN, gN, awN, htN, lpN) mN h) →
      J_next (j, ()) mN)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig) (aigWords' : List (BitVec 64))
      (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ sliceOkBool hdr0 aOff w = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) va.clz) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (clzInnerExpr h w hdr0.lits_len hdr0.lits_ptr
      (BitVec.ofNat 32 curr) xc J_next) mC := by
  dsimp only [clzInnerExpr, m2Cmp, m2Bin, m2AddrLit, m2LoadLit, m2LoadOom, m2Zext, m2Add64]
  rcases hinvC with ⟨_, hfrC, hextC, haigC, hoomC, hlenC, hlpC_len, hpreC, hwfC, hevC, hmC⟩
  have hwf_xcC : (xc >>> 1).toNat < gC.A + 1 + gC.nodes.size := by
    have hsz : g0.A + 1 + g0.nodes.size ≤ gC.A + 1 + gC.nodes.size := by
      have := hextC.1; have := hextC.2.1; omega
    rw [hxc_eq]; exact Nat.lt_of_lt_of_le (hwfa0 curr hcurr) hsz
  have hval_eq : (w - (1 : BitVec 32) - BitVec.ofNat 32 curr).toNat = w.toNat - 1 - curr := by
    rw [mul2_sub_eq_toNat (by
      rw [mul2_sub_eq_toNat (by rw [show (1 : BitVec 32).toNat = 1 from rfl]; omega),
        show (1 : BitVec 32).toNat = 1 from rfl, hcurr32]
      omega),
      mul2_sub_eq_toNat (by rw [show (1 : BitVec 32).toNat = 1 from rfl]; omega),
      show (1 : BitVec 32).toNat = 1 from rfl, hcurr32]
  c0_hstraight
  refine wp_while_state (α := Nat × BVHdrState × Aig × List (BitVec 64) ×
      List (BitVec 32) × List (BitVec 32))
    (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
    (fun st mJ => ClzInnerInv aOff w curr xc hdr0 g0 lp0 R st mJ h) ?_ ?_
  · intro J_j hJ_j; c0_hsteps
    exact hJ_j (0, hdrC, gC, awC, htC, lpC) mC
      ⟨Nat.zero_le _, hfrC, hextC, haigC, hoomC, hlenC, hlpC_len, hpreC, hwf_xcC, hwfC,
        fun ρ va i hi hva => by
          rw [ite_eq_right (by omega), ← evalPoolSlice_getLsbD hi, hevC ρ va hva],
        sep_ac hmC⟩
  · intro J_j ⟨j, hdrJ, gJ, awJ, htJ, lpJ⟩ mJ hinvJ ih_j
    have hj_w := hinvJ.1
    have hj32 : (BitVec.ofNat 32 j).toNat = j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
    c0_hstraight; c0_hsplit
    · have hj_lt : j < w.toNat := by
        have h1 : BitVec.ofNat 32 j < w := hc; rw [BitVec.lt_def, hj32] at h1; exact h1
      clear hc
      rcases hinvJ with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, hwf_xcJ, hwf_sJ,
        hbefJ, hmJ⟩
      let cbit : BitVec 32 :=
        if BitVec.ofNat 32 j < 32#32 then
          (w - (1 : BitVec 32) - BitVec.ofNat 32 curr) >>> BitVec.ofNat 32 j &&& 1#32
        else 0#32
      refine wp_join_state (α := BitVec 32) (fun c => (c, ()))
        (fun c mCb => c = cbit ∧ mCb = mJ) ?_ ?_
      · intro _ cb mCb ⟨hcb, hmCb⟩; subst hcb hmCb
        have houtj_sw : ((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
            hdr0.lits_len.toNat + j := by
          rw [mul2_setWidth64_toNat, BitVec.toNat_add, hj32,
            Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
        have hout_ag :
            lpJ[((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat]'(by
              rw [houtj_sw, hlpJ_len, hcap0]; omega) =
            lpJ.getD (hdr0.lits_len.toNat + j) 0#32 := by
          rw [← mul2_getD_eq_getElem lpJ (by rw [houtj_sw, hlpJ_len, hcap0]; omega), houtj_sw]
        have hwf_cb : (cbit >>> 1).toNat < gJ.A + 1 + gJ.nodes.size := by
          dsimp only [cbit]; split
          · exact mul2_clz_bitSelect_wf gJ _ _
          · exact SliceLitsWf.zero_shr1 gJ
        c0_hstraight; c0_hcall hIte
        refine ⟨hdrJ, gJ, awJ, htJ, array (t := i32) hdr0.lits_ptr lpJ ⋆ R, haigJ,
          fun _ => ⟨by rw [haigJ.aig_len_eq]; exact hwf_xcJ,
            by rw [haigJ.aig_len_eq]; exact hwf_cb,
            by rw [hout_ag, haigJ.aig_len_eq]; exact hwf_sJ j hj_lt⟩,
          sep_ac hmJ,
          fun ret hdrN gN awN htN mN hfrN hextN _ haigN hoomN _ hevN hmN => ?_⟩
        have hfr0N := hfrJ.trans hfrN.toOpsFrame
        have hext0N := Aig.extends_trans hextJ hextN
        have hlenN : hdrN.lits_len = hdr0.lits_len + w := hfrN.lits_len.trans hlenJ
        rw [← hfrJ.lits_ptr] at hmN
        have hmN' := ops_aig_frame_unfocus hfrN.toOpsFrame hmN
        rw [hfr0N.lits_ptr] at hmN'
        c0_hstraight
        rw [houtj_sw] at hm
        c0_hsplit
        · have hoom_ne : hdrN.oom ≠ 0#32 := by c0_bv_omega [hc]
          clear hc; c0_hsteps; rw [← hfr0N.lits_ptr] at hm
          exact clz_oom_close (lp' := lpJ.set (hdr0.lits_len.toNat + j) ret)
            hfr0N hext0N haigN (by simp [hlpJ_len])
            (by rw [hlenN, hl1_eq]; omega) (by rw [hlenN, hl1_eq, hfr0N.lits_cap]; omega)
            (fun q hq => by
              rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
                ← List.getD_eq_getElem?_getD]
              exact hpreJ q hq)
            hoom_ne (sep_ac hm) hQ
        · have hoomN0 : hdrN.oom = 0#32 := by c0_bv_omega [hc]
          clear hc; c0_hsteps
          obtain ⟨hret_bd, hret_ev⟩ := hevN hoomN0
          rw [haigN.aig_len_eq] at hret_bd
          have hstep := clz_ite_step_ok hlpJ_len hpreJ hwf_xcJ hxc_eq hwfa0 hwf_sJ hbefJ hval_eq
            hcurr hj_lt hj32 (by rw [hlpJ_len, hcap0]; omega) (by rw [hcap0]; omega) hextJ
            hextN hret_bd (fun ρ => by rw [hret_ev ρ]; dsimp only; rw [hout_ag]) rfl
          rw [mul2_bv32_succ_add (by have := w.isLt; omega)]
          exact ih_j (j + 1, hdrN, gN, awN, htN, _) _ (by dsimp only; omega)
            ⟨by omega, hfr0N, hext0N, haigN, hoomN0, hlenN, hstep.1, hstep.2.1, hstep.2.2.1,
              hstep.2.2.2.1, hstep.2.2.2.2, sep_ac hm⟩
      · intro J_cb hJ_cb; c0_hstraight; c0_hsplit
        · have hj32_lt : BitVec.ofNat 32 j < 32#32 := hc
          clear hc; c0_hsteps
          have hmod : (BitVec.ofNat 32 j).toNat % 32 = (BitVec.ofNat 32 j).toNat :=
            Nat.mod_eq_of_lt (BitVec.lt_def.mp hj32_lt)
          exact hJ_cb _ mJ ⟨by dsimp only [cbit]; rw [ite_eq_left hj32_lt, hmod]; rfl, rfl⟩
        · have hj32_ge : ¬ BitVec.ofNat 32 j < 32#32 := hc
          clear hc; c0_hsteps
          exact hJ_cb 0#32 mJ ⟨by dsimp only [cbit]; rw [ite_eq_right hj32_ge], rfl⟩
    · have hj_eq : j = w.toNat := by
        have h1 : ¬ BitVec.ofNat 32 j < w := hc; rw [BitVec.lt_def, hj32] at h1; omega
      clear hc; subst hj_eq
      exact hJ_next _ mJ ⟨hdrJ, gJ, awJ, htJ, lpJ, clzInnerInv_done hcurr hinvJ⟩

theorem mul_ite_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {mA : Mem 64}
    (hRel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {aOff bOff w ys added : BitVec 32} {s : Nat}
    {hdr0 hdrA : BVHdrState} {g0 gA : Aig} {awA : List (BitVec 64)}
    {htA lp0 lpA : List (BitVec 32)} {R : Mem 64 → Prop} {J_rel : Cont [i32]}
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (_hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (_hfit2 : w.toNat ≤ hdr0.lits_cap.toNat - (hdr0.lits_len + w).toNat)
    (hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat)
    (hl2_eq : (hdr0.lits_len + w + w).toNat = hdr0.lits_len.toNat + w.toNat + w.toNat)
    (hs1 : 1 ≤ s) (hs_lt : s < w.toNat)
    (hb_hi : bOff.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfb0 : SliceLitsWf g0 lp0 bOff.toNat w.toNat)
    (hys_eq : ys = lp0.getD (bOff.toNat + s) 0#32)
    (hadded_eq : added = hdr0.lits_len + w + w)
    (hadded_fit : hdr0.lits_len.toNat + w.toNat + w.toNat + w.toNat ≤ hdr0.lits_cap.toNat)
    (hinvA : MulIteInv aOff bOff w s ys added hdr0 g0 lp0 R
      (0, hdrA, gA, awA, htA, lpA) mA h)
    (hJ_rel : ∀ (jNext : BitVec 32) (mR : Mem 64),
      (∃ hdrR gR awR htR lpR,
        MulOuterInv aOff bOff w hdr0 g0 lp0 R (s + 1, hdrR, gR, awR, htR, lpR) mR h) →
      J_rel (jNext, ()) mR)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig) (aigWords' : List (BitVec 64))
      (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ true = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff w = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ true = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff w = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (va * vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (mulIteExpr h w hdr0.lits_len (hdr0.lits_len + w) ys added
      (hdr0.lits_len + w + w) hdr0.lits_ptr J_rel) mA := by
  dsimp only [mulIteExpr, m2Cmp, m2Bin, m2AddrLit, m2LoadLit, m2LoadOom, m2Zext, m2Add64]
  have hadded_n : added.toNat = hdr0.lits_len.toNat + w.toNat + w.toNat := by
    rw [hadded_eq, hl2_eq]
  refine wp_while_state (α := Nat × BVHdrState × Aig × List (BitVec 64) ×
      List (BitVec 32) × List (BitVec 32))
    (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
    (fun st mJ => MulIteInv aOff bOff w s ys added hdr0 g0 lp0 R st mJ h) ?_ ?_
  · intro J_j hJ_j; c0_hsteps
    exact hJ_j (0, hdrA, gA, awA, htA, lpA) mA hinvA
  · intro J_j ⟨j, hdrJ, gJ, awJ, htJ, lpJ⟩ mJ hinvJ ih_j
    have hj_w := hinvJ.1
    have hj32 : (BitVec.ofNat 32 j).toNat = j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
    c0_hstraight; c0_hsplit
    · have hj_lt : j < w.toNat := by
        have h1 : BitVec.ofNat 32 j < w := hc; rw [BitVec.lt_def, hj32] at h1; exact h1
      clear hc
      rcases hinvJ with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, hwf_ysJ,
        hwf_addJ, hwf_outJ, hev_addJ, hbefJ, hmJ⟩
      have haddj_sw : ((added + BitVec.ofNat 32 j).setWidth 64).toNat = added.toNat + j := by
        rw [mul2_setWidth64_toNat, BitVec.toNat_add, hj32, hadded_n,
          Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
      have houtj_sw : ((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
          hdr0.lits_len.toNat + j := by
        rw [mul2_setWidth64_toNat, BitVec.toNat_add, hj32,
          Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
      have hadd_ag :
          lpJ[((added + BitVec.ofNat 32 j).setWidth 64).toNat]'(by
            rw [haddj_sw, hlpJ_len, hcap0]; omega) =
          lpJ.getD (added.toNat + j) 0#32 := by
        rw [← mul2_getD_eq_getElem lpJ (by rw [haddj_sw, hlpJ_len, hcap0]; omega), haddj_sw]
      have hout_ag :
          lpJ[((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat]'(by
            rw [houtj_sw, hlpJ_len, hcap0]; omega) =
          lpJ.getD (hdr0.lits_len.toNat + j) 0#32 := by
        rw [← mul2_getD_eq_getElem lpJ (by rw [houtj_sw, hlpJ_len, hcap0]; omega), houtj_sw]
      c0_hstraight; c0_hcall hIte
      refine ⟨hdrJ, gJ, awJ, htJ, array (t := i32) hdr0.lits_ptr lpJ ⋆ R, haigJ,
        fun _ => ⟨by rw [haigJ.aig_len_eq]; exact hwf_ysJ,
          by rw [hadd_ag, haigJ.aig_len_eq]; exact hwf_addJ j hj_lt,
          by rw [hout_ag, haigJ.aig_len_eq]; exact hwf_outJ j hj_lt⟩,
        sep_ac hmJ,
        fun ret hdrN gN awN htN mN hfrN hextN _ haigN hoomN _ hevN hmN => ?_⟩
      have hfr0N := hfrJ.trans hfrN.toOpsFrame
      have hext0N := Aig.extends_trans hextJ hextN
      have hlenN : hdrN.lits_len = hdr0.lits_len + w + w + w := hfrN.lits_len.trans hlenJ
      rw [← hfrJ.lits_ptr] at hmN
      have hmN' := ops_aig_frame_unfocus hfrN.toOpsFrame hmN
      rw [hfr0N.lits_ptr] at hmN'
      c0_hstraight
      rw [houtj_sw] at hm
      c0_hsplit
      · have hoom_ne : hdrN.oom ≠ 0#32 := by c0_bv_omega [hc]
        clear hc
        have hlenN_n : hdrN.lits_len.toNat =
            hdr0.lits_len.toNat + w.toNat + w.toNat + w.toNat := by
          rw [hlenN, BitVec.toNat_add, hl2_eq,
            Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
        c0_hcall hRel
        refine ⟨hdrN, array64 hdrN.aig_ptr awN ⋆ array (t := i32) hdrN.ht_ptr htN ⋆
          array (t := i32) hdr0.lits_ptr _ ⋆ R, sep_ac hm, fun mO hmO => ?_⟩
        rw [ite_eq_left (by rw [hl1_eq, hlenN_n]; omega)] at hmO
        c0_hsteps
        have hfrO := mul2_opsFrame_with_lits_len hfr0N (hdr0.lits_len + w)
        have haigO := mul2_aigInv_with_lits_len haigN (hdr0.lits_len + w)
        rw [← hfr0N.lits_ptr] at hmO
        exact mul_oom_close (hdr' := { hdrN with lits_len := hdr0.lits_len + w })
          (lp' := lpJ.set (hdr0.lits_len.toNat + j) ret)
          hfrO hext0N haigO (by simp [hlpJ_len])
          (by dsimp only; rw [hl1_eq]; omega)
          (by dsimp only; rw [hl1_eq, hfr0N.lits_cap]; omega)
          (fun q hq => by
            rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
              ← List.getD_eq_getElem?_getD]
            exact hpreJ q hq)
          hoom_ne (sep_ac hmO) hQ
      · have hoomN0 : hdrN.oom = 0#32 := by c0_bv_omega [hc]
        clear hc; c0_hsteps
        obtain ⟨hret_bd, hret_ev⟩ := hevN hoomN0
        rw [haigN.aig_len_eq] at hret_bd
        have hstep := mul_ite_step_ok hlpJ_len hpreJ hwf_ysJ hys_eq hwfb0 hwf_addJ hwf_outJ
          hev_addJ hbefJ hs1 hs_lt hj_lt (by rw [hadded_n]; omega)
          (by rw [hlpJ_len, hcap0]; omega) (by rw [hcap0]; omega) hextJ hextN hret_bd
          (fun ρ => by rw [hret_ev ρ]; dsimp only; rw [hadd_ag, hout_ag]) rfl
        rw [mul2_bv32_succ_add (by have := w.isLt; omega)]
        exact ih_j (j + 1, hdrN, gN, awN, htN, _) _ (by dsimp only; omega)
          ⟨by omega, hfr0N, hext0N, haigN, hoomN0, hlenN, hstep.1, hstep.2.1, hstep.2.2.1,
            hstep.2.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.2.2.1, hstep.2.2.2.2.2.2, sep_ac hm⟩
    · have hj_eq : j = w.toNat := by
        have h1 : ¬ BitVec.ofNat 32 j < w := hc; rw [BitVec.lt_def, hj32] at h1; omega
      clear hc; subst hj_eq
      rcases hinvJ with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, hwf_ysJ,
        hwf_addJ, hwf_outJ, hev_addJ, hbefJ, hmJ⟩
      have hlenJ_n : hdrJ.lits_len.toNat =
          hdr0.lits_len.toNat + w.toNat + w.toNat + w.toNat := by
        rw [hlenJ, BitVec.toNat_add, hl2_eq,
          Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
      c0_hcall hRel
      refine ⟨hdrJ, array64 hdrJ.aig_ptr awJ ⋆ array (t := i32) hdrJ.ht_ptr htJ ⋆
        array (t := i32) hdr0.lits_ptr lpJ ⋆ R, sep_ac hmJ, fun mR hmR => ?_⟩
      rw [ite_eq_left (by rw [hl2_eq, hlenJ_n]; omega)] at hmR
      c0_hsteps
      have hdone := mulIteInv_done hs1 hs_lt hfrJ.lits_ptr
        ⟨Nat.le_refl _, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, hwf_ysJ, hwf_addJ,
          hwf_outJ, hev_addJ, hbefJ, hmJ⟩
      exact hJ_rel _ mR ⟨_, gJ, awJ, htJ, lpJ, hdone mR (sep_ac hmR)⟩

theorem mul_iter_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {mS : Mem 64}
    (hMark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (hRel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hAdd : Γ.Has "bv_blast_add" smBvBlastAddSpec)
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {aOff bOff w ys : BitVec 32} {s : Nat}
    {hdr0 hdrS : BVHdrState} {g0 gS : Aig} {awS : List (BitVec 64)}
    {htS lp0 lpS : List (BitVec 32)} {R : Mem 64 → Prop} {J_next : Cont [i32]}
    (_hoom0 : hdr0.oom = 0#32)
    (hsla : sliceOkBool hdr0 aOff w = true) (hslb : sliceOkBool hdr0 bOff w = true)
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hfit2 : w.toNat ≤ hdr0.lits_cap.toNat - (hdr0.lits_len + w).toNat)
    (hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat)
    (hl2_eq : (hdr0.lits_len + w + w).toNat = hdr0.lits_len.toNat + w.toNat + w.toNat)
    (hs1 : 1 ≤ s) (hs_lt : s < w.toNat) (hs32 : (BitVec.ofNat 32 s).toNat = s)
    (ha_hi : aOff.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hb_hi : bOff.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfa0 : SliceLitsWf g0 lp0 aOff.toNat w.toNat)
    (hwfb0 : SliceLitsWf g0 lp0 bOff.toNat w.toNat)
    (hys_eq : ys = lp0.getD (bOff.toNat + s) 0#32)
    (hinvS : MulOuterInv aOff bOff w hdr0 g0 lp0 R (s, hdrS, gS, awS, htS, lpS) mS h)
    (hJ_next : ∀ (jNext : BitVec 32) (mR : Mem 64),
      (∃ hdrR gR awR htR lpR,
        MulOuterInv aOff bOff w hdr0 g0 lp0 R (s + 1, hdrR, gR, awR, htR, lpR) mR h) →
      J_next (jNext, ()) mR)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig) (aigWords' : List (BitVec 64))
      (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ true = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff w = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ true = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff w = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (va * vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (mulIterExpr h aOff w hdr0.lits_len (hdr0.lits_len + w) (hdr0.lits_len + w)
      (BitVec.ofNat 32 s) ys hdr0.lits_ptr J_next) mS := by
  have _ := hslb
  have hlen0_cap : hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat := by
    unfold sliceOkBool at hsla; simp only [decide_eq_true_eq] at hsla; exact hsla.1
  dsimp only [mulIterExpr, m2Cmp, m2Bin, m2AddrLit, m2LoadLit, m2LoadOom, m2Zext, m2Add64]
  rcases hinvS with ⟨_, _, hfrS, hextS, haigS, hoomS, hlenS, hlpS_len, hpreS, hwfS, hevS, hmS⟩
  refine wp_while_state (α := Nat × List (BitVec 32))
    (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => s - j)
    (fun st mZ =>
      MulZeroInv aOff bOff w s hdr0 hdrS g0 gS awS htS lp0 R st mZ h) ?_ ?_
  · intro J_z hJ_z; c0_hsteps
    exact hJ_z (0, lpS) mS ⟨Nat.zero_le _, hlpS_len,
      fun q hq => by
        by_cases hq0 : q < hdr0.lits_len.toNat
        · exact Or.inl (hpreS q hq0)
        · exact Or.inr ⟨by omega, hq⟩,
      hpreS, hwfS, hevS, fun _ hk => by omega, sep_ac hmS⟩
  · intro J_z ⟨j, lpZ⟩ mZ hinvZ ih_z
    have hj_s := hinvZ.1
    have hj32 : (BitVec.ofNat 32 j).toNat = j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
    c0_hstraight; c0_hsplit
    · have hj_lt : j < s := by
        have h1 : BitVec.ofNat 32 j < BitVec.ofNat 32 s := hc
        rw [BitVec.lt_def, hj32, hs32] at h1; exact h1
      clear hc
      rcases hinvZ with ⟨_, hlpZ_len, _, hpreZ, hwfZ, hevZ, hzerosZ, hmZ⟩
      have hshj_sw : ((hdr0.lits_len + w + BitVec.ofNat 32 j).setWidth 64).toNat =
          hdr0.lits_len.toNat + w.toNat + j := by
        rw [mul2_setWidth64_toNat, BitVec.toNat_add, hj32, hl1_eq,
          Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
      c0_hsteps
      rw [hshj_sw] at hm
      have hstep := mul_zero_step_ok hlpZ_len hpreZ hwfZ hevZ hzerosZ hj_lt (by omega)
        (by rw [hlpZ_len, hcap0]; omega)
      rw [mul2_bv32_succ_add (by have := w.isLt; omega)]
      exact ih_z (j + 1, _) _ (by dsimp only; omega)
        ⟨by omega, hstep.1, fun q hq => by
            by_cases hq0 : q < hdr0.lits_len.toNat
            · exact Or.inl (hstep.2.1 q hq0)
            · exact Or.inr ⟨by omega, hq⟩,
          hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2, sep_ac hm⟩
    · have hj_eq : j = s := by
        have h1 : ¬ BitVec.ofNat 32 j < BitVec.ofNat 32 s := hc
        rw [BitVec.lt_def, hj32, hs32] at h1; omega
      clear hc; subst j
      rcases hinvZ with ⟨_, hlpZ_len, _, hpreZ, hwfZ, hevZ, hzerosZ, hmZ⟩
      refine wp_while_state (α := Nat × List (BitVec 32))
        (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
        (fun st mC =>
          MulCopyInv aOff bOff w s hdr0 hdrS g0 gS awS htS lp0 R st mC h) ?_ ?_
      · intro J_c hJ_c; c0_hsteps
        exact hJ_c (s, lpZ) mZ ⟨Nat.le_refl _, by omega, hlpZ_len, hpreZ, hwfZ, hevZ, hzerosZ,
          fun _ h1 h2 => by omega, sep_ac hmZ⟩
      · intro J_c ⟨j, lpC⟩ mC hinvC ih_c
        have hj_w := hinvC.2.1
        have hj32 : (BitVec.ofNat 32 j).toNat = j := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
        c0_hstraight; c0_hsplit
        · have hj_lt : j < w.toNat := by
            have h1 : BitVec.ofNat 32 j < w := hc; rw [BitVec.lt_def, hj32] at h1; exact h1
          clear hc
          rcases hinvC with ⟨hs_j, _, hlpC_len, hpreC, hwfC, hevC, hzerosC, hcopiesC, hmC⟩
          have hsub_to : (BitVec.ofNat 32 j - BitVec.ofNat 32 s).toNat = j - s := by
            rw [mul2_sub_eq_toNat (by rw [hj32, hs32]; exact hs_j), hj32, hs32]
          have hshj_sw : ((hdr0.lits_len + w + BitVec.ofNat 32 j).setWidth 64).toNat =
              hdr0.lits_len.toNat + w.toNat + j := by
            rw [mul2_setWidth64_toNat, BitVec.toNat_add, hj32, hl1_eq,
              Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
          have hasub_sw :
              ((aOff + (BitVec.ofNat 32 j - BitVec.ofNat 32 s)).setWidth 64).toNat =
                aOff.toNat + (j - s) := by
            rw [mul2_setWidth64_toNat, BitVec.toNat_add, hsub_to,
              Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
          c0_hsteps
          dsimp only at hm
          simp only [hshj_sw, hasub_sw] at hm
          rw [← mul2_getD_eq_getElem lpC (by rw [hlpC_len, hcap0]; omega)] at hm
          have hstep := mul_copy_step_ok hlpC_len hpreC hwfC hevC hzerosC hcopiesC ha_hi hs_j
            hj_lt (by rw [hlpC_len, hcap0]; omega)
          rw [mul2_bv32_succ_add (by have := w.isLt; omega)]
          exact ih_c (j + 1, _) _ (by dsimp only; omega)
            ⟨by omega, by omega, hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
              hstep.2.2.2.2.1, hstep.2.2.2.2.2, sep_ac hm⟩
        · have hj_eq : j = w.toNat := by
            have h1 : ¬ BitVec.ofNat 32 j < w := hc; rw [BitVec.lt_def, hj32] at h1; omega
          clear hc; subst j
          rcases hinvC with ⟨_, _, hlpC_len, hpreC, hwfC, hevC, hzerosC, hcopiesC, hmC⟩
          have hsh_pair := mul_shifted_wf_eval hs_lt hextS hwfa0 hpreC ha_hi
            (by rw [hcap0]; omega) hzerosC hcopiesC
          c0_hcall hMark
          refine ⟨hdrS, array64 hdrS.aig_ptr awS ⋆ array (t := i32) hdrS.ht_ptr htS ⋆
            array (t := i32) hdr0.lits_ptr lpC ⋆ R, sep_ac hmC, ?_⟩
          rw [hlenS]
          have hsl_out : sliceOkBool hdrS hdr0.lits_len w = true := by
            unfold sliceOkBool at hsla ⊢
            simp only [decide_eq_true_eq] at hsla ⊢
            refine ⟨by rw [hlenS, hl2_eq, hfrS.lits_cap]; omega,
              fun hw => by rw [hfrS.lits_ptr]; exact hsla.2.1 hw,
              by rw [hlenS, hl2_eq]; omega, by rw [hlenS, hl2_eq]; omega⟩
          have hsl_sh : sliceOkBool hdrS (hdr0.lits_len + w) w = true := by
            unfold sliceOkBool at hsla ⊢
            simp only [decide_eq_true_eq] at hsla ⊢
            refine ⟨by rw [hlenS, hl2_eq, hfrS.lits_cap]; omega,
              fun hw => by rw [hfrS.lits_ptr]; exact hsla.2.1 hw,
              by rw [hlenS, hl2_eq, hl1_eq]; omega, by rw [hlenS, hl2_eq, hl1_eq]; omega⟩
          c0_hcall hAdd
          refine ⟨hdrS, gS, awS, htS, lpC, R, haigS,
            (by rw [hlpC_len, hcap0, hfrS.lits_cap]), fun _ => ⟨hoomS, rfl, hsl_out, hsl_sh⟩,
            fun _ _ _ _ => ⟨hwfC, by rw [hl1_eq]; exact hsh_pair.1⟩,
            by rw [hfrS.lits_ptr]; exact sep_ac hmC,
            fun ret hdrA gA awA htA lpA mA hfrA hextA haigA hlpA hlenA1 hlenA2 hpreA
              hfailA hoomA hokA hmA => ?_⟩
          have hfr0A := hfrS.trans hfrA
          have hext0A := Aig.extends_trans hextS hextA
          rw [hfr0A.lits_ptr] at hmA
          c0_hstraight; c0_hsplit
          · have hoom_ne : hdrA.oom ≠ 0#32 := by c0_bv_omega [hc]
            clear hc
            c0_hcall hRel
            refine ⟨hdrA, array64 hdrA.aig_ptr awA ⋆ array (t := i32) hdrA.ht_ptr htA ⋆
              array (t := i32) hdr0.lits_ptr lpA ⋆ R, sep_ac hmA, fun mO hmO => ?_⟩
            rw [ite_eq_left (by rw [hl1_eq]; have := hlenS; rw [this, hl2_eq] at hlenA1; omega)]
              at hmO
            c0_hsteps
            have hfrO := mul2_opsFrame_with_lits_len hfr0A (hdr0.lits_len + w)
            have haigO := mul2_aigInv_with_lits_len haigA (hdr0.lits_len + w)
            rw [← hfr0A.lits_ptr] at hmO
            exact mul_oom_close hfrO hext0A haigO (hlpA.trans hlpC_len)
              (by dsimp only; rw [hl1_eq]; omega)
              (by dsimp only; rw [hl1_eq, hfr0A.lits_cap]; omega)
              (fun q hq => by
                have h1 := hpreA q (by rw [hlenS, hl2_eq]; omega)
                exact h1.trans (hpreC q hq))
              hoom_ne (sep_ac hmO) hQ
          · have hoomA0 : hdrA.oom = 0#32 := by c0_bv_omega [hc]
            clear hc
            obtain ⟨_, _, _, _, hret_eq, hlenA, hwf_add, hsemA⟩ := hokA hoomA0
            have hcapA : hdrS.lits_len.toNat ≤ hdrS.lits_cap.toNat := by
              rw [hlenS, hl2_eq, hfrS.lits_cap]; omega
            have hlenA_cap := hlenA2 hcapA
            have hno_wrap : hdrS.lits_len.toNat + w.toNat < 2 ^ 32 := by
              have hw32 := w.isLt
              rw [hlenA, BitVec.toNat_add] at hlenA1
              rcases Nat.lt_or_ge (hdrS.lits_len.toNat + w.toNat) (2 ^ 32) with hlt | hge
              · exact hlt
              · have hlt2 : (hdrS.lits_len.toNat + w.toNat) % 2 ^ 32 < hdrS.lits_len.toNat := by
                  rw [Nat.mod_eq_sub_mod (by omega)]
                  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
                omega
            have hadded_fit :
                hdr0.lits_len.toNat + w.toNat + w.toNat + w.toNat ≤ hdr0.lits_cap.toNat := by
              rw [← hfr0A.lits_cap, ← hl2_eq, ← hlenS]
              have := hlenA_cap
              rw [hlenA, BitVec.toNat_add, Nat.mod_eq_of_lt hno_wrap] at this
              exact this
            have hlenA_eq : hdrA.lits_len = hdr0.lits_len + w + w + w := by
              rw [hlenA, hlenS]
            have hwf_ysA : (ys >>> 1).toNat < gA.A + 1 + gA.nodes.size := by
              have hsz : g0.A + 1 + g0.nodes.size ≤ gA.A + 1 + gA.nodes.size := by
                have := hext0A.1; have := hext0A.2.1; omega
              rw [hys_eq]; exact Nat.lt_of_lt_of_le (hwfb0 s hs_lt) hsz
            have hpreA_out : ∀ q < hdr0.lits_len.toNat + w.toNat,
                lpA.getD q 0#32 = lpC.getD q 0#32 :=
              fun q hq => hpreA q (by rw [hlenS, hl2_eq]; omega)
            have hinv_ite : MulIteInv aOff bOff w s ys ret hdr0 g0 lp0 R
                (0, hdrA, gA, awA, htA, lpA) mA h := by
              refine ⟨Nat.zero_le _, hfr0A, hext0A, haigA, hoomA0, hlenA_eq,
                hlpA.trans hlpC_len, fun q hq => (hpreA_out q (by omega)).trans (hpreC q hq),
                hwf_ysA, hwf_add,
                SliceLitsWf.of_agree (fun k hk => hpreA_out (hdr0.lits_len.toNat + k) (by omega))
                  (hwfC.extend hextA),
                fun ρ va vb hva hvb => ?_, fun ρ va vb i hi hva hvb => ?_, sep_ac hmA⟩
              · have ha_den : SliceDenotes gS ρ (litsSlice lpC hdr0.lits_len.toNat w.toNat)
                    (va.mulRec vb (s - 1)) := by
                  rw [← hevC ρ va vb hva hvb]
                  exact sliceDenotes_evalPoolSlice (by rw [hlpC_len, hcap0]; omega)
                have hs_den : SliceDenotes gS ρ
                    (litsSlice lpC (hdr0.lits_len + w).toNat w.toNat) (va <<< s) := by
                  rw [hl1_eq, ← hsh_pair.2 ρ va hva]
                  exact sliceDenotes_evalPoolSlice (by rw [hlpC_len, hcap0]; omega)
                have hsd := hsemA ρ (va.mulRec vb (s - 1)) (va <<< s) ha_den hs_den
                apply BitVec.eq_of_getLsbD_eq
                intro i hi
                rw [evalPoolSlice_getLsbD hi,
                  ← litsSlice_getD (by rw [hlpA, hlpC_len, hcap0, hret_eq, hlenS, hl2_eq]; omega)
                    hi]
                exact hsd.2 i hi
              · rw [ite_eq_right (by omega), hpreA_out (hdr0.lits_len.toNat + i) (by omega),
                  Aig.evalLit_extend_node hextA (by rw [ofBv_shr1_toNat]; exact hwfC i hi),
                  ← evalPoolSlice_getLsbD hi, hevC ρ va vb hva hvb]
            exact mul_ite_wp hRel hIte hcap0 hfit1 hfit2 hl1_eq hl2_eq hs1 hs_lt hb_hi hwfb0
              hys_eq (hret_eq.trans hlenS) hadded_fit hinv_ite hJ_next hQ

theorem mul_loop_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {m0 : Mem 64}
    (hMark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (hRel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hAdd : Γ.Has "bv_blast_add" smBvBlastAddSpec)
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {aOff bOff w : BitVec 32} {jInit : BitVec 32}
    {hdr0 hdrS0 : BVHdrState} {g0 gS0 : Aig} {awS0 : List (BitVec 64)}
    {htS0 lp0 lpS0 : List (BitVec 32)} {R : Mem 64 → Prop}
    (hoom0 : hdr0.oom = 0#32)
    (hsla : sliceOkBool hdr0 aOff w = true) (hslb : sliceOkBool hdr0 bOff w = true)
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hfit2 : w.toNat ≤ hdr0.lits_cap.toNat - (hdr0.lits_len + w).toNat)
    (hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat)
    (hl2_eq : (hdr0.lits_len + w + w).toNat = hdr0.lits_len.toNat + w.toNat + w.toNat)
    (hw_gt1 : 1 < w.toNat)
    (ha_hi : aOff.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hb_hi : bOff.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfa0 : SliceLitsWf g0 lp0 aOff.toNat w.toNat)
    (hwfb0 : SliceLitsWf g0 lp0 bOff.toNat w.toNat)
    (hinv0 : MulOuterInv aOff bOff w hdr0 g0 lp0 R (1, hdrS0, gS0, awS0, htS0, lpS0) m0 h)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig) (aigWords' : List (BitVec 64))
      (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ true = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff w = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ true = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff w = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (va * vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (mulLoopExpr h aOff bOff w hdr0.lits_len (hdr0.lits_len + w)
      (hdr0.lits_len + w) hdr0.lits_ptr jInit) m0 := by
  dsimp only [mulLoopExpr, m2Cmp, m2Bin, m2AddrLit, m2LoadLit, m2LoadOom, m2Zext, m2Add64]
  refine wp_while_state (α := BitVec 32 × Nat × BVHdrState × Aig ×
      List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (fun (jd, s, _) => (jd, BitVec.ofNat 32 s, ())) (fun (_, s, _) => w.toNat - s)
    (fun (_, s, st) mS => MulOuterInv aOff bOff w hdr0 g0 lp0 R (s, st) mS h) ?_ ?_
  · intro J_s hJ_s; c0_hsteps
    exact hJ_s (jInit, 1, hdrS0, gS0, awS0, htS0, lpS0) m0 hinv0
  · intro J_s ⟨jd, s, hdrS, gS, awS, htS, lpS⟩ mS hinvS ih_s
    have hs1 := hinvS.1
    have hs_w := hinvS.2.1
    have hs32 : (BitVec.ofNat 32 s).toNat = s := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
    c0_hstraight; c0_hsplit
    · have hs_lt : s < w.toNat := by
        have h1 : BitVec.ofNat 32 s < w := hc; rw [BitVec.lt_def, hs32] at h1; exact h1
      clear hc
      rcases hinvS with ⟨_, _, hfrS, hextS, haigS, hoomS, hlenS, hlpS_len, hpreS, hwfS, hevS, hmS⟩
      have hbs_sw : ((bOff + BitVec.ofNat 32 s).setWidth 64).toNat = bOff.toNat + s := by
        rw [mul2_setWidth64_toNat, BitVec.toNat_add, hs32,
          Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
      have hbs_ag :
          lpS[((bOff + BitVec.ofNat 32 s).setWidth 64).toNat]'(by
            rw [hbs_sw, hlpS_len, hcap0]; omega) =
          lp0.getD (bOff.toNat + s) 0#32 := by
        rw [← mul2_getD_eq_getElem lpS (by rw [hbs_sw, hlpS_len, hcap0]; omega), hbs_sw]
        exact hpreS _ (by omega)
      c0_hstraight
      refine wp_join_state (α := BitVec 32) (fun jn => (jn, ()))
        (fun _ mR => ∃ hdrR gR awR htR lpR,
          MulOuterInv aOff bOff w hdr0 g0 lp0 R (s + 1, hdrR, gR, awR, htR, lpR) mR h) ?_ ?_
      · intro _ jn mR ⟨hdrR, gR, awR, htR, lpR, hinvR⟩
        c0_hsteps
        rw [mul2_bv32_succ_add (by have := w.isLt; omega)]
        exact ih_s (jn, s + 1, hdrR, gR, awR, htR, lpR) mR (by dsimp only; omega) hinvR
      · intro J_next hJ_next
        c0_hstraight; c0_hsplit
        · have hys_ne : lpS[((bOff + BitVec.ofNat 32 s).setWidth 64).toNat]'(by
              rw [hbs_sw, hlpS_len, hcap0]; omega) ≠ 0#32 := by
            c0_bv_omega [hc]
          clear hc
          exact mul_iter_wp hMark hRel hAdd hIte hoom0 hsla hslb hcap0 hfit1 hfit2 hl1_eq hl2_eq
            hs1 hs_lt hs32 ha_hi hb_hi hwfa0 hwfb0 hbs_ag
            ⟨hs1, hs_w, hfrS, hextS, haigS, hoomS, hlenS, hlpS_len, hpreS, hwfS, hevS, hmS⟩
            (fun jn mR hinvR => hJ_next jn mR hinvR) hQ
        · have hys0 : lp0.getD (bOff.toNat + s) 0#32 = 0#32 := by
            rw [← hbs_ag]; c0_bv_omega [hc]
          clear hc
          exact hJ_next jd mS ⟨hdrS, gS, awS, htS, lpS, by
            refine ⟨by omega, by omega, hfrS, hextS, haigS, hoomS, hlenS, hlpS_len, hpreS,
              hwfS, ?_, hmS⟩
            have hys0' : lpS.getD (bOff.toNat + s) 0#32 = 0#32 := by
              rw [hpreS _ (by omega)]; exact hys0
            exact mul_skip_step_ok hys0' hpreS hb_hi (by rw [hcap0]; omega) hs1 hs_lt hevS⟩
    · have hs_eq : s = w.toNat := by
        have h1 : ¬ BitVec.ofNat 32 s < w := hc; rw [BitVec.lt_def, hs32] at h1; omega
      clear hc; subst hs_eq
      rcases hinvS with ⟨_, _, hfrS, hextS, haigS, hoomS, hlenS, hlpS_len, hpreS, hwfS, hevS, hmS⟩
      c0_hcall hRel
      refine ⟨hdrS, array64 hdrS.aig_ptr awS ⋆ array (t := i32) hdrS.ht_ptr htS ⋆
        array (t := i32) hdr0.lits_ptr lpS ⋆ R, sep_ac hmS, fun mR hmR => ?_⟩
      rw [ite_eq_left (by rw [hlenS, hl1_eq, hl2_eq]; omega)] at hmR
      c0_hsteps
      have hfrR := mul2_opsFrame_with_lits_len hfrS (hdr0.lits_len + w)
      have haigR := mul2_aigInv_with_lits_len haigS (hdr0.lits_len + w)
      rw [← hfrR.lits_ptr] at hmR
      exact mul_ok_close hoom0 hsla hslb hfrR hextS haigR hlpS_len
        (by dsimp only; rw [hl1_eq]; omega)
        (by dsimp only; rw [hl1_eq, hfrR.lits_cap]; omega)
        hcap0 (by omega) hpreS hoomS rfl hwfS
        (fun ρ va vb hva hvb => by
          rw [hevS ρ va vb hva hvb, mul_eq_mulRec_last va vb (by omega)])
        (sep_ac hmR) hQ

end

end LeanQbe.T.Examples.Bitblast.Proof
