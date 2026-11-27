/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul1Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Stage Decomposition for `bv_blast_shift_var` (`Bitblast.Proof.OpsShiftMul1Stages`)

Decomposes `bv_blast_shift_var_body` into `4` exposed sub-expressions (`shiftVarSbitExpr`,
`shiftVarInnerExpr`, `shiftVarPhase2Expr`, `shiftVarTailExpr`) verified definitionally via
`bv_blast_shift_var_split_eq := rfl`, keeping every WP theorem fast and well under `300` lines.
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

/-! ## 1. Local `BVHdr` Accessors -/

@[local c0_load] private theorem s1s_load_hdr_lits_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 56) = some s.lits_ptr :=
  load_hdr_lits_ptr hm

@[local c0_load] private theorem s1s_load_hdr_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 120) = some s.oom :=
  load_hdr_oom hm

@[local c0_store] private theorem s1s_store_hdr_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 120) ∧
      (bvHdrMem h { s with oom := v } ⋆ R) (storeMem m i32 (h + 120) v) :=
  store_hdr_oom v hm

/-! ## 2. Exposed Sub-Expressions for `bv_blast_shift_var` -/

@[expose] public section

@[inline] def svCmp (c : CmpOp) (ty : Ty) (x y : Arg Val ty)
    (k : Val ty.mask → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [ty, ty], code := OpCode.cmp c ty, args := (x, y, ()) } (fun p => k p.fst)

@[inline] def svBin (code : OpCode [i32, i32] [i32]) (x y : Arg Val i32)
    (k : Val i32 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i32, i32], code := code, args := (x, y, ()) } (fun p => k p.fst)

@[inline] def svAdd64 (x y : Arg Val i64)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (x, y, ()) } (fun p => k p.fst)

@[inline] def svShl64 (x y : Arg Val i64)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.shl i64, args := (x, y, ()) } (fun p => k p.fst)

@[inline] def svZext (x : Arg Val i32)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (x, ()) } (fun p => k p.fst)

@[inline] def svTrunc (x : Arg Val i64)
    (k : Val i32 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (x, ()) } (fun p => k p.fst)

@[inline] def svLoadLit (litsPtr : Val i64) (idx : Val i32)
    (k : Val i32 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  svZext (Arg.var idx) fun p0 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p0, Arg.imm 4, ()) }
    fun p1 =>
  svAdd64 (Arg.var litsPtr) (Arg.var p1.fst) fun p2 =>
  Expr.load i32 (Arg.var p2) k

@[inline] def svAddrLit (litsPtr : Val i64) (idx : Val i32)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  svZext (Arg.var idx) fun p0 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p0, Arg.imm 4, ()) }
    fun p1 =>
  svAdd64 (Arg.var litsPtr) (Arg.var p1.fst) k

@[inline] def svLoadOom (h : Val i64) (k : Val i32 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  svAdd64 (Arg.var h) (Arg.imm 120) fun p0 => Expr.load i32 (Arg.var p0) k

@[inline] def svDist64 (pow : Val i32)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  svZext (Arg.var pow) fun p => svShl64 (Arg.imm 1) (Arg.var p) k

/-- `sbit` source-literal selection inside the Phase 2 inner loop of `bv_blast_shift_var`. -/
def shiftVarSbitExpr (w op out : Val i32) (litsPtr : Val i64) (j dist : Val i32)
    (J_sb : Cont [i32]) : Expr Val Cont [i32] :=
  svCmp .eq i32 (Arg.var op) (Arg.imm 19) fun p35 =>
  Expr.jnz (Arg.var p35)
    (Expr.group (sig := [[i32]])
      (fun _ => Blocks.cons (fun p => Expr.jump J_sb (Arg.var p.fst, ())) Blocks.nil)
      fun Js =>
      svCmp .uge i32 (Arg.var j) (Arg.var dist) fun p36 =>
      Expr.jnz (Arg.var p36)
        (svBin (OpCode.sub i32) (Arg.var j) (Arg.var dist) fun p =>
         svBin (OpCode.add i32) (Arg.var out) (Arg.var p) fun p =>
         svLoadLit litsPtr p fun ld => Expr.jump Js.fst (Arg.var ld, ()))
        (Expr.jump Js.fst (Arg.imm 0, ())))
    (Expr.group (sig := [[i32]])
      (fun _ => Blocks.cons (fun p => Expr.jump J_sb (Arg.var p.fst, ())) Blocks.nil)
      fun Js =>
      svCmp .eq i32 (Arg.var op) (Arg.imm 20) fun p36 =>
      Expr.jnz (Arg.var p36)
        (Expr.group (sig := [[i32]])
          (fun _ => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
          fun Js =>
          svBin (OpCode.sub i32) (Arg.var w) (Arg.var dist) fun p =>
          svCmp .ult i32 (Arg.var j) (Arg.var p) fun p =>
          Expr.jnz (Arg.var p)
            (svBin (OpCode.add i32) (Arg.var j) (Arg.var dist) fun p =>
             svBin (OpCode.add i32) (Arg.var out) (Arg.var p) fun p =>
             svLoadLit litsPtr p fun ld => Expr.jump Js.fst (Arg.var ld, ()))
            (Expr.jump Js.fst (Arg.imm 0, ())))
        (Expr.group (sig := [[i32]])
          (fun _ => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
          fun Js =>
          svBin (OpCode.sub i32) (Arg.var w) (Arg.var dist) fun p37 =>
          svCmp .ult i32 (Arg.var j) (Arg.var p37) fun p38 =>
          Expr.jnz (Arg.var p38)
            (svBin (OpCode.add i32) (Arg.var j) (Arg.var dist) fun p =>
             svBin (OpCode.add i32) (Arg.var out) (Arg.var p) fun p =>
             svLoadLit litsPtr p fun ld => Expr.jump Js.fst (Arg.var ld, ()))
            (svBin (OpCode.sub i32) (Arg.var w) (Arg.imm 1) fun p =>
             svBin (OpCode.add i32) (Arg.var out) (Arg.var p) fun p =>
             svLoadLit litsPtr p fun ld => Expr.jump Js.fst (Arg.var ld, ()))))

/-- Inner `j < w` `bv_aig_ite` + `bv_copy_lits` stage in Phase 2 of `bv_blast_shift_var`. -/
def shiftVarInnerExpr (h : Val i64) (w op out : Val i32) (litsPtr : Val i64)
    (mark tmp cond dist : Val i32) (J_ac : Cont []) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i32]])
    (fun Js =>
      Blocks.cons
        (fun p33 =>
          svCmp .ult i32 (Arg.var p33.fst) (Arg.var w) fun p34 =>
          Expr.jnz (Arg.var p34)
            (Expr.group (sig := [[i32]])
              (fun _ =>
                Blocks.cons
                  (fun p35 =>
                    svBin (OpCode.add i32) (Arg.var tmp) (Arg.var p33.fst) fun p36 =>
                    svAddrLit litsPtr p36 fun addr =>
                    svBin (OpCode.add i32) (Arg.var out) (Arg.var p33.fst) fun p40 =>
                    svLoadLit litsPtr p40 fun ld =>
                    Expr.call (as := [i64, i32, i32, i32]) (bs := [i32]) "bv_aig_ite"
                      (Arg.var h, Arg.var cond, Arg.var p35.fst, Arg.var ld, ()) fun p44 =>
                    Expr.store (Arg.var p44.fst) (Arg.var addr)
                      (svLoadOom h fun ld =>
                       svCmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p46 =>
                       Expr.jnz (Arg.var p46)
                         (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
                           (Arg.var h, Arg.var mark, ()) fun _ =>
                          Expr.ret (Arg.imm 4294967295, ()))
                         (svBin (OpCode.add i32) (Arg.var p33.fst) (Arg.imm 1) fun p =>
                          Expr.jump Js.fst (Arg.var p, ()))))
                  Blocks.nil)
              fun Js => shiftVarSbitExpr w op out litsPtr p33.fst dist Js.fst)
            (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "bv_copy_lits"
              (Arg.var h, Arg.var out, Arg.var tmp, Arg.var w, ()) fun _ =>
             Expr.jump J_ac ()))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

/-- Phase 2 doubling loop of `bv_blast_shift_var` (for `w > 1u`). -/
def shiftVarPhase2Expr (h : Val i64) (w bOff nw op out : Val i32) (litsPtr : Val i64)
    (J_fin : Cont [i32]) : Expr Val Cont [i32] :=
  Expr.call (as := [i64]) (bs := [i32]) "bv_lits_mark" (Arg.var h, ()) fun mark =>
  Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc" (Arg.var h, Arg.var w, ()) fun tmp =>
  svLoadOom h fun ld1 =>
  svCmp .ne i32 (Arg.var ld1) (Arg.imm 0) fun p17 =>
  Expr.jnz (Arg.var p17)
    (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
      (Arg.var h, Arg.var mark.fst, ()) fun _ =>
     Expr.ret (Arg.imm 4294967295, ()))
    (Expr.group (sig := [[i32]])
      (fun Js1 =>
        Blocks.cons
          (fun p18 =>
            Expr.group (sig := [[]])
              (fun _ =>
                Blocks.cons
                  (fun _ =>
                    Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
                      (Arg.var h, Arg.var mark.fst, ()) fun _ =>
                    Expr.jump J_fin (Arg.var p18.fst, ()))
                  Blocks.nil)
              fun Js =>
              svCmp .ult i32 (Arg.var p18.fst) (Arg.var nw) fun p19 =>
              Expr.jnz (Arg.var p19)
                (svCmp .ult i32 (Arg.var p18.fst) (Arg.imm 32) fun p20 =>
                 Expr.jnz (Arg.var p20)
                   (svDist64 p18.fst fun p22 =>
                    svZext (Arg.var w) fun p23 =>
                    svCmp .ult i64 (Arg.var p22) (Arg.var p23) fun p24 =>
                    Expr.jnz (Arg.var p24)
                      (svDist64 p18.fst fun p26 =>
                       svTrunc (Arg.var p26) fun dist =>
                       svBin (OpCode.add i32) (Arg.var bOff) (Arg.var p18.fst) fun p28 =>
                       svLoadLit litsPtr p28 fun cond =>
                       Expr.group (sig := [[]])
                         (fun _ =>
                           Blocks.cons
                             (fun _ =>
                               svBin (OpCode.add i32) (Arg.var p18.fst) (Arg.imm 1) fun p =>
                               Expr.jump Js1.fst (Arg.var p, ()))
                             Blocks.nil)
                         fun Js =>
                         svCmp .ne i32 (Arg.var cond) (Arg.imm 0) fun p32 =>
                         Expr.jnz (Arg.var p32)
                           (shiftVarInnerExpr h w op out litsPtr mark.fst tmp.fst cond dist Js.fst)
                           (Expr.jump Js.fst ()))
                      (Expr.jump Js.fst ()))
                   (Expr.jump Js.fst ()))
                (Expr.jump Js.fst ()))
          Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.imm 0, ()))

/-- Phase 3 saturation-fill (`fill` + `for j < w`) stage of `bv_blast_shift_var`. -/
def shiftVarFillExpr (h : Val i64) (w op out : Val i32) (litsPtr : Val i64)
    (ah : Val i32) (J_out2 : Cont []) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i32]])
    (fun _ =>
      Blocks.cons
        (fun fill =>
          Expr.group (sig := [[i32]])
            (fun Js4 =>
              Blocks.cons
                (fun p19 =>
                  svCmp .ult i32 (Arg.var p19.fst) (Arg.var w) fun p20 =>
                  Expr.jnz (Arg.var p20)
                    (svBin (OpCode.add i32) (Arg.var out) (Arg.var p19.fst) fun p21 =>
                     svAddrLit litsPtr p21 fun addr =>
                     svBin (OpCode.add i32) (Arg.var out) (Arg.var p19.fst) fun p25 =>
                     svLoadLit litsPtr p25 fun ld =>
                     Expr.call (as := [i64, i32, i32, i32]) (bs := [i32])
                       "bv_aig_ite" (Arg.var h, Arg.var ah,
                         Arg.var fill.fst, Arg.var ld, ()) fun p29 =>
                     Expr.store (Arg.var p29.fst) (Arg.var addr)
                       (svLoadOom h fun ld =>
                        svCmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p =>
                        Expr.jnz (Arg.var p)
                          (Expr.ret (Arg.imm 4294967295, ()))
                          (svBin (OpCode.add i32) (Arg.var p19.fst) (Arg.imm 1) fun p =>
                           Expr.jump Js4.fst (Arg.var p, ()))))
                    (Expr.jump J_out2 ()))
                Blocks.nil)
            fun Js => Expr.jump Js.fst (Arg.imm 0, ()))
        Blocks.nil)
    fun Js =>
    svCmp .eq i32 (Arg.var op) (Arg.imm 21) fun p =>
    Expr.jnz (Arg.var p)
      (svBin (OpCode.sub i32) (Arg.var w) (Arg.imm 1) fun p =>
       svBin (OpCode.add i32) (Arg.var out) (Arg.var p) fun p =>
       svLoadLit litsPtr p fun ld => Expr.jump Js.fst (Arg.var ld, ()))
      (Expr.jump Js.fst (Arg.imm 0, ()))

/-- Phase 3 high-bit OR-reduction and saturation stage of `bv_blast_shift_var`. -/
def shiftVarTailExpr (h : Val i64) (w bOff nw op out : Val i32) (litsPtr : Val i64)
    (pow : Val i32) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i32]])
    (fun _ => Blocks.cons (fun _ => Expr.ret (Arg.var out, ())) Blocks.nil)
    fun Js =>
    svCmp .ult i32 (Arg.var pow) (Arg.var nw) fun p14 =>
    Expr.jnz (Arg.var p14)
      (Expr.group (sig := [[i32, i32]])
        (fun Js1 =>
          Blocks.cons
            (fun p15 =>
              Expr.group (sig := [[]])
                (fun _ =>
                  Blocks.cons
                    (fun _ =>
                      Expr.group (sig := [[]])
                        (fun _ =>
                          Blocks.cons (fun _ => Expr.jump Js.fst (Arg.var p15.fst, ())) Blocks.nil)
                        fun Js =>
                        svCmp .ne i32 (Arg.var p15.snd.fst) (Arg.imm 0) fun p17 =>
                        Expr.jnz (Arg.var p17)
                          (shiftVarFillExpr h w op out litsPtr p15.snd.fst Js.fst)
                          (Expr.jump Js.fst ()))
                    Blocks.nil)
                fun Js =>
                svCmp .ult i32 (Arg.var p15.fst) (Arg.var nw) fun p16 =>
                Expr.jnz (Arg.var p16)
                  (svCmp .ne i32 (Arg.var p15.snd.fst) (Arg.imm 1) fun p17 =>
                   Expr.jnz (Arg.var p17)
                     (svBin (OpCode.add i32) (Arg.var bOff) (Arg.var p15.fst) fun p18 =>
                      svLoadLit litsPtr p18 fun ld =>
                      Expr.call (as := [i64, i32, i32]) (bs := [i32]) "bv_aig_or"
                        (Arg.var h, Arg.var p15.snd.fst, Arg.var ld, ()) fun p22 =>
                      svLoadOom h fun ld =>
                      svCmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p =>
                      Expr.jnz (Arg.var p)
                        (Expr.ret (Arg.imm 4294967295, ()))
                        (svBin (OpCode.add i32) (Arg.var p15.fst) (Arg.imm 1) fun p =>
                         Expr.jump Js1.fst (Arg.var p, Arg.var p22.fst, ())))
                     (Expr.jump Js.fst ()))
                  (Expr.jump Js.fst ()))
            Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.var pow, Arg.imm 0, ()))
      (Expr.jump Js.fst (Arg.var pow, ()))

end

/-! ## 3. Definitional Split & Stage WP Lemmas (`<= 240` lines each) -/

public section

/-- Definitional split equation matching `bv_blast_shift_var_body` to `shiftVarPhase2Expr` and
`shiftVarTailExpr`. -/
theorem bv_blast_shift_var_split_eq (h : Val i64) (aOff w bOff nw op : Val i32) :
    bv_blast_shift_var_body (V := Val) (L := Cont) (h, aOff, w, bOff, nw, op, ()) =
      Expr.group (sig := [[]])
        (fun _Js =>
          Blocks.cons
            (fun _ =>
              Expr.group (sig := [[]])
                (fun _Js =>
                  Blocks.cons
                    (fun _ =>
                      svAdd64 (Arg.var h) (Arg.imm 120) fun p =>
                      Expr.store (Arg.imm (t := i32) 1) (Arg.var p)
                        (Expr.ret (Arg.imm 4294967295, ())))
                    Blocks.nil)
                fun Js =>
                svLoadOom h fun ld =>
                svCmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p3 =>
                Expr.jnz (Arg.var p3) (Expr.jump Js.fst ())
                  (Expr.call (as := [i64, i32, i32]) (bs := [Ty.bool])
                    "bv_slice_ok" (Arg.var h, Arg.var aOff, Arg.var w, ()) fun p4 =>
                   Expr.jnz (Arg.var p4.fst)
                     (Expr.call (as := [i64, i32, i32]) (bs := [Ty.bool])
                       "bv_slice_ok" (Arg.var h, Arg.var bOff, Arg.var nw, ()) fun p5 =>
                      Expr.jnz (Arg.var p5.fst)
                        (Expr.call (as := [i64, i32]) (bs := [i32])
                          "bv_lits_alloc" (Arg.var h, Arg.var w, ()) fun p6 =>
                         svLoadOom h fun ld =>
                         svCmp .ne i32 (Arg.var ld) (Arg.imm 0) fun p8 =>
                         Expr.jnz (Arg.var p8) (Expr.ret (Arg.imm 4294967295, ()))
                           (svCmp .eq i32 (Arg.var w) (Arg.imm 0) fun p9 =>
                            Expr.jnz (Arg.var p9) (Expr.ret (Arg.var p6.fst, ()))
                              (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "bv_copy_lits"
                                (Arg.var h, Arg.var p6.fst, Arg.var aOff, Arg.var w, ()) fun _ =>
                               svCmp .eq i32 (Arg.var nw) (Arg.imm 0) fun p11 =>
                               Expr.jnz (Arg.var p11) (Expr.ret (Arg.var p6.fst, ()))
                               (svAdd64 (Arg.var h) (Arg.imm 56) fun p12 =>
                                Expr.load i64 (Arg.var p12) fun ld =>
                                Expr.group (sig := [[i32]])
                                  (fun _ =>
                                    Blocks.cons
                                      (fun p13 =>
                                        shiftVarTailExpr h w bOff nw op p6.fst ld p13.fst)
                                      Blocks.nil)
                                    fun Js =>
                                    svCmp .ugt i32 (Arg.var w) (Arg.imm 1) fun p13 =>
                                    Expr.jnz (Arg.var p13)
                                      (shiftVarPhase2Expr h w bOff nw op p6.fst ld Js.fst)
                                      (Expr.jump Js.fst (Arg.imm 0, ()))))))
                        (Expr.jump Js.fst ()))
                     (Expr.jump Js.fst ())))
            Blocks.nil)
        fun Js =>
        svCmp .ne i32 (Arg.var op) (Arg.imm 19) fun p1 =>
        Expr.jnz (Arg.var p1)
          (svCmp .ne i32 (Arg.var op) (Arg.imm 20) fun p2 =>
           Expr.jnz (Arg.var p2)
             (svCmp .ne i32 (Arg.var op) (Arg.imm 21) fun p3 =>
              Expr.jnz (Arg.var p3)
                (svAdd64 (Arg.var h) (Arg.imm 120) fun p =>
                 Expr.store (Arg.imm (t := i32) 1) (Arg.var p)
                   (Expr.ret (Arg.imm 4294967295, ())))
                (Expr.jump Js.fst ()))
             (Expr.jump Js.fst ()))
          (Expr.jump Js.fst ()) := rfl

theorem shiftVar_sbit_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {mJ : Mem 64}
    {h : BitVec 64} {aOff w bOff nw op : BitVec 32} {p j : Nat} {dist : BitVec 32}
    {hdr0 hdrJ : BVHdrState} {g0 gJ : Aig} {awJ : List (BitVec 64)}
    {htJ lp0 lpJ : List (BitVec 32)} {R : Mem 64 → Prop} {J_sb : Cont [i32]}
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hw_pos : 0 < w.toNat) (hp2 : 2 ^ p < w.toNat) (hj_lt : j < w.toNat)
    (hj32 : (BitVec.ofNat 32 j).toNat = j) (hdist : dist.toNat = 2 ^ p)
    (hlpJ_len : lpJ.length = lp0.length) (_hfrJ : hdr0.OpsFrame hdrJ)
    (hwf_outJ : SliceLitsWf gJ lpJ hdr0.lits_len.toNat w.toNat)
    (hev_outJ : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      evalPoolSlice gJ ρ lpJ hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb p)
    (hmJ : (bvHdrMem h hdrJ ⋆ array64 hdrJ.aig_ptr awJ ⋆
      array (t := i32) hdrJ.ht_ptr htJ ⋆ array (t := i32) hdr0.lits_ptr lpJ ⋆ R) mJ)
    (hJ_sb : ∀ (s : BitVec 32),
      ((s >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) →
      (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
        SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
        SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
        gJ.evalLit ρ (UInt32.ofBitVec s) =
          if op = 19#32 then
            if 2 ^ p ≤ j then (bvShiftCur op va vb p).getLsbD (j - 2 ^ p) else false
          else if op = 20#32 then
            if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p) else false
          else
            if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p)
            else (bvShiftCur op va vb p).getLsbD (w.toNat - 1)) →
      J_sb (s, ()) mJ) :
    wp Γ Q X (shiftVarSbitExpr w op hdr0.lits_len hdr0.lits_ptr
      (BitVec.ofNat 32 j) dist J_sb) mJ := by
  let SbitP : BitVec 32 → Prop := fun s =>
    ((s >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) ∧
    (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      gJ.evalLit ρ (UInt32.ofBitVec s) =
        if op = 19#32 then
          if 2 ^ p ≤ j then (bvShiftCur op va vb p).getLsbD (j - 2 ^ p) else false
        else if op = 20#32 then
          if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p) else false
        else
          if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p)
          else (bvShiftCur op va vb p).getLsbD (w.toNat - 1))
  dsimp only [shiftVarSbitExpr, svCmp, svBin, svLoadLit, svZext, svAdd64]
  c0_hstraight; c0_hsplit
  · have hop19 : op = 19#32 := by c0_bv_omega [hc]
    clear hc
    refine shift1_wp_join1_fwd (Inv := fun s m => SbitP s ∧ m = mJ)
      (fun s m ⟨h1, hm⟩ => hm ▸ hJ_sb s h1.1 h1.2) ?_
    intro J_sb' hJ_sb'; c0_hstraight; c0_hsplit
    · have hge_dist : 2 ^ p ≤ j := by
        rw [← hdist]; rw [Nat.mod_eq_of_lt (by have := w.isLt; omega)] at hc; exact hc
      clear hc
      have hidx_sw : ((hdr0.lits_len + (BitVec.ofNat 32 j - dist)).setWidth 64).toNat =
          hdr0.lits_len.toNat + (j - 2 ^ p) := by
        have hj_sub : (BitVec.ofNat 32 j - dist).toNat = j - 2 ^ p := by
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hj32, hdist]; exact hge_dist)),
            hj32, hdist]
        rw [shift1_setWidth64_toNat, BitVec.toNat_add, hj_sub,
          Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
      c0_hsteps
      have hsb := shiftVar_sbit_idx_lit hwf_outJ hev_outJ (by rw [hlpJ_len, hcap0]; omega)
        (by omega : j - 2 ^ p < w.toNat) (Or.inl ⟨hop19, hge_dist, rfl⟩)
      have hget : lpJ[((hdr0.lits_len + (BitVec.ofNat 32 j - dist)).setWidth 64).toNat]'(by
            rw [hidx_sw, hlpJ_len, hcap0]; omega) =
          lpJ[hdr0.lits_len.toNat + (j - 2 ^ p)]'(by rw [hlpJ_len, hcap0]; omega) := by
        congr 1
      rw [hget]
      exact hJ_sb' _ mJ ⟨⟨hsb.1, hsb.2⟩, rfl⟩
    · have hlt_dist : ¬ 2 ^ p ≤ j := by
        rw [← hdist]; rw [Nat.mod_eq_of_lt (by have := w.isLt; omega)] at hc; exact hc
      clear hc; c0_hsteps
      have hsb : SbitP 0#32 := shiftVar_sbit_zero_lit (Or.inl ⟨hop19, hlt_dist⟩) (Or.inl hop19)
      exact hJ_sb' 0#32 mJ ⟨⟨hsb.1, hsb.2⟩, rfl⟩
  · have hop_ne19 : op ≠ 19#32 := by c0_bv_omega [hc]
    clear hc
    refine shift1_wp_join1_fwd (Inv := fun s m => SbitP s ∧ m = mJ)
      (fun s m ⟨h1, hm⟩ => hm ▸ hJ_sb s h1.1 h1.2) ?_
    intro J_sb' hJ_sb'; c0_hstraight; c0_hsplit
    · have hop20 : op = 20#32 := by c0_bv_omega [hc]
      clear hc
      have hw_sub : (w - dist).toNat = w.toNat - 2 ^ p := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hdist]; omega)), hdist]
      refine shift1_wp_join1_fwd (Inv := fun s m => SbitP s ∧ m = mJ) hJ_sb' ?_
      intro J_sb'' hJ_sb''; c0_hstraight; c0_hsplit
      · have hj_wdist : j < w.toNat - 2 ^ p := by
          have h1 : BitVec.ofNat 32 j < w - dist := hc
          rw [BitVec.lt_def, hj32, hw_sub] at h1; exact h1
        clear hc
        have hidx_sw : ((hdr0.lits_len + (BitVec.ofNat 32 j + dist)).setWidth 64).toNat =
            hdr0.lits_len.toNat + (j + 2 ^ p) := by
          rw [shift1_setWidth64_toNat, BitVec.toNat_add, BitVec.toNat_add, hj32, hdist,
            Nat.mod_eq_of_lt (by have := w.isLt; omega),
            Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
        c0_hsteps
        have hsb := shiftVar_sbit_idx_lit hwf_outJ hev_outJ (by rw [hlpJ_len, hcap0]; omega)
          (by omega : j + 2 ^ p < w.toNat) (Or.inr (Or.inl ⟨hop_ne19, hop20, hj_wdist, rfl⟩))
        have hget : lpJ[((hdr0.lits_len + (BitVec.ofNat 32 j + dist)).setWidth 64).toNat]'(by
              rw [hidx_sw, hlpJ_len, hcap0]; omega) =
            lpJ[hdr0.lits_len.toNat + (j + 2 ^ p)]'(by rw [hlpJ_len, hcap0]; omega) := by
          congr 1
        rw [hget]
        exact hJ_sb'' _ mJ ⟨⟨hsb.1, hsb.2⟩, rfl⟩
      · have hj_ge : ¬ j < w.toNat - 2 ^ p := by
          have h1 : ¬ BitVec.ofNat 32 j < w - dist := hc
          rw [BitVec.lt_def, hj32, hw_sub] at h1; exact h1
        clear hc; c0_hsteps
        have hsb : SbitP 0#32 := shiftVar_sbit_zero_lit (Or.inr ⟨hop_ne19, hj_ge⟩) (Or.inr hop20)
        exact hJ_sb'' 0#32 mJ ⟨⟨hsb.1, hsb.2⟩, rfl⟩
    · have hop_ne20 : op ≠ 20#32 := by c0_bv_omega [hc]
      clear hc
      have hw_sub : (w - dist).toNat = w.toNat - 2 ^ p := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hdist]; omega)), hdist]
      refine shift1_wp_join1_fwd (Inv := fun s m => SbitP s ∧ m = mJ) hJ_sb' ?_
      intro J_sb'' hJ_sb''; c0_hstraight; c0_hsplit
      · have hj_wdist : j < w.toNat - 2 ^ p := by
          have h1 : BitVec.ofNat 32 j < w - dist := hc
          rw [BitVec.lt_def, hj32, hw_sub] at h1; exact h1
        clear hc
        have hidx_sw : ((hdr0.lits_len + (BitVec.ofNat 32 j + dist)).setWidth 64).toNat =
            hdr0.lits_len.toNat + (j + 2 ^ p) := by
          rw [shift1_setWidth64_toNat, BitVec.toNat_add, BitVec.toNat_add, hj32, hdist,
            Nat.mod_eq_of_lt (by have := w.isLt; omega),
            Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
        c0_hsteps
        have hsb := shiftVar_sbit_idx_lit hwf_outJ hev_outJ (by rw [hlpJ_len, hcap0]; omega)
          (by omega : j + 2 ^ p < w.toNat)
          (Or.inr (Or.inr (Or.inl ⟨hop_ne19, hop_ne20, hj_wdist, rfl⟩)))
        have hget : lpJ[((hdr0.lits_len + (BitVec.ofNat 32 j + dist)).setWidth 64).toNat]'(by
              rw [hidx_sw, hlpJ_len, hcap0]; omega) =
            lpJ[hdr0.lits_len.toNat + (j + 2 ^ p)]'(by rw [hlpJ_len, hcap0]; omega) := by
          congr 1
        rw [hget]
        exact hJ_sb'' _ mJ ⟨⟨hsb.1, hsb.2⟩, rfl⟩
      · have hj_ge : ¬ j < w.toNat - 2 ^ p := by
          have h1 : ¬ BitVec.ofNat 32 j < w - dist := hc
          rw [BitVec.lt_def, hj32, hw_sub] at h1; exact h1
        clear hc
        have hidx_sw : ((hdr0.lits_len + (w - (1 : BitVec 32))).setWidth 64).toNat =
            hdr0.lits_len.toNat + (w.toNat - 1) := by
          rw [shift1_setWidth64_toNat, BitVec.toNat_add,
            show (w - 1).toNat = w.toNat - 1 from shift1_sub1_toNat hw_pos,
            Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
        c0_hsteps
        have hsb := shiftVar_sbit_idx_lit hwf_outJ hev_outJ (by rw [hlpJ_len, hcap0]; omega)
          (by omega : w.toNat - 1 < w.toNat)
          (Or.inr (Or.inr (Or.inr ⟨hop_ne19, hop_ne20, hj_ge, rfl⟩)))
        have hget :
            lpJ[((hdr0.lits_len + (w - (1 : BitVec 32))).setWidth 64).toNat]'(by
              rw [hidx_sw, hlpJ_len, hcap0]; omega) =
            lpJ[hdr0.lits_len.toNat + (w.toNat - 1)]'(by rw [hlpJ_len, hcap0]; omega) := by
          congr 1
        rw [hget]
        exact hJ_sb'' _ mJ ⟨⟨hsb.1, hsb.2⟩, rfl⟩

theorem shiftVar_inner_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {mP : Mem 64}
    (hRel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hCopy : Γ.Has "bv_copy_lits" bvCopyLitsSpec)
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {aOff w bOff nw op cond dist : BitVec 32} {p : Nat}
    {hdr0 hdrP : BVHdrState} {g0 gP : Aig} {awP : List (BitVec 64)}
    {htP lp0 lpP : List (BitVec 32)} {R : Mem 64 → Prop} {J_ac : Cont []}
    (_hoom0 : hdr0.oom = 0#32)
    (_hop_t : decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true)
    (hop_disj : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (_hsla : sliceOkBool hdr0 aOff w = true) (_hslb : sliceOkBool hdr0 bOff nw = true)
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hfit2 : w.toNat ≤ hdr0.lits_cap.toNat - (hdr0.lits_len + w).toNat)
    (hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat)
    (hl2_eq : (hdr0.lits_len + w + w).toNat = hdr0.lits_len.toNat + w.toNat + w.toNat)
    (hw_pos : 0 < w.toNat) (hp_lt : p < nw.toNat) (hp_lt32 : p < 32) (hp2_lt : 2 ^ p < w.toNat)
    (hb_hi : bOff.toNat + nw.toNat ≤ hdr0.lits_len.toNat)
    (hdist : dist.toNat = 2 ^ p)
    (hwfb0 : SliceLitsWf g0 lp0 bOff.toNat nw.toNat)
    (hinvP : ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R (p, hdrP, gP, awP, htP, lpP) mP h)
    (hcond_eq : cond = lp0.getD (bOff.toNat + p) 0#32)
    (hJ_ac : ∀ (mN : Mem 64), (∃ hdrN gN awN htN lpN,
      ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R (p + 1, hdrN, gN, awN, htN, lpN) mN h) →
      J_ac () mN)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig) (aigWords' : List (BitVec 64))
      (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ q < hdr0.lits_len.toNat, litsPool'.getD q 0#32 = lp0.getD q 0#32) →
      (hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (bvShiftSem op va vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (shiftVarInnerExpr h w op hdr0.lits_len hdr0.lits_ptr
      (hdr0.lits_len + w) (hdr0.lits_len + w) cond dist J_ac) mP := by
  subst hcond_eq
  rcases hinvP with ⟨hp_nw, hp_32, hfrP, hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP,
    hevP, hmP⟩
  dsimp only [shiftVarInnerExpr, svCmp, svBin, svAddrLit, svLoadLit, svLoadOom, svZext, svAdd64]
  refine wp_while_state (α := Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) ×
      List (BitVec 32))
    (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
    (fun st mJ => ShiftInnerInv aOff w bOff nw op hdr0 g0 lp0 R p st mJ h) ?_ ?_
  · intro J_in hJ_in; c0_hsteps
    exact hJ_in (0, hdrP, gP, awP, htP, lpP) mP
      ⟨Nat.zero_le _, hfrP, hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP, hevP,
        fun _ h0 => absurd h0 (Nat.not_lt_zero _),
        fun _ _ _ _ h0 => absurd h0 (Nat.not_lt_zero _), sep_ac hmP⟩
  · intro J_in ⟨j, hdrJ, gJ, awJ, htJ, lpJ⟩ mJ hinvJ ih_in
    have hj_w := hinvJ.1
    have hj32 : (BitVec.ofNat 32 j).toNat = j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
    c0_hstraight; c0_hsplit
    · have hj_lt : j < w.toNat := by
        have h1 : BitVec.ofNat 32 j < w := hc; rw [BitVec.lt_def, hj32] at h1; exact h1
      clear hc
      rcases hinvJ with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, hwf_outJ,
        hev_outJ, hwf_tmpJ, hev_tmpJ, hmJ⟩
      c0_hstraight
      refine wp_join_state (α := BitVec 32) (fun s => (s, ()))
        (fun sbit mSb =>
          ((sbit >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) ∧
          (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
            SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
            SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
            gJ.evalLit ρ (UInt32.ofBitVec sbit) =
              if op = 19#32 then
                if 2 ^ p ≤ j then (bvShiftCur op va vb p).getLsbD (j - 2 ^ p) else false
              else if op = 20#32 then
                if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p) else false
              else
                if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p)
                else (bvShiftCur op va vb p).getLsbD (w.toNat - 1)) ∧ mSb = mJ) ?_ ?_
      · intro _ sbit mSb ⟨hsbit_bd, hsbit_ev, hmSb⟩; rw [hmSb] at *
        have htmpj_sw : ((hdr0.lits_len + w + BitVec.ofNat 32 j).setWidth 64).toNat =
            hdr0.lits_len.toNat + w.toNat + j := by
          rw [shift1_setWidth64_toNat, BitVec.toNat_add, hl1_eq, hj32,
            Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
        have houtj_sw : ((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
            hdr0.lits_len.toNat + j := by
          rw [shift1_setWidth64_toNat, BitVec.toNat_add, hj32,
            Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
        have hout_ag :
            lpJ[((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat]'(by
              rw [houtj_sw, hlpJ_len, hcap0]; omega) =
            lpJ.getD (hdr0.lits_len.toNat + j) 0#32 := by
          rw [← shift1_getD_eq_getElem lpJ (by rw [houtj_sw, hlpJ_len, hcap0]; omega), houtj_sw]
        have hwf_condJ : ((lp0.getD (bOff.toNat + p) 0#32) >>> 1).toNat <
            gJ.A + 1 + gJ.nodes.size := by
          have hsz : g0.A + 1 + g0.nodes.size ≤ gJ.A + 1 + gJ.nodes.size := by
            have := hextJ.1; have := hextJ.2.1; omega
          exact Nat.lt_of_lt_of_le (hwfb0 p hp_lt) hsz
        c0_hstraight
        c0_hcall hIte
        refine ⟨hdrJ, gJ, awJ, htJ, array (t := i32) hdr0.lits_ptr lpJ ⋆ R, haigJ,
          fun _ => ⟨by rw [haigJ.aig_len_eq]; exact hwf_condJ,
            by rw [haigJ.aig_len_eq]; exact hsbit_bd,
            by rw [hout_ag, haigJ.aig_len_eq]; exact hwf_outJ j hj_lt⟩,
          sep_ac hmJ, fun ret hdrN gN awN htN mN hfrN hextN _ haigN hoomN _ hevN hmN => ?_⟩
        have hfr0N := hfrJ.trans hfrN.toOpsFrame
        have hext0N := Aig.extends_trans hextJ hextN
        have hlenN : hdrN.lits_len = hdr0.lits_len + w + w := hfrN.lits_len.trans hlenJ
        rw [← hfrJ.lits_ptr] at hmN
        have hmN' := ops_aig_frame_unfocus hfrN.toOpsFrame hmN
        rw [hfr0N.lits_ptr] at hmN'
        c0_hstraight
        rw [htmpj_sw] at hm
        c0_hsplit
        · have hoom_ne : hdrN.oom ≠ 0#32 := by c0_bv_omega [hc]
          clear hc
          have hlenN_n : hdrN.lits_len.toNat = hdr0.lits_len.toNat + w.toNat + w.toNat := by
            rw [hlenN, hl2_eq]
          c0_hcall hRel
          refine ⟨hdrN, array64 hdrN.aig_ptr awN ⋆ array (t := i32) hdrN.ht_ptr htN ⋆
            array (t := i32) hdr0.lits_ptr _ ⋆ R, sep_ac hm, fun mO hmO => ?_⟩
          rw [ite_eq_left (by rw [hl1_eq, hlenN_n]; omega)] at hmO
          c0_hsteps
          have hfrO : hdr0.OpsFrame { hdrN with lits_len := hdr0.lits_len + w } := by
            rcases hfr0N with ⟨f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19⟩
            exact ⟨f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19⟩
          have haigO := shift1_aigInv_with_lits_len haigN (hdr0.lits_len + w)
          rw [← hfr0N.lits_ptr] at hmO
          exact shiftVar_oom_close (hdr' := { hdrN with lits_len := hdr0.lits_len + w })
            (lp' := lpJ.set (j + (w.toNat + hdr0.lits_len.toNat)) ret)
            hfrO hext0N haigO (by simp [hlpJ_len])
            (by dsimp only; rw [hl1_eq]; omega)
            (by dsimp only; rw [hl1_eq, hfr0N.lits_cap]; omega)
            (fun q hq => by
              rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
                ← List.getD_eq_getElem?_getD]
              exact hpreJ q hq)
            hoom_ne (sep_ac hmO) hQ
        · have hoomN0 : hdrN.oom = 0#32 := by c0_bv_omega [hc]
          clear hc
          c0_hsteps
          obtain ⟨hret_bd, hret_ev⟩ := hevN hoomN0
          rw [haigN.aig_len_eq] at hret_bd
          have hstep := shiftVar_ite_step_ok hlpJ_len hpreJ hwfb0 hp_lt hwf_outJ hev_outJ
            hwf_tmpJ hev_tmpJ hj_lt hop_disj hp2_lt (by rw [hlpJ_len, hcap0]; omega) hextN
            hret_bd hsbit_ev (fun ρ => by rw [hret_ev ρ]; dsimp only; rw [hout_ag]) rfl hextJ
            (by rw [hcap0]; omega)
          rw [shift1_bv32_succ_add (by have := w.isLt; omega)]
          exact ih_in (j + 1, hdrN, gN, awN, htN, _) _ (by dsimp only; omega)
            ⟨by omega, hfr0N, hext0N, haigN, hoomN0, hlenN, hstep.1, hstep.2.1, hstep.2.2.1,
              hstep.2.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.2.2, sep_ac hm⟩
      · intro J_sb hJ_sb
        exact shiftVar_sbit_wp hcap0 hfit1 hw_pos hp2_lt hj_lt hj32 hdist hlpJ_len hfrJ hwf_outJ
          hev_outJ hmJ fun s hb he => hJ_sb s mJ ⟨hb, he, rfl⟩
    · have hj_eq : j = w.toNat := by
        have h1 : ¬ BitVec.ofNat 32 j < w := hc; rw [BitVec.lt_def, hj32] at h1; omega
      clear hc; subst hj_eq
      rcases hinvJ with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, hwf_outJ,
        hev_outJ, hwf_tmpJ, hev_tmpJ, hmJ⟩
      c0_hcall hCopy
      refine ⟨hdrJ, lpJ, array64 hdrJ.aig_ptr awJ ⋆ array (t := i32) hdrJ.ht_ptr htJ ⋆ R,
        by rw [hlpJ_len, hcap0]; exact hdr0.lits_cap.isLt, by rw [hlpJ_len, hcap0]; omega,
        by rw [hl1_eq, hlpJ_len, hcap0]; omega, Or.inl (by rw [hl1_eq]; omega),
        by rw [hfrJ.lits_ptr]; exact sep_ac hmJ, fun lpN mN hlpN_len houtN hinN hmN => ?_⟩
      exact hJ_ac mN ⟨hdrJ, gJ, awJ, htJ, lpN, shiftInnerInv_to_phase2 hp_lt hp_lt32
        ⟨Nat.le_refl _, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, hwf_outJ, hev_outJ,
          hwf_tmpJ, hev_tmpJ, hmJ⟩
        hlpN_len houtN (by rw [hl1_eq] at hinN; exact hinN) (sep_ac hmN)⟩

theorem shiftVar_phase2_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {m2 : Mem 64}
    (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hMark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (hRel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hCopy : Γ.Has "bv_copy_lits" bvCopyLitsSpec)
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {aOff w bOff nw op : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig} {aw0 : List (BitVec 64)}
    {ht0 lp0 lp1 : List (BitVec 32)} {R : Mem 64 → Prop} {J_fin : Cont [i32]}
    (hoom0 : hdr0.oom = 0#32)
    (hop_t : decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true)
    (hop_disj : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (hsla : sliceOkBool hdr0 aOff w = true) (hslb : sliceOkBool hdr0 bOff nw = true)
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat)
    (hw_pos : 0 < w.toNat) (hnw_pos : 0 < nw.toNat)
    (hb_hi : bOff.toNat + nw.toNat ≤ hdr0.lits_len.toNat)
    (hfr1 : hdr0.OpsFrame { hdr0 with lits_len := hdr0.lits_len + w })
    (haig1 : AigInv { hdr0 with lits_len := hdr0.lits_len + w } g0 aw0 ht0)
    (hlp1_len : lp1.length = lp0.length)
    (hout1 : ∀ p, p < hdr0.lits_len.toNat ∨ hdr0.lits_len.toNat + w.toNat ≤ p →
      lp1.getD p 0#32 = lp0.getD p 0#32)
    (hwfc1 : SliceLitsWf g0 lp1 hdr0.lits_len.toNat w.toNat)
    (hev1 : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      evalPoolSlice g0 ρ lp1 hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb 0)
    (hwfb0 : SliceLitsWf g0 lp0 bOff.toNat nw.toNat)
    (hm2 : (bvHdrMem h { hdr0 with lits_len := hdr0.lits_len + w } ⋆
      (array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
        array (t := i32) hdr0.lits_ptr lp1 ⋆ R)) m2)
    (hJ_fin : ∀ st m', ShiftStageInv aOff w bOff nw op hdr0 g0 lp0 R st m' h →
      J_fin (BitVec.ofNat 32 st.1, ()) m')
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig) (aigWords' : List (BitVec 64))
      (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ q < hdr0.lits_len.toNat, litsPool'.getD q 0#32 = lp0.getD q 0#32) →
      (hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (bvShiftSem op va vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (shiftVarPhase2Expr h w bOff nw op hdr0.lits_len hdr0.lits_ptr J_fin) m2 := by
  dsimp only [shiftVarPhase2Expr, svCmp, svBin, svDist64, svZext, svShl64, svTrunc, svLoadLit,
    svLoadOom, svAdd64]
  c0_hcall hMark; refine ⟨{ hdr0 with lits_len := hdr0.lits_len + w },
    array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
    array (t := i32) hdr0.lits_ptr lp1 ⋆ R, sep_ac hm2, ?_⟩
  c0_hcall hAlloc; refine ⟨{ hdr0 with lits_len := hdr0.lits_len + w },
    array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
    array (t := i32) hdr0.lits_ptr lp1 ⋆ R, sep_ac hm2, ?_⟩
  by_cases hfit2 : w.toNat ≤ hdr0.lits_cap.toNat - (hdr0.lits_len + w).toNat
  · dsimp only
    rw [ite_eq_left (⟨hoom0, by rw [hl1_eq]; omega, hfit2⟩ :
        hdr0.oom = 0#32 ∧ (hdr0.lits_len + w).toNat ≤ hdr0.lits_cap.toNat ∧
        w.toNat ≤ hdr0.lits_cap.toNat - (hdr0.lits_len + w).toNat)]
    intro m3 hm3
    have hfr2 := hfr1.trans (ops_lits_alloc_ok_frame { hdr0 with lits_len := hdr0.lits_len + w } w)
    have haig2 := shift1_aigInv_with_lits_len haig1 (hdr0.lits_len + w + w)
    have hl2_eq : (hdr0.lits_len + w + w).toNat = hdr0.lits_len.toNat + w.toNat + w.toNat := by
      rw [BitVec.toNat_add, hl1_eq, Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
    c0_hstraight; c0_hsplit
    · exfalso; exact hc hoom0
    · clear hc
      refine wp_while_state (α := Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) ×
          List (BitVec 32))
        (fun (p, _) => (BitVec.ofNat 32 p, ())) (fun (p, _) => nw.toNat - p)
        (fun st mP => ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R st mP h) ?_ ?_
      · intro J_w hJ_w; c0_hsteps
        exact hJ_w (0, { hdr0 with lits_len := hdr0.lits_len + w + w }, g0, aw0, ht0, lp1) m3
          ⟨Nat.zero_le _, by decide, hfr2, shift1_aig_le_self g0, haig2, hoom0, rfl, hlp1_len,
            fun q hq => hout1 q (Or.inl hq), hwfc1, hev1, sep_ac hm3⟩
      · intro J_w ⟨p, hdrP, gP, awP, htP, lpP⟩ mP hinvP ih_w
        have hp_nw := hinvP.1
        have hp32_tn : (BitVec.ofNat 32 p).toNat = p := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := nw.isLt; omega)]
        refine wp_join0 (fun mR => ∃ hdrR gR awR htR lpR,
            (p < nw.toNat → w.toNat ≤ 2 ^ p) ∧
            ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R (p, hdrR, gR, awR, htR, lpR) mR h) ?_ ?_
        · intro _ mR ⟨hdrR, gR, awR, htR, lpR, hpwR, hinvR⟩
          have hlenR_n : hdrR.lits_len.toNat = hdr0.lits_len.toNat + w.toNat + w.toNat := by
            rw [hinvR.2.2.2.2.2.2.1, hl2_eq]
          c0_hcall hRel
          refine ⟨hdrR, array64 hdrR.aig_ptr awR ⋆ array (t := i32) hdrR.ht_ptr htR ⋆
            array (t := i32) hdr0.lits_ptr lpR ⋆ R, sep_ac hinvR.2.2.2.2.2.2.2.2.2.2.2,
            fun mS hmS => ?_⟩
          rw [ite_eq_left (by rw [hl1_eq, hlenR_n]; omega)] at hmS
          exact hJ_fin (p, { hdrR with lits_len := hdr0.lits_len + w }, gR, awR, htR, lpR) mS
            (shiftStageInv_of_rel hpwR hinvR hmS)
        · intro J_rel hJ_rel
          rcases hinvP with ⟨_, hp_32, hfrP, hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP,
            hevP, hmP⟩
          c0_hstraight; c0_hsplit
          · have hp_lt : p < nw.toNat := by
              have h1 : BitVec.ofNat 32 p < nw := hc; rw [BitVec.lt_def, hp32_tn] at h1; exact h1
            clear hc; c0_hstraight; c0_hsplit
            · have hp_lt32 : p < 32 := by c0_bv_omega [hc]
              clear hc; c0_hstraight; c0_hsplit
              · have hp2_lt : 2 ^ p < w.toNat := by
                  rw [show (1 : BitVec 64).toNat = 1 from rfl,
                    shift1_nat_shl1_mod hp_lt32] at hc
                  exact hc
                clear hc
                have hdist := shift1_dist_toNat hp_lt32
                have hb_sw : ((bOff + BitVec.ofNat 32 p).setWidth 64).toNat = bOff.toNat + p := by
                  rw [shift1_setWidth64_toNat, BitVec.toNat_add, hp32_tn,
                    Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
                c0_hstraight
                refine wp_join0 (fun mN => ∃ hdrN gN awN htN lpN,
                    ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R
                      (p + 1, hdrN, gN, awN, htN, lpN) mN h) ?_ ?_
                · intro _ mN ⟨hdrN, gN, awN, htN, lpN, hinvN⟩
                  c0_hsteps
                  rw [shift1_bv32_succ_add (by have := nw.isLt; omega)]
                  exact ih_w (p + 1, hdrN, gN, awN, htN, lpN) mN (by dsimp only; omega) hinvN
                · intro J_ac hJ_ac
                  c0_hstraight; c0_hsplit
                  · have hcond_eq :
                        lpP[((bOff + BitVec.ofNat 32 p).setWidth 64).toNat]'(by
                          rw [hb_sw, hlpP_len, hcap0]; omega) =
                        lp0.getD (bOff.toNat + p) 0#32 := by
                      rw [← shift1_getD_eq_getElem lpP (by rw [hb_sw, hlpP_len, hcap0]; omega),
                        hb_sw]
                      exact hpreP _ (by omega)
                    clear hc
                    exact shiftVar_inner_wp hRel hCopy hIte hoom0 hop_t hop_disj hsla hslb hcap0
                      hfit1 hfit2 hl1_eq hl2_eq hw_pos hp_lt hp_lt32 hp2_lt hb_hi hdist hwfb0
                      ⟨hp_nw, hp_32, hfrP, hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP,
                        hevP, hmP⟩
                      hcond_eq hJ_ac hQ
                  · have hcond0 : lpP[bOff.toNat + p]'(by rw [hlpP_len, hcap0]; omega) = 0#32 := by
                      have hget : lpP[bOff.toNat + p]'(by rw [hlpP_len, hcap0]; omega) =
                          lpP[((bOff + BitVec.ofNat 32 p).setWidth 64).toNat]'(by
                            rw [hb_sw, hlpP_len, hcap0]; omega) := by
                        congr 1; exact hb_sw.symm
                      rw [hget]; c0_bv_omega [hc]
                    clear hc
                    have hcond0' : lpP.getD (bOff.toNat + p) 0#32 = 0#32 := by
                      rw [shift1_getD_eq_getElem lpP (by rw [hlpP_len, hcap0]; omega), hcond0]
                    exact hJ_ac mP ⟨hdrP, gP, awP, htP, lpP, shiftPhase2Inv_cond_false hp_lt hp_lt32
                      hp2_lt hop_disj (by rw [hcap0]; omega) hb_hi
                      ⟨hp_nw, hp_32, hfrP, hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP,
                        hevP, hmP⟩ hcond0'⟩
              · have hpw_le : w.toNat ≤ 2 ^ p := by
                  rw [show (1 : BitVec 64).toNat = 1 from rfl,
                    shift1_nat_shl1_mod hp_lt32] at hc
                  omega
                clear hc
                exact hJ_rel mP ⟨hdrP, gP, awP, htP, lpP, fun _ => hpw_le, hp_nw, hp_32, hfrP,
                  hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP, hevP, hmP⟩
            · have hp_eq32 : p = 32 := by c0_bv_omega [hc]
              clear hc
              have hpw_le : w.toNat ≤ 2 ^ p := by rw [hp_eq32]; exact Nat.le_of_lt w.isLt
              exact hJ_rel mP ⟨hdrP, gP, awP, htP, lpP, fun _ => hpw_le, hp_nw, hp_32, hfrP,
                hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP, hevP, hmP⟩
          · have hp_eq : p = nw.toNat := by
              have h1 : ¬ BitVec.ofNat 32 p < nw := hc; rw [BitVec.lt_def, hp32_tn] at h1; omega
            clear hc
            exact hJ_rel mP ⟨hdrP, gP, awP, htP, lpP, fun hlt => absurd hp_eq (Nat.ne_of_lt hlt),
              hp_nw, hp_32, hfrP, hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP, hevP, hmP⟩
  · have hcond2 : ¬ ({ hdr0 with lits_len := hdr0.lits_len + w }.oom = 0#32 ∧
        { hdr0 with lits_len := hdr0.lits_len + w }.lits_len.toNat ≤ hdr0.lits_cap.toNat ∧
        w.toNat ≤ hdr0.lits_cap.toNat - (hdr0.lits_len + w).toNat) := fun h => hfit2 h.2.2
    rw [ite_eq_right hcond2]; dsimp only
    rw [ite_eq_right (fun h => h hoom0)]
    intro m3 hm3
    c0_hstraight; c0_hsplit
    · clear hc
      c0_hcall hRel
      refine ⟨{ hdr0 with lits_len := hdr0.lits_len + w, oom := 1#32 },
        array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
        array (t := i32) hdr0.lits_ptr lp1 ⋆ R, sep_ac hm3, fun m4 hm4 => ?_⟩
      dsimp only at hm4; rw [ite_eq_left (Nat.le_refl _)] at hm4
      c0_hsteps
      have hfr3 := hfr1.trans
        (ops_lits_pure_guard_oom { hdr0 with lits_len := hdr0.lits_len + w }).2.2.2
      have haig3 := shift1_aigInv_with_oom haig1 1#32
      exact shiftVar_oom_close hfr3 (shift1_aig_le_self g0) haig3 hlp1_len
        (by dsimp only; rw [hl1_eq]; omega) (by dsimp only; rw [hl1_eq]; omega)
        (fun q hq => hout1 q (Or.inl hq)) (show (1#32 : BitVec 32) ≠ 0#32 from by decide)
        (sep_ac hm4) hQ
    · exfalso; cases hc

theorem shiftVar_fill_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {mK : Mem 64}
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {aOff w bOff nw op ah : BitVec 32} {p0 k : Nat}
    {hdr0 hdrK : BVHdrState} {g0 gK : Aig} {awK : List (BitVec 64)}
    {htK lp0 lpS : List (BitVec 32)} {R : Mem 64 → Prop} {J_out2 : Cont []}
    (hop_disj : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat)
    (hw_pos : 0 < w.toNat)
    (hp0_nw : p0 ≤ nw.toNat) (hpw : w.toNat ≤ 2 ^ p0)
    (hlpS_len : lpS.length = lp0.length)
    (hpreS : ∀ q < hdr0.lits_len.toNat, lpS.getD q 0#32 = lp0.getD q 0#32)
    (hdone : k = nw.toNat ∨ ah = 1#32) (hk_hiE : k ≤ nw.toNat)
    (hfrE : hdr0.OpsFrame hdrK) (hextE : g0 ≤ gK) (haigE : AigInv hdrK gK awK htK)
    (hoomE : hdrK.oom = 0#32) (hlenE : hdrK.lits_len = hdr0.lits_len + w)
    (hwf_ahE : (ah >>> 1).toNat < gK.A + 1 + gK.nodes.size)
    (hwf_sE : SliceLitsWf gK lpS hdr0.lits_len.toNat w.toNat)
    (heval_ahE : ∀ (ρ : Nat → Bool) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      gK.evalLit ρ (UInt32.ofBitVec ah) = anyOrBool (fun i => vb.getLsbD i) p0 k)
    (heval_sE : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      evalPoolSlice gK ρ lpS hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb p0)
    (hmE : (bvHdrMem h hdrK ⋆ array64 hdrK.aig_ptr awK ⋆
      array (t := i32) hdrK.ht_ptr htK ⋆ array (t := i32) hdr0.lits_ptr lpS ⋆ R) mK)
    (hJ_out2 : ∀ (xs : Tup Val []) (m : Mem 64),
      ShiftDoneInv aOff w bOff nw op hdr0 g0 lp0 R h m → J_out2 xs m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig) (aigWords' : List (BitVec 64))
      (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat → hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ q < hdr0.lits_len.toNat, litsPool'.getD q 0#32 = lp0.getD q 0#32) →
      (hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (bvShiftSem op va vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (shiftVarFillExpr h w op hdr0.lits_len hdr0.lits_ptr ah J_out2) mK := by
  dsimp only [shiftVarFillExpr, svCmp, svBin, svAddrLit, svLoadLit, svLoadOom, svZext, svAdd64]
  refine wp_join_state (α := BitVec 32) (fun f => (f, ()))
    (fun f mFl => (f >>> 1).toNat < gK.A + 1 + gK.nodes.size ∧
      (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
        SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
        SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
        gK.evalLit ρ (UInt32.ofBitVec f) =
          if op = 21#32 then (bvShiftCur op va vb p0).getLsbD (w.toNat - 1)
          else false) ∧ mFl = mK) ?_ ?_
  · intro _ fill mFl ⟨hwf_fl, hev_fl, hmFl⟩; cases hmFl
    have hany_fin := shiftVar_any_fin_eval hdone hk_hiE heval_ahE
    c0_hstraight
    refine wp_while_state (α := Nat × BVHdrState × Aig × List (BitVec 64) ×
        List (BitVec 32) × List (BitVec 32))
      (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
      (fun st mL =>
        ShiftFillInv aOff w bOff nw op hdr0 g0 lp0 R p0 ah fill st mL h) ?_ ?_
    · intro J_fl hJ_fl; c0_hsteps
      exact hJ_fl (0, hdrK, gK, awK, htK, lpS) mK
        ⟨Nat.zero_le _, hfrE, hextE, haigE, hoomE, hlenE, hlpS_len, hpreS, hwf_ahE,
          hwf_fl, hwf_sE, hany_fin, hev_fl, fun ρ va vb i hi hva hvb => by
            rw [ite_eq_right (by omega), ← evalPoolSlice_getLsbD hi,
              heval_sE ρ va vb hva hvb],
          sep_ac hmE⟩
    · intro J_fl ⟨j, hdrL, gL, awL, htL, lpL⟩ mL hinvL ih_fl
      have hj_w := hinvL.1
      have hj32 : (BitVec.ofNat 32 j).toNat = j := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
      c0_hstraight; c0_hsplit
      · have hj_lt : j < w.toNat := by
          have h1 : BitVec.ofNat 32 j < w := hc
          rw [BitVec.lt_def, hj32] at h1; exact h1
        clear hc
        rcases hinvL with ⟨_, hfrL, hextL, haigL, hoomL, hlenL, hlpL_len, hpreL,
          hwf_ahL, hwf_flL, hwf_sL, hany_L, hev_flL, hbefL, hmL⟩
        have houtj_sw : ((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
            hdr0.lits_len.toNat + j := by
          rw [shift1_setWidth64_toNat, BitVec.toNat_add, hj32,
            Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
        have hout_ag :
            lpL[((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat]'(by
              rw [houtj_sw, hlpL_len, hcap0]; omega) =
            lpL.getD (hdr0.lits_len.toNat + j) 0#32 := by
          rw [← shift1_getD_eq_getElem lpL (by rw [houtj_sw, hlpL_len, hcap0]; omega),
            houtj_sw]
        c0_hstraight; c0_hcall hIte
        refine ⟨hdrL, gL, awL, htL, array (t := i32) hdr0.lits_ptr lpL ⋆ R, haigL,
          fun _ => ⟨by rw [haigL.aig_len_eq]; exact hwf_ahL,
            by rw [haigL.aig_len_eq]; exact hwf_flL,
            by rw [hout_ag, haigL.aig_len_eq]; exact hwf_sL j hj_lt⟩,
          sep_ac hmL,
          fun ret hdrN gN awN htN mN hfrN hextN _ haigN hoomN _ hevN hmN => ?_⟩
        have hfr0N := hfrL.trans hfrN.toOpsFrame
        have hext0N := Aig.extends_trans hextL hextN
        have hlenN : hdrN.lits_len = hdr0.lits_len + w := hfrN.lits_len.trans hlenL
        rw [← hfrL.lits_ptr] at hmN
        have hmN' := ops_aig_frame_unfocus hfrN.toOpsFrame hmN
        rw [hfr0N.lits_ptr] at hmN'
        c0_hstraight
        rw [houtj_sw] at hm
        c0_hsplit
        · have hoom_ne : hdrN.oom ≠ 0#32 := by c0_bv_omega [hc]
          clear hc; c0_hsteps; rw [← hfr0N.lits_ptr] at hm
          exact shiftVar_oom_close (lp' := lpL.set (hdr0.lits_len.toNat + j) ret)
            hfr0N hext0N haigN (by simp [hlpL_len])
            (by rw [hlenN, hl1_eq]; omega) (by rw [hlenN, hl1_eq, hfr0N.lits_cap]; omega)
            (fun q hq => by
              rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
                ← List.getD_eq_getElem?_getD]
              exact hpreL q hq)
            hoom_ne (sep_ac hm) hQ
        · have hoomN0 : hdrN.oom = 0#32 := by c0_bv_omega [hc]
          clear hc
          c0_hsteps
          obtain ⟨hret_bd, hret_ev⟩ := hevN hoomN0
          rw [haigN.aig_len_eq] at hret_bd
          have hstep := shiftVar_fill_ite_step_ok hlpL_len hpreL hwf_ahL hwf_flL hwf_sL
            hany_L hev_flL hbefL hj_lt hw_pos hop_disj hpw
            (by rw [hlpL_len, hcap0]; omega) hextN hret_bd
            (fun ρ => by rw [hret_ev ρ]; dsimp only; rw [hout_ag]) rfl hp0_nw
          rw [shift1_bv32_succ_add (by have := w.isLt; omega)]
          exact ih_fl (j + 1, hdrN, gN, awN, htN, _) _ (by dsimp only; omega)
            ⟨by omega, hfr0N, hext0N, haigN, hoomN0, hlenN, hstep.1, hstep.2.1,
              hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.2.2.1,
              hstep.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2, sep_ac hm⟩
      · have hj_eq : j = w.toNat := by
          have h1 : ¬ BitVec.ofNat 32 j < w := hc
          rw [BitVec.lt_def, hj32] at h1; omega
        clear hc; subst hj_eq
        exact hJ_out2 _ mL (shiftFillInv_done hinvL)
  · intro J_fl hJ_fl
    c0_hstraight; c0_hsplit
    · have hop21 : op = 21#32 := by c0_bv_omega [hc]
      clear hc
      have hwm1_sw : ((hdr0.lits_len + (w - (1 : BitVec 32))).setWidth 64).toNat =
          hdr0.lits_len.toNat + (w.toNat - 1) := by
        rw [shift1_setWidth64_toNat, BitVec.toNat_add,
          show (w - 1).toNat = w.toNat - 1 from shift1_sub1_toNat hw_pos,
          Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
      c0_hsteps
      have hwm1_eq :
          lpS[((hdr0.lits_len + (w - (1 : BitVec 32))).setWidth 64).toNat]'(by
            rw [hwm1_sw, hlpS_len, hcap0]; omega) =
          lpS[hdr0.lits_len.toNat + (w.toNat - 1)]'(by rw [hlpS_len, hcap0]; omega) := by
        congr 1
      rw [hwm1_eq]
      refine hJ_fl _ mK ⟨by
        rw [← shift1_getD_eq_getElem lpS (by rw [hlpS_len, hcap0]; omega)]
        exact hwf_sE (w.toNat - 1) (by omega), fun ρ va vb hva hvb => ?_, rfl⟩
      rw [ite_eq_left hop21]
      exact (shiftVar_sbit_in_bounds hwf_sE (heval_sE ρ va vb hva hvb)
        (by rw [hlpS_len, hcap0]; omega) (by omega)).2
    · have hop_ne : op ≠ 21#32 := by c0_bv_omega [hc]
      clear hc; c0_hsteps
      exact hJ_fl 0#32 mK ⟨SliceLitsWf.zero_shr1 gK, fun ρ _ _ _ _ => by
        rw [ite_eq_right hop_ne, evalLit_ofBv_zero], rfl⟩

theorem shiftVar_tail_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {mS : Mem 64}
    (hOr : Γ.Has "bv_aig_or" bvAigOrSpec) (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : BitVec 64} {aOff w bOff nw op : BitVec 32} {p0 : Nat}
    {hdr0 hdrS : BVHdrState} {g0 gS : Aig} {awS : List (BitVec 64)}
    {htS lp0 lpS : List (BitVec 32)} {R : Mem 64 → Prop}
    (hoom0 : hdr0.oom = 0#32)
    (hop_t : decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true)
    (hop_disj : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (hsla : sliceOkBool hdr0 aOff w = true) (hslb : sliceOkBool hdr0 bOff nw = true)
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat)
    (hw_pos : 0 < w.toNat)
    (hb_hi : bOff.toNat + nw.toNat ≤ hdr0.lits_len.toNat)
    (hwfb0 : SliceLitsWf g0 lp0 bOff.toNat nw.toNat)
    (hstS : ShiftStageInv aOff w bOff nw op hdr0 g0 lp0 R (p0, hdrS, gS, awS, htS, lpS) mS h)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig) (aigWords' : List (BitVec 64))
      (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ q < hdr0.lits_len.toNat, litsPool'.getD q 0#32 = lp0.getD q 0#32) →
      (hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (bvShiftSem op va vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (shiftVarTailExpr h w bOff nw op hdr0.lits_len hdr0.lits_ptr
      (BitVec.ofNat 32 p0)) mS := by
  have hpreS := hstS.2.2.2.2.2.2.2.2.2.1
  have hlpS_len := hstS.2.2.2.2.2.2.2.2.1
  have hp0_nw := hstS.1; have hp0_32 := hstS.2.1; have hpw0 := hstS.2.2.1
  dsimp only [shiftVarTailExpr, svCmp, svBin, svAddrLit, svLoadLit, svLoadOom, svZext, svAdd64]
  refine wp_join_group (fun _ mF => ShiftDoneInv aOff w bOff nw op hdr0 g0 lp0 R h mF) ?_ ?_
  · intro _ _ mF ⟨hdrF, gF, awF, htF, lpF, hfrF, hextF, haigF, hoomF, hlenF, hlpF_len, hpreF,
      hwfF, hevF, hmF⟩
    c0_hsteps
    have hlenF_n : hdrF.lits_len.toNat = hdr0.lits_len.toNat + w.toNat := by rw [hlenF, hl1_eq]
    exact shiftVar_ok_close hoom0 hop_t hsla hslb hfrF hextF haigF hlpF_len
      (by rw [hlenF_n]; omega) (by rw [hlenF_n, hfrF.lits_cap]; omega) hcap0 (by omega)
      hpreF hoomF hlenF hwfF hevF hmF hQ
  · intro J_out hJ_out
    c0_hstraight; c0_hsplit
    · have hp0_lt : p0 < nw.toNat := by
        have h1 : BitVec.ofNat 32 p0 < nw := hc
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp0_32] at h1; exact h1
      clear hc
      have hpw : w.toNat ≤ 2 ^ p0 := hpw0 hp0_lt
      c0_hstraight
      refine wp_while_state (α := Nat × BitVec 32 × BVHdrState × Aig × List (BitVec 64) ×
          List (BitVec 32))
        (fun (k, ah, _) => (BitVec.ofNat 32 k, ah, ()))
        (fun (k, ah, _) => nw.toNat - k + if ah = 1#32 then 0 else 1)
        (fun st mK => ShiftOrInv aOff w bOff nw op hdr0 g0 lp0 R p0 st mK h lpS) ?_ ?_
      · intro J_or hJ_or; c0_hsteps
        rcases hstS with ⟨_, _, _, hfrS, hextS, haigS, hoomS, hlenS, _, _, hwfS, hevS, hmS⟩
        exact hJ_or (p0, 0#32, hdrS, gS, awS, htS) mS
          ⟨Nat.le_refl _, hp0_nw, fun h1 => absurd h1 (by decide), hfrS, hextS, haigS, hoomS,
            hlenS, SliceLitsWf.zero_shr1 gS, hwfS,
            fun ρ _ _ => by rw [evalLit_ofBv_zero, anyOrBool_le _ (Nat.le_refl _)],
            hevS, sep_ac hmS⟩
      · intro J_or ⟨k, ah, hdrK, gK, awK, htK⟩ mK hinvK ih_or
        have hk_nw := hinvK.2.1
        have hk32 : (BitVec.ofNat 32 k).toNat = k := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := nw.isLt; omega)]
        refine wp_join0 (fun mEx => mEx = mK ∧ (k = nw.toNat ∨ ah = 1#32)) ?_ ?_
        · intro _ mEx ⟨hmEx, hdone⟩
          cases hmEx
          rcases hinvK with ⟨hk_loE, hk_hiE, hah1E, hfrE, hextE, haigE, hoomE, hlenE, hwf_ahE,
            hwf_sE, heval_ahE, heval_sE, hmE⟩
          refine wp_join_group (fun _ mF => ShiftDoneInv aOff w bOff nw op hdr0 g0 lp0 R h mF)
            (fun _ _ mF hd => by c0_hsteps; exact hJ_out _ mF hd) ?_
          intro J_out2 hJ_out2
          c0_hstraight; c0_hsplit
          · have hah_nz : ah ≠ 0#32 := by c0_bv_omega [hc]
            clear hc
            exact shiftVar_fill_wp hIte hop_disj hcap0 hfit1 hl1_eq hw_pos hp0_nw hpw hlpS_len
              hpreS hdone hk_hiE hfrE hextE haigE hoomE hlenE hwf_ahE hwf_sE heval_ahE heval_sE
              hmE hJ_out2 hQ
          · have hah0 : ah = 0#32 := by c0_bv_omega [hc]
            clear hc; subst hah0
            have hk_eq : k = nw.toNat := hdone.elim id (fun h => by cases h)
            subst hk_eq
            exact hJ_out2 _ mK (shiftOrInv_noHi_done hp0_nw (Nat.le_refl _) hdone hlpS_len hpreS
              ⟨hk_loE, hk_hiE, hah1E, hfrE, hextE, haigE, hoomE, hlenE, hwf_ahE, hwf_sE,
                heval_ahE, heval_sE, hmE⟩)
        · intro J_ex hJ_ex
          rcases hinvK with ⟨hk_lo, hk_hi, hah1, hfrK, hextK, haigK, hoomK, hlenK, hwf_ah,
            hwf_sK, heval_ah, heval_sK, hmK⟩
          c0_hstraight; c0_hsplit
          · have hk_lt : k < nw.toNat := by
              have h1 : BitVec.ofNat 32 k < nw := hc; rw [BitVec.lt_def, hk32] at h1; exact h1
            clear hc; c0_hstraight; c0_hsplit
            · have hah_ne : ah ≠ 1#32 := by c0_bv_omega [hc]
              clear hc
              have hb_sw : ((bOff + BitVec.ofNat 32 k).setWidth 64).toNat = bOff.toNat + k := by
                rw [shift1_setWidth64_toNat, BitVec.toNat_add, hk32,
                  Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
              have hlp_bk : lpS[((bOff + BitVec.ofNat 32 k).setWidth 64).toNat]'(by
                    rw [hb_sw, hlpS_len, hcap0]; omega) =
                  lp0.getD (bOff.toNat + k) 0#32 := by
                rw [← shift1_getD_eq_getElem lpS (by rw [hb_sw, hlpS_len, hcap0]; omega), hb_sw]
                exact hpreS _ (by omega)
              have hwf_bk : ((lp0.getD (bOff.toNat + k) 0#32) >>> 1).toNat <
                  gK.A + 1 + gK.nodes.size := by
                have hsz : g0.A + 1 + g0.nodes.size ≤ gK.A + 1 + gK.nodes.size := by
                  have := hextK.1; have := hextK.2.1; omega
                exact Nat.lt_of_lt_of_le (hwfb0 k hk_lt) hsz
              c0_hstraight; c0_hcall hOr
              refine ⟨hdrK, gK, awK, htK, array (t := i32) hdr0.lits_ptr lpS ⋆ R, haigK,
                fun _ => ⟨by rw [haigK.aig_len_eq]; exact hwf_ah,
                  by rw [hlp_bk, haigK.aig_len_eq]; exact hwf_bk⟩,
                sep_ac hmK, fun ret hdrN gN awN htN mN hfrN hextN _ haigN hoomN _ hevN hmN => ?_⟩
              have hfr0N := hfrK.trans hfrN.toOpsFrame
              have hext0N := Aig.extends_trans hextK hextN
              have hlenN : hdrN.lits_len = hdr0.lits_len + w := hfrN.lits_len.trans hlenK
              rw [← hfrK.lits_ptr] at hmN
              have hmN' := ops_aig_frame_unfocus hfrN.toOpsFrame hmN
              rw [hfr0N.lits_ptr] at hmN'
              c0_hstraight; c0_hsplit
              · have hoom_ne : hdrN.oom ≠ 0#32 := by c0_bv_omega [hc]
                clear hc; c0_hsteps; rw [← hfr0N.lits_ptr] at hmN'
                exact shiftVar_oom_close hfr0N hext0N haigN hlpS_len
                  (by rw [hlenN, hl1_eq]; omega) (by rw [hlenN, hl1_eq, hfr0N.lits_cap]; omega)
                  hpreS hoom_ne (sep_ac hmN') hQ
              · have hoomN0 : hdrN.oom = 0#32 := by c0_bv_omega [hc]
                clear hc
                c0_hsteps
                obtain ⟨hret_bd, hret_ev⟩ := hevN hoomN0
                rw [haigN.aig_len_eq] at hret_bd
                rw [shift1_bv32_succ_add (by have := nw.isLt; omega)]
                exact ih_or (k + 1, ret, hdrN, gN, awN, htN) mN
                  (by dsimp only; simp only [hah_ne, ↓reduceIte]; split <;> omega)
                  (shiftOrInv_or_step (_awK := awK) (_htK := htK) hk_lo hk_lt hfrK hextK hlenK
                    hwf_sK heval_ah heval_sK hfrN hextN haigN hoomN0 hret_bd
                    (fun ρ => by dsimp only at hret_ev ⊢; rw [hret_ev ρ, hlp_bk]) hwfb0
                    (by rw [hcap0]; omega) (sep_ac hmN'))
            · have hah1_eq : ah = 1#32 := by c0_bv_omega [hc]
              clear hc; subst hah1_eq
              exact hJ_ex mK ⟨rfl, Or.inr rfl⟩
          · have hk_eq : k = nw.toNat := by
              have h1 : ¬ BitVec.ofNat 32 k < nw := hc; rw [BitVec.lt_def, hk32] at h1; omega
            clear hc; subst hk_eq
            exact hJ_ex mK ⟨rfl, Or.inl rfl⟩
    · have hp0_eq : p0 = nw.toNat := by
        have h1 : ¬ BitVec.ofNat 32 p0 < nw := hc
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp0_32] at h1; omega
      clear hc
      exact hJ_out _ mS (shiftStageInv_tail_done hstS hp0_eq)

end

end LeanQbe.T.Examples.Bitblast.Proof
