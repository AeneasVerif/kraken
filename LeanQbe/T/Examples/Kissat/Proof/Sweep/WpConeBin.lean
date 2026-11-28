/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpCone0

/-!
# Step 13 `full_m6_sweep_cone` Binary Watch Loop (`Kissat.Proof.Sweep.WpConeBin`)

Proves `step13_cone_bin_watch_wp` and `step13_cone_bin_pass_wp` for the binary-watch inner and
polarity loops of `full_m6_sweep_cone`. Zero legacy imports; zero `@[expose]` on theorems.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten

open scoped FullArenaTactics FullK6DynMem

/-! ## 1. C0 Expression Definitions for Binary Watch Scanning -/

abbrev binCmpOp {t : Ty} (c : CmpOp) (a b : Arg Val t)
    (h : Ty.bool = t.mask := by rfl) : Op Val [Ty.bool] :=
  Op.mk (OpCode.cmp c t Ty.bool h) (a, b, ())

abbrev binMkOp {ts rs : List Ty} (c : OpCode ts rs) (a : Tup (Arg Val) ts) :
    Op Val rs :=
  Op.mk c a

@[expose] def s13BinWatchExpr (pH pWstk pVals pFl pTmk pTmp pWs pK : Val i64)
    (aPol aLit aCv aCurTmk aMvC aLimV aMaxOrig aLayerStart aNv0 aNc0 : Arg Val i32)
    (aLim0 : Arg Val Ty.bool) (aP0 aWEnd64 : Arg Val i64)
    (k_done : Val i32 → Val i32 → Arg Val Ty.bool → Val i64 → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group (fun (Jw : Tup Cont [[i32, i32, Ty.bool, i64]]) =>
    Blocks.cons (fun (p : Tup Val [i32, i32, Ty.bool, i64]) =>
      Expr.let_ (binCmpOp .ult (Arg.var p.snd.snd.snd.fst) aWEnd64) fun hp =>
      Expr.jnz (Arg.var hp.fst)
        (Expr.jnz (Arg.var p.snd.snd.fst)
          (k_done p.fst p.snd.fst (Arg.var p.snd.snd.fst) p.snd.snd.snd.fst)
          (Expr.let_ (binCmpOp .ult (Arg.var p.snd.fst) aMaxOrig) fun hnc =>
            Expr.jnz (Arg.var hnc.fst)
              (Expr.let_ (binMkOp (OpCode.mul i64) (Arg.var p.snd.snd.snd.fst, Arg.imm 4, ()))
                fun p4 =>
                Expr.let_ (binMkOp (OpCode.add i64) (Arg.var pWstk, Arg.var p4.fst, ()))
                  fun pwa =>
                Expr.load i32 (Arg.var pwa.fst) fun w0 =>
                Expr.let_ (binMkOp (OpCode.add i64) (Arg.var p.snd.snd.snd.fst, Arg.imm 1, ()))
                  fun p1 =>
                Expr.let_ (binMkOp (OpCode.and i32) (Arg.var w0, Arg.imm 2147483648, ()))
                  fun wbin =>
                Expr.let_ (binCmpOp .eq (Arg.var wbin.fst) (Arg.imm 0)) fun hnotbin =>
                Expr.jnz (Arg.var hnotbin.fst)
                  (Expr.let_ (binMkOp (OpCode.add i64) (Arg.var p1.fst, Arg.imm 1, ())) fun p2 =>
                    Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
                      Arg.var p2.fst, ()))
                  (Expr.let_ (binMkOp (OpCode.and i32) (Arg.var w0, Arg.imm 2147483647, ()))
                    fun ot =>
                    Expr.let_ (binMkOp (OpCode.lshr i32) (Arg.var ot.fst, Arg.imm 1, ())) fun ov =>
                    Expr.let_ (binMkOp (OpCode.zext 32 64) (Arg.var ov.fst, ())) fun ovz =>
                    Expr.let_ (binMkOp (OpCode.add i64) (Arg.var pH, Arg.imm 776, ())) fun pcva =>
                    Expr.load i64 (Arg.var pcva.fst) fun cv64 =>
                    Expr.let_ (binCmpOp .uge (Arg.var ovz.fst) (Arg.var cv64)) fun hov =>
                    Expr.jnz (Arg.var hov.fst)
                      (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
                        Arg.var p1.fst, ()))
                      (Expr.let_ (binMkOp (OpCode.zext 32 64) (Arg.var ov.fst, ())) fun ovz2 =>
                        Expr.let_ (binMkOp (OpCode.mul i64) (Arg.var ovz2.fst, Arg.imm 4, ()))
                          fun ov4 =>
                        Expr.let_ (binMkOp (OpCode.add i64) (Arg.var pFl, Arg.var ov4.fst, ()))
                          fun pfa =>
                        Expr.load i32 (Arg.var pfa.fst) fun fl =>
                        Expr.let_ (binMkOp (OpCode.and i32) (Arg.var fl, Arg.imm 1, ())) fun fl1 =>
                        Expr.let_ (binCmpOp .eq (Arg.var fl1.fst) (Arg.imm 0)) fun hfl0 =>
                        Expr.jnz (Arg.var hfl0.fst)
                          (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst,
                            Arg.var p.snd.snd.fst, Arg.var p1.fst, ()))
                          (Expr.let_ (binMkOp (OpCode.zext 32 64) (Arg.var ot.fst, ())) fun otz =>
                            Expr.let_ (binMkOp (OpCode.add i64)
                                (Arg.var pVals, Arg.var otz.fst, ())) fun pva =>
                            Expr.load i8 (Arg.var pva.fst) fun ovv =>
                            Expr.let_ (binMkOp (OpCode.trunc 32 8) (Arg.imm 0, ())) fun z8 =>
                            Expr.let_ (binMkOp (OpCode.sext 8 32) (Arg.var ovv, ())) fun ovs =>
                            Expr.let_ (binMkOp (OpCode.sext 8 32) (Arg.var z8.fst, ())) fun zs =>
                            Expr.let_ (binCmpOp .sgt (Arg.var ovs.fst) (Arg.var zs.fst))
                              fun hsgt =>
                            Expr.jnz (Arg.var hsgt.fst)
                              (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst,
                                Arg.var p.snd.snd.fst, Arg.var p1.fst, ()))
                              (Expr.let_ (binCmpOp .eq (Arg.var ov.fst) aCv) fun heqcv =>
                                Expr.jnz (Arg.var heqcv.fst)
                                  (Expr.group (fun _ =>
                                    Blocks.cons (fun (pb : Tup Val [i32, Ty.bool]) =>
                                      Expr.jump Jw.fst (Arg.var p.fst, Arg.var pb.fst,
                                        Arg.var pb.snd.fst, Arg.var p1.fst, ())) Blocks.nil)
                                    fun Jb =>
                                    Expr.let_ (binCmpOp .eq (Arg.var ot.fst) aLit) fun heqlit =>
                                    Expr.jnz (Arg.var heqlit.fst)
                                      (s13BinUnitCallExpr pH pTmp pK aCurTmk aPol
                                        (Arg.var p.snd.fst) (Arg.var p.snd.snd.fst)
                                        (fun nc' lim' =>
                                          Expr.jump Jb.fst (Arg.var nc', Arg.var lim', ())))
                                      (Expr.jump Jb.fst (Arg.var p.snd.fst,
                                        Arg.var p.snd.snd.fst, ())))
                                  (Expr.let_ (binMkOp (OpCode.trunc 32 8) (Arg.imm 0, ()))
                                      fun z8b =>
                                    Expr.let_ (binMkOp (OpCode.sext 8 32) (Arg.var ovv, ()))
                                      fun ovsb =>
                                    Expr.let_ (binMkOp (OpCode.sext 8 32) (Arg.var z8b.fst, ()))
                                      fun zsb =>
                                    Expr.let_ (binCmpOp .slt (Arg.var ovsb.fst) (Arg.var zsb.fst))
                                      fun hslt =>
                                    Expr.jnz (Arg.var hslt.fst)
                                      (s13BinUnitCallExpr pH pTmp pK aCurTmk aPol
                                        (Arg.var p.snd.fst) (Arg.var p.snd.snd.fst)
                                        (fun nc' lim' =>
                                          Expr.jump Jw.fst (Arg.var p.fst, Arg.var nc',
                                            Arg.var lim', Arg.var p1.fst, ())))
                                      (Expr.group (fun _ =>
                                        Blocks.cons (fun (_ : Tup Val []) =>
                                          Expr.group (fun _ =>
                                            Blocks.cons (fun (pb : Tup Val [i32, Ty.bool]) =>
                                              Expr.let_ (binMkOp (OpCode.sext 32 64)
                                                  (Arg.imm 0, ())) fun i0 =>
                                              Expr.let_ (binMkOp (OpCode.mul i64)
                                                  (Arg.var i0.fst, Arg.imm 4, ())) fun i04 =>
                                              Expr.let_ (binMkOp (OpCode.add i64)
                                                  (Arg.var pTmp, Arg.var i04.fst, ())) fun pa0 =>
                                              Expr.let_ (binMkOp (OpCode.shl i32)
                                                  (aCurTmk, Arg.imm 1, ())) fun c1 =>
                                              Expr.let_ (binMkOp (OpCode.or i32)
                                                  (Arg.var c1.fst, aPol, ())) fun l0 =>
                                              Expr.store (Arg.var l0.fst) (Arg.var pa0.fst)
                                                (Expr.let_ (binMkOp (OpCode.sext 32 64)
                                                    (Arg.imm 1, ())) fun i1 =>
                                                Expr.let_ (binMkOp (OpCode.mul i64)
                                                    (Arg.var i1.fst, Arg.imm 4, ())) fun i14 =>
                                                Expr.let_ (binMkOp (OpCode.add i64)
                                                    (Arg.var pTmp, Arg.var i14.fst, ())) fun pa1 =>
                                                Expr.let_ (binMkOp (OpCode.zext 32 64)
                                                    (Arg.var ov.fst, ())) fun ovz4 =>
                                                Expr.let_ (binMkOp (OpCode.mul i64)
                                                    (Arg.var ovz4.fst, Arg.imm 4, ())) fun ov4_4 =>
                                                Expr.let_ (binMkOp (OpCode.add i64)
                                                    (Arg.var pTmk, Arg.var ov4_4.fst, ()))
                                                  fun pta4 =>
                                                Expr.load i32 (Arg.var pta4.fst) fun ld2 =>
                                                Expr.let_ (binMkOp (OpCode.sub i32)
                                                    (Arg.var ld2, Arg.imm 1, ())) fun lm1 =>
                                                Expr.let_ (binMkOp (OpCode.shl i32)
                                                    (Arg.var lm1.fst, Arg.imm 1, ())) fun lm1s =>
                                                Expr.let_ (binMkOp (OpCode.and i32)
                                                    (Arg.var ot.fst, Arg.imm 1, ())) fun ot1 =>
                                                Expr.let_ (binMkOp (OpCode.or i32)
                                                    (Arg.var lm1s.fst, Arg.var ot1.fst, ()))
                                                  fun l1 =>
                                                Expr.store (Arg.var l1.fst) (Arg.var pa1.fst)
                                                  (s13AddClauseBlockExpr pH pTmp pK pWs pTmk
                                                    (Arg.imm 2) (Arg.var p.fst) (Arg.var pb.fst)
                                                    (Arg.var p.snd.fst) aLimV (Arg.var pb.snd.fst)
                                                    (fun nv'' nc'' lim'' =>
                                                      Expr.jump Jw.fst (Arg.var nv'', Arg.var nc'',
                                                        Arg.var lim'', Arg.var p1.fst, ())))))
                                            Blocks.nil)
                                            fun Jb =>
                                            Expr.let_ (binMkOp (OpCode.zext 32 64)
                                                (Arg.var ov.fst, ())) fun ovz3 =>
                                            Expr.let_ (binMkOp (OpCode.mul i64)
                                                (Arg.var ovz3.fst, Arg.imm 4, ())) fun ov4_3 =>
                                            Expr.let_ (binMkOp (OpCode.add i64)
                                                (Arg.var pTmk, Arg.var ov4_3.fst, ())) fun pta3 =>
                                            Expr.load i32 (Arg.var pta3.fst) fun t0 =>
                                            Expr.let_ (binCmpOp .eq (Arg.var t0) (Arg.imm 0))
                                              fun ht0 =>
                                            Expr.jnz (Arg.var ht0.fst)
                                              (Expr.let_ (binCmpOp .uge (Arg.var p.fst) aMvC)
                                                  fun hmv =>
                                                Expr.jnz (Arg.var hmv.fst)
                                                  (k_done p.fst p.snd.fst (Arg.imm true) p1.fst)
                                                  (Expr.let_ (binMkOp (OpCode.zext 32 64)
                                                      (Arg.var p.fst, ())) fun nvz =>
                                                    Expr.let_ (binMkOp (OpCode.mul i64)
                                                        (Arg.var nvz.fst, Arg.imm 4, ())) fun nv4 =>
                                                    Expr.let_ (binMkOp (OpCode.add i64)
                                                        (Arg.var pWs, Arg.var nv4.fst, ()))
                                                      fun pwsa =>
                                                    Expr.store (Arg.var ov.fst) (Arg.var pwsa.fst)
                                                      (Expr.let_ (binMkOp (OpCode.add i32)
                                                          (Arg.var p.fst, Arg.imm 1, ())) fun nv1 =>
                                                      Expr.let_ (binMkOp (OpCode.zext 32 64)
                                                          (Arg.var ov.fst, ())) fun ovz3b =>
                                                      Expr.let_ (binMkOp (OpCode.mul i64)
                                                          (Arg.var ovz3b.fst, Arg.imm 4, ()))
                                                        fun ov4_3b =>
                                                      Expr.let_ (binMkOp (OpCode.add i64)
                                                          (Arg.var pTmk, Arg.var ov4_3b.fst, ()))
                                                        fun pta3b =>
                                                      Expr.store (Arg.var nv1.fst)
                                                        (Arg.var pta3b.fst)
                                                        (Expr.jump Jb.fst (Arg.var nv1.fst,
                                                          Arg.var p.snd.snd.fst, ())))))
                                              (Expr.jump Jb.fst (Arg.var p.fst,
                                                Arg.var p.snd.snd.fst, ())))
                                          Blocks.nil)
                                        fun Ja =>
                                        Expr.let_ (binMkOp (OpCode.zext 32 64)
                                            (Arg.var ov.fst, ())) fun ovz2 =>
                                        Expr.let_ (binMkOp (OpCode.mul i64)
                                            (Arg.var ovz2.fst, Arg.imm 4, ())) fun ov4_2 =>
                                        Expr.let_ (binMkOp (OpCode.add i64)
                                            (Arg.var pTmk, Arg.var ov4_2.fst, ())) fun pta2 =>
                                        Expr.load i32 (Arg.var pta2.fst) fun old =>
                                        Expr.let_ (binCmpOp .ne (Arg.var old) (Arg.imm 0))
                                          fun hnz =>
                                        Expr.jnz (Arg.var hnz.fst)
                                          (Expr.let_ (binMkOp (OpCode.zext 32 64)
                                              (Arg.var ov.fst, ())) fun ovz2b =>
                                            Expr.let_ (binMkOp (OpCode.mul i64)
                                                (Arg.var ovz2b.fst, Arg.imm 4, ())) fun ov4_2b =>
                                            Expr.let_ (binMkOp (OpCode.add i64)
                                                (Arg.var pTmk, Arg.var ov4_2b.fst, ()))
                                              fun pta2b =>
                                            Expr.load i32 (Arg.var pta2b.fst) fun old2 =>
                                            Expr.let_ (binMkOp (OpCode.sub i32)
                                                (Arg.var old2, Arg.imm 1, ())) fun old1 =>
                                            Expr.let_ (binCmpOp .ult (Arg.var old1.fst) aLayerStart)
                                              fun hls =>
                                            Expr.jnz (Arg.var hls.fst)
                                              (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst,
                                                Arg.var p.snd.snd.fst, Arg.var p1.fst, ()))
                                              (Expr.jump Ja.fst ()))
                                          (Expr.jump Ja.fst ()))))))))
              (k_done p.fst p.snd.fst (Arg.var p.snd.snd.fst) p.snd.snd.snd.fst)))
        (k_done p.fst p.snd.fst (Arg.var p.snd.snd.fst) p.snd.snd.snd.fst)) Blocks.nil)
    fun Jw => Expr.jump Jw.fst (aNv0, aNc0, aLim0, aP0, ())

@[expose] def s13BinPassExpr (pH pWvec pWstk pVals pFl pTmk pTmp pWs pK : Val i64)
    (aCv aCurTmk aMvC aLimV aMaxOrig aLayerStart aNv0 aNc0 : Arg Val i32)
    (aLim0 : Arg Val Ty.bool)
    (k_done : Val i32 → Val i32 → Val Ty.bool → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group (fun (Jpol : Tup Cont [[i32, i32, Ty.bool, i32]]) =>
    Blocks.cons (fun (p : Tup Val [i32, i32, Ty.bool, i32]) =>
      Expr.group (fun _ =>
        Blocks.cons (fun (_ : Tup Val []) => k_done p.fst p.snd.fst p.snd.snd.fst) Blocks.nil)
        fun Jexit =>
      Expr.let_ (binCmpOp .ult (Arg.var p.snd.snd.snd.fst) (Arg.imm 2)) fun hpol =>
      Expr.jnz (Arg.var hpol.fst)
        (Expr.jnz (Arg.var p.snd.snd.fst) (Expr.jump Jexit.fst ())
          (Expr.let_ (binCmpOp .ult (Arg.var p.snd.fst) aMaxOrig) fun hnc =>
            Expr.jnz (Arg.var hnc.fst)
              (Expr.let_ (binMkOp (OpCode.shl i32) (aCv, Arg.imm 1, ())) fun cv2 =>
                Expr.let_ (binMkOp (OpCode.or i32)
                    (Arg.var cv2.fst, Arg.var p.snd.snd.snd.fst, ())) fun lit =>
                Expr.let_ (binMkOp (OpCode.zext 32 64) (Arg.var lit.fst, ())) fun litz =>
                Expr.let_ (binMkOp (OpCode.sext 32 64) (Arg.imm 1, ())) fun one =>
                Expr.let_ (binMkOp (OpCode.shl i64) (Arg.var litz.fst, Arg.var one.fst, ()))
                  fun l2 =>
                Expr.let_ (binMkOp (OpCode.mul i64) (Arg.var l2.fst, Arg.imm 4, ())) fun wo =>
                Expr.let_ (binMkOp (OpCode.add i64) (Arg.var pWvec, Arg.var wo.fst, ())) fun wa =>
                Expr.load i32 (Arg.var wa.fst) fun woff =>
                Expr.let_ (binMkOp (OpCode.zext 32 64) (Arg.var woff, ())) fun woffz =>
                Expr.let_ (binMkOp (OpCode.zext 32 64) (Arg.var lit.fst, ())) fun litz2 =>
                Expr.let_ (binMkOp (OpCode.sext 32 64) (Arg.imm 1, ())) fun one2 =>
                Expr.let_ (binMkOp (OpCode.shl i64) (Arg.var litz2.fst, Arg.var one2.fst, ()))
                  fun l22 =>
                Expr.let_ (binMkOp (OpCode.add i64) (Arg.var l22.fst, Arg.imm 1, ())) fun l221 =>
                Expr.let_ (binMkOp (OpCode.mul i64) (Arg.var l221.fst, Arg.imm 4, ())) fun wso =>
                Expr.let_ (binMkOp (OpCode.add i64) (Arg.var pWvec, Arg.var wso.fst, ())) fun wsa =>
                Expr.load i32 (Arg.var wsa.fst) fun wsz =>
                Expr.let_ (binMkOp (OpCode.zext 32 64) (Arg.var wsz, ())) fun wszz =>
                Expr.let_ (binMkOp (OpCode.add i64) (Arg.var woffz.fst, Arg.var wszz.fst, ()))
                  fun wend =>
                Expr.group (fun _ =>
                  Blocks.cons (fun (pw : Tup Val [i32, i32, Ty.bool, i64]) =>
                    Expr.let_ (binMkOp (OpCode.add i32)
                        (Arg.var p.snd.snd.snd.fst, Arg.imm 1, ())) fun pol1 =>
                    Expr.jump Jpol.fst (Arg.var pw.fst, Arg.var pw.snd.fst,
                      Arg.var pw.snd.snd.fst, Arg.var pol1.fst, ())) Blocks.nil) fun Jwe =>
                s13BinWatchExpr pH pWstk pVals pFl pTmk pTmp pWs pK
                  (Arg.var p.snd.snd.snd.fst) (Arg.var lit.fst) aCv aCurTmk aMvC aLimV aMaxOrig
                  aLayerStart (Arg.var p.fst) (Arg.var p.snd.fst) (Arg.var p.snd.snd.fst)
                  (Arg.var woffz.fst) (Arg.var wend.fst)
                  (fun nv' nc' lim' p' =>
                    Expr.jump Jwe.fst (Arg.var nv', Arg.var nc', lim', Arg.var p', ())))
              (Expr.jump Jexit.fst ())))
        (Expr.jump Jexit.fst ())) Blocks.nil)
    fun Jpol => Expr.jump Jpol.fst (aNv0, aNc0, aLim0, Arg.imm 0, ())

/-! ## 2. Helper Lemmas for Binary Watch Loop -/

private theorem s13_bin_curVars_load {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {ot : BitVec 32} (hag : AgreesExcept step13ConeMask s st)
    (hlen : st.LengthsOk c) (_hw : FullWitnessInv c F0 F_cur s.core)
    (hot_lt : ot.toNat < 2 * s.core.cur_vars) :
    have ov := ot >>> (1 : Nat)
    (BitVec.setWidth 64 ov).toNat < st.core.cur_vars ∧
      ¬ (BitVec.ofNat 64 st.core.cur_vars ≤ BitVec.setWidth 64 ov) ∧
      (BitVec.setWidth 64 ov).toNat < st.core.flags.length ∧
      (BitVec.setWidth 64 ot).toNat < st.core.vals.length ∧
      (BitVec.setWidth 64 ov).toNat < st.scratch.tarjan_mark.length ∧
      ov.toNat < s.core.cur_vars ∧ ot.toNat < s.core.vals.length := by
  have hcv := s13_cur_vars_eq hag
  have hov : (ot >>> (1 : Nat)).toNat = ot.toNat / 2 := m6_bv32_shr1_toNat ot
  have hov_lt : (ot >>> (1 : Nat)).toNat < s.core.cur_vars := by rw [hov]; omega
  have hlt_cv : (BitVec.setWidth 64 (ot >>> (1 : Nat))).toNat < st.core.cur_vars := by
    rw [bv_c0_zext32_64, hcv]; exact hov_lt
  have hcv64 : st.core.cur_vars < 2 ^ 64 := by
    have := hlen.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
  have hnot_ge : ¬ (BitVec.ofNat 64 st.core.cur_vars ≤ BitVec.setWidth 64 (ot >>> (1 : Nat))) := by
    intro hle; rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv64] at hle; omega
  have hfl : (BitVec.setWidth 64 (ot >>> (1 : Nat))).toNat < st.core.flags.length := by
    rw [bv_c0_zext32_64, hlen.core_ok.flags_len]; have := hlen.core_ok.cur_vars_le; omega
  have hvl : (BitVec.setWidth 64 ot).toNat < st.core.vals.length := by
    rw [bv_c0_zext32_64, hlen.core_ok.vals_len]; have := hlen.core_ok.cur_vars_le; omega
  have htmk : (BitVec.setWidth 64 (ot >>> (1 : Nat))).toNat < st.scratch.tarjan_mark.length := by
    rw [bv_c0_zext32_64, hlen.scratch_ok.tarjan_mark_len]; have := hlen.core_ok.cur_vars_le; omega
  have hot_vl : ot.toNat < s.core.vals.length := by
    rw [← s13_vals_eq hag, ← bv_c0_zext32_64 ot]; exact hvl
  exact ⟨hlt_cv, hnot_ge, hfl, hvl, htmk, hov_lt, hot_vl⟩

private theorem s13_bin_push_tmp2_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s st0 st_b : FullState} {ws0 scr0 : List (BitVec 32)}
    {mvC cv qi_l savedNv nv_b curTmk pol ov ot : BitVec 32} {nc : Nat}
    (hsb : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_b.toNat nc st_b)
    (hsav_ge1 : 1 ≤ savedNv.toNat) (hqi_sav : qi_l.toNat < savedNv.toNat)
    (hcurTmk : curTmk = st0.scratch.tarjan_mark[cv.toNat]?.getD 0#32 - 1#32)
    (hcv_tmk0 : st0.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1))
    (hpol : pol = 0#32 ∨ pol = 1#32) (hov_cv : ov ≠ cv) (hov : ov = ot >>> (1 : Nat))
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hov_idx : st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 ∧
      (st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32 - 1#32).toNat < nv_b.toNat ∧
      (st_b.scratch.work_stk1[(st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32 - 1#32).toNat]?
        |>.getD 0#32).toNat = ov.toNat)
    (hpushed_idx : savedNv.toNat < nv_b.toNat →
      (st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32 - 1#32).toNat + 1 = nv_b.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [2 * cv.toNat + pol.toNat, ot.toNat]))
    (hm_len : 2 ≤ st_b.core.tmp.length) :
    let l0 := (curTmk <<< (1 : Nat)) ||| pol
    let ld2 := st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32
    let l1 := ((ld2 - 1#32) <<< (1 : Nat)) ||| (ot &&& 1#32)
    let tmp' := (st_b.core.tmp.set 0 l0).set 1 l1
    let st_t : FullState := { st_b with core := { st_b.core with tmp := tmp' } }
    (st_b.core.tmp.set 0 l0).length = st_b.core.tmp.length ∧
    tmp'.length = st_b.core.tmp.length ∧
    st_t.LengthsOk c ∧
    Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_b.toNat nc st_t ∧
    (savedNv.toNat < nv_b.toNat → ∃ i < 2, (tmp'[i]?.getD 0#32).toNat / 2 + 1 = nv_b.toNat) ∧
    (∀ j < 2, (tmp'[j]?.getD 0#32).toNat < 2 * nv_b.toNat) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map (fun x => m6ConeLift st_t.scratch.work_stk1 x.toNat)
        (List.take 2 tmp'))) := by
  have _ := hsav_ge1; have _ := hov_cv; have _ := hov_lt
  have hcurTmk_eq : curTmk = qi_l := by
    rw [hcurTmk, hcv_tmk0]; exact m6_bv32_add1_sub1_eq qi_l
  have hqi_nv_b : qi_l.toNat < nv_b.toNat := Nat.lt_of_lt_of_le hqi_sav hsb.hsav_le
  have hcv32 : 2 * nv_b.toNat < 2 ^ 32 := by
    have := hsb.hcone.nv_le_cv; have := hsb.hlen.core_ok.cur_vars_le
    have := c.hmaxv; unfold dimacsBound at this; omega
  have hpol_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  let l0 := (curTmk <<< (1 : Nat)) ||| pol
  let ld2 := st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32
  let l1 := ((ld2 - 1#32) <<< (1 : Nat)) ||| (ot &&& 1#32)
  have hl0_eq : l0.toNat = 2 * qi_l.toNat + pol.toNat := by
    dsimp only [l0]; rw [hcurTmk_eq]; exact m6_bv32_shl1_or_pol qi_l pol (by omega) hpol_lt
  have hld2_lt : (ld2 - 1#32).toNat < nv_b.toNat := hov_idx.2.1
  have hl1_eq : l1.toNat = 2 * (ld2 - 1#32).toNat + (ot &&& 1#32).toNat := by
    dsimp only [l1]
    have hand : (ot &&& 1#32).toNat = ot.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    rw [hand]; exact m6_bv32_shl1_or_and1 (ld2 - 1#32) ot (by omega)
  let tmp0 := st_b.core.tmp.set 0 l0
  let tmp' := tmp0.set 1 l1
  let st_t : FullState := { st_b with core := { st_b.core with tmp := tmp' } }
  have hlen0 : tmp0.length = st_b.core.tmp.length := List.length_set
  have hlen1 : tmp'.length = st_b.core.tmp.length := by simp [tmp', tmp0]
  have hlen_t : st_t.LengthsOk c :=
    ⟨{ hsb.hlen.core_ok with tmp_len_arr := hlen1.trans hsb.hlen.core_ok.tmp_len_arr },
     hsb.hlen.scratch_ok⟩
  have hgu_t : S13GuOk L s savedNv.toNat st_t :=
    ⟨hsb.hgu_sav.1, hsb.hgu_sav.2, hsb.hgu_sav.3⟩
  have hsb_t : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_b.toNat nc st_t :=
    ⟨hlen_t, s13_upd_tmp tmp' hsb.hag, hgu_t,
     by cases hsb.hcone
        exact FidConeInv.mk ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›,
     hsb.htmk, hsb.hwk, hsb.hsav_le, hsb.hscr, hsb.hws⟩
  have ht0 : tmp'[0]?.getD 0#32 = l0 := by
    have : 0 < tmp'.length := by omega
    rw [List.getElem?_eq_getElem this, Option.getD_some]
    simp [tmp', tmp0, List.getElem_set_ne]
  have ht1 : tmp'[1]?.getD 0#32 = l1 := by
    have : 1 < tmp'.length := by omega
    rw [List.getElem?_eq_getElem this, Option.getD_some]
    simp [tmp']
  have hnew : savedNv.toNat < nv_b.toNat →
      ∃ i < 2, (tmp'[i]?.getD 0#32).toNat / 2 + 1 = nv_b.toNat := by
    intro hlt
    refine ⟨1, by omega, ?_⟩
    rw [ht1, hl1_eq]
    have hbit : (ot &&& 1#32).toNat < 2 := m6_bv32_and1_toNat ot ▸ Nat.mod_lt _ (by omega)
    have hdiv : (2 * (ld2 - 1#32).toNat + (ot &&& 1#32).toNat) / 2 = (ld2 - 1#32).toNat := by omega
    rw [hdiv]; exact hpushed_idx hlt
  have hlts : ∀ k < 2, (tmp'[k]?.getD 0#32).toNat < 2 * nv_b.toNat := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; rw [ht0, hl0_eq]; omega
    · have hk1 : k = 1 := by omega
      subst hk1; rw [ht1, hl1_eq]
      have hbit : (ot &&& 1#32).toNat < 2 := m6_bv32_and1_toNat ot ▸ Nat.mod_lt _ (by omega)
      omega
  have htake : List.take 2 tmp' = [l0, l1] := by
    match h_tmp : st_b.core.tmp with
    | a :: b :: rest => simp [tmp', tmp0, h_tmp]
    | [] | [_] => simp [h_tmp] at hm_len
  have hlift0 : m6ConeLift st_t.scratch.work_stk1 l0.toNat = 2 * cv.toNat + pol.toNat := by
    change m6ConeLift st_b.scratch.work_stk1 l0.toNat = _
    unfold m6ConeLift
    rw [hl0_eq]
    rcases hpol with rfl | rfl
    · have h0 : (0#32 : BitVec 32).toNat = 0 := rfl
      rw [h0, Nat.add_zero, show (2 * qi_l.toNat) / 2 = qi_l.toNat by omega,
        show (2 * qi_l.toNat) % 2 = 0 by omega, hsb.hwk]
      omega
    · have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
      rw [h1, show (2 * qi_l.toNat + 1) / 2 = qi_l.toNat by omega,
        show (2 * qi_l.toNat + 1) % 2 = 1 by omega, hsb.hwk]
      omega
  have hlift1 : m6ConeLift st_t.scratch.work_stk1 l1.toNat = ot.toNat := by
    change m6ConeLift st_b.scratch.work_stk1 l1.toNat = _
    unfold m6ConeLift
    rw [hl1_eq]
    have hbit := m6_bv32_and1_toNat ot
    have hbit_lt : (ot &&& 1#32).toNat < 2 := by rw [hbit]; exact Nat.mod_lt _ (by omega)
    have hdiv : (2 * (ld2 - 1#32).toNat + (ot &&& 1#32).toNat) / 2 = (ld2 - 1#32).toNat := by omega
    have hmod : (2 * (ld2 - 1#32).toNat + (ot &&& 1#32).toNat) % 2 = ot.toNat % 2 := by omega
    rw [hdiv, hmod, hov_idx.2.2, hov, m6_bv32_shr1_toNat ot]
    omega
  have hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map (fun x => m6ConeLift st_t.scratch.work_stk1 x.toNat)
        (List.take 2 tmp'))) := by
    rw [htake]; simp only [List.map_cons, List.map_nil, hlift0, hlift1]
    exact hent
  exact ⟨hlen0, hlen1, hlen_t, hsb_t, hnew, hlts, hent'⟩

/-! ## 3. WP Proofs for `s13BinWatchExpr` and `s13BinPassExpr` -/

theorem step13_cone_bin_watch_wp {Γ : Env}
    (hAddCl : Γ.Has "full_k6_add_clause" Proof.Kitten.Spec.step13K6AddClauseHwSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L : K6Layout}
    {pH pWstk pVals pFl pTmk pTmp pWs pK pWEnd : Val i64}
    {mvC maxOrig pol cv curTmk nv0 nc0 layerEnd lit : BitVec 32}
    {aPol aLit aCv aCurTmk aMvC aLimV aMaxOrig aLayerStart aNv0 aNc0 : Arg Val i32}
    {lim0 : Bool} {aLim0 : Arg Val Ty.bool} {wOff : BitVec 64} {aWOff : Arg Val i64}
    {qi_l : BitVec 32} {s st0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [i64]} {X : XPost}
    {k_done : Val i32 → Val i32 → Arg Val Ty.bool → Val i64 → Expr Val Cont [i64]}
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hpH : pH = c.hdr) (hpWstk : pWstk = c.pWstk) (hpVals : pVals = c.pVals)
    (hpFl : pFl = c.pFlags) (hpTmk : pTmk = c.pTarjanMark) (hpTmp : pTmp = c.pTmp)
    (hpWs : pWs = c.pWorkStk1) (hpK : pK = L.kPtr c.pScratchBuf)
    (hap : aPol.val = pol) (hlit : aLit.val = lit) (hacv : aCv.val = cv)
    (hact : aCurTmk.val = curTmk) (hamvc : aMvC.val = mvC) (halimv : aLimV.val.toNat ≤ mvC.toNat)
    (hamax : aMaxOrig.val = maxOrig)
    (hanv0 : aNv0.val = nv0) (hanc0 : aNc0.val = nc0)
    (halim0 : aLim0.val = lim0) (hawoff : aWOff.val = wOff)
    (hm_lt : maxOrig.toNat ≤ L.maxOrig)
    (hlen_s : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hlvl0 : s.core.cur_level = 0) (hdw : DenseWatchesInv F_cur s.core)
    (hlit_cv : lit.toNat < 2 * s.core.cur_vars)
    (hlit_def : lit = (cv <<< (1 : Nat)) ||| pol) (hpol : pol = 0#32 ∨ pol = 1#32)
    (hwoff : wOff.toNat = fullWatchOffCore s.core lit.toNat)
    (hwend : pWEnd.toNat = fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat)
    (hwend_le : pWEnd.toNat ≤ s.core.wstk.length)
    (hqi_le : qi_l.toNat < layerEnd.toNat) (hle_nv0 : layerEnd.toNat ≤ nv0.toNat)
    (hcurTmk : curTmk = st0.scratch.tarjan_mark[cv.toNat]?.getD 0#32 - 1#32)
    (hb0 : Step13ConeBase F_cur L mvC c s cv qi_l nv0.toNat nc0.toNat st0)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hCont : ∀ (nvE ncE : BitVec 32) (limE : Bool) (aLimE : Arg Val Ty.bool) (pE : BitVec 64)
        (stE : FullState) (mE : Mem 64),
      aLimE.val = limE →
      layerEnd.toNat ≤ nvE.toNat → nc0.toNat ≤ ncE.toNat → ncE.toNat ≤ L.maxOrig →
      Step13ConeBase F_cur L mvC c s cv qi_l nvE.toNat ncE.toNat stE →
      (FullMem c stE ⋆ R) mE → wp Γ Q X (k_done nvE ncE aLimE pE) mE) :
    wp Γ Q X (s13BinWatchExpr pH pWstk pVals pFl pTmk pTmp pWs pK aPol aLit aCv aCurTmk aMvC
      aLimV aMaxOrig aLayerStart aNv0 aNc0 aLim0 aWOff (Arg.var pWEnd) k_done) m0 := by
  subst hpH hpWstk hpVals hpFl hpTmk hpTmp hpWs hpK
  rw [s13BinWatchExpr]
  dsimp only [binCmpOp, binMkOp]
  refine wp_while_state (ts := [i32, i32, Ty.bool, i64])
    (proj := fun st : BitVec 32 × BitVec 32 × Bool × BitVec 64 =>
      (st.1, st.2.1, st.2.2.1, st.2.2.2, ()))
    (μ := fun st => pWEnd.toNat - st.2.2.2.toNat)
    (Inv := fun st mw => ∃ stW : FullState,
      layerEnd.toNat ≤ st.1.toNat ∧ nc0.toNat ≤ st.2.1.toNat ∧ st.2.1.toNat ≤ L.maxOrig ∧
      wOff.toNat ≤ st.2.2.2.toNat ∧ st.2.2.2.toNat ≤ pWEnd.toNat ∧
      DenseWatchSliceOk F_cur s.core lit.toNat st.2.2.2.toNat (pWEnd.toNat - st.2.2.2.toNat) ∧
      Step13ConeBase F_cur L mvC c s cv qi_l st.1.toNat st.2.1.toNat stW ∧
      (FullMem c stW ⋆ R) mw)
    ?_ ?_
  · intro Jw hJw; c0_hsteps_nogrp
    rw [hanv0, hanc0, halim0, hawoff]
    have hslice0 : DenseWatchSliceOk F_cur s.core lit.toNat wOff.toNat
        (pWEnd.toNat - wOff.toNat) := by
      have hlen_w := hdw.slices lit.toNat hlit_cv
      rwa [hwoff, show pWEnd.toNat - fullWatchOffCore s.core lit.toNat =
        fullWatchSizeCore s.core lit.toNat by omega]
    exact hJw (nv0, nc0, lim0, wOff) m0 ⟨st0, hle_nv0, le_refl _, hb0.hcone.nc_le, le_refl _,
      by dsimp only; have := hwoff; have := hwend; omega, hslice0, hb0, hm0⟩
  · rintro Jw ⟨nv_w, nc_w, lim_w, p_w⟩ mw
      ⟨st_w, hle_nv, hnc_ge, hnc_le, hp_ge, hp_le, hslice_w, hb_w, hmw⟩ ih_w
    dsimp only at *
    have hlen_w := hb_w.hlen; have hag_w := hb_w.hag; have hcone_w := hb_w.hcone
    have hcurTmk_w : curTmk = st_w.scratch.tarjan_mark[cv.toNat]?.getD 0#32 - 1#32 := by
      rw [hcurTmk, hb0.htmk, hb_w.htmk]
    c0_hsteps_nogrp
    c0_hsplit
    · -- `p_w < pWEnd`, `lim_w = true`
      have hp_lt : p_w.toNat < pWEnd.toNat := by bv_omega
      have hlim_t : lim_w = true := ‹_›
      subst hlim_t
      dsimp only
      exact hCont nv_w nc_w true (Arg.var true) p_w st_w mw rfl hle_nv hnc_ge hnc_le hb_w hmw
    · -- `p_w < pWEnd`, `lim_w = false`, `nc_w < maxOrig`
      have hlim_f : lim_w = false := ‹_›
      subst hlim_f
      have hp_lt : p_w.toNat < pWEnd.toNat := by bv_omega
      have hnc_lt_L : nc_w.toNat < L.maxOrig := by
        have : nc_w.toNat < maxOrig.toNat := by bv_omega
        omega
      have hp_wstk : p_w.toNat < st_w.core.wstk.length :=
        fid_cone_hp_wstk (s13_wstk_eq hag_w) hp_lt hwend_le
      have hp_lt63 : p_w.toNat < 2 ^ 63 := by
        have := hlen_s.core_ok.wstk_len_arr; have := c.hwcap; unfold dimacsBound at this; omega
      have hp1_eq : (p_w + 1#64).toNat = p_w.toNat + 1 := fid_cone_wstk_p_toNat_eq p_w hp_lt63
      c0_hsteps_nogrp
      let w0 := st_w.core.wstk[p_w.toNat]'hp_wstk
      have hw0_s : s.core.wstk[p_w.toNat]? = some w0 := by
        rw [← s13_wstk_eq hag_w, List.getElem?_eq_getElem hp_wstk]
      c0_hsplit
      · -- Occ watch (`(w0 &&& 0x80000000) == 0`): advance `p_w + 2`
        obtain ⟨_, _, _, _, _, _, hocc_slice⟩ :=
          m6_denseSlice_step_occ hslice_w (by omega) hw0_s (by assumption)
        have hp2_lt : (p_w + 1#64 + 1#64).toNat = p_w.toNat + 2 := by
          have : p_w.toNat + 2 ≤ pWEnd.toNat := by omega
          have := hlen_s.core_ok.wstk_len_arr; have := c.hwcap; unfold dimacsBound at this; bv_omega
        have hslice2 : DenseWatchSliceOk F_cur s.core lit.toNat (p_w + 1#64 + 1#64).toNat
            (pWEnd.toNat - (p_w + 1#64 + 1#64).toNat) := by
          rw [hp2_lt]
          simpa [show pWEnd.toNat - p_w.toNat - 2 = pWEnd.toNat - (p_w.toNat + 2) by omega]
            using hocc_slice
        c0_hsteps!
        exact ih_w (nv_w, nc_w, false, p_w + 1#64 + 1#64) mw (by rw [hp2_lt]; omega)
          ⟨st_w, hle_nv, hnc_ge, hnc_le, by rw [hp2_lt]; omega, by rw [hp2_lt]; omega,
           hslice2, hb_w, hmw⟩
      · -- Bin watch, `ov ≥ cur_vars` (impossible since `ot < 2 * cur_vars`)
        have hw0_s : s.core.wstk[p_w.toNat]? = some (st_w.core.wstk[p_w.toNat]'hp_wstk) := by
          rw [← s13_wstk_eq hag_w, List.getElem?_eq_getElem hp_wstk]
        obtain ⟨_, hot_lt, _, _⟩ := m6_denseSlice_step_bin hslice_w (by omega) hw0_s (by assumption)
        have hcv_eq := s13_cur_vars_eq hag_w
        have hcv_le := hlen_s.core_ok.cur_vars_le; have hmv := c.hmaxv; unfold dimacsBound at hmv
        have hge : st_w.core.cur_vars % 2 ^ 64 ≤
            (st_w.core.wstk[p_w.toNat] &&& 2147483647#32).toNat / 2 := ‹_›
        omega
      · -- Bin watch (`(w0 &&& 0x80000000) != 0`), `ov < cur_vars`
        let w0 := st_w.core.wstk[p_w.toNat]'hp_wstk
        have hw0_s : s.core.wstk[p_w.toNat]? = some w0 := by
          rw [← s13_wstk_eq hag_w, List.getElem?_eq_getElem hp_wstk]
        obtain ⟨_, hot_lt, hbin_ent, hbin_slice⟩ :=
          m6_denseSlice_step_bin hslice_w (by omega) hw0_s (by assumption)
        let ot := w0 &&& 2147483647#32
        let ov := ot >>> (1 : Nat)
        have hslice1 : DenseWatchSliceOk F_cur s.core lit.toNat (p_w + 1#64).toNat
            (pWEnd.toNat - (p_w + 1#64).toNat) := by
          rw [hp1_eq]
          simpa [show pWEnd.toNat - p_w.toNat - 1 = pWEnd.toNat - (p_w.toNat + 1) by omega]
            using hbin_slice
        have hcv_lt : cv.toNat < s.core.cur_vars := (hcone_w.fwd qi_l.toNat
          (Nat.lt_of_lt_of_le hqi_le hle_nv)).1 |> fun h =>
            by rw [hb_w.hwk, s13_cur_vars_eq hag_w] at h; exact h
        have hlit_to : lit.toNat = 2 * cv.toNat + pol.toNat := by
          have hcv_29 : 2 * cv.toNat < 2 ^ 32 := by
            have := hlen_s.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
          rw [hlit_def]
          exact m6_bv32_shl1_or_pol cv pol (by omega) (by rcases hpol with rfl | rfl <;> decide)
        have hent_bin : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [2 * cv.toNat + pol.toNat, ot.toNat]) := by
          rw [hlit_to] at hbin_ent
          exact hbin_ent
        obtain ⟨hov_lt_st, _, hfl_lt, hvl_lt, htmk_lt, hov_lt_s, hot_vl⟩ :=
          s13_bin_curVars_load hag_w hlen_w hw hot_lt
        have hcontinue_p1 : ∀ {st1 : FullState} {nv1 nc1 : BitVec 32} {lim1 : Bool}
            {m1 : Mem 64},
            layerEnd.toNat ≤ nv1.toNat → nc0.toNat ≤ nc1.toNat → nc1.toNat ≤ L.maxOrig →
            Step13ConeBase F_cur L mvC c s cv qi_l nv1.toNat nc1.toNat st1 →
            (FullMem c st1 ⋆ R) m1 →
            Jw (nv1, nc1, lim1, p_w + 1#64, ()) m1 := by
          intro st1 nv1 nc1 lim1 m1 hnv1 hnc1g hnc1l hb1 hm1
          exact ih_w (nv1, nc1, lim1, p_w + 1#64) m1 (by rw [hp1_eq]; omega)
            ⟨st1, hnv1, hnc1g, hnc1l, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega,
             hslice1, hb1, hm1⟩
        c0_hsteps_nogrp
        c0_hsplit
        · -- `(flags[ov] &&& 1) == 0`: skip
          exact hcontinue_p1 hle_nv hnc_ge hnc_le hb_w hmw
        · -- `ovv >s 0`: skip
          exact hcontinue_p1 hle_nv hnc_ge hnc_le hb_w hmw
        · -- `ovv ≤s 0`, `ov == cv`
          have hov_eq_cv : ov = cv := by rw [← hacv]; exact ‹_›
          have hmap_cv : (st_w.scratch.work_stk1[curTmk.toNat]?.getD 0#32).toNat = cv.toNat := by
            have hct : curTmk = qi_l := by
              rw [hcurTmk_w, hb_w.htmk]; exact m6_bv32_add1_sub1_eq qi_l
            rw [hct]; exact hb_w.hwk
          have hmap_lt : curTmk.toNat < nv_w.toNat := by
            have hct : curTmk = qi_l := by
              rw [hcurTmk_w, hb_w.htmk]; exact m6_bv32_add1_sub1_eq qi_l
            rw [hct]; exact Nat.lt_of_lt_of_le hqi_le hle_nv
          refine wp_join_group (ts := [i32, Ty.bool])
            (fun (nc', lim', ()) mJ => ∃ stJ : FullState,
              nc0.toNat ≤ nc'.toNat ∧ nc'.toNat ≤ L.maxOrig ∧
              Step13ConeBase F_cur L mvC c s cv qi_l nv_w.toNat nc'.toNat stJ ∧
              (FullMem c stJ ⋆ R) mJ) ?_ ?_
          · rintro _ ⟨nc', lim', ⟨⟩⟩ mJ ⟨stJ, hncJg, hncJl, hbJ, hmJ⟩
            c0_hsteps!; exact hcontinue_p1 hle_nv hncJg hncJl hbJ hmJ
          · intro Jb hJb
            c0_hsteps_nogrp
            c0_hsplit
            · -- `ot == lit`: unit `[lit]`
              have hent_u : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [2 * cv.toNat + pol.toNat]) := by
                have heql : ot = lit := by rw [← hlit]; exact ‹_›
                rw [heql, hlit_to] at hent_bin
                exact m6_entails_singleton_of_dup hent_bin
              refine step13_cone_bin_unit_call_wp hAddCl hLscr hLmv rfl hact hap rfl rfl
                hb_w rfl hnc_lt_L hpol hmap_lt hmap_cv hent_u hmw ?_
              intro nc' lim' st' m' hnc'l hnc'g _ hb' hm'
              c0_hsteps!; exact hJb (nc', lim', ()) m' ⟨st', le_trans hnc_ge hnc'g, hnc'l, hb', hm'⟩
            · -- `ot != lit`: skip
              exact hJb (nc_w, false, ()) mw ⟨st_w, hnc_ge, hnc_le, hb_w, hmw⟩
        · -- `ovv <s 0`, `ov ≠ cv` -> `ovv = 255#8` -> bin resolves with false -> unit `[lit]`!
          have hs_vals_eq : st_w.core.vals[ot.toNat]?.getD 0#8 =
              s.core.vals[ot.toNat]?.getD 0#8 := by rw [s13_vals_eq hag_w]
          have hslt_st : (st_w.core.vals[ot.toNat]?.getD 0#8).slt 0#8 = true := by
            have hot_len : ot.toNat < st_w.core.vals.length := by
              rwa [bv_c0_zext32_64] at hvl_lt
            rw [List.getElem?_eq_getElem hot_len, Option.getD_some]
            have hc' : (BitVec.signExtend 32 (st_w.core.vals[ot.toNat]'hot_len)).slt
                (BitVec.ofNat 32 0) = true := ‹_›
            simp only [BitVec.slt, BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 32)] at hc' ⊢
            exact hc'
          have hs_slt : (s.core.vals[ot.toNat]?.getD 0#8).slt 0#8 = true := by
            rwa [← hs_vals_eq]
          have h255 : s.core.vals[ot.toNat]?.getD 0#8 = 255#8 :=
            s13_vals_slt_zero_eq_255 hw hot_lt hs_slt
          have hent_u : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [2 * cv.toNat + pol.toNat]) :=
            m6_entails_fst_of_snd_false hw hlvl0 hot_lt h255 hent_bin
          have hmap_cv : (st_w.scratch.work_stk1[curTmk.toNat]?.getD 0#32).toNat = cv.toNat := by
            have hct : curTmk = qi_l := by
              rw [hcurTmk_w, hb_w.htmk]; exact m6_bv32_add1_sub1_eq qi_l
            rw [hct]; exact hb_w.hwk
          have hmap_lt : curTmk.toNat < nv_w.toNat := by
            have hct : curTmk = qi_l := by
              rw [hcurTmk_w, hb_w.htmk]; exact m6_bv32_add1_sub1_eq qi_l
            rw [hct]; exact Nat.lt_of_lt_of_le hqi_le hle_nv
          refine step13_cone_bin_unit_call_wp hAddCl hLscr hLmv rfl hact hap rfl rfl
            hb_w rfl hnc_lt_L hpol hmap_lt hmap_cv hent_u hmw ?_
          intro nc' lim' st' m' hnc'l hnc'g _ hb' hm'
          c0_hsteps!
          exact hcontinue_p1 hle_nv (le_trans hnc_ge hnc'g) hnc'l hb' hm'
        · -- `ovv == 0`, `ov ≠ cv`: `binAdd` (`old = tmk[ov]`)
          have hov_ne_cv : ov ≠ cv := by
            have hne : ¬ (st_w.core.wstk[p_w.toNat] &&& 2147483647#32) >>> (1 : BitVec 32) =
                aCv.val := ‹_›
            rw [hacv] at hne; exact hne
          have hov_lt_s' : ov.toNat < s.core.cur_vars := hov_lt_s
          have hovv_nsgt : (0#8).slt (st_w.core.vals[ot.toNat]?.getD 0#8) = false := by
            have hot_len : ot.toNat < st_w.core.vals.length := by
              rwa [bv_c0_zext32_64] at hvl_lt
            rw [List.getElem?_eq_getElem hot_len, Option.getD_some]
            have hc' : (BitVec.ofNat 32 0).slt
                (BitVec.signExtend 32 (st_w.core.vals[ot.toNat]'hot_len)) = false := ‹_›
            simp only [BitVec.slt, BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 32)] at hc' ⊢
            exact hc'
          have htmk_ov := s13_tmk_ov_at st_w ov (by
            rw [hlen_w.scratch_ok.tarjan_mark_len]; have := hlen_s.core_ok.cur_vars_le; omega)
          have htmk_idx := htmk_ov.2
          refine wp_join_group (ts := []) (fun () ma => ma = mw) ?_ ?_
          · rintro _ ⟨⟩ ma hma; subst ma
            dsimp only
            let ws0 := st_w.scratch.work_stk1
            let scr0 := st_w.scratch.scratch_buf
            have hsb0 : Step13ConeSavedBase F_cur L mvC c s cv qi_l nv_w ws0 scr0
                nv_w.toNat nc_w.toNat st_w :=
              ⟨hlen_w, hag_w, hb_w.hgu, hcone_w, hb_w.htmk, hb_w.hwk, le_refl _, rfl,
               fun _ _ => rfl⟩
            refine wp_join_group (ts := [i32, Ty.bool])
              (fun (nv_b, lim_b, ()) mB => ∃ st_b : FullState,
                lim_b = false ∧
                layerEnd.toNat ≤ nv_b.toNat ∧ nv_w.toNat ≤ nv_b.toNat ∧
                nv_b.toNat ≤ mvC.toNat ∧
                st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 ∧
                (st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32 - 1#32).toNat < nv_b.toNat ∧
                (st_b.scratch.work_stk1[(st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32 -
                  1#32).toNat]?.getD 0#32).toNat = ov.toNat ∧
                (nv_w.toNat < nv_b.toNat →
                  (st_b.scratch.tarjan_mark[ov.toNat]?.getD 0#32 - 1#32).toNat + 1 =
                    nv_b.toNat) ∧
                Step13ConeSavedBase F_cur L mvC c s cv qi_l nv_w ws0 scr0 nv_b.toNat nc_w.toNat
                  st_b ∧
                (FullMem c st_b ⋆ R) mB) ?_ ?_
            · rintro _ ⟨nv_b, lim_b, ⟨⟩⟩ mB
                ⟨st_b, hlim_b, hle_b, hnv_wb, hnv_bmv, hov_nz, hov_lt_nb, hov_wk, hpush_idx,
                 hsb_b, hmB⟩
              subst hlim_b
              have hhm_tmp : 2 ≤ st_b.core.tmp.length := by
                have hne_n : ov.toNat ≠ cv.toNat := fun h => hov_ne_cv (BitVec.eq_of_toNat_eq h)
                have := hsb_b.hlen.core_ok.tmp_len_arr
                have := hlen_s.core_ok.cur_vars_le
                omega
              have hcur_eq : curTmk =
                  st_b.scratch.tarjan_mark[cv.toNat]?.getD 0#32 - 1#32 := by
                rw [hcurTmk_w, hb_w.htmk, hsb_b.htmk]
              have ht0_b := s13_tmk_ov_at st_b ov (by
                rw [hsb_b.hlen.scratch_ok.tarjan_mark_len]
                have := hlen_s.core_ok.cur_vars_le; omega)
              have ht0_b_lt : (BitVec.setWidth 64 ov).toNat < st_b.scratch.tarjan_mark.length := by
                rw [ht0_b.1, hsb_b.hlen.scratch_ok.tarjan_mark_len]
                have := hlen_s.core_ok.cur_vars_le; omega
              obtain ⟨_, hprep_len, _, hprep_sb, hprep_new, hprep_lt, hprep_ent⟩ :=
                s13_bin_push_tmp2_ok hsb_b (by omega)
                  (Nat.lt_of_lt_of_le hqi_le hle_nv) hcurTmk_w hb_w.htmk hpol hov_ne_cv rfl
                  hov_lt_s ⟨hov_nz, hov_lt_nb, hov_wk⟩ hpush_idx hent_bin hhm_tmp
              have htmp0_lt : 0 < st_b.core.tmp.length := by omega
              have htmp1_lt : 1 < (st_b.core.tmp.set 0
                  (aCurTmk.val <<< (1 : BitVec 32) ||| aPol.val)).length := by
                rw [List.length_set]; omega
              have hi1_to : (BitVec.signExtend 64 1#32).toNat = 1 := rfl
              c0_hsteps_nogrp
              have hqi_w : qi_l.toNat < nv_w.toNat := Nat.lt_of_lt_of_le hqi_le hle_nv
              refine step13_cone_add_clause_block_wp (R := R) hAddCl hLscr hLmv rfl rfl rfl rfl
                rfl halimv rfl hprep_sb hqi_w
                (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hqi_w))
                hcone_w.k6_bdd hcone_w.k6_trl_bdd
                hprep_new hnc_lt_L (by decide) (by rw [hprep_len]; exact hhm_tmp)
                hprep_lt hprep_ent rfl ?_ ?_
              · rw [← hact, ← hap, ← ht0_b.2]; assumption
              · intro nv'' nc'' lim'' st'' m'' hnc''l hnc''g hnw_le _ _ hb'' hm''
                c0_hsteps!
                exact hcontinue_p1 (le_trans hle_nv hnw_le)
                  (le_trans hnc_ge hnc''g) hnc''l hb'' hm''
            · intro Jb hJb
              c0_hsteps_nogrp
              c0_hsplit
              · -- `tmk[ov] == 0`, `nv_w ≥ mvC`: overflow -> `lim = true`, break to `Jwe`
                exact hCont nv_w nc_w true (Arg.imm true) (p_w + 1#64) st_w mw rfl
                  hle_nv hnc_ge hnc_le hb_w hmw
              · -- `tmk[ov] == 0`, `nv_w < mvC`: push `ov` onto `ws1`, `tmk[ov] = nv_w + 1`
                have htmk_0 : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32 := by
                  have h0 : st_w.scratch.tarjan_mark[(st_w.core.wstk[p_w.toNat] &&&
                      2147483647#32).toNat / 2 ^ (1 : Nat)] = 0#32 := ‹_›
                  have hidx : (BitVec.setWidth 64 ov).toNat =
                      (st_w.core.wstk[p_w.toNat] &&& 2147483647#32).toNat / 2 ^ (1 : Nat) := by
                    rw [htmk_ov.1]
                    simp [ov, ot, w0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                  rw [← htmk_idx]; simpa [hidx] using h0
                have hnv_lt : nv_w.toNat < mvC.toNat := by
                  have hng : ¬ aMvC.val.toNat ≤ nv_w.toNat := ‹_›
                  rw [hamvc] at hng; omega
                obtain ⟨_, hnv1_to, _, _, hsb_p, hpush_wk⟩ :=
                  step13_cone_push_var_step_ok hsb0 hnv_lt hov_lt_s htmk_0
                    (Nat.lt_of_lt_of_le hqi_le hle_nv)
                have hnv_ws : (BitVec.setWidth 64 nv_w).toNat <
                    st_w.scratch.work_stk1.length := by
                  rw [bv_c0_zext32_64, hlen_w.scratch_ok.work_stk1_len]
                  have hle1 := hsb_p.hcone.nv_le_cv
                  have hcv_p := s13_cur_vars_eq hsb_p.hag
                  have := hlen_s.core_ok.cur_vars_le; omega
                c0_hsteps_nogrp
                let ws1' := st_w.scratch.work_stk1.set nv_w.toNat ov
                let nv1 := nv_w + 1#32
                let tmk' := st_w.scratch.tarjan_mark.set ov.toNat nv1
                let st_p : FullState :=
                  { st_w with
                    scratch := { st_w.scratch with work_stk1 := ws1', tarjan_mark := tmk' } }
                have htmk'_ov : st_p.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = nv1 := by
                  have : ov.toNat < tmk'.length := by
                    simp [tmk', hlen_w.scratch_ok.tarjan_mark_len]
                    have := hlen_s.core_ok.cur_vars_le; omega
                  rw [List.getElem?_eq_getElem this, Option.getD_some]
                  simp [tmk']
                have hidx_eq : (st_p.scratch.tarjan_mark[ov.toNat]?.getD 0#32 - 1#32).toNat =
                    nv_w.toNat := by
                  rw [htmk'_ov, show nv1 = nv_w + 1#32 from rfl,
                    m6_bv32_add1_sub1_eq nv_w]
                refine hJb (nv1, false, ()) _ ⟨st_p, rfl, by rw [hnv1_to]; omega,
                  by rw [hnv1_to]; omega, by rw [hnv1_to]; omega,
                  by rw [htmk'_ov]; intro h0
                     have h1 : nv1.toNat = 0 := by rw [h0]; rfl
                     rw [show nv1 = nv_w + 1#32 from rfl, hnv1_to] at h1; omega,
                  by rw [hidx_eq, hnv1_to]; omega,
                  by rw [hidx_eq]; exact hpush_wk,
                  fun _ => by rw [hidx_eq, hnv1_to],
                  hsb_p, ?_⟩
                simp only [st_p, ws1', tmk', nv1]
                rw [← bv_c0_zext32_64 nv_w, ← htmk_ov.1]
                assumption
              · -- `tmk[ov] ≠ 0`: reuse `ov` already in `ws1[old - 1]`, `nv` unchanged
                have htmk_nz : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 := by
                  rw [← htmk_idx]; exact ‹_›
                have htmk_rev : ∃ i < nv_w.toNat,
                    (st_w.scratch.work_stk1[i]?.getD 0#32).toNat = ov.toNat ∧
                    st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = BitVec.ofNat 32 (i + 1) := by
                  rcases hcone_w.rev ov.toNat (by rw [s13_cur_vars_eq hag_w]; exact hov_lt_s)
                    with h0 | hex
                  · exact absurd h0 htmk_nz
                  · exact hex
                obtain ⟨i_ov, hi_lt, hi_wk, hi_tmk⟩ := htmk_rev
                have hi_eq : (st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 - 1#32).toNat =
                    i_ov := by
                  have h32 : i_ov + 1 < 2 ^ 32 := by
                    have := hcone_w.nv_le_cv; have := hlen_s.core_ok.cur_vars_le
                    have := c.hmaxv; unfold dimacsBound at this; omega
                  rw [hi_tmk]
                  have : BitVec.ofNat 32 (i_ov + 1) = BitVec.ofNat 32 i_ov + 1#32 := by bv_omega
                  rw [this, m6_bv32_add1_sub1_eq]
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                exact hJb (nv_w, false, ()) mw ⟨st_w, rfl, hle_nv, le_refl _, hcone_w.nv_le_mvC,
                  htmk_nz, by rw [hi_eq]; exact hi_lt, by rw [hi_eq]; exact hi_wk,
                  fun h => absurd h (Nat.lt_irrefl _), hsb0, hmw⟩
          · intro Ja hJa
            c0_hsteps_nogrp
            c0_hsplit
            · -- `old ≠ 0`, `old - 1 < layerStart`: skip to `Jw`
              exact hcontinue_p1 hle_nv hnc_ge hnc_le hb_w hmw
            · -- `old ≠ 0`, `¬(old - 1 < layerStart)`: jump to `Ja`
              exact hJa () mw rfl
            · -- `old == 0`: jump to `Ja`
              exact hJa () mw rfl
    · -- `!(nc_w < maxOrig)`
      dsimp only
      exact hCont nv_w nc_w lim_w (Arg.var lim_w) p_w st_w mw rfl hle_nv hnc_ge hnc_le hb_w hmw
    · -- `!(p_w < pWEnd)`
      dsimp only
      exact hCont nv_w nc_w lim_w (Arg.var lim_w) p_w st_w mw rfl hle_nv hnc_ge hnc_le hb_w hmw

theorem step13_cone_bin_pass_wp {Γ : Env}
    (hAddCl : Γ.Has "full_k6_add_clause" Proof.Kitten.Spec.step13K6AddClauseHwSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L : K6Layout}
    {pH pWvec pWstk pVals pFl pTmk pTmp pWs pK : Val i64}
    {mvC maxOrig cv curTmk nv0 nc0 layerEnd : BitVec 32}
    {aCv aCurTmk aMvC aLimV aMaxOrig aLayerStart aNv0 aNc0 : Arg Val i32} {lim0 : Bool}
    {aLim0 : Arg Val Ty.bool} {qi_l : BitVec 32} {s st0 : FullState} {R : Mem 64 → Prop}
    {m0 : Mem 64} {Q : Post [i64]} {X : XPost}
    {k_done : Val i32 → Val i32 → Val Ty.bool → Expr Val Cont [i64]}
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hpH : pH = c.hdr) (hpWvec : pWvec = c.pWvec) (hpWstk : pWstk = c.pWstk)
    (hpVals : pVals = c.pVals) (hpFl : pFl = c.pFlags) (hpTmk : pTmk = c.pTarjanMark)
    (hpTmp : pTmp = c.pTmp) (hpWs : pWs = c.pWorkStk1) (hpK : pK = L.kPtr c.pScratchBuf)
    (hacv : aCv.val = cv) (hact : aCurTmk.val = curTmk) (hamvc : aMvC.val = mvC)
    (halimv : aLimV.val.toNat ≤ mvC.toNat)
    (hamax : aMaxOrig.val = maxOrig) (hanv0 : aNv0.val = nv0)
    (hanc0 : aNc0.val = nc0) (halim0 : aLim0.val = lim0) (hm_lt : maxOrig.toNat ≤ L.maxOrig)
    (hlen_s : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hlvl0 : s.core.cur_level = 0) (hdw : DenseWatchesInv F_cur s.core)
    (hqi_le : qi_l.toNat < layerEnd.toNat) (hle_nv0 : layerEnd.toNat ≤ nv0.toNat)
    (hcurTmk : curTmk = st0.scratch.tarjan_mark[cv.toNat]?.getD 0#32 - 1#32)
    (hb0 : Step13ConeBase F_cur L mvC c s cv qi_l nv0.toNat nc0.toNat st0)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hCont : ∀ (nvE ncE : BitVec 32) (limE : Bool) (stE : FullState) (mE : Mem 64),
      layerEnd.toNat ≤ nvE.toNat → nc0.toNat ≤ ncE.toNat → ncE.toNat ≤ L.maxOrig →
      Step13ConeBase F_cur L mvC c s cv qi_l nvE.toNat ncE.toNat stE →
      (FullMem c stE ⋆ R) mE → wp Γ Q X (k_done nvE ncE limE) mE) :
    wp Γ Q X (s13BinPassExpr pH pWvec pWstk pVals pFl pTmk pTmp pWs pK aCv aCurTmk aMvC aLimV
      aMaxOrig aLayerStart aNv0 aNc0 aLim0 k_done) m0 := by
  subst hpH hpWvec hpWstk hpVals hpFl hpTmk hpTmp hpWs hpK
  rw [s13BinPassExpr]
  dsimp only [binCmpOp, binMkOp]
  refine wp_while_state (ts := [i32, i32, Ty.bool, i32])
    (proj := fun st : BitVec 32 × BitVec 32 × Bool × BitVec 32 =>
      (st.1, st.2.1, st.2.2.1, st.2.2.2, ()))
    (μ := fun st => 2 - st.2.2.2.toNat)
    (Inv := fun st mp => ∃ stP : FullState,
      layerEnd.toNat ≤ st.1.toNat ∧ nc0.toNat ≤ st.2.1.toNat ∧ st.2.1.toNat ≤ L.maxOrig ∧
      st.2.2.2.toNat ≤ 2 ∧ Step13ConeBase F_cur L mvC c s cv qi_l st.1.toNat st.2.1.toNat stP ∧
      (FullMem c stP ⋆ R) mp)
    ?_ ?_
  · intro Jpol hJpol; c0_hsteps!
    rw [hanv0, hanc0, halim0]
    exact hJpol (nv0, nc0, lim0, 0#32) m0 ⟨st0, hle_nv0, le_refl _, hb0.hcone.nc_le,
      by show (0#32 : BitVec 32).toNat ≤ 2; decide, hb0, hm0⟩
  · rintro Jpol ⟨nv_p, nc_p, lim_p, pol_p⟩ mp ⟨st_p, hle_p, hnc_pg, hnc_pl, hpol_le, hb_p, hmp⟩
      ih_p
    dsimp only at *
    refine wp_join_group (ts := []) (fun () mX => mX = mp) ?_ ?_
    · rintro _ ⟨⟩ mX hmX; subst mX
      c0_hsteps!; exact hCont nv_p nc_p lim_p st_p mp hle_p hnc_pg hnc_pl hb_p hmp
    · intro Jexit hJexit
      dsimp only
      c0_hsteps_nogrp
      c0_hsplit
      · exact hJexit () mp rfl
      · have hpol_lt : pol_p.toNat < 2 := by bv_omega
        have hpol_01 : pol_p = 0#32 ∨ pol_p = 1#32 := by
          by_cases h0 : pol_p = 0#32
          · exact Or.inl h0
          · exact Or.inr (by bv_omega)
        have hcv_lt : cv.toNat < s.core.cur_vars := by
          have hq := Nat.lt_of_lt_of_le hqi_le hle_p
          have hcv_st := (hb_p.hcone.fwd qi_l.toNat hq).1
          rw [hb_p.hwk, s13_cur_vars_eq hb_p.hag] at hcv_st; exact hcv_st
        have hcv_29 : 2 * cv.toNat < 2 ^ 32 := by
          have := hlen_s.core_ok.cur_vars_le; have := c.hmaxv
          unfold dimacsBound at this; omega
        let lit_p := (cv <<< (1 : Nat)) ||| pol_p
        have hlit_to : lit_p.toNat = 2 * cv.toNat + pol_p.toNat :=
          m6_bv32_shl1_or_pol cv pol_p (by omega) hpol_lt
        have hlit_cv : lit_p.toNat < 2 * s.core.cur_vars := by
          rw [hlit_to]; rcases hpol_01 with rfl | rfl <;> omega
        obtain ⟨hwf_off, _, hwf_end, _, _, hwf_le, hwf_i0, hwf_i1⟩ :=
          step13_cone_wvec_facts hlen_s hb_p.hlen hb_p.hag hdw hlit_cv
        have hcv_s1 : (aCv.val <<< (1 : BitVec 32)) ||| pol_p = lit_p := by
          rw [hacv]; rfl
        have h0_wv : (BitVec.setWidth 64 (aCv.val <<< (1 : BitVec 32) ||| pol_p) <<<
            (1 : BitVec 64)).toNat < st_p.core.wvec.length := by
          rw [hcv_s1, show (BitVec.setWidth 64 lit_p <<< (1 : BitVec 64)) =
              BitVec.setWidth 64 lit_p <<< (1 : Nat) from rfl,
            ← hwf_i0, hb_p.hlen.core_ok.wvec_len]
          have := hlen_s.core_ok.cur_vars_le; omega
        have h1_wv : (BitVec.setWidth 64 (aCv.val <<< (1 : BitVec 32) ||| pol_p) <<<
            (1 : BitVec 64) + 1).toNat < st_p.core.wvec.length := by
          rw [hcv_s1, show (BitVec.setWidth 64 lit_p <<< (1 : BitVec 64)) =
              BitVec.setWidth 64 lit_p <<< (1 : Nat) from rfl,
            show (1 : BitVec 64) = 1#64 from rfl,
            ← hwf_i1, hb_p.hlen.core_ok.wvec_len]
          have := hlen_s.core_ok.cur_vars_le; omega
        have hi1_to : (BitVec.signExtend 64 1#32).toNat = 1 := rfl
        c0_hsteps_nogrp
        have h0_lit : (BitVec.setWidth 64 lit_p <<< (1 : Nat)).toNat < st_p.core.wvec.length := by
          rw [← hwf_i0, hb_p.hlen.core_ok.wvec_len]
          have := hlen_s.core_ok.cur_vars_le; omega
        have h1_lit : (BitVec.setWidth 64 lit_p <<< (1 : Nat) + 1#64).toNat <
            st_p.core.wvec.length := by
          rw [← hwf_i1, hb_p.hlen.core_ok.wvec_len]
          have := hlen_s.core_ok.cur_vars_le; omega
        have hw0_eq : BitVec.setWidth 64
            (st_p.core.wvec[(BitVec.setWidth 64 (aCv.val <<< (1 : BitVec 32) ||| pol_p) <<<
              (1 : BitVec 64)).toNat]'h0_wv) =
            BitVec.setWidth 64
              (st_p.core.wvec[(BitVec.setWidth 64 lit_p <<< (1 : Nat)).toNat]'h0_lit) := by
          congr 2; simp only [hcv_s1]; rfl
        have hw1_eq : BitVec.setWidth 64
            (st_p.core.wvec[(BitVec.setWidth 64 (aCv.val <<< (1 : BitVec 32) ||| pol_p) <<<
              (1 : BitVec 64) + 1).toNat]'h1_wv) =
            BitVec.setWidth 64
              (st_p.core.wvec[(BitVec.setWidth 64 lit_p <<< (1 : Nat) + 1#64).toNat]'h1_lit) := by
          congr 2; simp only [hcv_s1]; rfl
        have hcur_eq : curTmk = st_p.scratch.tarjan_mark[cv.toNat]?.getD 0#32 - 1#32 := by
          rw [hcurTmk, hb0.htmk, hb_p.htmk]
        refine wp_join_group (ts := [i32, i32, Ty.bool, i64])
          (fun (nvW, ncW, limW, _, ()) mW => ∃ stW : FullState,
            layerEnd.toNat ≤ nvW.toNat ∧ nc0.toNat ≤ ncW.toNat ∧ ncW.toNat ≤ L.maxOrig ∧
            Step13ConeBase F_cur L mvC c s cv qi_l nvW.toNat ncW.toNat stW ∧
            (FullMem c stW ⋆ R) mW) ?_ ?_
        · rintro _ ⟨nvW, ncW, limW, _p, ⟨⟩⟩ mW ⟨stW, hleW, hncWg, hncWl, hbW, hmW⟩
          c0_hsteps!
          have hpol1 : (pol_p + 1#32).toNat = pol_p.toNat + 1 :=
            m6_bv32_add1 (by omega : pol_p.toNat < 2 ^ 31)
          exact ih_p (nvW, ncW, limW, pol_p + 1#32) mW (by rw [hpol1]; omega)
            ⟨stW, hleW, hncWg, hncWl, by rw [hpol1]; omega, hbW, hmW⟩
        · intro Jwe hJwe
          have hsum_eq :
              (BitVec.setWidth 64 (st_p.core.wvec[(BitVec.setWidth 64
                (aCv.val <<< (1 : BitVec 32) ||| pol_p) <<< (1 : BitVec 64)).toNat]'h0_wv) +
              BitVec.setWidth 64 (st_p.core.wvec[(BitVec.setWidth 64
                (aCv.val <<< (1 : BitVec 32) ||| pol_p) <<< (1 : BitVec 64) + 1).toNat]'h1_wv)
              ).toNat =
              (BitVec.setWidth 64 (st_p.core.wvec[(BitVec.setWidth 64 lit_p <<<
                (1 : Nat)).toNat]'h0_lit) +
              BitVec.setWidth 64 (st_p.core.wvec[(BitVec.setWidth 64 lit_p <<<
                (1 : Nat) + 1#64).toNat]'h1_lit)).toNat := by
            rw [hw0_eq, hw1_eq]
          refine step13_cone_bin_watch_wp hAddCl hLscr hLmv rfl rfl rfl rfl rfl rfl rfl rfl
            rfl hcv_s1 hacv hact hamvc halimv hamax rfl rfl rfl hw0_eq hm_lt hlen_s hw hlvl0 hdw
            hlit_cv rfl hpol_01 hwf_off (hsum_eq.trans hwf_end)
            (hsum_eq.symm ▸ hwf_le)
            hqi_le hle_p hcur_eq hb_p hmp ?_
          intro nvE ncE limE aLimE pE stE mE haLimE hleE hncEg hncEl hbE hmE
          c0_hsteps!; rw [haLimE]
          exact hJwe (nvE, ncE, limE, pE, ()) mE
            ⟨stE, hleE, le_trans hnc_pg hncEg, hncEl, hbE, hmE⟩
      · exact hJexit () mp rfl
      · exact hJexit () mp rfl

end LeanQbe.T.Examples.Kissat.Proof.Sweep
