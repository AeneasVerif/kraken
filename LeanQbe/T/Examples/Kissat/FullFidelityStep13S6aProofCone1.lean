/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProofCone0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProofCone1a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProofCone1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv

import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofCone0
import LeanQbe.T.Examples.Kissat.FullM8SweepV2ConeProof
import LeanQbe.T.Examples.Kissat.FullM6SweepProofConeLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit

/-!
# Kissat Fidelity Step 13 Shard `S6a` — `fid11_sweep_cone` Binary & Outer WP (`Cone1`)

Lifts `FullFidelitySweepEnv.fid11_sweep_cone_body` (`S11-6a` Step-12 replacement) into
`step13SweepConeSpec`, composing `Cone1a` (`binAddExpr` / `binUnitCallExpr`), `Cone1b`
(`occPassExpr`), `binPassExpr`, `depthBfsExpr`, and `full_m6_sweep_cone_step13_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep.M6SweepTactics
open LeanQbe.T.Examples.Kissat.FullM6Sweep.K6MemATactics
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
open LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv

private def binPassExpr (pHdr pWs1 pTmk pWvec pWstk pVals pTmp pFlags pKptr : Val i64)
    (mv vlim maxOrig nv_in nc_in : Val i32) (done_in : Val .bool)
    (cv qi0 layer_start : Val i32)
    (occCont : Val i32 → Val i32 → Val .bool → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  .group (sig := [[i32, i32, Ty.bool, i32]]) (fun J10 => .cons (fun p76 =>
    .group (sig := [[]]) (fun J11 => .cons (fun _ => occCont p76.1 p76.2.1 p76.2.2.1) .nil)
    (fun J11 =>
      .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p76.2.2.2.1), (.imm 2), ())) fun v78 =>
      .jnz (.var v78.1) (.jnz (.var p76.2.2.1) (.jump J11.1 (())) (
        .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p76.2.1), (.var maxOrig), ())) fun v81 =>
        .jnz (.var v81.1) (
          .let_ (Op.mk (OpCode.shl i32) ((.var cv), (.imm 1), ())) fun v83 =>
          .let_ (Op.mk (OpCode.or i32) ((.var v83.1), (.var p76.2.2.2.1), ())) fun v84 =>
          .let_ (Op.mk (OpCode.zext 32 64) ((.var v84.1), ())) fun v85 =>
          .let_ (Op.mk (OpCode.sext 32 64) ((.imm 1), ())) fun v86 =>
          .let_ (Op.mk (OpCode.shl i64) ((.var v85.1), (.var v86.1), ())) fun v87 =>
          .let_ (Op.mk (OpCode.mul i64) ((.var v87.1), (.imm 4), ())) fun v88 =>
          .let_ (Op.mk (OpCode.add i64) ((.var pWvec), (.var v88.1), ())) fun v89 =>
          .load i32 (.var v89.1) fun ld90 =>
          .let_ (Op.mk (OpCode.zext 32 64) ((.var ld90), ())) fun v91 =>
          .let_ (Op.mk (OpCode.zext 32 64) ((.var v84.1), ())) fun v92 =>
          .let_ (Op.mk (OpCode.sext 32 64) ((.imm 1), ())) fun v93 =>
          .let_ (Op.mk (OpCode.shl i64) ((.var v92.1), (.var v93.1), ())) fun v94 =>
          .let_ (Op.mk (OpCode.add i64) ((.var v94.1), (.imm 1), ())) fun v95 =>
          .let_ (Op.mk (OpCode.mul i64) ((.var v95.1), (.imm 4), ())) fun v96 =>
          .let_ (Op.mk (OpCode.add i64) ((.var pWvec), (.var v96.1), ())) fun v97 =>
          .load i32 (.var v97.1) fun ld98 =>
          .let_ (Op.mk (OpCode.zext 32 64) ((.var ld98), ())) fun v99 =>
          .let_ (Op.mk (OpCode.add i64) ((.var v91.1), (.var v99.1), ())) fun v100 =>
          .group (sig := [[i32, i32, Ty.bool, i64]]) (fun J13 => .cons (fun p102 =>
            .let_ (Op.mk (OpCode.add i32) ((.var p76.2.2.2.1), (.imm 1), ())) fun v103 =>
            .jump J10.1 ((.var p102.1), (.var p102.2.1), (.var p102.2.2.1), (.var v103.1), ()))
            .nil) (fun J13 =>
            .group (sig := [[i32, i32, Ty.bool, i64]]) (fun J14 => .cons (fun p105 =>
              .let_ (Op.mk (.cmp CmpOp.ult i64) ((.var p105.2.2.2.1), (.var v100.1), ()))
                fun v106 =>
              .jnz (.var v106.1) (.jnz (.var p105.2.2.1)
                (.jump J13.1
                  ((.var p105.1), (.var p105.2.1), (.var p105.2.2.1), (.var p105.2.2.2.1), ())) (
                .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p105.2.1), (.var maxOrig), ())) fun v109 =>
                .jnz (.var v109.1) (
                  .let_ (Op.mk (OpCode.mul i64) ((.var p105.2.2.2.1), (.imm 4), ())) fun v111 =>
                  .let_ (Op.mk (OpCode.add i64) ((.var pWstk), (.var v111.1), ())) fun v112 =>
                  .load i32 (.var v112.1) fun ld113 =>
                  .let_ (Op.mk (OpCode.add i64) ((.var p105.2.2.2.1), (.imm 1), ())) fun v114 =>
                  .let_ (Op.mk (OpCode.and i32) ((.var ld113), (.imm 2147483648), ())) fun v115 =>
                  .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var v115.1), (.imm 0), ())) fun v116 =>
                  .jnz (.var v116.1) (
                    .let_ (Op.mk (OpCode.add i64) ((.var v114.1), (.imm 1), ())) fun v117 =>
                    .jump J14.1
                      ((.var p105.1), (.var p105.2.1), (.var p105.2.2.1), (.var v117.1), ())) (
                    .let_ (Op.mk (OpCode.and i32) ((.var ld113), (.imm 2147483647), ())) fun v119 =>
                    .let_ (Op.mk (OpCode.lshr i32) ((.var v119.1), (.imm 1), ())) fun v120 =>
                    .let_ (Op.mk (OpCode.zext 32 64) ((.var v120.1), ())) fun v121 =>
                    .let_ (Op.mk (OpCode.add i64) ((.var pHdr), (.imm 776), ())) fun v122 =>
                    .load i64 (.var v122.1) fun ld123 =>
                    .let_ (Op.mk (.cmp CmpOp.uge i64) ((.var v121.1), (.var ld123), ())) fun v124 =>
                    .jnz (.var v124.1) (.jump J14.1
                      ((.var p105.1), (.var p105.2.1), (.var p105.2.2.1), (.var v114.1), ())) (
                      .let_ (Op.mk (OpCode.zext 32 64) ((.var v120.1), ())) fun v126 =>
                      .let_ (Op.mk (OpCode.mul i64) ((.var v126.1), (.imm 4), ())) fun v127 =>
                      .let_ (Op.mk (OpCode.add i64) ((.var pFlags), (.var v127.1), ())) fun v128 =>
                      .load i32 (.var v128.1) fun ld129 =>
                      .let_ (Op.mk (OpCode.and i32) ((.var ld129), (.imm 1), ())) fun v130 =>
                      .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var v130.1), (.imm 0), ())) fun v131 =>
                      .jnz (.var v131.1) (.jump J14.1
                        ((.var p105.1), (.var p105.2.1), (.var p105.2.2.1), (.var v114.1), ())) (
                        .let_ (Op.mk (OpCode.zext 32 64) ((.var v119.1), ())) fun v133 =>
                        .let_ (Op.mk (OpCode.add i64) ((.var pVals), (.var v133.1), ())) fun v134 =>
                        .load i8 (.var v134.1) fun ld135 =>
                        .let_ (Op.mk (OpCode.trunc 32 8) ((.imm 0), ())) fun v136 =>
                        .let_ (Op.mk (OpCode.sext 8 32) ((.var ld135), ())) fun v137 =>
                        .let_ (Op.mk (OpCode.sext 8 32) ((.var v136.1), ())) fun v138 =>
                        .let_ (Op.mk (.cmp CmpOp.sgt i32) ((.var v137.1), (.var v138.1), ()))
                          fun v139 =>
                        .jnz (.var v139.1) (.jump J14.1
                          ((.var p105.1), (.var p105.2.1), (.var p105.2.2.1), (.var v114.1), ())) (
                          .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var v120.1), (.var cv), ()))
                            fun v141 =>
                          .jnz (.var v141.1) (
                            .group (sig := [[i32, Ty.bool]]) (fun J15 => .cons (fun p143 =>
                              .jump J14.1 ((.var p105.1), (.var p143.1),
                                (.var p143.2.1), (.var v114.1), ())) .nil) (fun J15 =>
                              .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var v119.1), (.var v84.1), ()))
                                fun v145 =>
                              .jnz (.var v145.1)
                                (binUnitCallExpr
                                  (fun nc' d' => .jump J15.1 ((.var nc'), (.var d'), ()))
                                  pHdr pTmp pKptr p105.2.1 p105.2.2.1 qi0 p76.2.2.2.1)
                                (.jump J15.1 ((.var p105.2.1), (.var p105.2.2.1), ())))) (
                            .let_ (Op.mk (OpCode.trunc 32 8) ((.imm 0), ())) fun v166 =>
                            .let_ (Op.mk (OpCode.sext 8 32) ((.var ld135), ())) fun v167 =>
                            .let_ (Op.mk (OpCode.sext 8 32) ((.var v166.1), ())) fun v168 =>
                            .let_ (Op.mk (.cmp CmpOp.slt i32) ((.var v167.1), (.var v168.1), ()))
                              fun v169 =>
                            .jnz (.var v169.1)
                              (binUnitCallExpr
                                (fun nc' d' => .jump J14.1 ((.var p105.1), (.var nc'),
                                  (.var d'), (.var v114.1), ()))
                                pHdr pTmp pKptr p105.2.1 p105.2.2.1 qi0 p76.2.2.2.1)
                              (binAddExpr J13.1 J14.1 pHdr pWs1 pTmk pTmp pKptr mv vlim
                                p105.1 p105.2.1 p105.2.2.1 v114.1
                                p76.2.2.2.1 qi0 v119.1 v120.1 layer_start))))))) (
                  .jump J13.1
                    ((.var p105.1), (.var p105.2.1), (.var p105.2.2.1),
                      (.var p105.2.2.2.1), ())))) (
                .jump J13.1
                  ((.var p105.1), (.var p105.2.1), (.var p105.2.2.1), (.var p105.2.2.2.1), ())))
              .nil) (fun J14 =>
              .jump J14.1 ((.var p76.1), (.var p76.2.1), (.var p76.2.2.1), (.var v91.1), ()))))
        (.jump J11.1 (())))) (.jump J11.1 (()))))
    .nil) (fun J10 =>
    .jump J10.1 ((.var nv_in), (.var nc_in), (.var done_in), (.imm 0), ()))

private def depthBfsExpr
    (pHdr pWs1 pTmk pWvec pWstk pArena pVals pTmp pFlags pKptr : Val i64)
    (maxV32 vlim maxOrig clim max_depth : Val i32) : Expr Val Cont [i64] :=
  .group (sig := [[i32, i32, i32, i32, Ty.bool]]) (fun J5 => .cons (fun p58 =>
    .group (sig := [[]]) (fun J6 => .cons (fun _ =>
      .let_ (Op.mk (OpCode.zext 32 64) ((.imm 4), ())) fun v60 =>
      .let_ (Op.mk (OpCode.mul i64) ((.var v60.1), (.imm 4), ())) fun v61 =>
      .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v61.1), ())) fun v62 =>
      .load i32 (.var v62.1) fun ld63 =>
      .let_ (Op.mk (OpCode.zext 32 64) ((.imm 0), ())) fun v64 =>
      .let_ (Op.mk (OpCode.mul i64) ((.var v64.1), (.imm 4), ())) fun v65 =>
      .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v65.1), ())) fun v66 =>
      .store (t := i32) (.var p58.1) (.var v66.1) <|
      .let_ (Op.mk (OpCode.zext 32 64) ((.imm 5), ())) fun v67 =>
      .let_ (Op.mk (OpCode.mul i64) ((.var v67.1), (.imm 4), ())) fun v68 =>
      .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v68.1), ())) fun v69 =>
      .group (sig := [[i32]]) (fun J7 => .cons (fun p71 =>
        .store (t := i32) (.var p71.1) (.var v69.1) <|
        .group (sig := [[]]) (fun J8 => .cons (fun _ =>
          .let_ (Op.mk (OpCode.zext 32 64) ((.var p58.1), ())) fun v73 =>
          .let_ (Op.mk (OpCode.zext 32 64) ((.var p58.2.1), ())) fun v74 =>
          .let_ (Op.mk (OpCode.sext 32 64) ((.imm 16), ())) fun v75 =>
          .let_ (Op.mk (OpCode.shl i64) ((.var v74.1), (.var v75.1), ())) fun v76 =>
          .let_ (Op.mk (OpCode.or i64) ((.var v73.1), (.var v76.1), ())) fun v77 =>
          .ret ((.var v77.1), ())) .nil) (fun J8 =>
          .let_ (Op.mk (.cmp CmpOp.ugt i32) ((.var p58.1), (.imm 0), ())) fun v79 =>
          .jnz (.var v79.1) (
            .let_ (Op.mk (OpCode.mul i32) ((.imm 3), (.var maxV32), ())) fun v80 =>
            .let_ (Op.mk (OpCode.add i32) ((.imm 32), (.var v80.1), ())) fun v81 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var v81.1), ())) fun v82 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v82.1), (.imm 4), ())) fun v83 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v83.1), ())) fun v84 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.imm 8), ())) fun v85 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v85.1), (.imm 4), ())) fun v86 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v86.1), ())) fun v87 =>
            .let_ (Op.mk (OpCode.sub i32) ((.var p58.1), (.imm 1), ())) fun v88 =>
            .store (t := i32) (.var v88.1) (.var v87.1) <|
            .let_ (Op.mk (OpCode.zext 32 64) ((.imm 9), ())) fun v89 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v89.1), (.imm 4), ())) fun v90 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v90.1), ())) fun v91 =>
            .let_ (Op.mk (OpCode.sub i32) ((.var p58.1), (.imm 1), ())) fun v92 =>
            .store (t := i32) (.var v92.1) (.var v91.1) <|
            .let_ (Op.mk (OpCode.zext 32 64) ((.imm 10), ())) fun v93 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v93.1), (.imm 4), ())) fun v94 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v94.1), ())) fun v95 =>
            .store (t := i32) (.var p58.1) (.var v95.1) <|
            .let_ (Op.mk (OpCode.sub i32) ((.var p58.1), (.imm 1), ())) fun v96 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var v96.1), ())) fun v97 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v97.1), (.imm 4), ())) fun v98 =>
            .let_ (Op.mk (OpCode.add i64) ((.var v84.1), (.var v98.1), ())) fun v99 =>
            .store (t := i32) (.imm 4294967295) (.var v99.1) <| .jump J8.1 (()))
            (.jump J8.1 (())))) .nil) (fun J7 =>
        .let_ (Op.mk (.cmp CmpOp.ule i32) ((.var ld63), (.var p58.1), ())) fun v70 =>
        .jnz (.var v70.1) (
          .let_ (Op.mk (OpCode.sub i32) ((.var p58.1), (.var ld63), ())) fun v71 =>
          .jump J7.1 ((.var v71.1), ())) (.jump J7.1 ((.imm 0), ())))) .nil) (fun J6 =>
      .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p58.2.2.1), (.var p58.1), ())) fun v59 =>
      .jnz (.var v59.1) (
        .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p58.2.2.2.1), (.var max_depth), ())) fun v60 =>
        .jnz (.var v60.1) (.jnz (.var p58.2.2.2.2.1) (.jump J6.1 (())) (
          .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p58.2.1), (.var clim), ())) fun v62 =>
          .jnz (.var v62.1) (
            .let_ (Op.mk (OpCode.add i32) ((.var p58.2.2.2.1), (.imm 1), ())) fun v63 =>
            .group (sig := [[i32, i32, i32, Ty.bool]]) (fun J9 => .cons (fun p86 =>
              .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p86.2.2.1), (.var p58.1), ())) fun v87 =>
              .jnz (.var v87.1) (.jnz (.var p86.2.2.2.1)
                (.jump J5.1 ((.var p86.1), (.var p86.2.1), (.var p86.2.2.1),
                  (.var v63.1), (.var p86.2.2.2.1), ())) (
                .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p86.2.1), (.var clim), ())) fun v90 =>
                .jnz (.var v90.1) (
                  .let_ (Op.mk (OpCode.zext 32 64) ((.var p86.2.2.1), ())) fun v92 =>
                  .let_ (Op.mk (OpCode.mul i64) ((.var v92.1), (.imm 4), ())) fun v93 =>
                  .let_ (Op.mk (OpCode.add i64) ((.var pWs1), (.var v93.1), ())) fun v94 =>
                  .load i32 (.var v94.1) fun ld95 =>
                  .let_ (Op.mk (OpCode.zext 32 64) ((.var ld95), ())) fun v96 =>
                  .let_ (Op.mk (OpCode.mul i64) ((.var v96.1), (.imm 4), ())) fun v97 =>
                  .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v97.1), ())) fun v98 =>
                  .load i32 (.var v98.1) fun ld99 =>
                  .let_ (Op.mk (OpCode.sub i32) ((.var ld99), (.imm 1), ())) fun v100 =>
                  .let_ (Op.mk (OpCode.add i32) ((.var p86.2.2.1), (.imm 1), ())) fun v101 =>
                  binPassExpr pHdr pWs1 pTmk pWvec pWstk pVals pTmp pFlags pKptr maxV32 vlim maxOrig
                    p86.1 p86.2.1 p86.2.2.2.1 ld95 v100.1 p58.2.2.1 fun nv_b nc_b done_b =>
                    occPassExpr J9.1 pHdr pWs1 pTmk pWvec pWstk pArena pVals pTmp pFlags pKptr
                      maxV32 vlim maxOrig nv_b nc_b done_b ld95 ld99 v101.1)
                (.jump J5.1 ((.var p86.1), (.var p86.2.1), (.var p86.2.2.1),
                  (.var v63.1), (.var p86.2.2.2.1), ()))))
              (.jump J5.1 ((.var p86.1), (.var p86.2.1), (.var p86.2.2.1),
                (.var v63.1), (.var p86.2.2.2.1), ()))) .nil) (fun J9 =>
              .jump J9.1
                ((.var p58.1), (.var p58.2.1), (.var p58.2.2.1), (.var p58.2.2.2.2.1), ())))
          (.jump J6.1 (())))) (.jump J6.1 (()))) (.jump J6.1 (())))) .nil) (fun J5 =>
    .jump J5.1 ((.imm 1), (.imm 0), (.imm 0), (.imm 0), (.imm false), ()))

public section

private theorem s13_cur_vars_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.cur_vars = s.core.cur_vars :=
  congrArg (fun t => t.core.cur_vars) hag

private theorem s13_vals_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.vals = s.core.vals :=
  congrArg (fun t => t.core.vals) hag

private theorem s13_wvec_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.wvec = s.core.wvec :=
  congrArg (fun t => t.core.wvec) hag

private theorem s13_wstk_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.wstk = s.core.wstk :=
  congrArg (fun t => t.core.wstk) hag

private theorem step13_cone_bin_pass_wp
    {Γ : Env} {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s st_in : FullState}
    {vlim maxOrig nv_in nc_in cv qi_l qi0 layer_start : BitVec 32} {done_in : Bool}
    {m : Mem 64}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (pHdr pWs1 pTmk pWvec pWstk pVals pTmp pFlags pKptr : Val i64)
    (occCont : Val i32 → Val i32 → Val .bool → Expr Val Cont [i64])
    (hpHdr : pHdr = c.hdr) (hpWs1 : pWs1 = c.pWorkStk1) (hpTmk : pTmk = c.pTarjanMark)
    (hpWvec : pWvec = c.pWvec) (hpWstk : pWstk = c.pWstk)
    (hpVals : pVals = c.pVals) (hpTmp : pTmp = c.pTmp)
    (hpFlags : pFlags = c.pFlags) (hpKptr : pKptr = L.kPtr c.pScratchBuf)
    (hw : FullWitnessInv c F0 F_cur s.core)
    (hlen_s : FullState.LengthsOk c s)
    (hlv0 : s.core.cur_level = 0)
    (hdw : DenseWatchesInv F_cur s.core)
    (hLscr : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hb_in : Step13ConeBase F_cur L mvC c s cv qi_l nv_in.toNat nc_in.toNat st_in)
    (hmaxOrig : maxOrig.toNat ≤ L.maxOrig)
    (hnv_in : nv_in.toNat ≤ mvC.toNat)
    (hnc_in : nc_in.toNat ≤ L.maxOrig)
    (hqi_lt : qi_l.toNat < nv_in.toNat)
    (hqi0 : qi0 = BitVec.ofNat 32 qi_l.toNat)
    (hm : (FullMem c st_in ⋆ R) m)
    (hOcc : ∀ (nv' nc' : BitVec 32) (done' : Bool) (st' : FullState) (m' : Mem 64),
      Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' →
      nv_in.toNat ≤ nv'.toNat → nv'.toNat ≤ mvC.toNat → nc'.toNat ≤ L.maxOrig →
      qi_l.toNat < nv'.toNat → (FullMem c st' ⋆ R) m' →
      wp Γ Q X (occCont nv' nc' done') m') :
    wp Γ Q X (binPassExpr pHdr pWs1 pTmk pWvec pWstk pVals pTmp pFlags pKptr
      mvC vlim maxOrig nv_in nc_in done_in cv qi0 layer_start occCont) m := by
  subst hpHdr hpWs1 hpTmk hpVals hpTmp hpFlags hpWvec hpWstk hpKptr; dsimp [binPassExpr]
  let α := BitVec 32 × BitVec 32 × Bool × BitVec 32 × FullState
  let Inv : α → Mem 64 → Prop := fun ⟨nv_k, nc_k, done_k, pol, st_k⟩ m' =>
    Step13ConeBase F_cur L mvC c s cv qi_l nv_k.toNat nc_k.toNat st_k ∧
    nv_in.toNat ≤ nv_k.toNat ∧ nv_k.toNat ≤ mvC.toNat ∧ nc_k.toNat ≤ L.maxOrig ∧
    qi_l.toNat < nv_k.toNat ∧ pol.toNat ≤ 2 ∧ (FullMem c st_k ⋆ R) m'
  refine wp_while_state (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, ()))
    (fun p => 2 - p.2.2.2.1.toNat) Inv ?_ ?_
  · intro J10 hJ10; dsimp only; rw [wp_jump]
    exact hJ10 (nv_in, nc_in, done_in, 0#32, st_in) m
      ⟨hb_in, Nat.le_refl _, hnv_in, hnc_in, hqi_lt, by decide, hm⟩
  · intro J10 ⟨nv_k, nc_k, done_k, pol, st_k⟩ m'
      ⟨hb_k, hnv_le_k, hnv_k, hnc_k, hqi_k, hpol_le, hm'⟩ hIH
    dsimp [Blocks.get, Member.here]
    refine wp_join_state (fun (_ : Unit) => ()) (fun _ m_occ => m_occ = m') ?_ ?_
    · intro J11 () m_occ hm_occ; dsimp [Blocks.get, Member.here]; rw [hm_occ]
      exact hOcc nv_k nc_k done_k st_k m' hb_k hnv_le_k hnv_k hnc_k hqi_k hm'
    · intro J11 hJ11; c0_hstraight; (try clear hc); m6_split
      · try intro hc
        have hpol_lt : pol.toNat < 2 := hc
        (try clear hc); (try dsimp only); (try rw [wp_jnz]); refine ⟨fun hc => ?_, fun hc => ?_⟩
        · subst hc; rw [wp_jump]; exact hJ11 () m' rfl
        · subst hc; c0_hstraight; (try clear hc); m6_split
          · try intro hc
            have hnc_lt_max : nc_k.toNat < maxOrig.toNat := hc
            have hcv_le28 := hlen_s.core_ok.cur_vars_le
            have hc_mv := c.hmaxv; simp only [LeanQbe.T.Examples.LratBytes.dimacsBound] at hc_mv
            have hcv_lt : cv.toNat < s.core.cur_vars := by
              have := s13_cur_vars_eq hb_k.hag; have := hb_k.hcone.fwd qi_l.toNat hqi_k
              have := hb_k.hwk; omega
            let lit := (cv <<< 1#32) ||| pol
            have hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat := by
              have h1 : (cv <<< 1#32).toNat = cv.toNat <<< 1 := by
                rw [show (cv <<< 1#32) = cv <<< 1 from rfl, BitVec.toNat_shiftLeft,
                  Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
              rw [BitVec.toNat_or, h1]
              rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : pol.toNat < 2 ^ 1), Nat.shiftLeft_eq]
              omega
            have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
              have := hlen_s.core_ok.cur_vars_le; omega
            have ⟨hwOff, hwSz, hwEnd, hwle, hwsub, hwend_le, hwv0, hwv1⟩ :=
              step13_cone_wvec_facts hlen_s hb_k.hlen hb_k.hag hdw hlit_lt
            have hwvec_eq := s13_wvec_eq hb_k.hag
            have hshl64 : BitVec.setWidth 64 lit <<< 1#64 = BitVec.setWidth 64 lit <<< 1 :=
              BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_shiftLeft])
            have hw0_idx : (BitVec.setWidth 64 lit <<< 1).toNat < st_k.core.wvec.length := by
              rw [hwvec_eq, ← hwv0]; have := hlen_s.core_ok.wvec_len
              have := hlen_s.core_ok.cur_vars_le; omega
            have hw1_idx : (BitVec.setWidth 64 lit <<< 1 + 1#64).toNat < st_k.core.wvec.length := by
              rw [hwvec_eq, ← hwv1]; have := hlen_s.core_ok.wvec_len
              have := hlen_s.core_ok.cur_vars_le; omega
            c0_hstraight; refine head_wp_load (congrArg (fun z => c.pWvec + z * 4#64) hshl64)
              (c0_load_full_wvec hw0_idx hm') ?_
            c0_hstraight
            refine head_wp_load (congrArg (fun z => c.pWvec + (z + 1#64) * 4#64) hshl64)
              (c0_load_full_wvec hw1_idx hm') ?_
            c0_hstraight
            let wOff := BitVec.setWidth 64 st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]
            let wSz :=
              BitVec.setWidth 64 st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]
            let wEnd := wOff + wSz
            have hwEnd63 : wEnd.toNat < 2 ^ 63 := by
              have h32a : wOff.toNat < 2 ^ 32 := by
                dsimp [wOff]; rw [BitVec.toNat_setWidth]
                exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)
              have h32b : wSz.toNat < 2 ^ 32 := by
                dsimp [wSz]; rw [BitVec.toNat_setWidth]
                exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)
              have := BitVec.toNat_add wOff wSz; dsimp [wEnd]; omega
            refine wp_join_state (ts := [i32, i32, Ty.bool, i64])
              (α := BitVec 32 × BitVec 32 × Bool × BitVec 64 × FullState)
              (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, ()))
              (fun ⟨nv_j, nc_j, done_j, _, st_j⟩ m'' =>
                Step13ConeBase F_cur L mvC c s cv qi_l nv_j.toNat nc_j.toNat st_j ∧
                nv_k.toNat ≤ nv_j.toNat ∧ nv_j.toNat ≤ mvC.toNat ∧ nc_j.toNat ≤ L.maxOrig ∧
                qi_l.toNat < nv_j.toNat ∧ (FullMem c st_j ⋆ R) m'') ?_ ?_
            · intro J13 ⟨nv_j, nc_j, done_j, _, st_j⟩ m''
                ⟨hb_j, hnv_kj, hnv_j, hnc_j, hqi_j, hm''⟩
              dsimp [Blocks.get, Member.here]; c0_hstraight
              have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 := by
                simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : pol.toNat + 1 < 2 ^ 32)]
              (try dsimp only); (try rw [wp_jump])
              exact hIH (nv_j, nc_j, done_j, pol + 1#32, st_j)
                m'' (by dsimp only; rw [hpol1]; omega) ⟨hb_j, Nat.le_trans hnv_le_k hnv_kj,
                  hnv_j, hnc_j, hqi_j, by rw [hpol1]; omega, hm''⟩
            · intro J13 hJ13
              let β := BitVec 32 × BitVec 32 × Bool × BitVec 64 × FullState
              let J14Inv : β → Mem 64 → Prop := fun ⟨nv_j, nc_j, done_j, p, st_j⟩ m'' =>
                Step13ConeBase F_cur L mvC c s cv qi_l nv_j.toNat nc_j.toNat st_j ∧
                nv_k.toNat ≤ nv_j.toNat ∧ nv_j.toNat ≤ mvC.toNat ∧ nc_j.toNat ≤ L.maxOrig ∧
                qi_l.toNat < nv_j.toNat ∧ p.toNat ≤ wEnd.toNat ∧
                DenseWatchSliceOk F_cur s.core lit.toNat p.toNat (wEnd.toNat - p.toNat) ∧
                (FullMem c st_j ⋆ R) m''
              refine wp_while_state (ts := [i32, i32, Ty.bool, i64]) (α := β)
                (fun q => (q.1, q.2.1, q.2.2.1, q.2.2.2.1, ()))
                (fun q => wEnd.toNat - q.2.2.2.1.toNat) J14Inv ?_ ?_
              · intro J14 hJ14
                have hslice0 : DenseWatchSliceOk F_cur s.core lit.toNat wOff.toNat
                    (wEnd.toNat - wOff.toNat) := by
                  have := hdw.slices lit.toNat hlit_lt; rw [← hwOff, ← hwsub] at this; exact this
                dsimp only; rw [wp_jump]; exact hJ14 (nv_k, nc_k, false, wOff, st_k) m'
                  ⟨hb_k, Nat.le_refl _, hnv_k, hnc_k, hqi_k, hwle, hslice0, hm'⟩
              · intro J14 ⟨nv_j, nc_j, done_j, p, st_j⟩ m''
                  ⟨hb_j, hnv_kj, hnv_j, hnc_j, hqi_j, hp_le, hslice, hm''⟩ hIH14
                dsimp [Blocks.get, Member.here]; c0_hstraight
                have hwEnd_unf : wEnd.toNat = (st_k.core.wvec[lit.toNat * 2 ^ 1 % 2 ^ 64].toNat +
                      st_k.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64].toNat) % 2 ^ 64 := by
                  have ha : (BitVec.setWidth 64 lit <<< 1).toNat = lit.toNat * 2 ^ 1 % 2 ^ 64 := by
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                  have hb : (BitVec.setWidth 64 lit <<< 1 + 1#64).toNat =
                      (lit.toNat * 2 ^ 1 + 1) % 2 ^ 64 := by simp [BitVec.toNat_add, ha]
                  have h0 : st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] =
                      st_k.core.wvec[lit.toNat * 2 ^ 1 % 2 ^ 64] := by
                    have hq : st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]? =
                        st_k.core.wvec[lit.toNat * 2 ^ 1 % 2 ^ 64]? := by rw [ha]
                    rw [List.getElem?_eq_getElem hw0_idx,
                      List.getElem?_eq_getElem (by rw [← ha]; exact hw0_idx)] at hq; injection hq
                  have h1 : st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat] =
                      st_k.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64] := by
                    have hq : st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]? =
                        st_k.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64]? := by rw [hb]
                    rw [List.getElem?_eq_getElem hw1_idx,
                      List.getElem?_eq_getElem (by rw [← hb]; exact hw1_idx)] at hq; injection hq
                  dsimp [wEnd, wOff, wSz]; rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                    Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)),
                    Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)), h0]
                  congr 2; exact congrArg BitVec.toNat h1
                (try clear hc); m6_split
                · try intro hc
                  have hp_lt : p.toNat < wEnd.toNat := by rw [hwEnd_unf]; exact hc
                  (try clear hc); (try dsimp only); rw [wp_jnz]; refine ⟨fun hc => ?_, fun hc => ?_⟩
                  · subst hc; (try dsimp only); (try rw [wp_jump])
                    exact hJ13 (nv_j, nc_j, true, p, st_j) m''
                      ⟨hb_j, hnv_kj, hnv_j, hnc_j, hqi_j, hm''⟩
                  · subst hc; c0_hstraight; (try clear hc); m6_split
                    · try intro hc
                      have hnc_j_lt : nc_j.toNat < maxOrig.toNat := hc
                      have hnc_j_orig : nc_j.toNat < L.maxOrig := by omega
                      have hwstk_eq := s13_wstk_eq hb_j.hag
                      have hwstk_idx : p.toNat < st_j.core.wstk.length :=
                        fid_cone_hp_wstk hwstk_eq hp_lt hwend_le
                      have hrem_pos : 0 < wEnd.toNat - p.toNat := by omega
                      have hp63 : p.toNat < 2 ^ 63 := by omega
                      have hp1 : (p + 1#64).toNat = p.toNat + 1 :=
                        fid_cone_wstk_p_toNat_eq p hp63
                      have hw0_at : s.core.wstk[p.toNat]? = some st_j.core.wstk[p.toNat] := by
                        have hq : s.core.wstk[p.toNat]? = st_j.core.wstk[p.toNat]? := by
                          rw [hwstk_eq]
                        rw [List.getElem?_eq_getElem hwstk_idx] at hq; exact hq
                      c0_hstraight; refine head_wp_load rfl (c0_load_full_wstk hwstk_idx hm'') ?_
                      c0_hstraight; (try clear hc); m6_split
                      · try intro hc
                        have hocc' : st_j.core.wstk[p.toNat] &&& 2147483648#32 = 0#32 := by
                          simpa using hc
                        rcases m6_denseSlice_step_occ hslice hrem_pos hw0_at hocc' with
                          ⟨h2rem, _, _, _, _, _, hslice_next⟩
                        have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                          have hlt2 : (p + 1#64).toNat + 1 < 2 ^ 64 := by rw [hp1]; omega
                          rw [BitVec.toNat_add, (by decide : (1#64 : BitVec 64).toNat = 1),
                            Nat.mod_eq_of_lt hlt2, hp1]
                        c0_hstraight
                        exact hIH14 (nv_j, nc_j, false, p + 1#64 + 1#64, st_j) m''
                          (by dsimp only; rw [hp2]; omega)
                          ⟨hb_j, hnv_kj, hnv_j, hnc_j, hqi_j, by rw [hp2]; omega,
                            by simpa [hp2, fid_cone_sub_sub_eq] using hslice_next, hm''⟩
                      · try intro hc
                        have hbin' : st_j.core.wstk[p.toNat] &&& 2147483648#32 ≠ 0#32 := by
                          simpa using hc
                        rcases m6_denseSlice_step_bin hslice hrem_pos hw0_at hbin' with
                          ⟨_, hot_lt, hent_pair, hslice_b⟩
                        let w0 := st_j.core.wstk[p.toNat]
                        let ot := w0 &&& 2147483647#32; let ov := ot >>> 1#32
                        have hslice_next : DenseWatchSliceOk F_cur s.core lit.toNat (p + 1#64).toNat
                            (wEnd.toNat - (p + 1#64).toNat) := by
                          simpa [hp1, fid_cone_sub_sub_eq] using hslice_b
                        have hskip1 : ∀ (nc' : BitVec 32) (done' : Bool) (st' : FullState)
                            (m3 : Mem 64), Step13ConeBase F_cur L mvC c s cv qi_l nv_j.toNat
                              nc'.toNat st' → nc'.toNat ≤ L.maxOrig → (FullMem c st' ⋆ R) m3 →
                            J14 (nv_j, nc', done', p + 1#64, ()) m3 :=
                          fun nc' d' st' m3 hb' hnc' m3' => hIH14 (nv_j, nc', d', p + 1#64, st') m3
                            (by dsimp only; rw [hp1]; omega) ⟨hb', hnv_kj, hnv_j, hnc', hqi_j,
                              by rw [hp1]; omega, hslice_next, m3'⟩
                        have hot_lt' : ot.toNat < 2 * s.core.cur_vars := hot_lt
                        have hov_lt : ov.toNat < s.core.cur_vars := by
                          dsimp [ov]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                          omega
                        have hcv_j := s13_cur_vars_eq hb_j.hag
                        c0_hstraight; refine head_wp_load rfl (load_full_cur_vars hm'') ?_
                        c0_hstraight; (try clear hc); m6_split
                        · rw [wp_jump]; exact hskip1 nc_j false st_j m'' hb_j hnc_j hm''
                        · have hfl_idx : (BitVec.setWidth 64 ov).toNat <
                              st_j.core.flags.length := by
                            have := hb_j.hlen.core_ok.flags_len; have := hlen_s.core_ok.cur_vars_le
                            simp; omega
                          c0_hstraight; refine head_wp_load rfl (c0_load_full_flags hfl_idx hm'') ?_
                          c0_hstraight; (try clear hc); m6_split
                          · rw [wp_jump]; exact hskip1 nc_j false st_j m'' hb_j hnc_j hm''
                          · have hvals_idx : (BitVec.setWidth 64 ot).toNat <
                                st_j.core.vals.length := by
                              have := hb_j.hlen.core_ok.vals_len; have := hlen_s.core_ok.cur_vars_le
                              rw [BitVec.toNat_setWidth,
                                Nat.mod_eq_of_lt (by omega : ot.toNat < 2 ^ 64)]; omega
                            c0_hstep; c0_hstep
                            refine head_wp_load rfl (c0_load_full_vals hvals_idx hm'') ?_
                            c0_hstraight; (try clear hc); m6_split
                            · rw [wp_jump]; exact hskip1 nc_j false st_j m'' hb_j hnc_j hm''
                            · have hqi0_nat : qi0.toNat = qi_l.toNat := by
                                rw [hqi0, BitVec.toNat_ofNat,
                                  Nat.mod_eq_of_lt (by omega : qi_l.toNat < 2 ^ 32)]
                              have hwk_lit : 2 *
                                  (st_j.scratch.work_stk1[qi0.toNat]?.getD 0#32).toNat +
                                  pol.toNat = lit.toNat := by rw [hqi0_nat, hb_j.hwk, hlit_eq]
                              c0_hstraight; (try clear hc); m6_split
                              · refine wp_join_state (α := BitVec 32 × Bool × FullState)
                                  (fun q => (q.1, q.2.1, ()))
                                  (fun ⟨nc', done', st'⟩ m3 =>
                                    Step13ConeBase F_cur L mvC c s cv qi_l nv_j.toNat
                                      nc'.toNat st' ∧ nc'.toNat ≤ L.maxOrig ∧
                                      (FullMem c st' ⋆ R) m3) ?_ ?_
                                · intro J15 ⟨nc', done', st'⟩ m3 ⟨hb', hnc', hm3⟩
                                  dsimp [Blocks.get, Member.here]; (try rw [wp_jump])
                                  exact hskip1 nc' done' st' m3 hb' hnc' hm3
                                · intro J15 hJ15; c0_hstraight; (try clear hc); m6_split
                                  · have hot_eq_lit : ot.toNat = lit.toNat :=
                                      congrArg BitVec.toNat (by simpa [ot, w0, lit] using hc)
                                    have hent_dup : (cnfOfClauses F_cur).EntailsClause
                                        (cnfClause [lit.toNat, lit.toNat]) := by
                                      rw [show ([lit.toNat, lit.toNat] : List Nat) =
                                        [lit.toNat, ot.toNat] from
                                        congrArg (fun x => [lit.toNat, x]) hot_eq_lit.symm]
                                      exact hent_pair
                                    exact step13_cone_bin_unit_call_wp hAddCl
                                      (fun nc' d' => .jump J15 ((.var nc'), (.var d'), ()))
                                      c.hdr c.pTmp (L.kPtr c.pScratchBuf) rfl rfl rfl hLscr hLmv
                                      hlen_s hb_j hnc_j_orig hqi_j hqi0 hpol_lt hwk_lit
                                      (m6_entails_singleton_of_dup hent_dup) hm''
                                      fun nc' d' st' m3 hb' hnc' hm3 => by
                                        (try dsimp only); (try rw [wp_jump])
                                        exact hJ15 (nc', d', st') m3 ⟨hb', hnc', hm3⟩
                                  · (try rw [wp_jump])
                                    exact hJ15 (nc_j, false, st_j) m'' ⟨hb_j, hnc_j, hm''⟩
                              · have hov_ne_cv : ov ≠ cv := hc
                                c0_hstraight; (try clear hc); m6_split
                                · have hs_vals : s.core.vals[ot.toNat]?.getD 0#8 = 255#8 := by
                                    refine s13_vals_slt_zero_eq_255 hw hot_lt ?_
                                    have hve := s13_vals_eq hb_j.hag
                                    have hlen_sv : ot.toNat < s.core.vals.length := by
                                      rw [← hve]; simpa using hvals_idx
                                    have hc' : (s.core.vals[ot.toNat]).slt 0#8 = true := by
                                      simpa [hve] using hc
                                    rw [List.getElem?_eq_getElem hlen_sv, Option.getD_some]
                                    have hse : ∀ x : BitVec 8,
                                        (BitVec.signExtend 32 x).slt 0#32 = x.slt 0#8 := by decide
                                    rw [hse]; exact hc'
                                  have hent_u :=
                                    m6_entails_fst_of_snd_false hw hlv0 hot_lt hs_vals hent_pair
                                  exact step13_cone_bin_unit_call_wp hAddCl
                                    (fun nc' d' => .jump J14 ((.var nv_j), (.var nc'), (.var d'),
                                      (.var (p + 1#64)), ()))
                                    c.hdr c.pTmp (L.kPtr c.pScratchBuf) rfl rfl rfl hLscr hLmv
                                    hlen_s hb_j hnc_j_orig hqi_j hqi0 hpol_lt hwk_lit hent_u hm''
                                    fun nc' d' st' m3 hb' hnc' hm3 => by
                                      (try dsimp only); (try rw [wp_jump])
                                      exact hskip1 nc' d' st' m3 hb' hnc' hm3
                                · exact step13_cone_bin_add_wp hAddCl J13 J14 c.hdr c.pWorkStk1
                                    c.pTarjanMark c.pTmp (L.kPtr c.pScratchBuf) rfl rfl rfl rfl rfl
                                    hw hlen_s hLscr hLmv hb_j hnv_j hnc_j_orig hqi_j hpol_lt hqi0
                                    hlit_eq.symm hot_lt rfl hov_ne_cv hent_pair hm''
                                    (vlim := vlim) (layer_start := layer_start)
                                    (fun nv' nc' done' st' m3 hb' _ hnv' hnc' hqi' hm3 =>
                                      hJ13 (nv', nc', done', p + 1#64, st') m3
                                        ⟨hb', by omega, hnv', hnc', hqi', hm3⟩)
                                    (fun nv' nc' done' st' m3 hb' _ hnv' hnc' hqi' hm3 =>
                                      hIH14 (nv', nc', done', p + 1#64, st') m3
                                        (by dsimp only; rw [hp1]; omega)
                                        ⟨hb', by omega, hnv', hnc', hqi', by rw [hp1]; omega,
                                          hslice_next, hm3⟩)
                    · (try dsimp only); (try rw [wp_jump]); exact hJ13 (nv_j, nc_j, false, p, st_j)
                        m'' ⟨hb_j, hnv_kj, hnv_j, hnc_j, hqi_j, hm''⟩
                · (try dsimp only); (try rw [wp_jump]); exact hJ13 (nv_j, nc_j, done_j, p, st_j) m''
                    ⟨hb_j, hnv_kj, hnv_j, hnc_j, hqi_j, hm''⟩
          · rw [wp_jump]; exact hJ11 () m' rfl
      · rw [wp_jump]; exact hJ11 () m' rfl

private theorem step13_cone_depth_bfs_wp
    {Γ : Env} {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {L : K6Layout}
    {s st_0 : FullState}
    {maxV32 vlim maxOrig clim max_depth : BitVec 32} {m : Mem 64}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (pHdr pWs1 pTmk pWvec pWstk pArena pVals pTmp pFlags pKptr : Val i64)
    (hpHdr : pHdr = c.hdr) (hpWs1 : pWs1 = c.pWorkStk1) (hpTmk : pTmk = c.pTarjanMark)
    (hpWvec : pWvec = c.pWvec) (hpWstk : pWstk = c.pWstk) (hpArena : pArena = c.pArena)
    (hpVals : pVals = c.pVals) (hpTmp : pTmp = c.pTmp)
    (hpFlags : pFlags = c.pFlags) (hpKptr : pKptr = L.kPtr c.pScratchBuf)
    (hdense : FullDenseInvW c F0 F_cur s)
    (hmin_scr : k6MinScr ≤ c.scratch_cap)
    (hLscr : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hmaxV32 : maxV32 = BitVec.ofNat 32 L.maxV)
    (hmaxOrig : maxOrig.toNat ≤ L.maxOrig)
    (_hclim_le : clim.toNat ≤ L.maxOrig)
    (hmd_le : max_depth.toNat ≤ 3)
    (hlen_0 : st_0.LengthsOk c)
    (hag_0 : AgreesExcept step13ConeMask s st_0)
    (hgu_0 : S13GuOk L s st_0)
    (hcone_0 : FidConeInv F_cur L maxV32 st_0 1 0)
    (hm : (FullMem c st_0 ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (tmp' ws1' tmk' scr' gu' : List (BitVec 32)) (m' : Mem 64),
      have s' : FullState :=
        { core := { s.core with tmp := tmp' }
          scratch := { s.scratch with
            work_stk1 := ws1', tarjan_mark := tmk', glue_used := gu', scratch_buf := scr' } }
      let nv := (r &&& 65535#64).toNat
      let nc := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent →
      M6SweepConeOk F_cur s' nv → nc ≤ 3 * k6MaxV c.scratch_cap →
      r.toNat = nv + nc * 2 ^ 16 →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (∃ L', L'.scrLen = c.scratch_cap ∧ L'.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L' (gu'[33]?.getD 0#32) (k6StateOfScratch L' scr')) →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv, (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (depthBfsExpr pHdr pWs1 pTmk pWvec pWstk pArena pVals pTmp pFlags pKptr
      maxV32 vlim maxOrig clim max_depth) m := by
  subst hpHdr hpWs1 hpTmk hpWvec hpWstk hpArena hpVals hpTmp hpFlags hpKptr; dsimp [depthBfsExpr]
  have ⟨hlen_s, hw, _, hnodup_a, _, hlv0, hdense_m⟩ := hdense
  have hdw : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; simp [hdense_m] at hmw; exact hmw
  have hmL := L.hmaxV
  have hmaxV_ge1 : 1 ≤ maxV32.toNat := by
    rw [hmaxV32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hmaxV_lt28 : maxV32.toNat < 2 ^ 28 := by
    rw [hmaxV32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  let α5 := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × Bool × FullState
  let Inv5 : α5 → Mem 64 → Prop := fun ⟨nv, nc, qi, depth, done, st⟩ m' =>
    st.LengthsOk c ∧ AgreesExcept step13ConeMask s st ∧ S13GuOk L s st ∧
    FidConeInv F_cur L maxV32 st nv.toNat nc.toNat ∧ nv.toNat ≤ maxV32.toNat ∧
    nc.toNat ≤ L.maxOrig ∧ qi.toNat ≤ nv.toNat ∧ depth.toNat ≤ max_depth.toNat ∧
    (FullMem c st ⋆ R) m'
  refine wp_while_state (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, ()))
    (fun p => max_depth.toNat - p.2.2.2.1.toNat) Inv5 ?_ ?_
  · intro J5 hJ5; dsimp only; rw [wp_jump]
    exact hJ5 (1#32, 0#32, 0#32, 0#32, false, st_0) m
      ⟨hlen_0, hag_0, hgu_0, hcone_0, hmaxV_ge1, by simp, by simp, by simp, hm⟩
  · intro J5 ⟨nv, nc, qi, depth, done, st_e⟩ m'
      ⟨hlen_e, hag_e, hgu_e, hcone_e, hnv_vlim, hnc_orig, hqi_le, hdepth_le, hm'⟩ hIH5
    dsimp [Blocks.get, Member.here]
    refine wp_join_state (fun (_ : Unit) => ()) (fun _ m_ex => m_ex = m') ?_ ?_
    · intro J6 () m_ex hm_ex; dsimp [Blocks.get, Member.here]
      have hm_ex' : (FullMem c st_e ⋆ R) m_ex := hm_ex ▸ hm'
      have htrl_le := m6_trl_end_le_of_bdd hcone_e.k6_inv hcone_e.k6_trl_bdd
      have hmemA : (K6MemA L (L.kPtr c.pScratchBuf)
            (k6StateOfScratch L st_e.scratch.scratch_buf) ⋆ (FullK6Frame c L st_e ⋆ R)) m_ex := by
        rw [fullMem_eq_k6Frame hcone_e.scr_len, sep_comm (FullK6Frame c L st_e), sep_assoc]
          at hm_ex'
        exact k6Mem_to_amem hcone_e.k6_inv.shapes (by simpa [k6StateOfScratch] using hm_ex')
      c0_hstraight; refine head_wp_load rfl (load_k6_trl_end hmemA) ?_
      c0_hstraight; refine head_wp_store rfl rfl (store_k6_nv nv hmemA) fun _ hm1 => ?_
      c0_hstraight; refine wp_join_state (fun p => (p, ()))
        (fun un_v m2 => un_v = nv - (k6StateOfScratch L st_e.scratch.scratch_buf).trl_end ∧
          (K6MemA L (L.kPtr c.pScratchBuf)
            ((k6StateOfScratch L st_e.scratch.scratch_buf).putHdr .nv nv) ⋆
            (FullK6Frame c L st_e ⋆ R)) m2) ?_ ?_
      · intro J7 un_v m2 ⟨hun_eq, hm2⟩; dsimp [Blocks.get, Member.here]
        refine head_wp_store rfl rfl (store_k6_unass un_v hm2) fun m3 hm3 => ?_
        c0_hstraight; refine wp_join_state (fun (_ : Unit) => ()) (fun _ m4 =>
          (K6MemA L (L.kPtr c.pScratchBuf)
            (((((((k6StateOfScratch L st_e.scratch.scratch_buf).putHdr .nv nv).putHdr
              .unass (nv - (k6StateOfScratch L st_e.scratch.scratch_buf).trl_end)).putHdr
              .qlast (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr
              .qnext (nv.toNat - 1) 4294967295#32) ⋆ (FullK6Frame c L st_e ⋆ R)) m4) ?_ ?_
        · intro J8 () m4 hm4; dsimp [Blocks.get, Member.here]; c0_hstraight
          exact step13_cone_exit_post ⟨hlen_s, hw, hdense.2.2.1, hnodup_a, hdense.2.2.2.2.1,
            hlv0, hdense_m⟩ hmin_scr hLscr hLmv hlen_e hag_e hgu_e hcone_e hm4 hQ
        · intro J8 hJ8; c0_hstraight; (try clear hc); m6_split
          · have hnv_pos := hcone_e.nv_ge1
            have hnv_sub_lt : nv.toNat - 1 < L.maxV := by
              have := hcone_e.mvC_leMax; have := hcone_e.nv_le_mvC; omega
            have hqnext_off : (BitVec.setWidth 64 (32#32 + 3#32 * maxV32) * 4#64) =
                BitVec.ofNat 64 (4 * L.oQNext) := by
              have := L.hmaxV; rw [hmaxV32]; apply BitVec.eq_of_toNat_eq
              simp [K6Layout.oQNext, BitVec.toNat_add, BitVec.toNat_mul,
                Nat.mod_eq_of_lt (by omega : 32 + 3 * L.maxV < 2 ^ 32)]; omega
            have hm3' : (K6MemA L (L.kPtr c.pScratchBuf)
                (((k6StateOfScratch L st_e.scratch.scratch_buf).putHdr .nv nv).putHdr .unass
                  (nv - (k6StateOfScratch L st_e.scratch.scratch_buf).trl_end)) ⋆
                (FullK6Frame c L st_e ⋆ R)) m3 := by rw [hun_eq] at hm3; exact hm3
            c0_hstraight; refine head_wp_store rfl rfl (store_k6_qlast (nv - 1#32) hm3')
              fun _ hm4 => ?_
            c0_hstraight; refine head_wp_store rfl rfl (store_k6_qsearch (nv - 1#32) hm4)
              fun _ hm5 => ?_
            c0_hstraight; refine head_wp_store rfl rfl (store_k6_qstamp nv hm5) fun _ hm6 => ?_
            c0_hstraight; refine head_wp_store rfl (by rw [hqnext_off]; rfl)
              (store_k6_qnext_sub1 4294967295#32 hnv_pos hnv_sub_lt hm6) fun _ hm7 => ?_
            (try dsimp only); (try rw [wp_jump]); exact hJ8 () _ hm7
          · have := hcone_e.nv_ge1; omega
      · intro J7 hJ7; c0_hstraight; (try clear hc); m6_split
        · c0_hstraight; (try rw [wp_jump]); exact hJ7 _ _ ⟨rfl, hm1⟩
        · have := htrl_le; omega
    · intro J6 hJ6; c0_hstraight; (try clear hc); m6_split
      · (try intro hc); have hqi_lt : qi.toNat < nv.toNat := hc
        c0_hstraight; (try clear hc); m6_split
        · (try intro hc); have hdep_lt : depth.toNat < max_depth.toNat := hc
          (try clear hc); (try dsimp only); rw [wp_jnz]; refine ⟨fun hc => ?_, fun hc => ?_⟩
          · rw [wp_jump]; exact hJ6 () m' rfl
          · (try clear hc); c0_hstraight; m6_split
            · (try clear hc); c0_hstraight
              have hdep1 : (depth + 1#32).toNat = depth.toNat + 1 := by
                simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : depth.toNat + 1 < 2 ^ 32)]
              let β9 := BitVec 32 × BitVec 32 × BitVec 32 × Bool × FullState
              let Inv9 : β9 → Mem 64 → Prop := fun ⟨nv_k, nc_k, qi_k, done_k, st_k⟩ m'' =>
                st_k.LengthsOk c ∧ AgreesExcept step13ConeMask s st_k ∧ S13GuOk L s st_k ∧
                FidConeInv F_cur L maxV32 st_k nv_k.toNat nc_k.toNat ∧ nv.toNat ≤ nv_k.toNat ∧
                nv_k.toNat ≤ maxV32.toNat ∧ nc_k.toNat ≤ L.maxOrig ∧ qi_k.toNat ≤ nv.toNat ∧
                (FullMem c st_k ⋆ R) m''
              refine wp_while_state (ts := [i32, i32, i32, Ty.bool]) (α := β9)
                (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, ()))
                (fun p => nv.toNat - p.2.2.1.toNat) Inv9 ?_ ?_
              · intro J9 hJ9; dsimp only; rw [wp_jump]
                exact hJ9 (nv, nc, qi, done, st_e) m'
                  ⟨hlen_e, hag_e, hgu_e, hcone_e, Nat.le_refl _, hnv_vlim, hnc_orig, by omega, hm'⟩
              · intro J9 ⟨nv_k, nc_k, qi_k, done_k, st_k⟩ m''
                  ⟨hlen_k, hag_k, hgu_k, hcone_k, hnv_le_k, hnv_k, hnc_k, hqi_k_le, hm''⟩ hIH9
                dsimp [Blocks.get, Member.here]; c0_hstraight; (try clear hc); m6_split
                · try intro hc
                  have hqi_k_lt : qi_k.toNat < nv.toNat := hc
                  have hqi_k_nv : qi_k.toNat < nv_k.toNat := by omega
                  (try clear hc); (try dsimp only); rw [wp_jnz]; refine ⟨fun hc => ?_, fun hc => ?_⟩
                  · subst hc; (try dsimp only); (try rw [wp_jump])
                    exact hIH5 (nv_k, nc_k, qi_k, depth + 1#32, true, st_k) m''
                      (by dsimp only; rw [hdep1]; omega) ⟨hlen_k, hag_k, hgu_k, hcone_k,
                        hnv_k, hnc_k, by omega, by rw [hdep1]; omega, hm''⟩
                  · subst hc; c0_hstraight; (try clear hc); m6_split
                    · have hws_idx : (BitVec.setWidth 64 qi_k).toNat <
                          st_k.scratch.work_stk1.length := by
                        have := hlen_k.scratch_ok.work_stk1_len; have := hcone_k.nv_le_cv
                        have := hlen_s.core_ok.cur_vars_le; have := s13_cur_vars_eq hag_k
                        simp; omega
                      have hfwd := hcone_k.fwd qi_k.toNat hqi_k_nv
                      have hqi_ws_nat : (BitVec.setWidth 64 qi_k).toNat = qi_k.toNat := by
                        simp [BitVec.toNat_setWidth]
                      have hqi_k_len : qi_k.toNat < st_k.scratch.work_stk1.length := by
                        simpa [hqi_ws_nat] using hws_idx
                      have htmk_len :
                          st_k.scratch.work_stk1[(BitVec.setWidth 64 qi_k).toNat].toNat <
                          st_k.scratch.tarjan_mark.length := by
                        have := hlen_k.scratch_ok.tarjan_mark_len
                        have := hlen_s.core_ok.cur_vars_le; have := s13_cur_vars_eq hag_k
                        have hf := hfwd.1
                        rw [List.getElem?_eq_getElem hqi_k_len, Option.getD_some] at hf
                        have hget : st_k.scratch.work_stk1[(BitVec.setWidth 64 qi_k).toNat] =
                            st_k.scratch.work_stk1[qi_k.toNat] := by simp [hqi_ws_nat]
                        rw [hget]; omega
                      have hta := s13_tmk_ov_at st_k
                        st_k.scratch.work_stk1[(BitVec.setWidth 64 qi_k).toNat] htmk_len
                      c0_hstraight; refine head_wp_load rfl (c0_load_full_work_stk1 hws_idx hm'') ?_
                      c0_hstraight; refine head_wp_load rfl
                        (c0_load_full_tarjan_mark (by rw [hta.1]; exact htmk_len) hm'') ?_
                      c0_hstraight
                      let cv := st_k.scratch.work_stk1[(BitVec.setWidth 64 qi_k).toNat]
                      let tmk_cv := st_k.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]
                      let qi0 := tmk_cv - 1#32; let qi_next := qi_k + 1#32
                      have hwk_cv : (st_k.scratch.work_stk1[qi_k.toNat]?.getD 0#32).toNat =
                          cv.toNat := by
                        dsimp [cv]; simp [List.getElem?_eq_getElem (by simpa using hws_idx)]
                      have htmk_cv : st_k.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                          BitVec.ofNat 32 (qi_k.toNat + 1) := by rw [← hwk_cv]; exact hfwd.2
                      have hqi0 : qi0 = BitVec.ofNat 32 qi_k.toNat := by
                        dsimp [qi0, tmk_cv]; rw [← hta.2, htmk_cv]; exact bv32_ofNat_sub1 (by omega)
                      have hqi_next : qi_next.toNat = qi_k.toNat + 1 := by
                        simp [qi_next, BitVec.toNat_add,
                          Nat.mod_eq_of_lt (by omega : qi_k.toNat + 1 < 2 ^ 32)]
                      have hb_k :
                          Step13ConeBase F_cur L maxV32 c s cv qi_k nv_k.toNat nc_k.toNat st_k :=
                        ⟨hlen_k, hag_k, hgu_k, hcone_k, htmk_cv, hwk_cv⟩
                      exact step13_cone_bin_pass_wp hAddCl c.hdr c.pWorkStk1 c.pTarjanMark
                        c.pWvec c.pWstk c.pVals c.pTmp c.pFlags (L.kPtr c.pScratchBuf)
                        (fun nv_b nc_b done_b => occPassExpr J9 c.hdr c.pWorkStk1
                          c.pTarjanMark c.pWvec c.pWstk c.pArena c.pVals c.pTmp c.pFlags
                          (L.kPtr c.pScratchBuf) maxV32 vlim maxOrig nv_b nc_b done_b cv tmk_cv
                          qi_next)
                        rfl rfl rfl rfl rfl rfl rfl rfl rfl hw hlen_s hlv0 hdw hLscr hLmv hb_k
                        hmaxOrig hnv_k hnc_k hqi_k_nv hqi0 hm''
                        fun nv_b nc_b done_b st_b m_b hb_b _ hnv_b hnc_b hqi_b hm_b =>
                        step13_cone_occ_pass_wp hAddCl J9 c.hdr c.pWorkStk1
                          c.pTarjanMark c.pWvec c.pWstk c.pArena c.pVals c.pTmp c.pFlags
                          (L.kPtr c.pScratchBuf) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                          hw hnodup_a hlen_s hlv0 hdw hLscr hLmv hb_b hmaxOrig
                          hnv_b hnc_b hqi_b hm_b (vlim := vlim)
                          fun nv2 nc2 done2 st2 m2 hb2 hnv2 _ hnc2 _ hm2 =>
                            hIH9 (nv2, nc2, qi_next, done2, st2) m2
                              (by dsimp only; rw [hqi_next]; omega)
                              ⟨hb2.hlen, hb2.hag, hb2.hgu, hb2.hcone, by omega, hnv2, hnc2,
                                by rw [hqi_next]; omega, hm2⟩
                    · (try rw [wp_jump])
                      exact hIH5 (nv_k, nc_k, qi_k, depth + 1#32, false, st_k) m''
                        (by dsimp only; rw [hdep1]; omega) ⟨hlen_k, hag_k, hgu_k, hcone_k,
                          hnv_k, hnc_k, by omega, by rw [hdep1]; omega, hm''⟩
                · (try rw [wp_jump])
                  exact hIH5 (nv_k, nc_k, qi_k, depth + 1#32, done_k, st_k) m''
                    (by dsimp only; rw [hdep1]; omega) ⟨hlen_k, hag_k, hgu_k, hcone_k,
                      hnv_k, hnc_k, by omega, by rw [hdep1]; omega, hm''⟩
            · rw [wp_jump]; exact hJ6 () m' rfl
        · rw [wp_jump]; exact hJ6 () m' rfl
      · rw [wp_jump]; exact hJ6 () m' rfl

private def s13ConeInitSt (s : FullState) (root_v : BitVec 32)
    (gu0 scr1 : List (BitVec 32)) : FullState :=
  { core := s.core, scratch := { s.scratch with
    work_stk1 := s.scratch.work_stk1.set 0 root_v
    tarjan_mark := s.scratch.tarjan_mark.set root_v.toNat 1#32
    glue_used := gu0, scratch_buf := scr1 } }

private theorem step13_cone_kptr_c0 {c : FullCfg} {L0 : K6Layout}
    (hmin : k6MinScr ≤ c.scratch_cap)
    (hmv_eq :
      BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = BitVec.ofNat 32 L0.maxV) :
    c.pScratchBuf + BitVec.setWidth 64 (1280#32 +
      (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<< (1 : Nat))) * 4#64 =
      L0.kPtr c.pScratchBuf := by
  have := L0.hmaxV; have hmv_b := k6MaxV_bounds hmin; dsimp [K6Layout.kPtr]
  apply congrArg (c.pScratchBuf + ·); apply BitVec.eq_of_toNat_eq
  rw [hmv_eq]
  have hsh : (BitVec.ofNat 32 L0.maxV <<< (1 : Nat)).toNat = 2 * L0.maxV := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : L0.maxV < 2 ^ 32), Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : L0.maxV * 2 < 2 ^ 32)]; omega
  have hadd32 : (1280#32 + BitVec.ofNat 32 L0.maxV <<< (1 : Nat)).toNat = 1280 + 2 * L0.maxV := by
    rw [BitVec.toNat_add, hsh, show (1280#32 : BitVec 32).toNat = 1280 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  rw [show L0.k6Base = 1280 + 2 * L0.maxV from rfl, BitVec.toNat_mul, BitVec.toNat_setWidth,
    hadd32]; simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 1280 + 2 * L0.maxV < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (1280 + 2 * L0.maxV) * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * (1280 + 2 * L0.maxV) < 2 ^ 64)]; omega

private theorem step13_cone_seed_addr {c : FullCfg} {L0 : K6Layout}
    (hmin : k6MinScr ≤ c.scratch_cap) (hLmv : L0.maxV = k6MaxV c.scratch_cap) :
    c.pScratchBuf + BitVec.setWidth 64 (1280#32 +
      (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<< (1 : Nat))) * 4#64 +
      25#64 * 4#64 = c.pScratchBuf + BitVec.ofNat 64 (L0.k6Base + 25) * 4#64 := by
  have := L0.hmaxV; have hmv_b := k6MaxV_bounds hmin; rw [BitVec.add_assoc]
  apply congrArg (c.pScratchBuf + ·); apply BitVec.eq_of_toNat_eq
  rw [show (25#64 * 4#64 : BitVec 64) = 100#64 from rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 32), ← hLmv]
  dsimp only [K6Layout.k6Base]
  rw [show (1280 % 2 ^ 32 : Nat) = 1280 from rfl, show (4 % 2 ^ 64 : Nat) = 4 from rfl,
    show (100 % 2 ^ 64 : Nat) = 100 from rfl]
  simp only [Nat.pow_one]
  rw [Nat.mod_eq_of_lt (by omega : L0.maxV * 2 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 1280 + L0.maxV * 2 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 1280 + L0.maxV * 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (1280 + L0.maxV * 2) * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (1280 + L0.maxV * 2) * 4 + 100 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 1280 + 2 * L0.maxV + 25 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (1280 + 2 * L0.maxV + 25) * 4 < 2 ^ 64)]; omega

private theorem step13_cone_seed_init_ok {c : FullCfg} {F_cur : List (List Nat)} {L0 : K6Layout}
    {s : FullState} {scr0 gu0 : List (BitVec 32)} {mv32 root_v seed : BitVec 32}
    (hs : s.LengthsOk c) (hLscr : L0.scrLen = c.scratch_cap)
    (hmv_nat : mv32.toNat = L0.maxV) (hrv : root_v.toNat < s.core.cur_vars)
    (htmk0 : M6TmkZero s) (hscr0_len : scr0.length = L0.scrLen)
    (hsi : ({ core := s.core, scratch :=
      { s.scratch with glue_used := gu0, scratch_buf := scr0 } } : FullState).LengthsOk c)
    (hgu_i : ∀ i < 64, i ≠ 33 → gu0[i]? = s.scratch.glue_used[i]?)
    (hclean_i : K6HwmClean L0 (gu0[33]?.getD 0#32) (k6StateOfScratch L0 scr0))
    (hinv_i : ∀ P, K6Inv L0 P (k6StateOfScratch L0 scr0))
    (hts_i : K6TrailSynced (k6StateOfScratch L0 scr0))
    (hnv_i : (k6StateOfScratch L0 scr0).nv = mv32)
    (hnc_i : (k6StateOfScratch L0 scr0).nc = 0#32)
    (hlvl_i : (k6StateOfScratch L0 scr0).lvl = 0#32)
    (htrl_i : (k6StateOfScratch L0 scr0).trl_end = 0#32)
    (hna_i : (k6StateOfScratch L0 scr0).nassump = 0#32) :
    let scr1 := scr0.set (L0.k6Base + 25) seed
    let s1 := s13ConeInitSt s root_v gu0 scr1
    s1.LengthsOk c ∧ AgreesExcept step13ConeMask s s1 ∧ S13GuOk L0 s s1 ∧
      FidConeInv F_cur L0 mv32 s1 1 0 := by
  have ⟨hnv_s, hnc_s, hlvl_s, htrl_s, hna_s, hts_s, hinv_s, hclean_s⟩ :=
    s13_k6StateOfScratch_set25 L0 scr0 seed hscr0_len
  have hlen_seed : ({ core := s.core, scratch := { s.scratch with
      glue_used := gu0, scratch_buf := scr0.set (L0.k6Base + 25) seed } } :
      FullState).LengthsOk c :=
    ⟨hsi.core_ok, { hsi.scratch_ok with
      scratch_buf_len := by simp [List.length_set, hsi.scratch_ok.scratch_buf_len] }⟩
  exact step13_cone_init_ok (F_cur := F_cur) (scr0 := scr0.set (L0.k6Base + 25) seed) (gu0 := gu0)
    hs hLscr (by rw [hmv_nat]; have := L0.hmaxV; omega) (Nat.le_of_eq hmv_nat) hrv htmk0
    hlen_seed hgu_i (hclean_s _ hclean_i) (fun P => hinv_s P (hinv_i P)) (hts_s hts_i)
    (by rw [hnv_s]; exact hnv_i) (by rw [hnc_s]; exact hnc_i) (by rw [hlvl_s]; exact hlvl_i)
    (by rw [htrl_s]; exact htrl_i) (by rw [hna_s]; exact hna_i)

private theorem step13_cone_mv32_maxOrig {L0 : K6Layout} {mv32 : BitVec 32}
    (hmv_eq : mv32 = BitVec.ofNat 32 L0.maxV) : (mv32 * 3#32).toNat ≤ L0.maxOrig := by
  have := L0.hmaxV; rw [hmv_eq]
  simp only [K6Layout.maxOrig, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : L0.maxV < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 3 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : L0.maxV * 3 < 2 ^ 32)]; omega

private abbrev s13ConePostInitExpr
    (hdr_p ws1_p tmk_p wvec_p wstk_p ar_p vals_p tmp_p fl_p : Val i64)
    (root_v mv32 vlim maxOrig clim md : BitVec 32) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.add i64) (Arg.var hdr_p, Arg.imm 920#64, ())) fun p34 =>
  Expr.load i64 (Arg.var p34.fst) fun ld35 =>
  Expr.let_ (Op.mk (.shl i32) (Arg.var mv32, Arg.imm 1#32, ())) fun p36 =>
  Expr.let_ (Op.mk (.add i32) (Arg.imm 1280#32, Arg.var p36.fst, ())) fun p37 =>
  Expr.let_ (Op.mk (.zext 32 64) (Arg.var p37.fst, ())) fun p38 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p38.fst, Arg.imm 4#64, ())) fun p39 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var ld35, Arg.var p39.fst, ())) fun p40 =>
  Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 25#32, ())) fun p41 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p41.fst, Arg.imm 4#64, ())) fun p42 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p40.fst, Arg.var p42.fst, ())) fun p43 =>
  Expr.let_ (Op.mk (.xor i32) (Arg.var root_v, Arg.imm 0x9e3779b9#32, ())) fun p44 =>
  Expr.let_ (Op.mk (.or i32) (Arg.var p44.fst, Arg.imm 1#32, ())) fun p45 =>
  Expr.store (t := i32) (Arg.var p45.fst) (Arg.var p43.fst)
  (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0#32, ())) fun p46 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p46.fst, Arg.imm 4#64, ())) fun p47 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var ws1_p, Arg.var p47.fst, ())) fun p48 =>
  Expr.store (t := i32) (Arg.var root_v) (Arg.var p48.fst)
  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var root_v, ())) fun p49 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p49.fst, Arg.imm 4#64, ())) fun p50 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var tmk_p, Arg.var p50.fst, ())) fun p51 =>
  Expr.store (t := i32) (Arg.imm 1#32) (Arg.var p51.fst)
    (depthBfsExpr hdr_p ws1_p tmk_p wvec_p wstk_p ar_p vals_p tmp_p fl_p
      p40.fst mv32 vlim maxOrig clim md)))

private def s13ConeL2L3Expr
    (hdr_p ws1_p tmk_p wvec_p wstk_p ar_p vals_p tmp_p fl_p : Val i64)
    (root_v mv32 maxOrig v13 v14 md : BitVec 32) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p32 =>
    Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p33 =>
      Expr.call (as := [i64, i32]) (bs := []) "full_k6_init"
        (Arg.var hdr_p, Arg.var mv32, ()) fun _ =>
        s13ConePostInitExpr hdr_p ws1_p tmk_p wvec_p wstk_p ar_p vals_p tmp_p fl_p
          root_v mv32 p32.fst maxOrig p33.fst md) Blocks.nil)
      (fun L3 =>
        Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var maxOrig, Arg.var v14, ())) fun p33 =>
          Expr.jnz (Arg.var p33.fst)
            (Expr.jump L3.fst (Arg.var maxOrig, ()))
            (Expr.jump L3.fst (Arg.var v14, ())))) Blocks.nil)
    (fun L2 =>
      Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var mv32, Arg.var v13, ())) fun p32 =>
        Expr.jnz (Arg.var p32.fst)
          (Expr.jump L2.fst (Arg.var mv32, ()))
          (Expr.jump L2.fst (Arg.var v13, ())))

private theorem step13_cone_post_init_wp (Γ : Env)
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L0 : K6Layout}
    {s : FullState} {gu0 scr0 : List (BitVec 32)} {root_v mv32 vlim maxOrig clim md : BitVec 32}
    {hdr_p ws1_p tmk_p wvec_p wstk_p ar_p vals_p tmp_p fl_p : Val i64}
    {R : Mem 64 → Prop} {m_i : Mem 64} {Q : Post [i64]} {X : XPost}
    (hhdr : hdr_p = c.hdr) (hws1 : ws1_p = c.pWorkStk1) (htmk : tmk_p = c.pTarjanMark)
    (hwvec : wvec_p = c.pWvec) (hwstk : wstk_p = c.pWstk) (har : ar_p = c.pArena)
    (hvals : vals_p = c.pVals) (htmp : tmp_p = c.pTmp) (hfl : fl_p = c.pFlags)
    (hdense : FullDenseInvW c F0 F_cur s) (hmin : k6MinScr ≤ c.scratch_cap)
    (hLscr : L0.scrLen = c.scratch_cap) (hLmv : L0.maxV = k6MaxV c.scratch_cap)
    (hmv_nat : mv32.toNat = L0.maxV) (hmv_eq : mv32 = BitVec.ofNat 32 L0.maxV)
    (hmv_def : mv32 = BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)))
    (hmorig : maxOrig.toNat ≤ L0.maxOrig) (hclim : clim.toNat ≤ L0.maxOrig)
    (hmd : md.toNat ≤ 3) (hrv : root_v.toNat < s.core.cur_vars) (htmk0 : M6TmkZero s)
    (hscr0_len : scr0.length = L0.scrLen)
    (hsi : ({ core := s.core, scratch :=
      { s.scratch with glue_used := gu0, scratch_buf := scr0 } } : FullState).LengthsOk c)
    (hgu_i : ∀ i < 64, i ≠ 33 → gu0[i]? = s.scratch.glue_used[i]?)
    (hclean_i : K6HwmClean L0 (gu0[33]?.getD 0#32) (k6StateOfScratch L0 scr0))
    (hinv_i : ∀ P, K6Inv L0 P (k6StateOfScratch L0 scr0))
    (hts_i : K6TrailSynced (k6StateOfScratch L0 scr0))
    (hnv_i : (k6StateOfScratch L0 scr0).nv = mv32)
    (hnc_i : (k6StateOfScratch L0 scr0).nc = 0#32)
    (hlvl_i : (k6StateOfScratch L0 scr0).lvl = 0#32)
    (htrl_i : (k6StateOfScratch L0 scr0).trl_end = 0#32)
    (hna_i : (k6StateOfScratch L0 scr0).nassump = 0#32)
    (hm_i : (FullMem c { core := s.core, scratch :=
      { s.scratch with glue_used := gu0, scratch_buf := scr0 } } ⋆ R) m_i)
    (hQ : ∀ (r : BitVec 64) (tmp' ws1' tmk' scr' gu' : List (BitVec 32)) (m' : Mem 64),
      let s' := { s with
        core := { s.core with tmp := tmp' }
        scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk',
                                    scratch_buf := scr', glue_used := gu' } }
      let nv := (r &&& 65535#64).toNat
      let nc := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent → M6SweepConeOk F_cur s' nv →
      nc ≤ 3 * k6MaxV c.scratch_cap → r.toNat = nv + nc * 2 ^ 16 →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (∃ L', L'.scrLen = c.scratch_cap ∧ L'.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L' (gu'[33]?.getD 0#32) (k6StateOfScratch L' scr')) →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i, i < nv ∧ (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (s13ConePostInitExpr hdr_p ws1_p tmk_p wvec_p wstk_p ar_p vals_p tmp_p fl_p
        root_v mv32 vlim maxOrig clim md) m_i := by
  subst hhdr hws1 htmk hwvec hwstk har hvals htmp hfl
  have hs := hdense.1
  have hscr64 : c.scratch_cap < 2 ^ 64 := by have := c.hsize; have := c.havail_fit; omega
  let s_i : FullState := { core := s.core, scratch :=
    { s.scratch with glue_used := gu0, scratch_buf := scr0 } }
  have hk6_32 : L0.k6Base + 32 ≤ L0.scrLen := by
    have := L0.hmaxV; have := L0.hacap
    dsimp [K6Layout.k6Base, K6Layout.scrLen, K6Layout.oArena]; omega
  have hseed_idx : (BitVec.ofNat 64 (L0.k6Base + 25)).toNat < s_i.scratch.scratch_buf.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; dsimp [s_i]; omega
  c0_hstraight; refine head_wp_load rfl (load_full_scratch_buf_ptr hm_i) ?_
  let seed := (root_v ^^^ 2654435769#32) ||| 1#32
  c0_hstraight; refine head_wp_store rfl
    (by dsimp only [Arg.val, Prod.fst]; rw [hmv_def]; exact step13_cone_seed_addr hmin hLmv)
    (c0_store_full_scratch_buf (s := s_i) seed hseed_idx hm_i) fun m_seed hm_seed => ?_
  let scr1 := scr0.set (L0.k6Base + 25) seed
  let s_seed : FullState := { core := s.core, scratch :=
    { s.scratch with glue_used := gu0, scratch_buf := scr1 } }
  have hidx25 : (BitVec.ofNat 64 (L0.k6Base + 25)).toNat = L0.k6Base + 25 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : L0.k6Base + 25 < 2 ^ 64)]
  have hm_seed' : (FullMem c s_seed ⋆ R) m_seed := by
    dsimp [s_seed, scr1]; rw [← hidx25]; exact hm_seed
  have hws0_idx : (BitVec.signExtend 64 0#32).toNat < s_seed.scratch.work_stk1.length := by
    have hlen_ws := hs.scratch_ok.work_stk1_len
    have := hs.core_ok.cur_vars_le; dsimp [s_seed]; simp; omega
  have h0_64' : (BitVec.ofNat 64 0 : BitVec 64).toNat = 0 := by decide
  let s_w0 : FullState := { s_seed with scratch := { s_seed.scratch with
    work_stk1 := s_seed.scratch.work_stk1.set 0 root_v } }
  have htmk0_idx : (BitVec.setWidth 64 root_v).toNat < s_w0.scratch.tarjan_mark.length := by
    have hlen_tm := hs.scratch_ok.tarjan_mark_len
    have := hs.core_ok.cur_vars_le; dsimp [s_w0, s_seed]; simp; omega
  c0_hstraight; refine head_wp_store rfl rfl
    (c0_store_full_work_stk1 root_v hws0_idx hm_seed') fun m_w0 hm_w0 => ?_
  have hm_w0' : (FullMem c s_w0 ⋆ R) m_w0 := by
    dsimp [s_w0]; rw [← h0_64']; exact hm_w0
  c0_hstraight; refine head_wp_store rfl rfl
    (c0_store_full_tarjan_mark (s := s_w0) 1#32 htmk0_idx hm_w0') fun m_0 hm_0 => ?_
  let s1 := s13ConeInitSt s root_v gu0 scr1
  have hm_0' : (FullMem c s1 ⋆ R) m_0 := by
    dsimp [s1, s13ConeInitSt, s_w0, s_seed]
    rw [← show (BitVec.setWidth 64 root_v).toNat = root_v.toNat by simp]; exact hm_0
  have ⟨hlen_1, hag_1, hgu_1, hcone_1⟩ := step13_cone_seed_init_ok (F_cur := F_cur)
    (L0 := L0) (mv32 := mv32) (seed := seed) hs hLscr hmv_nat hrv htmk0 hscr0_len hsi
    hgu_i hclean_i hinv_i hts_i hnv_i hnc_i hlvl_i htrl_i hna_i
  clear hm_i hm_seed hm_seed' hm_w0 hm_w0' hm_0
  clear_value s_i s_seed s_w0 seed
  exact step13_cone_depth_bfs_wp (L := L0) hAddCl c.hdr c.pWorkStk1 c.pTarjanMark c.pWvec c.pWstk
    c.pArena c.pVals c.pTmp c.pFlags _ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by dsimp only [Prod.fst]; rw [hmv_def]; exact step13_cone_kptr_c0 hmin (hmv_def ▸ hmv_eq))
    hdense hmin hLscr hLmv hmv_eq hmorig hclim hmd
    hlen_1 hag_1 hgu_1 hcone_1 hm_0' hQ

private theorem step13_cone_l2_l3_wp (Γ : Env)
    (hInit : M6EnvSpec Γ "full_k6_init" step13K6InitSpec)
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L0 : K6Layout}
    {s : FullState} {root_v mv32 maxOrig p13 v13 v14 md : BitVec 32}
    {hdr_p ws1_p tmk_p wvec_p wstk_p ar_p vals_p tmp_p fl_p : Val i64}
    {R : Mem 64 → Prop} {m2 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hhdr : hdr_p = c.hdr) (hws1 : ws1_p = c.pWorkStk1) (htmk : tmk_p = c.pTarjanMark)
    (hwvec : wvec_p = c.pWvec) (hwstk : wstk_p = c.pWstk) (har : ar_p = c.pArena)
    (hvals : vals_p = c.pVals) (htmp : tmp_p = c.pTmp) (hfl : fl_p = c.pFlags)
    (hdense : FullDenseInvW c F0 F_cur s) (hmin : k6MinScr ≤ c.scratch_cap)
    (hLscr : L0.scrLen = c.scratch_cap) (hLmv : L0.maxV = k6MaxV c.scratch_cap)
    (hLhwm : K6HwmClean L0 (s.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L0 s.scratch.scratch_buf))
    (hmv_nat : mv32.toNat = L0.maxV) (hmv_eq : mv32 = BitVec.ofNat 32 L0.maxV)
    (hmv_def : mv32 = BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)))
    (hmorig_eq : maxOrig = mv32 * 3#32) (hp13 : p13.toNat ≤ 5)
    (hv13 : v13 = 256#32 <<< p13) (hv14 : v14 = 1024#32 <<< p13)
    (hmd : md.toNat ≤ 3) (hrv : root_v.toNat < s.core.cur_vars) (htmk0 : M6TmkZero s)
    (hm2 : (FullMem c s ⋆ R) m2)
    (hQ : ∀ (r : BitVec 64) (tmp' ws1' tmk' scr' gu' : List (BitVec 32)) (m' : Mem 64),
      let s' := { s with
        core := { s.core with tmp := tmp' }
        scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk',
                                    scratch_buf := scr', glue_used := gu' } }
      let nv := (r &&& 65535#64).toNat
      let nc := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent → M6SweepConeOk F_cur s' nv →
      nc ≤ 3 * k6MaxV c.scratch_cap → r.toNat = nv + nc * 2 ^ 16 →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (∃ L', L'.scrLen = c.scratch_cap ∧ L'.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L' (gu'[33]?.getD 0#32) (k6StateOfScratch L' scr')) →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i, i < nv ∧ (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (s13ConeL2L3Expr hdr_p ws1_p tmk_p wvec_p wstk_p ar_p vals_p tmp_p fl_p
        root_v mv32 maxOrig v13 v14 md) m2 := by
  subst hhdr hws1 htmk hwvec hwstk har hvals htmp hfl hv13 hv14
  have hscr64 : c.scratch_cap < 2 ^ 64 := by have := c.hsize; have := c.havail_fit; omega
  have hcap64 : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hscr64]
  have hlen_s := hdense.1
  have hmv_bounds := k6MaxV_bounds hmin
  have hcomp := fid_comp_vlim_clim hp13
  dsimp only [s13ConeL2L3Expr]
  refine wp_join_state (fun p => (p, ()))
    (fun vlim m3 => m3 = m2 ∧ 1 ≤ vlim.toNat ∧ vlim.toNat ≤ L0.maxV) ?_ ?_
  · intro J3 vlim m3 ⟨hm3, _, _⟩; have hm_m3 : (FullMem c s ⋆ R) m3 := hm3 ▸ hm2
    clear hm2 hm3 J3
    rw [Blocks.get_here]
    refine wp_join_state (fun p => (p, ()))
      (fun clim m4 => m4 = m3 ∧ clim.toNat ≤ L0.maxOrig) ?_ ?_
    · intro J4 clim m4 ⟨hm4, hclim_le⟩; have hm_m4 : (FullMem c s ⋆ R) m4 := hm4 ▸ hm_m3
      clear hm_m3 hm4 J4
      rw [Blocks.get_here]
      refine head_wp_call rfl (hInit _ _ _ _ ⟨c, s, R, rfl, hlen_s, hm_m4,
        fun hbad => by
          dsimp [Arg.val] at hbad; (try rw [hcap64] at hbad)
          have hmv_id : (BitVec.setWidth 32
              (BitVec.ofNat 64 (k6MaxV c.scratch_cap))).toNat = L0.maxV := by
            rw [← hmv_def]; exact hmv_nat
          (try rw [hmv_id] at hbad); rw [← hLmv] at hbad; omega,
        fun _ _ => ⟨L0, hLscr, hLmv, hLhwm,
        fun scr0 gu0 m_i hlen_i _ hgu_i _ _ hclean_i hinv_i hts_i
            hnv_i hnc_i hlvl_i _ htrl_i _ _ hna_i _ _ _ hm_i => ?_⟩⟩)
      clear hInit hm_m4
      exact step13_cone_post_init_wp Γ hAddCl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        hdense hmin hLscr hLmv hmv_nat hmv_eq hmv_def
        (hmorig_eq ▸ step13_cone_mv32_maxOrig hmv_eq)
        hclim_le hmd hrv htmk0 (hlen_i.scratch_ok.scratch_buf_len.trans hLscr.symm)
        hlen_i hgu_i hclean_i hinv_i hts_i hnv_i
        hnc_i hlvl_i htrl_i hna_i hm_i hQ
    · intro J4 hJ4; clear hm_m3 hQ hAddCl hInit; m6_split
      · (try rw [wp_jump]); dsimp only [vals, Arg.val] at *
        refine hJ4 _ _ ⟨rfl, ?_⟩
        rw [hmorig_eq]; exact step13_cone_mv32_maxOrig hmv_eq
      · (try rw [wp_jump]); dsimp only [vals, Arg.val] at *; refine hJ4 _ _ ⟨rfl, ?_⟩
        have hsh1024 := fid_shl_1024_eq hp13
        have hpow : 2 ^ p13.toNat ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hp13
        have h1024_nat : (1024#32 <<< p13).toNat = 1024 * 2 ^ p13.toNat := by
          rw [Nat.mod_eq_of_lt (by omega : p13.toNat < 32)] at hsh1024; exact hsh1024
        have hm_hc : (BitVec.ofNat 32 L0.maxV * 3#32).toNat = 3 * L0.maxV := by
          have := L0.hmaxV
          rw [BitVec.toNat_mul, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : L0.maxV < 2 ^ 32),
            show (3#32 : BitVec 32).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega : L0.maxV * 3 < 2 ^ 32)]; omega
        have h1024_hc : 1024 % 2 ^ 32 * 2 ^ p13.toNat % 2 ^ 32 = 1024 * 2 ^ p13.toNat := by
          rw [show (1024 % 2 ^ 32 : Nat) = 1024 from rfl,
            Nat.mod_eq_of_lt (by omega : 1024 * 2 ^ p13.toNat < 2 ^ 32)]
        rw [hmorig_eq, hmv_eq] at hc
        try rw [hm_hc] at hc
        try rw [h1024_hc] at hc
        unfold K6Layout.maxOrig at *; rw [h1024_nat]; omega
  · intro J3 hJ3; clear hm2 hQ hAddCl hInit hdense hLhwm; m6_split
    · (try rw [wp_jump]); dsimp only [vals, Arg.val] at *
      refine hJ3 _ _ ⟨rfl, ?_, ?_⟩ <;> omega
    · (try rw [wp_jump]); dsimp only [vals, Arg.val] at *
      have ⟨hsh256, h256_pos⟩ := fid_shl_256_props hp13
      have hpow : 2 ^ p13.toNat ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hp13
      rw [Nat.mod_eq_of_lt (by omega : p13.toNat < 32)] at hsh256
      have h256_nat : (256#32 <<< p13).toNat = 256 * 2 ^ p13.toNat := hsh256
      have h256_hc : 256 % 2 ^ 32 * 2 ^ p13.toNat % 2 ^ 32 = 256 * 2 ^ p13.toNat := by
        rw [show (256 % 2 ^ 32 : Nat) = 256 from rfl,
          Nat.mod_eq_of_lt (by omega : 256 * 2 ^ p13.toNat < 2 ^ 32)]
      try rw [hmv_nat, h256_hc] at hc
      refine hJ3 _ _ ⟨rfl, ?_, ?_⟩ <;> · rw [h256_nat]; omega

/-- Lift `FullFidelitySweepEnv.fid11_sweep_cone_body` into `step13SweepConeSpec`. -/
private def s13ConeTopExpr (hdr : Val i64) (root_v : Val i32) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 928, ())) fun p0 =>
  Expr.load i64 (Arg.var p0.fst) fun ld1 =>
  Expr.call (as := [i64]) (bs := [i64]) "full_m6_max_v" (Arg.var ld1, ()) fun p2 =>
  Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p2.fst, ())) fun p3 =>
  Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var p3.fst, Arg.imm 0, ())) fun p4 =>
  Expr.jnz (Arg.var p4.fst) (Expr.ret (Arg.imm 0, ())) (
    Expr.let_ (Op.mk (.mul i32) (Arg.var p3.fst, Arg.imm 3, ())) fun p5 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 432, ())) fun p6 =>
    Expr.load i64 (Arg.var p6.fst) fun ld7 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 28, ())) fun p8 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p8.fst, Arg.imm 4, ())) fun p9 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld7, Arg.var p9.fst, ())) fun p10 =>
    Expr.load i32 (Arg.var p10.fst) fun ld11 =>
    Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p12 =>
      Expr.let_ (Op.mk (.shl i32) (Arg.imm 256, Arg.var p12.fst, ())) fun p13 =>
      Expr.let_ (Op.mk (.shl i32) (Arg.imm 1024, Arg.var p12.fst, ())) fun p14 =>
      Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p15 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 848, ())) fun p16 =>
        Expr.load i64 (Arg.var p16.fst) fun ld17 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 864, ())) fun p18 =>
        Expr.load i64 (Arg.var p18.fst) fun ld19 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 104, ())) fun p20 =>
        Expr.load i64 (Arg.var p20.fst) fun ld21 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 120, ())) fun p22 =>
        Expr.load i64 (Arg.var p22.fst) fun ld23 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 112, ())) fun p24 =>
        Expr.load i64 (Arg.var p24.fst) fun ld25 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 64, ())) fun p26 =>
        Expr.load i64 (Arg.var p26.fst) fun ld27 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 136, ())) fun p28 =>
        Expr.load i64 (Arg.var p28.fst) fun ld29 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 800, ())) fun p30 =>
        Expr.load i64 (Arg.var p30.fst) fun ld31 =>
        s13ConeL2L3Expr hdr ld17 ld19 ld21 ld23 ld25 ld27 ld29 ld31
          root_v p3.fst p5.fst p13.fst p14.fst p15.fst) Blocks.nil)
        (fun L1 =>
          Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl)
            (Arg.var p12.fst, Arg.imm 0, ())) fun p15 =>
          Expr.jnz (Arg.var p15.fst)
            (Expr.jump L1.fst (Arg.imm 3, ()))
            (Expr.jump L1.fst (Arg.imm 2, ())))) Blocks.nil)
      (fun L0 =>
        Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl)
          (Arg.var ld11, Arg.imm 5, ())) fun p12 =>
        Expr.jnz (Arg.var p12.fst)
          (Expr.jump L0.fst (Arg.imm 5, ()))
          (Expr.jump L0.fst (Arg.var ld11, ()))))

private theorem m6MaxVSpec_intro {cap : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : Q (BitVec.ofNat 64 (k6MaxV cap.toNat), ()) m) :
    m6MaxVSpec (cap, ()) m Q X := h

theorem full_m6_sweep_cone_step13_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hInit : M6EnvSpec Γ "full_k6_init" step13K6InitSpec)
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (args : Tup Val [i64, i32]) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hpre : step13SweepConeSpec args m Q X) :
    Func.wp Γ FullFidelitySweepEnv.fid11_sweep_cone_body args m Q X := by
  rcases args with ⟨h, root_v, ⟨⟩⟩
  rcases hpre with ⟨c, F0, F_cur, s, R, rfl, hdense, hmin_scr, hroot_lt, htmk0,
    ⟨L0, hL0_scr, hL0_mv, hL0_hwm⟩, hm, hQ⟩
  have hlen_s := hdense.1
  have hscr64 : c.scratch_cap < 2 ^ 64 := by have := c.hsize; have := c.havail_fit; omega
  have hscr_mod : c.scratch_cap % 18446744073709551616 = c.scratch_cap := Nat.mod_eq_of_lt hscr64
  have hcap64 : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    rw [BitVec.toNat_ofNat]; exact hscr_mod
  have hmv_bounds := k6MaxV_bounds hmin_scr
  let mv32 : BitVec 32 := BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap))
  have hmv32_nat : mv32.toNat = L0.maxV := by
    dsimp [mv32]; rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 32), ← hL0_mv]
  have hmv32_eq : mv32 = BitVec.ofNat 32 L0.maxV :=
    BitVec.eq_of_toNat_eq (by rw [hmv32_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  unfold Func.wp
  rw [show FullFidelitySweepEnv.fid11_sweep_cone_body Val Cont =
      fun ⟨h0, r0, ()⟩ => s13ConeTopExpr h0 r0 by t_kernel_rfl]
  unfold s13ConeTopExpr
  c0_hsteps_nogrp; refine head_wp_call (by dsimp [vals, Arg.val]) (hMaxV _ _ _ _ ?_)
  clear hMaxV
  refine m6MaxVSpec_intro ?_
  dsimp only
  rw [hcap64]
  c0_hstep; c0_hstep; rw [wp_jnz]; dsimp only [Arg.val, Prod.fst]
  refine ⟨fun hc => ?_, fun _ => ?_⟩
  · exfalso
    have h0 := congrArg BitVec.toNat (beq_iff_eq.mp hc)
    change mv32.toNat = (0#32).toNat at h0
    rw [hmv32_nat] at h0; simp at h0; omega
  · have hgu28_idx : (BitVec.setWidth 64 28#32).toNat < s.scratch.glue_used.length :=
      fid_gu28_lt hlen_s
    c0_hsteps_nogrp
    refine wp_join_state (fun p => (p, ()))
      (fun p13 m1 => m1 = m ∧ p13.toNat ≤ 5) ?_ ?_
    · intro J1 p13 m1 ⟨hm1, hp13_le⟩; have hm_m1 : (FullMem c s ⋆ R) m1 := hm1 ▸ hm
      clear hm hm1 J1
      rw [Blocks.get_here]; c0_hsteps_nogrp
      refine wp_join_state (fun p => (p, ())) (fun md m2 => m2 = m1 ∧ md.toNat ≤ 3) ?_ ?_
      · intro J2 md m2 ⟨hm2, hmd_le⟩; have hm_m2 : (FullMem c s ⋆ R) m2 := hm2 ▸ hm_m1
        clear hm_m1 hm2 J2
        rw [Blocks.get_here]; c0_hsteps_nogrp
        have hp13_mod : p13.toNat % 32 = p13.toNat := Nat.mod_eq_of_lt (by omega)
        have hv13_eq : ((256 : BitVec 32) <<< (p13.toNat % 32), ()).fst = 256#32 <<< p13 := by
          dsimp only [Prod.fst]; rw [hp13_mod]; rfl
        have hv14_eq : ((1024 : BitVec 32) <<< (p13.toNat % 32), ()).fst = 1024#32 <<< p13 := by
          dsimp only [Prod.fst]; rw [hp13_mod]; rfl
        exact step13_cone_l2_l3_wp Γ hInit hAddCl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          hdense hmin_scr hL0_scr hL0_mv hL0_hwm
          hmv32_nat hmv32_eq rfl rfl hp13_le hv13_eq hv14_eq hmd_le hroot_lt htmk0 hm_m2 hQ
      · intro J2 hJ2; clear hm_m1 hQ hAddCl hInit hdense hL0_hwm
        c0_hstep; rw [wp_jnz]; dsimp only [Arg.val, Prod.fst]
        refine ⟨fun _ => ?_, fun _ => ?_⟩
        · rw [wp_jump]; exact hJ2 _ _ ⟨rfl, by (try dsimp only [Arg.val]); decide⟩
        · rw [wp_jump]; exact hJ2 _ _ ⟨rfl, by (try dsimp only [Arg.val]); decide⟩
    · intro J1 hJ1; clear hm hQ hAddCl hInit hdense hL0_hwm
      c0_hstep; rw [wp_jnz]; dsimp only [Arg.val, Prod.fst]
      refine ⟨fun _ => ?_, fun hc => ?_⟩
      · rw [wp_jump]; exact hJ1 _ _ ⟨rfl, by (try dsimp only [Arg.val]); decide⟩
      · rw [wp_jump]; (try dsimp only [Arg.val])
        simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc
        exact hJ1 _ _ ⟨rfl, hc⟩

end
end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
