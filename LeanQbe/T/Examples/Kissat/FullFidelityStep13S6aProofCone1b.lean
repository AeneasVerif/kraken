module
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProofCone0
public import LeanQbe.T.Examples.Kissat.FullFidelitySweep

import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofCone0
import LeanQbe.T.Examples.Kissat.FullM8SweepV2ConeProof
import LeanQbe.T.Examples.Kissat.FullM6SweepProofConeLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep.M6SweepTactics
open LeanQbe.T.Examples.Kissat.FullFidelitySweep

@[expose] public section

def occScanExpr (J15 : Cont [i32, .bool, .bool, i32, i32])
    (pWs1 pTmk pArena pVals pTmp pFlags : Val i64)
    (mv savedNv cr sz cv tmk_cv pol : Val i32) (done_cur : Val .bool) :
    Expr Val Cont [i64] :=
  .group (sig := [[i32, i32, i32]]) (fun J20 => .cons (fun p150 =>
      .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p150.2.2.1), (.var sz), ())) fun v151 =>
      .jnz (.var v151.1) (
        .let_ (Op.mk (OpCode.zext 32 64) ((.var cr), ())) fun v152 =>
        .let_ (Op.mk (OpCode.add i64) ((.var v152.1), (.imm 3), ())) fun v153 =>
        .let_ (Op.mk (OpCode.zext 32 64) ((.var p150.2.2.1), ())) fun v154 =>
        .let_ (Op.mk (OpCode.add i64) ((.var v153.1), (.var v154.1), ())) fun v155 =>
        .let_ (Op.mk (OpCode.mul i64) ((.var v155.1), (.imm 4), ())) fun v156 =>
        .let_ (Op.mk (OpCode.add i64) ((.var pArena), (.var v156.1), ())) fun v157 =>
        .load i32 (.var v157.1) fun ld158 =>
        .let_ (Op.mk (OpCode.zext 32 64) ((.var ld158), ())) fun v159 =>
        .let_ (Op.mk (OpCode.add i64) ((.var pVals), (.var v159.1), ())) fun v160 =>
        .load i8 (.var v160.1) fun ld161 =>
        .let_ (Op.mk (OpCode.trunc 32 8) ((.imm 0), ())) fun v162 =>
        .let_ (Op.mk (OpCode.sext 8 32) ((.var ld161), ())) fun v163 =>
        .let_ (Op.mk (OpCode.sext 8 32) ((.var v162.1), ())) fun v164 =>
        .let_ (Op.mk (.cmp CmpOp.sgt i32) ((.var v163.1), (.var v164.1), ())) fun v165 =>
        .jnz (.var v165.1) (
          .jump J15 ((.var p150.1), (.var done_cur), (.imm true),
                (.var p150.2.1), (.var p150.2.2.1), ())
        ) (
          .group (sig := [[i32, Ty.bool, Ty.bool, i32]]) (fun J21 => .cons (fun p167 =>
              .let_ (Op.mk (OpCode.add i32) ((.var p150.2.2.1), (.imm 1), ())) fun v168 =>
              .jump J20.1 ((.var p167.1), (.var p167.2.2.2.1), (.var v168.1), ())
            ) .nil) (fun J21 =>
            .let_ (Op.mk (OpCode.trunc 32 8) ((.imm 0), ())) fun v167 =>
            .let_ (Op.mk (OpCode.sext 8 32) ((.var ld161), ())) fun v168 =>
            .let_ (Op.mk (OpCode.sext 8 32) ((.var v167.1), ())) fun v169 =>
            .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var v168.1), (.var v169.1), ())) fun v170 =>
            .jnz (.var v170.1) (
              .let_ (Op.mk (OpCode.lshr i32) ((.var ld158), (.imm 1), ())) fun v171 =>
              .let_ (Op.mk (OpCode.zext 32 64) ((.var v171.1), ())) fun v172 =>
              .let_ (Op.mk (OpCode.mul i64) ((.var v172.1), (.imm 4), ())) fun v173 =>
              .let_ (Op.mk (OpCode.add i64) ((.var pFlags), (.var v173.1), ())) fun v174 =>
              .load i32 (.var v174.1) fun ld175 =>
              .let_ (Op.mk (OpCode.and i32) ((.var ld175), (.imm 1), ())) fun v176 =>
              .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var v176.1), (.imm 0), ())) fun v177 =>
              .jnz (.var v177.1) (
                .jump J15 ((.var p150.1), (.var done_cur), (.imm true),
                    (.var p150.2.1), (.var p150.2.2.1), ())
              ) (
                .let_ (Op.mk (OpCode.zext 32 64) ((.var v171.1), ())) fun v178 =>
                .let_ (Op.mk (OpCode.mul i64) ((.var v178.1), (.imm 4), ())) fun v179 =>
                .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v179.1), ())) fun v180 =>
                .load i32 (.var v180.1) fun ld181 =>
                .group (sig := [[]]) (fun J22 => .cons (fun p183 =>
                    .group (sig := [[]]) (fun J23 => .cons (fun p185 =>
                        .group (sig := [[i32, Ty.bool, Ty.bool]]) (fun J24 => .cons (fun p187 =>
                            .let_ (Op.mk (OpCode.zext 32 64) ((.var p150.2.1), ())) fun v188 =>
                            .let_ (Op.mk (OpCode.mul i64) ((.var v188.1), (.imm 4), ())) fun v189 =>
                            .let_ (Op.mk (OpCode.add i64)
                                ((.var pTmp), (.var v189.1), ())) fun v190 =>
                            .let_ (Op.mk (OpCode.zext 32 64) ((.var v171.1), ())) fun v191 =>
                            .let_ (Op.mk (OpCode.mul i64) ((.var v191.1), (.imm 4), ())) fun v192 =>
                            .let_ (Op.mk (OpCode.add i64)
                                ((.var pTmk), (.var v192.1), ())) fun v193 =>
                            .load i32 (.var v193.1) fun ld194 =>
                            .let_ (Op.mk (OpCode.sub i32) ((.var ld194), (.imm 1), ())) fun v195 =>
                            .let_ (Op.mk (OpCode.shl i32) ((.var v195.1), (.imm 1), ())) fun v196 =>
                            .let_ (Op.mk (OpCode.and i32) ((.var ld158), (.imm 1), ())) fun v197 =>
                            .let_ (Op.mk (OpCode.or i32)
                                ((.var v196.1), (.var v197.1), ())) fun v198 =>
                            .store (t := i32) (.var v198.1) (.var v190.1) <|
                            .let_ (Op.mk (OpCode.add i32)
                                ((.var p150.2.1), (.imm 1), ())) fun v199 =>
                            .jump J21.1
                              ((.var p187.1), (.var p187.2.1), (.var p187.2.2.1), (.var v199.1), ())
                          ) .nil) (fun J24 =>
                          .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var ld181), (.imm 0), ())) fun v187 =>
                          .jnz (.var v187.1) (
                            .let_ (Op.mk (.cmp CmpOp.uge i32)
                                ((.var p150.1), (.var mv), ())) fun v188 =>
                            .jnz (.var v188.1) (
                              .jump J15 ((.var p150.1), (.imm true), (.imm true),
                                  (.var p150.2.1), (.var p150.2.2.1), ())
                            ) (
                              .let_ (Op.mk (OpCode.zext 32 64) ((.var p150.1), ())) fun v189 =>
                              .let_ (Op.mk (OpCode.mul i64)
                                  ((.var v189.1), (.imm 4), ())) fun v190 =>
                              .let_ (Op.mk (OpCode.add i64)
                                  ((.var pWs1), (.var v190.1), ())) fun v191 =>
                              .store (t := i32) (.var v171.1) (.var v191.1) <|
                              .let_ (Op.mk (OpCode.add i32)
                                  ((.var p150.1), (.imm 1), ())) fun v192 =>
                              .let_ (Op.mk (OpCode.zext 32 64) ((.var v171.1), ())) fun v193 =>
                              .let_ (Op.mk (OpCode.mul i64)
                                  ((.var v193.1), (.imm 4), ())) fun v194 =>
                              .let_ (Op.mk (OpCode.add i64)
                                  ((.var pTmk), (.var v194.1), ())) fun v195 =>
                              .store (t := i32) (.var v192.1) (.var v195.1) <|
                              .jump J24.1 ((.var v192.1), (.var done_cur), (.imm false), ())
                            )
                          ) (
                            .jump J24.1 ((.var p150.1), (.var done_cur), (.imm false), ())
                          )
                        )
                      ) .nil) (fun J23 =>
                      .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var v171.1), (.var cv), ())) fun v185 =>
                      .jnz (.var v185.1) (
                        .let_ (Op.mk (OpCode.and i32) ((.var ld158), (.imm 1), ())) fun v186 =>
                        .let_ (Op.mk (.cmp CmpOp.ult i32)
                            ((.var v186.1), (.var pol), ())) fun v187 =>
                        .jnz (.var v187.1) (
                          .jump J15 ((.var p150.1), (.var done_cur), (.imm true),
                              (.var p150.2.1), (.var p150.2.2.1), ())
                        ) (
                          .jump J23.1 (())
                        )
                      ) (
                        .jump J23.1 (())
                      )
                    )
                  ) .nil) (fun J22 =>
                  .let_ (Op.mk (.cmp CmpOp.ne i32) ((.var ld181), (.imm 0), ())) fun v183 =>
                  .jnz (.var v183.1) (
                    .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var ld181), (.var tmk_cv), ())) fun v184 =>
                    .jnz (.var v184.1) (
                      .jump J15 ((.var p150.1), (.var done_cur), (.imm true),
                          (.var p150.2.1), (.var p150.2.2.1), ())
                    ) (
                      .jump J22.1 (())
                    )
                  ) (
                    .jump J22.1 (())
                  )
                )
              )
            ) (
              .jump J21.1 ((.var p150.1), (.var done_cur), (.imm false), (.var p150.2.1), ())
            )
          )
        )
      ) (
        .jump J15
            ((.var p150.1), (.var done_cur), (.imm false), (.var p150.2.1), (.var p150.2.2.1), ())
      )
    ) .nil) (fun J20 =>
    .jump J20.1 ((.var savedNv), (.imm 0), (.imm 0), ())
  )

def occClauseExpr (J14 : Cont [i32, i32, .bool, i64])
    (pHdr pWs1 pTmk pArena pVals pTmp pFlags pKptr : Val i64)
    (mv vlim savedNv nc_cur cr sz cv tmk_cv pol : Val i32) (done_cur : Val .bool)
    (p_next : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[i32, Ty.bool, Ty.bool, i32, i32]]) (fun J15 => .cons (fun p149 =>
      .jnz (.var p149.2.2.1) (
        .group (sig := [[i32]]) (fun J16 => .cons (fun p151 =>
            .let_ (Op.mk (.cmp CmpOp.ugt i32) ((.var p151.1), (.var savedNv), ())) fun v152 =>
            .jnz (.var v152.1) (
              .let_ (Op.mk (OpCode.sub i32) ((.var p151.1), (.imm 1), ())) fun v153 =>
              .let_ (Op.mk (OpCode.zext 32 64) ((.var v153.1), ())) fun v154 =>
              .let_ (Op.mk (OpCode.mul i64) ((.var v154.1), (.imm 4), ())) fun v155 =>
              .let_ (Op.mk (OpCode.add i64) ((.var pWs1), (.var v155.1), ())) fun v156 =>
              .load i32 (.var v156.1) fun ld157 =>
              .let_ (Op.mk (OpCode.zext 32 64) ((.var ld157), ())) fun v158 =>
              .let_ (Op.mk (OpCode.mul i64) ((.var v158.1), (.imm 4), ())) fun v159 =>
              .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v159.1), ())) fun v160 =>
              .store (t := i32) (.imm 0) (.var v160.1) <|
              .jump J16.1 ((.var v153.1), ())
            ) (
              .jump J14 ((.var p151.1), (.var nc_cur), (.var p149.2.1), (.var p_next), ())
            )
          ) .nil) (fun J16 =>
          .jump J16.1 ((.var p149.1), ())
        )
      ) (
        .group (sig := [[i32, i32, Ty.bool]]) (fun J17 => .cons (fun p151 =>
            .jump J14 ((.var p151.1), (.var p151.2.1), (.var p151.2.2.1), (.var p_next), ())
          ) .nil) (fun J17 =>
          .call (as := [i64, i64, i32]) (bs := [.bool]) "full_k6_add_clause"
              ((.var pHdr), (.var pTmp), (.var p149.2.2.2.1), ()) fun c151 =>
          .jnz (.var c151.1) (
            .let_ (Op.mk (OpCode.add i32) ((.var nc_cur), (.imm 1), ())) fun v152 =>
            .group (sig := [[Ty.bool]]) (fun J18 => .cons (fun p154 =>
                .jump J17.1 ((.var p149.1), (.var v152.1), (.var p154.1), ())
              ) .nil) (fun J18 =>
              .let_ (Op.mk (OpCode.zext 32 64) ((.imm 6), ())) fun v154 =>
              .let_ (Op.mk (OpCode.mul i64) ((.var v154.1), (.imm 4), ())) fun v155 =>
              .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v155.1), ())) fun v156 =>
              .load i32 (.var v156.1) fun ld157 =>
              .let_ (Op.mk (.cmp CmpOp.ne i32) ((.var ld157), (.imm 0), ())) fun v158 =>
              .jnz (.var v158.1) (
                .jump J18.1 ((.imm true), ())
              ) (
                .let_ (Op.mk (.cmp CmpOp.uge i32) ((.var p149.1), (.var vlim), ())) fun v159 =>
                .jnz (.var v159.1) (
                  .jump J18.1 ((.imm true), ())
                ) (
                  .jump J18.1 ((.var p149.2.1), ())
                )
              )
            )
          ) (
            .group (sig := [[i32]]) (fun J19 => .cons (fun p153 =>
                .let_ (Op.mk (.cmp CmpOp.ugt i32) ((.var p153.1), (.var savedNv), ())) fun v154 =>
                .jnz (.var v154.1) (
                  .let_ (Op.mk (OpCode.sub i32) ((.var p153.1), (.imm 1), ())) fun v155 =>
                  .let_ (Op.mk (OpCode.zext 32 64) ((.var v155.1), ())) fun v156 =>
                  .let_ (Op.mk (OpCode.mul i64) ((.var v156.1), (.imm 4), ())) fun v157 =>
                  .let_ (Op.mk (OpCode.add i64) ((.var pWs1), (.var v157.1), ())) fun v158 =>
                  .load i32 (.var v158.1) fun ld159 =>
                  .let_ (Op.mk (OpCode.zext 32 64) ((.var ld159), ())) fun v160 =>
                  .let_ (Op.mk (OpCode.mul i64) ((.var v160.1), (.imm 4), ())) fun v161 =>
                  .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v161.1), ())) fun v162 =>
                  .store (t := i32) (.imm 0) (.var v162.1) <|
                  .jump J19.1 ((.var v155.1), ())
                ) (
                  .jump J17.1 ((.var p153.1), (.var nc_cur), (.imm true), ())
                )
              ) .nil) (fun J19 =>
              .jump J19.1 ((.var p149.1), ())
            )
          )
        )
      )
    ) .nil) (fun J15 =>
    occScanExpr J15.1 pWs1 pTmk pArena pVals pTmp pFlags
      mv savedNv cr sz cv tmk_cv pol done_cur
  )

def occPassExpr (J9 : Cont [i32, i32, i32, .bool])
    (pHdr pWs1 pTmk pWvec pWstk pArena pVals pTmp pFlags pKptr : Val i64)
    (mv vlim maxOrig nv_in nc_in : Val i32) (done_in : Val .bool)
    (cv tmk_cv qi_next : Val i32) : Expr Val Cont [i64] :=
  .group (sig := [[i32, i32, Ty.bool, i32]]) (fun J12 => .cons (fun p86 =>
      .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p86.2.2.2.1), (.imm 2), ())) fun v87 =>
      .jnz (.var v87.1) (
        .jnz (.var p86.2.2.1) (
          .jump J9 ((.var p86.1), (.var p86.2.1), (.var qi_next), (.var p86.2.2.1), ())
        ) (
          .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var p86.2.1), (.var maxOrig), ())) fun v88 =>
          .jnz (.var v88.1) (
            .let_ (Op.mk (OpCode.shl i32) ((.var cv), (.imm 1), ())) fun v89 =>
            .let_ (Op.mk (OpCode.or i32) ((.var v89.1), (.var p86.2.2.2.1), ())) fun v90 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var v90.1), ())) fun v91 =>
            .let_ (Op.mk (OpCode.sext 32 64) ((.imm 1), ())) fun v92 =>
            .let_ (Op.mk (OpCode.shl i64) ((.var v91.1), (.var v92.1), ())) fun v93 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v93.1), (.imm 4), ())) fun v94 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pWvec), (.var v94.1), ())) fun v95 =>
            .load i32 (.var v95.1) fun ld96 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var ld96), ())) fun v97 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var v90.1), ())) fun v98 =>
            .let_ (Op.mk (OpCode.sext 32 64) ((.imm 1), ())) fun v99 =>
            .let_ (Op.mk (OpCode.shl i64) ((.var v98.1), (.var v99.1), ())) fun v100 =>
            .let_ (Op.mk (OpCode.add i64) ((.var v100.1), (.imm 1), ())) fun v101 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v101.1), (.imm 4), ())) fun v102 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pWvec), (.var v102.1), ())) fun v103 =>
            .load i32 (.var v103.1) fun ld104 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var ld104), ())) fun v105 =>
            .let_ (Op.mk (OpCode.add i64) ((.var v97.1), (.var v105.1), ())) fun v106 =>
            .group (sig := [[i32, i32, Ty.bool, i64]]) (fun J13 => .cons (fun p108 =>
                .let_ (Op.mk (OpCode.add i32) ((.var p86.2.2.2.1), (.imm 1), ())) fun v109 =>
                .jump J12.1 ((.var p108.1), (.var p108.2.1), (.var p108.2.2.1), (.var v109.1), ())
              ) .nil) (fun J13 =>
              .group (sig := [[i32, i32, Ty.bool, i64]]) (fun J14 => .cons (fun p109 =>
                  .let_ (Op.mk (.cmp CmpOp.ult i64)
                      ((.var p109.2.2.2.1), (.var v106.1), ())) fun v110 =>
                  .jnz (.var v110.1) (
                    .jnz (.var p109.2.2.1) (
                      .jump J13.1 ((.var p109.1), (.var p109.2.1),
                          (.var p109.2.2.1), (.var p109.2.2.2.1), ())
                    ) (
                      .let_ (Op.mk (.cmp CmpOp.ult i32)
                          ((.var p109.2.1), (.var maxOrig), ())) fun v111 =>
                      .jnz (.var v111.1) (
                        .let_ (Op.mk (OpCode.mul i64)
                            ((.var p109.2.2.2.1), (.imm 4), ())) fun v112 =>
                        .let_ (Op.mk (OpCode.add i64) ((.var pWstk), (.var v112.1), ())) fun v113 =>
                        .load i32 (.var v113.1) fun ld114 =>
                        .let_ (Op.mk (OpCode.add i64)
                            ((.var p109.2.2.2.1), (.imm 1), ())) fun v115 =>
                        .let_ (Op.mk (OpCode.and i32)
                            ((.var ld114), (.imm 2147483648), ())) fun v116 =>
                        .let_ (Op.mk (.cmp CmpOp.ne i32) ((.var v116.1), (.imm 0), ())) fun v117 =>
                        .jnz (.var v117.1) (
                          .jump J14.1
                              ((.var p109.1), (.var p109.2.1), (.var p109.2.2.1), (.var v115.1), ())
                        ) (
                          .let_ (Op.mk (.cmp CmpOp.uge i64)
                              ((.var v115.1), (.var v106.1), ())) fun v118 =>
                          .jnz (.var v118.1) (
                            .jump J13.1 ((.var p109.1), (.var p109.2.1),
                                (.var p109.2.2.1), (.var v115.1), ())
                          ) (
                            .let_ (Op.mk (OpCode.mul i64) ((.var v115.1), (.imm 4), ())) fun v119 =>
                            .let_ (Op.mk (OpCode.add i64)
                                ((.var pWstk), (.var v119.1), ())) fun v120 =>
                            .load i32 (.var v120.1) fun ld121 =>
                            .let_ (Op.mk (OpCode.add i64) ((.var v115.1), (.imm 1), ())) fun v122 =>
                            .let_ (Op.mk (OpCode.zext 32 64) ((.var ld121), ())) fun v123 =>
                            .let_ (Op.mk (OpCode.add i64) ((.var v123.1), (.imm 3), ())) fun v124 =>
                            .let_ (Op.mk (OpCode.add i64) ((.var pHdr), (.imm 48), ())) fun v125 =>
                            .load i64 (.var v125.1) fun ld126 =>
                            .let_ (Op.mk (.cmp CmpOp.ugt i64)
                                ((.var v124.1), (.var ld126), ())) fun v127 =>
                            .jnz (.var v127.1) (
                              .jump J14.1 ((.var p109.1), (.var p109.2.1),
                                  (.var p109.2.2.1), (.var v122.1), ())
                            ) (
                              .let_ (Op.mk (OpCode.zext 32 64) ((.var ld121), ())) fun v128 =>
                              .let_ (Op.mk (OpCode.add i64)
                                  ((.var v128.1), (.imm 2), ())) fun v129 =>
                              .let_ (Op.mk (OpCode.mul i64)
                                  ((.var v129.1), (.imm 4), ())) fun v130 =>
                              .let_ (Op.mk (OpCode.add i64)
                                  ((.var pArena), (.var v130.1), ())) fun v131 =>
                              .load i32 (.var v131.1) fun ld132 =>
                              .let_ (Op.mk (OpCode.zext 32 64) ((.var ld121), ())) fun v133 =>
                              .let_ (Op.mk (OpCode.mul i64)
                                  ((.var v133.1), (.imm 4), ())) fun v134 =>
                              .let_ (Op.mk (OpCode.add i64)
                                  ((.var pArena), (.var v134.1), ())) fun v135 =>
                              .load i32 (.var v135.1) fun ld136 =>
                              .let_ (Op.mk (OpCode.or i32)
                                  ((.imm 524288), (.imm 4194304), ())) fun v137 =>
                              .let_ (Op.mk (OpCode.and i32)
                                  ((.var ld136), (.var v137.1), ())) fun v138 =>
                              .let_ (Op.mk (.cmp CmpOp.ne i32)
                                  ((.var v138.1), (.imm 0), ())) fun v139 =>
                              .jnz (.var v139.1) (
                                .jump J14.1 ((.var p109.1), (.var p109.2.1),
                                    (.var p109.2.2.1), (.var v122.1), ())
                              ) (
                                .let_ (Op.mk (.cmp CmpOp.ult i32)
                                    ((.var ld132), (.imm 3), ())) fun v140 =>
                                .jnz (.var v140.1) (
                                  .jump J14.1 ((.var p109.1), (.var p109.2.1),
                                      (.var p109.2.2.1), (.var v122.1), ())
                                ) (
                                  .let_ (Op.mk (OpCode.zext 32 64) ((.var ld121), ())) fun v141 =>
                                  .let_ (Op.mk (OpCode.add i64)
                                      ((.var v141.1), (.imm 3), ())) fun v142 =>
                                  .let_ (Op.mk (OpCode.zext 32 64) ((.var ld132), ())) fun v143 =>
                                  .let_ (Op.mk (OpCode.add i64)
                                      ((.var v142.1), (.var v143.1), ())) fun v144 =>
                                  .let_ (Op.mk (OpCode.add i64)
                                      ((.var pHdr), (.imm 48), ())) fun v145 =>
                                  .load i64 (.var v145.1) fun ld146 =>
                                  .let_ (Op.mk (.cmp CmpOp.ugt i64)
                                      ((.var v144.1), (.var ld146), ())) fun v147 =>
                                  .jnz (.var v147.1) (
                                    .jump J14.1 ((.var p109.1), (.var p109.2.1),
                                        (.var p109.2.2.1), (.var v122.1), ())
                                  ) ( occClauseExpr J14.1 pHdr pWs1 pTmk pArena pVals pTmp pFlags
                                      pKptr mv vlim p109.1 p109.2.1 ld121 ld132 cv tmk_cv
                                      p86.2.2.2.1 p109.2.2.1 v122.1
                                  )
                                )
                              )
                            )
                          )
                        )
                      ) (
                        .jump J13.1 ((.var p109.1), (.var p109.2.1),
                            (.var p109.2.2.1), (.var p109.2.2.2.1), ())
                      )
                    )
                  ) (
                    .jump J13.1
                        ((.var p109.1), (.var p109.2.1), (.var p109.2.2.1), (.var p109.2.2.2.1), ())
                  )
                ) .nil) (fun J14 =>
                .jump J14.1 ((.var p86.1), (.var p86.2.1), (.var p86.2.2.1), (.var v97.1), ())
              )
            )
          ) (
            .jump J9 ((.var p86.1), (.var p86.2.1), (.var qi_next), (.var p86.2.2.1), ())
          )
        )
      ) (
        .jump J9 ((.var p86.1), (.var p86.2.1), (.var qi_next), (.var p86.2.2.1), ())
      )
    ) .nil) (fun J12 =>
    .jump J12.1 ((.var nv_in), (.var nc_in), (.var done_in), (.imm 0), ())
  )

end

section Helpers

private theorem s13_arena_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.arena = s.core.arena :=
  congrArg (fun t => t.core.arena) hag

private theorem s13_vals_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.vals = s.core.vals :=
  congrArg (fun t => t.core.vals) hag

private theorem s13_cur_vars_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.cur_vars = s.core.cur_vars :=
  congrArg (fun t => t.core.cur_vars) hag

private theorem s13_arena_len_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.arena_len = s.core.arena_len :=
  congrArg (fun t => t.core.arena_len) hag

private theorem s13_wstk_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.wstk = s.core.wstk :=
  congrArg (fun t => t.core.wstk) hag

private theorem s13_wvec_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.wvec = s.core.wvec :=
  congrArg (fun t => t.core.wvec) hag

private theorem s13_sext8_255 {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) {l : Nat}
    (hlt : l < 2 * s.core.cur_vars)
    (hsgt : (0#32).slt (BitVec.signExtend 32 (s.core.vals[l]?.getD 0#8)) = false)
    (hne0 : s.core.vals[l]?.getD 0#8 ≠ 0#8) :
    s.core.vals[l]?.getD 0#8 = 255#8 := by
  rcases hw.vals_domain l hlt with hv | hv | hv <;> simp [hv] at hsgt hne0 ⊢

private theorem s13_tmk_at (st : FullState) (lit_k : BitVec 32)
    (hltm : lit_k.toNat / 2 < st.scratch.tarjan_mark.length) :
    (lit_k >>> 1#32).toNat = lit_k.toNat / 2 ∧
      (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat = lit_k.toNat / 2 ∧
      st.scratch.tarjan_mark[(BitVec.setWidth 64 (lit_k >>> 1#32)).toNat] =
        st.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 := by
  have hv : (lit_k >>> 1#32).toNat = lit_k.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt64 : lit_k.toNat / 2 < 2 ^ 64 := by have := lit_k.isLt; omega
  have hv64 : (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat = lit_k.toNat / 2 := by
    rw [BitVec.toNat_setWidth, hv, Nat.mod_eq_of_lt hlt64]
  refine ⟨hv, hv64, ?_⟩
  have hq : st.scratch.tarjan_mark[(BitVec.setWidth 64 (lit_k >>> 1#32)).toNat]? =
      st.scratch.tarjan_mark[lit_k.toNat / 2]? := by rw [hv64]
  rw [List.getElem?_eq_getElem (by rw [hv64]; exact hltm), List.getElem?_eq_getElem hltm] at hq
  injection hq with heq; rw [heq, List.getElem?_eq_getElem hltm, Option.getD_some]

private theorem s13_scan_tmp_step {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st_k st_u : FullState}
    {cv qi_l savedNv nv_k nv_u cr sz cnt idx lit_k : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {nc_w ilv : Nat}
    (hsb : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
      nv_k.toNat nc_w cnt.toNat idx.toNat st_k)
    (hsu : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_u.toNat nc_w st_u)
    (htmp_eq : st_u.core.tmp = st_k.core.tmp)
    (hws_eq : ∀ j, j < nv_k.toNat → st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?)
    (hnv_le : nv_k.toNat ≤ nv_u.toNat)
    (hidx_lt : idx.toNat < sz.toNat)
    (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcnt_le : cnt.toNat ≤ idx.toNat)
    (hlit_at : (s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat = lit_k.toNat)
    (hilv_lt : ilv < nv_u.toNat)
    (hilv_ws : (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2)
    (hilv_tmk : st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 = BitVec.ofNat 32 (ilv + 1))
    (hnodup : (List.map (fun x => x / 2) (fullArenaClauseLits s cr.toNat)).Nodup)
    (har_len : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat) :
    let new_l := (st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 - 1#32) <<< 1 |||
      lit_k &&& 1#32
    let st_u' : FullState :=
      { core := { st_u.core with tmp := st_u.core.tmp.set cnt.toNat new_l }
        scratch := st_u.scratch }
    (cnt + 1#32).toNat = cnt.toNat + 1 ∧ (idx + 1#32).toNat = idx.toNat + 1 ∧
      Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
        nv_u.toNat nc_w (cnt + 1#32).toNat (idx + 1#32).toNat st_u' := by
  intro new_l st_u'
  have hnv_max : nv_u.toNat ≤ L.maxV := Nat.le_trans hsu.hcone.nv_le_mvC hsu.hcone.mvC_leMax
  have hku := fid_cone_k_unassigned_step hsu.hlen htmp_eq hws_eq hnv_le
    hnv_max hidx_lt hsz_cv (by rw [← s13_cur_vars_eq hsb.hag]; exact hsb.hlen.core_ok.cur_vars_le)
    hcnt_le hlit_at hilv_lt hilv_ws hilv_tmk hsb.hlts hsb.hcov hsb.hvars hsb.hnd hnodup
    har_len hsz_eq hsu.hcone
  have hku1 : (cnt + 1#32).toNat = cnt.toNat + 1 := hku.1
  have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := by
    have : idx.toNat + 1 < 2 ^ 32 := by omega
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]
  refine ⟨hku1, hidx1, ?_⟩
  have hlen' : FullState.LengthsOk c st_u' := hku.2.1
  have hag' : AgreesExcept step13ConeMask s st_u' := by
    have h0 := hsu.hag
    simp only [AgreesExcept, step13ConeMask] at h0 ⊢; exact h0
  have hgu' : S13GuOk L s st_u' := hsu.hgu; have hc0 := hsu.hcone
  have hcone' : FidConeInv F_cur L mvC st_u' nv_u.toNat nc_w :=
    ⟨hc0.nv_ge1, hc0.nv_le_mvC, hc0.mvC_leMax, hc0.nv_le_cv, hc0.nc_le, hc0.scr_len,
      hc0.k6_inv, hc0.k6_sync, hc0.k6_nv, hc0.k6_lvl, hc0.k6_na, hc0.k6_bdd,
      hc0.k6_trl_bdd, hc0.fwd, hc0.rev⟩
  refine ⟨⟨⟨hlen', hag', hgu', hcone', hsu.htmk, hsu.hwk⟩,
    hsu.hsav_le, hsu.hscr, hsu.hws⟩, hku.2.2.1, ?_, hku.2.2.2.2.1, hku.2.2.2.2.2⟩
  intro i hi
  exact hku.2.2.2.1 i hi

private theorem s13_scan_skip_step {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st_k : FullState}
    {cv qi_l savedNv nv_k cr sz cnt idx : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {nc_w : Nat}
    (hsb : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
      nv_k.toNat nc_w cnt.toNat idx.toNat st_k)
    (hidx_lt : idx.toNat < sz.toNat)
    (hfal : s.core.vals[(s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat]?.getD 0#8 =
      255#8) :
    (idx + 1#32).toNat = idx.toNat + 1 ∧
      Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
        nv_k.toNat nc_w cnt.toNat (idx + 1#32).toNat st_k := by
  have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := by
    have : idx.toNat + 1 < 2 ^ 32 := by omega
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]
  refine ⟨hidx1, ?_⟩
  refine ⟨hsb.toStep13ConeSavedBase, hsb.hlts, ?_, ?_, hsb.hnd⟩
  · intro i hi
    have hi' : i < idx.toNat + 1 := by omega
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hlt | rfl
    · exact hsb.hcov i hlt
    · exact Or.inl hfal
  · intro j hj
    rcases hsb.hvars j hj with ⟨p, hp, hpe⟩
    exact ⟨p, by omega, hpe⟩

end Helpers

public section

theorem step13_cone_rollback_loop_wp
    {Γ : Env} {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s st_0 : FullState} {scr0 ws0 : List (BitVec 32)}
    {savedNv nv0 cv qi_l : BitVec 32} {nc_w : Nat} {m : Mem 64}
    (pWs1 pTmk : Val i64) (hpWs1 : pWs1 = c.pWorkStk1) (hpTmk : pTmk = c.pTarjanMark)
    (exitExpr : Val i32 → Expr Val Cont [i64])
    (hsav : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv0.toNat nc_w st_0)
    (hge1 : 1 ≤ savedNv.toNat) (hqi_lt : qi_l.toNat < savedNv.toNat)
    (hbdd : K6LitsBounded savedNv.toNat (k6StateOfScratch L scr0))
    (htrl : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * savedNv.toNat)
    (hm : (FullMem c st_0 ⋆ R) m)
    (hExit : ∀ (st_r : FullState) (m' : Mem 64),
      Step13ConeBase F_cur L mvC c s cv qi_l savedNv.toNat nc_w st_r →
      st_r.scratch.scratch_buf = scr0 →
      (∀ j, j < savedNv.toNat → st_r.scratch.work_stk1[j]? = ws0[j]?) →
      (FullMem c st_r ⋆ R) m' →
      wp Γ Q X (exitExpr savedNv) m') :
    wp Γ Q X (.group (sig := [[i32]]) (fun J => .cons
        (fun p => .let_ (Op.mk (.cmp CmpOp.ugt i32) ((.var p.1), (.var savedNv), ())) fun v1 =>
          .jnz (.var v1.1) ( .let_ (Op.mk (OpCode.sub i32) ((.var p.1), (.imm 1), ())) fun v2 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var v2.1), ())) fun v3 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v3.1), (.imm 4), ())) fun v4 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pWs1), (.var v4.1), ())) fun v5 =>
            .load i32 (.var v5.1) fun ld =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var ld), ())) fun v6 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v6.1), (.imm 4), ())) fun v7 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v7.1), ())) fun v8 =>
            .store (t := i32) (.imm 0) (.var v8.1) <|
            .jump J.1 ((.var v2.1), ())
          ) ( exitExpr p.1
          )
        )
        .nil) (fun J => .jump J.1 ((.var nv0), ()))) m := by
  subst hpWs1 hpTmk
  let α := BitVec 32 × FullState
  let Inv : α → Mem 64 → Prop := fun ⟨nv_r, st_r⟩ m' =>
    Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_r.toNat nc_w st_r ∧
    (FullMem c st_r ⋆ R) m'
  refine wp_while_state (fun p => (p.1, ())) (fun p => p.1.toNat - savedNv.toNat) Inv ?_ ?_
  · intro J hJ
    dsimp only; rw [wp_jump]; exact hJ (nv0, st_0) m ⟨hsav, hm⟩
  · intro J ⟨nv_r, st_r⟩ m' ⟨hrb, hm'⟩ hIH
    dsimp [Blocks.get, Member.here]; c0_hstraight
    try clear hc
    m6_split
    · try intro hc
      have hlt_rb : savedNv.toNat < nv_r.toNat := hc
      have hpop := step13_cone_pop_var_ok hrb.hlen hrb.hag hrb.hgu hrb.hcone hge1 hlt_rb
        hrb.hscr hbdd htrl hrb.hws
      rcases hpop with ⟨hnv', hvr_lt, hlen', hag', hgu', hcone', hscr', hws'⟩
      have hidx_ws : (BitVec.setWidth 64 (nv_r - 1#32)).toNat < st_r.scratch.work_stk1.length := by
        have h1 : (BitVec.setWidth 64 (nv_r - 1#32)).toNat = (nv_r - 1#32).toNat := by simp
        rw [h1, hnv']
        have hle := hrb.hcone.nv_le_mvC; have hmv := hrb.hcone.mvC_leMax
        have hcv := hrb.hcone.nv_le_cv; have hcv_le := hrb.hlen.core_ok.cur_vars_le
        have hws_len := hrb.hlen.scratch_ok.work_stk1_len
        omega
      have hvr_eq : st_r.scratch.work_stk1[(BitVec.setWidth 64 (nv_r - 1#32)).toNat] =
          st_r.scratch.work_stk1[(nv_r - 1#32).toNat]?.getD 0#32 := by
        have h1 : (BitVec.setWidth 64 (nv_r - 1#32)).toNat = (nv_r - 1#32).toNat := by simp
        have hlen1 : (nv_r - 1#32).toNat < st_r.scratch.work_stk1.length := by
          simpa [h1] using hidx_ws
        simp only [h1, List.getElem?_eq_getElem hlen1, Option.getD_some]
      have htmk_len : (BitVec.setWidth 64
            st_r.scratch.work_stk1[(BitVec.setWidth 64 (nv_r - 1#32)).toNat]).toNat <
              st_r.scratch.tarjan_mark.length := by
        rw [BitVec.toNat_setWidth]
        have h32 :
            st_r.scratch.work_stk1[(BitVec.setWidth 64 (nv_r - 1#32)).toNat].toNat < 2 ^ 64 :=
          Nat.lt_trans (BitVec.isLt _) (by decide)
        rw [Nat.mod_eq_of_lt h32, hvr_eq]; exact hvr_lt
      c0_hstraight
      try refine head_wp_load rfl (c0_load_full_work_stk1 hidx_ws hm') ?_
      c0_hstraight
      refine head_wp_store rfl rfl (c0_store_full_tarjan_mark 0#32 htmk_len hm') fun _ hm_s => ?_
      c0_hstraight
      try dsimp only
      try rw [wp_jump]
      have h32 : st_r.scratch.work_stk1[(BitVec.setWidth 64 (nv_r - 1#32)).toNat].toNat < 2 ^ 64 :=
        Nat.lt_trans (BitVec.isLt _) (by decide)
      have hidx_eq : (BitVec.setWidth 64
            st_r.scratch.work_stk1[(BitVec.setWidth 64 (nv_r - 1#32)).toNat]).toNat =
          (st_r.scratch.work_stk1[(nv_r - 1#32).toNat]?.getD 0#32).toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32, hvr_eq]
      have hsav' : savedNv.toNat ≤ (nv_r - 1#32).toNat := by rw [hnv']; omega
      have htmk' : (st_r.scratch.tarjan_mark.set
            (st_r.scratch.work_stk1[(nv_r - 1#32).toNat]?.getD 0#32).toNat
            0#32)[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1) := by
        have hne : (st_r.scratch.work_stk1[(nv_r - 1#32).toNat]?.getD 0#32).toNat ≠ cv.toNat := by
          intro heq
          have hlt1 : (nv_r - 1#32).toNat < nv_r.toNat := by rw [hnv']; omega
          have hfwd := hrb.hcone.fwd (nv_r - 1#32).toNat hlt1
          rw [heq, hrb.htmk] at hfwd
          have hqi1 : qi_l.toNat + 1 = nv_r.toNat := by
            have hto := congrArg BitVec.toNat hfwd.2
            simp only [BitVec.toNat_ofNat] at hto; rw [hnv'] at hto
            have hb1 : qi_l.toNat + 1 < 2 ^ 32 := by omega
            have hb2 : nv_r.toNat - 1 + 1 < 2 ^ 32 := by omega
            rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at hto; omega
          omega
        rw [List.getElem?_set_ne (by omega), hrb.htmk]
      rw [hidx_eq] at hm_s; exact hIH (nv_r - 1#32, _) _ (by dsimp only; rw [hnv']; omega)
        ⟨⟨⟨hlen', hag', hgu', hcone', htmk', hrb.hwk⟩, hsav', hrb.hscr, hws'⟩, hm_s⟩
    · try intro hc
      have hnv_eq : nv_r = savedNv := BitVec.eq_of_toNat_eq (by have := hrb.hsav_le; omega)
      subst hnv_eq; exact hExit st_r m' hrb.toStep13ConeBase hrb.hscr hrb.hws hm'

theorem step13_cone_occ_scan_wp
    {Γ : Env} {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s st_0 : FullState} {ws0 scr0 : List (BitVec 32)}
    {savedNv cr sz cv qi_l tmk_cv pol : BitVec 32} {done_cur : Bool}
    {nc_cur : BitVec 32} {m : Mem 64}
    (J15 : Cont [i32, .bool, .bool, i32, i32])
    (pWs1 pTmk pArena pVals pTmp pFlags : Val i64)
    (hpWs1 : pWs1 = c.pWorkStk1) (hpTmk : pTmk = c.pTarjanMark)
    (hpArena : pArena = c.pArena) (hpVals : pVals = c.pVals)
    (hpTmp : pTmp = c.pTmp) (hpFlags : pFlags = c.pFlags)
    (hw : FullWitnessInv c F0 F_cur s.core)
    (hnodup_a : FullArenaVarsNodup s)
    (hlen_s : FullState.LengthsOk c s)
    (hsav : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0
      savedNv.toNat nc_cur.toNat st_0)
    (hsav_mvC : savedNv.toNat ≤ mvC.toNat)
    (hqi_lt : qi_l.toNat < savedNv.toNat)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hgarb : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (har_len : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hm : (FullMem c st_0 ⋆ R) m)
    (hJ15 : ∀ (nv_k cnt_k idx_k : BitVec 32) (done_k abort_k : Bool)
        (st_k : FullState) (m' : Mem 64),
      Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_k.toNat nc_cur.toNat st_k →
      nv_k.toNat ≤ mvC.toNat →
      (abort_k = false → done_k = done_cur ∧ idx_k = sz ∧ cnt_k.toNat ≤ nv_k.toNat ∧
        cnt_k.toNat ≤ sz.toNat ∧
        Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
          nv_k.toNat nc_cur.toNat cnt_k.toNat sz.toNat st_k) →
      (FullMem c st_k ⋆ R) m' →
      J15 (nv_k, done_k, abort_k, cnt_k, idx_k, ()) m') :
    wp Γ Q X (occScanExpr J15 pWs1 pTmk pArena pVals pTmp pFlags
        mvC savedNv cr sz cv tmk_cv pol done_cur) m := by
  subst hpWs1 hpTmk hpArena hpVals hpTmp hpFlags
  let α := BitVec 32 × BitVec 32 × BitVec 32 × FullState
  let Inv : α → Mem 64 → Prop := fun ⟨nv_k, cnt, idx, st_k⟩ m' =>
    Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
      nv_k.toNat nc_cur.toNat cnt.toNat idx.toNat st_k ∧
    idx.toNat ≤ sz.toNat ∧
    cnt.toNat ≤ idx.toNat ∧
    nv_k.toNat ≤ mvC.toNat ∧
    (FullMem c st_k ⋆ R) m'
  refine wp_while_state (fun p => (p.1, p.2.1, p.2.2.1, ()))
    (fun p => sz.toNat - p.2.2.1.toNat) Inv ?_ ?_
  · intro J20 hJ20
    dsimp only; rw [wp_jump]; exact hJ20 (savedNv, 0#32, 0#32, st_0) m
      ⟨⟨hsav, by intro j hj; simp at hj, by intro i hi; simp at hi,
        by intro j hj; simp at hj, by intro j1 j2 h1; simp at h1⟩,
        by simp, by simp, hsav_mvC, hm⟩
  · intro J20 ⟨nv_k, cnt, idx, st_k⟩ m' ⟨hsb, hidx_le, hcnt_le, hnv_mvC, hm'⟩ hIH
    dsimp [Blocks.get, Member.here]; c0_hstraight
    try clear hc
    m6_split
    · try intro hc
      have hidx_lt : idx.toNat < sz.toNat := hc; have har_eq := s13_arena_eq hsb.hag
      have hvals_eq := s13_vals_eq hsb.hag; have hcv_eq := s13_cur_vars_eq hsb.hag
      have h1 : (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 idx).toNat =
          cr.toNat + 3 + idx.toNat := by
        have := cr.isLt; have := idx.isLt
        have hlt64 : cr.toNat + 3 + idx.toNat < 2 ^ 64 := by omega
        have hlt64a : cr.toNat + 3 < 2 ^ 64 := by omega
        simp [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt64a,
          Nat.mod_eq_of_lt hlt64]
      have har_idx : (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 idx).toNat <
          st_k.core.arena.length := by
        rw [h1, har_eq]; omega
      let lit_k := st_k.core.arena[(BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 idx).toNat]

      have hlit_at : (s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat = lit_k.toNat := by
        have hget_a :
            st_k.core.arena[(BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 idx).toNat]? =
              s.core.arena[cr.toNat + 3 + idx.toNat]? := by
          rw [har_eq, h1]
        rw [List.getElem?_eq_getElem har_idx] at hget_a; dsimp [lit_k]; rw [← hget_a]; rfl
      have hlit_mem : lit_k.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat := by
        have har_s : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]?.getD 0#32).toNat ≤
            s.core.arena.length := by
          change cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤ s.core.arena.length
          rw [← hsz_eq]; exact har_len
        rw [m6_arenaClauseLitsCore_mem_iff har_s]; refine ⟨idx.toNat, ?_, hlit_at⟩
        change idx.toNat < fullArenaClauseSizeCore s.core cr.toNat
        rw [← hsz_eq]; exact hidx_lt
      have hlit_lt : lit_k.toNat < 2 * s.core.cur_vars :=
        hw.arena.lits_lt cr.toNat hcr_ref hgarb lit_k.toNat hlit_mem
      have hvals_idx : (BitVec.setWidth 64 lit_k).toNat < st_k.core.vals.length := by
        simp [BitVec.toNat_setWidth]
        have := hsb.hlen.core_ok.vals_len; have := hlen_s.core_ok.cur_vars_le
        omega
      c0_hstraight
      try (refine head_wp_load rfl (c0_load_full_arena har_idx hm') ?_; c0_hstraight)
      try clear hc
      dsimp only; rw [wp_jnz]; refine ⟨fun hc => ?_, fun hc => ?_⟩
      · rw [wp_jump]
        exact hJ15 nv_k cnt idx done_cur true st_k m' hsb.toStep13ConeSavedBase hnv_mvC
          (by intro h; simp at h) hm'
      · have hsgt_f : (0#32).slt (BitVec.signExtend 32
            st_k.core.vals[(BitVec.setWidth 64 lit_k).toNat]) = false := hc
        refine wp_join_state (ts := [i32, Ty.bool, Ty.bool, i32])
          (α := BitVec 32 × Bool × Bool × BitVec 32 × FullState)
          (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, ()))
          (fun ⟨nv', d', ab', cnt', st'⟩ m'' =>
            d' = done_cur ∧ ab' = false ∧ cnt'.toNat ≤ idx.toNat + 1 ∧
            idx.toNat + 1 ≤ sz.toNat ∧ nv'.toNat ≤ mvC.toNat ∧
            Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
              nv'.toNat nc_cur.toNat cnt'.toNat (idx.toNat + 1) st' ∧
            (FullMem c st' ⋆ R) m'')
          ?_ ?_
        · intro J21 ⟨nv', d', ab', cnt', st'⟩ m'' ⟨hd', hab', hcnt', hidx1, hnv', hsb', hm''⟩
          dsimp [Blocks.get, Member.here]; c0_hstraight
          have hidx_eq : (idx + 1#32).toNat = idx.toNat + 1 := by
            have : idx.toNat + 1 < 2 ^ 32 := by omega
            simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]
          try dsimp only; rw [wp_jump]
          exact hIH (nv', cnt', idx + 1#32, st') m'' (by dsimp only; rw [hidx_eq]; omega)
            ⟨by simpa [hidx_eq] using hsb', by omega, by omega, hnv', hm''⟩
        · intro J21 hJ21
          c0_hstraight; (try clear hc); m6_split
          · have hv_lt : (lit_k >>> 1#32).toNat < s.core.cur_vars := by
              simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
            have hflags_idx : (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat <
                st_k.core.flags.length := by
              have := hsb.hlen.core_ok.flags_len; have := hlen_s.core_ok.cur_vars_le
              simp [BitVec.toNat_setWidth]; omega
            c0_hstraight
            try (refine head_wp_load rfl (c0_load_full_flags hflags_idx hm') ?_; c0_hstraight)
            try clear hc
            m6_split
            · rw [wp_jump]
              exact hJ15 nv_k cnt idx done_cur true st_k m' hsb.toStep13ConeSavedBase hnv_mvC
                (by intro h; simp at h) hm'
            · have htmk_idx : (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat <
                  st_k.scratch.tarjan_mark.length := by
                have := hsb.hlen.scratch_ok.tarjan_mark_len; have := hlen_s.core_ok.cur_vars_le
                simp [BitVec.toNat_setWidth]; omega
              have hltm_k : lit_k.toNat / 2 < st_k.scratch.tarjan_mark.length := by
                have := hsb.hlen.scratch_ok.tarjan_mark_len; have := hlen_s.core_ok.cur_vars_le
                omega
              have hta_k := s13_tmk_at st_k lit_k hltm_k
              c0_hstraight
              try refine head_wp_load rfl (c0_load_full_tarjan_mark htmk_idx hm') ?_
              c0_hstraight; refine wp_join_state (fun (_ : Unit) => ()) (fun _ m2 => m2 = m') ?_ ?_
              · intro J22 () m2 hm2
                dsimp [Blocks.get, Member.here]
                refine wp_join_state (fun (_ : Unit) => ()) (fun _ m3 => m3 = m2) ?_ ?_
                · intro J23 () m3 hm3
                  dsimp [Blocks.get, Member.here]; refine wp_join_state
                    (fun (p : BitVec 32 × Bool × Bool × FullState) => (p.1, p.2.1, p.2.2.1, ()))
                    (fun ⟨nv_u, d_u, ab_u, st_u⟩ m'' => d_u = done_cur ∧ ab_u = false ∧
                      nv_k.toNat ≤ nv_u.toNat ∧ nv_u.toNat ≤ mvC.toNat ∧
                      Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0
                        nv_u.toNat nc_cur.toNat st_u ∧ st_u.core.tmp = st_k.core.tmp ∧
                      (∀ j, j < nv_k.toNat →
                        st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?) ∧
                      (∃ ilv, ilv < nv_u.toNat ∧
                        (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2 ∧
                        st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 =
                          BitVec.ofNat 32 (ilv + 1)) ∧ (FullMem c st_u ⋆ R) m'') ?_ ?_
                  · intro J24 ⟨nv_u, d_u, ab_u, st_u⟩ m''
                      ⟨hd_u, hab_u, hnv_le, hnv_u_mvC, hsu, htmp_eq, hws_eq,
                        ⟨ilv, hilv_lt, hilv_ws, hilv_tmk⟩, hm_u⟩
                    dsimp [Blocks.get, Member.here]
                    have htmp_idx : (BitVec.setWidth 64 cnt).toNat < st_u.core.tmp.length := by
                      have := hsu.hlen.core_ok.tmp_len_arr; have := hlen_s.core_ok.cur_vars_le
                      simp [BitVec.toNat_setWidth]; omega
                    have hltm_u : lit_k.toNat / 2 < st_u.scratch.tarjan_mark.length := by
                      have := hsu.hlen.scratch_ok.tarjan_mark_len
                      have := hlen_s.core_ok.cur_vars_le; omega
                    have hta_u := s13_tmk_at st_u lit_k hltm_u
                    have htmk_u_idx : (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat <
                        st_u.scratch.tarjan_mark.length := by rw [hta_u.2.1]; exact hltm_u
                    c0_hstraight
                    refine head_wp_load rfl (c0_load_full_tarjan_mark htmk_u_idx hm_u) ?_
                    c0_hstraight; refine head_wp_store rfl rfl (c0_store_full_tmp _ htmp_idx hm_u)
                      fun _ hm_st => ?_
                    c0_hstraight
                    have hscan' := s13_scan_tmp_step hsb hsu htmp_eq hws_eq hnv_le hidx_lt
                      hsz_cv hcnt_le hlit_at hilv_lt hilv_ws hilv_tmk
                      (hnodup_a cr.toNat hcr_ref hgarb) har_len hsz_eq
                    have hcnt64 : (BitVec.setWidth 64 cnt).toNat = cnt.toNat := by simp
                    have h1bv : (1#32 : BitVec 32) = BitVec.ofNat 32 1 := rfl
                    try dsimp only
                    try rw [wp_jump]
                    rw [hcnt64, hta_u.2.2] at hm_st; exact hJ21 (nv_u, d_u, ab_u, cnt + 1#32, _) _
                      ⟨hd_u, hab_u, by rw [hscan'.1]; omega, by omega, hnv_u_mvC,
                        by rw [← hscan'.2.1]; exact hscan'.2.2,
                        by simpa [h1bv, lit_k] using hm_st⟩
                  · intro J24 hJ24
                    c0_hstraight; (try clear hc); m6_split
                    · try intro hc
                      have htmk_eq0 : st_k.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 =
                          0#32 := by rw [← hta_k.2.2]; exact hc
                      c0_hstraight; (try clear hc); m6_split
                      · rw [wp_jump]
                        exact hJ15 nv_k cnt idx true true st_k m3 hsb.toStep13ConeSavedBase
                          hnv_mvC (by intro h; simp at h) (by rw [hm3, hm2]; exact hm')
                      · try intro hc
                        have hnv_lt_mvC : nv_k.toNat < mvC.toNat := by omega
                        have hqi_lt_nv : qi_l.toNat < nv_k.toNat := by have := hsb.hsav_le; omega
                        have hpush := step13_cone_push_var_step_ok hsb.toStep13ConeSavedBase
                          hnv_lt_mvC hv_lt (by rw [hta_k.1]; exact htmk_eq0) hqi_lt_nv
                        have hws_idx : (BitVec.setWidth 64 nv_k).toNat <
                            st_k.scratch.work_stk1.length := by
                          have := hsb.hlen.scratch_ok.work_stk1_len
                          have := hsb.hcone.mvC_leMax; have := hsb.hcone.nv_le_cv
                          have := hsb.hlen.core_ok.cur_vars_le
                          simp [BitVec.toNat_setWidth]; omega
                        have hm_cur : (FullMem c st_k ⋆ R) m3 := by rw [hm3, hm2]; exact hm'
                        c0_hstraight; refine head_wp_store rfl rfl
                          (c0_store_full_work_stk1 (lit_k >>> 1#32) hws_idx hm_cur)
                          fun _ hm_w => ?_
                        c0_hstraight
                        have htmk_k_idx : (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat <
                            st_k.scratch.tarjan_mark.length := by
                          rw [hta_k.2.1]; exact hltm_k
                        refine head_wp_store rfl rfl
                          (c0_store_full_tarjan_mark (nv_k + 1#32) (by exact htmk_k_idx) hm_w)
                          fun m_t hm_t => ?_
                        c0_hstraight
                        try dsimp only
                        try rw [wp_jump]
                        rcases hpush with ⟨_, hnv1, _, _, hsu', _⟩
                        have h1 : (BitVec.setWidth 64 nv_k).toNat = nv_k.toNat := by simp
                        have hlen_w : nv_k.toNat < st_k.scratch.work_stk1.length := by
                          simpa [h1] using hws_idx
                        have hbv : nv_k + 1#32 = BitVec.ofNat 32 (nv_k.toNat + 1) := by
                          apply BitVec.eq_of_toNat_eq
                          have := (nv_k + 1#32).isLt
                          rw [hnv1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        let st_push : FullState :=
                          { core := st_k.core
                            scratch :=
                              { st_k.scratch with
                                work_stk1 := st_k.scratch.work_stk1.set nv_k.toNat (lit_k >>> 1#32)
                                tarjan_mark := st_k.scratch.tarjan_mark.set (lit_k >>> 1#32).toNat
                                    (nv_k + 1#32) } }
                        have hbw : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat :=
                          fun x => by simp
                        have hs32 : ∀ x : BitVec 32, (x >>> 1#32) = x >>> (1 : Nat) := fun x => by
                          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight]
                        have hsr_n : (lit_k >>> (1 : Nat)).toNat = lit_k.toNat / 2 := by
                          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                        have hm_t' : (FullMem c st_push ⋆ R) m_t := by
                          simpa [st_push, h1, hbw, hs32, lit_k] using hm_t
                        exact hJ24 (nv_k + 1#32, done_cur, false, st_push) m_t
                          ⟨rfl, rfl, by rw [hnv1]; omega, by rw [hnv1]; omega, hsu', rfl,
                            fun j hj => by
                              dsimp [st_push]
                              exact List.getElem?_set_ne (by omega : nv_k.toNat ≠ j),
                            ⟨nv_k.toNat, by omega, by
                                dsimp [st_push]
                                rw [List.getElem?_set_self hlen_w, Option.getD_some, hsr_n],
                              by
                                dsimp [st_push]
                                rw [← hsr_n, List.getElem?_set_self (by rw [hsr_n]; exact hltm_k),
                                  Option.getD_some, hbv]⟩,
                            hm_t'⟩
                    · try intro hc
                      have htm_val_ne0 :
                          st_k.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 ≠ 0#32 := by
                        rw [← hta_k.2.2]; exact hc
                      have hv_cur : lit_k.toNat / 2 < st_k.core.cur_vars := by rw [hcv_eq]; omega
                      rcases hsb.hcone.rev (lit_k.toNat / 2) hv_cur with
                        h0 | ⟨ilv, hilv_lt, hilv_ws, hilv_tmk⟩
                      · exact False.elim (htm_val_ne0 h0)
                      · dsimp only; rw [wp_jump]
                        exact hJ24 (nv_k, done_cur, false, st_k) m3
                          ⟨rfl, rfl, Nat.le_refl _, hnv_mvC, hsb.toStep13ConeSavedBase, rfl,
                            fun _ _ => rfl, ⟨ilv, hilv_lt, hilv_ws, hilv_tmk⟩,
                            by rw [hm3, hm2]; exact hm'⟩
                · intro J23 hJ23
                  c0_hstraight; (try clear hc); m6_split
                  · c0_hstraight; (try clear hc); m6_split
                    · rw [wp_jump]
                      exact hJ15 nv_k cnt idx done_cur true st_k m2 hsb.toStep13ConeSavedBase
                        hnv_mvC (by intro h; simp at h) (by rw [hm2]; exact hm')
                    · dsimp only; rw [wp_jump]; exact hJ23 () m2 rfl
                  · dsimp only; rw [wp_jump]; exact hJ23 () m2 rfl
              · intro J22 hJ22
                c0_hstraight; (try clear hc); m6_split
                · c0_hstraight; (try clear hc); m6_split
                  · rw [wp_jump]
                    exact hJ15 nv_k cnt idx done_cur true st_k m' hsb.toStep13ConeSavedBase
                      hnv_mvC (by intro h; simp at h) hm'
                  · dsimp only; rw [wp_jump]; exact hJ22 () m' rfl
                · dsimp only; rw [wp_jump]; exact hJ22 () m' rfl
          · try intro hc
            have heq0_f := hc; have hval_false :
                s.core.vals[(s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat]?.getD 0#8 =
                  255#8 := by
              have hlit_to : (BitVec.setWidth 64 lit_k).toNat = lit_k.toNat := by simp
              have hvals_len_k : lit_k.toNat < st_k.core.vals.length := by
                rw [← hlit_to]; exact hvals_idx
              have hget : st_k.core.vals[lit_k.toNat] = s.core.vals[lit_k.toNat]?.getD 0#8 := by
                have hq : st_k.core.vals[lit_k.toNat]? = s.core.vals[lit_k.toNat]? := by
                  rw [hvals_eq]
                rw [List.getElem?_eq_getElem hvals_len_k] at hq; rw [← hq]; rfl
              have hsgt0 : (0#32).slt (BitVec.signExtend 32 (s.core.vals[lit_k.toNat]?.getD 0#8)) =
                  false := by rw [← hget]; exact hsgt_f
              have hne0' : s.core.vals[lit_k.toNat]?.getD 0#8 ≠ 0#8 := by
                rw [← hget]
                have hlk : lit_k.toNat = st_k.core.arena[cr.toNat + 3 + idx.toNat].toNat := by
                  simp only [lit_k, h1]
                simpa [hlk] using heq0_f
              simpa [hlit_at] using s13_sext8_255 hw hlit_lt hsgt0 hne0'
            have hskip := s13_scan_skip_step hsb hidx_lt hval_false
            dsimp only; rw [wp_jump]; exact hJ21 (nv_k, done_cur, false, cnt, st_k) m'
              ⟨rfl, rfl, by omega, by omega, hnv_mvC, by simpa [hskip.1] using hskip.2, hm'⟩
    · try intro hc
      have hidx_eq : idx = sz := BitVec.eq_of_toNat_eq (by omega)
      subst hidx_eq
      have hcnt_nv : cnt.toNat ≤ nv_k.toNat := m6_cone_cnt_le_nv hsb.hlts hsb.hnd
      rw [wp_jump]
      exact hJ15 nv_k cnt idx done_cur false st_k m' hsb.toStep13ConeSavedBase hnv_mvC
        (fun _ => ⟨rfl, rfl, hcnt_nv, hcnt_le, hsb⟩) hm'

theorem step13_cone_occ_clause_wp
    {Γ : Env} {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s st_0 : FullState}
    {vlim savedNv nc_cur cr sz cv qi_l tmk_cv pol : BitVec 32} {done_cur : Bool}
    {p_next : BitVec 64} {m : Mem 64}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (J14 : Cont [i32, i32, .bool, i64])
    (pHdr pWs1 pTmk pArena pVals pTmp pFlags pKptr : Val i64)
    (hpHdr : pHdr = c.hdr) (hpWs1 : pWs1 = c.pWorkStk1) (hpTmk : pTmk = c.pTarjanMark)
    (hpArena : pArena = c.pArena) (hpVals : pVals = c.pVals) (hpTmp : pTmp = c.pTmp)
    (hpFlags : pFlags = c.pFlags) (hpKptr : pKptr = L.kPtr c.pScratchBuf)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnodup_a : FullArenaVarsNodup s)
    (hlen_s : FullState.LengthsOk c s) (hlv0 : s.core.cur_level = 0)
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hsav : Step13ConeBase F_cur L mvC c s cv qi_l savedNv.toNat nc_cur.toNat st_0)
    (hsav_mvC : savedNv.toNat ≤ mvC.toNat) (hqi_lt : qi_l.toNat < savedNv.toNat)
    (hnc_lt : nc_cur.toNat < L.maxOrig) (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hgarb : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (har_len : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length) (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hm : (FullMem c st_0 ⋆ R) m)
    (hJ14 : ∀ (nv' nc' : BitVec 32) (done' : Bool) (st' : FullState) (m' : Mem 64),
      Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' →
      savedNv.toNat ≤ nv'.toNat → nv'.toNat ≤ mvC.toNat → nc'.toNat ≤ L.maxOrig →
      (FullMem c st' ⋆ R) m' → J14 (nv', nc', done', p_next, ()) m') :
    wp Γ Q X (occClauseExpr J14 pHdr pWs1 pTmk pArena pVals pTmp pFlags pKptr
        mvC vlim savedNv nc_cur cr sz cv tmk_cv pol done_cur p_next) m := by
  subst hpHdr hpWs1 hpTmk hpArena hpVals hpTmp hpFlags hpKptr
  let ws0 := st_0.scratch.work_stk1; let scr0 := st_0.scratch.scratch_buf
  have hsav0 : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0
      savedNv.toNat nc_cur.toNat st_0 := ⟨hsav, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  have hge1 : 1 ≤ savedNv.toNat := hsav.hcone.nv_ge1
  have hbdd : K6LitsBounded savedNv.toNat (k6StateOfScratch L scr0) := hsav.hcone.k6_bdd
  have htrl : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * savedNv.toNat :=
    hsav.hcone.k6_trl_bdd
  refine wp_join_state (fun (p : BitVec 32 × Bool × Bool × BitVec 32 × BitVec 32 × FullState) =>
      (p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, ()))
    (fun ⟨nv_k, done_k, abort_k, cnt_k, idx_k, st_k⟩ m' =>
      Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_k.toNat nc_cur.toNat st_k ∧
      nv_k.toNat ≤ mvC.toNat ∧
      (abort_k = false →
        done_k = done_cur ∧ idx_k = sz ∧ cnt_k.toNat ≤ nv_k.toNat ∧ cnt_k.toNat ≤ sz.toNat ∧
        Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
          nv_k.toNat nc_cur.toNat cnt_k.toNat sz.toNat st_k) ∧
      (FullMem c st_k ⋆ R) m')
    ?_ ?_
  · intro J15 ⟨nv_k, done_k, abort_k, cnt_k, idx_k, st_k⟩ m' ⟨hsb_k, hnv_k, hok_k, hm_k⟩
    dsimp [Blocks.get, Member.here]
    try rw [wp_jnz]
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · refine step13_cone_rollback_loop_wp c.pWorkStk1 c.pTarjanMark rfl rfl
        (fun p => .jump J14 ((.var p), (.var nc_cur), (.var done_k), (.var p_next), ()))
        hsb_k hge1 hqi_lt hbdd htrl hm_k ?_
      intro st_r m_r hbase_r _ _ hm_r
      rw [wp_jump]
      exact hJ14 savedNv nc_cur done_k st_r m_r hbase_r (Nat.le_refl _) hsav_mvC (by omega) hm_r
    · rcases hok_k hc with ⟨hd_eq, hidx_sz, hcnt_nv, hcnt_sz, hscan_k⟩
      refine wp_join_state
        (fun (p : BitVec 32 × BitVec 32 × Bool × FullState) => (p.1, p.2.1, p.2.2.1, ()))
        (fun ⟨nv_o, nc_o, done_o, st_o⟩ m'' =>
          Step13ConeBase F_cur L mvC c s cv qi_l nv_o.toNat nc_o.toNat st_o ∧
          savedNv.toNat ≤ nv_o.toNat ∧
          nv_o.toNat ≤ mvC.toNat ∧ nc_o.toNat ≤ L.maxOrig ∧ (FullMem c st_o ⋆ R) m'')
        ?_ ?_
      · intro J17 ⟨nv_o, nc_o, done_o, st_o⟩ m'' ⟨hb_o, hsav_o, hnv_o, hnc_o, hm_o⟩
        dsimp [Blocks.get, Member.here]
        exact hJ14 nv_o nc_o done_o st_o m'' hb_o hsav_o hnv_o hnc_o hm_o
      · intro J17 hJ17
        have hcnt_lt28 : cnt_k.toNat < 2 ^ 28 := by
          have := L.hmaxV; have := hscan_k.hcone.mvC_leMax; omega
        have hcnt_tmp : cnt_k.toNat ≤ st_k.core.tmp.length := by
          have := hscan_k.hlen.core_ok.tmp_len_arr; have := hlen_s.core_ok.cur_vars_le
          omega
        have hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
            (List.map (fun x => m6ConeLift st_k.scratch.work_stk1 x.toNat)
              (List.take cnt_k.toNat st_k.core.tmp))) := by
          refine m6_cone_clause_entails_filtered hw hlv0 hcr_ref hgarb ?_
          intro l hl
          have har_s : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]?.getD 0#32).toNat ≤
              s.core.arena.length := by
            change cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤ s.core.arena.length
            rw [← hsz_eq]; exact har_len
          rw [m6_arenaClauseLitsCore_mem_iff har_s] at hl; rcases hl with ⟨i, hi, rfl⟩
          change i < fullArenaClauseSizeCore s.core cr.toNat at hi
          rw [← hsz_eq] at hi; exact hscan_k.hcov i hi
        refine step13_cone_call_add_clause hAddCl rfl rfl rfl hLscr hLmv
          hscan_k.hlen hscan_k.hag hscan_k.hgu hscan_k.hcone hnc_lt hcnt_lt28 hcnt_tmp
          hscan_k.hlts hent hm_k ?_
        intro ok st' m'' hlen' hag' hgu' hcone' hscr_eq htmk_eq hws_eq hm''
        dsimp only; rw [wp_jnz]; refine ⟨fun hc => ?_, fun hc => ?_⟩
        · subst hc
          have hnc1_le : (nc_cur + 1#32).toNat ≤ L.maxOrig := by
            have : nc_cur.toNat + 1 < 2 ^ 32 := by
              have := hLmv; have := L.hmaxV
              simp only [K6Layout.maxOrig] at hnc_lt ⊢; omega
            simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]; omega
          have hkptr := (fid_cone_load_kptr_hdr hcone' hm'').1
          c0_hstraight
          refine wp_join_state (fun (p : Bool) => (p, ())) (fun done' m3 => m3 = m'') ?_ ?_
          · intro J18 done' m3 hm3
            dsimp [Blocks.get, Member.here]
            try dsimp only; try rw [wp_jump]
            exact hJ17 (nv_k, nc_cur + 1#32, done', st') m3
              ⟨⟨hlen', hag', hgu', hcone', by rw [htmk_eq]; exact hscan_k.htmk,
                by rw [hws_eq]; exact hscan_k.hwk⟩,
                hscan_k.hsav_le, hnv_k, hnc1_le, by rw [hm3]; exact hm''⟩
          · intro J18 hJ18
            c0_hstraight; refine head_wp_load rfl hkptr ?_
            c0_hstraight; (try clear hc); m6_split
            · try dsimp only; try rw [wp_jump]; exact hJ18 true m'' rfl
            · c0_hstraight; (try clear hc); m6_split
              · try dsimp only; try rw [wp_jump]; exact hJ18 true m'' rfl
              · try dsimp only; try rw [wp_jump]; exact hJ18 done_k m'' rfl
        · subst hc
          have hsb' : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0
              nv_k.toNat nc_cur.toNat st' :=
            ⟨⟨hlen', hag', hgu', hcone', by rw [htmk_eq]; exact hscan_k.htmk,
              by rw [hws_eq]; exact hscan_k.hwk⟩,
              hscan_k.hsav_le, by rw [hscr_eq rfl, hscan_k.hscr],
              fun j hj => by rw [hws_eq]; exact hscan_k.hws j hj⟩
          refine step13_cone_rollback_loop_wp c.pWorkStk1 c.pTarjanMark rfl rfl
            (fun p => .jump J17 ((.var p), (.var nc_cur), (.imm true), ()))
            hsb' hge1 hqi_lt hbdd htrl hm'' ?_
          intro st_r m_r hbase_r _ _ hm_r
          try dsimp only; try rw [wp_jump]
          exact hJ17 (savedNv, nc_cur, true, st_r) m_r
            ⟨hbase_r, Nat.le_refl _, hsav_mvC, by omega, hm_r⟩
  · intro J15 hJ15
    exact step13_cone_occ_scan_wp J15 c.pWorkStk1 c.pTarjanMark c.pArena c.pVals c.pTmp
      c.pFlags rfl rfl rfl rfl rfl rfl hw hnodup_a hlen_s hsav0 hsav_mvC hqi_lt
      hcr_ref hgarb hsz_eq har_len hsz_cv hm fun nv_k cnt_k idx_k done_k abort_k st_k m'
        hsb_k hnv_k hok_k hm' => by
      exact hJ15 (nv_k, done_k, abort_k, cnt_k, idx_k, st_k) m' ⟨hsb_k, hnv_k, hok_k, hm'⟩

theorem step13_cone_occ_pass_wp
    {Γ : Env} {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s st_in : FullState}
    {vlim maxOrig nv_in nc_in cv qi_l tmk_cv qi_next : BitVec 32} {done_in : Bool}
    {m : Mem 64}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (J9 : Cont [i32, i32, i32, .bool])
    (pHdr pWs1 pTmk pWvec pWstk pArena pVals pTmp pFlags pKptr : Val i64)
    (hpHdr : pHdr = c.hdr) (hpWs1 : pWs1 = c.pWorkStk1) (hpTmk : pTmk = c.pTarjanMark)
    (hpWvec : pWvec = c.pWvec) (hpWstk : pWstk = c.pWstk) (hpArena : pArena = c.pArena)
    (hpVals : pVals = c.pVals) (hpTmp : pTmp = c.pTmp) (hpFlags : pFlags = c.pFlags)
    (hpKptr : pKptr = L.kPtr c.pScratchBuf)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnodup_a : FullArenaVarsNodup s)
    (hlen_s : FullState.LengthsOk c s) (hlv0 : s.core.cur_level = 0)
    (hdw : DenseWatchesInv F_cur s.core)
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hb_in : Step13ConeBase F_cur L mvC c s cv qi_l nv_in.toNat nc_in.toNat st_in)
    (hmaxOrig : maxOrig.toNat ≤ L.maxOrig)
    (hnv_in : nv_in.toNat ≤ mvC.toNat) (hnc_in : nc_in.toNat ≤ L.maxOrig)
    (hqi_lt : qi_l.toNat < nv_in.toNat) (hm : (FullMem c st_in ⋆ R) m)
    (hJ9 : ∀ (nv' nc' : BitVec 32) (done' : Bool) (st' : FullState) (m' : Mem 64),
      Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' →
      nv'.toNat ≤ mvC.toNat → nv_in.toNat ≤ nv'.toNat → nc'.toNat ≤ L.maxOrig →
      qi_l.toNat < nv'.toNat → (FullMem c st' ⋆ R) m' →
      J9 (nv', nc', qi_next, done', ()) m') :
    wp Γ Q X (occPassExpr J9 pHdr pWs1 pTmk pWvec pWstk pArena pVals pTmp pFlags pKptr
        mvC vlim maxOrig nv_in nc_in done_in cv tmk_cv qi_next) m := by
  subst hpHdr hpWs1 hpTmk hpWvec hpWstk hpArena hpVals hpTmp hpFlags hpKptr
  let α := BitVec 32 × BitVec 32 × Bool × BitVec 32 × FullState
  let Inv : α → Mem 64 → Prop := fun ⟨nv_k, nc_k, done_k, pol, st_k⟩ m' =>
    Step13ConeBase F_cur L mvC c s cv qi_l nv_k.toNat nc_k.toNat st_k ∧
    nv_k.toNat ≤ mvC.toNat ∧ nv_in.toNat ≤ nv_k.toNat ∧ nc_k.toNat ≤ L.maxOrig ∧
    qi_l.toNat < nv_k.toNat ∧ pol.toNat ≤ 2 ∧ (FullMem c st_k ⋆ R) m'
  refine wp_while_state (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, ()))
    (fun p => 2 - p.2.2.2.1.toNat) Inv ?_ ?_
  · intro J12 hJ12
    dsimp only; rw [wp_jump]
    exact hJ12 (nv_in, nc_in, done_in, 0#32, st_in) m
      ⟨hb_in, hnv_in, Nat.le_refl _, hnc_in, hqi_lt, by decide, hm⟩
  · intro J12 ⟨nv_k, nc_k, done_k, pol, st_k⟩ m'
      ⟨hb_k, hnv_k, hnv_le_k, hnc_k, hqi_k, hpol_le, hm'⟩ hIH
    dsimp [Blocks.get, Member.here]; c0_hstraight
    try clear hc
    m6_split
    · try intro hc
      have hpol_lt : pol.toNat < 2 := hc
      try clear hc
      try dsimp only
      try rw [wp_jnz]
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · subst hc
        rw [wp_jump]; exact hJ9 nv_k nc_k true st_k m' hb_k hnv_k hnv_le_k hnc_k hqi_k hm'
      · subst hc
        c0_hstraight
        try clear hc
        m6_split
        · try intro hc
          have hnc_lt_max : nc_k.toNat < maxOrig.toNat := hc
          have hcv_lt : cv.toNat < s.core.cur_vars := by
            have := s13_cur_vars_eq hb_k.hag; have hfwd := hb_k.hcone.fwd qi_l.toNat hqi_k
            have hwk := hb_k.hwk
            omega
          let lit := (cv <<< 1#32) ||| pol
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
            have hcv_31 : cv.toNat < 2 ^ 31 := by
              have hmv := c.hmaxv
              simp only [Examples.LratBytes.dimacsBound] at hmv
              have := hlen_s.core_ok.cur_vars_le
              omega
            have h2 : ((cv <<< 1#32) ||| pol).toNat = 2 * cv.toNat + pol.toNat := by
              have h1 : (cv <<< 1#32).toNat = cv.toNat <<< 1 := by
                simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
              rw [BitVec.toNat_or, h1,
                ← Nat.shiftLeft_add_eq_or_of_lt (by omega : pol.toNat < 2 ^ 1),
                Nat.shiftLeft_eq]
              omega
            have hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat := h2
            omega
          have hwv := step13_cone_wvec_facts hlen_s hb_k.hlen hb_k.hag hdw hlit_lt
          rcases hwv with ⟨hwOff, hwSz, hwEnd, hwle, hwsub, hwend_le, hwv0, hwv1⟩
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
          c0_hstraight; refine head_wp_load (congrArg (fun z => c.pWvec + (z + 1#64) * 4#64) hshl64)
            (c0_load_full_wvec hw1_idx hm') ?_
          c0_hstraight
          let wOff := BitVec.setWidth 64 st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]
          let wSz := BitVec.setWidth 64 st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]
          let wEnd := wOff + wSz
          have hwEnd63 : wEnd.toNat < 2 ^ 63 := by
            have h32a : wOff.toNat < 2 ^ 32 := by
              dsimp [wOff]; rw [BitVec.toNat_setWidth]
              exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)
            have h32b : wSz.toNat < 2 ^ 32 := by
              dsimp [wSz]; rw [BitVec.toNat_setWidth]
              exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)
            have hmod : (wOff + wSz).toNat = (wOff.toNat + wSz.toNat) % 2 ^ 64 :=
              BitVec.toNat_add wOff wSz
            dsimp [wEnd]; omega
          refine wp_join_state (ts := [i32, i32, Ty.bool, i64])
            (α := BitVec 32 × BitVec 32 × Bool × BitVec 64 × FullState)
            (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, ()))
            (fun ⟨nv_j, nc_j, done_j, _, st_j⟩ m'' =>
              Step13ConeBase F_cur L mvC c s cv qi_l nv_j.toNat nc_j.toNat st_j ∧
              nv_j.toNat ≤ mvC.toNat ∧ nv_k.toNat ≤ nv_j.toNat ∧ nc_j.toNat ≤ L.maxOrig ∧
              qi_l.toNat < nv_j.toNat ∧ (FullMem c st_j ⋆ R) m'') ?_ ?_
          · intro J13 ⟨nv_j, nc_j, done_j, _, st_j⟩ m''
              ⟨hb_j, hnv_j, hnv_kj, hnc_j, hqi_j, hm''⟩
            dsimp [Blocks.get, Member.here]; c0_hstraight
            have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 := by
              have : pol.toNat + 1 < 2 ^ 32 := by omega
              simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]
            try dsimp only
            try rw [wp_jump]
            exact hIH (nv_j, nc_j, done_j, pol + 1#32, st_j) m'' (by dsimp only; rw [hpol1]; omega)
              ⟨hb_j, hnv_j, Nat.le_trans hnv_le_k hnv_kj, hnc_j, hqi_j, by rw [hpol1]; omega, hm''⟩
          · intro J13 hJ13
            let β := BitVec 32 × BitVec 32 × Bool × BitVec 64 × FullState
            let J14Inv : β → Mem 64 → Prop := fun ⟨nv_j, nc_j, done_j, p, st_j⟩ m'' =>
              Step13ConeBase F_cur L mvC c s cv qi_l nv_j.toNat nc_j.toNat st_j ∧
              nv_j.toNat ≤ mvC.toNat ∧ nv_k.toNat ≤ nv_j.toNat ∧ nc_j.toNat ≤ L.maxOrig ∧
              qi_l.toNat < nv_j.toNat ∧ p.toNat ≤ wEnd.toNat ∧
              DenseWatchSliceOk F_cur s.core lit.toNat p.toNat (wEnd.toNat - p.toNat) ∧
              (FullMem c st_j ⋆ R) m''
            refine wp_while_state (ts := [i32, i32, Ty.bool, i64]) (α := β)
              (fun q => (q.1, q.2.1, q.2.2.1, q.2.2.2.1, ()))
              (fun q => wEnd.toNat - q.2.2.2.1.toNat) J14Inv ?_ ?_
            · intro J14 hJ14
              have hslice0 : DenseWatchSliceOk F_cur s.core lit.toNat wOff.toNat
                  (wEnd.toNat - wOff.toNat) := by
                have := hdw.slices lit.toNat hlit_lt
                rw [← hwOff, ← hwsub] at this; exact this
              dsimp only; rw [wp_jump]; exact hJ14 (nv_k, nc_k, false, wOff, st_k) m'
                ⟨hb_k, hnv_k, Nat.le_refl _, hnc_k, hqi_k, hwle, hslice0, hm'⟩
            · intro J14 ⟨nv_j, nc_j, done_j, p, st_j⟩ m''
                ⟨hb_j, hnv_j, hnv_kj, hnc_j, hqi_j, hp_le, hslice, hm''⟩ hIH14
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
                    List.getElem?_eq_getElem (by rw [← ha]; exact hw0_idx)] at hq
                  injection hq
                have h1 : st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat] =
                    st_k.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64] := by
                  have hq : st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]? =
                      st_k.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64]? := by rw [hb]
                  rw [List.getElem?_eq_getElem hw1_idx,
                    List.getElem?_eq_getElem (by rw [← hb]; exact hw1_idx)] at hq
                  injection hq
                dsimp [wEnd, wOff, wSz]; rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                  Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)),
                  Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)), h0]
                congr 2; exact congrArg BitVec.toNat h1
              try clear hc
              m6_split
              · try intro hc
                have hp_lt : p.toNat < wEnd.toNat := by rw [hwEnd_unf]; exact hc
                (try clear hc); (try dsimp only)
                rw [wp_jnz]; refine ⟨fun hc => ?_, fun hc => ?_⟩
                · subst hc; (try dsimp only); (try rw [wp_jump])
                  exact hJ13 (nv_j, nc_j, true, p, st_j) m''
                    ⟨hb_j, hnv_j, hnv_kj, hnc_j, hqi_j, hm''⟩
                · subst hc; c0_hstraight; (try clear hc); m6_split
                  · try intro hc
                    have hnc_j_lt : nc_j.toNat < maxOrig.toNat := hc
                    have hwstk_eq := s13_wstk_eq hb_j.hag
                    have hwstk_idx : p.toNat < st_j.core.wstk.length :=
                      fid_cone_hp_wstk hwstk_eq hp_lt hwend_le
                    have hrem_pos : 0 < wEnd.toNat - p.toNat := by omega
                    have hp63 : p.toNat < 2 ^ 63 := by omega
                    have hw0_at : s.core.wstk[p.toNat]? = some st_j.core.wstk[p.toNat] := by
                      have hq : s.core.wstk[p.toNat]? = st_j.core.wstk[p.toNat]? := by rw [hwstk_eq]
                      rw [List.getElem?_eq_getElem hwstk_idx] at hq; exact hq
                    c0_hstraight; refine head_wp_load rfl (c0_load_full_wstk hwstk_idx hm'') ?_
                    c0_hstraight
                    try clear hc
                    m6_split
                    · try intro hc
                      have hbin' : st_j.core.wstk[p.toNat] &&& 2147483648#32 ≠ 0#32 := by
                        simpa using hc
                      have hstep_b := m6_denseSlice_step_bin hslice hrem_pos hw0_at hbin'
                      have hp1 : (p + 1#64).toNat = p.toNat + 1 := fid_cone_wstk_p_toNat_eq p hp63
                      dsimp only; rw [wp_jump]; exact hIH14 (nv_j, nc_j, false, p + 1#64, st_j) m''
                        (by dsimp only; rw [hp1]; omega)
                        ⟨hb_j, hnv_j, hnv_kj, hnc_j, hqi_j, by rw [hp1]; omega,
                          by simpa [hp1, fid_cone_sub_sub_eq] using hstep_b.2.2.2, hm''⟩
                    · try intro hc
                      have hocc' : st_j.core.wstk[p.toNat] &&& 2147483648#32 = 0#32 := by
                        simpa using hc
                      rcases m6_denseSlice_step_occ hslice hrem_pos hw0_at hocc' with
                        ⟨h2rem, _, cr, hcr_wstk, _, hcr_ref, hslice_next⟩
                      have hp1 : (p + 1#64).toNat = p.toNat + 1 := fid_cone_wstk_p_toNat_eq p hp63
                      have h1lt : (p + 1#64).toNat < wEnd.toNat := by rw [hp1]; omega
                      c0_hstraight
                      try clear hc
                      m6_split
                      · try intro hc
                        rw [← hwEnd_unf] at hc
                        have hp_mod : (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 :=
                          Nat.mod_eq_of_lt (by omega)
                        rw [hp_mod, ← hp1] at hc; omega
                      · have hp1_63 : (p + 1#64).toNat < 2 ^ 63 := by rw [hp1]; omega
                        have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                          have hlt2 : (p + 1#64).toNat + 1 < 2 ^ 64 := by rw [hp1]; omega
                          have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
                          rw [BitVec.toNat_add, h1_64, Nat.mod_eq_of_lt hlt2, hp1]
                        have hcr_idx : (p + 1#64).toNat < st_j.core.wstk.length :=
                          fid_cone_hp_wstk hwstk_eq h1lt hwend_le
                        have har_len_eq := s13_arena_len_eq hb_j.hag
                        have har_eq := s13_arena_eq hb_j.hag
                        have hal_load := load_full_arena_len hm''
                        c0_hstraight; refine head_wp_load rfl (c0_load_full_wstk hcr_idx hm'') ?_
                        c0_hstraight; refine head_wp_load rfl hal_load ?_
                        c0_hstraight
                        have hlen1 : p.toNat + 1 < st_j.core.wstk.length := by
                          rw [← hp1]; exact hcr_idx
                        have hcr_ld' : st_j.core.wstk[p.toNat + 1] = cr := by
                          have hq : s.core.wstk[p.toNat + 1]? = st_j.core.wstk[p.toNat + 1]? := by
                            rw [hwstk_eq]
                          rw [hcr_wstk, List.getElem?_eq_getElem hlen1] at hq
                          injection hq with heq; exact heq.symm
                        have hcr_ld : st_j.core.wstk[(p + 1#64).toNat] = cr := by
                          have hq2 : st_j.core.wstk[(p + 1#64).toNat]? =
                              st_j.core.wstk[p.toNat + 1]? := by rw [hp1]
                          rw [List.getElem?_eq_getElem hcr_idx,
                            List.getElem?_eq_getElem hlen1] at hq2
                          injection hq2 with h2; exact h2.trans hcr_ld'
                        have hskip2 : J14 (nv_j, nc_j, false, p + 1#64 + 1#64, ()) m'' :=
                          hIH14 (nv_j, nc_j, false, p + 1#64 + 1#64, st_j) m''
                            (by dsimp only; rw [hp2]; omega)
                            ⟨hb_j, hnv_j, hnv_kj, hnc_j, hqi_j, by rw [hp2]; omega,
                              by simpa [hp2, fid_cone_sub_sub_eq] using hslice_next, hm''⟩
                        try clear hc
                        m6_split
                        · dsimp only; rw [wp_jump]; exact hskip2
                        · try intro hc
                          have hcr2_idx : (BitVec.setWidth 64 cr + 2#64).toNat <
                              st_j.core.arena.length := by
                            have := hlen_s.core_ok.arena_len_arr
                            have := hlen_s.core_ok.arena_len_le; have := cr.isLt
                            have hcr3_64 : (BitVec.setWidth 64 cr + 3#64).toNat = cr.toNat + 3 := by
                              simp [BitVec.toNat_add,
                                Nat.mod_eq_of_lt (by omega : cr.toNat + 3 < 2 ^ 64)]
                            have hal64 : (BitVec.ofNat 64 st_j.core.arena_len).toNat =
                                s.core.arena_len := by
                              have := c.hsize; have := c.havail_fit; rw [har_len_eq]
                              rw [BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)]
                            have hnot : ¬(BitVec.ofNat 64 st_j.core.arena_len).toNat <
                                (BitVec.setWidth 64 cr + 3#64).toNat := by
                              simpa [hcr_ld, hcr_ld'] using hc
                            rw [har_eq]; simp [BitVec.toNat_add]; omega
                          have hcr0_idx :
                              (BitVec.setWidth 64 cr).toNat < st_j.core.arena.length := by
                            have := cr.isLt; rw [har_eq] at hcr2_idx ⊢
                            simp [BitVec.toNat_add] at hcr2_idx ⊢; omega
                          have hcr2_idx' : (BitVec.setWidth 64
                              st_j.core.wstk[(p + 1#64).toNat] + 2#64).toNat <
                              st_j.core.arena.length := by simpa [hcr_ld, hcr_ld'] using hcr2_idx
                          have hcr0_idx' : (BitVec.setWidth 64
                              st_j.core.wstk[(p + 1#64).toNat]).toNat <
                              st_j.core.arena.length := by simpa [hcr_ld, hcr_ld'] using hcr0_idx
                          c0_hstraight
                          refine head_wp_load rfl (c0_load_full_arena hcr2_idx' hm'') ?_
                          c0_hstraight
                          refine head_wp_load rfl (c0_load_full_arena hcr0_idx' hm'') ?_
                          c0_hstraight
                          try clear hc
                          m6_split
                          · dsimp only; rw [wp_jump]; exact hskip2
                          · try intro hc
                            have hhdr_ok := hc
                            c0_hstraight; (try clear hc); m6_split
                            · dsimp only; rw [wp_jump]; exact hskip2
                            · c0_hstraight
                              refine head_wp_load rfl hal_load ?_
                              c0_hstraight
                              try clear hc
                              m6_split
                              · dsimp only; rw [wp_jump]; exact hskip2
                              · let sz := st_j.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]
                                have hsz_eq : sz.toNat =
                                    fullArenaClauseSizeCore s.core cr.toNat := by
                                  dsimp [sz, fullArenaClauseSizeCore]
                                  have h2 :
                                      (BitVec.setWidth 64 cr + 2#64).toNat = cr.toNat + 2 := by
                                    have := cr.isLt
                                    simp [BitVec.toNat_add,
                                      Nat.mod_eq_of_lt (by omega : cr.toNat + 2 < 2 ^ 64)]
                                  have hlen_a : cr.toNat + 2 < s.core.arena.length := by
                                    rw [← har_eq, ← h2]; exact hcr2_idx
                                  have hidx2 : ((BitVec.setWidth 64 cr).toNat + 2) % 2 ^ 64 =
                                      cr.toNat + 2 := by
                                    have := cr.isLt
                                    simp [BitVec.toNat_setWidth,
                                      Nat.mod_eq_of_lt (by omega : cr.toNat + 2 < 2 ^ 64)]
                                  have hidx2_lt : ((BitVec.setWidth 64 cr).toNat + 2) % 2 ^ 64 <
                                      st_j.core.arena.length := by
                                    simpa [BitVec.toNat_add] using hcr2_idx
                                  have hq : st_j.core.arena[
                                          ((BitVec.setWidth 64 cr).toNat + 2) % 2 ^ 64]? =
                                        s.core.arena[cr.toNat + 2]? := by rw [har_eq, hidx2]
                                  rw [List.getElem?_eq_getElem hidx2_lt,
                                    List.getElem?_eq_getElem hlen_a] at hq
                                  injection hq with heq
                                  rw [List.getElem?_eq_getElem hlen_a, Option.getD_some]
                                  exact congrArg BitVec.toNat heq
                                have hocc_ok := m6_cone_occ_hdr_ok hlen_s hw hnodup_a
                                  har_eq hcr_ref hsz_eq (by
                                    have hcr0_eq : (BitVec.setWidth 64 cr).toNat = cr.toNat := by
                                      simp
                                    simpa [hcr0_eq, hcr_ld, hcr_ld'] using hhdr_ok)
                                rcases hocc_ok with ⟨hgarb, _, hsz_cv, har_len⟩
                                have hsz_ld : st_j.core.arena[
                                        (BitVec.setWidth 64 st_j.core.wstk[(p + 1#64).toNat] +
                                          2#64).toNat] = sz := by
                                  have hq : st_j.core.arena[
                                          (BitVec.setWidth 64 st_j.core.wstk[(p + 1#64).toNat] +
                                            2#64).toNat]? =
                                        st_j.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]? := by
                                    rw [hcr_ld]
                                  rw [List.getElem?_eq_getElem hcr2_idx',
                                    List.getElem?_eq_getElem hcr2_idx] at hq
                                  injection hq
                                try dsimp only
                                rw [hsz_ld, hcr_ld]; exact step13_cone_occ_clause_wp hAddCl J14
                                  c.hdr c.pWorkStk1 c.pTarjanMark c.pArena c.pVals
                                  c.pTmp c.pFlags (L.kPtr c.pScratchBuf)
                                  rfl rfl rfl rfl rfl rfl rfl rfl
                                  hw hnodup_a hlen_s hlv0 hLscr hLmv hb_j hnv_j hqi_j (by omega)
                                  hcr_ref hgarb hsz_eq har_len hsz_cv hm''
                                  (vlim := vlim) (tmk_cv := tmk_cv) (pol := pol) (done_cur := false)
                                  (p_next := p + 1#64 + 1#64)
                                  fun nv' nc' done' st' m3 hb' hsav_nv' hnv' hnc' hm3 => by
                                  try dsimp only
                                  try rw [wp_jump]
                                  exact hIH14 (nv', nc', done', p + 1#64 + 1#64, st') m3
                                    (by dsimp only; rw [hp2]; omega)
                                    ⟨hb', hnv', by omega, hnc', by omega, by rw [hp2]; omega,
                                      by simpa [hp2, fid_cone_sub_sub_eq] using hslice_next,
                                      hm3⟩
                  · try dsimp only; try rw [wp_jump]
                    exact hJ13 (nv_j, nc_j, false, p, st_j) m''
                      ⟨hb_j, hnv_j, hnv_kj, hnc_j, hqi_j, hm''⟩
              · try dsimp only; try rw [wp_jump]
                exact hJ13 (nv_j, nc_j, done_j, p, st_j) m''
                  ⟨hb_j, hnv_j, hnv_kj, hnc_j, hqi_j, hm''⟩
        · rw [wp_jump]
          exact hJ9 nv_k nc_k false st_k m' hb_k hnv_k hnv_le_k hnc_k hqi_k hm'
    · rw [wp_jump]
      exact hJ9 nv_k nc_k done_k st_k m' hb_k hnv_k hnv_le_k hnc_k hqi_k hm'

end
end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
