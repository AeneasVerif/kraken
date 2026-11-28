/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpWatchHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpFlushHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpOvfFlush
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerBin
public import LeanQbe.T.Examples.Kissat.Src.PropSearch
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat PropSearch Inner-Loop Large-Clause & Main-Loop WP Proofs (`Proof.PropSearch.WpInnerLarge`)

Defines the remaining modular inner-loop C0 expressions (`s13LpMaxLvlLoopExpr`,
`s13LpReplScanSubExpr`, `s13LpReplDelExpr`, `s13LpNoReplExpr`, `s13LpScanExpr`,
`s13LpLargeStepExpr`, `s13LpLoopExpr`) and proves their WP theorems (`s13_lp_loop_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec

local macro "s13_hstraight" : tactic =>
  `(tactic| (
    try first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _
    try dsimp only [opI64, opCmp64, opCmp32, opI32]
    c0_hstraight))

local macro "s13_hsteps" : tactic =>
  `(tactic| (
    try first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _
    try dsimp only [opI64, opCmp64, opCmp32, opI32]
    c0_hsteps))

local macro "s13_hsteps_nogrp" : tactic =>
  `(tactic| (
    try first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _
    try dsimp only [opI64, opCmp64, opCmp32, opI32]
    c0_hsteps_nogrp))

local macro "s13_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

@[expose] def s13LpMaxLvlLoopExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (arena lvl : V i64) (not_lit : V i32) (cbase3 csz : V i64) (J_done : L [i32]) :
    Expr V L rs :=
  Expr.group (sig := [[i32, i64]]) (fun J267 =>
    Blocks.cons (fun b268 =>
      Expr.let_ (opCmp64 CmpOp.ult (Arg.var b268.2.1) (Arg.var csz)) fun v269 =>
      Expr.jnz (Arg.var v269.1)
        (Expr.let_ (opI64 (OpCode.add i64) (Arg.var cbase3) (Arg.var b268.2.1)) fun v270 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v270.1) (@Arg.imm _ i64 4)) fun v271 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v271.1)) fun v272 =>
        Expr.load i32 (Arg.var v272.1) fun ld273 =>
        Expr.group (sig := [[i32]]) (fun _J274 =>
          Blocks.cons (fun b275 =>
            Expr.let_ (opI64 (OpCode.add i64) (Arg.var b268.2.1) (@Arg.imm _ i64 1)) fun v276 =>
            Expr.jump J267.1 (Arg.var b275.1, Arg.var v276.1, ()))
            Blocks.nil)
          fun J274 =>
          Expr.let_ (opCmp32 CmpOp.ne (Arg.var ld273) (Arg.var not_lit)) fun v277 =>
          Expr.jnz (Arg.var v277.1)
            (Expr.let_ (opI32 (OpCode.lshr i32) (Arg.var ld273) (@Arg.imm _ i32 1)) fun v278 =>
            Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var v278.1, ()) } fun v279 =>
            Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v279.1) (@Arg.imm _ i64 4)) fun v280 =>
            Expr.let_ (opI64 (OpCode.add i64) (Arg.var lvl) (Arg.var v280.1)) fun v281 =>
            Expr.load i32 (Arg.var v281.1) fun ld282 =>
            Expr.group (sig := [[i32]]) (fun _J283 =>
              Blocks.cons (fun b284 => Expr.jump J274.1 (Arg.var b284.1, ())) Blocks.nil)
              fun J283 =>
              Expr.let_ (opCmp32 CmpOp.ugt (Arg.var ld282) (Arg.var b268.1)) fun v285 =>
              Expr.jnz (Arg.var v285.1)
                (Expr.jump J283.1 (Arg.var ld282, ()))
                (Expr.jump J283.1 (Arg.var b268.1, ())))
            (Expr.jump J274.1 (Arg.var b268.1, ())))
        (Expr.jump J_done (Arg.var b268.1, ())))
      Blocks.nil)
    fun J267 => Expr.jump J267.1 (@Arg.imm _ i32 0, @Arg.imm _ i64 0, ())

@[expose] def s13LpReplScanSubExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (vals arena cbase3 limit : V i64) (r_init : Arg V i64)
    (def_lit : Arg V i32) (def_ok : Arg V Ty.bool)
    (J_out : L [i64, i32, Ty.bool]) : Expr V L rs :=
  Expr.group (sig := [[i64]]) (fun J =>
    Blocks.cons (fun r =>
      Expr.let_ (opCmp64 CmpOp.ult (Arg.var r.1) (Arg.var limit)) fun c_lt =>
      Expr.jnz (Arg.var c_lt.1)
        (Expr.let_ (opI64 (OpCode.add i64) (Arg.var cbase3) (Arg.var r.1)) fun idx =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var idx.1) (@Arg.imm _ i64 4)) fun off =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var off.1)) fun ap =>
        Expr.load i32 (Arg.var ap.1) fun cand =>
        Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var cand, ()) } fun c64 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var vals) (Arg.var c64.1)) fun vp =>
        Expr.load i8 (Arg.var vp.1) fun vc =>
        Expr.let_ { code := OpCode.trunc 32 8, args := (@Arg.imm _ i32 0, ()) } fun z8 =>
        Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var vc, ()) } fun vc32 =>
        Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var z8.1, ()) } fun z32 =>
        Expr.let_ (opCmp32 CmpOp.sge (Arg.var vc32.1) (Arg.var z32.1)) fun ok =>
        Expr.jnz (Arg.var ok.1)
          (Expr.jump J_out (Arg.var r.1, Arg.var cand, @Arg.imm _ Ty.bool true, ()))
          (Expr.let_ (opI64 (OpCode.add i64) (Arg.var r.1) (@Arg.imm _ i64 1)) fun r1 =>
          Expr.jump J.1 (Arg.var r1.1, ())))
        (Expr.jump J_out (Arg.var r.1, def_lit, def_ok, ())))
      Blocks.nil)
    fun J => Expr.jump J.1 (r_init, ())

@[expose] def s13LpReplDelExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (J_lp : L s13LpSig) (J_ovf : L (s13OvfSig isBeyond))
    (wstk arena delayed dlim : V i64) (not_lit cref other : V i32)
    (cbase3 : V i64) (te un uf tk1 p2 q di ri : V i64) (repl : V i32)
    (brk : Arg V i64) : Expr V L rs :=
  Expr.group (sig := [[i64, i64, Ty.bool, i32, i32, i32, i64]]) (fun _J160 =>
    Blocks.cons (fun b161 =>
      Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1, Arg.var p2,
        Arg.var b161.1, Arg.var b161.2.1, ()))
      Blocks.nil)
    fun J160 =>
    Expr.let_ (opCmp32 CmpOp.eq (Arg.var repl) (Arg.var not_lit)) fun v162 =>
    Expr.jnz (Arg.var v162.1)
      (Expr.let_ (opI64 (OpCode.mul i64) (Arg.var cbase3) (@Arg.imm _ i64 4)) fun v163 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v163.1)) fun v164 =>
      Expr.store (Arg.var other) (Arg.var v164.1) (
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var cbase3) (@Arg.imm _ i64 1)) fun v165 =>
      Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v165.1) (@Arg.imm _ i64 4)) fun v166 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v166.1)) fun v167 =>
      Expr.store (Arg.var repl) (Arg.var v167.1) (
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var cbase3) (Arg.var ri)) fun v168 =>
      Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v168.1) (@Arg.imm _ i64 4)) fun v169 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v169.1)) fun v170 =>
      Expr.store (Arg.var not_lit) (Arg.var v170.1) (
      Expr.let_ (opI64 (OpCode.mul i64) (Arg.var q) (@Arg.imm _ i64 4)) fun v171 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v171.1)) fun v172 =>
      Expr.store (Arg.var other) (Arg.var v172.1) (
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 1)) fun v173 =>
      Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v173.1) (@Arg.imm _ i64 4)) fun v174 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v174.1)) fun v175 =>
      Expr.store (Arg.var cref) (Arg.var v175.1) (
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 2)) fun v176 =>
      Expr.jump J160.1 (Arg.var v176.1, Arg.var di, @Arg.imm _ Ty.bool false,
        @Arg.imm _ i32 0, @Arg.imm _ i32 0, @Arg.imm _ i32 0, @Arg.imm _ i64 0, ())))))))
      (Expr.let_ (opCmp64 CmpOp.ult (Arg.var di) (Arg.var dlim)) fun v177 =>
      Expr.jnz (Arg.var v177.1)
        (Expr.let_ (opI64 (OpCode.mul i64) (Arg.var cbase3) (@Arg.imm _ i64 4)) fun v178 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v178.1)) fun v179 =>
        Expr.store (Arg.var other) (Arg.var v179.1) (
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var cbase3) (@Arg.imm _ i64 1)) fun v180 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v180.1) (@Arg.imm _ i64 4)) fun v181 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v181.1)) fun v182 =>
        Expr.store (Arg.var repl) (Arg.var v182.1) (
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var cbase3) (Arg.var ri)) fun v183 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v183.1) (@Arg.imm _ i64 4)) fun v184 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v184.1)) fun v185 =>
        Expr.store (Arg.var not_lit) (Arg.var v185.1) (
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var di) (@Arg.imm _ i64 4)) fun v186 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var delayed) (Arg.var v186.1)) fun v187 =>
        Expr.store (Arg.var repl) (Arg.var v187.1) (
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var di) (@Arg.imm _ i64 1)) fun v188 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v188.1) (@Arg.imm _ i64 4)) fun v189 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var delayed) (Arg.var v189.1)) fun v190 =>
        Expr.store (Arg.var other) (Arg.var v190.1) (
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var di) (@Arg.imm _ i64 2)) fun v191 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v191.1) (@Arg.imm _ i64 4)) fun v192 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var delayed) (Arg.var v192.1)) fun v193 =>
        Expr.store (Arg.var cref) (Arg.var v193.1) (
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var di) (@Arg.imm _ i64 3)) fun v194 =>
        Expr.jump J160.1 (Arg.var q, Arg.var v194.1, @Arg.imm _ Ty.bool false,
          @Arg.imm _ i32 0, @Arg.imm _ i32 0, @Arg.imm _ i32 0, @Arg.imm _ i64 0, ()))))))))
        (s13OvfJump isBeyond J_ovf (Arg.var te) (Arg.var un) (Arg.var uf) (Arg.var tk1)
          (Arg.var p2) (Arg.var q) (Arg.var di) brk (@Arg.imm _ Ty.bool true)
          (Arg.var repl) (Arg.var other) (Arg.var cref) (Arg.var ri)))

@[expose] def s13LpNoReplExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (h : V i64) (ignore_ref : Arg V i64)
    (J_lp : L s13LpSig) (J_ovf : L (s13OvfSig isBeyond))
    (vals wstk arena lvl rsns trl tpos flags phases : V i64)
    (cur_lvl32 : V i32) (rec_ph nonchrono : V Ty.bool)
    (not_lit nl_lvl w0 cref other : V i32) (vo : V i8) (cbase3 csz : V i64)
    (te un uf tk1 p2 q di : V i64) : Expr V L rs :=
  Expr.let_ (opI64 (OpCode.mul i64) (Arg.var q) (@Arg.imm _ i64 4)) fun v195 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v195.1)) fun v196 =>
  Expr.store (Arg.var w0) (Arg.var v196.1) (
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 1)) fun v197 =>
  Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v197.1) (@Arg.imm _ i64 4)) fun v198 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v198.1)) fun v199 =>
  Expr.store (Arg.var cref) (Arg.var v199.1) (
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 2)) fun v200 =>
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var cref, ()) } fun v201 =>
  Expr.let_ (opCmp64 CmpOp.eq (Arg.var v201.1) ignore_ref) fun v202 =>
  Expr.jnz (Arg.var v202.1)
    (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1, Arg.var p2,
      Arg.var v200.1, Arg.var di, ()))
    (Expr.let_ { code := OpCode.trunc 32 8, args := (@Arg.imm _ i32 0, ()) } fun v203 =>
    Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var vo, ()) } fun v204 =>
    Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var v203.1, ()) } fun v205 =>
    Expr.let_ (opCmp32 CmpOp.slt (Arg.var v204.1) (Arg.var v205.1)) fun v206 =>
    Expr.jnz (Arg.var v206.1)
      (match isBeyond, J_ovf with
      | true, _ =>
        Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1, Arg.var p2,
          Arg.var v200.1, Arg.var di, ())
      | false, J_ovf' =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var h) (@Arg.imm _ i64 528)) fun v207 =>
        Expr.store (@Arg.imm _ i64 2) (Arg.var v207.1) (
        Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var cref, ()) } fun v208 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var h) (@Arg.imm _ i64 176)) fun v209 =>
        Expr.store (Arg.var v208.1) (Arg.var v209.1) (
        s13OvfJump false J_ovf' (Arg.var te) (Arg.var un) (Arg.var uf) (Arg.var tk1)
          (Arg.var p2) (Arg.var v200.1) (Arg.var di) (@Arg.imm _ i64 1)
          (@Arg.imm _ Ty.bool false) (@Arg.imm _ i32 0) (@Arg.imm _ i32 0)
          (@Arg.imm _ i32 0) (@Arg.imm _ i64 0))))
      (Expr.let_ (opI64 (OpCode.add i64) (Arg.var tk1) (@Arg.imm _ i64 1)) fun v210 =>
      Expr.group (sig := [[i32]]) (fun _J211 =>
        Blocks.cons (fun b212 =>
          s13LpAssignTailExpr false J_lp vals lvl rsns trl tpos flags phases rec_ph nonchrono
            not_lit te un uf di v210.1 p2 v200.1 other b212.1 cref)
          Blocks.nil)
        fun J211 =>
        Expr.let_ (opCmp32 CmpOp.ult (Arg.var nl_lvl) (Arg.var cur_lvl32)) fun v266 =>
        Expr.jnz (Arg.var v266.1)
          (s13LpMaxLvlLoopExpr arena lvl other cbase3 csz J211.1)
          (Expr.jump J211.1 (Arg.var nl_lvl, ()))))))

@[expose] def s13LpScanExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (h : V i64) (ignore_ref : Arg V i64)
    (J_lp : L s13LpSig) (J_ovf : L (s13OvfSig isBeyond))
    (vals wstk arena lvl rsns trl tpos flags phases delayed : V i64)
    (dlim : V i64) (cur_lvl32 : V i32) (rec_ph nonchrono : V Ty.bool)
    (not_lit nl_lvl w0 cref other : V i32) (vo : V i8) (cbase3 tk1 : V i64)
    (te un uf p2 q di : V i64) (brk : Arg V i64) : Expr V L rs :=
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var cref, ()) } fun v136 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var v136.1) (@Arg.imm _ i64 2)) fun v137 =>
  Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v137.1) (@Arg.imm _ i64 4)) fun v138 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v138.1)) fun v139 =>
  Expr.load i32 (Arg.var v139.1) fun ld140 =>
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var ld140, ()) } fun v141 =>
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var cref, ()) } fun v142 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var v142.1) (@Arg.imm _ i64 1)) fun v143 =>
  Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v143.1) (@Arg.imm _ i64 4)) fun v144 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v144.1)) fun v145 =>
  Expr.load i32 (Arg.var v145.1) fun ld146 =>
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var ld146, ()) } fun v147 =>
  Expr.group (sig := [[i64]]) (fun _J148 =>
    Blocks.cons (fun b149 =>
      Expr.group (sig := [[i64, i32, Ty.bool]]) (fun _J150 =>
        Blocks.cons (fun b151 =>
          Expr.group (sig := [[i64, i32, Ty.bool]]) (fun _J152 =>
            Blocks.cons (fun b153 =>
              Expr.jnz (Arg.var b153.2.2.1)
                (Expr.let_ (opI64 (OpCode.add i64) (Arg.var tk1) (@Arg.imm _ i64 1)) fun v154 =>
                Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var cref, ()) } fun v155 =>
                Expr.let_ (opI64 (OpCode.add i64) (Arg.var v155.1) (@Arg.imm _ i64 1)) fun v156 =>
                Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v156.1) (@Arg.imm _ i64 4)) fun v157 =>
                Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v157.1)) fun v158 =>
                Expr.let_ { code := OpCode.trunc 64 32, args := (Arg.var b153.1, ()) } fun v159 =>
                Expr.store (Arg.var v159.1) (Arg.var v158.1) (
                s13LpReplDelExpr isBeyond J_lp J_ovf wstk arena delayed dlim not_lit cref other
                  cbase3 te un uf v154.1 p2 q di b153.1 b153.2.1 brk))
                (s13LpNoReplExpr isBeyond h ignore_ref J_lp J_ovf vals wstk arena lvl rsns trl
                  tpos flags phases cur_lvl32 rec_ph nonchrono not_lit nl_lvl w0 cref other vo
                  cbase3 v141.1 te un uf tk1 p2 q di))
              Blocks.nil)
            fun J152 =>
            Expr.jnz (Arg.var b151.2.2.1)
              (Expr.jump J152.1 (Arg.var b151.1, Arg.var b151.2.1, Arg.var b151.2.2.1, ()))
              (Expr.group (sig := [[i64, i32, Ty.bool]]) (fun _J286 =>
                Blocks.cons (fun b287 =>
                  Expr.jump J152.1 (Arg.var b287.1, Arg.var b287.2.1, Arg.var b287.2.2.1, ()))
                  Blocks.nil)
                fun J286 =>
                s13LpReplScanSubExpr vals arena cbase3 b149.1 (@Arg.imm _ i64 2)
                  (Arg.var b151.2.1) (Arg.var b151.2.2.1) J286.1))
          Blocks.nil)
        fun J150 =>
        s13LpReplScanSubExpr vals arena cbase3 v141.1 (Arg.var b149.1)
          (@Arg.imm _ i32 0) (@Arg.imm _ Ty.bool false) J150.1)
      Blocks.nil)
    fun J148 =>
    Expr.let_ (opCmp64 CmpOp.ult (Arg.var v147.1) (@Arg.imm _ i64 2)) fun v318 =>
    Expr.jnz (Arg.var v318.1)
      (Expr.jump J148.1 (@Arg.imm _ i64 2, ()))
      (Expr.let_ (opCmp64 CmpOp.uge (Arg.var v147.1) (Arg.var v141.1)) fun v319 =>
      Expr.jnz (Arg.var v319.1)
        (Expr.jump J148.1 (@Arg.imm _ i64 2, ()))
        (Expr.jump J148.1 (Arg.var v147.1, ())))

@[expose] def s13LpLargeStepExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (h : V i64) (ignore_ref : Arg V i64)
    (J_lp : L s13LpSig) (J_ovf : L (s13OvfSig isBeyond))
    (vals wstk arena lvl rsns trl tpos flags phases delayed : V i64)
    (dlim two_cv : V i64) (cur_lvl32 : V i32) (rec_ph nonchrono : V Ty.bool)
    (not_lit nl_lvl w0 : V i32) (te un uf tk p q di : V i64) (brk : Arg V i64) :
    Expr V L rs :=
  Expr.group (sig := [[]]) (fun _J96 =>
    Blocks.cons (fun _ =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var p) (@Arg.imm _ i64 1)) fun v98 =>
      Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v98.1) (@Arg.imm _ i64 4)) fun v99 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v99.1)) fun v100 =>
      Expr.load i32 (Arg.var v100.1) fun ld101 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var p) (@Arg.imm _ i64 2)) fun v102 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var tk) (@Arg.imm _ i64 1)) fun v103 =>
      Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var ld101, ()) } fun v104 =>
      Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v104.1) (@Arg.imm _ i64 4)) fun v105 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v105.1)) fun v106 =>
      Expr.load i32 (Arg.var v106.1) fun ld107 =>
      Expr.let_ (opI32 (OpCode.and i32) (Arg.var ld107) (@Arg.imm _ i32 524288)) fun v108 =>
      Expr.let_ (opCmp32 CmpOp.ne (Arg.var v108.1) (@Arg.imm _ i32 0)) fun v109 =>
      Expr.jnz (Arg.var v109.1)
        (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var v103.1, Arg.var v102.1,
          Arg.var q, Arg.var di, ()))
        (Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var ld101, ()) } fun v110 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var v110.1) (@Arg.imm _ i64 3)) fun v111 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v111.1) (@Arg.imm _ i64 4)) fun v112 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v112.1)) fun v113 =>
        Expr.load i32 (Arg.var v113.1) fun ld114 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var v111.1) (@Arg.imm _ i64 1)) fun v115 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v115.1) (@Arg.imm _ i64 4)) fun v116 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var arena) (Arg.var v116.1)) fun v117 =>
        Expr.load i32 (Arg.var v117.1) fun ld118 =>
        Expr.group (sig := [[]]) (fun _J119 =>
          Blocks.cons (fun _ =>
            Expr.let_ (opI32 (OpCode.xor i32) (Arg.var ld114) (Arg.var ld118)) fun v121 =>
            Expr.let_ (opI32 (OpCode.xor i32) (Arg.var v121.1) (Arg.var not_lit)) fun v122 =>
            Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var v122.1, ()) } fun v123 =>
            Expr.let_ (opI64 (OpCode.add i64) (Arg.var vals) (Arg.var v123.1)) fun v124 =>
            Expr.load i8 (Arg.var v124.1) fun ld125 =>
            Expr.let_ { code := OpCode.trunc 32 8, args := (@Arg.imm _ i32 0, ()) } fun v126 =>
            Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var ld125, ()) } fun v127 =>
            Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var v126.1, ()) } fun v128 =>
            Expr.let_ (opCmp32 CmpOp.sgt (Arg.var v127.1) (Arg.var v128.1)) fun v129 =>
            Expr.jnz (Arg.var v129.1)
              (Expr.let_ (opI64 (OpCode.mul i64) (Arg.var q) (@Arg.imm _ i64 4)) fun v130 =>
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v130.1)) fun v131 =>
              Expr.store (Arg.var v122.1) (Arg.var v131.1) (
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 1)) fun v132 =>
              Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v132.1) (@Arg.imm _ i64 4)) fun v133 =>
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v133.1)) fun v134 =>
              Expr.store (Arg.var ld101) (Arg.var v134.1) (
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 2)) fun v135 =>
              Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var v103.1,
                Arg.var v102.1, Arg.var v135.1, Arg.var di, ()))))
              (s13LpScanExpr isBeyond h ignore_ref J_lp J_ovf vals wstk arena lvl rsns trl tpos
                flags phases delayed dlim cur_lvl32 rec_ph nonchrono not_lit nl_lvl w0 ld101
                v122.1 ld125 v111.1 v103.1 te un uf v102.1 q di brk))
            Blocks.nil)
          fun J119 =>
          Expr.let_ (opCmp32 CmpOp.ne (Arg.var ld114) (Arg.var not_lit)) fun v320 =>
          Expr.jnz (Arg.var v320.1)
            (Expr.let_ (opCmp32 CmpOp.ne (Arg.var ld118) (Arg.var not_lit)) fun v321 =>
            Expr.jnz (Arg.var v321.1)
              (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var v103.1,
                Arg.var v102.1, Arg.var q, Arg.var di, ()))
              (Expr.jump J119.1 ()))
            (Expr.jump J119.1 ())))
      Blocks.nil)
    fun J96 =>
    Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var w0, ()) } fun v322 =>
    Expr.let_ (opCmp64 CmpOp.ult (Arg.var v322.1) (Arg.var two_cv)) fun v323 =>
    Expr.jnz (Arg.var v323.1)
      (Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var w0, ()) } fun v324 =>
      Expr.let_ (opI64 (OpCode.add i64) (Arg.var vals) (Arg.var v324.1)) fun v325 =>
      Expr.load i8 (Arg.var v325.1) fun ld326 =>
      Expr.let_ { code := OpCode.trunc 32 8, args := (@Arg.imm _ i32 0, ()) } fun v327 =>
      Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var ld326, ()) } fun v328 =>
      Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var v327.1, ()) } fun v329 =>
      Expr.let_ (opCmp32 CmpOp.sgt (Arg.var v328.1) (Arg.var v329.1)) fun v330 =>
      Expr.jnz (Arg.var v330.1)
        (Expr.let_ (opI64 (OpCode.add i64) (Arg.var p) (@Arg.imm _ i64 1)) fun v331 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v331.1) (@Arg.imm _ i64 4)) fun v332 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v332.1)) fun v333 =>
        Expr.load i32 (Arg.var v333.1) fun ld334 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var p) (@Arg.imm _ i64 2)) fun v335 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var q) (@Arg.imm _ i64 4)) fun v336 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v336.1)) fun v337 =>
        Expr.store (Arg.var w0) (Arg.var v337.1) (
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 1)) fun v338 =>
        Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v338.1) (@Arg.imm _ i64 4)) fun v339 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v339.1)) fun v340 =>
        Expr.store (Arg.var ld334) (Arg.var v340.1) (
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 2)) fun v341 =>
        Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk, Arg.var v335.1,
          Arg.var v341.1, Arg.var di, ()))))
        (Expr.jump J96.1 ()))
      (Expr.jump J96.1 ())

@[expose] def s13LpLoopExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (h : V i64) (ignore_ref : Arg V i64)
    (vals wstk arena lvl rsns trl tpos flags phases delayed : V i64)
    (dlim two_cv : V i64) (cur_lvl32 : V i32) (rec_ph nonchrono : V Ty.bool)
    (not_lit nl_lvl : V i32) (te0 un0 uf0 tk0 p0 q0 end_v di0 : V i64)
    (brk0 : Arg V i64) (J_ovf : L (s13OvfSig isBeyond)) : Expr V L rs :=
  Expr.group (sig := [s13LpSig]) (fun J0 =>
    Blocks.cons (fun b1 =>
      Expr.let_ (opCmp64 CmpOp.ult (Arg.var b1.2.2.2.2.1) (Arg.var end_v)) fun v2 =>
      Expr.jnz (Arg.var v2.1)
        (Expr.let_ (opI64 (OpCode.mul i64) (Arg.var b1.2.2.2.2.1) (@Arg.imm _ i64 4)) fun v3 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v3.1)) fun v4 =>
        Expr.load i32 (Arg.var v4.1) fun ld5 =>
        Expr.let_ (opI32 (OpCode.and i32) (Arg.var ld5) (@Arg.imm _ i32 2147483648)) fun v6 =>
        Expr.let_ (opCmp32 CmpOp.ne (Arg.var v6.1) (@Arg.imm _ i32 0)) fun v7 =>
        Expr.jnz (Arg.var v7.1)
          (s13LpBinStepExpr isBeyond h J0.1 J_ovf vals wstk lvl rsns trl tpos flags phases
            rec_ph nonchrono not_lit nl_lvl ld5 b1.1 b1.2.1 b1.2.2.1 b1.2.2.2.1
            b1.2.2.2.2.1 b1.2.2.2.2.2.1 b1.2.2.2.2.2.2.1)
          (s13LpLargeStepExpr isBeyond h ignore_ref J0.1 J_ovf vals wstk arena lvl rsns trl tpos
            flags phases delayed dlim two_cv cur_lvl32 rec_ph nonchrono not_lit nl_lvl ld5
            b1.1 b1.2.1 b1.2.2.1 b1.2.2.2.1 b1.2.2.2.2.1 b1.2.2.2.2.2.1
            b1.2.2.2.2.2.2.1 brk0))
        (s13OvfJump isBeyond J_ovf (Arg.var b1.1) (Arg.var b1.2.1) (Arg.var b1.2.2.1)
          (Arg.var b1.2.2.2.1) (Arg.var b1.2.2.2.2.1) (Arg.var b1.2.2.2.2.2.1)
          (Arg.var b1.2.2.2.2.2.2.1) brk0 (@Arg.imm _ Ty.bool false)
          (@Arg.imm _ i32 0) (@Arg.imm _ i32 0) (@Arg.imm _ i32 0) (@Arg.imm _ i64 0)))
      Blocks.nil)
    fun J0 =>
    Expr.jump J0.1 (Arg.var te0, Arg.var un0, Arg.var uf0, Arg.var tk0, Arg.var p0, Arg.var q0,
      Arg.var di0, ())

section InnerLargeProofs

open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Std.Sat

private theorem s13_with_mem {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {e : Expr Val Cont rs} {m : Mem 64} {P : Mem 64 → Prop}
    (hp : P m) (hk : P m → wp Γ Q X e m) : wp Γ Q X e m := hk hp

private theorem s13_fastPropMem_with_delayed (s0 sem : FullState) (dl' : List (BitVec 32)) :
    { fastPropMem s0 sem with
      scratch := { (fastPropMem s0 sem).scratch with delayed := dl' } } =
      fastPropMem s0 { core := sem.core, scratch := { sem.scratch with delayed := dl' } } := by
  simp [fastPropMem]

private theorem s13_arena_lit_mem {k : FullCoreState} {cref r : Nat}
    (hr : r < fullArenaClauseSizeCore k cref)
    (hle : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length) :
    (k.arena[cref + 3 + r]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore k cref := by
  have h1 : cref + 3 + r < k.arena.length := by omega
  have h2 : r < (List.take (fullArenaClauseSizeCore k cref)
      (List.drop (cref + 3) k.arena)).length := by
    simp [List.length_take, List.length_drop]; omega
  refine List.mem_map.mpr ⟨k.arena[cref + 3 + r]'h1, ?_, ?_⟩
  · have := List.getElem_mem h2
    simp only [List.getElem_take, List.getElem_drop] at this
    exact this
  · simp [List.getElem?_eq_getElem h1]

private theorem s13_mem_arena_lit_ex {k : FullCoreState} {cref l : Nat}
    (hle : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length)
    (hl : l ∈ fullArenaClauseLitsCore k cref) :
    ∃ r, r < fullArenaClauseSizeCore k cref ∧
      (k.arena[cref + 3 + r]?.getD 0#32).toNat = l := by
  rcases List.mem_map.mp hl with ⟨w, hw, rfl⟩
  rcases List.getElem_of_mem hw with ⟨r, hr, rfl⟩
  have hrcsz : r < fullArenaClauseSizeCore k cref := by
    rw [List.length_take] at hr; exact Nat.lt_of_lt_of_le hr (Nat.min_le_left _ _)
  have h1 : cref + 3 + r < k.arena.length := by omega
  refine ⟨r, hrcsz, ?_⟩
  simp [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem h1]

private theorem s13_large_false_lvl_le {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {l : Nat} (hl_lt : l < 2 * k.cur_vars)
    (hval_f : k.vals[l]?.getD 0#8 = 255#8) :
    (k.lvl[l / 2]?.getD 0#32).toNat ≤ k.cur_level := by
  have hex : ∃ idx, idx < k.trail_end ∧ (k.trl[idx]?.getD 0#32).toNat = l ^^^ 1 := by
    have h1 := (hnw.vals_false_iff l (by simpa [withEmptyWatchesCore] using hl_lt)).mp
      (by simpa [withEmptyWatchesCore] using hval_f)
    simpa [withEmptyWatchesCore] using h1
  rcases hex with ⟨idx, hidx, htrl⟩
  have hle := hnw.lvl_le idx (by simpa [withEmptyWatchesCore] using hidx)
  have hdiv : (l ^^^ 1) / 2 = l / 2 := nat_xor1_div2 l
  simpa [withEmptyWatchesCore, htrl, hdiv] using hle

private theorem s13_ovf_confl_large_body {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ignore_ref : BitVec 64} {s_disk s_pi0 sem0 sem : FullState}
    {del0 : List (BitVec 32)} {dlen : Nat}
    {not_lit cref : BitVec 32} {off_v end_v brk0 te un uf tk p2 q2 di : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = sem.core.cur_vars)
    (hsd_pr : sem.core.propagated ≤ s_disk.core.trail_end)
    (hs0_cv : sem.core.cur_vars = sem0.core.cur_vars)
    (hs0_pr : sem.core.propagated = sem0.core.propagated)
    (hs0_dl : sem.scratch.delayed_len = sem0.scratch.delayed_len)
    (hs0_tk : sem.scratch.search_ticks = sem0.scratch.search_ticks)
    (hs0_oom : sem.core.oom = sem0.core.oom)
    (hdel : Spec.DelayedWatchesOk sem.core del0 dlen not_lit.toNat)
    (hdel_eq : c.delayed_cap = 0 → del0 = s_pi0.scratch.delayed)
    (hte : te.toNat = sem.core.trail_end) (hun : sem.core.unassigned = un)
    (huf : sem.core.unflushed = uf)
    (hdi_eq : di.toNat = 3 * dlen) (hdlen_le : dlen ≤ c.delayed_cap)
    (hpi : PropLitInv c F0 F_cur { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
      sem not_lit.toNat off_v.toNat q2.toNat p2.toNat end_v.toNat)
    (hcref_ref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hcref_ng : fullArenaClauseGarbCore sem.core cref.toNat = false)
    (hfls : ∀ l, l ∈ fullArenaClauseLitsCore sem.core cref.toNat →
      sem.core.vals[l]?.getD 0#8 = 255#8)
    (hne_ign : BitVec.setWidth 64 cref ≠ ignore_ref) (hbrk0 : brk0 = 0#64)
    (hm : (FullMem c (fastPropMem s_disk {
      core := { sem.core with confl_ref := BitVec.setWidth 64 cref, confl_type := 2#64 },
      scratch := sem.scratch }) ⋆ R) m) :
    S13OvfBody false c F0 F_cur ignore_ref s_disk s_pi0 sem0 not_lit off_v end_v brk0 R
      te un uf tk p2 q2 di 1#64 false 0#32 0#32 0#32 0#64 m := by
  let sem2 : FullState := {
    core := { sem.core with confl_ref := BitVec.setWidth 64 cref, confl_type := 2#64 },
    scratch := sem.scratch }
  have hc_res := propLit_large_confl hpi hcref_ref hcref_ng hfls
  have hconfl2 : PropLitConfl F_cur ignore_ref sem2.core := ⟨hc_res.2, fun _ => hne_ign⟩
  have hdel2 : Spec.DelayedWatchesOk sem2.core del0 dlen not_lit.toNat := by
    intro j hj; simpa [Spec.DelayedWatchesOk, sem2, fullArenaClauseRefsCore] using hdel j hj
  exact ⟨sem2, del0, dlen, hm, hc_res.1, hdel2, hdel_eq, hte.symm,
    hun, huf, hdi_eq, hdlen_le, hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hsd_len,
    hsd_cv.trans hs0_cv, hsd_pr, by simpa [hbrk0] using hconfl2⟩

private theorem s13_lits_xor_other {l0 l1 not_lit : BitVec 32}
    (hl : l0 = not_lit ∨ l1 = not_lit) :
    (l0 = not_lit ∧ l0 ^^^ l1 ^^^ not_lit = l1) ∨
      (l1 = not_lit ∧ l0 ^^^ l1 ^^^ not_lit = l0) := by
  rcases hl with rfl | rfl
  · exact Or.inl ⟨rfl, fid_xor_cancel_l l0 l1⟩
  · exact Or.inr ⟨rfl, fid_xor_cancel_r l0 l1⟩

private def S13MaxLvlInv (sem : FullState) (cref skip_lit : BitVec 32)
    (csz : BitVec 64) (acc : BitVec 32) (k : BitVec 64) : Prop :=
  k.toNat ≤ csz.toNat ∧
    (∀ r, r < k.toNat →
      let lit := sem.core.arena[cref.toNat + 3 + r]?.getD 0#32
      lit.toNat ≠ skip_lit.toNat →
        (sem.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ acc.toNat) ∧
    (acc = 0#32 ∨ ∃ r, r < k.toNat ∧
      let lit := sem.core.arena[cref.toNat + 3 + r]?.getD 0#32
      lit.toNat ≠ skip_lit.toNat ∧ acc = sem.core.lvl[lit.toNat / 2]?.getD 0#32)

theorem s13_lp_max_lvl_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {s_disk sem1 : FullState}
    {cref skip_lit : BitVec 32} {cbase3 csz : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost} {J_done : Cont [i32]}
    (_hfp_len : (fastPropMem s_disk sem1).LengthsOk c)
    (hlen1 : sem1.LengthsOk c)
    (hcbase : cbase3.toNat = cref.toNat + 3)
    (hcsz : csz.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (hcref_end :
      cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hlits_lt : ∀ r, r < fullArenaClauseSizeCore sem1.core cref.toNat →
      (sem1.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat < 2 * sem1.core.cur_vars)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_done : ∀ (alvl : BitVec 32),
      (∀ l, l ∈ fullArenaClauseLitsCore sem1.core cref.toNat → l ≠ skip_lit.toNat →
        (sem1.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat) →
      (alvl = 0#32 ∨ ∃ l, l ∈ fullArenaClauseLitsCore sem1.core cref.toNat ∧
        l ≠ skip_lit.toNat ∧ alvl = sem1.core.lvl[l / 2]?.getD 0#32) →
      wp Γ Q X (Expr.jump J_done (Arg.var alvl, ())) m) :
    wp Γ Q X (s13LpMaxLvlLoopExpr c.pArena c.pLevel skip_lit cbase3 csz J_done) m := by
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  have haren : c.arena_cap < 2 * dimacsBound := c.harena
  have hdim : dimacsBound = 268435456 := rfl
  have hcv_le : sem1.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
  have har_len : sem1.core.arena.length = c.arena_cap := hlen1.core_ok.arena_len_arr
  have har_le : sem1.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
  have hcsz_bnd : cref.toNat + 3 + csz.toNat ≤ sem1.core.arena.length := by omega
  have hcsz_ar : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤
      sem1.core.arena.length := by rw [← hcsz]; exact hcsz_bnd
  dsimp only [s13LpMaxLvlLoopExpr]
  refine wp_loop_group (fun n (xs : Tup Val [i32, i64]) m' =>
    m' = m ∧ n = csz.toNat - xs.2.1.toNat ∧ S13MaxLvlInv sem1 cref skip_lit csz xs.1 xs.2.1) ?_ ?_
  · intro J267 n ⟨acc, k, _⟩ m' hrec ⟨hm'_eq, hn_eq, hk_le, hacc_ge, hacc_ex⟩
    subst m'
    dsimp only at hn_eq hk_le hacc_ge hacc_ex
    s13_hstraight
    s13_hsplit
    · have hk_lt : k.toNat < csz.toNat := by simpa using hc
      clear hc
      have hcbase_k : (cbase3 + k).toNat = cref.toNat + 3 + k.toNat := by
        rw [m7_bv64_add_toNat (by omega), hcbase]
      have hcbase_lt : (cbase3 + k).toNat < (fastPropMem s_disk sem1).core.arena.length := by
        rw [BcpPropTactics.fastPropMem_arena, har_len]; omega
      s13_hstraight
      have har_get : ∀ h_pf, (fastPropMem s_disk sem1).core.arena[(cbase3 + k).toNat]'h_pf =
          sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32 := by
        intro h_pf
        have h1 : cref.toNat + 3 + k.toNat < sem1.core.arena.length := by omega
        rw [List.getElem?_eq_getElem h1, Option.getD_some]
        exact fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_arena s_disk sem1) hcbase_k _ _
      apply wp_join_group (fun (xs : Tup Val [i32]) m_j =>
        m_j = m ∧ S13MaxLvlInv sem1 cref skip_lit csz xs.1 (k + 1#64))
      · intro _ b275 m_j ⟨hmj_eq, hinv'⟩
        subst m_j
        s13_hstraight
        have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1_toNat (by omega)
        exact hrec (csz.toNat - (k + 1#64).toNat) (b275.1, k + 1#64, ()) m (by rw [hk1]; omega)
          ⟨rfl, rfl, hinv'⟩
      · intro J274 hP274
        have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1_toNat (by omega)
        s13_hstraight
        rw [har_get]
        s13_hsplit
        · have hne : sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32 ≠ skip_lit := by
            simpa using hc
          clear hc
          have hlit_lt : (sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32).toNat <
              2 * sem1.core.cur_vars :=
            hlits_lt k.toNat (by omega)
          have hlit_r :
              (BitVec.setWidth 64
                ((sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32) >>> 1)).toNat =
                (sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32).toNat / 2 := by
            simp only [BitVec.toNat_setWidth]
            rw [Nat.mod_eq_of_lt (by omega)]
            exact m7_bv32_rshift1_toNat _
          have hlvl_lt :
              (BitVec.setWidth 64
                ((sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32) >>> 1)).toNat <
                (fastPropMem s_disk sem1).core.lvl.length := by
            rw [hlit_r, BcpPropTactics.fastPropMem_lvl, hlen1.core_ok.lvl_len]; omega
          s13_hstraight
          have hlvl_get : ∀ h_pf,
              (fastPropMem s_disk sem1).core.lvl[(BitVec.setWidth 64
                ((sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32) >>> 1)).toNat]'h_pf =
                sem1.core.lvl[(sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32).toNat /
                  2]?.getD 0#32 := by
            intro h_pf
            have hlv_lt2 : (sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32).toNat / 2 <
                sem1.core.lvl.length := by
              rw [hlen1.core_ok.lvl_len]; omega
            rw [List.getElem?_eq_getElem hlv_lt2, Option.getD_some]
            exact fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_lvl s_disk sem1) hlit_r _ _
          have hne' : (sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32).toNat ≠
              skip_lit.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
          apply wp_join_group (fun (xs : Tup Val [i32]) m_j =>
            m_j = m ∧ S13MaxLvlInv sem1 cref skip_lit csz xs.1 (k + 1#64))
          · intro _ b284 m_j ⟨hmj_eq, hinv'⟩
            subst m_j; s13_hstraight; exact hP274 b284 m ⟨rfl, hinv'⟩
          · intro J283 hP283
            s13_hstraight
            rw [hlvl_get]
            s13_hsplit
            · have hgt : acc.toNat <
                  (sem1.core.lvl[(sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32).toNat /
                    2]?.getD 0#32).toNat := by simpa using hc
              clear hc; s13_hstraight; apply hP283
              refine ⟨rfl, hk1 ▸ Nat.succ_le_of_lt hk_lt, fun r hr => ?_,
                Or.inr ⟨k.toNat, ?_, hne', rfl⟩⟩
              · rw [hk1] at hr
                rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
                · exact fun hn => Nat.le_trans (hacc_ge r hlt hn) (Nat.le_of_lt hgt)
                · exact fun _ => Nat.le_refl _
              · rw [hk1]; omega
            · have hle :
                  (sem1.core.lvl[(sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32).toNat /
                    2]?.getD 0#32).toNat ≤ acc.toNat := by simpa using hc
              clear hc; s13_hstraight; apply hP283
              refine ⟨rfl, hk1 ▸ Nat.succ_le_of_lt hk_lt, fun r hr => ?_, ?_⟩
              · rw [hk1] at hr
                rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
                · exact hacc_ge r hlt
                · exact fun _ => hle
              · rcases hacc_ex with rfl | ⟨r0, hr0, hne0, heq0⟩
                · exact Or.inl rfl
                · exact Or.inr ⟨r0, hk1 ▸ Nat.lt_succ_of_lt hr0, hne0, heq0⟩
        · have heq : sem1.core.arena[cref.toNat + 3 + k.toNat]?.getD 0#32 = skip_lit := by
            simpa using hc
          clear hc; s13_hstraight; apply hP274
          refine ⟨rfl, hk1 ▸ Nat.succ_le_of_lt hk_lt, fun r hr hn => ?_, ?_⟩
          · rw [hk1] at hr
            rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
            · exact hacc_ge r hlt hn
            · exact absurd (congrArg BitVec.toNat heq) hn
          · rcases hacc_ex with rfl | ⟨r0, hr0, hne0, heq0⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨r0, hk1 ▸ Nat.lt_succ_of_lt hr0, hne0, heq0⟩
    · have hk_ge : csz.toNat ≤ k.toNat := by simpa using hc
      have hk_eq : k.toNat = csz.toNat := by omega
      s13_hstraight
      apply hJ_done acc
      · intro l hl hne
        rcases s13_mem_arena_lit_ex hcsz_ar hl with ⟨r, hr, rfl⟩
        exact hacc_ge r (by rw [hk_eq, hcsz]; exact hr) hne
      · rcases hacc_ex with rfl | ⟨r, hr, hne, heq⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨_, s13_arena_lit_mem (by rw [← hcsz, ← hk_eq]; exact hr) hcsz_ar,
            hne, heq⟩
  · intro J267 hP267
    s13_hstraight
    exact hP267 csz.toNat (0#32, 0#64, ()) m
      ⟨rfl, by simp, Nat.zero_le _, fun _ hr => by simp at hr, Or.inl rfl⟩

theorem s13_lp_repl_scan_sub_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {s_disk sem1 : FullState}
    {cref : BitVec 32} {cbase3 limit : BitVec 64}
    {r_init_arg : Arg Val i64} {def_lit_arg : Arg Val i32} {def_ok_arg : Arg Val Ty.bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_out : Cont [i64, i32, Ty.bool]}
    {r_init : BitVec 64} {def_lit : BitVec 32} {def_ok : Bool}
    (hr_eval : r_init_arg = Arg.imm r_init ∨ r_init_arg = Arg.var r_init)
    (hdl_eval : def_lit_arg = Arg.imm def_lit ∨ def_lit_arg = Arg.var def_lit)
    (hdo_eval : def_ok_arg = Arg.imm def_ok ∨ def_ok_arg = Arg.var def_ok)
    (_hfp_len : (fastPropMem s_disk sem1).LengthsOk c)
    (hlen1 : sem1.LengthsOk c)
    (hcbase : cbase3.toNat = cref.toNat + 3)
    (hr_le_lim : r_init.toNat ≤ limit.toNat)
    (hlim_csz : limit.toNat ≤ fullArenaClauseSizeCore sem1.core cref.toNat)
    (hcref_end :
      cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hlits_lt : ∀ r0, r_init.toNat ≤ r0 → r0 < limit.toNat →
      (sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat < 2 * sem1.core.cur_vars)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_found : ∀ (r : BitVec 64) (cand : BitVec 32),
      r_init.toNat ≤ r.toNat → r.toNat < limit.toNat →
      sem1.core.arena[cref.toNat + 3 + r.toNat]? = some cand →
      cand.toNat < 2 * sem1.core.cur_vars →
      (BitVec.signExtend 32 (sem1.core.vals[cand.toNat]?.getD 0#8)).slt 0#32 = false →
      (∀ r0, r_init.toNat ≤ r0 → r0 < r.toNat →
        (BitVec.signExtend 32 (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r0]?.getD
          0#32).toNat]?.getD 0#8)).slt 0#32 = true) →
      wp Γ Q X (Expr.jump J_out (Arg.var r, Arg.var cand, Arg.imm true, ())) m)
    (hJ_none :
      (∀ r0, r_init.toNat ≤ r0 → r0 < limit.toNat →
        (BitVec.signExtend 32 (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r0]?.getD
          0#32).toNat]?.getD 0#8)).slt 0#32 = true) →
      wp Γ Q X (Expr.jump J_out (Arg.var limit, Arg.var def_lit, Arg.imm def_ok, ())) m) :
    wp Γ Q X (s13LpReplScanSubExpr c.pVals c.pArena cbase3 limit
      r_init_arg def_lit_arg def_ok_arg J_out) m := by
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  have haren : c.arena_cap < 2 * dimacsBound := c.harena
  have hdim : dimacsBound = 268435456 := rfl
  have hcv_le : sem1.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
  have har_len : sem1.core.arena.length = c.arena_cap := hlen1.core_ok.arena_len_arr
  have har_le : sem1.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
  have hvals_len : sem1.core.vals.length = 2 * c.max_vars := hlen1.core_ok.vals_len
  dsimp only [s13LpReplScanSubExpr]
  refine wp_loop_group (fun n (xs : Tup Val [i64]) m' =>
    m' = m ∧ n = limit.toNat - xs.1.toNat ∧
      r_init.toNat ≤ xs.1.toNat ∧ xs.1.toNat ≤ limit.toNat ∧
      (∀ r0, r_init.toNat ≤ r0 → r0 < xs.1.toNat →
        (BitVec.signExtend 32 (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r0]?.getD
          0#32).toNat]?.getD 0#8)).slt 0#32 = true)) ?_ ?_
  · intro J n ⟨r, ⟨⟩⟩ m' hrec ⟨hm'_eq, hn_eq, hr_ge, hr_le, hr_all⟩
    subst m'
    dsimp only at hn_eq hr_ge hr_le hr_all
    s13_hstraight
    s13_hsplit
    · have hr_lt : r.toNat < limit.toNat := by simpa using hc
      clear hc
      have hcbase_r : (cbase3 + r).toNat = cref.toNat + 3 + r.toNat := by
        rw [m7_bv64_add_toNat (by rw [hcbase]; omega), hcbase]
      have har_lt : (cbase3 + r).toNat < (fastPropMem s_disk sem1).core.arena.length := by
        rw [BcpPropTactics.fastPropMem_arena, har_len, hcbase_r]; omega
      have hcand_lt : (sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32).toNat <
          2 * sem1.core.cur_vars :=
        hlits_lt r.toNat hr_ge hr_lt
      have har_elem : ∀ h_pf, (fastPropMem s_disk sem1).core.arena[(cbase3 + r).toNat]'h_pf =
          sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32 := by
        intro h_pf
        have h1 : cref.toNat + 3 + r.toNat < sem1.core.arena.length := by omega
        rw [List.getElem?_eq_getElem h1, Option.getD_some]
        exact fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_arena s_disk sem1) hcbase_r _ _
      have hc64_eq :
          (BitVec.setWidth 64 (sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32)).toNat =
            (sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32).toNat := by
        simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
      have hvals_lt : ∀ h_pf,
          (BitVec.setWidth 64
            ((fastPropMem s_disk sem1).core.arena[(cbase3 + r).toNat]'h_pf)).toNat <
            (fastPropMem s_disk sem1).core.vals.length := by
        intro h_pf; rw [har_elem, hc64_eq, BcpPropTactics.fastPropMem_vals, hvals_len]; omega
      have hvals_lt' := hvals_lt har_lt
      have hcb_r_m : (cbase3.toNat + r.toNat) % 2 ^ 64 = cref.toNat + 3 + r.toNat := by
        rw [Nat.mod_eq_of_lt (by rw [hcbase]; omega), hcbase]
      have h_ar_m : ∀ h_pf,
          (fastPropMem s_disk sem1).core.arena[(cbase3.toNat + r.toNat) % 2 ^ 64]'h_pf =
            sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32 := by
        intro h_pf
        have h1 : cref.toNat + 3 + r.toNat < sem1.core.arena.length := by omega
        rw [List.getElem?_eq_getElem h1, Option.getD_some]
        exact fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_arena s_disk sem1) hcb_r_m _ _
      have hidx_m : ∀ h_pf,
          ((fastPropMem s_disk sem1).core.arena[(cbase3.toNat + r.toNat) % 2 ^ 64]'h_pf).toNat =
            (sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32).toNat := by
        intro h_pf; rw [h_ar_m]
      s13_hstraight
      have hv_elem : ∀ h1 h2,
          (fastPropMem s_disk sem1).core.vals[((fastPropMem s_disk sem1).core.arena[(cbase3.toNat +
            r.toNat) % 2 ^ 64]'h1).toNat]'h2 =
            sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32).toNat]?.getD
              0#8 := by
        intro h1 h2
        have h1_lt : (sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32).toNat <
            sem1.core.vals.length := by
          rw [hvals_len]; omega
        rw [List.getElem?_eq_getElem h1_lt, Option.getD_some]
        exact fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_vals s_disk sem1) (hidx_m h1) _ _
      s13_hsplit
      · have hok : (BitVec.signExtend 32 (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 +
            r.toNat]?.getD 0#32).toNat]?.getD 0#8)).slt 0#32 = false := by
          rw [hv_elem] at hc; simpa [BitVec.sle, BitVec.slt] using hc
        clear hc
        s13_hstraight
        try rw [har_elem]
        try rw [h_ar_m]
        have h1 : cref.toNat + 3 + r.toNat < sem1.core.arena.length := by omega
        have hsome : sem1.core.arena[cref.toNat + 3 + r.toNat]? =
            some (sem1.core.arena[cref.toNat + 3 + r.toNat]?.getD 0#32) := by
          simp [List.getElem?_eq_getElem h1]
        exact hJ_found r _ hr_ge hr_lt hsome hcand_lt hok hr_all
      · have hneg : (BitVec.signExtend 32 (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 +
            r.toNat]?.getD 0#32).toNat]?.getD 0#8)).slt 0#32 = true := by
          rw [hv_elem] at hc; simpa [BitVec.sle, BitVec.slt] using hc
        clear hc
        s13_hstraight
        have hr1 : (r + 1#64).toNat = r.toNat + 1 := m7_bv64_add1_toNat (by omega)
        have hr1_m : (r.toNat + 1) % 2 ^ 64 = r.toNat + 1 := Nat.mod_eq_of_lt (by omega)
        refine hrec (limit.toNat - (r + 1#64).toNat) (r + 1#64, ()) m (by rw [hr1]; omega)
          ⟨rfl, rfl, by dsimp; rw [hr1_m]; omega, by dsimp; rw [hr1_m]; omega,
            fun r0 h0 hlt => ?_⟩
        dsimp at hlt; rw [hr1_m] at hlt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
        · exact hr_all r0 h0 hlt'
        · exact hneg
    · have hr_ge_lim : limit.toNat ≤ r.toNat := by simpa using hc
      have hr_eq : r = limit := BitVec.eq_of_toNat_eq (by omega)
      subst r
      s13_hstraight
      rcases hdl_eval with rfl | rfl <;> rcases hdo_eval with rfl | rfl <;>
        exact hJ_none hr_all
  · intro J hP
    s13_hstraight
    rcases hr_eval with rfl | rfl <;>
      exact hP (limit.toNat - r_init.toNat) (r_init, ()) m
        ⟨rfl, rfl, by simp, by simpa using hr_le_lim,
          fun _ h0 hlt => absurd hlt (by simp at h0 ⊢; omega)⟩

theorem s13_lp_repl_del_wp {isBeyond : Bool} {Γ : Env} {rs : List Ty} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {s_disk s_pi0 sem0 sem1 : FullState}
    {del0 : List (BitVec 32)} {dlen : Nat}
    {not_lit cref other l0 l1 repl : BitVec 32}
    {cbase3 te un uf tk1 p2 q di ri off_v end_v brk0 : BitVec 64} {brk_arg : Arg Val i64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont s13LpSig} {J_ovf : Cont (s13OvfSig isBeyond)}
    (hbrk_eval : brk_arg = Arg.imm brk0 ∨ brk_arg = Arg.var brk0)
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = sem1.core.cur_vars)
    (hsd_pr : sem1.core.propagated ≤ s_disk.core.trail_end)
    (hs0_cv : sem1.core.cur_vars = sem0.core.cur_vars)
    (hs0_pr : sem1.core.propagated = sem0.core.propagated)
    (hs0_dl : sem1.scratch.delayed_len = sem0.scratch.delayed_len)
    (hs0_tk : sem1.scratch.search_ticks = sem0.scratch.search_ticks)
    (hs0_oom : sem1.core.oom = sem0.core.oom)
    (hs0_ct : S13ConflEq sem0.core sem1.core)
    (hdel_ok : Spec.DelayedWatchesOk sem1.core del0 dlen not_lit.toNat)
    (hdel_eq : c.delayed_cap = 0 → del0 = s_pi0.scratch.delayed)
    (hdi_eq : di.toNat = 3 * dlen) (hdlen_le : dlen ≤ c.delayed_cap)
    (hpi1 : PropLitInv c F0 F_cur { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
      sem1 not_lit.toNat off_v.toNat q.toNat p2.toNat end_v.toNat)
    (hp2_eq : ∃ p0 : BitVec 64, p2 = p0 + 2#64 ∧ p0.toNat + 2 = p2.toNat ∧ q.toNat ≤ p0.toNat)
    (_hnot_lt : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hcref_31 : cref.toNat < 2147483648)
    (hcref_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hcref_ng : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat)
    (hcref_end :
      cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hcbase : cbase3.toNat = cref.toNat + 3)
    (hl0 : sem1.core.arena[cref.toNat + 3]? = some l0)
    (hl1 : sem1.core.arena[cref.toNat + 4]? = some l1)
    (hnl_or : l0 = not_lit ∨ l1 = not_lit)
    (hoth : other = l0 ^^^ l1 ^^^ not_lit)
    (hri_ge2 : 2 ≤ ri.toNat)
    (hri_lt : ri.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (hrepl_ar : sem1.core.arena[cref.toNat + 3 + ri.toNat]? = some repl)
    (hrepl_lt : repl.toNat < 2 * sem1.core.cur_vars)
    (hrepl_ge0 : (BitVec.signExtend 32 (sem1.core.vals[repl.toNat]?.getD 0#8)).slt 0#32 = false)
    (hte : te.toNat = sem1.core.trail_end) (hun : sem1.core.unassigned = un)
    (huf : sem1.core.unflushed = uf)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_lp : ∀ (te' un' uf' tk' p' q' di' : BitVec 64) (sem' : FullState) (m' : Mem 64),
      S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem' not_lit off_v end_v te' un' uf' tk' p' q' di'
        m' R → p' = p2 →
      wp Γ Q X (Expr.jump J_lp (Arg.var te', Arg.var un', Arg.var uf', Arg.var tk',
        Arg.var p', Arg.var q', Arg.var di', ())) m')
    (hJ_ovf : ∀ (xs : Tup Val (s13OvfSig isBeyond)) (m' : Mem 64),
      S13OvfExitPred isBeyond c F0 F_cur ignore_ref s_disk s_pi0 sem0
        not_lit off_v end_v brk0 R xs m' → s13OvfP xs = p2 → J_ovf xs m') :
    wp Γ Q X (s13LpReplDelExpr isBeyond J_lp J_ovf c.pWstk c.pArena c.pDelayed
      (BitVec.ofNat 64 (3 * c.delayed_cap)) not_lit cref other cbase3
      te un uf tk1 p2 q di ri repl brk_arg) m := by
  let s_pi := { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  have haren : c.arena_cap < 2 * dimacsBound := c.harena
  have hdelc : c.delayed_cap < dimacsBound := c.hdel
  have hdim : dimacsBound = 268435456 := rfl
  have hcv_le : sem1.core.cur_vars ≤ c.max_vars := hpi1.len.core_ok.cur_vars_le
  have har_len : sem1.core.arena.length = c.arena_cap := hpi1.len.core_ok.arena_len_arr
  have har_le : sem1.core.arena_len ≤ c.arena_cap := hpi1.len.core_ok.arena_len_le
  have hfp1_len : (fastPropMem s_disk sem1).LengthsOk c :=
    fastPropMem_lengthsOk hsd_len hpi1.len hsd_cv hsd_pr rfl
  have hoth_lt : other.toNat < 2 * sem1.core.cur_vars := by
    have h_ar_end : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤
        sem1.core.arena.length := har_len ▸ Nat.le_trans hcref_end har_le
    rcases s13_lits_xor_other hnl_or with ⟨_, hoth_eq⟩ | ⟨_, hoth_eq⟩
    · rw [hoth, hoth_eq]
      have hm1 : (sem1.core.arena[cref.toNat + 3 + 1]?.getD 0#32).toNat ∈
          fullArenaClauseLitsCore (withEmptyWatchesCore c sem1.core) cref.toNat := by
        dsimp only [withEmptyWatchesCore]
        exact s13_arena_lit_mem (r := 1) (Nat.lt_of_lt_of_le (by decide) hcsz3) h_ar_end
      have h1 := hpi1.nw.arena.lits_lt cref.toNat hcref_ref hcref_ng _ hm1
      simpa [withEmptyWatchesCore, hl1] using h1
    · rw [hoth, hoth_eq]
      have hm0 : (sem1.core.arena[cref.toNat + 3 + 0]?.getD 0#32).toNat ∈
          fullArenaClauseLitsCore (withEmptyWatchesCore c sem1.core) cref.toNat := by
        dsimp only [withEmptyWatchesCore]
        exact s13_arena_lit_mem (r := 0) (Nat.lt_of_lt_of_le (by decide) hcsz3) h_ar_end
      have h0 := hpi1.nw.arena.lits_lt cref.toNat hcref_ref hcref_ng _ hm0
      simpa [withEmptyWatchesCore, hl0] using h0
  have hoth_mask : other &&& 2147483647#32 = other := m7_bv32_mask7f_eq (by omega)
  have hoth_31 : other.toNat < 2 ^ 31 := by omega
  have hrepl_ne : repl.toNat ≠ not_lit.toNat := by
    intro heq
    have hnf : sem1.core.vals[repl.toNat]?.getD 0#8 = 255#8 := by rw [heq]; exact hpi1.not_f
    have htr := propLit_vals_neg hpi1.nw (l := repl)
      (by simpa [withEmptyWatchesCore] using hrepl_lt) (by simpa [withEmptyWatchesCore] using hnf)
    have htr' : (BitVec.signExtend 32 (sem1.core.vals[repl.toNat]?.getD 0#8)).slt 0#32 = true := by
      simpa [withEmptyWatchesCore] using htr
    rw [hrepl_ge0] at htr'
    exact absurd htr' (by decide)
  dsimp only [s13LpReplDelExpr]
  apply wp_join_group (fun (xs : Tup Val [i64, i64, Ty.bool, i32, i32, i32, i64]) m' =>
    ∃ sem', S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem' not_lit off_v end_v
      te un uf tk1 p2 xs.1 xs.2.1 m' R)
  · intro _ b161 m' ⟨sem', hinv'⟩
    s13_hstraight; exact hJ_lp _ _ _ _ _ _ _ sem' m' hinv' rfl
  · intro J160 hP160
    s13_hstraight; s13_hsplit
    · exact absurd (congrArg BitVec.toNat (by simpa using hc)) hrepl_ne
    · clear hc
      have hdlim_toNat : (BitVec.ofNat 64 (3 * c.delayed_cap)).toNat = 3 * c.delayed_cap := by
        simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      s13_hstraight; s13_hsplit
      · have hdi_lt : dlen < c.delayed_cap := by
          have : di.toNat < (BitVec.ofNat 64 (3 * c.delayed_cap)).toNat := by simpa using hc
          omega
        clear hc
        rcases hp2_eq with ⟨p0, rfl, hp0_2, hqp0⟩
        have hcbase1 : (cbase3 + 1#64).toNat = cref.toNat + 4 := by
          rw [m7_bv64_add1_toNat (by omega), hcbase]
        have hcbase_ri : (cbase3 + ri).toNat = cref.toNat + 3 + ri.toNat := by
          rw [m7_bv64_add_toNat (by rw [hcbase]; omega), hcbase]
        have hcbase1_m : (cbase3.toNat + 1) % 2 ^ 64 = cref.toNat + 4 := by
          rw [Nat.mod_eq_of_lt (by rw [hcbase]; omega), hcbase]
        have hcb_ri_m : (cbase3.toNat + ri.toNat) % 2 ^ 64 = cref.toNat + 3 + ri.toNat := by
          rw [Nat.mod_eq_of_lt (by rw [hcbase]; omega), hcbase]
        have har_l0 : cbase3.toNat < (fastPropMem s_disk sem1).core.arena.length := by
          rw [BcpPropTactics.fastPropMem_arena, har_len]; omega
        have har_l1 : (cbase3 + 1#64).toNat <
            ((fastPropMem s_disk sem1).core.arena.set cbase3.toNat other).length := by
          rw [List.length_set, BcpPropTactics.fastPropMem_arena, har_len, hcbase1]; omega
        have har_lri : (cbase3 + ri).toNat <
            (((fastPropMem s_disk sem1).core.arena.set cbase3.toNat other).set
              (cbase3 + 1#64).toNat repl).length := by
          simp only [List.length_set, BcpPropTactics.fastPropMem_arena, har_len]
          rw [hcbase_ri]; omega
        have hdl_len : sem1.scratch.delayed.length = 3 * c.delayed_cap :=
          hpi1.len.scratch_ok.delayed_len_arr
        have hdel_l0 : di.toNat < (fastPropMem s_disk sem1).scratch.delayed.length := by
          rw [BcpPropTactics.fastPropMem_delayed, hdl_len]; omega
        have hdel_l1 : (di + 1#64).toNat <
            ((fastPropMem s_disk sem1).scratch.delayed.set di.toNat repl).length := by
          rw [List.length_set, BcpPropTactics.fastPropMem_delayed, hdl_len]
          rw [m7_bv64_add1_toNat (by omega)]; omega
        have hdel_l2 : (di + 2#64).toNat <
            (((fastPropMem s_disk sem1).scratch.delayed.set di.toNat repl).set
              (di + 1#64).toNat other).length := by
          simp only [List.length_set, BcpPropTactics.fastPropMem_delayed, hdl_len]
          rw [m7_bv64_add2_toNat (by omega)]; omega
        s13_hstraight
        have hpi1' : PropLitInv c F0 F_cur s_pi sem1 not_lit.toNat off_v.toNat
            q.toNat (p0.toNat + 2) end_v.toNat := hp0_2 ▸ hpi1
        have ⟨hnw3, hperm3, har3_0, har3_1, har3_ri⟩ := s13_unswapped_ar_swap_nw hpi1'.len.core_ok
          hpi1'.nw hcref_ref hcsz3 hcref_end hri_ge2 hri_lt hnl_or hoth hl0 hl1 hrepl_ar
        let ar' := ((sem1.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) repl).set
          (cref.toNat + 3 + ri.toNat) not_lit
        let st3 : FullState := { core := { sem1.core with arena := ar' }, scratch := sem1.scratch }
        have hlen3 : st3.LengthsOk c := by
          refine ⟨⟨hpi1.len.core_ok.vals_len, hpi1.len.core_ok.lit_mark_len,
            hpi1.len.core_ok.mrk_len, hpi1.len.core_ok.flags_len, hpi1.len.core_ok.lvl_len,
            hpi1.len.core_ok.rsns_len, hpi1.len.core_ok.trl_len, hpi1.len.core_ok.trail_pos_len,
            hpi1.len.core_ok.tmp_len_arr, hpi1.len.core_ok.min_clr_len_arr,
            hpi1.len.core_ok.frame_trail_len, hpi1.len.core_ok.frame_dec_len,
            hpi1.len.core_ok.wvec_len, hpi1.len.core_ok.repr_len, hpi1.len.core_ok.min_stk_len,
            by dsimp [st3, ar']; simp only [List.length_set]; exact har_len,
            hpi1.len.core_ok.wstk_len_arr,
            hpi1.len.core_ok.cur_vars_ge, hpi1.len.core_ok.cur_vars_le,
            hpi1.len.core_ok.arena_len_le, hpi1.len.core_ok.wlen_le, hpi1.len.core_ok.trail_end_le,
            hpi1.len.core_ok.propagated_le, hpi1.len.core_ok.tmp_len_le,
            hpi1.len.core_ok.min_clr_len_le⟩, hpi1.len.scratch_ok⟩
        have hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off_v.toNat q.toNat
            (p0.toNat + 2) end_v.toNat :=
          SplitWatchesInv.with_nonwatch hpi1'.sw rfl rfl rfl rfl
            (fun r hr => by rw [hperm3.2.1]; exact hr)
        have hperm3_pi : FullArenaPermEq s_pi.core st3.core := by
          have := hpi1.perm
          exact ⟨this.1, hperm3.2.1.trans this.2.1, fun r hr => by
            have h1 := hperm3.2.2 r (by rw [this.2.1]; exact hr)
            have h2 := this.2.2 r hr
            exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩⟩
        have hsc3 : st3.scratch = { s_pi.scratch with
            search_ticks := st3.scratch.search_ticks, phases := st3.scratch.phases,
            wsort := st3.scratch.wsort } := hpi1.sc_eq
        have hcref_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core := by
          rw [hperm3.2.1]; exact hcref_ref
        have hfd := fid_repl_delay_step (other := other) (ri_n := ri.toNat) hpi1' hdi_lt hlen3
          hnw3 hsw3 (by simpa [AgreesExcept, propLitCoreMask, st3] using hpi1.ag)
          (by simpa [FullTrailExt, st3] using hpi1.tr)
          (by simpa [Spec.FullTrailRsnsPres, st3] using hpi1.rsns_pres) hperm3_pi hsc3
          hpi1.not_f hdel_ok hrepl_lt hrepl_ne hcref_31 hcref_ref3
          (w0 := other) (by
            rw [← hoth_mask, BitVec.and_assoc,
              (by decide : (2147483647#32 &&& 2147483648#32) = 0#32), BitVec.and_zero])
        let del' := ((st3.scratch.delayed.set (3 * dlen) repl).set (3 * dlen + 1) other).set
          (3 * dlen + 2) cref
        let st4 : FullState := { core := st3.core, scratch := { st3.scratch with delayed := del' } }
        have hcbase1_v : (cbase3 + 1).toNat = cref.toNat + 4 := hcbase1
        have hdi1 : (di + 1).toNat = 3 * dlen + 1 := by
          change (di + 1#64).toNat = _
          rw [m7_bv64_add1_toNat (by rw [hdi_eq]; omega), hdi_eq]
        have hdi2 : (di + 2).toNat = 3 * dlen + 2 := by
          change (di + 2#64).toNat = _
          rw [m7_bv64_add2_toNat (by rw [hdi_eq]; omega), hdi_eq]
        have hdi1_m : (di.toNat + 1) % 2 ^ 64 = 3 * dlen + 1 := by
          rw [Nat.mod_eq_of_lt (by rw [hdi_eq]; omega), hdi_eq]
        have hdi2_m : (di.toNat + 2) % 2 ^ 64 = 3 * dlen + 2 := by
          rw [Nat.mod_eq_of_lt (by rw [hdi_eq]; omega), hdi_eq]
        have hdi3 : (di + 3#64).toNat = 3 * (dlen + 1) := by
          rw [m7_bv64_add_toNat (by simp only [hdi_eq, BitVec.toNat_ofNat]; omega), hdi_eq]
          simp only [BitVec.toNat_ofNat]; omega
        dsimp only at hm
        rw [BcpPropTactics.fastPropMem_arena] at hm
        try rw [hcbase, hcbase1, hcbase_ri] at hm
        try rw [hcbase, hcbase1_v, hcbase_ri] at hm
        try rw [hcbase, hcbase1_m, hcb_ri_m] at hm
        rw [← m7_fastPropMem_with_arena] at hm
        dsimp only at hm
        rw [BcpPropTactics.fastPropMem_delayed] at hm
        try rw [hdi_eq, hdi1, hdi2] at hm
        try rw [hdi_eq, hdi1_m, hdi2_m] at hm
        change (FullMem c (fastPropMem s_disk st4) ⋆ R) _ at hm
        have hpi4 : PropLitInv c F0 F_cur
            { s_pi0 with scratch := { s_pi0.scratch with delayed := del' } }
            st4 not_lit.toNat off_v.toNat q.toNat (p0 + 2#64).toNat end_v.toNat :=
          hp0_2 ▸ hfd.1
        apply hP160 (q, di + 3#64, false, 0#32, 0#32, 0#32, 0#64, ()) _
        refine ⟨st4, del', dlen + 1, hm, hpi4, hfd.2,
          fun hc0 => absurd hc0 (by omega), hte.symm, hun, huf, hdi3, hdi_lt,
          hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len,
          hsd_cv.trans hs0_cv, hsd_pr⟩
      · have hnot_lt_dl : c.delayed_cap ≤ dlen := by
          have hge : (BitVec.ofNat 64 (3 * c.delayed_cap)).toNat ≤ di.toNat := by simpa using hc
          omega
        clear hc
        rcases hp2_eq with ⟨p0, rfl, hp0_2, hqp0⟩
        cases isBeyond <;> rcases hbrk_eval with rfl | rfl <;>
          · s13_hstraight
            refine hJ_ovf _ _ ?_ rfl
            exact ⟨sem1, del0, dlen, hm, hpi1, hdel_ok, hdel_eq, hte.symm, hun, huf,
              hdi_eq, hdlen_le, hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom,
              hsd_len, hsd_cv.trans hs0_cv, hsd_pr,
              rfl, by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega, hs0_ct, hrepl_lt, hrepl_ne,
              hcref_31, hcref_ref, hcref_ng, hcsz3, hcref_end, hri_ge2, hri_lt,
              ⟨l0, l1, hl0, hl1, hnl_or, hoth, hrepl_ar⟩, hoth_mask⟩

private theorem s13_fastPropMem_with_wstk (s0 sem : FullState) (ws' : List (BitVec 32)) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with wstk := ws' } } =
      fastPropMem s0 { core := { sem.core with wstk := ws' }, scratch := sem.scratch } := by
  simp [fastPropMem]

theorem s13_lp_no_repl_wp {isBeyond : Bool} {Γ : Env} {rs : List Ty} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {ignore_arg : Arg Val i64} {s_disk s_pi0 sem0 sem1 : FullState}
    {del0 : List (BitVec 32)} {dlen : Nat}
    {not_lit nl_lvl w0 cref other l0 l1 : BitVec 32} {vo : BitVec 8}
    {cbase3 csz te un uf tk1 p2 q di : BitVec 64} {cur_lvl32 : BitVec 32}
    {rec_ph nonchrono : Bool} {off_v end_v brk0 : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont s13LpSig} {J_ovf : Cont (s13OvfSig isBeyond)}
    (hign_eval : ignore_arg = Arg.imm ignore_ref ∨ ignore_arg = Arg.var ignore_ref)
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = sem1.core.cur_vars)
    (hsd_pr : sem1.core.propagated ≤ s_disk.core.trail_end)
    (hs0_cv : sem1.core.cur_vars = sem0.core.cur_vars)
    (hs0_pr : sem1.core.propagated = sem0.core.propagated)
    (hs0_dl : sem1.scratch.delayed_len = sem0.scratch.delayed_len)
    (hs0_tk : sem1.scratch.search_ticks = sem0.scratch.search_ticks)
    (hs0_oom : sem1.core.oom = sem0.core.oom)
    (hs0_ct : S13ConflEq sem0.core sem1.core)
    (hdel_ok : Spec.DelayedWatchesOk sem1.core del0 dlen not_lit.toNat)
    (hdel_eq : c.delayed_cap = 0 → del0 = s_pi0.scratch.delayed)
    (hdi_eq : di.toNat = 3 * dlen) (hdlen_le : dlen ≤ c.delayed_cap)
    (hpi1 : PropLitInv c F0 F_cur { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
      sem1 not_lit.toNat off_v.toNat q.toNat p2.toNat end_v.toNat)
    (hp2_eq : ∃ p0 : BitVec 64, p2 = p0 + 2#64 ∧ p0.toNat + 2 = p2.toNat ∧ q.toNat ≤ p0.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hnl_lvl : nl_lvl = sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32)
    (hcur_lvl : cur_lvl32.toNat = sem1.core.cur_level)
    (hw0_msb : w0 &&& 2147483648#32 = 0#32)
    (hcref_31 : cref.toNat < 2147483648)
    (hcref_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hcref_ng : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat)
    (hcref_end :
      cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hcbase : cbase3.toNat = cref.toNat + 3)
    (hcsz : csz.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (hl0 : sem1.core.arena[cref.toNat + 3]? = some l0)
    (hl1 : sem1.core.arena[cref.toNat + 4]? = some l1)
    (hnl_or : l0 = not_lit ∨ l1 = not_lit)
    (hoth : other = l0 ^^^ l1 ^^^ not_lit)
    (hvo_eq : vo = sem1.core.vals[other.toNat]?.getD 0#8)
    (hvo_ng : (0#32).slt (BitVec.signExtend 32 vo) = false)
    (hall_neg : ∀ r, 2 ≤ r → r < fullArenaClauseSizeCore sem1.core cref.toNat →
      (BitVec.signExtend 32
        (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat]?.getD 0#8)).slt
          0#32 = true)
    (hte : te.toNat = sem1.core.trail_end) (hun : sem1.core.unassigned = un)
    (huf : sem1.core.unflushed = uf) (hbrk0 : brk0 = 0#64)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_lp : ∀ (te' un' uf' tk' p' q' di' : BitVec 64) (sem' : FullState) (m' : Mem 64),
      S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem' not_lit off_v end_v te' un' uf' tk' p' q' di'
        m' R → p' = p2 →
      wp Γ Q X (Expr.jump J_lp (Arg.var te', Arg.var un', Arg.var uf', Arg.var tk',
        Arg.var p', Arg.var q', Arg.var di', ())) m')
    (hJ_ovf : ∀ (xs : Tup Val (s13OvfSig isBeyond)) (m' : Mem 64),
      S13OvfExitPred isBeyond c F0 F_cur ignore_ref s_disk s_pi0 sem0
        not_lit off_v end_v brk0 R xs m' → s13OvfP xs = p2 → J_ovf xs m') :
    wp Γ Q X (s13LpNoReplExpr isBeyond c.hdr ignore_arg J_lp J_ovf c.pVals c.pWstk
      c.pArena c.pLevel c.pReason c.pTrail c.pTrailPos c.pFlags c.pPhases
      cur_lvl32 rec_ph nonchrono not_lit nl_lvl w0 cref other vo cbase3 csz
      te un uf tk1 p2 q di) m := by
  let s_pi := { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  have haren : c.arena_cap < 2 * dimacsBound := c.harena
  have hwcap : c.wcap < 2 * dimacsBound := c.hwcap
  have hdim : dimacsBound = 268435456 := rfl
  have hcv_le : sem1.core.cur_vars ≤ c.max_vars := hpi1.len.core_ok.cur_vars_le
  have har_len : sem1.core.arena.length = c.arena_cap := hpi1.len.core_ok.arena_len_arr
  have har_le : sem1.core.arena_len ≤ c.arena_cap := hpi1.len.core_ok.arena_len_le
  have hend_wcap := SplitWatchesInv.end_lt_wcap hpi1.len.core_ok hpi1.sw
    (by simpa [withEmptyWatchesCore] using hnot_lt)
  have hwstk_len : sem1.core.wstk.length = c.wcap := hpi1.len.core_ok.wstk_len_arr
  rcases hp2_eq with ⟨p0, rfl, hp0_2, hqp0⟩
  have hp2_end : p0.toNat + 2 ≤ end_v.toNat := by rw [hp0_2]; exact hpi1.sw.p_le_end
  have hq_lt_ws : q.toNat < (fastPropMem s_disk sem1).core.wstk.length := by
    rw [BcpPropTactics.fastPropMem_wstk, hwstk_len]; omega
  have hq1_lt_ws : (q + 1#64).toNat <
      ((fastPropMem s_disk sem1).core.wstk.set q.toNat w0).length := by
    rw [List.length_set, BcpPropTactics.fastPropMem_wstk, hwstk_len]
    rw [m7_bv64_add1_toNat (by omega)]; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hq1_64 : (q + 1#64).toNat = q.toNat + 1 := hq1
  have hq1_m : (q.toNat + 1) % 2 ^ 64 = q.toNat + 1 := Nat.mod_eq_of_lt (by omega)
  have hq2 : (q + 2#64).toNat = q.toNat + 2 := m7_bv64_add2_toNat (by omega)
  have hoth_lt : other.toNat < 2 * sem1.core.cur_vars := by
    have h_ar_end : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤
        sem1.core.arena.length := har_len ▸ Nat.le_trans hcref_end har_le
    rcases s13_lits_xor_other hnl_or with ⟨_, hoth_eq⟩ | ⟨_, hoth_eq⟩
    · rw [hoth, hoth_eq]
      have hm1 : (sem1.core.arena[cref.toNat + 3 + 1]?.getD 0#32).toNat ∈
          fullArenaClauseLitsCore (withEmptyWatchesCore c sem1.core) cref.toNat := by
        dsimp only [withEmptyWatchesCore]
        exact s13_arena_lit_mem (r := 1) (Nat.lt_of_lt_of_le (by decide) hcsz3) h_ar_end
      have h1 := hpi1.nw.arena.lits_lt cref.toNat hcref_ref hcref_ng _ hm1
      simpa [withEmptyWatchesCore, hl1] using h1
    · rw [hoth, hoth_eq]
      have hm0 : (sem1.core.arena[cref.toNat + 3 + 0]?.getD 0#32).toNat ∈
          fullArenaClauseLitsCore (withEmptyWatchesCore c sem1.core) cref.toNat := by
        dsimp only [withEmptyWatchesCore]
        exact s13_arena_lit_mem (r := 0) (Nat.lt_of_lt_of_le (by decide) hcsz3) h_ar_end
      have h0 := hpi1.nw.arena.lits_lt cref.toNat hcref_ref hcref_ng _ hm0
      simpa [withEmptyWatchesCore, hl0] using h0
  dsimp only [s13LpNoReplExpr]
  s13_hstraight
  have hign_val : ignore_arg.val = ignore_ref := by rcases hign_eval with rfl | rfl <;> rfl
  let ws' := (sem1.core.wstk.set q.toNat w0).set (q.toNat + 1) cref
  let sem_k : FullState := { core := { sem1.core with wstk := ws' }, scratch := sem1.scratch }
  dsimp only at hm
  rw [BcpPropTactics.fastPropMem_wstk] at hm
  try rw [hq1] at hm
  try rw [hq1_m] at hm
  rw [s13_fastPropMem_with_wstk] at hm
  change (FullMem c (fastPropMem s_disk sem_k) ⋆ R) _ at hm
  have hpi1' : PropLitInv c F0 F_cur s_pi sem1 not_lit.toNat off_v.toNat
      q.toNat (p0.toNat + 2) end_v.toNat := hp0_2 ▸ hpi1
  have hpi_k : PropLitInv c F0 F_cur s_pi sem_k not_lit.toNat off_v.toNat
      (q + 2#64).toNat (p0 + 2#64).toNat end_v.toNat := by
    have hk := propLit_inv_keep_large hpi1' hnot_lt hqp0
      (by rw [hwstk_len]; omega) (by rw [hwstk_len]; omega) hw0_msb hcref_31 hcref_ref
    rw [hq2, ← hp0_2]; exact hk
  have hdel_k : Spec.DelayedWatchesOk sem_k.core del0 dlen not_lit.toNat := by
    intro j hj; simpa [Spec.DelayedWatchesOk, sem_k, fullArenaClauseRefsCore] using hdel_ok j hj
  have hfp_k_len : (fastPropMem s_disk sem_k).LengthsOk c :=
    fastPropMem_lengthsOk hsd_len hpi_k.len hsd_cv hsd_pr rfl
  have hlits_lt_k : ∀ r, r < fullArenaClauseSizeCore sem_k.core cref.toNat →
      (sem_k.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat < 2 * sem_k.core.cur_vars :=
    fun r hr => hpi_k.nw.arena.lits_lt cref.toNat hcref_ref hcref_ng _
      (s13_arena_lit_mem hr (har_len ▸ Nat.le_trans hcref_end har_le))
  have hall_neg_vals : ∀ r, 2 ≤ r → r < fullArenaClauseSizeCore sem_k.core cref.toNat →
      sem_k.core.vals[(sem_k.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat]?.getD 0#8 =
        255#8 := by
    intro r hr0 hr1
    have hlt := hlits_lt_k r hr1
    have hsn := hall_neg r hr0 hr1
    rcases hpi_k.nw.vals_domain (sem_k.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat
      (by simpa [withEmptyWatchesCore] using hlt) with hv | hv | hv
    · dsimp only [sem_k, withEmptyWatchesCore] at hv; rw [hv] at hsn; cases hsn
    · dsimp only [sem_k, withEmptyWatchesCore] at hv; rw [hv] at hsn; cases hsn
    · exact hv
  rw [hign_val]
  have hq2_fst : (q + 2, ()).fst = q + 2#64 := rfl
  rw [hq2_fst]
  s13_hsplit
  · have hign : BitVec.setWidth 64 cref = ignore_ref := by simpa using hc
    refine hJ_lp te un uf tk1 (p0 + 2#64) (q + 2#64) di sem_k _ ?_ rfl
    exact ⟨del0, dlen, hm, hpi_k, hdel_k, hdel_eq, hte.symm, hun, huf, hdi_eq, hdlen_le,
      hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_cv.trans hs0_cv, hsd_pr⟩
  · have hne_ign : BitVec.setWidth 64 cref ≠ ignore_ref := by simpa using hc
    clear hc
    s13_hstraight
    s13_hsplit
    · have hvo_neg : (BitVec.signExtend 32 vo).slt 0#32 = true := by simpa using hc
      clear hc
      have hvo_f : sem_k.core.vals[other.toNat]?.getD 0#8 = 255#8 := by
        rcases hpi_k.nw.vals_domain other.toNat
          (by simpa [withEmptyWatchesCore, sem_k] using hoth_lt) with hv | hv | hv
        · dsimp only [withEmptyWatchesCore, sem_k] at hv
          rw [hvo_eq, hv] at hvo_neg; exact absurd hvo_neg (by decide)
        · dsimp only [withEmptyWatchesCore, sem_k] at hv
          rw [hvo_eq, hv] at hvo_neg; exact absurd hvo_neg (by decide)
        · exact hv
      have hfls : ∀ l, l ∈ fullArenaClauseLitsCore sem_k.core cref.toNat →
          sem_k.core.vals[l]?.getD 0#8 = 255#8 :=
        s13_clause_falsified_of_find_repl_none hpi_k.len.core_ok hpi_k.nw hcref_ref hcsz3
          hcref_end hnl_or hoth hl0 hl1 hpi_k.not_f hvo_f
          (fun r hr0 hr1 => ⟨hlits_lt_k r hr1, hall_neg r hr0 hr1⟩)
      cases isBeyond
      · s13_hstraight
        dsimp only at hm ⊢
        change (FullMem c (fastPropMem s_disk {
          core := { sem_k.core with confl_ref := BitVec.setWidth 64 cref, confl_type := 2#64 },
          scratch := sem_k.scratch }) ⋆ R) _ at hm
        refine hJ_ovf _ _ ?_ rfl
        exact s13_ovf_confl_large_body (sem := sem_k) (tk := tk1) hsd_len
          (by simpa [sem_k] using hsd_cv) (by simpa [sem_k] using hsd_pr)
          (by simpa [sem_k] using hs0_cv) (by simpa [sem_k] using hs0_pr)
          (by simpa [sem_k] using hs0_dl)
          (by simpa [sem_k] using hs0_tk) (by simpa [sem_k] using hs0_oom) hdel_k hdel_eq
          (by simpa [sem_k] using hte) (by simpa [sem_k] using hun)
          (by simpa [sem_k] using huf) hdi_eq hdlen_le hpi_k hcref_ref hcref_ng hfls hne_ign
          hbrk0 hm
      · s13_hstraight
        refine hJ_lp te un uf tk1 (p0 + 2#64) (q + 2#64) di sem_k _ ?_ rfl
        exact ⟨del0, dlen, hm, hpi_k, hdel_k, hdel_eq, hte.symm, hun, huf, hdi_eq, hdlen_le,
          hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len,
          hsd_cv.trans hs0_cv, hsd_pr⟩
    · have hvo_nlt : (BitVec.signExtend 32 vo).slt 0#32 = false := by simpa using hc
      clear hc
      have hvo_un : sem_k.core.vals[other.toNat]?.getD 0#8 = 0#8 := by
        have h1 := propLit_vals_un hpi_k.nw
          (by dsimp only [withEmptyWatchesCore, sem_k]; exact hoth_lt)
          (by dsimp only [withEmptyWatchesCore, sem_k]; rw [← hvo_eq]; exact hvo_nlt)
          (by dsimp only [withEmptyWatchesCore, sem_k]; rw [← hvo_eq]; exact hvo_ng)
        exact h1
      have hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem_k.core cref.toNat := by
        have h_ar_end_k : cref.toNat + 3 + fullArenaClauseSizeCore sem_k.core cref.toNat ≤
            sem_k.core.arena.length := har_len ▸ Nat.le_trans hcref_end har_le
        rcases hnl_or with rfl | rfl
        · have hm0 := s13_arena_lit_mem (k := sem_k.core) (cref := cref.toNat) (r := 0)
            (Nat.lt_of_lt_of_le (by decide) hcsz3) h_ar_end_k
          simpa [sem_k, hl0] using hm0
        · have hm1 := s13_arena_lit_mem (k := sem_k.core) (cref := cref.toNat) (r := 1)
            (Nat.lt_of_lt_of_le (by decide) hcsz3) h_ar_end_k
          simpa [sem_k, hl1] using hm1
      have hoth_mem : other.toNat ∈ fullArenaClauseLitsCore sem_k.core cref.toNat := by
        have h_ar_end_k : cref.toNat + 3 + fullArenaClauseSizeCore sem_k.core cref.toNat ≤
            sem_k.core.arena.length := har_len ▸ Nat.le_trans hcref_end har_le
        rcases s13_lits_xor_other hnl_or with ⟨_, hoth_eq⟩ | ⟨_, hoth_eq⟩
        · have hm1 := s13_arena_lit_mem (k := sem_k.core) (cref := cref.toNat) (r := 1)
            (Nat.lt_of_lt_of_le (by decide) hcsz3) h_ar_end_k
          simpa [sem_k, hl1, hoth, hoth_eq] using hm1
        · have hm0 := s13_arena_lit_mem (k := sem_k.core) (cref := cref.toNat) (r := 0)
            (Nat.lt_of_lt_of_le (by decide) hcsz3) h_ar_end_k
          simpa [sem_k, hl0, hoth, hoth_eq] using hm0
      have hunit_inv : ∀ l, l ∈ fullArenaClauseLitsCore sem_k.core cref.toNat →
          l = other.toNat ∨ sem_k.core.vals[l]?.getD 0#8 = 255#8 := by
        have ha : sem_k.core.arena[cref.toNat + 3]? = some (BitVec.ofNat 32 other.toNat) ∨
            sem_k.core.arena[cref.toNat + 3]? = some (BitVec.ofNat 32 not_lit.toNat) := by
          rcases s13_lits_xor_other hnl_or with ⟨h_l0, _⟩ | ⟨_, hoth_eq⟩
          · exact Or.inr (by simpa [sem_k, h_l0] using hl0)
          · exact Or.inl (by simpa [sem_k, hoth, hoth_eq] using hl0)
        have hb : sem_k.core.arena[cref.toNat + 4]? = some (BitVec.ofNat 32 not_lit.toNat) ∨
            sem_k.core.arena[cref.toNat + 4]? = some (BitVec.ofNat 32 other.toNat) := by
          rcases s13_lits_xor_other hnl_or with ⟨_, hoth_eq⟩ | ⟨h_l1, _⟩
          · exact Or.inr (by simpa [sem_k, hoth, hoth_eq] using hl1)
          · exact Or.inl (by simpa [sem_k, h_l1] using hl1)
        exact propLit_hunit (_F_cur := F_cur) ha hb hcsz3 (har_len ▸ Nat.le_trans hcref_end har_le)
          hpi_k.not_f hall_neg_vals other.isLt not_lit.isLt
      have hoth_ne_not : not_lit.toNat ≠ other.toNat := by
        intro heq
        have h1 : sem_k.core.vals[not_lit.toNat]?.getD 0#8 = 255#8 := hpi_k.not_f
        rw [heq, hvo_un] at h1
        exact absurd h1 (by decide)
      s13_hstraight
      apply wp_join_group (fun (xs : Tup Val [i32]) m' =>
        m' = m ∧ S13AssignSrc F_cur sem_k.core not_lit other xs.1 cref false ∧
          xs.1.toNat ≤ sem_k.core.cur_level)
      · intro _ b212 m' ⟨hm_eq, hsrc, hlvl_le⟩
        subst m'
        exact s13_lp_assign_tail_wp hsd_len (by simpa [sem_k] using hsd_cv)
          (by simpa [sem_k] using hsd_pr) (by simpa [sem_k] using hs0_cv)
          (by simpa [sem_k] using hs0_pr) (by simpa [sem_k] using hs0_dl)
          (by simpa [sem_k] using hs0_tk) (by simpa [sem_k] using hs0_oom)
          (by simpa [sem_k] using hs0_ct) hdel_k hdel_eq hdi_eq hdlen_le hpi_k
          (by simpa [sem_k] using hnot_lt) (by simpa [sem_k] using hoth_lt) hvo_un
          (by simpa [sem_k] using hte) (by rw [← hp0_2]; dsimp; omega) hsrc hlvl_le hm
          (fun te' un' uf' sem' m'' hinv'' => hJ_lp te' un' uf' (tk1 + 1#64)
            (p0 + 2#64) (q + 2#64) di sem' m'' hinv'' rfl)
      · intro J211 hP211
        s13_hstraight
        have hcsz_k : csz.toNat = fullArenaClauseSizeCore sem_k.core cref.toNat := hcsz
        have hall_lvl_from : ∀ (alvl : BitVec 32),
            (∀ l, l ∈ fullArenaClauseLitsCore sem_k.core cref.toNat → l ≠ other.toNat →
              (sem_k.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat) →
            (alvl = 0#32 ∨ ∃ l, l ∈ fullArenaClauseLitsCore sem_k.core cref.toNat ∧
              l ≠ other.toNat ∧ alvl = sem_k.core.lvl[l / 2]?.getD 0#32) →
            alvl.toNat ≤ sem_k.core.cur_level := by
          intro alvl _ hdisj
          rcases hdisj with rfl | ⟨l, hl_mem, hne, rfl⟩
          · simp
          · have hl_nw :
                l ∈ fullArenaClauseLitsCore (withEmptyWatchesCore c sem_k.core) cref.toNat := by
              dsimp only [withEmptyWatchesCore]; exact hl_mem
            have hlt : l < 2 * sem_k.core.cur_vars :=
              hpi_k.nw.arena.lits_lt cref.toNat hcref_ref hcref_ng l hl_nw
            have hf : sem_k.core.vals[l]?.getD 0#8 = 255#8 := by
              rcases hunit_inv l hl_mem with rfl | hf
              · exact absurd rfl hne
              · exact hf
            exact s13_large_false_lvl_le hpi_k.nw hlt hf
        have hmk_src : ∀ (alvl : BitVec 32),
            (∀ l, l ∈ fullArenaClauseLitsCore sem_k.core cref.toNat → l ≠ other.toNat →
              (sem_k.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat) →
            (alvl = 0#32 ∨ ∃ l, l ∈ fullArenaClauseLitsCore sem_k.core cref.toNat ∧
              l ≠ other.toNat ∧ alvl = sem_k.core.lvl[l / 2]?.getD 0#32) →
            S13AssignSrc F_cur sem_k.core not_lit other alvl cref false := by
          intro alvl hall hdisj
          exact ⟨hcref_31, hcref_ref, hcref_ng, hnot_mem, hoth_mem, hunit_inv, hall, hdisj⟩
        s13_hsplit
        · exact s13_lp_max_lvl_wp hfp_k_len hpi_k.len hcbase hcsz_k
            hcref_end hlits_lt_k hm
            (fun alvl hall hdisj => hP211 (alvl, ()) m
              ⟨rfl, hmk_src alvl hall hdisj, hall_lvl_from alvl hall hdisj⟩)
        · have hcur_le_nl : cur_lvl32.toNat ≤ nl_lvl.toNat := by simpa using hc
          clear hc
          have hall_nl : ∀ l, l ∈ fullArenaClauseLitsCore sem_k.core cref.toNat →
              l ≠ other.toNat → (sem_k.core.lvl[l / 2]?.getD 0#32).toNat ≤ nl_lvl.toNat := by
            intro l hl_mem hne
            have hl_nw :
                l ∈ fullArenaClauseLitsCore (withEmptyWatchesCore c sem_k.core) cref.toNat := by
              dsimp only [withEmptyWatchesCore]; exact hl_mem
            have hlt : l < 2 * sem_k.core.cur_vars :=
              hpi_k.nw.arena.lits_lt cref.toNat hcref_ref hcref_ng l hl_nw
            have hf : sem_k.core.vals[l]?.getD 0#8 = 255#8 := by
              rcases hunit_inv l hl_mem with rfl | hf
              · exact absurd rfl hne
              · exact hf
            have h1 := s13_large_false_lvl_le hpi_k.nw hlt hf
            have h2 : sem_k.core.cur_level = cur_lvl32.toNat := by
              simpa [sem_k] using hcur_lvl.symm
            omega
          have hdisj_nl : nl_lvl = 0#32 ∨ ∃ l,
              l ∈ fullArenaClauseLitsCore sem_k.core cref.toNat ∧ l ≠ other.toNat ∧
              nl_lvl = sem_k.core.lvl[l / 2]?.getD 0#32 :=
            Or.inr ⟨not_lit.toNat, hnot_mem, hoth_ne_not, hnl_lvl⟩
          s13_hstraight
          exact hP211 (nl_lvl, ()) m
            ⟨rfl, hmk_src nl_lvl hall_nl hdisj_nl, hall_lvl_from nl_lvl hall_nl hdisj_nl⟩

end InnerLargeProofs

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
