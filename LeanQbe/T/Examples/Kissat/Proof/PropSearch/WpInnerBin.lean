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
# Kissat PropSearch Inner-Loop ASTs and Binary/Delay WP Proofs (`Proof.PropSearch.WpInnerBin`)

Defines the unified modular C0 expressions (`isBeyond : Bool`) matching both
`full_propagate_ignore_hot_body` (`false`) and `full_propagate_beyond_m7_body` (`true`),
proves the hyper-binary jump-reason step (`s13_bin_jump_rsn_nw_step`, `s13_bin_jump_rsn_step`),
and proves WP theorems for `s13LpAssignTailExpr`, `s13LpBinStepExpr`, and `s13LpReplDelExpr`.
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

@[expose] def s13LpSig : List Ty := [i64, i64, i64, i64, i64, i64, i64]

abbrev opI64 {V : Ty → Type} (code : OpCode [i64, i64] [i64])
    (a b : Arg V i64) : Op V [i64] :=
  { code := code, args := (a, b, ()) }

abbrev opCmp64 {V : Ty → Type} (op : CmpOp)
    (a b : Arg V i64) : Op V [Ty.bool] :=
  { code := OpCode.cmp op i64 Ty.bool rfl, args := (a, b, ()) }

abbrev opCmp32 {V : Ty → Type} (op : CmpOp)
    (a b : Arg V i32) : Op V [Ty.bool] :=
  { code := OpCode.cmp op i32 Ty.bool rfl, args := (a, b, ()) }

abbrev opI32 {V : Ty → Type} (code : OpCode [i32, i32] [i32])
    (a b : Arg V i32) : Op V [i32] :=
  { code := code, args := (a, b, ()) }

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

@[expose] def s13LpAssignTailExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBin : Bool) (J_lp : L s13LpSig)
    (vals lvl rsns trl tpos flags phases : V i64)
    (rec_ph nonchrono : V Ty.bool) (not_lit : V i32)
    (te un uf di tk_next p_next q_next : V i64)
    (unit lvl32 rsn_src : V i32) : Expr V L rs :=
  Expr.let_ (opI32 (OpCode.lshr i32) (Arg.var unit) (@Arg.imm _ i32 1)) fun v30 =>
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var v30.1, ()) } fun v31 =>
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var unit, ()) } fun v32 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var vals) (Arg.var v32.1)) fun v33 =>
  Expr.let_ { code := OpCode.trunc 32 8, args := (@Arg.imm _ i32 1, ()) } fun v34 =>
  Expr.store (Arg.var v34.1) (Arg.var v33.1) (
  Expr.let_ (opI32 (OpCode.xor i32) (Arg.var unit) (@Arg.imm _ i32 1)) fun v35 =>
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var v35.1, ()) } fun v36 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var vals) (Arg.var v36.1)) fun v37 =>
  Expr.let_ { code := OpCode.neg i32, args := (@Arg.imm _ i32 1, ()) } fun v38 =>
  Expr.let_ { code := OpCode.trunc 32 8, args := (Arg.var v38.1, ()) } fun v39 =>
  Expr.store (Arg.var v39.1) (Arg.var v37.1) (
  Expr.group (sig := [[i64]]) (fun _J40 =>
    Blocks.cons (fun b41 =>
      Expr.group (sig := [[]]) (fun _J42 =>
        Blocks.cons (fun _ =>
          Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v31.1) (@Arg.imm _ i64 4)) fun v44 =>
          Expr.let_ (opI64 (OpCode.add i64) (Arg.var lvl) (Arg.var v44.1)) fun v45 =>
          Expr.store (Arg.var lvl32) (Arg.var v45.1) (
          Expr.group (sig := [[i64]]) (fun _J46 =>
            Blocks.cons (fun b47 =>
              Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v31.1) (@Arg.imm _ i64 4)) fun v48 =>
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var tpos) (Arg.var v48.1)) fun v49 =>
              Expr.let_ { code := OpCode.trunc 64 32, args := (Arg.var te, ()) } fun v50 =>
              Expr.store (Arg.var v50.1) (Arg.var v49.1) (
              Expr.let_ (opI64 (OpCode.mul i64) (Arg.var te) (@Arg.imm _ i64 4)) fun v51 =>
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var trl) (Arg.var v51.1)) fun v52 =>
              Expr.store (Arg.var unit) (Arg.var v52.1) (
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var te) (@Arg.imm _ i64 1)) fun v53 =>
              Expr.jump J_lp (Arg.var v53.1, Arg.var b41.1, Arg.var b47.1, Arg.var tk_next,
                Arg.var p_next, Arg.var q_next, Arg.var di, ()))))
              Blocks.nil)
            fun J46 =>
            Expr.let_ (opCmp32 CmpOp.eq (Arg.var lvl32) (@Arg.imm _ i32 0)) fun v54 =>
            Expr.jnz (Arg.var v54.1)
              (Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v31.1) (@Arg.imm _ i64 4)) fun v55 =>
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var rsns) (Arg.var v55.1)) fun v56 =>
              Expr.store (@Arg.imm _ i32 4294967295) (Arg.var v56.1) (
              Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v31.1) (@Arg.imm _ i64 4)) fun v57 =>
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var flags) (Arg.var v57.1)) fun v58 =>
              Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v31.1) (@Arg.imm _ i64 4)) fun v59 =>
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var flags) (Arg.var v59.1)) fun v60 =>
              Expr.load i32 (Arg.var v60.1) fun ld61 =>
              Expr.let_ { code := OpCode.not i32, args := (@Arg.imm _ i32 1, ()) } fun v62 =>
              Expr.let_ (opI32 (OpCode.and i32) (Arg.var ld61) (Arg.var v62.1)) fun v63 =>
              Expr.store (Arg.var v63.1) (Arg.var v58.1) (
              Expr.let_ (opI64 (OpCode.add i64) (Arg.var uf) (@Arg.imm _ i64 1)) fun v64 =>
              Expr.jump J46.1 (Arg.var v64.1, ()))))
              (if isBin then
                Expr.let_ (opI32 (OpCode.or i32) (@Arg.imm _ i32 2147483648)
                  (Arg.var not_lit)) fun v65 =>
                Expr.group (sig := [[i32]]) (fun _J66 =>
                  Blocks.cons (fun b67 =>
                    Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v31.1)
                      (@Arg.imm _ i64 4)) fun v68 =>
                    Expr.let_ (opI64 (OpCode.add i64) (Arg.var rsns) (Arg.var v68.1)) fun v69 =>
                    Expr.store (Arg.var b67.1) (Arg.var v69.1) (
                    Expr.jump J46.1 (Arg.var uf, ())))
                    Blocks.nil)
                  fun J66 =>
                  Expr.jnz (Arg.var nonchrono)
                    (Expr.let_ (opI32 (OpCode.lshr i32) (Arg.var not_lit)
                      (@Arg.imm _ i32 1)) fun v70 =>
                    Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var v70.1, ()) } fun v71 =>
                    Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v71.1)
                      (@Arg.imm _ i64 4)) fun v72 =>
                    Expr.let_ (opI64 (OpCode.add i64) (Arg.var rsns) (Arg.var v72.1)) fun v73 =>
                    Expr.load i32 (Arg.var v73.1) fun ld74 =>
                    Expr.group (sig := [[i32]]) (fun _J75 =>
                      Blocks.cons (fun b76 => Expr.jump J66.1 (Arg.var b76.1, ())) Blocks.nil)
                      fun J75 =>
                      Expr.let_ (opCmp32 CmpOp.ne (Arg.var ld74)
                        (@Arg.imm _ i32 4294967295)) fun v77 =>
                      Expr.jnz (Arg.var v77.1)
                        (Expr.let_ (opI32 (OpCode.and i32) (Arg.var ld74)
                          (@Arg.imm _ i32 2147483648)) fun v78 =>
                        Expr.let_ (opCmp32 CmpOp.ne (Arg.var v78.1)
                          (@Arg.imm _ i32 0)) fun v79 =>
                        Expr.jnz (Arg.var v79.1)
                          (Expr.jump J75.1 (Arg.var ld74, ()))
                          (Expr.jump J75.1 (Arg.var v65.1, ())))
                        (Expr.jump J75.1 (Arg.var v65.1, ())))
                    (Expr.jump J66.1 (Arg.var v65.1, ()))
              else
                Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v31.1) (@Arg.imm _ i64 4)) fun v68 =>
                Expr.let_ (opI64 (OpCode.add i64) (Arg.var rsns) (Arg.var v68.1)) fun v69 =>
                Expr.store (Arg.var rsn_src) (Arg.var v69.1) (
                Expr.jump J46.1 (Arg.var uf, ())))))
          Blocks.nil)
        fun J42 =>
        Expr.jnz (Arg.var rec_ph)
          (Expr.group (sig := [[]]) (fun _J80 =>
            Blocks.cons (fun _ => Expr.jump J42.1 ()) Blocks.nil)
            fun J80 =>
            Expr.let_ (opI32 (OpCode.and i32) (Arg.var unit) (@Arg.imm _ i32 1)) fun v82 =>
            Expr.let_ (opCmp32 CmpOp.ne (Arg.var v82.1) (@Arg.imm _ i32 0)) fun v83 =>
            Expr.jnz (Arg.var v83.1)
              (Expr.let_ (opI64 (OpCode.add i64) (Arg.var phases) (Arg.var v31.1)) fun v84 =>
              Expr.let_ { code := OpCode.neg i32, args := (@Arg.imm _ i32 1, ()) } fun v85 =>
              Expr.let_ { code := OpCode.trunc 32 8, args := (Arg.var v85.1, ()) } fun v86 =>
              Expr.store (Arg.var v86.1) (Arg.var v84.1) (
              Expr.jump J80.1 ()))
              (Expr.let_ (opI64 (OpCode.add i64) (Arg.var phases) (Arg.var v31.1)) fun v87 =>
              Expr.let_ { code := OpCode.trunc 32 8, args := (@Arg.imm _ i32 1, ()) } fun v88 =>
              Expr.store (Arg.var v88.1) (Arg.var v87.1) (
              Expr.jump J80.1 ())))
          (Expr.jump J42.1 ()))
      Blocks.nil)
    fun J40 =>
    Expr.let_ (opI64 (OpCode.mul i64) (Arg.var v31.1) (@Arg.imm _ i64 4)) fun v89 =>
    Expr.let_ (opI64 (OpCode.add i64) (Arg.var flags) (Arg.var v89.1)) fun v90 =>
    Expr.load i32 (Arg.var v90.1) fun ld91 =>
    Expr.let_ (opI32 (OpCode.and i32) (Arg.var ld91) (@Arg.imm _ i32 1)) fun v92 =>
    Expr.let_ (opCmp32 CmpOp.ne (Arg.var v92.1) (@Arg.imm _ i32 0)) fun v93 =>
    Expr.jnz (Arg.var v93.1)
      (Expr.let_ (opCmp64 CmpOp.ugt (Arg.var un) (@Arg.imm _ i64 0)) fun v94 =>
      Expr.jnz (Arg.var v94.1)
        (Expr.let_ (opI64 (OpCode.sub i64) (Arg.var un) (@Arg.imm _ i64 1)) fun v95 =>
        Expr.jump J40.1 (Arg.var v95.1, ()))
        (Expr.jump J40.1 (Arg.var un, ())))
      (Expr.jump J40.1 (Arg.var un, ()))))

@[expose] def s13LpBinStepExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (h : V i64) (J_lp : L s13LpSig) (J_ovf : L (s13OvfSig isBeyond))
    (vals wstk lvl rsns trl tpos flags phases : V i64)
    (rec_ph nonchrono : V Ty.bool) (not_lit nl_lvl w0 : V i32)
    (te un uf tk p q di : V i64) : Expr V L rs :=
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var p) (@Arg.imm _ i64 1)) fun v8 =>
  Expr.let_ (opI32 (OpCode.and i32) (Arg.var w0) (@Arg.imm _ i32 2147483647)) fun v9 =>
  Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var v9.1, ()) } fun v10 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var vals) (Arg.var v10.1)) fun v11 =>
  Expr.load i8 (Arg.var v11.1) fun ld12 =>
  Expr.let_ (opI64 (OpCode.mul i64) (Arg.var q) (@Arg.imm _ i64 4)) fun v13 =>
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var wstk) (Arg.var v13.1)) fun v14 =>
  Expr.store (Arg.var w0) (Arg.var v14.1) (
  Expr.let_ (opI64 (OpCode.add i64) (Arg.var q) (@Arg.imm _ i64 1)) fun v15 =>
  Expr.let_ { code := OpCode.trunc 32 8, args := (@Arg.imm _ i32 0, ()) } fun v16 =>
  Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var ld12, ()) } fun v17 =>
  Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var v16.1, ()) } fun v18 =>
  Expr.let_ (opCmp32 CmpOp.sgt (Arg.var v17.1) (Arg.var v18.1)) fun v19 =>
  Expr.jnz (Arg.var v19.1)
    (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk,
      Arg.var v8.1, Arg.var v15.1, Arg.var di, ()))
    (Expr.let_ { code := OpCode.trunc 32 8, args := (@Arg.imm _ i32 0, ()) } fun v20 =>
    Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var ld12, ()) } fun v21 =>
    Expr.let_ { code := OpCode.sext 8 32, args := (Arg.var v20.1, ()) } fun v22 =>
    Expr.let_ (opCmp32 CmpOp.slt (Arg.var v21.1) (Arg.var v22.1)) fun v23 =>
    Expr.jnz (Arg.var v23.1)
      (match isBeyond, J_ovf with
      | true, _ =>
        Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk,
          Arg.var v8.1, Arg.var v15.1, Arg.var di, ())
      | false, J_ovf' =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var h) (@Arg.imm _ i64 528)) fun v24 =>
        Expr.store (@Arg.imm _ i64 1) (Arg.var v24.1) (
        Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var not_lit, ()) } fun v25 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var h) (@Arg.imm _ i64 536)) fun v26 =>
        Expr.store (Arg.var v25.1) (Arg.var v26.1) (
        Expr.let_ { code := OpCode.zext 32 64, args := (Arg.var v9.1, ()) } fun v27 =>
        Expr.let_ (opI64 (OpCode.add i64) (Arg.var h) (@Arg.imm _ i64 544)) fun v28 =>
        Expr.store (Arg.var v27.1) (Arg.var v28.1) (
        s13OvfJump false J_ovf' (Arg.var te) (Arg.var un) (Arg.var uf) (Arg.var tk)
          (Arg.var v8.1) (Arg.var v15.1) (Arg.var di) (@Arg.imm _ i64 1)
          (@Arg.imm _ Ty.bool false) (@Arg.imm _ i32 0) (@Arg.imm _ i32 0)
          (@Arg.imm _ i32 0) (@Arg.imm _ i64 0)))))
      (Expr.let_ (opI64 (OpCode.add i64) (Arg.var tk) (@Arg.imm _ i64 1)) fun v29 =>
      s13LpAssignTailExpr true J_lp vals lvl rsns trl tpos flags phases rec_ph nonchrono
        not_lit te un uf di v29.1 v8.1 v15.1 v9.1 nl_lvl nl_lvl)))

@[expose] def S13LpInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s_disk s_pi0 sem0 sem : FullState) (not_lit : BitVec 32)
    (off_v end_v : BitVec 64) (te un uf _tk p q di : BitVec 64)
    (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ (del : List (BitVec 32)) (dlen : Nat),
    let s_pi := { s_pi0 with scratch := { s_pi0.scratch with delayed := del } }
    (FullMem c (fastPropMem s_disk sem) ⋆ R) m ∧
      PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q.toNat p.toNat end_v.toNat ∧
        Spec.DelayedWatchesOk sem.core s_pi.scratch.delayed dlen not_lit.toNat ∧
          (c.delayed_cap = 0 → del = s_pi0.scratch.delayed) ∧
            sem.core.trail_end = te.toNat ∧
              sem.core.unassigned = un ∧
                sem.core.unflushed = uf ∧
                  di.toNat = 3 * dlen ∧
                    dlen ≤ c.delayed_cap ∧
                      sem.core.cur_vars = sem0.core.cur_vars ∧
                        sem.core.propagated = sem0.core.propagated ∧
                          sem.scratch.delayed_len = sem0.scratch.delayed_len ∧
                            sem.scratch.search_ticks = sem0.scratch.search_ticks ∧
                              sem.core.oom = sem0.core.oom ∧
                                S13ConflEq sem0.core sem.core ∧
                                  s_disk.LengthsOk c ∧
                                    s_disk.core.cur_vars = sem0.core.cur_vars ∧
                                      sem.core.propagated ≤ s_disk.core.trail_end

@[expose] def S13OvfBody (isBeyond : Bool) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (ignore_ref : BitVec 64)
    (s_disk s_pi0 sem0 : FullState) (not_lit : BitVec 32)
    (off_v end_v brk0 : BitVec 64) (R : Mem 64 → Prop)
    (te un uf _tk p q di brk : BitVec 64) (ovf : Bool)
    (repl_lit other_lit cr_ref : BitVec 32) (ri_v : BitVec 64) (m : Mem 64) : Prop :=
  ∃ (sem : FullState) (del : List (BitVec 32)) (dlen : Nat),
    let s_pi := { s_pi0 with scratch := { s_pi0.scratch with delayed := del } }
    (FullMem c (fastPropMem s_disk sem) ⋆ R) m ∧
      PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q.toNat p.toNat end_v.toNat ∧
        Spec.DelayedWatchesOk sem.core s_pi.scratch.delayed dlen not_lit.toNat ∧
          (c.delayed_cap = 0 → del = s_pi0.scratch.delayed) ∧
            sem.core.trail_end = te.toNat ∧
              sem.core.unassigned = un ∧
                sem.core.unflushed = uf ∧
                  di.toNat = 3 * dlen ∧
                    dlen ≤ c.delayed_cap ∧
                      sem.core.cur_vars = sem0.core.cur_vars ∧
                        sem.core.propagated = sem0.core.propagated ∧
                          sem.scratch.delayed_len = sem0.scratch.delayed_len ∧
                            sem.scratch.search_ticks = sem0.scratch.search_ticks ∧
                              sem.core.oom = sem0.core.oom ∧
                                s_disk.LengthsOk c ∧
                                  s_disk.core.cur_vars = sem0.core.cur_vars ∧
                                    sem.core.propagated ≤ s_disk.core.trail_end ∧
                                    (if ovf then
                                      let csz := fullArenaClauseSizeCore sem.core cr_ref.toNat
                                      brk = brk0 ∧ q.toNat + 2 ≤ p.toNat ∧
                                        S13ConflEq sem0.core sem.core ∧
                                        repl_lit.toNat < 2 * sem.core.cur_vars ∧
                                        repl_lit.toNat ≠ not_lit.toNat ∧
                                        cr_ref.toNat < 2 ^ 31 ∧
                                        cr_ref.toNat ∈ fullArenaClauseRefsCore sem.core ∧
                                        fullArenaClauseGarbCore sem.core cr_ref.toNat = false ∧
                                        3 ≤ csz ∧
                                        cr_ref.toNat + 3 + csz ≤ sem.core.arena_len ∧
                                        2 ≤ ri_v.toNat ∧ ri_v.toNat < csz ∧
                                        (∃ l0 l1,
                                          sem.core.arena[cr_ref.toNat + 3]? = some l0 ∧
                                          sem.core.arena[cr_ref.toNat + 4]? = some l1 ∧
                                          (l0 = not_lit ∨ l1 = not_lit) ∧
                                          other_lit = l0 ^^^ l1 ^^^ not_lit ∧
                                          sem.core.arena[cr_ref.toNat + 3 + ri_v.toNat]? =
                                            some repl_lit) ∧
                                        other_lit &&& 2147483647#32 = other_lit
                                    else if brk = brk0 then
                                      p = end_v ∧ S13ConflEq sem0.core sem.core
                                    else
                                      isBeyond = false ∧ brk = 1#64 ∧
                                        PropLitConfl F_cur ignore_ref sem.core)

@[expose] def S13OvfExitPred (isBeyond : Bool) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (ignore_ref : BitVec 64)
    (s_disk s_pi0 sem0 : FullState) (not_lit : BitVec 32)
    (off_v end_v brk0 : BitVec 64) (R : Mem 64 → Prop)
    (xs : Tup Val (s13OvfSig isBeyond)) (m : Mem 64) : Prop :=
  match isBeyond, xs with
  | true, (te, un, uf, tk, p, q, di, ovf, repl, oth, cr, ri, ()) =>
    S13OvfBody true c F0 F_cur ignore_ref s_disk s_pi0 sem0 not_lit off_v end_v brk0 R
      te un uf tk p q di brk0 ovf repl oth cr ri m
  | false, (te, un, uf, tk, p, q, di, brk, ovf, repl, oth, cr, ri, ()) =>
    S13OvfBody false c F0 F_cur ignore_ref s_disk s_pi0 sem0 not_lit off_v end_v brk0 R
      te un uf tk p q di brk ovf repl oth cr ri m

@[expose] def s13OvfP : {isBeyond : Bool} → Tup Val (s13OvfSig isBeyond) → BitVec 64
  | true, (_, _, _, _, p, _, _, _, _, _, _, _, ()) => p
  | false, (_, _, _, _, p, _, _, _, _, _, _, _, _, ()) => p

@[expose] def s13OvfFlag : {isBeyond : Bool} → Tup Val (s13OvfSig isBeyond) → Bool
  | true, (_, _, _, _, _, _, _, ovf, _, _, _, _, ()) => ovf
  | false, (_, _, _, _, _, _, _, _, ovf, _, _, _, _, ()) => ovf

@[expose] def S13AssignSrc (F_cur : List (List Nat)) (k : FullCoreState)
    (not_lit unit lvl32 rsn_src : BitVec 32) (isBin : Bool) : Prop :=
  if isBin then
    k.lvl[not_lit.toNat / 2]?.getD 0#32 = lvl32 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, unit.toNat])
  else
    rsn_src.toNat < 2147483648 ∧
      rsn_src.toNat ∈ fullArenaClauseRefsCore k ∧
        fullArenaClauseGarbCore k rsn_src.toNat = false ∧
          not_lit.toNat ∈ fullArenaClauseLitsCore k rsn_src.toNat ∧
            unit.toNat ∈ fullArenaClauseLitsCore k rsn_src.toNat ∧
              (∀ l, l ∈ fullArenaClauseLitsCore k rsn_src.toNat →
                l = unit.toNat ∨ k.vals[l]?.getD 0#8 = 255#8) ∧
              (∀ l, l ∈ fullArenaClauseLitsCore k rsn_src.toNat →
                l ≠ unit.toNat → (k.lvl[l / 2]?.getD 0#32).toNat ≤ lvl32.toNat) ∧
              (lvl32 = 0#32 ∨ ∃ l, l ∈ fullArenaClauseLitsCore k rsn_src.toNat ∧
                l ≠ unit.toNat ∧ lvl32 = k.lvl[l / 2]?.getD 0#32)

private theorem s13_bin_jump_rsn_nw_step {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState}
    (hl : k.LengthsOk c) (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {not_lit other alvl ld74 : BitVec 32}
    (halvl_le : alvl.toNat ≤ k.cur_level) (halvl_nz : alvl ≠ 0#32)
    (hother_lt : other.toNat < 2 * k.cur_vars)
    (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_lt : not_lit.toNat < 2 * k.cur_vars)
    (hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 255#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, other.toNat]))
    (hnl_le : (k.lvl[not_lit.toNat / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hnl0_iff : alvl = 0#32 ↔ k.lvl[not_lit.toNat / 2]?.getD 0#32 = 0#32)
    (hld_eq : ld74 = k.rsns[not_lit.toNat / 2]?.getD 4294967295#32)
    (hld_ne : ld74 ≠ 4294967295#32)
    (hld_bin : ld74 &&& 2147483648#32 ≠ 0#32)
    (flags' : List (BitVec 32)) (unas' unfl' : BitVec 64) :
    have v := other.toNat / 2
    have k' := { k with
      unassigned := unas', unflushed := unfl', trail_end := k.trail_end + 1,
      vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 255#8,
      flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v ld74,
      trl := k.trl.set k.trail_end other,
      trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end) }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧
      FullTrailExt k k' ∧ Spec.FullTrailRsnsPres k k' := by
  intro v k'
  have hbase := full_bin_assign_nw_step hl hnw halvl_le hother_lt hun hnot_lt hnot_f
    hent hnl_le hnl0_iff flags' unas' unfl'
  rcases hbase with ⟨hnw_b, htr_b, hrp_b⟩
  let rsn0 := not_lit &&& 2147483647#32 ||| 2147483648#32
  let rsn_b := if alvl = 0#32 then 4294967295#32 else rsn0
  let k_b : FullCoreState := { k with
    unassigned := unas', unflushed := unfl', trail_end := k.trail_end + 1,
    vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 255#8,
    flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn_b,
    trl := k.trl.set k.trail_end other,
    trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end) }
  have hk_te : k.trail_end < k.cur_vars :=
    m7_trail_end_lt_of_unassigned (k := withEmptyWatchesCore c k) hnw
      (by simpa [withEmptyWatchesCore] using hother_lt)
      (by simpa [withEmptyWatchesCore] using hun)
  have hk_te_trl : k.trail_end < k.trl.length := by
    have := hl.trail_end_le; have := hl.cur_vars_le; have := hl.trl_len; omega
  have hv_lt_rsns : v < k.rsns.length := by
    have := hl.cur_vars_le; have := hl.rsns_len; change other.toNat / 2 < k.rsns.length; omega
  have hrs_eq : ∀ i, i < k.trail_end → (k.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
    intro i hi hEq
    have hi_lt : i < k.trl.length := by omega
    have hne_i : i ≠ k.trail_end := by omega
    have h1 : (k_b.trl[i]?.getD 0#32).toNat / 2 =
        (k_b.trl[k.trail_end]?.getD 0#32).toNat / 2 := by
      simp only [k_b, List.getElem?_set_ne hne_i.symm, List.getElem?_set_self hk_te_trl]
      change (k.trl[i]?.getD 0#32).toNat / 2 = other.toNat / 2
      exact hEq
    have hnod := hnw_b.trail_vars_nodup i k.trail_end
      (Nat.lt_succ_of_lt (by simpa [k_b, withEmptyWatchesCore] using hi))
      (by simp [withEmptyWatchesCore])
      (by simpa [withEmptyWatchesCore] using h1)
    omega
  have hrs_at_lt : ∀ i, i < k.trail_end →
      k'.rsns[(k'.trl[i]?.getD 0#32).toNat / 2]? =
        k_b.rsns[(k_b.trl[i]?.getD 0#32).toNat / 2]? := by
    intro i hi
    have hne_i : i ≠ k.trail_end := by omega
    have htrl : k'.trl[i]? = k.trl[i]? := List.getElem?_set_ne hne_i.symm
    have htrlb : k_b.trl[i]? = k.trl[i]? := List.getElem?_set_ne hne_i.symm
    have hne := hrs_eq i hi
    simp only [k', k_b, htrl] at hne ⊢
    rw [List.getElem?_set_ne hne.symm, List.getElem?_set_ne hne.symm]
  have hnot_idx : ∃ idx0, idx0 < k.trail_end ∧
      (k.trl[idx0]?.getD 0#32).toNat = not_lit.toNat ^^^ 1 := by
    have := (hnw.vals_false_iff not_lit.toNat
      (by simpa [withEmptyWatchesCore] using hnot_lt)).mp
      (by simpa [withEmptyWatchesCore] using hnot_f)
    simpa [withEmptyWatchesCore] using this
  rcases hnot_idx with ⟨idx0, hidx0, htrl_idx0⟩
  have hri0 := hnw.reason_inv idx0 (by simpa [withEmptyWatchesCore] using hidx0)
  have hp0_div : (not_lit.toNat ^^^ 1) / 2 = not_lit.toNat / 2 := nat_xor1_div2 _
  have hrsn0_eq : (withEmptyWatchesCore c k).rsns[not_lit.toNat / 2]?.getD 4294967295#32 =
      ld74 := by
    simpa [withEmptyWatchesCore] using hld_eq.symm
  have hr0_body : let ot := (ld74 &&& 2147483647#32).toNat
      ot < 2 * k.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat ^^^ 1, ot]) ∧
          ∃ m, m < idx0 ∧ (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
            (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[not_lit.toNat / 2]?.getD 0#32).toNat := by
    have htr0' : ((withEmptyWatchesCore c k).trl[idx0]?.getD 0#32).toNat =
        not_lit.toNat ^^^ 1 := htrl_idx0
    have hri0' := hri0
    dsimp only at hri0'
    rw [htr0', hp0_div, hrsn0_eq] at hri0'
    simpa [withEmptyWatchesCore, hld_bin] using hri0' hld_ne
  have harena' : FullArenaClausesInv c F_cur (withEmptyWatchesCore c k') :=
    ⟨hnw_b.arena.len_ok, hnw_b.arena.refs_wf, hnw_b.arena.shrk_term,
      hnw_b.arena.lits_lt, hnw_b.arena.entails⟩
  have hwatch_slice' : ∀ {l p rem}, WatchSliceOk F_cur (withEmptyWatchesCore c k_b) l p rem →
      WatchSliceOk F_cur (withEmptyWatchesCore c k') l p rem := by
    intro l p rem h
    induction h with
    | empty => exact WatchSliceOk.empty
    | bin h1 h2 h3 h4 h5 _ ih => exact WatchSliceOk.bin h1 h2 h3 h4 h5 ih
    | large h1 h2 h3 h4 h5 _ ih =>
      exact WatchSliceOk.large h1 h2 h3 h4
        (by dsimp only [fullArenaClauseRefsCore] at h5 ⊢; exact h5) ih
  have hwatches' : ModeWatchesInv F_cur (withEmptyWatchesCore c k') := by
    have hw := hnw_b.watches
    dsimp only [ModeWatchesInv, withEmptyWatchesCore] at hw ⊢
    exact ⟨⟨hw.layout.bounds, hw.layout.pos_off, hw.layout.disjoint, hw.layout.no_sentinel⟩,
      fun l hl => hwatch_slice' (hw.slices l hl)⟩
  refine ⟨?_, htr_b, ?_⟩
  · refine FullWitnessInv.mk hnw_b.ext_sound hnw_b.inconsistent_sound harena'
      hwatches' hnw_b.cur_level_le hnw_b.trail_lits_lt hnw_b.trail_vars_nodup
      hnw_b.vals_domain hnw_b.vals_true_iff hnw_b.vals_false_iff hnw_b.lvl_le
      ?_ hnw_b.levels_inhabited hnw_b.level0_sound hnw_b.trail_pos_inv
      ?_ hnw_b.frame_trail_lt hnw_b.frame_trail_mono hnw_b.frame_trail_before_lt
      hnw_b.frame_dec_lt ?_ ?_
    · intro i j hi hj hlv hdec
      have hj' : j < k.trail_end := by
        rcases Nat.lt_or_eq_of_le
            (Nat.lt_succ_iff.mp (by simpa [k', withEmptyWatchesCore] using hj)) with hlt | rfl
        · exact hlt
        · have hjrs : (withEmptyWatchesCore c k').rsns[v]?.getD 4294967295#32 = ld74 := by
            simp [k', withEmptyWatchesCore, List.getElem?_set_self hv_lt_rsns]
          have htrl_j : ((withEmptyWatchesCore c k').trl[k.trail_end]?.getD 0#32).toNat =
              other.toNat := by
            simp [k', withEmptyWatchesCore, List.getElem?_set_self hk_te_trl]
          have hconj : (withEmptyWatchesCore c k').rsns[
              ((withEmptyWatchesCore c k').trl[k.trail_end]?.getD 0#32).toNat / 2]?.getD
                4294967295#32 = ld74 := by
            simpa [htrl_j, v] using hjrs
          exact False.elim (hld_ne (hconj.symm.trans hdec.2))
      have hi' : i < k.trail_end + 1 := by simpa [k', withEmptyWatchesCore] using hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hil | rfl
      · have hne_i : i ≠ k.trail_end := by omega
        have hne_j : j ≠ k.trail_end := by omega
        have hlv' : (k_b.lvl[(k_b.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
            (k_b.lvl[(k_b.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          simpa [k', k_b, withEmptyWatchesCore, List.getElem?_set_ne hne_i.symm,
            List.getElem?_set_ne hne_j.symm] using hlv
        have hdec_rsn : k_b.rsns[(k_b.trl[j]?.getD 0#32).toNat / 2]?.getD 4294967295#32 =
            4294967295#32 := by
          have h1 := hrs_at_lt j hj'
          have h2 : k'.rsns[(k'.trl[j]?.getD 0#32).toNat / 2]?.getD 4294967295#32 =
              4294967295#32 := by
            simpa [withEmptyWatchesCore] using hdec.2
          rw [← h1]; exact h2
        have hdec' : 0 < (k_b.lvl[(k_b.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
            k_b.rsns[(k_b.trl[j]?.getD 0#32).toNat / 2]?.getD 4294967295#32 = 4294967295#32 := by
          refine ⟨?_, hdec_rsn⟩
          simpa [k', k_b, withEmptyWatchesCore, List.getElem?_set_ne hne_j.symm] using hdec.1
        have hres := hnw_b.dec_earliest i j
          (Nat.lt_succ_of_lt (by simpa [k_b, withEmptyWatchesCore] using hil))
          (Nat.lt_succ_of_lt (by simpa [k_b, withEmptyWatchesCore] using hj'))
          (by simpa [k_b, withEmptyWatchesCore] using hlv')
          (by simpa [k_b, withEmptyWatchesCore] using hdec')
        exact hres
      · exact Nat.le_of_lt hj'
    · intro idx hidx hlv0
      have hidx' : idx < k.trail_end := by
        rcases Nat.lt_or_eq_of_le
            (Nat.lt_succ_iff.mp (by simpa [k', withEmptyWatchesCore] using hidx)) with hlt | rfl
        · exact hlt
        · have hv_lt_lvl : v < k.lvl.length := by
            have := hl.cur_vars_le; have := hl.lvl_len; change other.toNat / 2 < k.lvl.length; omega
          have htrl_te : ((withEmptyWatchesCore c k').trl[k.trail_end]?.getD 0#32).toNat =
              other.toNat := by
            simp [k', withEmptyWatchesCore, List.getElem?_set_self hk_te_trl]
          have hlvl_te : ((withEmptyWatchesCore c k').lvl[v]?.getD 0#32).toNat = alvl.toNat := by
            simp [k', withEmptyWatchesCore, List.getElem?_set_self hv_lt_lvl]
          rw [htrl_te] at hlv0
          change ((withEmptyWatchesCore c k').lvl[v]?.getD 0#32).toNat = 0 at hlv0
          rw [hlvl_te] at hlv0
          exact False.elim (halvl_nz (BitVec.eq_of_toNat_eq (by simpa using hlv0)))
      have hne_idx : idx ≠ k.trail_end := by omega
      have h0 : (k_b.lvl[(k_b.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        simpa [k', k_b, withEmptyWatchesCore, List.getElem?_set_ne hne_idx.symm] using hlv0
      have hb := hnw_b.level0_rsn_none idx
        (Nat.lt_succ_of_lt (by simpa [k_b, withEmptyWatchesCore] using hidx'))
        (by simpa [k_b, withEmptyWatchesCore] using h0)
      have h1 := hrs_at_lt idx hidx'
      simpa [withEmptyWatchesCore, h1] using hb
    · intro idx hidx
      have hidx' : idx < k.trail_end + 1 := by simpa [k', withEmptyWatchesCore] using hidx
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hidx') with hlt | rfl
      · have hne_idx : idx ≠ k.trail_end := by omega
        have hb := hnw_b.reason_inv idx
          (Nat.lt_succ_of_lt (by simpa [k_b, withEmptyWatchesCore] using hlt))
        have h1 := hrs_at_lt idx hlt
        dsimp only [withEmptyWatchesCore] at hb ⊢
        rw [h1]
        simpa [k', k_b, withEmptyWatchesCore, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
          fullArenaClauseLitsCore, fullArenaHdrCore, fullArenaClauseSizeCore] using hb
      · dsimp only
        intro hrsn_ne
        have htrl_te : ((withEmptyWatchesCore c k').trl[k.trail_end]?.getD 0#32).toNat =
            other.toNat := by
          simp [k', withEmptyWatchesCore, List.getElem?_set_self hk_te_trl]
        have hrsn_te : (withEmptyWatchesCore c k').rsns[v]?.getD 4294967295#32 = ld74 := by
          simp [k', withEmptyWatchesCore, List.getElem?_set_self hv_lt_rsns]
        rw [htrl_te, show other.toNat / 2 = v by rfl, hrsn_te, ite_eq_left hld_bin]
        rcases hr0_body with ⟨hot_lt, hot_ent, m, hm_lt, hm_trl, hm_lvl⟩
        have hm_te : m < k.trail_end := Nat.lt_trans hm_lt hidx0
        have hm_var_ne : (ld74 &&& 2147483647#32).toNat / 2 ≠ v := by
          intro hEq
          have hm_l : (k.trl[m]?.getD 0#32).toNat = (ld74 &&& 2147483647#32).toNat ^^^ 1 := hm_trl
          have hdiv_ot : ((ld74 &&& 2147483647#32).toNat ^^^ 1) / 2 =
              (ld74 &&& 2147483647#32).toNat / 2 := nat_xor1_div2 _
          have hdiv_m : (k.trl[m]?.getD 0#32).toNat / 2 = other.toNat / 2 := by
            rw [hm_l, hdiv_ot, hEq]
          have h1 : (withEmptyWatchesCore c k).vals[(k.trl[m]?.getD 0#32).toNat]?.getD 0#8 = 1#8 :=
            (hnw.vals_true_iff (k.trl[m]?.getD 0#32).toNat
              (hnw.trail_lits_lt m (by simpa [withEmptyWatchesCore] using hm_te))).mpr
              ⟨m, by simpa [withEmptyWatchesCore] using hm_te, rfl⟩
          have hm_eq_or : (k.trl[m]?.getD 0#32).toNat = other.toNat ∨
              (k.trl[m]?.getD 0#32).toNat = other.toNat ^^^ 1 := by
            rw [nat_xor1_eq other.toNat]
            split <;> omega
          rcases hm_eq_or with heq | hneg
          · have : k.vals[other.toNat]?.getD 0#8 = 1#8 := by
              simpa [withEmptyWatchesCore, heq] using h1
            rw [hun] at this; exact absurd this (by decide)
          · have h2 : k.vals[other.toNat]?.getD 0#8 = 255#8 :=
              (hnw.vals_false_iff other.toNat
                (by simpa [withEmptyWatchesCore] using hother_lt)).mpr
                ⟨m, by simpa [withEmptyWatchesCore] using hm_te, hneg⟩
            rw [hun] at h2; exact absurd h2 (by decide)
        refine ⟨by simpa [k', withEmptyWatchesCore] using hot_lt, ?_, m, hm_te, ?_, ?_⟩
        · have hxx : (not_lit.toNat ^^^ 1) ^^^ 1 = not_lit.toNat := by simp [Nat.xor_assoc]
          have : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [other.toNat, (ld74 &&& 2147483647#32).toNat]) :=
            s13_bin_resolve (not_lit := other.toNat)
              (ot := not_lit.toNat ^^^ 1) (blk := (ld74 &&& 2147483647#32).toNat)
              (by simpa [Nat.xor_assoc] using hot_ent)
              (by rw [hxx]; exact cnfClause_swap2 hent)
          simpa [withEmptyWatchesCore] using this
        · have hne_m : m ≠ k.trail_end := by omega
          simp [k', withEmptyWatchesCore, List.getElem?_set_ne hne_m.symm, hm_trl]
        · have hv_lt_lvl : v < k.lvl.length := by
            have := hl.cur_vars_le; have := hl.lvl_len; change other.toNat / 2 < k.lvl.length; omega
          have hlvl_ot : k'.lvl[(ld74 &&& 2147483647#32).toNat / 2]? =
              k.lvl[(ld74 &&& 2147483647#32).toNat / 2]? :=
            List.getElem?_set_ne hm_var_ne.symm
          have hlvl_v : k'.lvl[v]?.getD 0#32 = alvl := by
            simp [k', List.getElem?_set_self hv_lt_lvl]
          change (k'.lvl[(ld74 &&& 2147483647#32).toNat / 2]?.getD 0#32).toNat ≤
            (k'.lvl[v]?.getD 0#32).toNat
          rw [hlvl_ot, hlvl_v]
          exact Nat.le_trans hm_lvl hnl_le
    · intro idx hidx
      dsimp only
      intro hrsn_ne hrsn_nl
      have hidx' : idx < k.trail_end := by
        rcases Nat.lt_or_eq_of_le
            (Nat.lt_succ_iff.mp (by simpa [k', withEmptyWatchesCore] using hidx)) with hlt | rfl
        · exact hlt
        · have htrl_te : ((withEmptyWatchesCore c k').trl[k.trail_end]?.getD 0#32).toNat =
              other.toNat := by
            simp [k', withEmptyWatchesCore, List.getElem?_set_self hk_te_trl]
          have hrsn_te : (withEmptyWatchesCore c k').rsns[v]?.getD 4294967295#32 = ld74 := by
            simp [k', withEmptyWatchesCore, List.getElem?_set_self hv_lt_rsns]
          rw [htrl_te, show other.toNat / 2 = v by rfl, hrsn_te] at hrsn_nl
          exact False.elim (hld_bin hrsn_nl)
      have hne_idx : idx ≠ k.trail_end := by omega
      have hb := hnw_b.reason_lit_mem idx
        (Nat.lt_succ_of_lt (by simpa [k_b, withEmptyWatchesCore] using hidx'))
      have h1 := hrs_at_lt idx hidx'
      dsimp only [withEmptyWatchesCore] at hb hrsn_ne hrsn_nl ⊢
      rw [h1] at hrsn_ne hrsn_nl ⊢
      simpa [k', k_b, withEmptyWatchesCore, fullArenaClauseLitsCore, fullArenaClauseSizeCore]
        using hb (by simpa [k_b, withEmptyWatchesCore] using hrsn_ne)
          (by simpa [k_b, withEmptyWatchesCore] using hrsn_nl)
  · intro i hi
    have hne_i : i ≠ k.trail_end := by omega
    have htrl_k' : k'.trl[i]? = k.trl[i]? := List.getElem?_set_ne hne_i.symm
    have h1 := hrs_at_lt i hi
    rw [htrl_k'] at h1
    rw [h1]
    exact hrp_b i hi

private theorem s13_bin_jump_rsn_step {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_pi sem : FullState}
    {not_lit blk alvl nl_lvl0 ld74 : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {flags' : List (BitVec 32)}
    {ph' : List (BitVec 8)} {unas' unfl' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
      end_v.toNat)
    (hfl : flags'.length = c.max_vars) (hph : ph'.length = c.max_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hblk_lt : blk.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[blk.toNat]?.getD 0#8 = 0#8)
    (halvl_le : alvl.toNat ≤ sem.core.cur_level) (halvl_nz : alvl ≠ 0#32)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, blk.toNat]))
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hnl_le : (sem.core.lvl[not_lit.toNat / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hnl0_iff : alvl = 0#32 ↔ sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = 0#32)
    (hld_eq : ld74 = sem.core.rsns[not_lit.toNat / 2]?.getD 4294967295#32)
    (hld_ne : ld74 ≠ 4294967295#32) (hld_bin : ld74 &&& 2147483648#32 ≠ 0#32) :
    have sem2 : FullState := {
      core := { sem.core with
        unassigned := unas', unflushed := unfl', trail_end := sem.core.trail_end + 1,
        vals := (sem.core.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 255#8,
        flags := flags', lvl := sem.core.lvl.set (blk.toNat / 2) alvl,
        rsns := sem.core.rsns.set (blk.toNat / 2) ld74,
        trl := sem.core.trl.set sem.core.trail_end blk,
        trail_pos := sem.core.trail_pos.set (blk.toNat / 2)
          (BitVec.ofNat 32 sem.core.trail_end) },
      scratch := { sem.scratch with phases := ph' } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
        end_v.toNat ∧
      sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
  intro sem2
  have hsw2 : SplitWatchesInv F_cur sem2.core not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
      end_v.toNat :=
    SplitWatchesInv.with_nonwatch hpi.sw rfl rfl rfl rfl (fun _ h => h)
  have hnw2 := s13_bin_jump_rsn_nw_step hpi.len.core_ok hpi.nw halvl_le halvl_nz hblk_lt hun
    hnot_lt hpi.not_f hent hnl_le hnl0_iff hld_eq hld_ne hld_bin flags' unas' unfl'
  exact fastPropMem_eq_of_eq (nl_lvl0 := nl_lvl0) hpi hsw2 rfl hfl hph hnot_lt hblk_lt hun hnl
    (by simpa [sem2] using hnw2)

private theorem s13_pi_keep_bin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem : FullState} {not_lit : BitVec 32} {off_v q_v p_v end_v : BitVec 64}
    {w0 : BitVec 32}
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
      end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hp_lt : p_v.toNat < end_v.toNat) (hp_w : sem.core.wstk[p_v.toNat]? = some w0)
    (hbin : w0 &&& 2147483648#32 ≠ 0#32) :
    have sem1 : FullState := {
      core := { sem.core with wstk := sem.core.wstk.set q_v.toNat w0 },
      scratch := sem.scratch }
    q_v.toNat < sem.core.wstk.length ∧
      (p_v + 1#64).toNat = p_v.toNat + 1 ∧
        (q_v + 1#64).toNat = q_v.toNat + 1 ∧
          (w0 &&& 2147483647#32).toNat < 2 * sem.core.cur_vars ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause [not_lit.toNat, (w0 &&& 2147483647#32).toNat]) ∧
              PropLitInv c F0 F_cur s_pi sem1 not_lit.toNat off_v.toNat (q_v + 1#64).toNat
                (p_v + 1#64).toNat end_v.toNat := by
  intro sem1
  have ⟨hblk_lt, hent, hrem'⟩ := watchSlice_inv_bin hpi.sw.rem_slice (by omega) hp_w hbin
  have hsw_adv : SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 1) end_v.toNat :=
    SplitWatchesInv.advance_rem hpi.sw (by omega) (by omega)
      (by simpa [Nat.sub_add_eq] using hrem')
  have hend_wc := SplitWatchesInv.end_lt_wcap hpi.len.core_ok hpi.sw hnot_lt
  have hq_le_p := hpi.sw.q_le_p
  have hp_end := hpi.sw.p_le_end
  have hq_len : q_v.toNat < sem.core.wstk.length := by
    have := hpi.len.core_ok.wstk_len_arr; omega
  have hwcap64 : c.wcap < 2 ^ 64 := by
    have := c.hwcap; have : dimacsBound = 268435456 := rfl; omega
  have hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hsw1 : SplitWatchesInv F_cur sem1.core not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v + 1#64).toNat end_v.toNat := by
    rw [hq1_nat, hp1_nat]
    exact SplitWatchesInv.write_bin hsw_adv hpi.len.core_ok.cur_vars_le hnot_lt
      (by omega) hq_len hbin hblk_lt hent
  have hlen1 : sem1.LengthsOk c := by
    refine ⟨⟨hpi.len.core_ok.vals_len, hpi.len.core_ok.lit_mark_len, hpi.len.core_ok.mrk_len,
      hpi.len.core_ok.flags_len, hpi.len.core_ok.lvl_len, hpi.len.core_ok.rsns_len,
      hpi.len.core_ok.trl_len, hpi.len.core_ok.trail_pos_len, hpi.len.core_ok.tmp_len_arr,
      hpi.len.core_ok.min_clr_len_arr, hpi.len.core_ok.frame_trail_len,
      hpi.len.core_ok.frame_dec_len, hpi.len.core_ok.wvec_len, hpi.len.core_ok.repr_len,
      hpi.len.core_ok.min_stk_len, hpi.len.core_ok.arena_len_arr,
      by simpa [sem1] using hpi.len.core_ok.wstk_len_arr, hpi.len.core_ok.cur_vars_ge,
      hpi.len.core_ok.cur_vars_le, hpi.len.core_ok.arena_len_le, hpi.len.core_ok.wlen_le,
      hpi.len.core_ok.trail_end_le, hpi.len.core_ok.propagated_le, hpi.len.core_ok.tmp_len_le,
      hpi.len.core_ok.min_clr_len_le⟩, hpi.len.scratch_ok⟩
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
    fullWitnessInv_nw_congr hpi.len.core_ok.cur_vars_le hpi.nw rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl
  have hag1 : AgreesExcept propLitCoreMask s_pi.core sem1.core := by
    simpa [AgreesExcept, propLitCoreMask, sem1] using hpi.ag
  refine ⟨hq_len, hp1_nat, hq1_nat, hblk_lt, hent,
    ⟨hlen1, hnw1, hsw1, hag1, hpi.tr, hpi.rsns_pres, hpi.perm, hpi.sc_eq, hpi.not_f⟩⟩

private def s13AssignRsnOk (sem : FullState)
    (not_lit lvl32 rsn_src rsn' : BitVec 32) (isBin : Bool) : Prop :=
  if lvl32 = 0#32 then rsn' = 4294967295#32
  else if isBin then
    rsn' = (not_lit &&& 2147483647#32 ||| 2147483648#32) ∨
      (rsn' = sem.core.rsns[not_lit.toNat / 2]?.getD 4294967295#32 ∧
        rsn' ≠ 4294967295#32 ∧ rsn' &&& 2147483648#32 ≠ 0#32)
  else rsn' = rsn_src

private theorem s13_with_mem {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {e : Expr Val Cont rs} {m : Mem 64} {P : Mem 64 → Prop}
    (hp : P m) (hk : P m → wp Γ Q X e m) : wp Γ Q X e m := hk hp

private theorem s13_lengths_with_assign {c : FullCfg} {sem : FullState}
    (hlen : sem.LengthsOk c) {vs' : List (BitVec 8)} {ph' : List (BitVec 8)}
    {lv' rs' fl' : List (BitVec 32)}
    (hvs : vs'.length = 2 * c.max_vars) (hph : ph'.length = c.max_vars)
    (hlv : lv'.length = c.max_vars) (hrs : rs'.length = c.max_vars)
    (hfl : fl'.length = c.max_vars) :
    FullState.LengthsOk c {
      core := { sem.core with vals := vs', lvl := lv', rsns := rs', flags := fl' },
      scratch := { sem.scratch with phases := ph' } } := by
  have hc := hlen.core_ok; have hs := hlen.scratch_ok
  refine ⟨⟨hvs, hc.lit_mark_len, hc.mrk_len, hfl, hlv, hrs, hc.trl_len, hc.trail_pos_len,
    hc.tmp_len_arr, hc.min_clr_len_arr, hc.frame_trail_len, hc.frame_dec_len, hc.wvec_len,
    hc.repr_len, hc.min_stk_len, hc.arena_len_arr, hc.wstk_len_arr, hc.cur_vars_ge,
    hc.cur_vars_le, hc.arena_len_le, hc.wlen_le, hc.trail_end_le, hc.propagated_le,
    hc.tmp_len_le, hc.min_clr_len_le⟩,
    ⟨hs.walk_vals_len, hph, hs.phases_target_len, hs.phases_best_len, hs.walk_best_len,
      hs.heap_len_arr, hs.pos_len, hs.shrink_stk_len, hs.q_prev_len, hs.q_next_len,
      hs.q_stamp_len, hs.wsort_len, hs.work_stk1_len, hs.work_stk2_len, hs.tarjan_mark_len,
      hs.tarjan_reach_len, hs.score_len, hs.sim_sig_len, hs.glue_used_len, hs.last_learned_len,
      hs.delayed_len_arr, hs.red_refs_len, hs.extend_stk_len, hs.scratch_buf_len⟩⟩

private theorem s13_lp_assign_tail_pi2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi0 sem : FullState} {del0 : List (BitVec 32)}
    {not_lit unit lvl32 rsn_src rsn' : BitVec 32}
    {p_next q_next off_v end_v unas' unfl' : BitVec 64}
    {fl' : List (BitVec 32)} {ph' : List (BitVec 8)} {isBin : Bool}
    (hpi : PropLitInv c F0 F_cur { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
      sem not_lit.toNat off_v.toNat q_next.toNat p_next.toNat end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hunit_lt : unit.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[unit.toNat]?.getD 0#8 = 0#8)
    (hp_ge : if isBin then 1 ≤ p_next.toNat else 2 ≤ p_next.toNat)
    (hsrc : S13AssignSrc F_cur sem.core not_lit unit lvl32 rsn_src isBin)
    (hlvl_le : lvl32.toNat ≤ sem.core.cur_level)
    (hfl'_len : fl'.length = c.max_vars) (hph'_len : ph'.length = c.max_vars)
    (hrsn_ok : s13AssignRsnOk sem not_lit lvl32 rsn_src rsn' isBin) :
    let vs' := (sem.core.vals.set unit.toNat 1#8).set (unit.toNat ^^^ 1) 255#8
    let lv' := sem.core.lvl.set (unit.toNat / 2) lvl32
    let sem2 : FullState := {
      core := { sem.core with
        unassigned := unas', unflushed := unfl', trail_end := sem.core.trail_end + 1,
        vals := vs', flags := fl', lvl := lv',
        rsns := sem.core.rsns.set (unit.toNat / 2) rsn',
        trl := sem.core.trl.set sem.core.trail_end unit,
        trail_pos := sem.core.trail_pos.set (unit.toNat / 2)
          (BitVec.ofNat 32 sem.core.trail_end) },
      scratch := { sem.scratch with phases := ph' } }
    PropLitInv c F0 F_cur { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
      sem2 not_lit.toNat off_v.toNat q_next.toNat p_next.toNat end_v.toNat := by
  intro vs' lv' sem2
  by_cases hlv0 : lvl32 = 0#32
  · have hrsn_eq : rsn' = 4294967295#32 := by simpa [s13AssignRsnOk, hlv0] using hrsn_ok
    subst hrsn_eq
    cases isBin
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp_ge
      dsimp only [S13AssignSrc, Bool.false_eq_true, ↓reduceIte] at hsrc
      rcases hsrc with ⟨hcr31, hcr_ref, hcr_ng, hnot_m, hunit_m, hunit_c, hmaxl, hmaxw⟩
      let p0 : BitVec 64 := BitVec.ofNat 64 (p_next.toNat - 2)
      let q0 : BitVec 64 := q_next - 2#64
      have hp0 : p0.toNat + 2 = p_next.toNat := by
        simp only [p0, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hq0 : (q0 + 2#64).toNat = q_next.toNat := by
        simp only [q0, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hpi0 : PropLitInv c F0 F_cur
          { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
          sem not_lit.toNat off_v.toNat (q0 + 2#64).toNat (p0.toNat + 2) end_v.toNat := by
        simpa [hq0, hp0] using hpi
      have hstep := m7_large_assign_step (unas' := unas') (unfl' := unfl')
        hpi0 hfl'_len hph'_len hcr31 hcr_ref hcr_ng hnot_lt hunit_lt hun hnot_m hunit_m
        hunit_c rfl hmaxl hmaxw
      simpa [hlv0, sem2, vs', lv', hq0, hp0] using hstep.1
    · simp only [↓reduceIte] at hp_ge
      dsimp only [S13AssignSrc, ↓reduceIte] at hsrc
      rcases hsrc with ⟨hnl_eq, hent⟩
      let p0 : BitVec 64 := BitVec.ofNat 64 (p_next.toNat - 1)
      let q0 : BitVec 64 := q_next - 1#64
      have hp0 : p0.toNat + 1 = p_next.toNat := by
        simp only [p0, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hq0 : (q0 + 1#64).toNat = q_next.toNat := by
        simp only [q0, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hpi0 : PropLitInv c F0 F_cur
          { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
          sem not_lit.toNat off_v.toNat (q0 + 1#64).toNat (p0.toNat + 1) end_v.toNat := by
        simpa [hq0, hp0] using hpi
      have hstep := s13_bin_jumpreason_step (unas' := unas') (unfl' := unfl')
        hpi0 hfl'_len hph'_len hnot_lt hunit_lt hun hlvl_le hent hnl_eq
        (by simp [hnl_eq]) (by simp [hnl_eq])
      simpa [hlv0, sem2, vs', lv', hq0, hp0] using hstep.1
  · cases isBin
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp_ge
      dsimp only [S13AssignSrc, Bool.false_eq_true, ↓reduceIte] at hsrc
      rcases hsrc with ⟨hcr31, hcr_ref, hcr_ng, hnot_m, hunit_m, hunit_c, hmaxl, hmaxw⟩
      have hrsn_eq : rsn' = rsn_src := by simpa [s13AssignRsnOk, hlv0] using hrsn_ok
      subst hrsn_eq
      let p0 : BitVec 64 := BitVec.ofNat 64 (p_next.toNat - 2)
      let q0 : BitVec 64 := q_next - 2#64
      have hp0 : p0.toNat + 2 = p_next.toNat := by
        simp only [p0, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hq0 : (q0 + 2#64).toNat = q_next.toNat := by
        simp only [q0, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hpi0 : PropLitInv c F0 F_cur
          { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
          sem not_lit.toNat off_v.toNat (q0 + 2#64).toNat (p0.toNat + 2) end_v.toNat := by
        simpa [hq0, hp0] using hpi
      have hstep := m7_large_assign_step (unas' := unas') (unfl' := unfl')
        hpi0 hfl'_len hph'_len hcr31 hcr_ref hcr_ng hnot_lt hunit_lt hun hnot_m hunit_m
        hunit_c rfl hmaxl hmaxw
      simpa [hlv0, sem2, vs', lv', hq0, hp0] using hstep.1
    · simp only [↓reduceIte] at hp_ge
      dsimp only [S13AssignSrc, ↓reduceIte] at hsrc
      rcases hsrc with ⟨hnl_eq, hent⟩
      simp only [s13AssignRsnOk, hlv0, ↓reduceIte] at hrsn_ok
      rcases hrsn_ok with hrsn_std | ⟨hrsn_ld, hld_ne, hld_bin⟩
      · subst hrsn_std
        let p0 : BitVec 64 := BitVec.ofNat 64 (p_next.toNat - 1)
        let q0 : BitVec 64 := q_next - 1#64
        have hp0 : p0.toNat + 1 = p_next.toNat := by
          simp only [p0, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have hq0 : (q0 + 1#64).toNat = q_next.toNat := by
          simp only [q0, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
        have hpi0 : PropLitInv c F0 F_cur
            { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
            sem not_lit.toNat off_v.toNat (q0 + 1#64).toNat (p0.toNat + 1) end_v.toNat := by
          simpa [hq0, hp0] using hpi
        have hstep := s13_bin_jumpreason_step (unas' := unas') (unfl' := unfl')
          hpi0 hfl'_len hph'_len hnot_lt hunit_lt hun hlvl_le hent hnl_eq
          (by simp [hnl_eq]) (by simp [hnl_eq])
        simpa [hlv0, sem2, vs', lv', hq0, hp0] using hstep.1
      · subst hrsn_ld
        have hstep := s13_bin_jump_rsn_step (unas' := unas') (unfl' := unfl')
          hpi hfl'_len hph'_len hnot_lt hunit_lt hun hlvl_le hlv0 hent hnl_eq
          (by simp [hnl_eq]) (by simp [hnl_eq]) rfl hld_ne hld_bin
        simpa [sem2, vs', lv'] using hstep.1

theorem s13_lp_assign_tail_wp {Γ : Env} {rs : List Ty} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_disk s_pi0 sem0 sem : FullState}
    {del0 : List (BitVec 32)} {dlen : Nat}
    {not_lit unit lvl32 rsn_src : BitVec 32}
    {te un uf di tk_next p_next q_next off_v end_v : BitVec 64}
    {rec_ph nonchrono : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont s13LpSig}
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = sem.core.cur_vars)
    (hsd_pr : sem.core.propagated ≤ s_disk.core.trail_end)
    (hs0_cv : sem.core.cur_vars = sem0.core.cur_vars)
    (hs0_pr : sem.core.propagated = sem0.core.propagated)
    (hs0_dl : sem.scratch.delayed_len = sem0.scratch.delayed_len)
    (hs0_tk : sem.scratch.search_ticks = sem0.scratch.search_ticks)
    (hs0_oom : sem.core.oom = sem0.core.oom)
    (hs0_ct : S13ConflEq sem0.core sem.core)
    (hdel_ok : Spec.DelayedWatchesOk sem.core del0 dlen not_lit.toNat)
    (hdel_eq : c.delayed_cap = 0 → del0 = s_pi0.scratch.delayed)
    (hdi_eq : di.toNat = 3 * dlen) (hdlen_le : dlen ≤ c.delayed_cap)
    (hpi : PropLitInv c F0 F_cur { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
      sem not_lit.toNat off_v.toNat q_next.toNat p_next.toNat end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hunit_lt : unit.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[unit.toNat]?.getD 0#8 = 0#8)
    (hte : te.toNat = sem.core.trail_end)
    {isBin : Bool}
    (hp_ge : if isBin then 1 ≤ p_next.toNat else 2 ≤ p_next.toNat)
    (hsrc : S13AssignSrc F_cur sem.core not_lit unit lvl32 rsn_src isBin)
    (hlvl_le : lvl32.toNat ≤ sem.core.cur_level)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ_lp : ∀ (te' un' uf' : BitVec 64) (sem' : FullState) (m' : Mem 64),
      S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem' not_lit off_v end_v
        te' un' uf' tk_next p_next q_next di m' R →
      wp Γ Q X (Expr.jump J_lp (Arg.var te', Arg.var un', Arg.var uf', Arg.var tk_next,
        Arg.var p_next, Arg.var q_next, Arg.var di, ())) m') :
    wp Γ Q X
      (s13LpAssignTailExpr isBin J_lp c.pVals c.pLevel c.pReason c.pTrail c.pTrailPos
        c.pFlags c.pPhases rec_ph nonchrono not_lit te un uf di tk_next p_next q_next
        unit lvl32 rsn_src) m := by
  let s_pi := { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
  change PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q_next.toNat p_next.toNat
    end_v.toNat at hpi
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hdim : dimacsBound = 268435456 := rfl
  have hcv_le : sem.core.cur_vars ≤ c.max_vars := hpi.len.core_ok.cur_vars_le
  have hunit_xor : (unit ^^^ 1#32).toNat < 2 * sem.core.cur_vars := by
    rw [show (unit ^^^ 1#32).toNat = unit.toNat ^^^ 1 from bv32_xor_1 unit]
    exact nat_xor1_lt hunit_lt
  have hunit_lt_vals : unit.toNat < (fastPropMem s_disk sem).core.vals.length := by
    rw [BcpPropTactics.fastPropMem_vals, hpi.len.core_ok.vals_len]; omega
  have hux_lt_vals : (unit ^^^ 1#32).toNat < (fastPropMem s_disk sem).core.vals.length := by
    rw [BcpPropTactics.fastPropMem_vals, hpi.len.core_ok.vals_len]; omega
  have hte_lt_cv : sem.core.trail_end < sem.core.cur_vars :=
    m7_trail_end_lt_of_unassigned (k := withEmptyWatchesCore c sem.core) hpi.nw
      (by simpa [withEmptyWatchesCore] using hunit_lt)
      (by simpa [withEmptyWatchesCore] using hun)
  have hfp_len : (fastPropMem s_disk sem).LengthsOk c :=
    fastPropMem_lengthsOk hsd_len hpi.len hsd_cv hsd_pr rfl
  let vs' := (sem.core.vals.set unit.toNat 1#8).set (unit.toNat ^^^ 1) 255#8
  let sem_v : FullState := { core := { sem.core with vals := vs' }, scratch := sem.scratch }
  have hvs'_len : vs'.length = 2 * c.max_vars := by
    simp [vs', hpi.len.core_ok.vals_len]
  have hv_lt_mv : unit.toNat / 2 < c.max_vars := by omega
  have hnl_lt_mv : not_lit.toNat / 2 < c.max_vars := by omega
  have hv64_eq : (BitVec.setWidth 64 (unit >>> 1#32)).toNat = unit.toNat / 2 := by
    simp only [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact m7_bv32_rshift1_toNat unit
  have hv64_lt_mv : (BitVec.setWidth 64 (unit >>> 1#32)).toNat < c.max_vars := by
    rw [hv64_eq]; exact hv_lt_mv
  have hux_lt_set : (unit ^^^ 1#32).toNat <
      ((fastPropMem s_disk sem).core.vals.set (BitVec.setWidth 64 unit).toNat 1).length := by
    simpa using hux_lt_vals
  dsimp only [s13LpAssignTailExpr]
  s13_hstraight
  refine s13_with_mem (P := FullMem c (fastPropMem s_disk sem_v) ⋆ R) ?_ (fun hm_v => ?_)
  · rw [← m7_fastPropMem_with_vals]
    dsimp only [vs']
    have hzw_u : (BitVec.setWidth 64 unit).toNat = unit.toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    have hzw_ux : (BitVec.setWidth 64 (unit ^^^ 1#32)).toNat = unit.toNat ^^^ 1 := by
      simp only [BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega)]; exact bv32_xor_1 unit
    have hneg1 : BitVec.setWidth 8 (-1#32) = 255#8 := by decide
    try rw [hzw_u] at hm
    try rw [hzw_ux] at hm
    try rw [hneg1] at hm
    exact hm
  have hlen_v : sem_v.LengthsOk c :=
    s13_lengths_with_assign hpi.len hvs'_len hpi.len.scratch_ok.phases_len
      hpi.len.core_ok.lvl_len hpi.len.core_ok.rsns_len hpi.len.core_ok.flags_len
  have hfp_v : (fastPropMem s_disk sem_v).LengthsOk c :=
    fastPropMem_lengthsOk hsd_len hlen_v hsd_cv (by simpa [sem_v] using hsd_pr) rfl
  have hv64_lt_flags : (BitVec.setWidth 64 (unit >>> 1#32)).toNat <
      (fastPropMem s_disk sem_v).core.flags.length := by
    rw [hv64_eq, BcpPropTactics.fastPropMem_flags, hpi.len.core_ok.flags_len]; omega
  have hv64_lt_ph : (BitVec.setWidth 64 (unit >>> 1#32)).toNat <
      (fastPropMem s_disk sem_v).scratch.phases.length := by
    rw [hv64_eq, BcpPropTactics.fastPropMem_phases, hpi.len.scratch_ok.phases_len]; omega
  apply wp_join_group (fun _ m_j40 => (FullMem c (fastPropMem s_disk sem_v) ⋆ R) m_j40)
  · intro _ b41 m41 hm41
    apply wp_join_group (fun _ m_j42 =>
      ∃ ph' : List (BitVec 8), ph'.length = c.max_vars ∧
        (FullMem c (fastPropMem s_disk
          { core := sem_v.core, scratch := { sem_v.scratch with phases := ph' } }) ⋆ R) m_j42)
    · intro _ _ m42 hm42
      rcases hm42 with ⟨ph', hph'_len, hm42⟩
      let lv' := sem_v.core.lvl.set (unit.toNat / 2) lvl32
      let sem_vp : FullState := {
        core := sem_v.core, scratch := { sem_v.scratch with phases := ph' } }
      let sem_vl : FullState := {
        core := { sem_vp.core with lvl := lv' },
        scratch := sem_vp.scratch }
      have hlv'_len : lv'.length = c.max_vars := by
        simp [lv', sem_v, hpi.len.core_ok.lvl_len]
      have hlen_vl : sem_vl.LengthsOk c :=
        s13_lengths_with_assign hpi.len hvs'_len hph'_len hlv'_len
          hpi.len.core_ok.rsns_len hpi.len.core_ok.flags_len
      have hfp_vl : (fastPropMem s_disk sem_vl).LengthsOk c :=
        fastPropMem_lengthsOk hsd_len hlen_vl hsd_cv
          (by simpa [sem_vl, sem_vp, sem_v] using hsd_pr) rfl
      have hv64_lt_lvl : (BitVec.setWidth 64 (unit >>> 1#32)).toNat <
          (fastPropMem s_disk sem_vp).core.lvl.length := by
        rw [hv64_eq, BcpPropTactics.fastPropMem_lvl, hpi.len.core_ok.lvl_len]; omega
      s13_hstraight
      refine s13_with_mem (P := FullMem c (fastPropMem s_disk sem_vl) ⋆ R) ?_ (fun hm_vl => ?_)
      · dsimp only [sem_vl]
        rw [← m7_fastPropMem_with_lvl]
        dsimp only [lv', sem_vp, sem_v] at hm ⊢
        try rw [hv64_eq] at hm
        exact hm
      have hv64_lt_flags_vl : (BitVec.setWidth 64 (unit >>> 1#32)).toNat <
          (fastPropMem s_disk sem_vl).core.flags.length := by
        rw [hv64_eq, BcpPropTactics.fastPropMem_flags, hpi.len.core_ok.flags_len]; omega
      have hv64_lt_rsns_vl : (BitVec.setWidth 64 (unit >>> 1#32)).toNat <
          (fastPropMem s_disk sem_vl).core.rsns.length := by
        rw [hv64_eq, BcpPropTactics.fastPropMem_rsns, hpi.len.core_ok.rsns_len]; omega
      apply wp_join_group (fun _ m_j46 =>
        ∃ (fl' : List (BitVec 32)) (rsn' : BitVec 32),
          fl'.length = c.max_vars ∧
            s13AssignRsnOk sem not_lit lvl32 rsn_src rsn' isBin ∧
            (FullMem c (fastPropMem s_disk
              { core := { sem_vl.core with
                  flags := fl', rsns := sem_vl.core.rsns.set (unit.toNat / 2) rsn' },
                scratch := sem_vl.scratch }) ⋆ R) m_j46)
      · intro _ b47 m46 hm46
        rcases hm46 with ⟨fl', rsn', hfl'_len, hrsn_ok, hm46⟩
        let sem_vr : FullState := {
          core := { sem_vl.core with
            flags := fl', rsns := sem_vl.core.rsns.set (unit.toNat / 2) rsn' },
          scratch := sem_vl.scratch }
        have hrs'_len : (sem_vl.core.rsns.set (unit.toNat / 2) rsn').length = c.max_vars := by
          simp [sem_vl, sem_vp, sem_v, hpi.len.core_ok.rsns_len]
        have hlen_vr : sem_vr.LengthsOk c :=
          s13_lengths_with_assign hpi.len hvs'_len hph'_len hlv'_len hrs'_len hfl'_len
        have hfp_vr : (fastPropMem s_disk sem_vr).LengthsOk c :=
          fastPropMem_lengthsOk hsd_len hlen_vr hsd_cv
            (by simpa [sem_vr, sem_vl, sem_vp, sem_v] using hsd_pr) rfl
        have hte64_eq : (BitVec.setWidth 64 te).toNat = te.toNat := by
          simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
        have hte64_lt_trl : (BitVec.setWidth 64 te).toNat <
            (fastPropMem s_disk sem_vr).core.trl.length := by
          rw [hte64_eq, BcpPropTactics.fastPropMem_trl, hpi.len.core_ok.trl_len]; omega
        have hv64_lt_tp0 : (BitVec.setWidth 64 (unit >>> 1#32)).toNat <
            (fastPropMem s_disk sem_vr).core.trail_pos.length := by
          rw [hv64_eq, BcpPropTactics.fastPropMem_trail_pos, hpi.len.core_ok.trail_pos_len]
          omega
        s13_hstraight
        let sem2 : FullState := {
          core := { sem.core with
            unassigned := b41.1, unflushed := b47.1, trail_end := sem.core.trail_end + 1,
            vals := vs', flags := fl', lvl := lv',
            rsns := sem.core.rsns.set (unit.toNat / 2) rsn',
            trl := sem.core.trl.set sem.core.trail_end unit,
            trail_pos := sem.core.trail_pos.set (unit.toNat / 2)
              (BitVec.ofNat 32 sem.core.trail_end) },
          scratch := { sem.scratch with phases := ph' } }
        have hm2 : (FullMem c (fastPropMem s_disk sem2) ⋆ R) m := by
          have htr32 : BitVec.truncate 32 te = BitVec.ofNat 32 sem.core.trail_end := by
            apply BitVec.eq_of_toNat_eq
            change te.toNat % 2 ^ 32 = sem.core.trail_end % 2 ^ 32
            rw [hte, Nat.mod_eq_of_lt (by omega)]
          let sem_vt : FullState := {
            core := { sem_vr.core with
              trail_pos := sem_vr.core.trail_pos.set (unit.toNat / 2)
                (BitVec.ofNat 32 sem.core.trail_end) },
            scratch := sem_vr.scratch }
          have heq_mem : fastPropMem s_disk {
              core := { sem_vt.core with trl := sem_vt.core.trl.set te.toNat unit },
              scratch := sem_vt.scratch } = fastPropMem s_disk sem2 := by
            simp [fastPropMem, sem2, sem_vt, sem_vr, sem_vl, sem_vp, sem_v, vs', lv', hte]
          have h_tp_eq := BcpPropTactics.fastPropMem_trail_pos s_disk sem_vr
          have h_tr_eq := BcpPropTactics.fastPropMem_trl s_disk sem_vr
          rw [← heq_mem, ← fastPropMem_with_trl, ← fastPropMem_with_trail_pos]
          dsimp only [sem_vt, sem_vr, sem_vl, sem_vp, sem_v, vs', lv'] at h_tp_eq h_tr_eq hm ⊢
          rw [h_tp_eq, h_tr_eq] at hm
          have hv64_1 : (BitVec.setWidth 64 (unit >>> 1)).toNat = unit.toNat / 2 := hv64_eq
          have htr32_sw : BitVec.setWidth 32 te = BitVec.ofNat 32 sem.core.trail_end := htr32
          try rw [hv64_eq] at hm
          try rw [hv64_1] at hm
          try rw [hte64_eq] at hm
          try rw [htr32] at hm
          try rw [htr32_sw] at hm
          exact hm
        have hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat
            q_next.toNat p_next.toNat end_v.toNat :=
          s13_lp_assign_tail_pi2 (unas' := b41.1) (unfl' := b47.1)
            hpi hnot_lt hunit_lt hun hp_ge hsrc hlvl_le hfl'_len hph'_len hrsn_ok
        have hdel2 : Spec.DelayedWatchesOk sem2.core s_pi.scratch.delayed dlen not_lit.toNat := by
          intro j hj
          simpa [Spec.DelayedWatchesOk, sem2, fullArenaClauseRefsCore]
            using hdel_ok j hj
        refine hJ_lp _ b41.1 b47.1 sem2 _ ⟨del0, dlen, hm2, hpi2, hdel2, hdel_eq,
          ?_, rfl, rfl, hdi_eq, hdlen_le, hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct,
          hsd_len, hsd_cv.trans hs0_cv, hsd_pr⟩
        · simp only [sem2]
          have hte1_eq : (te + 1 : BitVec 64) = te + 1#64 := rfl
          have hte1 : (te + 1#64).toNat = te.toNat + 1 := m7_bv64_add1_toNat (by omega)
          rw [hte1_eq]; omega
      · intro J46 hP46
        s13_hsteps_nogrp
        s13_hsplit
        · have hlv_eq : lvl32 = 0#32 := by simpa using hc
          clear hc
          s13_hsteps_nogrp
          apply hP46
          have hfl_lt : unit.toNat / 2 < sem.core.flags.length := by
            rw [hpi.len.core_ok.flags_len]; omega
          refine ⟨sem_vl.core.flags.set (unit.toNat / 2)
              (sem.core.flags[unit.toNat / 2]?.getD 0#32 &&& ~~~1#32), 4294967295#32,
            by simp [sem_vl, sem_vp, sem_v, hpi.len.core_ok.flags_len],
            by simp [s13AssignRsnOk, hlv_eq], ?_⟩
          let sem_r : FullState := {
            core := { sem_vl.core with
              rsns := sem_vl.core.rsns.set (unit.toNat / 2) 4294967295#32 },
            scratch := sem_vl.scratch }
          have heq_f : fastPropMem s_disk {
              core := { sem_r.core with
                flags := sem_r.core.flags.set (unit.toNat / 2)
                  (sem.core.flags[unit.toNat / 2]?.getD 0#32 &&& ~~~1#32) },
              scratch := sem_r.scratch } = fastPropMem s_disk {
              core := { sem_vl.core with
                flags := sem_vl.core.flags.set (unit.toNat / 2)
                  (sem.core.flags[unit.toNat / 2]?.getD 0#32 &&& ~~~1#32),
                rsns := sem_vl.core.rsns.set (unit.toNat / 2) 4294967295#32 },
              scratch := sem_vl.scratch } := rfl
          rw [← heq_f, ← m7_fastPropMem_with_flags, ← m7_fastPropMem_with_rsns]
          have hfp_fl : (fastPropMem s_disk sem_vl).core.flags = sem.core.flags :=
            BcpPropTactics.fastPropMem_flags s_disk sem_vl
          have hzw_r : (BitVec.setWidth 64 (unit >>> 1#32)).toNat = unit.toNat / 2 := hv64_eq
          have hzw_r1 : (BitVec.setWidth 64 (unit >>> 1)).toNat = unit.toNat / 2 := hv64_eq
          have hfl_val :
              (fastPropMem s_disk sem_vl).core.flags[(BitVec.setWidth 64 (unit >>> 1)).toNat]'
                hv64_lt_flags_vl = sem.core.flags[unit.toNat / 2]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem hfl_lt, Option.getD_some]
            have hcong : ∀ (l1 l2 : List (BitVec 32)), l1 = l2 → ∀ (i j : Nat) h1 h2,
                i = j → l1[i]'h1 = l2[j]'h2 := by
              rintro l _ rfl i _ _ _ rfl; rfl
            exact hcong _ _ hfp_fl _ _ _ _ hzw_r1
          dsimp only [sem_r, sem_vl, sem_vp, sem_v] at hfl_val hfp_fl hm ⊢
          rw [hfl_val] at hm
          rw [hfp_fl] at hm
          try rw [hzw_r] at hm
          try rw [hzw_r1] at hm
          exact hm
        · have hlv_ne : lvl32 ≠ 0#32 := by simpa using hc
          clear hc
          cases isBin
          · rw [ite_eq_right Bool.false_ne_true]
            s13_hsteps_nogrp
            apply hP46
            refine ⟨sem_vl.core.flags, rsn_src, hpi.len.core_ok.flags_len,
              by simp [s13AssignRsnOk, hlv_ne], ?_⟩
            rw [← m7_fastPropMem_with_rsns]
            dsimp only [sem_vl, sem_vp, sem_v] at hm ⊢
            try rw [hv64_eq] at hm
            exact hm
          · rw [ite_eq_left rfl]
            s13_hsteps_nogrp
            have hnot_31 : not_lit.toNat < 2 ^ 31 := by omega
            have hv65_eq : (2147483648#32 ||| not_lit) =
                (not_lit &&& 2147483647#32 ||| 2147483648#32) := by
              rw [m7_bv32_mask7f_eq hnot_31, BitVec.or_comm]
            apply wp_join_group (fun (xs : Tup Val [i32]) m_j66 =>
              m_j66 = m ∧ (xs.1 = (not_lit &&& 2147483647#32 ||| 2147483648#32) ∨
                (xs.1 = sem.core.rsns[not_lit.toNat / 2]?.getD 4294967295#32 ∧
                  xs.1 ≠ 4294967295#32 ∧ xs.1 &&& 2147483648#32 ≠ 0#32)))
            · intro _ b67 m66 ⟨hm66_eq, hb67⟩
              subst hm66_eq
              s13_hsteps_nogrp
              apply hP46
              refine ⟨sem_vl.core.flags, b67.1, hpi.len.core_ok.flags_len,
                by simp [s13AssignRsnOk, hlv_ne, hb67], ?_⟩
              rw [← m7_fastPropMem_with_rsns]
              dsimp only [sem_vl, sem_vp, sem_v] at hm ⊢
              try rw [hv64_eq] at hm
              exact hm
            · intro J66 hP66
              s13_hsplit
              · have hnl_r_eq : (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat =
                    not_lit.toNat / 2 := by
                  simp only [BitVec.toNat_setWidth]
                  rw [Nat.mod_eq_of_lt (by omega)]; exact m7_bv32_rshift1_toNat not_lit
                have hnl_lt_rsns_vl : (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat <
                    (fastPropMem s_disk sem_vl).core.rsns.length := by
                  rw [hnl_r_eq, BcpPropTactics.fastPropMem_rsns]
                  dsimp only [sem_vl, sem_vp, sem_v]
                  rw [hpi.len.core_ok.rsns_len]; exact hnl_lt_mv
                s13_hsteps_nogrp
                apply wp_join_group (fun (xs : Tup Val [i32]) m_j75 =>
                  m_j75 = m ∧ (xs.1 = (not_lit &&& 2147483647#32 ||| 2147483648#32) ∨
                    (xs.1 = sem.core.rsns[not_lit.toNat / 2]?.getD 4294967295#32 ∧
                      xs.1 ≠ 4294967295#32 ∧ xs.1 &&& 2147483648#32 ≠ 0#32)))
                · intro _ b76 _ hm75
                  s13_hsteps_nogrp; exact hP66 _ _ hm75
                · intro J75 hP75
                  s13_hsplit
                  · have hne4 := hc
                    clear hc
                    s13_hsplit
                    · have hbin4 := hc
                      clear hc
                      s13_hsteps_nogrp
                      apply hP75
                      have hl_eq :
                          (fastPropMem s_disk sem_vl).core.rsns[(BitVec.setWidth 64
                            (not_lit >>> 1)).toNat]'hnl_lt_rsns_vl =
                          (fastPropMem s_disk sem_vl).core.rsns[not_lit.toNat / 2]'(by
                            rw [← hnl_r_eq]; exact hnl_lt_rsns_vl) :=
                        (by rintro i _ _ _ rfl; rfl :
                          ∀ (i j : Nat) h1 h2, i = j →
                            (fastPropMem s_disk sem_vl).core.rsns[i]'h1 =
                              (fastPropMem s_disk sem_vl).core.rsns[j]'h2) _ _ _ _ hnl_r_eq
                      refine ⟨rfl, Or.inr ⟨?_, ?_, ?_⟩⟩
                      · rw [hl_eq]
                        have hrsn_lt_len : not_lit.toNat / 2 < sem.core.rsns.length := by
                          rw [hpi.len.core_ok.rsns_len]; omega
                        rw [List.getElem?_eq_getElem hrsn_lt_len, Option.getD_some]
                        have hcong : ∀ (l1 l2 : List (BitVec 32)), l1 = l2 → ∀ h1 h2,
                            l1[not_lit.toNat / 2]'h1 = l2[not_lit.toNat / 2]'h2 := by
                          rintro l _ rfl _ _; rfl
                        exact hcong _ _ (BcpPropTactics.fastPropMem_rsns s_disk sem_vl) _ _
                      · rw [hl_eq]; exact by simpa using hne4
                      · rw [hl_eq]; exact by simpa using hbin4
                    · s13_hsteps_nogrp; exact hP75 _ _ ⟨rfl, Or.inl hv65_eq⟩
                  · s13_hsteps_nogrp; exact hP75 _ _ ⟨rfl, Or.inl hv65_eq⟩
              · s13_hsteps_nogrp; exact hP66 _ _ ⟨rfl, Or.inl hv65_eq⟩
    · intro J42 hP42
      s13_hsteps_nogrp
      s13_hsplit
      · apply wp_join_group (fun _ m_j80 =>
          ∃ ph' : List (BitVec 8), ph'.length = c.max_vars ∧
            (FullMem c (fastPropMem s_disk
              { core := sem_v.core, scratch := { sem_v.scratch with phases := ph' } }) ⋆ R) m_j80)
        · intro _ _ m80 hm80; s13_hsteps_nogrp; exact hP42 () m80 hm80
        · intro J80 hP80
          s13_hsteps_nogrp
          s13_hsplit
          · s13_hsteps_nogrp
            apply hP80
            refine ⟨sem_v.scratch.phases.set (unit.toNat / 2) 255#8,
              by simp [sem_v, hpi.len.scratch_ok.phases_len], ?_⟩
            rw [← m7_fastPropMem_with_phases]
            rw [BcpPropTactics.fastPropMem_phases] at hm
            dsimp only [sem_v] at hm ⊢
            have hzw_r : (BitVec.setWidth 64 (unit >>> 1#32)).toNat = unit.toNat / 2 := hv64_eq
            have hzw_r1 : (BitVec.setWidth 64 (unit >>> 1)).toNat = unit.toNat / 2 := hv64_eq
            have hneg1 : BitVec.setWidth 8 (-1 : BitVec 32) = 255#8 := by decide
            try rw [hzw_r] at hm
            try rw [hzw_r1] at hm
            try rw [hneg1] at hm
            exact hm
          · s13_hsteps_nogrp
            apply hP80
            refine ⟨sem_v.scratch.phases.set (unit.toNat / 2) 1#8,
              by simp [sem_v, hpi.len.scratch_ok.phases_len], ?_⟩
            rw [← m7_fastPropMem_with_phases]
            rw [BcpPropTactics.fastPropMem_phases] at hm
            dsimp only [sem_v] at hm ⊢
            have hzw_r : (BitVec.setWidth 64 (unit >>> 1#32)).toNat = unit.toNat / 2 := hv64_eq
            have hzw_r1 : (BitVec.setWidth 64 (unit >>> 1)).toNat = unit.toNat / 2 := hv64_eq
            have hpos1 : BitVec.setWidth 8 (1 : BitVec 32) = 1#8 := by decide
            try rw [hzw_r] at hm
            try rw [hzw_r1] at hm
            try rw [hpos1] at hm
            exact hm
      · s13_hsteps_nogrp
        exact hP42 () _ ⟨sem_v.scratch.phases, hpi.len.scratch_ok.phases_len, hm41⟩
  · intro J40 hP40
    s13_hstraight
    s13_hsplit
    · s13_hsplit
      · s13_hstraight; exact hP40 _ _ hm_v
      · s13_hstraight; exact hP40 _ _ hm_v
    · s13_hstraight
      exact hP40 _ _ hm_v

theorem s13_lp_bin_wp {isBeyond : Bool} {Γ : Env} {rs : List Ty} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {s_disk s_pi0 sem0 sem : FullState}
    {not_lit nl_lvl w0 : BitVec 32}
    {te un uf tk p q di off_v end_v brk0 : BitVec 64}
    {rec_ph nonchrono : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont s13LpSig} {J_ovf : Cont (s13OvfSig isBeyond)}
    (hinv : S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem not_lit off_v end_v te un uf tk p q di m R)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hp_lt : p.toNat < end_v.toNat) (hp_w : sem.core.wstk[p.toNat]? = some w0)
    (hbin : w0 &&& 2147483648#32 ≠ 0#32)
    (hbrk0 : brk0 = 0#64)
    (hJ_lp : ∀ (te' un' uf' tk' p' q' di' : BitVec 64) (sem' : FullState) (m' : Mem 64),
      S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem' not_lit off_v end_v
        te' un' uf' tk' p' q' di' m' R → p' = p + 1#64 →
      wp Γ Q X (Expr.jump J_lp (Arg.var te', Arg.var un', Arg.var uf', Arg.var tk',
        Arg.var p', Arg.var q', Arg.var di', ())) m')
    (hJ_ovf : ∀ (xs : Tup Val (s13OvfSig isBeyond)) (m' : Mem 64),
      S13OvfExitPred isBeyond c F0 F_cur ignore_ref s_disk s_pi0 sem0 not_lit off_v end_v
        brk0 R xs m' → s13OvfP xs = p + 1#64 →
      J_ovf xs m') :
    wp Γ Q X
      (s13LpBinStepExpr isBeyond c.hdr J_lp J_ovf c.pVals c.pWstk c.pLevel c.pReason
        c.pTrail c.pTrailPos c.pFlags c.pPhases rec_ph nonchrono not_lit nl_lvl w0
        te un uf tk p q di) m := by
  rcases hinv with ⟨del0, dlen, hm, hpi, hdel_ok, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
    hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_s0, hsd_pr⟩
  have hsd_cv : s_disk.core.cur_vars = sem.core.cur_vars := hsd_s0.trans hs0_cv.symm
  have ⟨hq_len, hp1_nat, hq1_nat, hblk_lt, hent, hpi1⟩ :=
    s13_pi_keep_bin hpi hnot_lt hp_lt hp_w hbin
  let blk := w0 &&& 2147483647#32
  change blk.toNat < 2 * sem.core.cur_vars at hblk_lt
  let sem1 : FullState := {
    core := { sem.core with wstk := sem.core.wstk.set q.toNat w0 },
    scratch := sem.scratch }
  have hfp_len : (fastPropMem s_disk sem).LengthsOk c :=
    fastPropMem_lengthsOk hsd_len hpi.len hsd_cv hsd_pr rfl
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hdim : dimacsBound = 268435456 := rfl
  have hcv_le : sem.core.cur_vars ≤ c.max_vars := hpi.len.core_ok.cur_vars_le
  have hblk_lt_vals : blk.toNat < (fastPropMem s_disk sem).core.vals.length := by
    rw [BcpPropTactics.fastPropMem_vals, hpi.len.core_ok.vals_len]; omega
  dsimp only [s13LpBinStepExpr]
  s13_hstraight
  refine s13_with_mem (P := FullMem c (fastPropMem s_disk sem1) ⋆ R) ?_ (fun hm1 => ?_)
  · rw [← fastPropMem_with_wstk]
    dsimp only [sem1] at hm ⊢
    try rw [show (BitVec.setWidth 64 q).toNat = q.toNat from by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)] at hm
    exact hm
  have hdel1 : Spec.DelayedWatchesOk sem1.core del0 dlen not_lit.toNat := by
    intro j hj; simpa [Spec.DelayedWatchesOk, sem1, fullArenaClauseRefsCore] using hdel_ok j hj
  have hdom := hpi.nw.vals_domain blk.toNat (by simpa [withEmptyWatchesCore] using hblk_lt)
  have hblk64_eq : (BitVec.setWidth 64 (w0 &&& 2147483647#32)).toNat = blk.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hval_get : (fastPropMem s_disk sem).core.vals[(w0 &&& 2147483647).toNat]'(by
        simpa [blk] using hblk_lt_vals) =
      (withEmptyWatchesCore c sem.core).vals[blk.toNat]?.getD 0#8 := by
    have h1 : blk.toNat < sem.core.vals.length := by
      rw [← BcpPropTactics.fastPropMem_vals]; exact hblk_lt_vals
    have h2 : (fastPropMem s_disk sem).core.vals[blk.toNat]'hblk_lt_vals =
        sem.core.vals[blk.toNat]?.getD 0#8 := by
      simp [BcpPropTactics.fastPropMem_vals, List.getElem?_eq_getElem h1]
    simpa [blk, withEmptyWatchesCore] using h2
  s13_hsplit
  · refine hJ_lp _ _ _ _ _ _ _ sem1 _ ?_ rfl
    exact ⟨del0, dlen, hm1, hpi1, hdel1, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
      hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_s0, hsd_pr⟩
  · have hgt_f := hc; clear hc
    s13_hstraight
    s13_hsplit
    · have hslt_t := hc; clear hc
      have hblk_f : sem1.core.vals[blk.toNat]?.getD 0#8 = 255#8 := by
        rw [hval_get] at hslt_t
        rcases hdom with h0 | h1 | h255
        · rw [h0] at hslt_t; exact absurd hslt_t (by decide)
        · rw [h1] at hslt_t; exact absurd hslt_t (by decide)
        · simpa [sem1, withEmptyWatchesCore] using h255
      cases isBeyond
      · dsimp only [s13OvfJump]
        have hfp1_len : (fastPropMem s_disk sem1).LengthsOk c :=
          fastPropMem_lengthsOk hsd_len hpi1.len (by simpa [sem1] using hsd_cv)
            (by simpa [sem1] using hsd_pr) rfl
        s13_hstraight
        let sem2 : FullState := {
          core := { sem1.core with
            confl_type := 1#64, confl_lit0 := BitVec.setWidth 64 not_lit,
            confl_lit1 := BitVec.setWidth 64 blk },
          scratch := sem1.scratch }
        have hc_res := propLit_bin_confl (not_lit_v := not_lit) (other_v := blk) hpi1 rfl
          (by simpa [sem1] using hnot_lt) (by simpa [sem1] using hblk_lt) hblk_f
          (by simpa [blk, BitVec.toNat_and, sem1] using hent)
        let sem2_confl : FullState := {
          core := { sem1.core with
            confl_type := 1#64, confl_ref := 4294967295#64,
            confl_lit0 := BitVec.setWidth 64 not_lit,
            confl_lit1 := BitVec.setWidth 64 blk },
          scratch := sem1.scratch }
        have hconfl2 : PropLitConfl F_cur ignore_ref sem2.core := by
          have hc_ok : FullConflOkW F_cur sem2.core := by
            have := hc_res.2.1
            simpa [FullConflOkW, sem2, sem2_confl] using this
          exact ⟨hc_ok, fun hct => by simp [sem2] at hct⟩
        have hnw2 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem2.core) := by
          have hnwc := hc_res.1.nw
          exact FullWitnessInv.mk hnwc.ext_sound hnwc.inconsistent_sound
            (by simpa [sem2, sem2_confl, withEmptyWatchesCore] using hnwc.arena)
            (by simpa [sem2, sem2_confl, withEmptyWatchesCore] using hnwc.watches)
            hnwc.cur_level_le hnwc.trail_lits_lt hnwc.trail_vars_nodup hnwc.vals_domain
            hnwc.vals_true_iff hnwc.vals_false_iff hnwc.lvl_le hnwc.dec_earliest
            hnwc.levels_inhabited hnwc.level0_sound hnwc.trail_pos_inv hnwc.level0_rsn_none
            hnwc.frame_trail_lt hnwc.frame_trail_mono hnwc.frame_trail_before_lt
            hnwc.frame_dec_lt
            (by simpa [sem2, sem2_confl, withEmptyWatchesCore] using hnwc.reason_inv)
            (by simpa [sem2, sem2_confl, withEmptyWatchesCore] using hnwc.reason_lit_mem)
        have hpi2 : PropLitInv c F0 F_cur
            { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
            sem2 not_lit.toNat off_v.toNat (q + 1#64).toNat (p + 1#64).toNat end_v.toNat := by
          have hag2 : AgreesExcept propLitCoreMask s_pi0.core sem2.core := by
            simpa [AgreesExcept, propLitCoreMask, sem2] using hpi1.ag
          refine ⟨⟨⟨hpi1.len.core_ok.vals_len, hpi1.len.core_ok.lit_mark_len,
            hpi1.len.core_ok.mrk_len, hpi1.len.core_ok.flags_len, hpi1.len.core_ok.lvl_len,
            hpi1.len.core_ok.rsns_len, hpi1.len.core_ok.trl_len, hpi1.len.core_ok.trail_pos_len,
            hpi1.len.core_ok.tmp_len_arr, hpi1.len.core_ok.min_clr_len_arr,
            hpi1.len.core_ok.frame_trail_len, hpi1.len.core_ok.frame_dec_len,
            hpi1.len.core_ok.wvec_len, hpi1.len.core_ok.repr_len, hpi1.len.core_ok.min_stk_len,
            hpi1.len.core_ok.arena_len_arr, hpi1.len.core_ok.wstk_len_arr,
            hpi1.len.core_ok.cur_vars_ge, hpi1.len.core_ok.cur_vars_le,
            hpi1.len.core_ok.arena_len_le, hpi1.len.core_ok.wlen_le, hpi1.len.core_ok.trail_end_le,
            hpi1.len.core_ok.propagated_le, hpi1.len.core_ok.tmp_len_le,
            hpi1.len.core_ok.min_clr_len_le⟩, hpi1.len.scratch_ok⟩,
            hnw2, SplitWatchesInv.with_nonwatch hpi1.sw rfl rfl rfl rfl (fun _ h => h), hag2,
            by simpa [FullTrailExt, sem2, sem1] using hpi1.tr,
            by simpa [Spec.FullTrailRsnsPres, sem2, sem1] using hpi1.rsns_pres,
            by simpa [FullArenaPermEq, fullArenaClauseRefsCore, fullArenaClauseSizeCore,
              fullArenaClauseGarbCore, fullArenaClauseLitsCore, fullArenaHdrCore,
              sem2, sem1] using hpi1.perm,
            by simpa [sem2] using hpi1.sc_eq, by simpa [sem2] using hpi1.not_f⟩
        have hdel2 : Spec.DelayedWatchesOk sem2.core del0 dlen not_lit.toNat := by
          intro j hj; simpa [Spec.DelayedWatchesOk, sem2, fullArenaClauseRefsCore] using hdel1 j hj
        refine hJ_ovf _ _ ?_ rfl
        refine ⟨sem2, del0, dlen, ?_, hpi2, hdel2, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
          hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hsd_len, hsd_s0, hsd_pr,
          by simpa [hbrk0] using hconfl2⟩
        · dsimp only [sem2]
          rw [← fid_fastPropMem_with_bin_confl]
          exact hm
      · dsimp only [s13OvfJump]
        refine hJ_lp _ _ _ _ _ _ _ sem1 _ ?_ rfl
        exact ⟨del0, dlen, hm1, hpi1, hdel1, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
          hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_s0, hsd_pr⟩
    · have hslt_f := hc; clear hc
      have hblk_un : sem1.core.vals[blk.toNat]?.getD 0#8 = 0#8 := by
        rw [hval_get] at hgt_f hslt_f
        rcases hdom with h0 | h1 | h255
        · simpa [sem1, withEmptyWatchesCore] using h0
        · rw [h1] at hgt_f; exact absurd hgt_f (by decide)
        · rw [h255] at hslt_f; exact absurd hslt_f (by decide)
      have hnl_le : nl_lvl.toNat ≤ sem1.core.cur_level := by
        have hnot_idx : ∃ idx, idx < sem.core.trail_end ∧
            (sem.core.trl[idx]?.getD 0#32).toNat = not_lit.toNat ^^^ 1 :=
          (hpi.nw.vals_false_iff not_lit.toNat (by simpa [withEmptyWatchesCore] using hnot_lt)).mp
            (by simpa [withEmptyWatchesCore] using hpi.not_f)
        rcases hnot_idx with ⟨idx, hidx, htrl⟩
        have hle := hpi.nw.lvl_le idx (by simpa [withEmptyWatchesCore] using hidx)
        have hdiv : (not_lit.toNat ^^^ 1) / 2 = not_lit.toNat / 2 := nat_xor1_div2 not_lit.toNat
        simpa [sem1, withEmptyWatchesCore, htrl, hdiv, hnl] using hle
      s13_hstraight
      exact s13_lp_assign_tail_wp (sem := sem1) hsd_len (by simpa [sem1] using hsd_cv)
        (by simpa [sem1] using hsd_pr) hs0_cv (by simpa [sem1] using hs0_pr)
        (by simpa [sem1] using hs0_dl) (by simpa [sem1] using hs0_tk)
        (by simpa [sem1] using hs0_oom) (by simpa [sem1] using hs0_ct) hdel1 hdel_eq
        hdi_eq hdlen_le hpi1 (by simpa [sem1] using hnot_lt) (by simpa [sem1] using hblk_lt)
        hblk_un (by simpa [sem1] using hte.symm) (by simp [hp1_nat])
        ⟨by simpa [sem1] using hnl,
          by change (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, blk.toNat]);
             exact hent⟩
        hnl_le hm1
        (fun te' un' uf' sem' m' hinv' =>
          hJ_lp te' un' uf' (tk + 1#64) _ _ di sem' m' hinv' rfl)

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
