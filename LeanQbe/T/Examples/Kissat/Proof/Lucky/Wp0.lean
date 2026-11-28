/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
public import LeanQbe.T.Examples.Kissat.Src.Lucky
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Lucky.Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proofs for `Kissat.Src.Lucky` Part 0 (`Wp0`)

Proves `full_lucky_ord_fid_wp` and `full_lucky_polar_m7_wp` (factored into small
`< 250`-line helpers) with zero legacy imports.
-/

set_option autoImplicit false

local elab "lk0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local elab "lk0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := true } 10000

local macro "lk0_to_group" : tactic =>
  `(tactic| (
    (try first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _)
    lk0_hfast_nogrp))

private theorem lk0_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem lk0_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem lk0_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "lk0_strip" : tactic =>
  `(tactic| first | apply lk0_strip_32_64 | apply lk0_strip_8_32 | apply lk0_strip_8_64)

local macro "lk0_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _)

local elab "lk0_hsteps_ns" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local macro "lk0_hsteps_raw" : tactic =>
  `(tactic| (
    (try lk0_unmdata)
    (repeat lk0_strip)
    lk0_hsteps_ns
    repeat (any_goals (lk0_strip; repeat lk0_strip); lk0_hsteps_ns)))

local macro "lk0_steps" : tactic =>
  `(tactic| (
    (try lk0_unmdata)
    (repeat lk0_strip)
    c0_steps
    repeat (any_goals (lk0_strip; repeat lk0_strip); c0_steps)))

open Lean Elab Tactic in
local elab "lk0_to_group_step" : tactic => do
  for _ in [:500] do
    let mut progressed := false
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g'' ← g.change ty (checkDefEq := false)
        replaceMainGoal [g'']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push (← getMainGoal)
      else if ← LeanQbe.T.C0Step.stepOnce then
        progressed := true
        evalTactic (← `(tactic| all_goals (try (repeat lk0_strip))))
        out := out ++ (← getUnsolvedGoals)
      else
        out := out.push (← getMainGoal)
    setGoals out.toList
    if !progressed then break

local macro "lk0_to_group_ns" : tactic =>
  `(tactic| ((try lk0_unmdata); (repeat lk0_strip); lk0_to_group_step))

open Lean Elab Tactic in
local elab "lk0_split" : tactic => do
  for _ in [:120] do
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step))
      break
    evalTactic (← `(tactic| all_goals (repeat lk0_strip)))
    if ← Lean.Elab.Tactic.tryTactic (evalTactic (← `(tactic| c0_step))) then
      evalTactic (← `(tactic| all_goals (repeat lk0_strip)))
    else
      break

local macro "lk0_call" hSpec:term : tactic =>
  `(tactic| (
    lk0_unmdata
    refine LeanQbe.T.wp_call_of_spec _ _ ($hSpec _ _ _ _ ?_)
    try c0_let_simp))

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Lucky

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Lucky
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6ProofUtilTactics

/-! ## 1. `full_lucky_ord_fid_wp` -/

private theorem ord_fid_fallback_wp {Γ : Env} {c : FullCfg} {s s0 : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m0 : Mem 64}
    (hmaxv : c.max_vars < 2 ^ 29) (hcore0 : s0.core = s.core)
    (hlen0 : s0.LengthsOk c) (hext0 : FullExtScratchPres s s0) (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ : ∀ (r : Tup Val [i64]) (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c → r.1.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q r m') :
    wp Γ Q X
      (Expr.group (sig := [[i64]])
        (fun Js =>
          Blocks.cons
            (fun (p : Tup Val [i64]) =>
              Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                  (Arg.var p.fst, Arg.var (BitVec.ofNat 64 s.core.cur_vars), ())) fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_2 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanReach, Arg.var p_2.fst, ()))
                      fun p_3 =>
                      Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p.fst, ())) fun p_4 =>
                        Expr.store (t := i32) (Arg.var p_4.fst) (Arg.var p_3.fst)
                          (Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                            Expr.jump Js.fst (Arg.var p.fst, ())))
                  (Expr.ret (Arg.var (BitVec.ofNat 64 s.core.cur_vars), ())))
            Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m0 := by
  have hcv_le := hlen0.core_ok.cur_vars_le
  rw [hcore0] at hcv_le
  refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s0 R (fun _ => True) trivial
    (fun s1 (v, ()) => v.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s1)
    (fun (v, ()) => s.core.cur_vars - v.toNat)
    (fun Jv hJv => by
      c0_hsteps
      exact hJv s0 (0#64, ()) m0 hm0 rfl hlen0 ⟨Nat.zero_le _, hext0⟩)
    (fun Jv s1 (v, ()) m1 hcore1 hs1 _ ⟨hv_le, hext1⟩ hm1 hJv => ?_)
  dsimp only [fullSafetySlice] at hcore1 hs1 hm1
  have htr1 := hs1.scratch_ok.tarjan_reach_len
  c0_hsteps_nogrp
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    have hv_tr : v.toNat < s1.scratch.tarjan_reach.length := by rw [htr1]; omega
    have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
    let s1' : FullState :=
      { s1 with scratch := { s1.scratch with
          tarjan_reach := s1.scratch.tarjan_reach.set v.toNat (v.setWidth 32) } }
    c0_hsteps
    refine hJv s1' (v + 1#64, ()) _ ?_ (by dsimp only; rw [hv1]; omega)
      rfl ⟨hs1.core_ok, { hs1.scratch_ok with
        tarjan_reach_len := by dsimp only [s1']; rw [List.length_set, htr1] }⟩
      ⟨by rw [hv1]; omega, hext1⟩
    dsimp only [fullSafetySlice]; exact by assumption
  · c0_hsteps
    refine hQ _ s1 m1 (Eq.trans hcore1 hcore0) hs1 ⟨?_, hext1⟩ hm1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _

private theorem ord_fid_post_mark_wp {Γ : Env} {c : FullCfg} {s s0 : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m0 : Mem 64} {len0 : Val i64}
    (hmaxv : c.max_vars < 2 ^ 29) (hlen0_le : len0.toNat ≤ c.max_vars)
    (hcore0 : s0.core = s.core) (hlen0 : s0.LengthsOk c)
    (hext0 : FullExtScratchPres s s0) (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ : ∀ (r : Tup Val [i64]) (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c → r.1.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q r m') :
    wp Γ Q X
      (Expr.group (sig := [[i64]])
        (fun Js =>
          Blocks.cons
            (fun (p : Tup Val [i64]) =>
              Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                  (Arg.var p.fst, Arg.var (BitVec.ofNat 64 s.core.cur_vars), ())) fun p_2 =>
                Expr.jnz (Arg.var p_2.fst)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_3 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanMark, Arg.var p_3.fst, ()))
                      fun p_4 =>
                      Expr.store (t := i32) (Arg.imm 0) (Arg.var p_4.fst)
                        (Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                          Expr.jump Js.fst (Arg.var p.fst, ())))
                  (Expr.group (sig := [[i64, i64]])
                    (fun Js =>
                      Blocks.cons
                        (fun (p : Tup Val [i64, i64]) =>
                          Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                              (Arg.var p.fst, Arg.var len0, ())) fun p_3 =>
                            Expr.jnz (Arg.var p_3.fst)
                              (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ()))
                                fun p_4 =>
                                Expr.let_ (Op.mk (.add i64)
                                    (Arg.var c.pTarjanReach, Arg.var p_4.fst, ()))
                                  fun p_5 =>
                                  Expr.load i32 (Arg.var p_5.fst) fun ld =>
                                    Expr.group (sig := [[i64]])
                                      (fun _Js_1 =>
                                        Blocks.cons
                                          (fun (p_6 : Tup Val [i64]) =>
                                            Expr.let_ (Op.mk (.add i64)
                                                (Arg.var p.fst, Arg.imm 1, ()))
                                              fun p =>
                                              Expr.jump Js.fst (Arg.var p.fst, Arg.var p_6.fst, ()))
                                          Blocks.nil)
                                      fun Js =>
                                      Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_6 =>
                                        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                                            (Arg.var p_6.fst,
                                              Arg.var (BitVec.ofNat 64 s.core.cur_vars), ()))
                                          fun p_7 =>
                                          Expr.jnz (Arg.var p_7.fst)
                                            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ()))
                                              fun p_8 =>
                                              Expr.let_ (Op.mk (.mul i64)
                                                  (Arg.var p_8.fst, Arg.imm 4, ()))
                                                fun p_9 =>
                                                Expr.let_ (Op.mk (.add i64)
                                                    (Arg.var c.pTarjanMark, Arg.var p_9.fst, ()))
                                                  fun p_10 =>
                                                  Expr.load i32 (Arg.var p_10.fst) fun ld_1 =>
                                                    Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl)
                                                        (Arg.var ld_1, Arg.imm 0, ())) fun p_11 =>
                                                      Expr.jnz (Arg.var p_11.fst)
                                                        (Expr.let_
                                                          (Op.mk (.cmp .ult i64 Ty.bool rfl)
                                                            (Arg.var p.snd.fst,
                                                              Arg.var
                                                                (BitVec.ofNat 64 s.core.cur_vars),
                                                              ()))
                                                          fun p_12 =>
                                                          Expr.jnz (Arg.var p_12.fst)
                                                            (Expr.let_
                                                              (Op.mk (.zext 32 64) (Arg.var ld, ()))
                                                              fun p_13 =>
                                                              Expr.let_ (Op.mk (.mul i64)
                                                                  (Arg.var p_13.fst, Arg.imm 4, ()))
                                                                fun p_14 =>
                                                                Expr.let_ (Op.mk (.add i64)
                                                                    (Arg.var c.pTarjanMark,
                                                                      Arg.var p_14.fst, ()))
                                                                  fun p_15 =>
                                                                  Expr.store (t := i32) (Arg.imm 1)
                                                                    (Arg.var p_15.fst)
                                                                    (Expr.let_ (Op.mk (.mul i64)
                                                                        (Arg.var p.snd.fst,
                                                                          Arg.imm 4, ()))
                                                                      fun p_16 =>
                                                                      Expr.let_ (Op.mk (.add i64)
                                                                          (Arg.var c.pTarjanReach,
                                                                            Arg.var p_16.fst, ()))
                                                                        fun p_17 =>
                                                                        Expr.store (t := i32)
                                                                          (Arg.var ld)
                                                                          (Arg.var p_17.fst)
                                                                          (Expr.let_
                                                                            (Op.mk (.add i64)
                                                                              (Arg.var p.snd.fst,
                                                                                Arg.imm 1, ()))
                                                                            fun p_18 =>
                                                                            Expr.jump Js.fst
                                                                              (Arg.var p_18.fst,
                                                                                ()))))
                                                            (Expr.jump Js.fst
                                                              (Arg.var p.snd.fst, ())))
                                                        (Expr.jump Js.fst (Arg.var p.snd.fst, ())))
                                            (Expr.jump Js.fst (Arg.var p.snd.fst, ())))
                              (Expr.group (sig := [[i64, i64]])
                                (fun Js =>
                                  Blocks.cons
                                    (fun (p : Tup Val [i64, i64]) =>
                                      Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                                          (Arg.var p.snd.fst,
                                            Arg.var (BitVec.ofNat 64 s.core.cur_vars), ()))
                                        fun p_4 =>
                                        Expr.jnz (Arg.var p_4.fst)
                                          (Expr.group (sig := [[i64]])
                                            (fun _Js_1 =>
                                              Blocks.cons
                                                (fun (p_5 : Tup Val [i64]) =>
                                                  Expr.let_ (Op.mk (.add i64)
                                                      (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
                                                    Expr.jump Js.fst
                                                      (Arg.var p_5.fst, Arg.var p.fst, ()))
                                                Blocks.nil)
                                            fun Js =>
                                            Expr.let_ (Op.mk (.mul i64)
                                                (Arg.var p.snd.fst, Arg.imm 4, ()))
                                              fun p_5 =>
                                              Expr.let_ (Op.mk (.add i64)
                                                  (Arg.var c.pTarjanMark, Arg.var p_5.fst, ()))
                                                fun p_6 =>
                                                Expr.load i32 (Arg.var p_6.fst) fun ld =>
                                                  Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl)
                                                      (Arg.var ld, Arg.imm 0, ())) fun p_7 =>
                                                    Expr.jnz (Arg.var p_7.fst)
                                                      (Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                                                          (Arg.var p.fst,
                                                            Arg.var
                                                              (BitVec.ofNat 64 s.core.cur_vars),
                                                            ()))
                                                        fun p_8 =>
                                                        Expr.jnz (Arg.var p_8.fst)
                                                          (Expr.let_ (Op.mk (.mul i64)
                                                              (Arg.var p.fst, Arg.imm 4, ()))
                                                            fun p_9 =>
                                                            Expr.let_ (Op.mk (.add i64)
                                                                (Arg.var c.pTarjanReach,
                                                                  Arg.var p_9.fst, ()))
                                                              fun p_10 =>
                                                              Expr.let_ (Op.mk (.trunc 64 32)
                                                                  (Arg.var p.snd.fst, ()))
                                                                fun p_11 =>
                                                                Expr.store (t := i32)
                                                                  (Arg.var p_11.fst)
                                                                  (Arg.var p_10.fst)
                                                                  (Expr.let_ (Op.mk (.add i64)
                                                                      (Arg.var p.fst, Arg.imm 1,
                                                                        ()))
                                                                    fun p =>
                                                                    Expr.jump Js.fst
                                                                      (Arg.var p.fst, ())))
                                                          (Expr.jump Js.fst (Arg.var p.fst, ())))
                                                      (Expr.jump Js.fst (Arg.var p.fst, ())))
                                          (Expr.ret (Arg.var p.fst, ())))
                                    Blocks.nil)
                                fun Js => Expr.jump Js.fst (Arg.var p.snd.fst, Arg.imm 0, ())))
                        Blocks.nil)
                    fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())))
            Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m0 := by
  have hcv_le := hlen0.core_ok.cur_vars_le; rw [hcore0] at hcv_le
  refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s0 R (fun _ => True) trivial
    (fun s1 (i, ()) => i.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s1)
    (fun (i, ()) => s.core.cur_vars - i.toNat)
    (fun Ji hJi => by c0_hsteps; exact hJi s0 (0#64, ()) m0 hm0 rfl hlen0 ⟨Nat.zero_le _, hext0⟩)
    (fun Ji s1 (i, ()) m1 hcore1 hs1 _ ⟨hi_le, hext1⟩ hm1 hJi => ?_)
  dsimp only [fullSafetySlice] at hcore1 hs1 hm1
  have htm1 := hs1.scratch_ok.tarjan_mark_len
  c0_hsteps_nogrp
  · have hi_lt : i.toNat < s.core.cur_vars := by c0_bound
    have hi_tm : i.toNat < s1.scratch.tarjan_mark.length := by rw [htm1]; omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    let s1' : FullState :=
      { s1 with scratch :=
          { s1.scratch with tarjan_mark := s1.scratch.tarjan_mark.set i.toNat 0#32 } }
    c0_hsteps
    refine hJi s1' (i + 1#64, ()) _ ?_ (by dsimp only; rw [hi1]; omega)
      rfl ⟨hs1.core_ok, { hs1.scratch_ok with
        tarjan_mark_len := by dsimp only [s1']; rw [List.length_set, htm1] }⟩
      ⟨by rw [hi1]; omega, hext1⟩
    dsimp only [fullSafetySlice]; exact by assumption
  · refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s1 R (fun _ => True) trivial
      (fun s2 (i2, out_n, ()) => i2.toNat ≤ len0.toNat ∧ out_n.toNat ≤ s.core.cur_vars ∧
        FullExtScratchPres s s2)
      (fun (i2, _, ()) => len0.toNat - i2.toNat)
      (fun J2 hJ2 => by
        c0_hsteps
        exact hJ2 s1 (0#64, 0#64, ()) m1 hm1 rfl hs1 ⟨Nat.zero_le _, Nat.zero_le _, hext1⟩)
      (fun J2 s2 (i2, out_n, ()) m2 hcore2 hs2 _ ⟨hi2_le, ho2_le, hext2⟩ hm2 hJ2 => ?_)
    dsimp only [fullSafetySlice] at hcore2 hs2 hm2
    have htr2 := hs2.scratch_ok.tarjan_reach_len
    have htm2 := hs2.scratch_ok.tarjan_mark_len
    c0_hsteps_nogrp
    · have hi2_lt : i2.toNat < len0.toNat := by c0_bound
      have hi2_tr : i2.toNat < s2.scratch.tarjan_reach.length := by rw [htr2]; omega
      have hi2_1 : (i2 + 1#64).toNat = i2.toNat + 1 := by bv_omega
      let ld := s2.scratch.tarjan_reach[i2.toNat]
      refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s2 R (fun _ => True) trivial
        (fun s3 (out_n', ()) => out_n'.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s3)
        (fun Jk s3 (out_n', ()) m3 hcore3 hs3 _ ⟨ho3_le, hext3⟩ hm3 => ?_)
        (fun Jk hJk => ?_)
      · rw [Blocks.get_here]; c0_hsteps
        exact hJ2 s3 (i2 + 1#64, out_n', ()) m3 hm3 (by dsimp only; rw [hi2_1]; omega)
          hcore3 hs3 ⟨by rw [hi2_1]; omega, ho3_le, hext3⟩
      · c0_hsteps_nogrp
        · have hv_lt : ld.toNat < s.core.cur_vars := by dsimp only [ld]; c0_bound
          have ho2_lt : out_n.toNat < s.core.cur_vars := by c0_bound
          have ho2_1 : (out_n + 1#64).toNat = out_n.toNat + 1 := by bv_omega
          let s2' : FullState :=
            { s2 with scratch := { s2.scratch with
                tarjan_mark := s2.scratch.tarjan_mark.set ld.toNat 1#32
                tarjan_reach := s2.scratch.tarjan_reach.set out_n.toNat ld } }
          refine hJk s2' (out_n + 1#64, ()) _ ?_ rfl
            ⟨hs2.core_ok, { hs2.scratch_ok with
              tarjan_mark_len := by dsimp only [s2']; rw [List.length_set, htm2],
              tarjan_reach_len := by dsimp only [s2']; rw [List.length_set, htr2] }⟩
            ⟨by rw [ho2_1]; omega, hext2⟩
          dsimp only [fullSafetySlice]; exact by assumption
        all_goals exact hJk s2 (out_n, ()) m2 hm2 rfl hs2 ⟨ho2_le, hext2⟩
    · refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s2 R
        (fun _ => True) trivial
        (fun s3 (out_n3, v3, ()) => out_n3.toNat ≤ s.core.cur_vars ∧ v3.toNat ≤ s.core.cur_vars ∧
          FullExtScratchPres s s3)
        (fun (_, v3, ()) => s.core.cur_vars - v3.toNat)
        (fun J3 hJ3 => by
          c0_hsteps
          exact hJ3 s2 (out_n, 0#64, ()) m2 hm2 rfl hs2 ⟨ho2_le, Nat.zero_le _, hext2⟩)
        (fun J3 s3 (out_n3, v3, ()) m3 hcore3 hs3 _ ⟨ho3_le, hv3_le, hext3⟩ hm3 hJ3 => ?_)
      dsimp only [fullSafetySlice] at hcore3 hs3 hm3
      have htr3 := hs3.scratch_ok.tarjan_reach_len
      have htm3 := hs3.scratch_ok.tarjan_mark_len
      c0_hsteps_nogrp
      · have hv3_lt : v3.toNat < s.core.cur_vars := by c0_bound
        have hv3_tm : v3.toNat < s3.scratch.tarjan_mark.length := by rw [htm3]; omega
        have hv3_1 : (v3 + 1#64).toNat = v3.toNat + 1 := by bv_omega
        refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s3 R (fun _ => True) trivial
          (fun s4 (out_n4, ()) => out_n4.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s4)
          (fun Jk s4 (out_n4, ()) m4 hcore4 hs4 _ ⟨ho4_le, hext4⟩ hm4 => ?_)
          (fun Jk hJk => ?_)
        · rw [Blocks.get_here]; c0_hsteps
          exact hJ3 s4 (out_n4, v3 + 1#64, ()) m4 hm4 (by dsimp only; rw [hv3_1]; omega)
            hcore4 hs4 ⟨ho4_le, by rw [hv3_1]; omega, hext4⟩
        · c0_hsteps_nogrp
          all_goals
            first
            | exact hJk s3 (out_n3, ()) m3 hm3 rfl hs3 ⟨ho3_le, hext3⟩
            | (have ho3_lt : out_n3.toNat < s.core.cur_vars := by c0_bound
               have ho3_tr : out_n3.toNat < s3.scratch.tarjan_reach.length := by rw [htr3]; omega
               have ho3_1 : (out_n3 + 1#64).toNat = out_n3.toNat + 1 := by bv_omega
               let s3' : FullState :=
                 { s3 with scratch := { s3.scratch with
                     tarjan_reach := s3.scratch.tarjan_reach.set out_n3.toNat (v3.setWidth 32) } }
               c0_hsteps
               refine hJk s3' (out_n3 + 1#64, ()) _ ?_ rfl
                 ⟨hs3.core_ok, { hs3.scratch_ok with
                   tarjan_reach_len := by dsimp only [s3']; rw [List.length_set, htr3] }⟩
                 ⟨by rw [ho3_1]; omega, hext3⟩
               dsimp only [fullSafetySlice]; exact by assumption)
      · exact hQ (out_n3, ()) s3 m3 (Eq.trans hcore3 (Eq.trans hcore2 (Eq.trans hcore1 hcore0)))
          hs3 ⟨ho3_le, hext3⟩ hm3

theorem full_lucky_ord_fid_wp (Γ : Env) :
    ∀ a m Q X, fullLuckyOrdFidSpec a m Q X →
      Func.wp Γ full_lucky_ord_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, R, rfl, hlen, hm, hQ⟩ := hs
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hext := c.hext; unfold dimacsBound at hext
  have hcl := hlen.core_ok
  have hsc := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le
  unfold Func.wp full_lucky_ord_fid_body
  c0_hsteps_nogrp
  refine wp_join_safety_slice (ts := [.bool, i64]) (fullSafetySlice c) s R (fun _ => True) trivial
    (fun s1 (found, len0, ()) =>
      (found = true → len0.toNat ≤ c.max_vars ∧
        1 + len0.toNat ≤ (BitVec.ofNat 64 s.scratch.extend_len).toNat ∧
        (BitVec.ofNat 64 s.scratch.extend_len).toNat ≤ c.extend_cap) ∧ FullExtScratchPres s s1)
    (fun Js s1 (found, len0, ()) m1 hcore1 hs1 _ ⟨hpre1, hext1⟩ hm1 => ?_)
    (fun Js hJs => ?_)
  · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hs1 hm1
    c0_hsteps_nogrp
    · have hfound : found = true := by cases found <;> first | rfl | exact absurd ‹_› (by decide)
      obtain ⟨hlen0_le, hlen0_ext, hlen0_cap⟩ := hpre1 hfound
      refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s1 R (fun _ => True) trivial
        (fun s2 (i, ()) => i.toNat ≤ len0.toNat ∧ FullExtScratchPres s s2)
        (fun (i, ()) => len0.toNat - i.toNat)
        (fun Ji hJi => by
          c0_hsteps
          exact hJi s1 (0#64, ()) m1 hm1 rfl hs1 ⟨Nat.zero_le _, hext1⟩)
        (fun Ji s2 (i, ()) m2 hcore2 hs2 _ ⟨hi_le, hext2⟩ hm2 hJi => ?_)
      dsimp only [fullSafetySlice] at hcore2 hs2 hm2
      have htr2 := hs2.scratch_ok.tarjan_reach_len
      have hes2 := hs2.scratch_ok.extend_stk_len
      c0_hsteps_nogrp
      · have hi_lt : i.toNat < len0.toNat := by c0_bound
        have hi_tr : i.toNat < s2.scratch.tarjan_reach.length := by rw [htr2]; omega
        have hi1_ext : (1#64 + i).toNat < s2.scratch.extend_stk.length := by
          have : (1#64 + i).toNat = 1 + i.toNat := by bv_omega
          rw [this, hes2]; omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        let s2' : FullState :=
          { s2 with scratch := { s2.scratch with
              tarjan_reach := s2.scratch.tarjan_reach.set i.toNat
                s2.scratch.extend_stk[(1#64 + i).toNat] } }
        c0_hsteps
        refine hJi s2' (i + 1#64, ()) _ ?_ (by dsimp only; rw [hi1]; omega)
          rfl ⟨hs2.core_ok, { hs2.scratch_ok with
            tarjan_reach_len := by dsimp only [s2']; rw [List.length_set, htr2] }⟩
          ⟨by rw [hi1]; omega, hext2⟩
        dsimp only [fullSafetySlice]; exact by assumption
      · have hpos0 : (1#64 + len0).toNat = 1 + len0.toNat := by bv_omega
        refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s2 R
          (fun _ => True) trivial
          (fun s3 (len_cur, pos, ()) =>
            pos.toNat ≤ (BitVec.ofNat 64 s.scratch.extend_len).toNat ∧
            FullExtScratchPres s s3)
          (fun (_, pos, ()) => (BitVec.ofNat 64 s.scratch.extend_len).toNat - pos.toNat)
          (fun Jp hJp => by
            c0_hsteps
            exact hJp s2 (i, 1#64 + len0, ()) m2 hm2 rfl hs2
              ⟨by rw [hpos0]; exact hlen0_ext, hext2⟩)
          (fun Jp s3 (len_cur, pos, ()) m3 hcore3 hs3 _ ⟨hpos_le, hext3⟩ hm3 hJp => ?_)
        dsimp only [fullSafetySlice] at hcore3 hs3 hm3
        have hes3 := hs3.scratch_ok.extend_stk_len
        have htr3 := hs3.scratch_ok.tarjan_reach_len
        c0_hsteps_nogrp
        · have hpos_lt : pos.toNat < (BitVec.ofNat 64 s.scratch.extend_len).toNat := by c0_bound
          have hpos_ext : pos.toNat < s3.scratch.extend_stk.length := by rw [hes3]; omega
          refine wp_join_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s3 R
            (fun _ => True) trivial
            (fun s4 (lc', pos', ()) => pos.toNat < pos'.toNat ∧
              pos'.toNat ≤ (BitVec.ofNat 64 s.scratch.extend_len).toNat ∧ FullExtScratchPres s s4)
            (fun _ s4 (lc', pos', ()) m4 hcore4 hs4 _ ⟨hgt4, hle4, hext4⟩ hm4 => ?_)
            (fun Js hJs => ?_)
          · rw [Blocks.get_here]; c0_hsteps
            exact hJp s4 (lc', pos', ()) m4 hm4 (by dsimp only; omega) hcore4 hs4 ⟨hle4, hext4⟩
          · c0_hsteps_nogrp
            · refine wp_unroll_group fun Js_in hJs_in => ?_
              c0_hsteps_nogrp
              refine wp_unroll_group fun Js1 hJs1 => ?_
              c0_hsteps_nogrp
              · let len' := (s3.scratch.extend_stk[pos.toNat] &&& 1073741823#32).setWidth 64
                have hlen'_le : len'.toNat ≤ c.max_vars := by dsimp only [len']; c0_bound
                have hpos_len' : (pos + 1#64 + len').toNat = pos.toNat + 1 + len'.toNat := by
                  bv_omega
                have hfit' : pos.toNat + 1 + len'.toNat ≤
                    (BitVec.ofNat 64 s.scratch.extend_len).toNat := by
                  have h1 : (pos.toNat + BitVec.toNat (1 : BitVec 64) +
                      (s3.scratch.extend_stk[pos.toNat] &&& 1073741823#32).toNat) % 2 ^ 64 ≤
                      s.scratch.extend_len % 2 ^ 64 := by assumption
                  have hlen'_eq : len'.toNat =
                      (s3.scratch.extend_stk[pos.toNat] &&& 1073741823#32).toNat := by
                    dsimp only [len']
                    simp only [BitVec.toNat_setWidth]
                    exact Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))
                  have hpos_cap : pos.toNat < c.extend_cap := by
                    have hmod : (BitVec.ofNat 64 s.scratch.extend_len).toNat =
                        s.scratch.extend_len % 2 ^ 64 := by simp [BitVec.toNat_ofNat]
                    omega
                  have h1' : (pos.toNat + 1 + len'.toNat) % 2 ^ 64 ≤
                      s.scratch.extend_len % 2 ^ 64 := by
                    rw [hlen'_eq]; exact h1
                  have hmod_lhs : (pos.toNat + 1 + len'.toNat) % 2 ^ 64 =
                      pos.toNat + 1 + len'.toNat := Nat.mod_eq_of_lt (by omega)
                  rw [BitVec.toNat_ofNat]
                  change _ ≤ s.scratch.extend_len % 2 ^ 64
                  rw [← hmod_lhs]
                  exact h1'
                refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s3 R
                  (fun _ => True) trivial
                  (fun s4 (k, ()) => k.toNat ≤ c.max_vars ∧ FullExtScratchPres s s4)
                  (fun (k, ()) => c.max_vars - k.toNat)
                  (fun Jm hJm => by
                    c0_hsteps; exact hJm s3 (0#64, ()) m3 hm3 rfl hs3 ⟨Nat.zero_le _, hext3⟩)
                  (fun Jm s4 (k, ()) m4 hcore4 hs4 _ ⟨hk_le, hext4⟩ hm4 hJm => ?_)
                dsimp only [fullSafetySlice] at hcore4 hs4 hm4
                have htm4 := hs4.scratch_ok.tarjan_mark_len
                c0_hsteps_nogrp
                · have hk_lt : k.toNat < c.max_vars := by c0_bound
                  have hk_tm : k.toNat < s4.scratch.tarjan_mark.length := by rw [htm4]; omega
                  have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                  let s4' : FullState :=
                    { s4 with scratch := { s4.scratch with
                        tarjan_mark := s4.scratch.tarjan_mark.set k.toNat 2147483647#32 } }
                  c0_hsteps
                  refine hJm s4' (k + 1#64, ()) _ ?_ (by dsimp only; rw [hk1]; omega) rfl
                    ⟨hs4.core_ok, { hs4.scratch_ok with
                      tarjan_mark_len := by dsimp only [s4']; rw [List.length_set, htm4] }⟩
                    ⟨by rw [hk1]; omega, hext4⟩
                  dsimp only [fullSafetySlice]; exact by assumption
                · refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s4 R
                    (fun _ => True) trivial
                    (fun s5 (k5, ()) => k5.toNat ≤ len'.toNat ∧ FullExtScratchPres s s5)
                    (fun (k5, ()) => len'.toNat - k5.toNat)
                    (fun Jk5 hJk5 => by
                      c0_hsteps; exact hJk5 s4 (0#64, ()) m4 hm4 rfl hs4 ⟨Nat.zero_le _, hext4⟩)
                    (fun Jk5 s5 (k5, ()) m5 hcore5 hs5 _ ⟨hk5_le, hext5⟩ hm5 hJk5 => ?_)
                  dsimp only [fullSafetySlice] at hcore5 hs5 hm5
                  have hes5 := hs5.scratch_ok.extend_stk_len
                  have htm5 := hs5.scratch_ok.tarjan_mark_len
                  c0_hsteps_nogrp
                  · have hk5_lt : k5.toNat < len'.toNat := by c0_bound
                    have hk5_1 : (k5 + 1#64).toNat = k5.toNat + 1 := by bv_omega
                    have hidx5 : (pos + 1#64 + k5).toNat = pos.toNat + 1 + k5.toNat := by bv_omega
                    have hidx5_ext : (pos + 1#64 + k5).toNat < s5.scratch.extend_stk.length := by
                      rw [hidx5, hes5]; omega
                    c0_hsteps_nogrp
                    refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s5 R
                      (fun _ => True) trivial
                      (fun s6 _ => FullExtScratchPres s s6)
                      (fun _ s6 _ m6 hcore6 hs6 _ hext6 hm6 => ?_)
                      (fun Jk hJk => ?_)
                    · rw [Blocks.get_here]; c0_hsteps
                      exact hJk5 s6 (k5 + 1#64, ()) m6 hm6 (by dsimp only; rw [hk5_1]; omega)
                        hcore6 hs6 ⟨by rw [hk5_1]; omega, hext6⟩
                    · c0_hsteps_nogrp
                      · let ov := s5.scratch.extend_stk[(pos + 1#64 + k5).toNat]
                        have hov_lt : (ov.setWidth 64).toNat < c.max_vars := by
                          dsimp only [ov]; c0_bound
                        have hov_tm : ov.toNat < s5.scratch.tarjan_mark.length := by
                          have hov32 := ov.isLt
                          have : (ov.setWidth 64).toNat = ov.toNat := by
                            simp only [BitVec.toNat_setWidth]
                            exact Nat.mod_eq_of_lt (by omega)
                          rw [htm5, ← this]; omega
                        let s5' : FullState :=
                          { s5 with scratch := { s5.scratch with
                              tarjan_mark :=
                                s5.scratch.tarjan_mark.set ov.toNat (k5.setWidth 32) } }
                        c0_hsteps
                        refine hJk s5' () _ ?_ rfl
                          ⟨hs5.core_ok, { hs5.scratch_ok with
                            tarjan_mark_len := by dsimp only [s5']; rw [List.length_set, htm5] }⟩
                          hext5
                        dsimp only [fullSafetySlice]; exact by assumption
                      · exact hJk s5 () m5 hm5 rfl hs5 hext5
                  · refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s5 R
                      (fun _ => True) trivial
                      (fun s6 (e2, ()) => e2.toNat ≤ len0.toNat ∧ FullExtScratchPres s s6)
                      (fun (e2, ()) => len0.toNat - e2.toNat)
                      (fun Je hJe => by
                        c0_hsteps; exact hJe s5 (0#64, ()) m5 hm5 rfl hs5 ⟨Nat.zero_le _, hext5⟩)
                      (fun Je s6 (e2, ()) m6 hcore6 hs6 _ ⟨he2_le, hext6⟩ hm6 hJe => ?_)
                    dsimp only [fullSafetySlice] at hcore6 hs6 hm6
                    have htr6 := hs6.scratch_ok.tarjan_reach_len
                    have htm6 := hs6.scratch_ok.tarjan_mark_len
                    c0_hsteps_nogrp
                    · have he2_lt : e2.toNat < len0.toNat := by c0_bound
                      have he2_tr : e2.toNat < s6.scratch.tarjan_reach.length := by rw [htr6]; omega
                      have he2_1 : (e2 + 1#64).toNat = e2.toNat + 1 := by bv_omega
                      c0_hsteps_nogrp
                      refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) s6 R
                        (fun _ => True) trivial
                        (fun s7 _ => FullExtScratchPres s s7)
                        (fun _ s7 (nv, ()) m7 hcore7 hs7 _ hext7 hm7 => ?_)
                        (fun J7 hJ7 => ?_)
                      · rw [Blocks.get_here]
                        dsimp only [fullSafetySlice] at hcore7 hs7 hm7
                        have htr7 := hs7.scratch_ok.tarjan_reach_len
                        have he2_tr7 : e2.toNat < s7.scratch.tarjan_reach.length := by
                          rw [htr7]; omega
                        let s7' : FullState :=
                          { s7 with scratch := { s7.scratch with
                              tarjan_reach := s7.scratch.tarjan_reach.set e2.toNat nv } }
                        c0_hsteps
                        refine hJe s7' (e2 + 1#64, ()) _ ?_ (by dsimp only; rw [he2_1]; omega)
                          hcore7 ⟨hs7.core_ok, { hs7.scratch_ok with
                            tarjan_reach_len := by dsimp only [s7']; rw [List.length_set, htr7] }⟩
                          ⟨by rw [he2_1]; omega, hext7⟩
                        dsimp only [fullSafetySlice]; exact by assumption
                      · c0_hsteps_nogrp
                        · let cur := s6.scratch.tarjan_reach[e2.toNat]
                          have hcur_lt : (cur.setWidth 64).toNat < c.max_vars := by
                            dsimp only [cur]; c0_bound
                          have hcur_tm :
                              (cur.setWidth 64).toNat < s6.scratch.tarjan_mark.length := by
                            rw [htm6]; omega
                          c0_hsteps
                          exact hJ7 s6 (s6.scratch.tarjan_mark[(cur.setWidth 64).toNat], ())
                            m6 hm6 rfl hs6 hext6
                        · c0_hsteps
                          exact hJ7 s6 (_, ()) m6 hm6 rfl hs6 hext6
                    · (try apply hJs_in); (try c0_hsteps)
                      exact hJs s6 (e2, pos + 1#64 + len', ()) m6 hm6
                        (Eq.trans hcore6 (Eq.trans hcore5 (Eq.trans hcore4 rfl)))
                        hs6 ⟨by rw [hpos_len']; omega, by rw [hpos_len']; omega, hext6⟩
              all_goals
                have hpos1 : (pos + 1#64).toNat = pos.toNat + 1 := by bv_omega
                (try apply hJs1); (try c0_hsteps_nogrp)
                (try apply hJs_in); (try c0_hsteps)
                exact hJs s3 (len_cur, pos + 1#64, ()) m3 hm3 rfl hs3
                  ⟨by rw [hpos1]; omega, by rw [hpos1]; omega, hext3⟩
            · have hpos1 : (pos + 1#64).toNat = pos.toNat + 1 := by bv_omega
              refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s3 R
                (fun _ => True) trivial
                (fun s4 (q, ()) => pos.toNat < q.toNat ∧
                  q.toNat ≤ (BitVec.ofNat 64 s.scratch.extend_len).toNat ∧
                  FullExtScratchPres s s4)
                (fun (q, ()) => (BitVec.ofNat 64 s.scratch.extend_len).toNat - q.toNat)
                (fun Jq hJq => by
                  c0_hsteps
                  exact hJq s3 (pos + 1#64, ()) m3 hm3 rfl hs3
                    ⟨by rw [hpos1]; omega, by rw [hpos1]; omega, hext3⟩)
                (fun Jq s4 (q, ()) m4 hcore4 hs4 _ ⟨hgt4, hle4, hext4⟩ hm4 hJq => ?_)
              dsimp only [fullSafetySlice] at hcore4 hs4 hm4
              have hes4 := hs4.scratch_ok.extend_stk_len
              c0_hsteps_nogrp
              · have hq_lt : q.toNat < (BitVec.ofNat 64 s.scratch.extend_len).toNat := by c0_bound
                have hq_ext : q.toNat < s4.scratch.extend_stk.length := by rw [hes4]; omega
                have hq1 : (q + 1#64).toNat = q.toNat + 1 := by bv_omega
                c0_hsteps_nogrp
                · exact hJq s4 (q + 1#64, ()) m4 hm4 (by dsimp only; rw [hq1]; omega)
                    rfl hs4 ⟨by rw [hq1]; omega, by rw [hq1]; omega, hext4⟩
                · exact hJs s4 (len_cur, q, ()) m4 hm4 hcore4 hs4 ⟨hgt4, hle4, hext4⟩
              · exact hJs s4 (len_cur, q, ()) m4 hm4 hcore4 hs4 ⟨hgt4, hle4, hext4⟩
        · exact ord_fid_post_mark_wp (by omega) hlen0_le (Eq.trans hcore3 (Eq.trans hcore2 hcore1))
            hs3 hext3 hm3 hQ
    · exact ord_fid_fallback_wp (by omega) hcore1 hs1 hext1 hm1 hQ
  · have hes_len := hsc.extend_stk_len
    c0_hsteps_nogrp
    · have hex_pos : 0 < (BitVec.ofNat 64 s.scratch.extend_len).toNat := by c0_bound
      have hex_le : (BitVec.ofNat 64 s.scratch.extend_len).toNat ≤ c.extend_cap := by
        have hcap64 : (BitVec.ofNat 64 c.extend_cap).toNat = c.extend_cap := by bv_omega
        rw [← hcap64]; c0_bound
      have h0_ext : 0 < s.scratch.extend_stk.length := by rw [hes_len]; omega
      c0_hsteps
      · let len0 := (s.scratch.extend_stk[0] &&& 536870911#32).setWidth 64
        have h1 : (s.scratch.extend_stk[0 % 2 ^ 64] &&& 536870911#32).toNat ≤
            c.max_vars % 2 ^ 64 := by assumption
        have h2 : (1 + (s.scratch.extend_stk[0 % 2 ^ 64] &&& 536870911#32).toNat) % 2 ^ 64 ≤
            s.scratch.extend_len % 2 ^ 64 := by assumption
        simp only [Nat.zero_mod] at h1 h2
        have h32 := (s.scratch.extend_stk[0] &&& 536870911#32).isLt
        have hlen0_lt : len0.toNat = (s.scratch.extend_stk[0] &&& 536870911#32).toNat := by
          dsimp only [len0]; simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
        have hcm : c.max_vars % 2 ^ 64 = c.max_vars := Nat.mod_eq_of_lt (by omega)
        exact hJs s (true, len0, ()) m hm rfl hlen
          ⟨fun _ => ⟨by rw [hlen0_lt, ← hcm]; exact h1,
            by rw [BitVec.toNat_ofNat, hlen0_lt]
               rw [← Nat.mod_eq_of_lt (a := 1 + _)]; exact h2; omega,
            hex_le⟩,
            fullExtScratchPres_refl s⟩
      all_goals
        exact hJs s (false, _, ()) m hm rfl hlen ⟨(fun h => by cases h), fullExtScratchPres_refl s⟩
    all_goals
      exact hJs s (false, 0#64, ()) m hm rfl hlen
        ⟨(fun h => by cases h), fullExtScratchPres_refl s⟩

/-! ## 2. `full_lucky_polar_m7_wp` -/

private theorem polar_widx_0 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat = 2 * (2 * v.toNat) := by
  rw [lk_bv64_shl1_eq, lk_bv64_shl1_eq]; bv_omega

private theorem polar_widx_01 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat =
      2 * (2 * v.toNat) + 1 := by
  rw [lk_bv64_shl1_eq, lk_bv64_shl1_eq]; bv_omega

private theorem polar_widx_10 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat =
      2 * (2 * v.toNat + 1) := by
  rw [lk_bv64_shl1_or1_eq, lk_bv64_shl1_eq]; bv_omega

private theorem polar_widx_11 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat =
      2 * (2 * v.toNat + 1) + 1 := by
  rw [lk_bv64_shl1_or1_eq, lk_bv64_shl1_eq]; bv_omega

local macro "lk0_polar_watch_loop"
    s:ident m:ident hlen:ident
    off:ident sz:ident init_flg:ident hoff:ident hsz:ident hbd:ident hpw:ident
    hJdone:ident : tactic =>
  `(tactic| (
    apply wp_loop_group (ts := [.bool, i64])
      (fun (wrem : Nat) xw mw => ∃ (flg : Bool) (jw : BitVec 64),
        xw = (flg, jw, ()) ∧ mw = $m ∧
        jw.toNat + wrem = ($off).toNat + ($sz).toNat ∧
        PolarWatchOk ($s).core jw.toNat wrem)
    · intro Jwl nw xw mw hrecw ⟨flg, jw, hxw, hmw, hjw_sum, hpw_cur⟩
      subst hxw; subst mw; rw [Blocks.get_here]
      have hsum_w : ($off).toNat + ($sz).toNat < 2 ^ 64 := by omega
      have hjw_end : (BitVec.setWidth 64 $off + BitVec.setWidth 64 $sz).toNat =
          ($off).toNat + ($sz).toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (Nat.lt_trans ($off).isLt (by decide)),
          Nat.mod_eq_of_lt (Nat.lt_trans ($sz).isLt (by decide)),
          Nat.mod_eq_of_lt (by omega)]
      lk0_hsteps_raw
      rw [wp_jnz]; constructor
      · intro hc
        have hlt : jw.toNat < ($off).toNat + ($sz).toNat := by
          have hc0 : BitVec.ult jw (BitVec.setWidth 64 $off + BitVec.setWidth 64 $sz) = true :=
            hc
          rw [BitVec.ult] at hc0
          exact hjw_end ▸ of_decide_eq_true hc0
        rw [wp_jnz]; refine ⟨fun hflg => ?_, fun hflg => ?_⟩
        · subst hflg; rw [wp_jump]; exact $hJdone _ $m rfl
        · have hnw : 0 < nw := by omega
          have hjw_lt : jw.toNat < ($s).core.wstk.length := by
            have := ($hlen).wstk_len_arr; have := ($hlen).wlen_le
            have hbd' := $hbd
            rw [← $hoff, ← $hsz] at hbd'; omega
          lk0_to_group_ns
          apply wp_join_group (ts := [.bool, i64]) (fun xs' mw' =>
            ∃ (flg' : Bool) (jw' : BitVec 64), xs' = (flg', jw', ()) ∧
              mw' = $m ∧ jw'.toNat ≤ ($off).toNat + ($sz).toNat ∧ jw.toNat < jw'.toNat ∧
              PolarWatchOk ($s).core jw'.toNat (($off).toNat + ($sz).toNat - jw'.toNat))
          · intro _Js ⟨flg', jw', ⟨⟩⟩ mw' hmw'
            rcases hmw' with ⟨f', j', hxs', hmw_eq, hj_le, hj_gt, hp'⟩
            subst mw'; injection hxs' with hf'; subst hf'
            injection (by assumption : (jw', ()) = (j', ())) with hj'; subst hj'
            rw [Blocks.get_here, wp_jump]
            exact hrecw (($off).toNat + ($sz).toNat - jw'.toNat) (flg', jw', ()) $m (by omega)
              ⟨flg', jw', rfl, rfl, by omega, hp'⟩
          · intro Js hJs
            cases hpw_cur with
            | empty => omega
            | bin hw_some hbit hne hlit_lt hpw_next =>
              have hld_eq := Option.some.inj ((List.getElem?_eq_getElem hjw_lt).symm.trans hw_some)
              have hbit' := hld_eq.symm ▸ hbit
              have hval_lt : (BitVec.setWidth 64
                  (($s).core.wstk[jw.toNat] &&& 2147483647#32)).toNat <
                  ($s).core.vals.length := by
                rw [hld_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
                have := ($hlen).vals_len; have := ($hlen).cur_vars_le; omega
              have h1 : (jw + 1#64).toNat = jw.toNat + 1 := by bv_omega
              have hp_next : PolarWatchOk ($s).core (jw + 1#64).toNat
                  (($off).toNat + ($sz).toNat - (jw + 1#64).toNat) := by
                rw [h1]; exact (congrArg (PolarWatchOk ($s).core _) (by omega)).mpr hpw_next
              lk0_hsteps_raw
              rw [wp_jnz]
              refine ⟨fun _ => ?_, fun hc' => False.elim (hbit' (by simpa using hc'))⟩
              apply wp_join_group (ts := [.bool]) (fun _ m' => m' = $m)
              · intro _Js1 ⟨flg', ⟨⟩⟩ m' hm'; subst m'; rw [Blocks.get_here]
                lk0_hsteps_raw
                exact hJs (flg', jw + 1#64, ()) $m
                  ⟨flg', jw + 1#64, rfl, rfl, by rw [h1]; omega, by rw [h1]; omega, hp_next⟩
              · intro Js1 hJs1; lk0_to_group_ns
                · apply wp_join_group (ts := [.bool]) (fun _ m' => m' = $m)
                  · intro _Js2 ⟨flg', ⟨⟩⟩ m' hm'
                    subst m'; rw [Blocks.get_here, wp_jump]; exact hJs1 (flg', ()) $m rfl
                  · intro Js2 hJs2
                    lk0_hsteps_raw
                    rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                    · rw [wp_jump]; exact hJs2 _ $m rfl
                    · lk0_hsteps_raw
                      rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                      · lk0_hsteps_raw
                        rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                          (rw [wp_jump]; exact hJs2 _ $m rfl)
                      · rw [wp_jump]; exact hJs2 _ $m rfl
                · exact hJs1 _ $m rfl
            | large hw_some hbit hpw_next =>
              have hld_eq := Option.some.inj ((List.getElem?_eq_getElem hjw_lt).symm.trans hw_some)
              have hbit' := hld_eq.symm ▸ hbit
              have h2 : (jw + 2#64).toNat = jw.toNat + 2 := by
                rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                simp only [Nat.reducePow, Nat.reduceMod]
                rw [Nat.mod_eq_of_lt (by omega)]
              have hp_next : PolarWatchOk ($s).core (jw + 2#64).toNat
                  (($off).toNat + ($sz).toNat - (jw + 2#64).toNat) := by
                rw [h2]; exact (congrArg (PolarWatchOk ($s).core _) (by omega)).mpr hpw_next
              lk0_hsteps_raw
              rw [wp_jnz]
              refine ⟨fun hc' =>
                False.elim ((by simpa using hc' :
                  ($s).core.wstk[jw.toNat] &&& 2147483648#32 ≠ 0#32) hbit'),
                fun _ => ?_⟩
              lk0_hsteps_raw
              exact hJs (flg, jw + 2#64, ()) $m
                ⟨flg, jw + 2#64, rfl, rfl, by rw [h2]; omega, by rw [h2]; omega, hp_next⟩
      · intro _; rw [wp_jump]; exact $hJdone _ $m rfl
    · intro Jwl hJwl; rw [wp_jump]
      have hoff_64 : (BitVec.setWidth 64 $off).toNat = ($off).toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ($off).isLt (by decide))]
      have hpw' := $hpw
      rw [← $hoff, ← $hsz] at hpw'
      exact hJwl ($sz).toNat ($init_flg, BitVec.setWidth 64 $off, ()) $m
        ⟨$init_flg, BitVec.setWidth 64 $off, rfl, rfl, by rw [hoff_64],
          by rw [hoff_64]; exact hpw'⟩))

theorem full_lucky_polar_m7_wp (Γ : Env)
    (hNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X) :
    ∀ a m Q X, fullLuckyPolarM7Spec a m Q X →
      Func.wp Γ full_lucky_polar_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_lucky_polar_m7_body
  lk0_to_group_ns
  rcases hinv with ⟨hlen_all, F_cur, hwe⟩
  have hlen := hlen_all.core_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hdb : (268435456 : Nat) < 2 ^ 30 := by decide
  have hcv_lt : s.core.cur_vars < 2 ^ 31 := by have := hlen.cur_vars_le; omega
  have hal_lt : s.core.arena_len < 2 ^ 31 := by
    have := hlen.arena_len_le; have := c.harena; unfold dimacsBound at *; omega
  have hwl_lt : s.core.wlen < 2 ^ 31 := by
    have := hlen.wlen_le; have := c.hwcap; unfold dimacsBound at *; omega
  obtain ⟨hlay, hpw⟩ := modeWatchesInv_toPolar hwe.watches
  apply wp_join_group (ts := [.bool, .bool, i64]) (fun _ m2 => m2 = m)
  · rintro _J0 ⟨sp, sn, _r, ⟨⟩⟩ m2 hm2
    rw [hm2]; clear hm2 m2; rw [Blocks.get_here]; try dsimp only
    lk0_to_group_ns
    apply wp_loop_group (ts := [.bool, .bool, i64])
      (fun (v_rem : Nat) xs2 m2 => ∃ (sp2 sn2 : Bool) (v : BitVec 64),
        xs2 = (sp2, sn2, v, ()) ∧ m2 = m ∧ v_rem = s.core.cur_vars - v.toNat ∧
        v.toNat ≤ s.core.cur_vars)
    · intro J2 n2 xs2 m2 hrec2 ⟨sp2, sn2, v, hxs2, hm2, hn2, hv_le⟩
      subst hxs2; rw [hm2]; clear hm2 m2; rw [Blocks.get_here]; try dsimp only; lk0_to_group_ns
      apply wp_join_group (ts := []) (fun _ m3 => m3 = m)
      · intro _Jret ⟨⟩ m3 hm3; rw [hm3]; clear hm3 m3; lk0_steps <;> exact hQ _ (by decide)
      · intro Jret hJret
        lk0_to_group_ns
        · have hv_lt : v.toNat < s.core.cur_vars := by
            have hc1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
            rwa [Nat.mod_eq_of_lt (by omega)] at hc1
          lk0_to_group_ns
          apply wp_join_group (ts := []) (fun _ m3 => m3 = m)
          · intro _J2b ⟨⟩ m3 hm3
            rw [hm3]; clear hm3 m3; lk0_to_group_ns
            apply wp_join_group (ts := [.bool, .bool]) (fun _ m4 => m4 = m)
            · intro _J2next ⟨sp', sn', ⟨⟩⟩ m4 hm4
              rw [hm4]; clear hm4 m4; rw [Blocks.get_here]; lk0_hsteps_raw
              have hv1_lt : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
              exact hrec2 (s.core.cur_vars - (v + 1#64).toNat) (sp', sn', v + 1#64, ()) m
                (by omega) ⟨sp', sn', v + 1#64, rfl, rfl, rfl, by omega⟩
            · intro J2next hJ2next
              have h_vals : (v <<< 1#64).toNat < s.core.vals.length := by
                rw [lk_bv64_shl1_eq]; have := hlen.vals_len; have := hlen.cur_vars_le; bv_omega
              have h_flags : v.toNat < s.core.flags.length := by
                have := hlen.flags_len; have := hlen.cur_vars_le; omega
              have := hlen.cur_vars_le
              have hv30 : v.toNat < 2 ^ 30 := by omega
              have hcv2 : 2 * (2 * v.toNat + 1) + 1 < 4 * s.core.cur_vars := by omega
              have hl1_0 := polar_widx_10 hv30
              have hl1_1 := polar_widx_11 hv30
              have hl0_0 := polar_widx_0 hv30
              have hl0_1 := polar_widx_01 hv30
              have hw0 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat <
                  s.core.wvec.length := by
                rw [hl1_0]; have := hlen.wvec_len; have := hlen.cur_vars_le; omega
              have hw1 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat <
                  s.core.wvec.length := by
                rw [hl1_1]; have := hlen.wvec_len; have := hlen.cur_vars_le; omega
              have hw2 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat < s.core.wvec.length := by
                rw [hl0_0]; have := hlen.wvec_len; have := hlen.cur_vars_le; omega
              have hw3 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat <
                  s.core.wvec.length := by
                rw [hl0_1]; have := hlen.wvec_len; have := hlen.cur_vars_le; omega
              let i1_0 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat
              let i1_1 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat
              let off1 := s.core.wvec[i1_0]; let sz1 := s.core.wvec[i1_1]
              have hoff1 : off1.toNat = fullWatchOffCore s.core (2 * v.toNat + 1) := by
                dsimp [fullWatchOffCore]; rw [← hl1_0, List.getElem?_eq_getElem hw0]; rfl
              have hsz1 : sz1.toNat = fullWatchSizeCore s.core (2 * v.toNat + 1) := by
                dsimp [fullWatchSizeCore]; rw [← hl1_1, List.getElem?_eq_getElem hw1]; rfl
              have hbd1 := hlay.bounds (2 * v.toNat + 1) (by omega)
              have hpw1 := hpw (2 * v.toNat + 1) (by omega)
              let i0_0 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat
              let i0_1 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat
              let off0 := s.core.wvec[i0_0]; let sz0 := s.core.wvec[i0_1]
              have hoff0 : off0.toNat = fullWatchOffCore s.core (2 * v.toNat) := by
                dsimp [fullWatchOffCore]; rw [← hl0_0, List.getElem?_eq_getElem hw2]; rfl
              have hsz0 : sz0.toNat = fullWatchSizeCore s.core (2 * v.toNat) := by
                dsimp [fullWatchSizeCore]; rw [← hl0_1, List.getElem?_eq_getElem hw3]; rfl
              have hbd0 := hlay.bounds (2 * v.toNat) (by omega)
              have hpw0 := hpw (2 * v.toNat) (by omega)
              lk0_split
              · lk0_split
                · lk0_to_group_ns
                  apply wp_join_group (ts := [.bool, i64]) (fun _ m4 => m4 = m)
                  · intro _Jw1_done ⟨sp', _w1j, ⟨⟩⟩ m4 hm4
                    rw [hm4]; clear hm4 m4; rw [Blocks.get_here]; lk0_to_group_ns
                    apply wp_join_group (ts := [.bool, i64]) (fun _ m5 => m5 = m)
                    · intro _Jw2_done ⟨sn', _w0j, ⟨⟩⟩ m5 hm5
                      rw [hm5]; clear hm5 m5; rw [Blocks.get_here, wp_jump]
                      exact hJ2next (sp', sn', ()) m rfl
                    · intro Jw2_done hJw2_done
                      lk0_to_group_ns
                      · lk0_polar_watch_loop s m hlen off0 sz0 sn2 hoff0 hsz0 hbd0 hpw0
                          hJw2_done
                      all_goals exact hJw2_done _ m rfl
                  · intro Jw1_done hJw1_done
                    lk0_to_group_ns
                    · lk0_polar_watch_loop s m hlen off1 sz1 sp2 hoff1 hsz1 hbd1 hpw1
                        hJw1_done
                    all_goals exact hJw1_done _ m rfl
                · exact hJ2next (sp2, sn2, ()) m rfl
              · exact hJ2next (sp2, sn2, ()) m rfl
          · intro J2b hJ2b
            lk0_to_group_ns <;> first | exact hJret () m rfl | exact hJ2b () m rfl
        · lk0_to_group_ns; exact hJret () m rfl
    · intro J2 hJ2; rw [wp_jump]
      exact hJ2 s.core.cur_vars (sp, sn, 0#64, ()) m ⟨sp, sn, 0#64, rfl, rfl, rfl, Nat.zero_le _⟩
  · intro J0 hJ0
    lk0_to_group_ns
    apply wp_loop_group (ts := [.bool, .bool, i64])
      (fun (r_rem : Nat) xs m' => ∃ (sp sn : Bool) (r : BitVec 64),
        xs = (sp, sn, r, ()) ∧ m' = m ∧ r_rem = s.core.arena_len - r.toNat ∧
        r.toNat ≤ s.core.arena_len ∧
        (r.toNat = s.core.arena_len ∨ r.toNat ∈ fullArenaClauseRefsCore s.core))
    · intro J n xs m' hrec ⟨sp, sn, r, hxs, hm', hn, hr_le, hr⟩
      subst hxs; subst m'; rw [Blocks.get_here]; try dsimp only
      rcases hr with hr_eq | hr_mem
      · lk0_to_group_ns <;> first
          | exact hJ0 _ m rfl
          | (exfalso
             have : r.toNat < s.core.arena_len % 2 ^ 64 := by assumption
             rw [hr_eq, Nat.mod_eq_of_lt (by omega)] at this; omega)
      · have hwf := hwe.arena.refs_wf r.toNat hr_mem
        have hr_lt0 : r.toNat < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        have hr_lt2 : (r + 2#64).toNat < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          simp only [Nat.reducePow, Nat.reduceMod]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        lk0_to_group_ns
        · apply wp_join_group (ts := []) (fun _ m2 => m2 = m)
          · intro _Jbody ⟨⟩ m2 hm2; rw [hm2]; clear hm2 m2; rw [Blocks.get_here]; try dsimp only
            lk0_to_group_ns
            let nxt := fullArenaNextOff s.core.arena s.core.arena_len r.toNat
            have hr32 : (BitVec.setWidth 32 r).toNat = r.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            refine ⟨fun res m4 => res = (BitVec.ofNat 32 nxt, ()) ∧ m4 = m, X,
              hNext (c.hdr, BitVec.setWidth 32 r, ()) m _ X
                ⟨c, s, R, rfl, hlen_all, hm, ⟨by rw [hr32], rfl⟩⟩, ?_, fun _ _ _ _ => id⟩
            rintro ⟨r32, ⟨⟩⟩ m4 ⟨hr32_eq, hm4⟩; rw [hm4]; clear hm4 m4
            injection hr32_eq with hr32_eq; subst r32
            lk0_hsteps_raw
            have hnxt_eq : (BitVec.setWidth 64 (BitVec.ofNat 32 nxt)).toNat = nxt := by
              have := hwf.2.2.2.1
              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            have hnxt_mem : nxt = s.core.arena_len ∨ nxt ∈ fullArenaClauseRefsCore s.core :=
              fullArenaScanRefs_next_mem s.core.arena s.core.arena_len s.core.arena_len 0
                r.toNat (Nat.le_refl _)
                (fun p hp => by
                  have hpwf := hwe.arena.refs_wf p hp
                  exact ⟨Nat.le_trans (by omega) hpwf.2.2.1, hpwf.2.2.2.2⟩)
                hr_mem
            apply wp_join_group (ts := [.bool, .bool]) (fun _ m5 => m5 = m)
            · intro _Jn ⟨sp', sn', ⟨⟩⟩ m5 hm5; rw [hm5]; clear hm5 m5; rw [Blocks.get_here]
              lk0_hsteps_raw
              rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
              · rw [wp_jump]
                first
                | exact hJ0 (sp', sn', r, ()) m rfl
                | exact hrec (s.core.arena_len - nxt)
                    (sp', sn', BitVec.setWidth 64 (BitVec.ofNat 32 nxt), ()) m
                    (by have := hwf.2.2.1; have := hwf.1; omega)
                    ⟨sp', sn', BitVec.setWidth 64 (BitVec.ofNat 32 nxt), rfl, rfl,
                      by rw [hnxt_eq], by rw [hnxt_eq]; exact hwf.2.2.2.1,
                      by rw [hnxt_eq]; exact hnxt_mem⟩
            · intro Jn hJn; lk0_to_group_ns
              apply wp_join_group (ts := [.bool, .bool]) (fun _ m5 => m5 = m)
              · intro _Jn2 ⟨sp', sn', ⟨⟩⟩ m5 hm5; rw [hm5]; clear hm5 m5
                rw [Blocks.get_here, wp_jump]; exact hJn (sp', sn', ()) m rfl
              · intro Jn2 hJn2; lk0_to_group_ns
                · have hsz_eq : (s.core.arena[(r + 2#64).toNat]).toNat =
                      fullArenaClauseSizeCore s.core r.toNat := by
                    have hr2_eq : (r + 2#64).toNat = r.toNat + 2 := by
                      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                      simp only [Nat.reducePow, Nat.reduceMod]
                      rw [Nat.mod_eq_of_lt (by omega)]
                    have ha : s.core.arena[r.toNat + 2]? =
                        some s.core.arena[(r + 2#64).toNat] := by
                      rw [← hr2_eq]; exact List.getElem?_eq_getElem hr_lt2
                    dsimp only [fullArenaClauseSizeCore]; rw [ha]; rfl
                  have hgarb_false : fullArenaClauseGarbCore s.core r.toNat = false := by
                    have ha : s.core.arena[r.toNat]? = some s.core.arena[r.toNat] :=
                      List.getElem?_eq_getElem hr_lt0
                    dsimp [fullArenaClauseGarbCore, fullArenaHdrCore]
                    rw [ha]; simp; assumption
                  apply wp_join_group (ts := [.bool, .bool, .bool, i32]) (fun _ m5 => m5 = m)
                  · intro _Jpost ⟨sat', any', _skip', _j', ⟨⟩⟩ m5 hm5
                    rw [hm5]; clear hm5 m5; rw [Blocks.get_here]; lk0_to_group_ns
                    apply wp_join_group (ts := [.bool, .bool]) (fun _ m6 => m6 = m)
                    · intro _Jn3 ⟨sp', sn', ⟨⟩⟩ m6 hm6; rw [hm6]; clear hm6 m6
                      rw [Blocks.get_here, wp_jump]; exact hJn2 (sp', sn', ()) m rfl
                    · intro Jn3 hJn3
                      rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                      · rw [wp_jump]; exact hJn3 (sp, sn, ()) m rfl
                      · apply wp_join_group (ts := [.bool]) (fun _ m6 => m6 = m)
                        · intro _Jsp ⟨sp', ⟨⟩⟩ m6 hm6; rw [hm6]; clear hm6 m6
                          rw [Blocks.get_here]
                          apply wp_join_group (ts := [.bool]) (fun _ m6 => m6 = m)
                          · intro _Jsn ⟨sn', ⟨⟩⟩ m6 hm6; rw [hm6]; clear hm6 m6
                            rw [Blocks.get_here, wp_jump]; exact hJn3 (sp', sn', ()) m rfl
                          · intro Jsn hJsn
                            rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                              (rw [wp_jump]; exact hJsn _ m rfl)
                        · intro Jsp hJsp
                          rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                            (rw [wp_jump]; exact hJsp _ m rfl)
                  · intro Jpost hJpost; lk0_to_group_ns
                    apply wp_loop_group (ts := [.bool, .bool, i32])
                      (fun (jrem : Nat) xj mj => ∃ (sat? any? : Bool) (j : BitVec 32),
                        xj = (sat?, any?, j, ()) ∧ mj = m ∧
                        jrem = fullArenaClauseSizeCore s.core r.toNat - j.toNat ∧
                        j.toNat ≤ fullArenaClauseSizeCore s.core r.toNat)
                    · intro Jj nj xj mj hrecj ⟨sat?, any?, j, hxj, hmj, hnj, hj_le⟩
                      subst hxj; subst mj; rw [Blocks.get_here]
                      lk0_hsteps_raw
                      rw [wp_jnz]; constructor
                      · intro hc
                        have hlt :
                            decide (j.toNat < s.core.arena[(r + 2#64).toNat].toNat) =
                              true := by simpa [BitVec.ult] using hc
                        have hj : j.toNat < fullArenaClauseSizeCore s.core r.toNat := by
                          rw [← hsz_eq]; exact of_decide_eq_true hlt
                        have hj_ar :
                            (r + 3#64 + BitVec.setWidth 64 j).toNat <
                              s.core.arena.length := by
                          have := hlen.arena_len_le; have := hlen.arena_len_arr
                          have := hwf.2.2.1
                          rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
                            BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (Nat.lt_trans j.isLt (by decide))]
                          simp only [Nat.reducePow, Nat.reduceMod]
                          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                          omega
                        lk0_to_group_ns
                        apply wp_join_group (ts := [.bool, .bool, .bool]) (fun _ m4 => m4 = m)
                        · intro _Jjnext ⟨_broke, ap', an', ⟨⟩⟩ m4 hm4
                          rw [hm4]; clear hm4 m4; rw [Blocks.get_here]
                          lk0_hsteps_raw
                          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
                            rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                            simp only [Nat.reducePow, Nat.reduceMod]
                            rw [Nat.mod_eq_of_lt (by omega)]
                          exact hrecj
                            (fullArenaClauseSizeCore s.core r.toNat - (j + 1#32).toNat)
                            (ap', an', j + 1#32, ()) m (by omega)
                            ⟨ap', an', j + 1#32, rfl, rfl, rfl, by omega⟩
                        · intro Jjnext hJjnext
                          have h_ar_idx : (r + 3#64 + BitVec.setWidth 64 j).toNat =
                              r.toNat + 3 + j.toNat := by
                            rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
                              BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (Nat.lt_trans j.isLt (by decide))]
                            simp only [Nat.reducePow, Nat.reduceMod]
                            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                          have hlit_mem :
                              s.core.arena[(r + 3#64 + BitVec.setWidth 64 j).toNat].toNat ∈
                                fullArenaClauseLitsCore s.core r.toNat := by
                            simp only [h_ar_idx]
                            exact arena_lit_mem_clauseLits s.core r.toNat j.toNat hj
                              (h_ar_idx ▸ hj_ar)
                          have hlit_lt : (BitVec.setWidth 64
                              s.core.arena[(r + 3#64 + BitVec.setWidth 64 j).toNat]).toNat <
                              s.core.vals.length := by
                            have := hwe.arena.lits_lt r.toNat hr_mem hgarb_false _ hlit_mem
                            have := hlen.vals_len; have := hlen.cur_vars_le
                            rw [BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (Nat.lt_trans
                                (s.core.arena[(r + 3#64 +
                                  BitVec.setWidth 64 j).toNat]).isLt (by decide))]
                            omega
                          lk0_to_group_ns
                          lk0_split
                          · exact hJpost (true, sat?, any?, j, ()) m rfl
                          · apply wp_join_group (ts := [.bool, .bool]) (fun _ m' => m' = m)
                            · intro _Js ⟨ap', an', ⟨⟩⟩ m' hm'; subst m'
                              rw [Blocks.get_here, wp_jump]
                              exact hJjnext (false, ap', an', ()) m rfl
                            · intro Js hJs
                              lk0_hsteps_raw
                              rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                              · apply wp_join_group (ts := [.bool, .bool]) (fun _ m' => m' = m)
                                · intro _Js2 ⟨ap', an', ⟨⟩⟩ m' hm'; subst m'
                                  rw [Blocks.get_here, wp_jump]
                                  exact hJs (ap', an', ()) m rfl
                                · intro Js2 hJs2
                                  lk0_hsteps_raw
                                  rw [wp_jnz]
                                  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                                    (rw [wp_jump]; exact hJs2 _ m rfl)
                              · rw [wp_jump]; exact hJs _ m rfl
                          · exact hJjnext (false, sat?, any?, ()) m rfl
                      · intro _; rw [wp_jump]
                        exact hJpost (false, sat?, any?, j, ()) m rfl
                    · intro Jj hJj; rw [wp_jump]
                      exact hJj (fullArenaClauseSizeCore s.core r.toNat)
                        (false, false, 0#32, ()) m
                        ⟨false, false, 0#32, rfl, rfl, rfl, Nat.zero_le _⟩
                all_goals exact hJn2 (sp, sn, ()) m rfl
          · intro Jbody hJbody
            lk0_to_group_ns <;>
              (try rw [wp_jump]) <;>
              first | exact hJbody () m rfl | exact hJ0 _ m rfl
    · intro J hJ; rw [wp_jump]
      have h0 : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefsCore s.core := by
        rcases hwe.arena.len_ok with h0 | h3
        · exact Or.inl h0.symm
        · right; simp only [fullArenaClauseRefsCore]
          cases al : s.core.arena_len with
          | zero => omega
          | succ k =>
            have hle3 : 0 + 3 ≤ Nat.succ k := by omega
            simp only [fullArenaScanRefs]
            simp [hle3]
      exact hJ s.core.arena_len (false, false, 0#64, ()) m
        ⟨false, false, 0#64, rfl, rfl, rfl, Nat.zero_le _, h0⟩

end LeanQbe.T.Examples.Kissat.Proof.Lucky