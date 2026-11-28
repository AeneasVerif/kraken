/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Frontend.C0
import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Verification Suite for `P0-2` (`C0HeadStep` Tactic Upgrades)

Covers:
1. `c0_hcall` across explicit, implicit, `Env.Has`, and `Env.Sat.has` caller specs, tail-call
   `ret` reduction (`m6o_fwd0`/`m6o_fwd1` patterns), multi-step continuations, `Blocks.get`, and
   outer/inner `MData`, plus backward-compatibility check that `C0Step.c0_call` is unshadowed.
2. `c0_hstep_np`, `c0_hfast_nogrp`, and `c0_hsteps_np` (unpruned `jnz` + stopping before
   `Expr.group`).
3. `HeadStepConfig.useBound` and `c0_*_nobound` tactics (skipping `c0_bound` fallback when side
   bounds are supplied via `assumption`/`rfl`, failing fast when `c0_bound` would be needed).
4. `.mdata` stripping (outer target AND inner `wp … (.mdata _ …)`) in `c0_mstep`, `c0_msteps`,
   `c0_msteps!`, `c0_mto_group`, and `c0_msplit` (without shadowing `C0Step.c0_step*`).
5. `#print axioms` strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.C0HeadStepP02Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep

/-! ## Meta Helpers for `.mdata` Wrapping and Diagnostic Assertions -/

private meta def wrapOuterMData : Lean.Elab.Tactic.TacticM Unit := do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  let g' ← g.change (Lean.mkMData {} ty) (checkDefEq := false)
  Lean.Elab.Tactic.replaceMainGoal [g']

private meta def wrapWpExprMData : Lean.Elab.Tactic.TacticM Unit := do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LeanQbe.T.wp 6 do
    throwError "wrap_wp_expr_mdata: expected `wp` goal"
  let e' := Lean.mkMData {} (ty.getArg! 4)
  let ty' := Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e')
  let g' ← g.change ty' (checkDefEq := false)
  Lean.Elab.Tactic.replaceMainGoal [g']

private meta def expectTacticFail (tac : Lean.TSyntax `tactic) : Lean.Elab.Tactic.TacticM Unit := do
  let s ← Lean.Elab.Tactic.saveState
  try
    Lean.Elab.Tactic.evalTactic tac
    s.restore
    throwError "expected tactic failure, but succeeded"
  catch _ =>
    s.restore

private meta def checkGoalCount (expected : Nat) : Lean.Elab.Tactic.TacticM Unit := do
  let n := (← Lean.Elab.Tactic.getUnsolvedGoals).length
  unless n == expected do
    throwError "expected {expected} goals, got {n}"

/-! ## 1. `c0_hcall` Compatibility, `O(1)` Behavior, & Unshadowed `c0_call` -/

section C0HCallTests

def addOneSpec : Spec [i32] [i32] :=
  fun (x, ()) m Q _ => Q (x + 1#32, ()) m

def unitSpec : Spec [i32] [] :=
  fun (_, ()) m Q _ => Q () m

theorem fwd1_eq {t : Ty} {Q : Post [t]} :
    (fun (r : Tup Val [t]) m' => Q (r.fst, ()) m') = Q :=
  funext fun ⟨_, ⟨⟩⟩ => rfl

theorem fwd0_eq {Q : Post []} :
    (fun (_ : Tup Val []) m' => Q () m') = Q :=
  funext fun ⟨⟩ => rfl

def fwd1Body : Func [i32] [i32] := fun _ _ (x, ()) =>
  .call "add1" (as := [i32]) (bs := [i32]) (Arg.var x, ()) fun r => .ret (Arg.var r.1, ())

def fwd0Body : Func [i32] [] := fun _ _ (x, ()) =>
  .call "unitfn" (as := [i32]) (bs := []) (Arg.var x, ()) fun _ => .ret ()

def contBody : Func [i32] [i32] := fun _ _ (x, ()) =>
  .call "add1" (as := [i32]) (bs := [i32]) (Arg.var x, ()) fun r =>
    .let_ (op2 (.add i32) (Arg.var r.1) (Arg.imm 2#32)) fun (y, _) =>
      .ret (Arg.var y, ())

def letBeforeCallBody : Func [i32] [i32] := fun _ _ (x, ()) =>
  .let_ (op2 (.xor i32) (Arg.var x) (Arg.imm 1#32)) fun (x', _) =>
    .call "add1" (as := [i32]) (bs := [i32]) (Arg.var x', ()) fun r => .ret (Arg.var r.1, ())

theorem fwd1_xfree : addOneSpec.XFree := by xfree

theorem call_explicit_fwd1 (Γ : Env)
    (hSub : ∀ a m Q X, addOneSpec a m Q X → Γ "add1" [i32] [i32] a m Q X) :
    ∀ a m Q X, addOneSpec a m Q X → Func.wp Γ fwd1Body a m Q X := by
  intro (x, ()) m Q X hs
  unfold Func.wp fwd1Body
  c0_hcall hSub
  rwa [fwd1_eq]

theorem call_implicit_fwd0 (Γ : Env)
    (hSub : ∀ {a m Q X}, unitSpec a m Q X → Γ "unitfn" [i32] [] a m Q X) :
    ∀ a m Q X, unitSpec a m Q X → Func.wp Γ fwd0Body a m Q X := by
  intro (x, ()) m Q X hs
  unfold Func.wp fwd0Body
  c0_hcall hSub
  rwa [fwd0_eq]

theorem call_env_has_cont (Γ : Env)
    (hHas : Γ.Has "add1" addOneSpec) (x : BitVec 32) (m : Mem 64)
    (Q : Post [i32]) (X : XPost) (hQ : Q (x + 1#32 + 2#32, ()) m) :
    Func.wp Γ contBody (x, ()) m Q X := by
  unfold Func.wp contBody
  c0_hcall hHas
  dsimp only [addOneSpec]
  c0_hsteps
  exact hQ

theorem call_env_sat_has (Γ : Env)
    (hSat : Γ.Sat [⟨"add1", [i32], [i32], addOneSpec, true⟩])
    (x : BitVec 32) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hQ : Q (x + 1#32 + 2#32, ()) m) :
    Func.wp Γ contBody (x, ()) m Q X := by
  unfold Func.wp contBody
  c0_hcall (hSat.has (e := ⟨"add1", [i32], [i32], addOneSpec, true⟩) (by simp) fwd1_xfree)
  dsimp only [addOneSpec]
  c0_hsteps
  exact hQ

theorem call_mdata_wrapped_ret (Γ : Env)
    (hSub : ∀ a m Q X, addOneSpec a m Q X → Γ "add1" [i32] [i32] a m Q X)
    (x : BitVec 32) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hQ : Q (x + 1#32, ()) m) :
    wp Γ Q X (.call "add1" (as := [i32]) (bs := [i32]) (Arg.imm x, ())
      fun r => .ret (Arg.var r.1, ())) m := by
  run_tac wrapWpExprMData
  run_tac wrapOuterMData
  c0_hcall hSub
  exact hQ

theorem call_blocks_get_mdata (Γ : Env)
    (hHas : Γ.Has "add1" addOneSpec) (x : BitVec 32) (m : Mem 64)
    (Q : Post [i32]) (X : XPost) (hQ : Q (x + 1#32, ()) m) :
    wp Γ Q X
      (Blocks.get (.cons (fun (y : Tup Val [i32]) =>
        .call "add1" (as := [i32]) (bs := [i32]) (Arg.var y.1, ())
          fun r => .ret (Arg.var r.1, ())) .nil)
        .here (x, ())) m := by
  run_tac wrapOuterMData
  c0_hcall hHas
  exact hQ

theorem c0_call_unshadowed_let_before_call (Γ : Env)
    (hSub : ∀ a m Q X, addOneSpec a m Q X → Γ "add1" [i32] [i32] a m Q X)
    (x : BitVec 32) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hQ : Q ((x ^^^ 1#32) + 1#32, ()) m) :
    Func.wp Γ letBeforeCallBody (x, ()) m Q X := by
  unfold Func.wp letBeforeCallBody
  run_tac expectTacticFail (← `(tactic| c0_hcall hSub))
  c0_call hSub
  exact hQ

end C0HCallTests

/-! ## 2. `c0_hstep_np`, `c0_hfast_nogrp`, and `c0_hsteps_np` -/

section FastNoGrpNoPruneTests

theorem hstep_np_keeps_dead_jnz (Γ : Env) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (hQ : Q (2#32, ()) m) :
    wp Γ Q X (.jnz (Arg.imm false) (.ret (Arg.imm 1#32, ())) (.ret (Arg.imm 2#32, ()))) m := by
  c0_hstep_np
  run_tac checkGoalCount 2
  · simp at *
  · c0_hstep_np; exact hQ

theorem hfast_nogrp_stops_before_groups (Γ : Env) (c : Bool) (x : BitVec 32) (m : Mem 64)
    (Q : Post [i32]) (X : XPost)
    (hT : Q (x + 1#32, ()) m) (hF : Q (x + 2#32, ()) m) :
    wp Γ Q X (.let_ (op2 (.add i32) (Arg.imm x) (Arg.imm 0#32)) fun (y, _) =>
      .jnz (Arg.imm c)
        (.group (rs := [i32]) (sig := [[i32]])
          (fun _ => .cons (fun (z, _) => .ret (Arg.var z, ())) .nil)
          fun (J, _) =>
            .let_ (op2 (.add i32) (Arg.var y) (Arg.imm 1#32)) fun (z, _) =>
              .jump J (Arg.var z, ()))
        (.group (rs := [i32]) (sig := [[i32]])
          (fun _ => .cons (fun (z, _) => .ret (Arg.var z, ())) .nil)
          fun (J, _) =>
            .let_ (op2 (.add i32) (Arg.var y) (Arg.imm 2#32)) fun (z, _) =>
              .jump J (Arg.var z, ())))
      m := by
  c0_hfast_nogrp
  run_tac checkGoalCount 2
  · refine wp_unroll_group fun _ _ => ?_
    c0_hsteps_np
    simpa using hT
  · refine wp_unroll_group fun _ _ => ?_
    c0_hsteps_np
    simpa using hF

end FastNoGrpNoPruneTests

/-! ## 3. `HeadStepConfig.useBound` & `c0_*_nobound` Tactics -/

section UseBoundTests

theorem nobound_skips_c0_bound_and_uses_assumption (Γ : Env) (a : BitVec 64) (i : BitVec 32)
    (xs : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hm : (array64 a xs ⋆ R) m) (hiPlus : i.toNat + 1 ≤ xs.length)
    (hQ : ∀ hi : i.toNat < xs.length, Q (xs[i.toNat]'hi, ()) m) :
    wp Γ Q X (.load i64 (Arg.imm (a + i.setWidth 64 * 8)) fun v => .ret (Arg.var v, ())) m := by
  run_tac expectTacticFail (← `(tactic| c0_hsteps_nobound))
  run_tac expectTacticFail (← `(tactic| c0_hfast_nobound))
  run_tac expectTacticFail (← `(tactic| c0_hfast_nogrp_nobound))
  have hi : i.toNat < xs.length := by omega
  c0_hfast_nogrp_nobound
  exact hQ hi

theorem usebound_true_closes_with_c0_bound (Γ : Env) (a : BitVec 64) (i : BitVec 32)
    (xs : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hm : (array64 a xs ⋆ R) m) (hiPlus : i.toNat + 1 ≤ xs.length)
    (hQ : ∀ hi : i.toNat < xs.length, Q (xs[i.toNat]'hi, ()) m) :
    wp Γ Q X (.load i64 (Arg.imm (a + i.setWidth 64 * 8)) fun v => .ret (Arg.var v, ())) m := by
  c0_hsteps!
  exact hQ (by omega)

theorem hsplit_nobound_respects_flag (Γ : Env) (c : Bool) (a : BitVec 64) (i : BitVec 32)
    (xs : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hm : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length)
    (hT : Q (xs[i.toNat]'hi, ()) m) (hF : Q (0#64, ()) m) :
    wp Γ Q X (.jnz (Arg.imm c)
      (.load i64 (Arg.imm (a + i.setWidth 64 * 8)) fun v => .ret (Arg.var v, ()))
      (.ret (Arg.imm 0#64, ()))) m := by
  c0_hsplit_nobound
  · c0_hstep_nobound; c0_hstep_nobound; exact hT
  · c0_hstep_nobound; exact hF

end UseBoundTests

/-! ## 4. `.mdata` Stripping (`c0_mstep`, `c0_msteps`, `c0_msteps!`, `c0_mto_group`, `c0_msplit`) -/

section MDataStrippingTests

theorem c0_step_and_steps_strip_outer_inner_mdata (Γ : Env) (a : BitVec 64) (i : BitVec 32)
    (xs : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hm : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length)
    (hQ : Q (xs[i.toNat]'hi + 3#64, ()) m) :
    wp Γ Q X (.let_ (op2 (.add i32) (Arg.imm 1#32) (Arg.imm 2#32)) fun (_, _) =>
      .load i64 (Arg.imm (a + i.setWidth 64 * 8)) fun v =>
        .let_ (op2 (.add i64) (Arg.var v) (Arg.imm 3#64)) fun (w, _) =>
          .ret (Arg.var w, ())) m := by
  run_tac wrapWpExprMData
  run_tac wrapOuterMData
  c0_mstep
  run_tac wrapWpExprMData
  run_tac wrapOuterMData
  c0_msteps!
  exact hQ

theorem c0_steps_non_strict_mdata (Γ : Env) (x : BitVec 32) (m : Mem 64)
    (Q : Post [i32]) (X : XPost) (hQ : Q (x + 5#32, ()) m) :
    wp Γ Q X (.let_ (op2 (.add i32) (Arg.imm x) (Arg.imm 5#32)) fun (y, _) =>
      .ret (Arg.var y, ())) m := by
  run_tac wrapWpExprMData
  run_tac wrapOuterMData
  c0_msteps
  exact hQ

theorem c0_to_group_strips_inner_mdata (Γ : Env) (x : BitVec 32) (m : Mem 64)
    (Q : Post [i32]) (X : XPost) (hQ : Q (x + 1#32 + 3#32, ()) m) :
    wp Γ Q X (.let_ (op2 (.add i32) (Arg.imm x) (Arg.imm 1#32)) fun (y, _) =>
      .group (rs := [i32]) (sig := [[i32]])
        (fun _ => .cons (fun (z, _) => .ret (Arg.var z, ())) .nil)
        fun (J, _) =>
          .let_ (op2 (.add i32) (Arg.var y) (Arg.imm 3#32)) fun (z, _) =>
            .jump J (Arg.var z, ())) m := by
  run_tac wrapWpExprMData
  run_tac wrapOuterMData
  c0_mto_group
  refine wp_unroll_group fun _ _ => ?_
  c0_msteps
  exact hQ

theorem c0_split_strips_inner_mdata (Γ : Env) (c : Bool) (x : BitVec 32) (m : Mem 64)
    (Q : Post [i32]) (X : XPost) (hT : Q (x + 1#32, ()) m) (hF : Q (x + 2#32, ()) m) :
    wp Γ Q X (.let_ (op2 (.add i32) (Arg.imm x) (Arg.imm 0#32)) fun (y, _) =>
      .jnz (Arg.imm c)
        (.let_ (op2 (.add i32) (Arg.var y) (Arg.imm 1#32)) fun (z, _) => .ret (Arg.var z, ()))
        (.let_ (op2 (.add i32) (Arg.var y) (Arg.imm 2#32)) fun (z, _) => .ret (Arg.var z, ())))
      m := by
  run_tac wrapWpExprMData
  run_tac wrapOuterMData
  c0_msplit
  · c0_msteps; simpa using hT
  · c0_msteps; simpa using hF

theorem c0_steps_unshadowed_stops_on_inner_mdata (Γ : Env) (x : BitVec 32) (m : Mem 64)
    (Q : Post [i32]) (X : XPost) (hQ : Q (x + 5#32, ()) m) :
    wp Γ Q X (.let_ (op2 (.add i32) (Arg.imm x) (Arg.imm 5#32)) fun (y, _) =>
      .ret (Arg.var y, ())) m := by
  run_tac wrapWpExprMData
  run_tac expectTacticFail (← `(tactic| c0_step))
  c0_msteps
  exact hQ

end MDataStrippingTests

/-! ## 5. Axiom Audit (`<= [propext, Classical.choice, Quot.sound]`) -/

#print axioms call_explicit_fwd1
#print axioms call_implicit_fwd0
#print axioms call_env_has_cont
#print axioms call_env_sat_has
#print axioms call_mdata_wrapped_ret
#print axioms call_blocks_get_mdata
#print axioms c0_call_unshadowed_let_before_call
#print axioms hstep_np_keeps_dead_jnz
#print axioms hfast_nogrp_stops_before_groups
#print axioms nobound_skips_c0_bound_and_uses_assumption
#print axioms usebound_true_closes_with_c0_bound
#print axioms hsplit_nobound_respects_flag
#print axioms c0_step_and_steps_strip_outer_inner_mdata
#print axioms c0_steps_non_strict_mdata
#print axioms c0_to_group_strips_inner_mdata
#print axioms c0_split_strips_inner_mdata
#print axioms c0_steps_unshadowed_stops_on_inner_mdata

end LeanQbeTest.T.C0HeadStepP02Test
