/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.InlinePlanLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbeTest.T.SegCertToy.SrcFull
public import LeanQbeTest.T.SegCertToy.Build.Inl.Full
meta import LeanQbe.T.InlinePlan
meta import LeanQbe.T.Module
meta import LeanQbe.T.Ty
meta import LeanQbeTest.T.SegCertToy.SrcFull
meta import LeanQbeTest.T.SegCertToy.Build.Inl.Full

/-!
# Gate G1 Arch-Neutral Spec, `ModuleOk`, and Policy-vs-Plan Parity (`SegCertToyTest`)

Proves `ModuleOk toyEnv toyModule` for the 3-segment Gate G1 toy and verifies exact post-inline
`TFlatFn` AST parity between `toyModule.inlinePlan Build.Inl.Full.fullPlan` and legacy
`toyModule.optInlinePolicy toyPolicy` (including multi-dep cross-segment inlining).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToyTest

open LeanQbe.T
open LeanQbeTest.T.SegCertToy

/-- Specification value of `toy_inc(x)`. -/
@[expose] def toyIncVal (x : BitVec 64) : BitVec 64 := x + 1#64

/-- Specification value of `toy_helper1(x)`. -/
@[expose] def toyHelper1Val (x : BitVec 64) : BitVec 64 := (x + 7#64) ^^^ 3#64

/-- Specification value of `toy_add_inc(x, y)`. -/
@[expose] def toyAddIncVal (x y : BitVec 64) : BitVec 64 := toyIncVal x + y

/-- Specification value of `toy_mix2(x, y)`. -/
@[expose] def toyMix2Val (x y : BitVec 64) : BitVec 64 :=
  toyAddIncVal (toyHelper1Val x) y + 2#64

/-- Specification value of `toy_step3(x)`. -/
@[expose] def toyStep3Val (x : BitVec 64) : BitVec 64 :=
  toyIncVal (toyAddIncVal x 10#64) + 5#64

/-- Specification value of `toy_main(x, y)`. -/
@[expose] def toyMainVal (x y : BitVec 64) : BitVec 64 :=
  toyMix2Val x y + toyStep3Val x

#guard toyMainVal 10#64 20#64 == 68#64

/-- Pure specification lookup for the 6-function Gate G1 toy module. -/
@[expose] def toySpec (f : Sym) (as bs : List Ty) : Option (Tup Val as → Mem 64 → Post bs → Prop) :=
  match f, as, bs with
  | "toy_inc", [.bits 64], [.bits 64] => some fun (x, ()) m Q => Q (toyIncVal x, ()) m
  | "toy_helper1", [.bits 64], [.bits 64] => some fun (x, ()) m Q => Q (toyHelper1Val x, ()) m
  | "toy_add_inc", [.bits 64, .bits 64], [.bits 64] =>
      some fun (x, y, ()) m Q => Q (toyAddIncVal x y, ()) m
  | "toy_mix2", [.bits 64, .bits 64], [.bits 64] =>
      some fun (x, y, ()) m Q => Q (toyMix2Val x y, ()) m
  | "toy_step3", [.bits 64], [.bits 64] => some fun (x, ()) m Q => Q (toyStep3Val x, ()) m
  | "toy_main", [.bits 64, .bits 64], [.bits 64] =>
      some fun (x, y, ()) m Q => Q (toyMainVal x y, ()) m
  | _, _, _ => none

/-- Total arithmetic specification environment for the 6-function Gate G1 toy module. -/
@[expose] def toyEnv : Env := fun f as bs xs m Q _ =>
  match toySpec f as bs with
  | some spec => spec xs m Q
  | none => False

theorem toyEnv_noExit (f : Fn) : InlNoExit toyEnv f :=
  fun _ _ _ _ _ h => h

private theorem fnToyInc_wf : Src1.fnToyInc.Wf := by t_wf_reify
private theorem fnToyHelper1_wf : Src1.fnToyHelper1.Wf := by t_wf_reify
private theorem fnToyAddInc_wf : Src2.fnToyAddInc.Wf := by t_wf_reify
private theorem fnToyMix2_wf : Src2.fnToyMix2.Wf := by t_wf_reify
private theorem fnToyStep3_wf : Src3.fnToyStep3.Wf := by t_wf_reify
private theorem fnToyMain_wf : Src3.fnToyMain.Wf := by t_wf_reify

/-- Source `ModuleOk` for the 3-segment Gate G1 toy module. -/
theorem toyModule_ok : ModuleOk toyEnv SrcFull.toyModule := by
  refine ⟨by simp [Module.namesNodup, Module.names, SrcFull.toyModule, SrcFull.toyFns,
    Src1.fns, Src2.fns, Src3.fns, Src1.fnToyInc, Src1.fnToyHelper1, Src2.fnToyAddInc,
    Src2.fnToyMix2, Src3.fnToyStep3, Src3.fnToyMain], fun pre fn post hsplit => ?_⟩
  rcases pre with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, pre⟩⟩⟩⟩⟩⟩ <;>
    simp [SrcFull.toyModule, SrcFull.toyFns, Src1.fns, Src2.fns, Src3.fns] at hsplit
  · rcases hsplit with ⟨rfl, rfl⟩
    refine ⟨fnToyInc_wf, by simp [Fn.callsOk, Src1.fnToyInc, Expr.callsOk], ?_⟩
    rintro ⟨x, ⟨⟩⟩ m Q X h
    simpa [Func.wp, Src1.fnToyInc, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat,
      Arg.val, vals, toyEnv, toySpec, toyIncVal] using h
  · rcases hsplit with ⟨rfl, rfl, rfl⟩
    refine ⟨fnToyHelper1_wf, by simp [Fn.callsOk, Src1.fnToyHelper1, Expr.callsOk], ?_⟩
    rintro ⟨x, ⟨⟩⟩ m Q X h
    simpa [Func.wp, Src1.fnToyHelper1, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat,
      Arg.val, vals, toyEnv, toySpec, toyHelper1Val] using h
  · rcases hsplit with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨fnToyAddInc_wf,
      by simp [Fn.callsOk, Src2.fnToyAddInc, Expr.callsOk, Fn.sig, Src1.fnToyInc], ?_⟩
    rintro ⟨x, y, ⟨⟩⟩ m Q X h
    simp only [Func.wp, Src2.fnToyAddInc, wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat,
      Arg.val, vals, toyEnv, toySpec, toyAddIncVal, i64, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact ⟨fun (t, _) m₁ => t = toyIncVal x ∧ m₁ = m, X, ⟨rfl, rfl⟩,
      by rintro ⟨_, ⟨⟩⟩ _ ⟨rfl, rfl⟩; exact h, fun _ _ _ _ hx => hx⟩
  · rcases hsplit with ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨fnToyMix2_wf,
      by simp [Fn.callsOk, Src2.fnToyMix2, Expr.callsOk, Fn.sig,
               Src1.fnToyHelper1, Src2.fnToyAddInc], ?_⟩
    rintro ⟨x, y, ⟨⟩⟩ m Q X h
    simp only [Func.wp, Src2.fnToyMix2, wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat,
      Arg.val, vals, toyEnv, toySpec, toyMix2Val, i64, Bool.false_eq_true, ↓reduceIte] at h ⊢
    refine ⟨fun (a, _) m₁ => a = toyHelper1Val x ∧ m₁ = m, X, ⟨rfl, rfl⟩, ?_,
      fun _ _ _ _ hx => hx⟩
    rintro ⟨a, ⟨⟩⟩ m₁ ⟨rfl, rfl⟩
    exact ⟨fun (b, _) m₂ => b = toyAddIncVal (toyHelper1Val x) y ∧ m₂ = m₁, X, ⟨rfl, rfl⟩,
      by rintro ⟨_, ⟨⟩⟩ _ ⟨rfl, rfl⟩; exact h, fun _ _ _ _ hx => hx⟩
  · rcases hsplit with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨fnToyStep3_wf,
      by simp [Fn.callsOk, Src3.fnToyStep3, Expr.callsOk, Fn.sig,
               Src1.fnToyInc, Src2.fnToyAddInc], ?_⟩
    rintro ⟨x, ⟨⟩⟩ m Q X h
    simp only [Func.wp, Src3.fnToyStep3, wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat,
      Arg.val, vals, toyEnv, toySpec, toyStep3Val, i64, Bool.false_eq_true, ↓reduceIte] at h ⊢
    refine ⟨fun (a, _) m₁ => a = toyAddIncVal x 10#64 ∧ m₁ = m, X, ⟨rfl, rfl⟩, ?_,
      fun _ _ _ _ hx => hx⟩
    rintro ⟨a, ⟨⟩⟩ m₁ ⟨rfl, rfl⟩
    exact ⟨fun (b, _) m₂ => b = toyIncVal (toyAddIncVal x 10#64) ∧ m₂ = m₁, X, ⟨rfl, rfl⟩,
      by rintro ⟨_, ⟨⟩⟩ _ ⟨rfl, rfl⟩; exact h, fun _ _ _ _ hx => hx⟩
  · rcases hsplit with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨fnToyMain_wf,
      by simp [Fn.callsOk, Src3.fnToyMain, Expr.callsOk, Fn.sig,
               Src2.fnToyMix2, Src3.fnToyStep3], ?_⟩
    rintro ⟨x, y, ⟨⟩⟩ m Q X h
    simp only [Func.wp, Src3.fnToyMain, wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat,
      Arg.val, vals, toyEnv, toySpec, toyMainVal, i64, Bool.false_eq_true, ↓reduceIte] at h ⊢
    refine ⟨fun (a, _) m₁ => a = toyMix2Val x y ∧ m₁ = m, X, ⟨rfl, rfl⟩, ?_,
      fun _ _ _ _ hx => hx⟩
    rintro ⟨a, ⟨⟩⟩ m₁ ⟨rfl, rfl⟩
    exact ⟨fun (b, _) m₂ => b = toyStep3Val x ∧ m₂ = m₁, X, ⟨rfl, rfl⟩,
      by rintro ⟨_, ⟨⟩⟩ _ ⟨rfl, rfl⟩; exact h, fun _ _ _ _ hx => hx⟩

/-! ## Policy-vs-Plan Exact AST Parity Checks (Kernel `rfl` + `#guard`) -/

@[expose] def reifyModFns (M : Module) : List TFlatFn :=
  M.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩

/-- Kernel-verified exact post-inline `TFlatFn` parity between `inlinePlan fullPlan` and legacy
`optInlinePolicy`. -/
theorem inlinePlan_vs_optInlinePolicy_ast_eq :
    reifyModFns (SrcFull.toyModule.inlinePlan Build.Inl.Full.fullPlan) =
      reifyModFns (SrcFull.toyModule.optInlinePolicy SrcFull.toyPolicy) := rfl

private def dummyFn : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

private def planInlFns : List Fn :=
  (SrcFull.toyModule.inlinePlan Build.Inl.Full.fullPlan).fns

private def policyInlFns : List Fn :=
  (SrcFull.toyModule.optInlinePolicy SrcFull.toyPolicy).fns

#guard (planInlFns.map Fn.name) == (policyInlFns.map Fn.name)
#guard (planInlFns.map Fn.size) == (policyInlFns.map Fn.size)
#guard (planInlFns.getD 2 dummyFn).checkCallsOk [] []
#guard (planInlFns.getD 3 dummyFn).checkCallsOk [("toy_helper1", [i64], [i64])] []
#guard !(planInlFns.getD 3 dummyFn).checkCallsOk [] []
#guard (planInlFns.getD 4 dummyFn).checkCallsOk [] []
#guard (planInlFns.getD 5 dummyFn).checkCallsOk
  [("toy_mix2", [i64, i64], [i64]), ("toy_step3", [i64], [i64])] []

end LeanQbeTest.T.SegCertToyTest
