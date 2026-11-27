/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop0
public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop1
public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop2

/-!
# Top-Level Bitblast `OpsDivCpop` Module Proof (`Bitblast.Proof.OpsDivCpop`)

Assembles all `9` canonical `Γ`-parametric `Func.wp` proofs from `OpsDivCpop{0,1,2}` into:
* `opsDivCpop_tableImpl`: `TableImpl Γ opsDivCpopFns opsDivCpopSpecs`
* `opsDivCpop_moduleOk`: `ModuleOk opsDivCpopEnv opsDivCpopModule`
* `opsDivCpopSpecs_xfree` & `opsDivCpopEnv_xfree`: `Spec.XFree` and `noExit` soundness
* `opsDivCpopEnv_has_*`: `Env.Has` witnesses for every function and dependency
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop
open LeanQbe.T.Examples.Bitblast.Proof

section

/-- Closed specification table covering both external AIG/`OpsCore` dependencies and all `9`
`OpsDivCpop` C0 functions. -/
@[expose] public def opsDivCpopTable : List SpecEntry :=
  opsDivCpopDeps ++ opsDivCpopSpecs

/-- Canonical `Env.ofTable` environment for `opsDivCpopModule`. -/
@[expose] public def opsDivCpopEnv : Env :=
  Env.ofTable opsDivCpopTable

private theorem ofTable_append_right {A B : List SpecEntry} {f : Sym}
    (hne : ∀ e ∈ A, e.name ≠ f) {as bs : List Ty} (xs : Tup Val as) (m : Mem 64)
    (Q : Post bs) (X : XPost) (h : Env.ofTable (A ++ B) f as bs xs m Q X) :
    Env.ofTable B f as bs xs m Q X := by
  induction A with
  | nil => exact h
  | cons a A ih =>
    apply ih (fun e he => hne e (List.mem_cons_of_mem a he))
    exact (Env.ofTable_cons_ne (hne a List.mem_cons_self) xs m Q X).mp h

public theorem opsDivCpopTable_nodup :
    (List.map SpecEntry.name opsDivCpopTable).Nodup := by
  decide

public theorem opsDivCpopFns_nodup :
    (List.map Fn.name opsDivCpopFns).Nodup := by
  decide

public theorem opsDivCpopTable_noExit :
    ∀ e ∈ opsDivCpopTable, e.noExit = true := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · simp only [opsDivCpopDeps, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [opsDivCpopSpecs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

public theorem opsDivCpopSpecs_noExit :
    ∀ e ∈ opsDivCpopSpecs, e.noExit = true := fun e he =>
  opsDivCpopTable_noExit e (List.mem_append_right _ he)

public theorem opsDivCpopSpecs_xfree :
    ∀ e ∈ opsDivCpopSpecs, e.spec.XFree := by
  intro e he
  simp only [opsDivCpopSpecs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bvBlastIteIntoSpec_xfree
  · exact bvBlastIteSliceSpec_xfree
  · exact bvBlastSubWithBorrowSpec_xfree
  · exact bvBlastUdivUmodSpec_xfree
  · exact bvBlastUdivSpec_xfree
  · exact bvBlastUmodSpec_xfree
  · exact bvBlastAddIntoSpec_xfree
  · exact bvBlastCpopLayerSpec_xfree
  · exact bvBlastCpopSpec_xfree

public theorem opsDivCpopEnv_sat : opsDivCpopEnv.Sat opsDivCpopTable :=
  Env.Sat.ofTable_self opsDivCpopTable_nodup

public theorem opsDivCpopEnv_satDeps : opsDivCpopEnv.Sat opsDivCpopDeps :=
  Env.Sat.ofTable opsDivCpopTable_nodup (fun _ he => List.mem_append_left _ he)

public theorem opsDivCpopEnv_satSpecs : opsDivCpopEnv.Sat opsDivCpopSpecs :=
  Env.Sat.ofTable opsDivCpopTable_nodup (fun _ he => List.mem_append_right _ he)

public theorem opsDivCpopEnv_has_bv_slice_ok :
    opsDivCpopEnv.Has "bv_slice_ok" bvSliceOkSpec :=
  opsDivCpopEnv_satDeps ⟨"bv_slice_ok", [i64, i32, i32], [Ty.bool], bvSliceOkSpec, true⟩
    (by simp [opsDivCpopDeps])

public theorem opsDivCpopEnv_has_bv_blast_eq :
    opsDivCpopEnv.Has "bv_blast_eq" bvBlastEqSpec :=
  opsDivCpopEnv_satDeps ⟨"bv_blast_eq", [i64, i32, i32, i32], [i32], bvBlastEqSpec, true⟩
    (by simp [opsDivCpopDeps])

public theorem opsDivCpopEnv_has_ite_into :
    opsDivCpopEnv.Has "bv_blast_ite_into" bvBlastIteIntoSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_ite_into", [i64, i32, i32, i32, i32, i32], [Ty.bool], bvBlastIteIntoSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_has_ite_slice :
    opsDivCpopEnv.Has "bv_blast_ite_slice" bvBlastIteSliceSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_ite_slice", [i64, i32, i32, i32, i32], [i32], bvBlastIteSliceSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_has_sub_with_borrow :
    opsDivCpopEnv.Has "bv_blast_sub_with_borrow" bvBlastSubWithBorrowSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_sub_with_borrow", [i64, i32, i32, i32, i32], [i32], bvBlastSubWithBorrowSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_has_udiv_umod :
    opsDivCpopEnv.Has "bv_blast_udiv_umod" bvBlastUdivUmodSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_udiv_umod", [i64, i32, i32, i32, i32], [i32], bvBlastUdivUmodSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_has_udiv :
    opsDivCpopEnv.Has "bv_blast_udiv" bvBlastUdivSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_udiv", [i64, i32, i32, i32], [i32], bvBlastUdivSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_has_umod :
    opsDivCpopEnv.Has "bv_blast_umod" bvBlastUmodSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_umod", [i64, i32, i32, i32], [i32], bvBlastUmodSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_has_add_into :
    opsDivCpopEnv.Has "bv_blast_add_into" bvBlastAddIntoSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_add_into", [i64, i32, i32, i32, i32], [Ty.bool], bvBlastAddIntoSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_has_cpop_layer :
    opsDivCpopEnv.Has "bv_blast_cpop_layer" bvBlastCpopLayerSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_cpop_layer", [i64, i32, i32, i32, i32], [Ty.bool], bvBlastCpopLayerSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_has_cpop :
    opsDivCpopEnv.Has "bv_blast_cpop" bvBlastCpopSpec :=
  opsDivCpopEnv_satSpecs
    ⟨"bv_blast_cpop", [i64, i32, i32], [i32], bvBlastCpopSpec, true⟩
    (by simp [opsDivCpopSpecs])

public theorem opsDivCpopEnv_noExit :
    ∀ (f : Sym) (as bs : List Ty) (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X X' : XPost),
      opsDivCpopEnv f as bs xs m Q X → opsDivCpopEnv f as bs xs m Q X' :=
  Env.ofTable_noExit opsDivCpopTable_noExit

public theorem opsDivCpop_tableImpl (Γ : Env)
    (hDeps : Γ.Sat opsDivCpopDeps) (hSpecs : Γ.Sat opsDivCpopSpecs) :
    TableImpl Γ opsDivCpopFns opsDivCpopSpecs := by
  simp only [Env.Sat, opsDivCpopDeps, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hDeps
  simp only [Env.Sat, opsDivCpopSpecs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hSpecs
  rcases hDeps with ⟨hAnd, hNot, hOr, hXor, hIte, hMark, hRel, hAlloc, hOk, hEq⟩
  rcases hSpecs with ⟨hIteInto, _, hSub, hUdivUmod, _, _, hAdd, hLayer, _⟩
  dsimp only [opsDivCpopFns, ops_div_cpop_fns, opsDivCpopSpecs, TableImpl]
  refine ⟨SpecEntry.Impl.of (bv_blast_ite_into_wp Γ hOk hIte), ?_⟩
  refine ⟨SpecEntry.Impl.of (bv_blast_ite_slice_wp Γ hOk hMark hRel hAlloc hIteInto), ?_⟩
  refine ⟨SpecEntry.Impl.of (bv_blast_sub_with_borrow_wp Γ hOk hNot hAnd hOr hXor), ?_⟩
  refine ⟨SpecEntry.Impl.of
    (bv_blast_udiv_umod_wp Γ hOk hMark hAlloc hRel hEq hNot hSub hIteInto), ?_⟩
  refine ⟨SpecEntry.Impl.of (bv_blast_udiv_wp Γ hUdivUmod), ?_⟩
  refine ⟨SpecEntry.Impl.of (bv_blast_umod_wp Γ hUdivUmod), ?_⟩
  refine ⟨SpecEntry.Impl.of (bv_blast_add_into_wp Γ hOk hXor hAnd hOr), ?_⟩
  refine ⟨SpecEntry.Impl.of (bv_blast_cpop_layer_wp Γ hOk hAdd), ?_⟩
  exact ⟨SpecEntry.Impl.of (bv_blast_cpop_wp Γ hOk hMark hAlloc hRel hLayer), True.intro⟩

public theorem opsDivCpopEnv_tableImpl :
    TableImpl opsDivCpopEnv opsDivCpopFns opsDivCpopSpecs :=
  opsDivCpop_tableImpl opsDivCpopEnv opsDivCpopEnv_satDeps opsDivCpopEnv_satSpecs

public theorem opsDivCpop_moduleOk :
    ModuleOk opsDivCpopEnv opsDivCpopModule := by
  refine Module.moduleOk_of_checkAcyclic opsDivCpop_checkAcyclic opsDivCpopFns_wf ?_
  have hSound := Env.ofTable_sound opsDivCpopFns_nodup opsDivCpopEnv_tableImpl
  intro fn hfn xs m Q X hPre
  apply hSound fn hfn xs m Q X
  have hne : ∀ e ∈ opsDivCpopDeps, e.name ≠ fn.name := by
    have hAll : ∀ f ∈ opsDivCpopFns, ∀ d ∈ opsDivCpopDeps, d.name ≠ f.name := by decide
    exact hAll fn hfn
  exact ofTable_append_right hne xs m Q X hPre

end

end LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop
