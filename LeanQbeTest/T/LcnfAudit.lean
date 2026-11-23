module

public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.LeanLCNF.Demo
public import LeanQbe.T.LeanLCNF.Coverage
public import LeanQbe.T.LeanLRC.ToT
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.LeanLCNF.Demo
meta import LeanQbe.T.LeanLCNF.Coverage
meta import LeanQbe.T.LeanLRC.ToT
meta import LeanQbe.T.FlatLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# `LeanLCNF` & `LeanLRC` Frontend Lowering Audit

Self-contained audit for the Lean 4 impure-LCNF (`LeanQbe.T.LeanLCNF`) and λRC
(`LeanQbe.T.LeanLRC`) frontends targeting `LeanQbe.T`. Architecture-independent (imports neither
`Kraken.X64` nor `Kraken.AArch64`).

## What This Workstream Proves
1. **Unconditional PHOAS well-formedness (`audit_tflat_wf`)**: every `TFlatFn` lowered by either
   `LeanLCNF` or `LeanLRC` and reified via `LeanLRC.tflatFnsToFns` satisfies `Fn.Wf` (parametric
   PHOAS scoping/typing) unconditionally, making every lowered function admissible to the verified
   `LeanQbe.T` mid-end (`OptLemmas`), legalizer (`LegalLemmas`), and backend (`MainLemmas`).
2. **Real impure LCNF demo (`audit_lcnf_demo_wf`)**: all 80+ real Lean 4 declarations extracted
   from `LeanLCNF.Demo` (red-black trees with FBIP `isShared`/`oset` reuse, merge sort + closures,
   DPLL SAT solver, 6-parameter `UInt64` VM, boxed `USize` closures) plus synthesized
   `lcnf_apply_1..3` dispatchers satisfy `Fn.Wf` and `Func.checkTFlat`.
3. **Core C0 runtime & λRC modules (`audit_lrc_rt_wf`, `audit_lrc_mod_wf`)**: all 28 C0 runtime
   functions (`rtBase_fns`: boxing/unboxing, reference counting, bump allocation, constructors,
   closures, `Nat` arithmetic) satisfy `Fn.Wf` via `t_wf_reify`, and every combined
   `toLeanModuleWithRuntime tfs` module satisfies `∀ f ∈ m.fns, f.Wf`.

## Inputs / Assumptions
* `LeanLCNF.Demo.demoMod` is extracted at elaboration time by `lcnf_of_lean!` from real Lean 4
  definitions; `LeanLRC.realLeanIrMod` is extracted from real `Lean.IR`.
* `lowerModule` / `lowerLrcProgram` succeed (checked by `#guard` below) and emit `TFlatFn` lists
  that reify cleanly to `LeanQbe.T.Fn`, C++20 (`PrintCpp`), and QBE SSA (`PrintQbe`).

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`) for all `Fn.Wf` proofs.
* **Important scope note**: semantic preservation of the `lcnf_of_lean!` / `lrc_of_lean!` meta
  extractors and of the `LeanLCNF` / `LeanLRC` lowering passes themselves is currently validated
  by differential execution against Lean 4 (`test/lcnf/run.sh`, `test/lrc/run.sh`) rather than by
  a Lean-level semantic refinement proof; only structural `Fn.Wf` + `Func.checkTFlat` + codegen
  invariants are formally proved here.
-/

set_option autoImplicit false

@[expose] public section

namespace LcnfAudit

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLRC
open LeanQbe.T.Frontend.C0 (TFlatFn)

/-! ## 1. Formal `Fn.Wf` Theorems -/

/-- Lowered `TFlatFn` list for `Demo.lcnfProgram` (verified non-error by `#guard` below). -/
def demoTfs : List TFlatFn :=
  (lowerModule Demo.lcnfProgram).toOption.getD []

/-- Reified `LeanQbe.T.Fn` list for `Demo.lcnfProgram`. -/
def demoFns : List Fn :=
  LeanLRC.tflatFnsToFns demoTfs

theorem audit_tflat_wf (tfs : List TFlatFn) :
    ∀ f ∈ LeanLRC.tflatFnsToFns tfs, f.Wf :=
  LeanLRC.tflatFnsToFns_wf tfs

theorem audit_lcnf_demo_wf :
    ∀ f ∈ demoFns, f.Wf :=
  LeanLRC.tflatFnsToFns_wf demoTfs

/-- Lowered `TFlatFn` list for `Coverage.covProgram` (verified non-error by `#guard` below). -/
def covTfs : List TFlatFn :=
  (lowerModule Coverage.covProgram).toOption.getD []

/-- Reified `LeanQbe.T.Fn` list for `Coverage.covProgram`. -/
def covFns : List Fn :=
  LeanLRC.tflatFnsToFns covTfs

theorem audit_lcnf_cov_wf :
    ∀ f ∈ covFns, f.Wf :=
  LeanLRC.tflatFnsToFns_wf covTfs

private theorem wf_is_scalar : Func.Wf lean_is_scalar_body := by t_wf_reify
private theorem wf_box : Func.Wf lean_box_body := by t_wf_reify
private theorem wf_unbox : Func.Wf lean_unbox_body := by t_wf_reify
private theorem wf_obj_tag : Func.Wf lean_obj_tag_body := by t_wf_reify
private theorem wf_rt_enter : Func.Wf lean_rt_enter_body := by t_wf_reify
private theorem wf_rt_tick : Func.Wf lean_rt_tick_body := by t_wf_reify
private theorem wf_rt_leave : Func.Wf lean_rt_leave_body := by t_wf_reify
private theorem wf_alloc_small : Func.Wf lean_alloc_small_body := by t_wf_reify
private theorem wf_alloc_ctor : Func.Wf lean_alloc_ctor_body := by t_wf_reify
private theorem wf_ctor_get : Func.Wf lean_ctor_get_body := by t_wf_reify
private theorem wf_ctor_set : Func.Wf lean_ctor_set_body := by t_wf_reify
private theorem wf_ctor_set_tag : Func.Wf lean_ctor_set_tag_body := by t_wf_reify
private theorem wf_inc : Func.Wf lean_inc_body := by t_wf_reify
private theorem wf_dec : Func.Wf lean_dec_body := by t_wf_reify
private theorem wf_is_shared : Func.Wf lean_is_shared_body := by t_wf_reify
private theorem wf_alloc_clo : Func.Wf lean_alloc_closure_body := by t_wf_reify
private theorem wf_clo_get : Func.Wf lean_closure_get_body := by t_wf_reify
private theorem wf_clo_set : Func.Wf lean_closure_set_body := by t_wf_reify
private theorem wf_box_u64 : Func.Wf lean_box_u64_body := by t_wf_reify
private theorem wf_unbox_u64 : Func.Wf lean_unbox_u64_body := by t_wf_reify
private theorem wf_nat_add : Func.Wf lean_nat_add_body := by t_wf_reify
private theorem wf_nat_sub : Func.Wf lean_nat_sub_body := by t_wf_reify
private theorem wf_nat_mul : Func.Wf lean_nat_mul_body := by t_wf_reify
private theorem wf_nat_div : Func.Wf lean_nat_div_body := by t_wf_reify
private theorem wf_nat_mod : Func.Wf lean_nat_mod_body := by t_wf_reify
private theorem wf_nat_eq : Func.Wf lean_nat_dec_eq_body := by t_wf_reify
private theorem wf_nat_le : Func.Wf lean_nat_dec_le_body := by t_wf_reify
private theorem wf_nat_lt : Func.Wf lean_nat_dec_lt_body := by t_wf_reify

theorem audit_lrc_rt_wf :
    ∀ f ∈ LeanLRC.rtBase_fns, f.Wf := by
  intro f hf
  simp only [rtBase_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wf_is_scalar
  · exact wf_box
  · exact wf_unbox
  · exact wf_obj_tag
  · exact wf_rt_enter
  · exact wf_rt_tick
  · exact wf_rt_leave
  · exact wf_alloc_small
  · exact wf_alloc_ctor
  · exact wf_ctor_get
  · exact wf_ctor_set
  · exact wf_ctor_set_tag
  · exact wf_inc
  · exact wf_dec
  · exact wf_is_shared
  · exact wf_alloc_clo
  · exact wf_clo_get
  · exact wf_clo_set
  · exact wf_box_u64
  · exact wf_unbox_u64
  · exact wf_nat_add
  · exact wf_nat_sub
  · exact wf_nat_mul
  · exact wf_nat_div
  · exact wf_nat_mod
  · exact wf_nat_eq
  · exact wf_nat_le
  · exact wf_nat_lt

theorem audit_lrc_mod_wf (tfs : List TFlatFn) :
    ∀ f ∈ (LeanLRC.toLeanModuleWithRuntime tfs).fns, f.Wf := by
  intro f hf
  simp only [toLeanModuleWithRuntime, List.mem_append] at hf
  rcases hf with hrt | hprog
  · exact audit_lrc_rt_wf f hrt
  · exact LeanLRC.tflatFnsToFns_wf tfs f hprog

/-! ## 2. Concrete `#guard` Sanity Checks (Lean 4 Semantics, Lowering, Codegen) -/

-- Real Lean 4 demo functions behave as expected before lowering.
#guard Demo.usizeSum 5 == 37
#guard Demo.satSolve 0 3 2 0 % 2 == 0
#guard Demo.satSolve 0 2 2 0 % 2 == 1
#guard Demo.sortBench 8 42 % 2 == 1
#guard Demo.vmBench 8 3 42 > 0

-- Spliced impure LCNF structure and lowering invariants.
#guard Demo.demoMod.decls.length ≥ 80
#guard Demo.demoMod.maxAp == 3
#guard (lowerModule Demo.lcnfProgram).isOk
#guard demoTfs.length == Demo.lcnfProgram.decls.length + 3
#guard demoFns.all fun f => Func.checkTFlat f.body
#guard (demoFns.map (·.name)).contains "lcnf_apply_3"
#guard (PrintCpp.ppTModule (lcnfTModule demoTfs)).isOk
#guard (lowerModule Coverage.covProgram).isOk
#guard !covFns.isEmpty
#guard covFns.all fun f => Func.checkTFlat f.body
#guard (PrintCpp.ppTModule (lcnfTModule covTfs)).isOk
#guard (PrintQbe.module (lcnfTModule covTfs)).isOk

-- LeanLRC runtime, benchmark modules, real spliced Lean.IR, and codegen.
#guard LeanLRC.rtBase_fns.length == 28
#guard LeanLRC.rtBase_fns.all fun fn => Func.checkTFlat fn.body
#guard LeanLRC.sumToMod.sccs == [["lrc_sumTo"], ["lrc_sumToAcc"]]
#guard LeanLRC.realLeanIrMod.maxApArity == 2
#guard match lowerLrcProgram LeanLRC.allBenchLrcMod with
  | .ok tfs =>
    let m := toLeanModuleWithRuntime tfs
    m.fns.length == 61 &&
      (tflatFnsToFns tfs).all (fun fn => Func.checkTFlat fn.body) &&
      (PrintCpp.ppTModule m).isOk &&
      (PrintQbe.module m).isOk
  | .error _ => false
#guard match lowerLrcProgram LeanLRC.realLeanIrMod with
  | .ok tfs => (tflatFnsToFns tfs).all fun fn => Func.checkTFlat fn.body
  | .error _ => false

/-! ## 3. Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_tflat_wf
#print axioms audit_lcnf_demo_wf
#print axioms audit_lcnf_cov_wf
#print axioms audit_lrc_rt_wf
#print axioms audit_lrc_mod_wf

end LcnfAudit
