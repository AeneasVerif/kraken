module

import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.FlatLemmas
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.LeanLCNF.Demo
meta import LeanQbe.T.LeanLCNF.Coverage
meta import LeanQbe.T.FlatLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# `LeanLCNF` Frontend Lowering Audit

Self-contained audit for the Lean 4 impure-LCNF (`LeanQbe.T.LeanLCNF`) frontend targeting
`LeanQbe.T`. Architecture-independent (imports neither `Kraken.X64` nor `Kraken.AArch64`).

## What This Workstream Proves
1. **Unconditional PHOAS well-formedness (`audit_tflat_wf`)**: every `TFlatFn` lowered by
   `LeanLCNF` and reified via `Frontend.C0.tflatFnsToFns` satisfies `Fn.Wf` (parametric PHOAS
   scoping/typing) unconditionally, making every lowered function admissible to the verified
   `LeanQbe.T` mid-end (`OptLemmas`), legalizer (`LegalLemmas`), and backend (`MainLemmas`).
2. **Real impure LCNF demo (`audit_lcnf_demo_wf`)**: all 80+ real Lean 4 declarations extracted
   from `LeanLCNF.Demo` (red-black trees with FBIP `isShared`/`oset` reuse, merge sort +
   closures, DPLL SAT solver, 6-parameter `UInt64` VM, boxed `USize` closures) plus
   synthesized `lcnf_apply_1..3` dispatchers satisfy `Fn.Wf` and `Func.checkTFlat`.

## Inputs / Assumptions
* `LeanLCNF.Demo.demoMod` is extracted at elaboration time by `lcnf_of_lean!` from real Lean 4
  definitions.
* `lowerModule` succeeds (checked by `#guard` below) and emits `TFlatFn` lists that reify
  cleanly to `LeanQbe.T.Fn`, C++20 (`PrintCpp`), and QBE SSA (`PrintQbe`).

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`) for all `Fn.Wf` proofs.
* **Important scope note**: semantic preservation of the `lcnf_of_lean!` meta extractor and of
  the `LeanLCNF` lowering passes themselves is currently validated by differential execution
  against Lean 4 (`test/lcnf/run.sh`) rather than by a Lean-level semantic refinement proof;
  only structural `Fn.Wf` + `Func.checkTFlat` + codegen invariants are formally proved here.
-/

set_option autoImplicit false

section

namespace LcnfAudit

open LeanQbe.T hiding TFlatFn
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0 (TFlatFn)

/-! ## 1. Formal `Fn.Wf` Theorems -/

/-- Lowered `TFlatFn` list for `Demo.lcnfProgram` (verified non-error by `#guard` below). -/
def demoTfs : List TFlatFn :=
  (lowerModule Demo.lcnfProgram).toOption.getD []

/-- Reified `LeanQbe.T.Fn` list for `Demo.lcnfProgram`. -/
def demoFns : List Fn :=
  Frontend.C0.tflatFnsToFns demoTfs

theorem audit_tflat_wf (tfs : List TFlatFn) :
    ∀ f ∈ Frontend.C0.tflatFnsToFns tfs, f.Wf :=
  Frontend.C0.tflatFnsToFns_wf tfs

theorem audit_lcnf_demo_wf :
    ∀ f ∈ demoFns, f.Wf :=
  Frontend.C0.tflatFnsToFns_wf demoTfs

/-- Lowered `TFlatFn` list for `Coverage.covProgram` (verified non-error by `#guard` below). -/
def covTfs : List TFlatFn :=
  (lowerModule Coverage.covProgram).toOption.getD []

/-- Reified `LeanQbe.T.Fn` list for `Coverage.covProgram`. -/
def covFns : List Fn :=
  Frontend.C0.tflatFnsToFns covTfs

theorem audit_lcnf_cov_wf :
    ∀ f ∈ covFns, f.Wf :=
  Frontend.C0.tflatFnsToFns_wf covTfs

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

/-! ## 3. Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_tflat_wf
#print axioms audit_lcnf_demo_wf
#print axioms audit_lcnf_cov_wf

end LcnfAudit
