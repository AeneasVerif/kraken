/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBase
public import LeanQbe.T.Examples.Kissat.FullFidelitySweep
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityBase
meta import LeanQbe.T.Examples.Kissat.FullFidelitySweep
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 1 (`FullFidelityAssemblyStep1`)

Step-1 C0 assembly (`469` fns, `0` externs, `0` exits) composing purified
`FullFidelityBase.fidBaseModule` (`469` fns) + `FullFidelitySweep.fidSweepRepls` (`4` sweep.c
parity replacements, `0` new helpers) via `PatchModule.splice_module!`.

Strictly Gate-1 (`0` beyond-upstream heuristics: `0` `XorGauss`, `0` `Prelearn`, `0` `WaveACore`,
`0` `SbvaTie`, `0` `CadicalFx`, `0` `D-11`/`D-22`). Subsequent layers (`BcpHotPush[Mem]`, `Bve`,
`Cong`, `VivK6`, `Bva`) stack directly on top of `fidStep1Module` via `PatchModule.PatchBundle`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Step-1 `PatchModule` Splice (`fidBaseModule` + `fidSweepRepls` = `469` fns) -/

/-- Ordered `469`-fn Step-1 function list (`FullFidelityBase.fidBaseFns` + `fidSweepRepls`). -/
def fidStep1Fns : List Fn :=
  patchFns fidSweepRepls [] FullFidelityBase.fidBaseFns

/-- Closed `469`-function Step-1 module (`0` externs, `0` exits). -/
def fidStep1Module : LeanQbe.T.Module :=
  { FullFidelityBase.fidBaseModule with fns := fidStep1Fns }

theorem fidStep1Fns_eq : fidStep1Module.fns = fidStep1Fns :=
  rfl

theorem fidStep1Module_wf : ∀ f ∈ fidStep1Module.fns, f.Wf := by
  refine patchFns_wf FullFidelityBase.fidBaseFns_wf FullFidelitySweep.fidSweepRepls_wf ?_
  intro f hf
  simp at hf

theorem fidStep1_noExit : fidStep1Module.exits = [] :=
  FullFidelityBase.fidBase_noExit

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep1Fns.length == 469
#guard (fidStep1Fns.map Fn.name).eraseDups.length == 469
#guard fidStep1Module.checkAcyclic == true
#guard fidStep1Module.externs.isEmpty && fidStep1Module.exits.isEmpty
#guard !(fidStep1Fns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidStep1Fns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidStep1Fns.map Fn.name).contains "m8_log2_q16"
#guard !(fidStep1Fns.map Fn.name).contains "full_xor_gauss"
#guard !(fidStep1Fns.map Fn.name).contains "full_prelearn_m8"
#guard (fidStep1Fns.map Fn.name).contains "full_bve_gates_fid"
#guard (fidStep1Fns.map Fn.name).contains "full_has_ternary"
#guard (fidStep1Fns.map Fn.name).contains "full_bva_hop1"
#guard (fidStep1Fns.map Fn.name).contains "full_bva_hop2"
#guard (fidStep1Fns.map Fn.name).contains "full_m6_sweep_vars"
#guard (PrintCpp.ppTModule fidStep1Module).isOk
#guard (PrintQbe.module fidStep1Module).isOk
#guard (PrintCpp.ppModule (fidSweepRepls.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidSweepRepls.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidSweepRepls.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidSweepRepls.map (Fn.legal .x64AVX512))).isOk
#guard fidSweepRepls.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidSweepRepls.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidSweepRepls.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidSweepRepls.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1

end
