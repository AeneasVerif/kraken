/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep7
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 7 (`FullFidelityAssemblyStep7`, `501` fns)

Step-7 C0 assembly (`501` fns, `0` externs, `0` exits) splicing the `22` Step-7 functions
(`FullFidelityStep7.fidStep7Repls` `20` + `FullFidelityStep7.fidStep7Befores` `2`:
`full_sort_bin_watches_fid`, `full_bva_upd_lit_fid`) onto Step 6 `fidModule` (`499` fns) via
`PatchModule.patchFns`.

Strictly Gate-1 (`0` `D-11` XOR, `0` `D-22` BCE, `0` `XorGauss`/`Prelearn`/`WaveACore`/`SbvaTie`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Step-7 `PatchModule` Splice (`fidModule` `499` -> `501` fns) -/

/-- Ordered `501`-fn Step-7 `KissatFidelity` function list
(`fidFns` + `FullFidelityStep7.fidStep7Repls` + `FullFidelityStep7.fidStep7Befores`). -/
def fidStep7Fns : List Fn :=
  patchFns FullFidelityStep7.fidStep7Repls FullFidelityStep7.fidStep7Befores fidFns

/-- Closed `501`-function Gate-1 Step-7 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep7Module : LeanQbe.T.Module :=
  { fidModule with fns := fidStep7Fns }

theorem fidStep7Fns_eq : fidStep7Module.fns = fidStep7Fns :=
  rfl

theorem fidStep7Fns_eq_step7 : fidStep7Fns = FullFidelityStep7.fidStep7ModuleFns :=
  rfl

theorem fidStep7Module_eq_step7 : fidStep7Module = FullFidelityStep7.fidStep7Module :=
  rfl

theorem fidStep7Module_wf : ∀ f ∈ fidStep7Module.fns, f.Wf :=
  patchFns_wf fidModule_wf FullFidelityStep7.fidStep7Repls_wf
    FullFidelityStep7.fidStep7Befores_wf

theorem fidStep7_noExit : fidStep7Module.exits = [] :=
  fid_noExit

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep7Fns.length == 501
#guard (fidStep7Fns.map Fn.name).eraseDups.length == 501
#guard fidStep7Module.checkAcyclic == true
#guard fidStep7Module.externs.isEmpty && fidStep7Module.exits.isEmpty
#guard (fidStep7Fns.map Fn.name).contains "full_sort_bin_watches_fid"
#guard (fidStep7Fns.map Fn.name).contains "full_bva_upd_lit_fid"
#guard !(fidStep7Fns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidStep7Fns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidStep7Fns.map Fn.name).contains "m8_log2_q16"
#guard !(fidStep7Fns.map Fn.name).contains "full_xor_gauss"
#guard !(fidStep7Fns.map Fn.name).contains "full_prelearn_m8"
#guard (PrintCpp.ppTModule fidStep7Module).isOk
#guard (PrintQbe.module fidStep7Module).isOk
#guard (PrintCpp.ppModule (FullFidelityStep7.fidStep7Fns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep7.fidStep7Fns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep7.fidStep7Fns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep7.fidStep7Fns.map (Fn.legal .x64AVX512))).isOk
#guard FullFidelityStep7.fidStep7Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard FullFidelityStep7.fidStep7Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard FullFidelityStep7.fidStep7Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard FullFidelityStep7.fidStep7Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7

end
