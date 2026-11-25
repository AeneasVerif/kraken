/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
meta import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 4 (`FullFidelityAssemblyStep4`)

Step-4 C0 assembly (`478` fns, `0` externs, `0` exits) layering `FullFidelityVivK6`'s
`fidVivK6Repls` (`6` replacements: `full_unwatch_large`, `full_vivify_tier_m6_hdr`,
`full_vivify_m6_hdr`, `full_k6_propagate`, `full_k6_core_m8`, `full_bva_commit`) +
`fidVivK6Befores` (`4` inserted dynamic-vivification helpers: `full_viv_collect_fid`,
`full_viv_count_fid`, `full_viv_sort2_fid`, `full_viv_sort_fid`) onto `fidStep3Module`
(`474` fns) via `PatchModule.patchFns`, preserving unified `FullMem`.
Strictly Gate-1 (`0` beyond-upstream heuristics).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Step-4 `PatchModule` Splice (`fidStep3Module` + `VivK6` = `478` fns) -/

/-- Ordered `478`-fn Step-4 function list (`fidStep3Fns` + `fidVivK6Repls` + `fidVivK6Befores`). -/
def fidStep4Fns : List Fn :=
  patchFns fidVivK6Repls fidVivK6Befores fidStep3Fns

/-- Closed `478`-function Step-4 module (`0` externs, `0` exits). -/
def fidStep4Module : LeanQbe.T.Module :=
  { fidStep3Module with fns := fidStep4Fns }

theorem fidStep4Fns_eq : fidStep4Module.fns = fidStep4Fns :=
  rfl

theorem fidStep4Module_wf : ∀ f ∈ fidStep4Module.fns, f.Wf :=
  patchFns_wf fidStep3Module_wf fidVivK6Repls_wf fidVivK6Befores_wf

theorem fidStep4_noExit : fidStep4Module.exits = [] :=
  fidStep3_noExit

/-- All `10` functions added or replaced in Step 4 (`6` replacements + `4` helpers). -/
def fidStep4NewFns : List Fn :=
  fidVivK6Fns

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep4Fns.length == 478
#guard (fidStep4Fns.map Fn.name).eraseDups.length == 478
#guard fidStep4Module.checkAcyclic == true
#guard fidStep4Module.externs.isEmpty && fidStep4Module.exits.isEmpty
#guard !(fidStep4Fns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidStep4Fns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidStep4Fns.map Fn.name).contains "m8_log2_q16"
#guard !(fidStep4Fns.map Fn.name).contains "full_xor_gauss"
#guard !(fidStep4Fns.map Fn.name).contains "full_prelearn_m8"
#guard (fidStep4Fns.map Fn.name).contains "full_viv_collect_fid"
#guard (fidStep4Fns.map Fn.name).contains "full_viv_count_fid"
#guard (fidStep4Fns.map Fn.name).contains "full_viv_sort2_fid"
#guard (fidStep4Fns.map Fn.name).contains "full_viv_sort_fid"
#guard (fidStep4Fns.map Fn.name).contains "full_unwatch_large"
#guard (fidStep4Fns.map Fn.name).contains "full_vivify_tier_m6_hdr"
#guard (fidStep4Fns.map Fn.name).contains "full_vivify_m6_hdr"
#guard (fidStep4Fns.map Fn.name).contains "full_k6_propagate"
#guard (fidStep4Fns.map Fn.name).contains "full_k6_core_m8"
#guard (fidStep4Fns.map Fn.name).contains "full_bva_commit"
#guard (PrintCpp.ppTModule fidStep4Module).isOk
#guard (PrintQbe.module fidStep4Module).isOk
#guard (PrintCpp.ppModule (fidStep4NewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep4NewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep4NewFns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep4NewFns.map (Fn.legal .x64AVX512))).isOk
#guard fidStep4NewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidStep4NewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidStep4NewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidStep4NewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4

end
