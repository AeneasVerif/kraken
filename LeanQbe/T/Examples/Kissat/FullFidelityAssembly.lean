/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
public import LeanQbe.T.Examples.Kissat.FullFidelityBva
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
meta import LeanQbe.T.Examples.Kissat.FullFidelityBva
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Assembly (`FullFidelityAssembly`, `499` fns)

Final Gate-1 `KissatFidelity` C0 assembly (`499` fns, `0` externs, `0` exits) layering
`FullFidelityBva`'s `fidBvaRepls` (`7` replacements: `full_bva_scan_cands`, `full_bva_pick_cand`,
`full_bva_filter_row`, `full_bva_commit`, `full_bva_try_lit`, `full_factor`, `full_probe_m6`) +
`fidBvaBefores` (`7` dynamic-matrix/FHeap helpers before `"full_bva_scan_cands"`) onto
`fidStep5Module` (`492` fns) via `PatchModule.patchFns`:
- Full composition stack (`6` layers): `FullFidelityBase` (`469` fns) -> `FullFidelitySweep` ->
  `FullFidelityStep2S15` (`BcpHotPush` + `CoreParity` + `Sweep`, `471` fns) ->
  `FullFidelityCong` + `FullFidelityTiers` (`474` fns) -> `FullFidelityVivK6` (`478` fns) ->
  `FullFidelityBve` (`492` fns) -> `FullFidelityBva` (`499` fns).
- Strictly Gate-1 (`0` `D-11` XOR, `0` `D-22` BCE, `0` `XorGauss`/`Prelearn`/`WaveACore`/`SbvaTie`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssembly

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Canonical Gate-1 `PatchModule` Splice (`fidStep5Module` + `Bva` = `499` fns) -/

/-- Ordered `499`-fn canonical Gate-1 `KissatFidelity` function list
(`fidStep5Fns` + `fidBvaRepls` + `fidBvaBefores`). -/
def fidFns : List Fn :=
  patchFns fidBvaRepls fidBvaBefores fidStep5Fns

/-- Closed `499`-function Gate-1 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidModule : LeanQbe.T.Module :=
  { fidStep5Module with fns := fidFns }

theorem fidFns_eq : fidModule.fns = fidFns :=
  rfl

theorem fidBvaBefores_wf : ∀ h ∈ fidBvaBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidBvaBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hh
  exact fidBvaHelpers_wf h hh

theorem fidModule_wf : ∀ f ∈ fidModule.fns, f.Wf :=
  patchFns_wf fidStep5Module_wf fidBvaRepls_wf fidBvaBefores_wf

theorem fid_noExit : fidModule.exits = [] :=
  fidStep5_noExit

/-- All `14` functions added or replaced in Step 6 (`7` helpers + `7` replacements). -/
def fidNewFns : List Fn :=
  fidBvaHelpers ++ fidBvaRepls

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidFns.length == 499
#guard (fidFns.map Fn.name).eraseDups.length == 499
#guard fidModule.checkAcyclic == true
#guard fidModule.externs.isEmpty && fidModule.exits.isEmpty
#guard !(fidFns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidFns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidFns.map Fn.name).contains "m8_log2_q16"
#guard !(fidFns.map Fn.name).contains "full_xor_gauss"
#guard !(fidFns.map Fn.name).contains "full_prelearn_m8"
#guard (fidFns.map Fn.name).contains "full_bva_steps_cap_fid"
#guard (fidFns.map Fn.name).contains "full_bva_connect_clauses_fid"
#guard (fidFns.map Fn.name).contains "full_bva_scan_cands"
#guard (fidFns.map Fn.name).contains "full_bva_commit"
#guard (fidFns.map Fn.name).contains "full_bva_try_lit"
#guard (fidFns.map Fn.name).contains "full_factor"
#guard (fidFns.map Fn.name).contains "full_probe_m6"
#guard (PrintCpp.ppTModule fidModule).isOk
#guard (PrintQbe.module fidModule).isOk
#guard (PrintCpp.ppModule (fidNewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidNewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidNewFns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidNewFns.map (Fn.legal .x64AVX512))).isOk
#guard fidNewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidNewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidNewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidNewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

end LeanQbe.T.Examples.Kissat.FullFidelityAssembly

end
