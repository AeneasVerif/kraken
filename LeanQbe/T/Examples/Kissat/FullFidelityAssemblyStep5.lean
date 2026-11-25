/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
public import LeanQbe.T.Examples.Kissat.FullFidelityBve
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
meta import LeanQbe.T.Examples.Kissat.FullFidelityBve
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 5 (`FullFidelityAssemblyStep5`)

Step-5 C0 assembly (`492` fns, `0` externs, `0` exits) layering `FullFidelityBve`'s pure dynamic
K6 + unit-certification BVE parity patch onto `fidStep4Module` (`478` fns):
- **`fidStep5NewHelpers` (`14` fns):** `(FullFidelityBve.fidBveHelpers.drop 5).take 14` (`+14` new
  helpers inserted immediately before `"full_bve_gates_fid"` for strict topological DAG order,
  omitting the `5` `m8BveFind*` helpers already present in `fidBaseModule`).
- **`fidStep5Repls` (`6` fns):** `fidBveRepls ++ [FullFidelityBve.fidBveGatesFn]` replacing
  `full_bve_gates_fid`, `full_bve_var_m7`, `full_bve_var`, `full_bve_var_key_m7`,
  `full_elim_bve_m7`, and `full_eliminate_m6`.

Strictly Gate-1 (`0` `D-11` XOR, `0` `D-22` BCE, `0` beyond-upstream heuristics).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Step-5 `PatchModule` Splice (`fidStep4Module` + `Bve` = `492` fns) -/

/-- `14` new pure dynamic-K6 / unit-certification BVE helpers not already in `fidStep4Fns`. -/
def fidStep5NewHelpers : List Fn :=
  (FullFidelityBve.fidBveHelpers.drop 5).take 14

/-- `6` canonical BVE replacement functions (`fidBveRepls ++ [FullFidelityBve.fidBveGatesFn]`). -/
def fidStep5Repls : List Fn :=
  fidBveRepls ++ [FullFidelityBve.fidBveGatesFn]

/-- Insertion plan placing the `14` new BVE helpers immediately before `"full_bve_gates_fid"`. -/
def fidStep5Befores : List (Sym × List Fn) :=
  [ ("full_bve_gates_fid", fidStep5NewHelpers) ]

/-- Ordered `492`-fn Step-5 function list (`fidStep4Fns` + `fidStep5Repls` + `fidStep5Befores`). -/
def fidStep5Fns : List Fn :=
  patchFns fidStep5Repls fidStep5Befores fidStep4Fns

/-- Closed `492`-function Step-5 module (`0` externs, `0` exits). -/
def fidStep5Module : LeanQbe.T.Module :=
  { fidStep4Module with fns := fidStep5Fns }

theorem fidStep5Fns_eq : fidStep5Module.fns = fidStep5Fns :=
  rfl

theorem fidStep5NewHelpers_wf : ∀ h ∈ fidStep5NewHelpers, h.Wf := by
  intro h hh
  exact fidBveHelpers_wf h (List.mem_of_mem_drop (List.mem_of_mem_take hh))

theorem fidStep5Repls_wf : ∀ r ∈ fidStep5Repls, r.Wf := by
  intro r hr
  rcases List.mem_append.mp hr with hr1 | hr2
  · exact fidBveRepls_wf r hr1
  · rcases List.mem_singleton.mp hr2 with rfl
    exact FullFidelityBve.full_bve_gates_fid_wf

theorem fidStep5Befores_wf : ∀ h ∈ fidStep5Befores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep5Befores, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hh
  exact fidStep5NewHelpers_wf h hh

theorem fidStep5Module_wf : ∀ f ∈ fidStep5Module.fns, f.Wf :=
  patchFns_wf fidStep4Module_wf fidStep5Repls_wf fidStep5Befores_wf

theorem fidStep5_noExit : fidStep5Module.exits = [] :=
  fidStep4_noExit

/-- All `20` functions added or replaced in Step 5 (`14` helpers + `6` replacements). -/
def fidStep5NewFns : List Fn :=
  fidStep5NewHelpers ++ fidStep5Repls

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep5NewHelpers.length == 14
#guard fidStep5Repls.length == 6
#guard fidStep5Fns.length == 492
#guard (fidStep5Fns.map Fn.name).eraseDups.length == 492
#guard fidStep5Module.checkAcyclic == true
#guard fidStep5Module.externs.isEmpty && fidStep5Module.exits.isEmpty
#guard !(fidStep5Fns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidStep5Fns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidStep5Fns.map Fn.name).contains "m8_log2_q16"
#guard !(fidStep5Fns.map Fn.name).contains "full_xor_gauss"
#guard !(fidStep5Fns.map Fn.name).contains "full_prelearn_m8"
#guard (fidStep5Fns.map Fn.name).contains "full_bve_k6_mv_fid"
#guard (fidStep5Fns.map Fn.name).contains "full_bve_certify_unit_fid"
#guard (fidStep5Fns.map Fn.name).contains "full_bve_def_k6_fid"
#guard (fidStep5Fns.map Fn.name).contains "full_bve_gates_fid"
#guard (fidStep5Fns.map Fn.name).contains "full_elim_bve_m7"
#guard (fidStep5Fns.map Fn.name).contains "full_eliminate_m6"
#guard (PrintCpp.ppTModule fidStep5Module).isOk
#guard (PrintQbe.module fidStep5Module).isOk
#guard (PrintCpp.ppModule (fidStep5NewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep5NewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep5NewFns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep5NewFns.map (Fn.legal .x64AVX512))).isOk
#guard fidStep5NewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidStep5NewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidStep5NewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidStep5NewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5

end
