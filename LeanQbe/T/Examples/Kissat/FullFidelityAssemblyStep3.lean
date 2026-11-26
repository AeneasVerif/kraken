/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
public import LeanQbe.T.Examples.Kissat.FullFidelityCong
public import LeanQbe.T.Examples.Kissat.FullFidelityTiers
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
meta import LeanQbe.T.Examples.Kissat.FullFidelityCong
meta import LeanQbe.T.Examples.Kissat.FullFidelityTiers
meta import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 3 (`FullFidelityAssemblyStep3`)

Step-3 C0 assembly (`474` fns, `0` externs, `0` exits) layering both landed parity slices:
- `FullFidelityCong.fidCongRepls` (`19` replacements) + `fidCongBefores` (`3` inserted helpers:
  `full_cong_emit_xor4`, `full_cong_sift_pairs_fid`, `full_cong_sort_pairs_fid`), and
- `FullFidelityTiers.fidTiersRepls` (`2` replacements: `m6_hdr_sync_legacy_tiers`,
  `full_analyze_rsn_m6_hdr`)
atop `fidStep2Module` (`471` fns) via `PatchModule.patchFns`, preserving unified `FullMem`.
Strictly Gate-1 (`0` beyond-upstream heuristics).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open LeanQbe.T.Examples.Kissat.FullFidelityTiers
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Step-3 `PatchModule` Splice (`fidStep2Module` + `Cong` + `Tiers` = `474` fns) -/

/-- Combined `21`-function replacement list (`fidCongRepls` `19` + `fidTiersRepls` `2`). -/
def fidStep3Repls : List Fn :=
  fidCongRepls ++ fidTiersRepls

/-- Ordered `474`-fn Step-3 function list (`fidStep2Fns` + `fidCong` + `fidTiers`). -/
def fidStep3Fns : List Fn :=
  patchFns fidStep3Repls fidCongBefores fidStep2Fns

/-- Closed `474`-function Step-3 module (`0` externs, `0` exits). -/
def fidStep3Module : LeanQbe.T.Module :=
  { fidStep2Module with fns := fidStep3Fns }

theorem fidStep3Fns_eq : fidStep3Module.fns = fidStep3Fns :=
  rfl

theorem fidStep3Repls_wf : ∀ f ∈ fidStep3Repls, f.Wf := fun f hf => by
  rcases List.mem_append.mp hf with hc | ht
  · exact fidCongRepls_wf f hc
  · exact fidTiersRepls_wf f ht

theorem fidStep3Module_wf : ∀ f ∈ fidStep3Module.fns, f.Wf :=
  patchFns_wf fidStep2Module_wf fidStep3Repls_wf fidCongBefores_wf

theorem fidStep3_noExit : fidStep3Module.exits = [] :=
  fidStep2_noExit

/-- All `24` functions added or replaced in Step 3 (`21` replacements + `3` helpers). -/
def fidStep3NewFns : List Fn :=
  fidStep3Repls ++ [fidCongEmitXor4Fn, fidCongSiftPairsFn, fidCongSortPairsFn]

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep3Fns.length == 474
#guard (fidStep3Fns.map Fn.name).eraseDups.length == 474
#guard fidStep3Module.checkAcyclic == true
#guard fidStep3Module.externs.isEmpty && fidStep3Module.exits.isEmpty
#guard !(fidStep3Fns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidStep3Fns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidStep3Fns.map Fn.name).contains "m8_log2_q16"
#guard !(fidStep3Fns.map Fn.name).contains "full_xor_gauss"
#guard !(fidStep3Fns.map Fn.name).contains "full_prelearn_m8"
#guard (fidStep3Fns.map Fn.name).contains "full_cong_emit_xor4"
#guard (fidStep3Fns.map Fn.name).contains "full_cong_sift_pairs_fid"
#guard (fidStep3Fns.map Fn.name).contains "full_cong_sort_pairs_fid"
#guard (fidStep3Fns.map Fn.name).contains "full_congruence_dense"
#guard (fidStep3Fns.map Fn.name).contains "m6_hdr_sync_legacy_tiers"
#guard (fidStep3Fns.map Fn.name).contains "full_analyze_rsn_m6_hdr"

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3

end
