/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Kissat.Src.InlPolicy
import LeanQbe.T.Examples.Kissat.Build.Common.CertParamCommon
import LeanQbe.T.FlatLemmas

/-!
# Leaf Guard & Axiom Audit for `Src.InlPolicy` and `Build.Common.CertParamCommon`

Verifies:
1. `Src.InlPolicy` parity guards (`418` live fns in `Src.Full.kissatFns`, `154` live PGO
   overrides, Step-13 `OPT-9` Arm B + Tier A/B budgets, `singleSiteMax = 0` on
   `kissatInlChunkPolicy`, and `<= std3` axioms).
2. `#print axioms` on every public theorem in `Build.Common.CertParamCommon` (`<= std3`,
   `0` unsafe, `0` legacy `Full*`/`PatchModule`/`Solver` imports in transitive closure).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.KissatBuildCommonTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Full
open LeanQbe.T.Examples.Kissat.Src.InlPolicy
open LeanQbe.T.Examples.Kissat.Build.Common.CertParamCommon

-- `Src.InlPolicy` configuration & Step-13 OPT-9 Arm B + Tier A/B sanity guards
example : kissatModule.fns.length = 418 := by t_kernel_rfl
example : kissatPgoOverrides.length = 154 := rfl
example : kissatInlPolicy.leafMax = 165 := rfl
example : kissatInlPolicy.singleSiteMax = 0 := rfl
example : kissatInlPolicy.maxCallerSize = 2800 := rfl
example : kissatInlPolicy.maxCalleeCalls = 2 := rfl
example : kissatInlPolicy.maxCalleeLoops = some 1 := rfl
example : kissatInlPolicy.maxTotalDup = 1500 := rfl
example : kissatInlPolicy.requireLoopSite = false := rfl
example : kissatInlPolicy.maxCallerCalls = 24 := rfl
example : kissatInlPolicy.keepOutOfLine =
  [ "full_add_unit", "m6_hdr_init", "full_watch_push_slow_m6"
  , "full_prop_flush_slow_fid", "full_prop_flush_del_fid", "full_k6_init" ] := rfl
example : kissatInlChunkPolicy.singleSiteMax = 0 := rfl
example : kissatInlChunkPolicy.maxTotalDup = 0 := rfl
example : kissatInlChunkPolicy.requireLoopSite = false := rfl

-- Step-13 Tier A, Tier B, and OPT-9 Arm B spot checks
example : kissatPgoBudget "full_analyze_rsn_m6_hdr" = 480 := rfl
example : kissatPgoBudget "f64u_round_pack" = 240 := rfl
example : kissatPgoBudget "full_fwd_scan_lit_m7" = 260 := rfl
example : kissatPgoBudget "full_save_target_best" = 95 := rfl
example : kissatPgoBudget "full_add_unit" = 0 := rfl
example : kissatPgoBudget "m6_hdr_init" = 0 := rfl
example : kissatPgoBudget "full_k6_init" = 0 := rfl
example : kissatPgoBudget "unlisted_cold_fn" = 15 := rfl

-- `Src.InlPolicy` public guard theorems
abbrev ax_inl_overrides_live := @kissatPgoOverrides_live
abbrev ax_inl_overrides_nodup := @kissatPgoOverrides_nodup
abbrev ax_inl_budget_eq := @kissatPgoBudget_eq_of_mem
abbrev ax_inl_ne_default_live := @kissatPgoBudget_ne_default_live
abbrev ax_inl_kool_live := @kissatInlPolicy_keepOutOfLine_live
abbrev ax_inl_kool_zero := @kissatInlPolicy_keepOutOfLine_zero
abbrev ax_inl_chunk_singleSite := @kissatInlChunkPolicy_singleSiteMax
abbrev ax_inl_chunk_maxDup := @kissatInlChunkPolicy_maxTotalDup
abbrev ax_inl_chunk_reqLoop := @kissatInlChunkPolicy_requireLoopSite
abbrev ax_inl_chunk_parity := @kissatInlChunkPolicy_parity

-- `Build.Common.CertParamCommon` public theorems (`FnSpec`-level)
abbrev ax_solve_fnspec := @solve_bytes_unsat_of_fnspec
abbrev ax_correct_fnspec := @unsat_correct_of_fnspec
abbrev ax_nv_fnspec := @unsat_nonvacuous_of_fnspec
abbrev ax_run_fnspec := @run_unsat_of_fnspec

-- `Build.Common.CertParamCommon` generic `M'` / `LinkedCert` / `compileModule` theorems
abbrev ax_mod_fnspec_cert_ok := @module_fnspec_of_cert_moduleOk
abbrev ax_mod_fnspec_maxB_cert_ok := @module_fnspec_maxB_of_cert_moduleOk
abbrev ax_entry_cert_ok := @entryFn_spec_of_cert_moduleOk
abbrev ax_mod_fnspec_compile_mod := @module_fnspec_of_compile_mod
abbrev ax_mod_fnspec_maxB_compile_mod := @module_fnspec_maxB_of_compile_mod
abbrev ax_entry_compile_mod := @entryFn_spec_of_compile_mod
abbrev ax_solve_entry_cert := @solve_bytes_unsat_entry_of_cert
abbrev ax_correct_entry_cert := @unsat_correct_entry_of_cert
abbrev ax_nv_entry_cert := @unsat_nonvacuous_entry_of_cert
abbrev ax_run_entry_cert := @run_unsat_entry_of_cert
abbrev ax_solve_maxB_cert := @solve_bytes_unsat_maxB_of_cert
abbrev ax_correct_maxB_cert := @unsat_correct_maxB_of_cert
abbrev ax_nv_maxB_cert := @unsat_nonvacuous_maxB_of_cert
abbrev ax_run_maxB_cert := @run_unsat_maxB_of_cert

-- `Build.Common.CertParamCommon` `optInlinePolicy` specializations
abbrev ax_mod_fnspec_abi := @module_fnspec_of_abi
abbrev ax_mod_fnspec_maxB_abi := @module_fnspec_maxB_of_abi
abbrev ax_mod_fnspec_compile := @module_fnspec_of_compile
abbrev ax_mod_fnspec_maxB_compile := @module_fnspec_of_compile_maxB
abbrev ax_solve_abi := @solve_bytes_unsat_of_abi
abbrev ax_correct_abi := @unsat_correct_of_abi
abbrev ax_nv_abi := @unsat_nonvacuous_of_abi
abbrev ax_run_abi := @run_unsat_of_abi
abbrev ax_solve_entry_abi := @solve_bytes_unsat_entry_of_abi
abbrev ax_correct_entry_abi := @unsat_correct_entry_of_abi
abbrev ax_nv_entry_abi := @unsat_nonvacuous_entry_of_abi
abbrev ax_run_entry_abi := @run_unsat_entry_of_abi
abbrev ax_solve_maxB_abi := @solve_bytes_unsat_maxB_of_abi
abbrev ax_correct_maxB_abi := @unsat_correct_maxB_of_abi
abbrev ax_nv_maxB_abi := @unsat_nonvacuous_maxB_of_abi
abbrev ax_run_maxB_abi := @run_unsat_maxB_of_abi
abbrev ax_solve_compile_mod := @solve_bytes_unsat_of_compile_mod
abbrev ax_correct_compile_mod := @unsat_correct_of_compile_mod
abbrev ax_nv_compile_mod := @unsat_nonvacuous_of_compile_mod
abbrev ax_solve_compile_mod_maxB := @solve_bytes_unsat_of_compile_mod_maxB
abbrev ax_correct_compile_mod_maxB := @unsat_correct_of_compile_mod_maxB
abbrev ax_nv_compile_mod_maxB := @unsat_nonvacuous_of_compile_mod_maxB
abbrev ax_run_compile_mod_maxB := @run_unsat_of_compile_mod_maxB
abbrev ax_solve_compile := @solve_bytes_unsat_of_compile
abbrev ax_correct_compile := @unsat_correct_of_compile
abbrev ax_nv_compile := @unsat_nonvacuous_of_compile
abbrev ax_solve_compile_maxB := @solve_bytes_unsat_of_compile_maxB
abbrev ax_correct_compile_maxB := @unsat_correct_of_compile_maxB
abbrev ax_nv_compile_maxB := @unsat_nonvacuous_of_compile_maxB
abbrev ax_run_compile_maxB := @run_unsat_of_compile_maxB

#print axioms ax_inl_overrides_live
#print axioms ax_inl_overrides_nodup
#print axioms ax_inl_budget_eq
#print axioms ax_inl_ne_default_live
#print axioms ax_inl_kool_live
#print axioms ax_inl_kool_zero
#print axioms ax_inl_chunk_singleSite
#print axioms ax_inl_chunk_maxDup
#print axioms ax_inl_chunk_reqLoop
#print axioms ax_inl_chunk_parity
#print axioms ax_solve_fnspec
#print axioms ax_correct_fnspec
#print axioms ax_nv_fnspec
#print axioms ax_run_fnspec
#print axioms ax_mod_fnspec_cert_ok
#print axioms ax_mod_fnspec_maxB_cert_ok
#print axioms ax_entry_cert_ok
#print axioms ax_mod_fnspec_compile_mod
#print axioms ax_mod_fnspec_maxB_compile_mod
#print axioms ax_entry_compile_mod
#print axioms ax_solve_entry_cert
#print axioms ax_correct_entry_cert
#print axioms ax_nv_entry_cert
#print axioms ax_run_entry_cert
#print axioms ax_solve_maxB_cert
#print axioms ax_correct_maxB_cert
#print axioms ax_nv_maxB_cert
#print axioms ax_run_maxB_cert
#print axioms ax_mod_fnspec_abi
#print axioms ax_mod_fnspec_maxB_abi
#print axioms ax_mod_fnspec_compile
#print axioms ax_mod_fnspec_maxB_compile
#print axioms ax_solve_abi
#print axioms ax_correct_abi
#print axioms ax_nv_abi
#print axioms ax_run_abi
#print axioms ax_solve_entry_abi
#print axioms ax_correct_entry_abi
#print axioms ax_nv_entry_abi
#print axioms ax_run_entry_abi
#print axioms ax_solve_maxB_abi
#print axioms ax_correct_maxB_abi
#print axioms ax_nv_maxB_abi
#print axioms ax_run_maxB_abi
#print axioms ax_solve_compile_mod
#print axioms ax_correct_compile_mod
#print axioms ax_nv_compile_mod
#print axioms ax_solve_compile_mod_maxB
#print axioms ax_correct_compile_mod_maxB
#print axioms ax_nv_compile_mod_maxB
#print axioms ax_run_compile_mod_maxB
#print axioms ax_solve_compile
#print axioms ax_correct_compile
#print axioms ax_nv_compile
#print axioms ax_solve_compile_maxB
#print axioms ax_correct_compile_maxB
#print axioms ax_nv_compile_maxB
#print axioms ax_run_compile_maxB

end LeanQbeTest.T.KissatBuildCommonTest
