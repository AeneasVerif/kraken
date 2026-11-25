/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBase
public import LeanQbe.T.Examples.Kissat.FullFidelityBaseProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBaseProofBveVar
public import LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullFidelityBase
meta import LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Purified `FullFidelityBase`

1. Executable `#guard` checks on `fidBaseModule` (`469` fns, `0` externs, `0` exits, `0`
   beyond-upstream heuristics), flat `fidBaseSpecTable` (`469` rows, `noExit = true`, exact sig
   match), `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`,
   `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering all `5` purified leaf C0 `Func.wp` proofs
   (`D-11`, `D-22`, `D-19`, `D-01` vivify sort guard), closed unconditional `469/469`
   `fidBase_moduleOk` / `fidBase_tableImpl` / byte-level UNSAT soundness over flat
   `fidBaseEnv := Env.ofTable fidBaseSpecTable`, and genuine non-bailout concrete `Mem 64` UNSAT
   non-vacuity (`XPost := False`).
3. Single-line `<= 100`c `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityBaseTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen, Purification & Legalization Checks -/

private def fidBasePatchedFns : List Fn :=
  fidBaseRepls ++ m8MinHelpers ++ fidBveHelpers

#guard fidBaseFns.length == 469
#guard (fidBaseFns.map Fn.name).eraseDups.length == 469
#guard fidBaseRepls.length == 12
#guard fidBaseBefores.length == 2
#guard m8MinHelpers.length == 3
#guard fidBveHelpers.length == 17
#guard fidBaseModule.checkAcyclic == true
#guard fidBaseModule.externs.isEmpty == true
#guard fidBaseModule.exits.isEmpty == true
#guard !(fidBaseFns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidBaseFns.map Fn.name).contains "full_bve_bce_side_m8"
#guard (fidBaseFns.map Fn.name).contains "full_bve_gates_fid"
#guard (fidBaseFns.map Fn.name).contains "full_has_ternary"
#guard (fidBaseFns.map Fn.name).contains "full_bva_hop1"
#guard (fidBaseFns.map Fn.name).contains "full_bva_hop2"
#guard fidBaseSpecTable.length == 469
#guard fidBaseSpecTable.all SpecEntry.noExit == true
#guard fidBaseSpecTable.map (fun e => (e.name, e.as, e.rs)) == fidBaseModule.sigs
#guard (ppTModule fidBaseModule).isOk
#guard (PrintQbe.module fidBaseModule).isOk
#guard (ppModule (fidBasePatchedFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidBasePatchedFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidBasePatchedFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (fidBasePatchedFns.map (Fn.legal .x64AVX512))).isOk
#guard fidBasePatchedFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidBasePatchedFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidBasePatchedFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidBasePatchedFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem fb_repls_wf : ∀ r ∈ fidBaseRepls, r.Wf := fidBaseRepls_wf
theorem fb_bve_wf : ∀ h ∈ fidBveHelpers, h.Wf := fidBveHelpers_wf
theorem fb_fns_wf : ∀ f ∈ fidBaseFns, f.Wf := fidBaseFns_wf
theorem fb_names_nodup : (fidBaseFns.map Fn.name).Nodup := fidBaseFns_names_nodup
theorem fb_fns_len : fidBaseFns.length = 469 := fidBaseFns_length
theorem fb_tbl_sigs :
    fidBaseSpecTable.map (fun e => (e.name, e.as, e.rs)) = fidBaseFns.map Fn.sig :=
  fidBaseSpecTable_sigs
theorem fb_tbl_len : fidBaseSpecTable.length = 469 := fidBaseSpecTable_length
theorem fb_tbl_noExit : fidBaseSpecTable.all SpecEntry.noExit = true := fidBaseSpecTable_noExit
theorem fb_env_noExit :
    ∀ f as bs xs m Q X X', fidBaseEnv f as bs xs m Q X → fidBaseEnv f as bs xs m Q X' :=
  fidBaseEnv_noExit

theorem fb_gates_wp (Γ : Env)
    (hEquiv : ∀ a m Q X, m8BveFindEquivSpec a m Q X →
      Γ "full_bve_find_equiv_m8" [i64, i32, i32] [.bool] a m Q X)
    (hAnd : ∀ a m Q X, m8BveFindAndSpec a m Q X →
      Γ "full_bve_find_and_m8" [i64, i32, i32, i32] [.bool] a m Q X)
    (hIte : ∀ a m Q X, m8BveFindIteSpec a m Q X →
      Γ "full_bve_find_ite_m8" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefK6 : ∀ a m Q X, m8BveGatesSpec a m Q X →
      Γ "full_bve_def_k6_m8" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, m8BveGatesSpec a m Q X → Func.wp Γ full_bve_gates_fid_body a m Q X :=
  full_bve_gates_fid_wp Γ hEquiv hAnd hIte hDefK6

theorem fb_bve_var_m7_wp (Γ : Env)
    (hCol : ∀ a m Q X, fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m7" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGatesFid : ∀ a m Q X, m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X)
    (hGatesM7 : ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Γ "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlush : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X) :
    ∀ a m Q X, fullBveVarDefSpec a m Q X → Func.wp Γ full_bve_var_m7_fid_body a m Q X :=
  full_bve_var_m7_fid_wp Γ hCol hExtNeed hWeaken hInact hGatesFid hGatesM7 hResPair hDefrag
    hCommit hFlush

theorem fb_bve_var_wp (Γ : Env)
    (hM7 : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullBveVarDefSpec a m Q X → Func.wp Γ full_bve_var_fid_body a m Q X :=
  full_bve_var_fid_wp Γ hM7

theorem fb_vivify_tier_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Func.wp Γ full_vivify_tier_m6_hdr_fid_body a m Q X :=
  full_vivify_tier_m6_hdr_fid_wp Γ hBacktrack hCollect hCount hKeys hSortSched hVivClause hProp
    hClearTier

theorem fb_sweep_vars_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDP : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec)
    (hCol : M6EnvSpec Γ "full_m6_collect_cands" m6CollectCandsSpec)
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec) :
    ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp Γ full_m6_sweep_vars_fid_body args m Q X :=
  fid_sweep_vars_wp Γ hMaxV hDP hCol hSV

theorem fb_mod_ok : ModuleOk fidBaseEnv fidBaseModule := fidBase_moduleOk
theorem fb_tbl_impl : TableImpl fidBaseEnv fidBaseModule.fns fidBaseSpecTable :=
  fidBase_tableImpl

theorem fb_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidBaseEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidBase_solve_bytes_sound hcfit hwfit hm

theorem fb_solve_host
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  fidBase_solve_bytes_host_sound hpost hhost

theorem fb_unsat_nv :
    Func.wp fidBaseEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidBase_unsat_nv

theorem fb_nv_key_mid :
    Func.wp fidBaseEnv FullM8CoreParity.full_bve_var_key_m7_body
      (nvM8Cfg.hdr, 1#32, ()) nvM8KeyMidMem
      (fun (r, ()) m' =>
        r = ((1607100#64 <<< 32) ||| 0xFFFFFFFA#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyMidState m')
      (fun _ _ _ _ => False) :=
  nv_fid_bve_var_key_mid

theorem fb_nv_key_cap :
    Func.wp fidBaseEnv FullM8CoreParity.full_bve_var_key_m7_body
      (nvM8Cfg.hdr, 1#32, ()) nvM8KeyCapMem
      (fun (r, ()) m' =>
        r = ((8000#64 <<< 32) ||| 0xFFFFFFF8#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyCapState m')
      (fun _ _ _ _ => False) :=
  nv_fid_bve_var_key_cap

theorem fb_nv_dt_init :
    Func.wp fidBaseEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, true, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  nv_fid_probe_dticks_init

theorem fb_nv_dt_noninit :
    Func.wp fidBaseEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => ∃ ext' s',
        10000000 ≤ r.toNat ∧ s'.core = (nvM8DtState 25000000#64).core ∧
        s'.LengthsOk nvM8Cfg ∧ M6HdrScratchPres (nvM8DtState 25000000#64) s' ∧
        M6HdrExtOk ext' ∧ nvM8F0.Unsat ∧ FullM6HdrMem nvM8Cfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_probe_dticks_noninit

theorem fb_nv_dfs :
    Func.wp fidBaseEnv full_min_lit_dfs_m8_body (nvM8Cfg.hdr, 3#32, false, false, ())
      nvM8DfsMem0
      (fun (r, ()) m' =>
        r = true ∧ nvM8DfsStEnd.scratch.search_ticks = 1#64 ∧
        nvM8DfsStEnd.core.mrk = [0#8, 0#8, 2#8, 0#8] ∧ nvM8DfsStEnd.LengthsOk nvM8Cfg ∧
        FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur nvM8DfsStEnd.core ∧ nvM8F0.Unsat ∧
        FullMem nvM8Cfg nvM8DfsStEnd m')
      (fun _ _ _ _ => False) :=
  nv_fid_min_lit_dfs_large_bin_true

theorem fb_nv_shrink :
    Func.wp fidBaseEnv FullM8CoreParity.full_min_shrink_m6_body (nvM8Min18Cfg.hdr, ())
      nvM8Min18Mem
      (fun () m' => ∃ (F_cur : List (List Nat)) (s' : FullState),
        s'.LengthsOk nvM8Min18Cfg ∧ 1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ FullOtfsWitnessInv nvM8Min18Cfg nvM8F0 F_cur s'.core ∧
        nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_min_shrink_m6

theorem fb_nv_vivify :
    Func.wp fidBaseEnv full_vivify_tier_m6_hdr_fid_body (nvM8Min18Cfg.hdr, 0#64, 1#64, 100#64, ())
      nvVivMin18Mem
      (fun (r, ()) m' => ∃ s' : FullState,
        (r = 1#64 ∨ r = 20#64) ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        FullSparseInv nvM8Min18Cfg nvM8F0 s' ∧ nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_vivify_tier_sort_guard

end LeanQbeTest.T.KissatFidelityBaseTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev fidb_r_wf := @LeanQbeTest.T.KissatFidelityBaseTest.fb_repls_wf
abbrev fidb_b_wf := @LeanQbeTest.T.KissatFidelityBaseTest.fb_bve_wf
abbrev fidb_f_wf := @LeanQbeTest.T.KissatFidelityBaseTest.fb_fns_wf
abbrev fidb_nd := @LeanQbeTest.T.KissatFidelityBaseTest.fb_names_nodup
abbrev fidb_len := @LeanQbeTest.T.KissatFidelityBaseTest.fb_fns_len
abbrev fidb_tsigs := @LeanQbeTest.T.KissatFidelityBaseTest.fb_tbl_sigs
abbrev fidb_tlen := @LeanQbeTest.T.KissatFidelityBaseTest.fb_tbl_len
abbrev fidb_tnoex := @LeanQbeTest.T.KissatFidelityBaseTest.fb_tbl_noExit
abbrev fidb_noex := @LeanQbeTest.T.KissatFidelityBaseTest.fb_env_noExit
abbrev fidb_gates := @LeanQbeTest.T.KissatFidelityBaseTest.fb_gates_wp
abbrev fidb_bvm7 := @LeanQbeTest.T.KissatFidelityBaseTest.fb_bve_var_m7_wp
abbrev fidb_bv := @LeanQbeTest.T.KissatFidelityBaseTest.fb_bve_var_wp
abbrev fidb_viv := @LeanQbeTest.T.KissatFidelityBaseTest.fb_vivify_tier_wp
abbrev fidb_swv := @LeanQbeTest.T.KissatFidelityBaseTest.fb_sweep_vars_wp
abbrev fidb_ok := @LeanQbeTest.T.KissatFidelityBaseTest.fb_mod_ok
abbrev fidb_tbl := @LeanQbeTest.T.KissatFidelityBaseTest.fb_tbl_impl
abbrev fidb_sb := @LeanQbeTest.T.KissatFidelityBaseTest.fb_solve_sound
abbrev fidb_host := @LeanQbeTest.T.KissatFidelityBaseTest.fb_solve_host
abbrev fidb_nv := @LeanQbeTest.T.KissatFidelityBaseTest.fb_unsat_nv
abbrev fidb_nvk1 := @LeanQbeTest.T.KissatFidelityBaseTest.fb_nv_key_mid
abbrev fidb_nvk2 := @LeanQbeTest.T.KissatFidelityBaseTest.fb_nv_key_cap
abbrev fidb_nvdt1 := @LeanQbeTest.T.KissatFidelityBaseTest.fb_nv_dt_init
abbrev fidb_nvdt2 := @LeanQbeTest.T.KissatFidelityBaseTest.fb_nv_dt_noninit
abbrev fidb_nvdfs := @LeanQbeTest.T.KissatFidelityBaseTest.fb_nv_dfs
abbrev fidb_nvshr := @LeanQbeTest.T.KissatFidelityBaseTest.fb_nv_shrink
abbrev fidb_nvviv := @LeanQbeTest.T.KissatFidelityBaseTest.fb_nv_vivify

#print axioms fidb_r_wf
#print axioms fidb_b_wf
#print axioms fidb_f_wf
#print axioms fidb_nd
#print axioms fidb_len
#print axioms fidb_tsigs
#print axioms fidb_tlen
#print axioms fidb_tnoex
#print axioms fidb_noex
#print axioms fidb_gates
#print axioms fidb_bvm7
#print axioms fidb_bv
#print axioms fidb_viv
#print axioms fidb_swv
#print axioms fidb_ok
#print axioms fidb_tbl
#print axioms fidb_sb
#print axioms fidb_host
#print axioms fidb_nv
#print axioms fidb_nvk1
#print axioms fidb_nvk2
#print axioms fidb_nvdt1
#print axioms fidb_nvdt2
#print axioms fidb_nvdfs
#print axioms fidb_nvshr
#print axioms fidb_nvviv
