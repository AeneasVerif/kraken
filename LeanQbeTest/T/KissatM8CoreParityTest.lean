/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofNv
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM8CoreParity
meta import LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
meta import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
meta import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofNv
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M8 `FullM8CoreParity`

1. Executable `#guard` checks on `m8CoreParityModule` (`435` fns, `0` externs, `0` exits),
   `m8CoreParitySpecTable` (`435` rows, `noExit = true`), `m8CoreParityHotModule` (`435` fns),
   `m8HotHop1BridgeModule` (`13` fns), `m8SweepV2CoreParityModule` (`471` fns, `noExit = true`),
   `nvM8DtModule` (`3` fns), `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`,
   `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering Rank `#4` (`probe`), Rank `#5` (`shrink`),
   `analyze` bridges, closed unconditional `m8CoreParity_moduleOk` / `TableImpl` / UNSAT
   soundness, all three `PatchModule` splice bridges (`HotTernary`, `HotHop1`, `FullM8SweepV2`),
   and genuine non-vacuous concrete `Mem 64` UNSAT NV theorems (`XPost := False`).
3. Single-line `<= 100`c `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM8CoreParityTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

private def m8PatchedFns : List Fn := m8CoreParityRepls ++ m8MinHelpers ++ m8BveHelpers

#guard m8CoreParityFns.length == 435
#guard (m8CoreParityFns.map Fn.name).eraseDups.length == 435
#guard m8CoreParityRepls.length == 7
#guard m8CoreParityBefores.length == 2
#guard m8MinHelpers.length == 3
#guard m8BveHelpers.length == 19
#guard m8CoreParityModule.checkAcyclic == true
#guard m8CoreParityModule.externs.isEmpty == true
#guard m8CoreParityModule.exits.isEmpty == true
#guard m8CoreParitySpecTable.length == 435
#guard m8CoreParitySpecTable.all SpecEntry.noExit == true
#guard m8CoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) == m8CoreParityModule.sigs
#guard m8CoreParityHotModule.checkAcyclic == true
#guard m8CoreParityHotFns.length == 435
#guard m8HotHop1BridgeModule.checkAcyclic == true
#guard m8HotHop1BridgeFns.length == 13
#guard m8SweepV2CoreParityModule.checkAcyclic == true
#guard m8SweepV2CoreParityFns.length == 471
#guard m8SweepV2CoreParitySpecTable.length == 471
#guard m8SweepV2CoreParitySpecTable.all SpecEntry.noExit == true
#guard m8SweepV2CoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) ==
    m8SweepV2CoreParityModule.sigs
#guard nvM8DtModule.checkAcyclic == true
#guard nvM8DtModule.fns.length == 3
#guard (ppTModule m8CoreParityModule).isOk
#guard (PrintQbe.module m8CoreParityModule).isOk
#guard (ppTModule m8SweepV2CoreParityModule).isOk
#guard (ppModule (m8PatchedFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m8PatchedFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m8PatchedFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (m8PatchedFns.map (Fn.legal .x64AVX512))).isOk
#guard m8PatchedFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m8PatchedFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m8PatchedFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard m8PatchedFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem cp_repls_wf : ∀ r ∈ m8CoreParityRepls, r.Wf := m8CoreParityRepls_wf
theorem cp_befores_wf : ∀ p ∈ m8CoreParityBefores, ∀ h ∈ p.2, h.Wf := m8CoreParityBefores_wf
theorem cp_fns_wf : ∀ f ∈ m8CoreParityFns, f.Wf := m8CoreParityFns_wf
theorem cp_names_nodup : (m8CoreParityFns.map Fn.name).Nodup := m8CoreParityFns_names_nodup
theorem cp_acyclic : m8CoreParityModule.checkAcyclic = true := m8CoreParity_acyclic
theorem cp_tbl_len : m8CoreParitySpecTable.length = 435 := m8CoreParitySpecTable_length
theorem cp_tbl_noExit : m8CoreParitySpecTable.all SpecEntry.noExit = true :=
  m8CoreParitySpecTable_noExit

theorem cp_noExit :
    ∀ f as bs xs m Q X X',
      m8CoreParityEnv f as bs xs m Q X → m8CoreParityEnv f as bs xs m Q X' :=
  m8CoreParityEnv_noExit

theorem cp_probe_dticks_wp (Γ : Env)
    (hGetWm : EnvSpec Γ "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64])) :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp Γ FullM8CoreParity.full_probe_dticks_m6_hdr_body a m Q X :=
  full_probe_dticks_m6_hdr_m8_wp Γ hGetWm

theorem cp_probe_m6_wp (Γ : Env)
    (hProbeDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hScaleM5 : EnvSpec Γ "full_scale_delta_m5" schedScaleDeltaSpec)
    (hViv : EnvSpec Γ "full_vivify_m6_hdr" m6aVivifySpec)
    (hEnter : EnvSpec Γ "full_enter_dense" schedEnterDenseSpec)
    (hDelay : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCong : EnvSpec Γ "full_congruence_dense" m3CongruenceDenseSpec)
    (hReb : EnvSpec Γ "full_rebuild_watches" fullRebuildWatchesSpec)
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRedD : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBumpD : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSweepD : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSubst : EnvSpec Γ "full_substitute" fullSubstituteSpec)
    (hTail : EnvSpec Γ "full_probe_tail_m6" m6ProbeTailSpec)
    (hBone : EnvSpec Γ "full_backbone_m6" FullM3Backbone.fullBackboneSpec)
    (hMin : EnvSpec Γ "full_min_u64" schedMinU64Spec)
    (hFactor : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec) :
    ∀ a m Q X, m6ProbeSpec a m Q X →
      Func.wp Γ FullM8CoreParity.full_probe_m6_body a m Q X :=
  full_probe_m6_m8_wp Γ hProbeDt hLog10 hScaleM5 hViv hEnter hDelay hCong hReb hSetWm hRedD
    hBumpD hSweepD hSubst hTail hBone hMin hFactor

theorem cp_search_m6_wp (Γ : Env)
    (hLuckyLate : EnvSpec Γ "full_lucky_late_m7" m7LuckyLateSpec)
    (hProp : EnvSpec Γ "full_propagate" fullBcpS15Spec)
    (hAnalyze : EnvSpec Γ "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hReduce : EnvSpec Γ "full_reduce_m6" m6ReduceSpec)
    (hSwitch : EnvSpec Γ "full_switch_mode_m7" m7SwitchModeSpec)
    (hRstDue : EnvSpec Γ "full_restart_due" fullRestartDueSpec)
    (hRst : EnvSpec Γ "full_restart" fullRestartSpec)
    (hReorder : EnvSpec Γ "full_reorder_m6" m4ReorderSpec)
    (hRephase : EnvSpec Γ "full_rephase" m7RephaseSpec)
    (hSimplify : EnvSpec Γ "full_simplify_m6" fullM6SimplifySpec)
    (hDecideFid : EnvSpec Γ "m6_hdr_decide_fid" m6HdrDecideSpec) :
    ∀ a m Q X, fullM6SearchSpec a m Q X →
      Func.wp Γ FullM8CoreParity.full_search_m6_body a m Q X :=
  full_search_m6_m8_wp Γ hLuckyLate hProp hAnalyze hReduce hSwitch hRstDue hRst hReorder
    hRephase hSimplify hDecideFid

theorem cp_min_lit_dfs_wp (Γ : Env)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X) :
    ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Func.wp Γ full_min_lit_dfs_m8_body args m Q X :=
  full_min_lit_dfs_m8_wp Γ hMm

theorem cp_shrink_lower_wp (Γ : Env)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X) :
    ∀ args m Q X, m8ShrinkLowerSpec args m Q X →
      Func.wp Γ full_shrink_lower_m8_body args m Q X :=
  full_shrink_lower_m8_wp Γ hMm hDfs

theorem cp_shrink_blk_bool_wp (Γ : Env)
    (hSl : ∀ args m Q X, m8ShrinkLowerSpec args m Q X →
      Γ "full_shrink_lower_m8" [i64, i32, i32] [.bool] args m Q X)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X) :
    ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Func.wp Γ full_shrink_blk_bool_m8_body args m Q X :=
  full_shrink_blk_bool_m8_wp Γ hSl hMm

theorem cp_min_shrink_wp (Γ : Env)
    (hSt : ∀ args m Q X, FullM7AnalyzeSort.m7SortTmpSpec args m Q X →
      Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, m8MinShrinkSpec args m Q X →
      Func.wp Γ FullM8CoreParity.full_min_shrink_m6_body args m Q X :=
  full_min_shrink_m6_m8_wp Γ hSt hMm hDfs hSb

theorem cp_analyze_m8_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
      Γ "full_deduce_1uip" [i64] [i64] a m Q X)
    (hRestoreBump : ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m5" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, m8MinShrinkSpec a m Q X →
      Γ "full_min_shrink" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, fullTickRelSpec a m Q X →
      Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ args m Q X, fullAnalyzeSpec args m Q X →
      Func.wp Γ FullM8FidV12.m8_analyze_body args m Q X :=
  m8_analyze_m8_wp Γ hOneLit hDeduce hRestoreBump hMinShrink hTickRel hEma hLearnCl

theorem cp_analyze_core_m6_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, m6aAnaFailedLitSpec a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, m7Deduce1uipHdrSpec a m Q X →
      Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X)
    (hRestore : ∀ a m Q X, m6aRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, m8MinShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hTick : ∀ a m Q X, fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearn : ∀ a m Q X, fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Func.wp Γ FullM8FidV12.m8_analyze_core_m6_body a m Q X :=
  m8_analyze_core_m6_m8_wp Γ hOneLit hFailed hDeduce hRestore hMinShrink hTick hEma hLearn

theorem cp_mod_ok : ModuleOk m8CoreParityEnv m8CoreParityModule := m8CoreParity_moduleOk
theorem cp_tbl_impl : TableImpl m8CoreParityEnv m8CoreParityModule.fns m8CoreParitySpecTable :=
  m8CoreParity_tableImpl

theorem cp_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8CoreParity_solve_bytes_sound hcfit hwfit hm

theorem cp_solve_host
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
  m8CoreParity_solve_bytes_host_sound hpost hhost

theorem cp_unsat_nv :
    Func.wp m8CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8CoreParity_unsat_nv

theorem cp_hot_acyc : m8CoreParityHotModule.checkAcyclic = true := m8CoreParityHot_acyclic
theorem cp_hot_ok : ModuleOk m8CoreParityEnv m8CoreParityHotModule := m8CoreParityHot_moduleOk
theorem cp_hot_tbl :
    TableImpl m8CoreParityEnv m8CoreParityHotModule.fns m8CoreParitySpecTable :=
  m8CoreParityHot_tableImpl

theorem cp_hot_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8CoreParityHot_solve_bytes_sound hcfit hwfit hm

theorem cp_hot_nv :
    Func.wp m8CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8CoreParityHot_unsat_nv

theorem cp_hop1_acyc : m8HotHop1BridgeModule.checkAcyclic = true := m8HotHop1Bridge_acyclic
theorem cp_hop1_ok : ModuleOk FullBvaHeap.bvaHeapEnv m8HotHop1BridgeModule :=
  m8HotHop1Bridge_moduleOk

theorem cp_sw_len : m8SweepV2CoreParitySpecTable.length = 471 :=
  m8SweepV2CoreParitySpecTable_length
theorem cp_sw_ok : ModuleOk m8SweepV2CoreParityEnv m8SweepV2CoreParityModule :=
  m8SweepV2CoreParity_moduleOk
theorem cp_sw_tbl :
    TableImpl m8SweepV2CoreParityEnv m8SweepV2CoreParityModule.fns m8SweepV2CoreParitySpecTable :=
  m8SweepV2CoreParity_tableImpl

theorem cp_sw_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8SweepV2CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8SweepV2CoreParity_solve_bytes_sound hcfit hwfit hm

theorem cp_sw_nv :
    Func.wp m8SweepV2CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8SweepV2CoreParity_unsat_nv

theorem cp_nv_key_mid :
    Func.wp m8CoreParityEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyMidMem
      (fun (r, ()) m' =>
        r = ((1607100#64 <<< 32) ||| 0xFFFFFFFA#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyMidState m')
      (fun _ _ _ _ => False) :=
  nv_m8_bve_var_key_mid

theorem cp_nv_key_cap :
    Func.wp m8CoreParityEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyCapMem
      (fun (r, ()) m' =>
        r = ((8000#64 <<< 32) ||| 0xFFFFFFF8#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyCapState m')
      (fun _ _ _ _ => False) :=
  nv_m8_bve_var_key_cap

theorem cp_nv_key_mid_sw :
    Func.wp m8SweepV2CoreParityEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyMidMem
      (fun (r, ()) m' =>
        r = ((1607100#64 <<< 32) ||| 0xFFFFFFFA#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyMidState m')
      (fun _ _ _ _ => False) :=
  nv_m8_bve_var_key_mid_sw

theorem cp_nv_key_cap_sw :
    Func.wp m8SweepV2CoreParityEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyCapMem
      (fun (r, ()) m' =>
        r = ((8000#64 <<< 32) ||| 0xFFFFFFF8#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyCapState m')
      (fun _ _ _ _ => False) :=
  nv_m8_bve_var_key_cap_sw

theorem cp_nv_dt_mod : ModuleOk nvM8DtEnv nvM8DtModule := nvM8Dt_moduleOk

theorem cp_nv_dt_delta :
    Func.wp nvM8DtEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 15000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  nv_m8_probe_dticks_exact_delta

theorem cp_nv_dt_floor :
    Func.wp nvM8DtEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 20000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 20000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  nv_m8_probe_dticks_exact_floor

theorem cp_nv_dt_init :
    Func.wp m8CoreParityEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, true, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  nv_m8_probe_dticks_init

theorem cp_nv_dt_noninit :
    Func.wp m8CoreParityEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body
      (nvM8Cfg.hdr, false, ()) (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => ∃ ext' s',
        10000000 ≤ r.toNat ∧ s'.core = (nvM8DtState 25000000#64).core ∧
        s'.LengthsOk nvM8Cfg ∧ M6HdrScratchPres (nvM8DtState 25000000#64) s' ∧
        M6HdrExtOk ext' ∧ nvM8F0.Unsat ∧ FullM6HdrMem nvM8Cfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_probe_dticks_noninit

theorem cp_nv_dt_init_sw :
    Func.wp m8SweepV2CoreParityEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body
      (nvM8Cfg.hdr, true, ()) (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  nv_m8_probe_dticks_init_sw

theorem cp_nv_dt_noninit_sw :
    Func.wp m8SweepV2CoreParityEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body
      (nvM8Cfg.hdr, false, ()) (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => ∃ ext' s',
        10000000 ≤ r.toNat ∧ s'.core = (nvM8DtState 25000000#64).core ∧
        s'.LengthsOk nvM8Cfg ∧ M6HdrScratchPres (nvM8DtState 25000000#64) s' ∧
        M6HdrExtOk ext' ∧ nvM8F0.Unsat ∧ FullM6HdrMem nvM8Cfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_probe_dticks_noninit_sw

theorem cp_nv_dfs :
    Func.wp m8CoreParityEnv full_min_lit_dfs_m8_body (nvM8Cfg.hdr, 3#32, false, false, ())
      nvM8DfsMem0
      (fun (r, ()) m' =>
        r = true ∧ nvM8DfsStEnd.scratch.search_ticks = 1#64 ∧
        nvM8DfsStEnd.core.mrk = [0#8, 0#8, 2#8, 0#8] ∧ nvM8DfsStEnd.LengthsOk nvM8Cfg ∧
        FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur nvM8DfsStEnd.core ∧ nvM8F0.Unsat ∧
        FullMem nvM8Cfg nvM8DfsStEnd m')
      (fun _ _ _ _ => False) :=
  nv_m8_min_lit_dfs_large_bin_true

theorem cp_nv_dfs_sw :
    Func.wp m8SweepV2CoreParityEnv full_min_lit_dfs_m8_body
      (nvM8Cfg.hdr, 3#32, false, false, ()) nvM8DfsMem0
      (fun (r, ()) m' =>
        r = true ∧ nvM8DfsStEnd.scratch.search_ticks = 1#64 ∧
        nvM8DfsStEnd.core.mrk = [0#8, 0#8, 2#8, 0#8] ∧ nvM8DfsStEnd.LengthsOk nvM8Cfg ∧
        FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur nvM8DfsStEnd.core ∧ nvM8F0.Unsat ∧
        FullMem nvM8Cfg nvM8DfsStEnd m')
      (fun _ _ _ _ => False) :=
  nv_m8_min_lit_dfs_large_bin_true_sw

theorem cp_nv_shrink :
    Func.wp m8CoreParityEnv FullM8CoreParity.full_min_shrink_m6_body
      (nvM8Min18Cfg.hdr, ()) nvM8Min18Mem
      (fun () m' => ∃ (F_cur : List (List Nat)) (s' : FullState),
        s'.LengthsOk nvM8Min18Cfg ∧ 1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ FullOtfsWitnessInv nvM8Min18Cfg nvM8F0 F_cur s'.core ∧
        nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_min_shrink_m6

theorem cp_nv_shrink_sw :
    Func.wp m8SweepV2CoreParityEnv FullM8CoreParity.full_min_shrink_m6_body
      (nvM8Min18Cfg.hdr, ()) nvM8Min18Mem
      (fun () m' => ∃ (F_cur : List (List Nat)) (s' : FullState),
        s'.LengthsOk nvM8Min18Cfg ∧ 1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ FullOtfsWitnessInv nvM8Min18Cfg nvM8F0 F_cur s'.core ∧
        nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_min_shrink_m6_sw

end LeanQbeTest.T.KissatM8CoreParityTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m8cp_r_wf := @LeanQbeTest.T.KissatM8CoreParityTest.cp_repls_wf
abbrev m8cp_b_wf := @LeanQbeTest.T.KissatM8CoreParityTest.cp_befores_wf
abbrev m8cp_f_wf := @LeanQbeTest.T.KissatM8CoreParityTest.cp_fns_wf
abbrev m8cp_nd := @LeanQbeTest.T.KissatM8CoreParityTest.cp_names_nodup
abbrev m8cp_acyc := @LeanQbeTest.T.KissatM8CoreParityTest.cp_acyclic
abbrev m8cp_tlen := @LeanQbeTest.T.KissatM8CoreParityTest.cp_tbl_len
abbrev m8cp_tnoex := @LeanQbeTest.T.KissatM8CoreParityTest.cp_tbl_noExit
abbrev m8cp_noex := @LeanQbeTest.T.KissatM8CoreParityTest.cp_noExit
abbrev m8cp_pdt := @LeanQbeTest.T.KissatM8CoreParityTest.cp_probe_dticks_wp
abbrev m8cp_probe := @LeanQbeTest.T.KissatM8CoreParityTest.cp_probe_m6_wp
abbrev m8cp_search := @LeanQbeTest.T.KissatM8CoreParityTest.cp_search_m6_wp
abbrev m8cp_dfs := @LeanQbeTest.T.KissatM8CoreParityTest.cp_min_lit_dfs_wp
abbrev m8cp_low := @LeanQbeTest.T.KissatM8CoreParityTest.cp_shrink_lower_wp
abbrev m8cp_blk := @LeanQbeTest.T.KissatM8CoreParityTest.cp_shrink_blk_bool_wp
abbrev m8cp_mshr := @LeanQbeTest.T.KissatM8CoreParityTest.cp_min_shrink_wp
abbrev m8cp_ana := @LeanQbeTest.T.KissatM8CoreParityTest.cp_analyze_m8_wp
abbrev m8cp_anac := @LeanQbeTest.T.KissatM8CoreParityTest.cp_analyze_core_m6_wp
abbrev m8cp_ok := @LeanQbeTest.T.KissatM8CoreParityTest.cp_mod_ok
abbrev m8cp_tbl := @LeanQbeTest.T.KissatM8CoreParityTest.cp_tbl_impl
abbrev m8cp_sb := @LeanQbeTest.T.KissatM8CoreParityTest.cp_solve_sound
abbrev m8cp_host := @LeanQbeTest.T.KissatM8CoreParityTest.cp_solve_host
abbrev m8cp_nv := @LeanQbeTest.T.KissatM8CoreParityTest.cp_unsat_nv
abbrev m8cp_hot_a := @LeanQbeTest.T.KissatM8CoreParityTest.cp_hot_acyc
abbrev m8cp_hot_ok := @LeanQbeTest.T.KissatM8CoreParityTest.cp_hot_ok
abbrev m8cp_hot_tbl := @LeanQbeTest.T.KissatM8CoreParityTest.cp_hot_tbl
abbrev m8cp_hot_sb := @LeanQbeTest.T.KissatM8CoreParityTest.cp_hot_sound
abbrev m8cp_hot_nv := @LeanQbeTest.T.KissatM8CoreParityTest.cp_hot_nv
abbrev m8cp_hop_a := @LeanQbeTest.T.KissatM8CoreParityTest.cp_hop1_acyc
abbrev m8cp_hop_ok := @LeanQbeTest.T.KissatM8CoreParityTest.cp_hop1_ok
abbrev m8cp_sw_len := @LeanQbeTest.T.KissatM8CoreParityTest.cp_sw_len
abbrev m8cp_sw_ok := @LeanQbeTest.T.KissatM8CoreParityTest.cp_sw_ok
abbrev m8cp_sw_tbl := @LeanQbeTest.T.KissatM8CoreParityTest.cp_sw_tbl
abbrev m8cp_sw_sb := @LeanQbeTest.T.KissatM8CoreParityTest.cp_sw_sound
abbrev m8cp_sw_nv := @LeanQbeTest.T.KissatM8CoreParityTest.cp_sw_nv
abbrev m8cp_nvk1 := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_key_mid
abbrev m8cp_nvk2 := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_key_cap
abbrev m8cp_nvk1s := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_key_mid_sw
abbrev m8cp_nvk2s := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_key_cap_sw
abbrev m8cp_nvdt := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dt_mod
abbrev m8cp_nvdt1 := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dt_delta
abbrev m8cp_nvdt2 := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dt_floor
abbrev m8cp_nvdt3 := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dt_init
abbrev m8cp_nvdt4 := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dt_noninit
abbrev m8cp_nvdt3s := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dt_init_sw
abbrev m8cp_nvdt4s := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dt_noninit_sw
abbrev m8cp_nvdfs := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dfs
abbrev m8cp_nvdfss := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_dfs_sw
abbrev m8cp_nvshr := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_shrink
abbrev m8cp_nvshrs := @LeanQbeTest.T.KissatM8CoreParityTest.cp_nv_shrink_sw

#print axioms m8cp_r_wf
#print axioms m8cp_b_wf
#print axioms m8cp_f_wf
#print axioms m8cp_nd
#print axioms m8cp_acyc
#print axioms m8cp_tlen
#print axioms m8cp_tnoex
#print axioms m8cp_noex
#print axioms m8cp_pdt
#print axioms m8cp_probe
#print axioms m8cp_search
#print axioms m8cp_dfs
#print axioms m8cp_low
#print axioms m8cp_blk
#print axioms m8cp_mshr
#print axioms m8cp_ana
#print axioms m8cp_anac
#print axioms m8cp_ok
#print axioms m8cp_tbl
#print axioms m8cp_sb
#print axioms m8cp_host
#print axioms m8cp_nv
#print axioms m8cp_hot_a
#print axioms m8cp_hot_ok
#print axioms m8cp_hot_tbl
#print axioms m8cp_hot_sb
#print axioms m8cp_hot_nv
#print axioms m8cp_hop_a
#print axioms m8cp_hop_ok
#print axioms m8cp_sw_len
#print axioms m8cp_sw_ok
#print axioms m8cp_sw_tbl
#print axioms m8cp_sw_sb
#print axioms m8cp_sw_nv
#print axioms m8cp_nvk1
#print axioms m8cp_nvk2
#print axioms m8cp_nvk1s
#print axioms m8cp_nvk2s
#print axioms m8cp_nvdt
#print axioms m8cp_nvdt1
#print axioms m8cp_nvdt2
#print axioms m8cp_nvdt3
#print axioms m8cp_nvdt4
#print axioms m8cp_nvdt3s
#print axioms m8cp_nvdt4s
#print axioms m8cp_nvdfs
#print axioms m8cp_nvdfss
#print axioms m8cp_nvshr
#print axioms m8cp_nvshrs
