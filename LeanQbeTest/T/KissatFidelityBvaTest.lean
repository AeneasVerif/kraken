/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBva
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullFidelityBva
meta import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, & Audit (`FullFidelityBva`)

1. Executable `#guard` checks on `fidBvaModule` (`14` fns, `24` externs, `38` spec rows, `0`
   exits), `checkAcyclic = true`, `fidBvaBefores`/`fidBvaRepls` splice handles, `PrintCpp`,
   `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, closed `fidBva_moduleOk`,
   `PatchModule`-ready `TableImpl` bridges, parametric `Func.wp` specs, and concrete `Mem 64`
   UNSAT non-vacuity (`XPost := False`, `scratch_cap = 64` and `scratch_cap = 0` fallback).
3. Single-line `< 100c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityBvaTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullFidelityBva

/-! ## 1. Executable `#guard` Codegen, Splice & 4-ISA Legalization Checks -/

#guard fidBvaModule.checkAcyclic == true
#guard fidBvaModule.exits.isEmpty == true
#guard fidBvaFns.length == 14
#guard fidBvaExterns.length == 24
#guard fidBvaHelpers.length == 7
#guard fidBvaRepls.length == 7
#guard fidBvaSpecTable.length == 38
#guard fidBvaSpecTable.all (·.noExit) == true
#guard fidBvaSpecTable.map (fun e => (e.name, e.as, e.rs)) ==
  fidBvaModule.fns.map Fn.sig ++ fidBvaModule.externs.map Extern.sig
#guard fidBvaPatchBeforeRows.map (fun e => (e.name, e.as, e.rs)) ==
  fidBvaHelpers.map Fn.sig
#guard fidBvaPatchReplRows.map (fun e => (e.name, e.as, e.rs)) ==
  fidBvaRepls.map Fn.sig
#guard fidBvaPatchHeapReplRows.map (fun e => (e.name, e.as, e.rs)) ==
  fidBvaRepls.map Fn.sig
#guard fidBvaBefores.map (fun p => (p.1, p.2.map Fn.sig)) ==
  [("full_bva_scan_cands", fidBvaHelpers.map Fn.sig)]
#guard fidBvaPatchRowBefores.map (fun p => (p.1, p.2.map (fun e => (e.name, e.as, e.rs)))) ==
  [("full_bva_scan_cands", fidBvaHelpers.map Fn.sig)]
#guard fidBvaFns.map Fn.name ==
  [ "full_bva_steps_cap_fid", "full_bva_clines_fid", "full_fheap_up_fid"
  , "full_fheap_down_fid", "full_bva_count_lit_deg_fid"
  , "full_bva_connect_clauses_fid", "full_bva_match_large_bva_fid"
  , "full_bva_scan_cands", "full_bva_pick_cand", "full_bva_filter_row"
  , "full_bva_commit", "full_bva_try_lit", "full_factor", "full_probe_m6" ]
#guard (ppTModule fidBvaModule).isOk
#guard match ppTModule fidBvaModule with
  | .ok s =>
      (s.splitOn "full_bva_steps_cap_fid").length > 1 &&
      (s.splitOn "full_bva_clines_fid").length > 1 &&
      (s.splitOn "full_fheap_up_fid").length > 1 &&
      (s.splitOn "full_fheap_down_fid").length > 1 &&
      (s.splitOn "full_bva_count_lit_deg_fid").length > 1 &&
      (s.splitOn "full_bva_connect_clauses_fid").length > 1 &&
      (s.splitOn "full_bva_match_large_bva_fid").length > 1 &&
      (s.splitOn "full_bva_scan_cands").length > 1 &&
      (s.splitOn "full_bva_pick_cand").length > 1 &&
      (s.splitOn "full_bva_filter_row").length > 1 &&
      (s.splitOn "full_bva_commit").length > 1 &&
      (s.splitOn "full_bva_try_lit").length > 1 &&
      (s.splitOn "full_factor").length > 1 &&
      (s.splitOn "full_probe_m6").length > 1
  | .error _ => false
#guard (PrintQbe.module fidBvaModule).isOk
#guard (ppModule (fidBvaFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidBvaFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidBvaFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (fidBvaFns.map (Fn.legal .x64AVX512))).isOk
#guard fidBvaFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidBvaFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidBvaFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidBvaFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem fb_fns_wf : ∀ f ∈ fidBvaFns, f.Wf := fidBvaFns_wf
theorem fb_acyc : fidBvaModule.checkAcyclic = true := fidBva_acyclic
theorem fb_nd : (fidBvaSpecTable.map SpecEntry.name).Nodup := fidBvaSpecTable_nodup

theorem fb_no_exit :
    ∀ f as bs xs m Q X X', fidBvaEnv f as bs xs m Q X → fidBvaEnv f as bs xs m Q X' :=
  fidBvaEnv_noExit

theorem fb_mod_ok : ModuleOk fidBvaEnv fidBvaModule := fidBva_moduleOk
theorem fb_tbl_impl : TableImpl fidBvaEnv fidBvaFns fidBvaSpecTable := fidBva_tableImpl

theorem fb_befores_ti (Γ : Env)
    (hFlush : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X) :
    TableImpl Γ fidBvaHelpers fidBvaPatchBeforeRows :=
  fidBvaPatchBefores_tableImpl Γ hFlush hNext hPush hDeg

theorem fb_scan_wp (Γ : Env)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X →
      Γ "full_bva_clines_fid" [i64] [i64] a m Q X) :
    ∀ a m Q X, fidBvaScanCandsSpec a m Q X →
      Func.wp Γ FullFidelityBva.full_bva_scan_cands_body a m Q X :=
  full_bva_scan_cands_fid_wp Γ hClines

theorem fb_pick_wp (Γ : Env) :
    ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Func.wp Γ FullFidelityBva.full_bva_pick_cand_body a m Q X :=
  full_bva_pick_cand_fid_wp Γ

theorem fb_filter_wp (Γ : Env)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X →
      Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    (hMatchLarge : ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Γ "full_bva_match_large_bva_fid" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Func.wp Γ FullFidelityBva.full_bva_filter_row_body a m Q X :=
  full_bva_filter_row_fid_wp Γ hClines hMatchLarge

theorem fb_commit_wp (Γ : Env)
    (hSteps : ∀ args m Q X, fidBvaStepsCapSpec args m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] args m Q X)
    (hDefrag : ∀ args m Q X, fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hAllocCl : ∀ args m Q X, fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hDelBin : ∀ args m Q X, fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, fidBvaCommitSpec args m Q X →
      Func.wp Γ FullFidelityBva.full_bva_commit_body args m Q X :=
  full_bva_commit_fid_wp Γ hSteps hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch

theorem fb_try_lit_wp (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hScan : ∀ a m Q X, fidBvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilter : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    (hCommit : ∀ a m Q X, fidBvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidBvaTryLitSpec a m Q X →
      Func.wp Γ FullFidelityBva.full_bva_try_lit_body a m Q X :=
  full_bva_try_lit_fid_wp Γ hSteps hScan hPick hFilter hCommit

theorem fb_try_lit_heap_wp (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hScan : ∀ a m Q X, fidBvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilter : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    (hCommit : ∀ a m Q X, fidBvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBvaTryLitHeapSpec a m Q X →
      Func.wp Γ FullFidelityBva.full_bva_try_lit_body a m Q X :=
  full_bva_try_lit_heap_wp Γ hSteps hScan hPick hFilter hCommit

theorem fb_factor_wp (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hConn : ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
      Γ "full_bva_connect_clauses_fid" [i64] [] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    (hTry : ∀ a m Q X, fidBvaTryLitSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Func.wp Γ FullFidelityBva.full_factor_body a m Q X :=
  full_factor_fid_wp Γ hSteps hConn hDeg hUp hDown hTry

theorem fb_probe_wp (Γ : Env)
    (hDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hL10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hSc : EnvSpec Γ "full_scale_delta_m5" schedScaleDeltaSpec)
    (hViv : EnvSpec Γ "full_vivify_m6_hdr" m6aVivifySpec)
    (hEd : EnvSpec Γ "full_enter_dense" schedEnterDenseSpec)
    (hDl : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCg : EnvSpec Γ "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
    (hRw : EnvSpec Γ "full_rebuild_watches" fullRebuildWatchesSpec)
    (hSw : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRd : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBd : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSp : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSb : EnvSpec Γ "full_substitute" fullSubstituteSpec)
    (hTl : EnvSpec Γ "full_probe_tail_m6" m6ProbeTailSpec)
    (hBb : EnvSpec Γ "full_backbone_m6" fullBackboneSpec)
    (hFac : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec) :
    ∀ a m Q X, m6ProbeSpec a m Q X →
      Func.wp Γ FullFidelityBva.full_probe_m6_body a m Q X :=
  full_probe_m6_fid_wp Γ hDt hL10 hSc hViv hEd hDl hCg hRw hSw hRd hBd hSp hSb hTl hBb hFac

theorem fb_nv_sc64 :
    Func.wp fidBvaEnv full_bva_steps_cap_fid_body (64#64, ()) nvFidBvaMem
      (fun (r, ()) m' => r = 8#32 ∧ 0 < r.toNat ∧ m' = nvFidBvaMem)
      (fun _ _ _ _ => False) :=
  nv_fid_bva_steps_cap_64

theorem fb_nv_sctiny :
    Func.wp fidBvaEnv full_bva_steps_cap_fid_body (0#64, ()) nvFidTinyMem
      (fun (r, ()) m' => r = 0#32 ∧ m' = nvFidTinyMem)
      (fun _ _ _ _ => False) :=
  nv_fid_bva_steps_cap_tiny

theorem fb_nv_conn64 :
    Func.wp fidBvaEnv full_bva_connect_clauses_fid_body (nvFidBvaCfg.hdr, ()) nvFidBvaMem
      (fun _ m' => ∃ s', FullDenseInvW nvFidBvaCfg nvOneLitF0 [[0], [1]] s' ∧
        s'.core.cur_vars = 1 ∧ nvOneLitF0.Unsat ∧ FullMem nvFidBvaCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bva_connect_64

theorem fb_nv_fac64 :
    Func.wp fidBvaEnv FullFidelityBva.full_factor_body (nvFidBvaCfg.hdr, 100#64, ()) nvFidBvaMem
      (fun (r, ()) m' => ∃ s', FullDenseInv nvFidBvaCfg nvOneLitF0 s' ∧
        1 ≤ s'.core.cur_vars ∧ r = 1#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvFidBvaCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bva_factor_64

theorem fb_nv_factiny :
    Func.wp fidBvaEnv FullFidelityBva.full_factor_body
      (nvFidTinyCfg.hdr, 100#64, ()) nvFidTinyMem
      (fun (r, ()) m' => ∃ s', FullDenseInv nvFidTinyCfg nvOneLitF0 s' ∧
        1 ≤ s'.core.cur_vars ∧ r = 1#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvFidTinyCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bva_factor_tiny

theorem fb_nv_probe :
    Func.wp fidBvaEnv FullFidelityBva.full_probe_m6_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_probe_m6

end AuditSpec

end LeanQbeTest.T.KissatFidelityBvaTest

/-! ## 3. Single-Line `< 100c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev fbva_wf := @LeanQbeTest.T.KissatFidelityBvaTest.fb_fns_wf
abbrev fbva_ac := @LeanQbeTest.T.KissatFidelityBvaTest.fb_acyc
abbrev fbva_nd := @LeanQbeTest.T.KissatFidelityBvaTest.fb_nd
abbrev fbva_nx := @LeanQbeTest.T.KissatFidelityBvaTest.fb_no_exit
abbrev fbva_ok := @LeanQbeTest.T.KissatFidelityBvaTest.fb_mod_ok
abbrev fbva_ti := @LeanQbeTest.T.KissatFidelityBvaTest.fb_tbl_impl
abbrev fbva_bf := @LeanQbeTest.T.KissatFidelityBvaTest.fb_befores_ti
abbrev fbva_sc := @LeanQbeTest.T.KissatFidelityBvaTest.fb_scan_wp
abbrev fbva_pk := @LeanQbeTest.T.KissatFidelityBvaTest.fb_pick_wp
abbrev fbva_fl := @LeanQbeTest.T.KissatFidelityBvaTest.fb_filter_wp
abbrev fbva_cm := @LeanQbeTest.T.KissatFidelityBvaTest.fb_commit_wp
abbrev fbva_tl := @LeanQbeTest.T.KissatFidelityBvaTest.fb_try_lit_wp
abbrev fbva_tlh := @LeanQbeTest.T.KissatFidelityBvaTest.fb_try_lit_heap_wp
abbrev fbva_fc := @LeanQbeTest.T.KissatFidelityBvaTest.fb_factor_wp
abbrev fbva_pr := @LeanQbeTest.T.KissatFidelityBvaTest.fb_probe_wp
abbrev fbva_s64 := @LeanQbeTest.T.KissatFidelityBvaTest.fb_nv_sc64
abbrev fbva_st := @LeanQbeTest.T.KissatFidelityBvaTest.fb_nv_sctiny
abbrev fbva_c64 := @LeanQbeTest.T.KissatFidelityBvaTest.fb_nv_conn64
abbrev fbva_f64 := @LeanQbeTest.T.KissatFidelityBvaTest.fb_nv_fac64
abbrev fbva_ft := @LeanQbeTest.T.KissatFidelityBvaTest.fb_nv_factiny
abbrev fbva_nvp := @LeanQbeTest.T.KissatFidelityBvaTest.fb_nv_probe

#print axioms fbva_wf
#print axioms fbva_ac
#print axioms fbva_nd
#print axioms fbva_nx
#print axioms fbva_ok
#print axioms fbva_ti
#print axioms fbva_bf
#print axioms fbva_sc
#print axioms fbva_pk
#print axioms fbva_fl
#print axioms fbva_cm
#print axioms fbva_tl
#print axioms fbva_tlh
#print axioms fbva_fc
#print axioms fbva_pr
#print axioms fbva_s64
#print axioms fbva_st
#print axioms fbva_c64
#print axioms fbva_f64
#print axioms fbva_ft
#print axioms fbva_nvp
