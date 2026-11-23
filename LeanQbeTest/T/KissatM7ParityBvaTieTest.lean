module

public import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
public import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTieProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
meta import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTieProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M7 `FullM7ParityBvaTie`

1. Executable `#guard` checks on `m7ParityBvaTieModule` (`3` fns, `19` externs, `0` exits),
   `m7ParityBvaTieSpecTable` (`22` rows, `noExit = true`), `FullM7Splice.patchFns`/`patchRows`
   handles (`m7btBvaPickCandFn`, `m7btProbeTailFn`, `m7btProbeFn`), `PrintCpp`, `PrintQbe`, and
   4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, all `3` parametric
   `Func.wp` contracts, closed `TableImpl` / `ModuleOk`, `patchFns`/`patchRows` `SpecEntry.Impl`
   and `TableImpl` bridges, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7ParityBvaTieTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m7ParityBvaTie_fns.length == 3
#guard m7ParityBvaTieExterns.length == 19
#guard m7ParityBvaTieModule.checkAcyclic == true
#guard m7ParityBvaTieModule.exits.isEmpty == true
#guard m7ParityBvaTieSpecTable.length == 22
#guard m7ParityBvaTieSpecTable.all (·.noExit) == true
#guard m7ParityBvaTieSpecTable.map (fun e => (e.name, e.as, e.rs)) ==
  m7ParityBvaTieModule.sigs
#guard m7ParityBvaTie_fns.map Fn.name ==
  [ "full_bva_pick_cand_bt", "full_probe_tail_bt", "full_probe_bt" ]
#guard m7ParityBvaTiePatchFns.map Fn.name ==
  [ "full_bva_pick_cand", "full_probe_tail_m6", "full_probe_m6" ]
#guard m7ParityBvaTiePatchRows.map (fun e => (e.name, e.as, e.rs)) ==
  m7ParityBvaTiePatchFns.map Fn.sig
#guard m7ParityBvaTiePatchRows.all (·.noExit) == true
#guard (ppTModule m7ParityBvaTieModule).isOk
#guard (PrintQbe.module m7ParityBvaTieModule).isOk
#guard (ppModule (m7ParityBvaTie_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7ParityBvaTie_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7ParityBvaTie_fns.map (Fn.legal .x64AVX2))).isOk
#guard m7ParityBvaTie_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem bt_pick_wf : Func.Wf full_bva_pick_cand_bt_body := full_bva_pick_cand_bt_wf
theorem bt_tail_wf : Func.Wf full_probe_tail_bt_body := full_probe_tail_bt_wf
theorem bt_probe_wf : Func.Wf full_probe_bt_body := full_probe_bt_wf
theorem bt_fns_wf : ∀ f ∈ m7ParityBvaTie_fns, f.Wf := m7ParityBvaTie_fns_wf
theorem bt_patch_fns_wf : ∀ f ∈ m7ParityBvaTiePatchFns, f.Wf := m7ParityBvaTiePatchFns_wf
theorem bt_acyc : m7ParityBvaTieModule.checkAcyclic = true := m7ParityBvaTie_acyclic
theorem bt_tbl_len : m7ParityBvaTieSpecTable.length = 22 := m7ParityBvaTieSpecTable_length

theorem bt_noExit :
    ∀ f as bs xs m Q X X',
      m7ParityBvaTieEnv f as bs xs m Q X → m7ParityBvaTieEnv f as bs xs m Q X' :=
  m7ParityBvaTieEnv_noExit

theorem bt_pick_wp (Γ : Env) :
    ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Func.wp Γ full_bva_pick_cand_bt_body a m Q X :=
  full_bva_pick_cand_bt_wp Γ

theorem bt_tail_wp (Γ : Env)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hProbeRun : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, m6aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Func.wp Γ full_probe_tail_bt_body a m Q X :=
  full_probe_tail_bt_wp Γ hBackbone hTrans hMin hProbeRun hViv

theorem bt_probe_wp (Γ : Env)
    (hDticks : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweep : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, Full.fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X →
      Func.wp Γ full_probe_bt_body a m Q X :=
  full_probe_bt_wp Γ hDticks hIlog hScale hEnter hDelay hCong hRebuild
    hSetWm hRedD hBumpD hSweep hSubst hTail hBackbone hMin hFactor

theorem bt_tbl_impl :
    TableImpl m7ParityBvaTieEnv m7ParityBvaTieModule.fns m7ParityBvaTieSpecTable :=
  m7ParityBvaTie_tableImpl

theorem bt_mod_ok : ModuleOk m7ParityBvaTieEnv m7ParityBvaTieModule :=
  m7ParityBvaTie_moduleOk

theorem bt_patch_tbl_impl :
    TableImpl m7ParityBvaTieEnv m7ParityBvaTiePatchFns m7ParityBvaTiePatchRows :=
  m7ParityBvaTiePatch_tableImpl

theorem bt_pick_fn_impl : SpecEntry.Impl m7ParityBvaTieEnv m7btBvaPickCandFn
    ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩ :=
  m7btBvaPickCandFn_impl

theorem bt_tail_fn_impl : SpecEntry.Impl m7ParityBvaTieEnv m7btProbeTailFn
    ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :=
  m7btProbeTailFn_impl

theorem bt_probe_fn_impl : SpecEntry.Impl m7ParityBvaTieEnv m7btProbeFn
    ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :=
  m7btProbeFn_impl

theorem bt_nv_pick :
    Func.wp m7ParityBvaTieEnv full_bva_pick_cand_bt_body
      (nvOneLitCfg.hdr, 2#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullBvaHeapHelpers.FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7bt_bva_pick_cand

theorem bt_nv_tail :
    Func.wp m7ParityBvaTieEnv full_probe_tail_bt_body (nvOneLitCfg.hdr, 1024#64, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m7bt_probe_tail

theorem bt_nv_probe :
    Func.wp m7ParityBvaTieEnv full_probe_bt_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m7bt_probe

end LeanQbeTest.T.KissatM7ParityBvaTieTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7bt_wf_p := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_pick_wf
abbrev m7bt_wf_t := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_tail_wf
abbrev m7bt_wf_b := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_probe_wf
abbrev m7bt_wf_all := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_fns_wf
abbrev m7bt_wf_pat := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_patch_fns_wf
abbrev m7bt_acyc := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_acyc
abbrev m7bt_tbl_len := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_tbl_len
abbrev m7bt_nx := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_noExit
abbrev m7bt_wp_p := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_pick_wp
abbrev m7bt_wp_t := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_tail_wp
abbrev m7bt_wp_b := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_probe_wp
abbrev m7bt_tbl := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_tbl_impl
abbrev m7bt_mod := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_mod_ok
abbrev m7bt_ptbl := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_patch_tbl_impl
abbrev m7bt_fn_p := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_pick_fn_impl
abbrev m7bt_fn_t := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_tail_fn_impl
abbrev m7bt_fn_b := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_probe_fn_impl
abbrev m7bt_nv_p := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_nv_pick
abbrev m7bt_nv_t := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_nv_tail
abbrev m7bt_nv_b := @LeanQbeTest.T.KissatM7ParityBvaTieTest.bt_nv_probe

#print axioms m7bt_wf_p
#print axioms m7bt_wf_t
#print axioms m7bt_wf_b
#print axioms m7bt_wf_all
#print axioms m7bt_wf_pat
#print axioms m7bt_acyc
#print axioms m7bt_tbl_len
#print axioms m7bt_nx
#print axioms m7bt_wp_p
#print axioms m7bt_wp_t
#print axioms m7bt_wp_b
#print axioms m7bt_tbl
#print axioms m7bt_mod
#print axioms m7bt_ptbl
#print axioms m7bt_fn_p
#print axioms m7bt_fn_t
#print axioms m7bt_fn_b
#print axioms m7bt_nv_p
#print axioms m7bt_nv_t
#print axioms m7bt_nv_b
