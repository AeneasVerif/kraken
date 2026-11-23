module

public import LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
public import LeanQbe.T.Examples.Kissat.FullM7BvaV5FixProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
meta import LeanQbe.T.Examples.Kissat.FullM7BvaV5FixProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M7 `FullM7BvaV5Fix`

1. Executable `#guard` checks on `m7BvaV5FixModule` (`4` fns, `28` externs, `0` exits),
   `m7BvaV5FixSpecTable` (`32` rows, `noExit = true`), drop-in `Fn` handles (`m7v5CalcMaxVFn`,
   `m7v5ProbeFn`, `m7v5ForwardSubFn`, `m7v5EliminateFn`), `PrintCpp`, `PrintQbe`, and 4-ISA
   `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, all `4` parametric
   `Func.wp` contracts, closed `ModuleOk`, drop-in `SpecEntry.Impl` bridges, and concrete
   `Mem 64` UNSAT non-vacuity (`XPost := False`, zero SAT proofs).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7BvaV5FixTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m7BvaV5Fix_fns.length == 4
#guard m7BvaV5FixExterns.length == 28
#guard m7BvaV5FixModule.checkAcyclic == true
#guard m7BvaV5FixModule.exits.isEmpty == true
#guard m7BvaV5FixSpecTable.length == 32
#guard m7BvaV5FixSpecTable.all (·.noExit) == true
#guard m7BvaV5FixSpecTable.map (fun e => (e.name, e.as, e.rs)) == m7BvaV5FixModule.sigs
#guard m7BvaV5Fix_fns.map Fn.name ==
  [ "full_calc_max_v_m7v5", "full_probe_m7v5",
    "full_forward_sub_m7v5", "full_eliminate_m7v5" ]
#guard m7v5CalcMaxVFn.name == "full_calc_max_v"
#guard m7v5ProbeFn.name == "full_probe_m6"
#guard m7v5ForwardSubFn.name == "full_forward_sub"
#guard m7v5EliminateFn.name == "full_eliminate_m6"
#guard (ppTModule m7BvaV5FixModule).isOk
#guard (PrintQbe.module m7BvaV5FixModule).isOk
#guard (ppModule (m7BvaV5Fix_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7BvaV5Fix_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7BvaV5Fix_fns.map (Fn.legal .x64AVX2))).isOk
#guard m7BvaV5Fix_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem v5_calc_wf : Func.Wf full_calc_max_v_m7v5_body := full_calc_max_v_m7v5_wf
theorem v5_probe_wf : Func.Wf full_probe_m7v5_body := full_probe_m7v5_wf
theorem v5_fwd_wf : Func.Wf full_forward_sub_m7v5_body := full_forward_sub_m7v5_wf
theorem v5_elim_wf : Func.Wf full_eliminate_m7v5_body := full_eliminate_m7v5_wf
theorem v5_fns_wf : ∀ f ∈ m7BvaV5Fix_fns, f.Wf := m7BvaV5Fix_fns_wf
theorem v5_acyc : m7BvaV5FixModule.checkAcyclic = true := m7BvaV5Fix_acyclic
theorem v5_tbl_len : m7BvaV5FixSpecTable.length = 32 := m7BvaV5FixSpecTable_length

theorem v5_noExit :
    ∀ f as bs xs m Q X X',
      m7BvaV5FixEnv f as bs xs m Q X → m7BvaV5FixEnv f as bs xs m Q X' :=
  m7BvaV5FixEnv_noExit

theorem v5_calc_wp (Γ : Env)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullCalcMaxVSpec a m Q X →
      Func.wp Γ full_calc_max_v_m7v5_body a m Q X :=
  full_calc_max_v_m7v5_wp Γ hFixed

theorem v5_probe_wp (Γ : Env)
    (hDticks : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
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
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X →
      Func.wp Γ full_probe_m7v5_body a m Q X :=
  full_probe_m7v5_wp Γ hDticks hIlog hScale hEnter hDelay hCong hRebuild
    hSetWm hRedD hBumpD hSweep hSubst hTail hBackbone hMin hFactor

theorem v5_fwd_wp (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hCollectSort : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Γ "full_fwd_collect_sort_m7" [i64] [i64] a m Q X)
    (hFlushLarge : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hCheckCl : ∀ a m Q X, m7v5FwdCheckClSpec a m Q X →
      Γ "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X)
    (hConnectSub : ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Γ "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hReconnect : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Γ "full_fwd_reconnect_irred_m7" [i64] [] a m Q X) :
    ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Func.wp Γ full_forward_sub_m7v5_body a m Q X :=
  full_forward_sub_m7v5_wp Γ hDedup hFlushUnits hCollectSort hFlushLarge
    hCheckCl hConnectSub hArenaNext hReconnect

theorem v5_elim_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m7v5" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorHeapSpec a m Q X → Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_m7v5_body a m Q X :=
  full_eliminate_m7v5_wp Γ hDticks hIlog hScale hEnter hMin hFwd hBve hFact hReb

theorem v5_tbl_impl : TableImpl m7BvaV5FixEnv m7BvaV5FixModule.fns m7BvaV5FixSpecTable :=
  m7BvaV5Fix_tableImpl

theorem v5_mod_ok : ModuleOk m7BvaV5FixEnv m7BvaV5FixModule := m7BvaV5Fix_moduleOk

theorem v5_calc_fn_impl : SpecEntry.Impl m7BvaV5FixEnv m7v5CalcMaxVFn
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], Full.fullCalcMaxVSpec, true⟩ :=
  m7v5CalcMaxVFn_impl

theorem v5_probe_fn_impl : SpecEntry.Impl m7BvaV5FixEnv m7v5ProbeFn
    ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :=
  m7v5ProbeFn_impl

theorem v5_fwd_fn_impl : SpecEntry.Impl m7BvaV5FixEnv m7v5ForwardSubFn
    ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
  m7v5ForwardSubFn_impl

theorem v5_elim_fn_impl : SpecEntry.Impl m7BvaV5FixEnv m7v5EliminateFn
    ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
  m7v5EliminateFn_impl

theorem v5_nv_calc :
    Func.wp m7BvaV5FixEnv full_calc_max_v_m7v5_body
      (33554432#64, 2#64, 1#64, BitVec.ofNat 64 (fullFixedBytes 2), ())
      (∅ : Mem 64)
      (fun (r, ()) m' => r = 4098#64 ∧ m' = (∅ : Mem 64))
      (fun _ _ _ _ => False) :=
  nv_m7v5_calc_max_v

theorem v5_nv_fwd :
    Func.wp m7BvaV5FixEnv full_forward_sub_m7v5_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, ()) FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7v5_forward_sub

theorem v5_nv_elim :
    Func.wp m7BvaV5FixEnv full_eliminate_m7v5_body
      (FullM4Sweep.nvM4SweepCfg.hdr, true, ()) FullM4Sweep.nvM4SweepSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7v5_eliminate

end LeanQbeTest.T.KissatM7BvaV5FixTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7v5_wf_c := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_calc_wf
abbrev m7v5_wf_p := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_probe_wf
abbrev m7v5_wf_f := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_fwd_wf
abbrev m7v5_wf_e := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_elim_wf
abbrev m7v5_wf_all := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_fns_wf
abbrev m7v5_acyc := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_acyc
abbrev m7v5_tbl_len := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_tbl_len
abbrev m7v5_nx := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_noExit
abbrev m7v5_wp_c := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_calc_wp
abbrev m7v5_wp_p := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_probe_wp
abbrev m7v5_wp_f := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_fwd_wp
abbrev m7v5_wp_e := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_elim_wp
abbrev m7v5_tbl := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_tbl_impl
abbrev m7v5_mod := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_mod_ok
abbrev m7v5_fn_c := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_calc_fn_impl
abbrev m7v5_fn_p := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_probe_fn_impl
abbrev m7v5_fn_f := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_fwd_fn_impl
abbrev m7v5_fn_e := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_elim_fn_impl
abbrev m7v5_nv_c := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_nv_calc
abbrev m7v5_nv_f := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_nv_fwd
abbrev m7v5_nv_e := @LeanQbeTest.T.KissatM7BvaV5FixTest.v5_nv_elim

#print axioms m7v5_wf_c
#print axioms m7v5_wf_p
#print axioms m7v5_wf_f
#print axioms m7v5_wf_e
#print axioms m7v5_wf_all
#print axioms m7v5_acyc
#print axioms m7v5_tbl_len
#print axioms m7v5_nx
#print axioms m7v5_wp_c
#print axioms m7v5_wp_p
#print axioms m7v5_wp_f
#print axioms m7v5_wp_e
#print axioms m7v5_tbl
#print axioms m7v5_mod
#print axioms m7v5_fn_c
#print axioms m7v5_fn_p
#print axioms m7v5_fn_f
#print axioms m7v5_fn_e
#print axioms m7v5_nv_c
#print axioms m7v5_nv_f
#print axioms m7v5_nv_e
