module

public import LeanQbe.T.Examples.Kissat.FullM6BveFwd
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6BveFwd
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Checks, and Axiom Audit for Kissat `M6` (`FullM6BveFwd`)

1. Executable `#guard` checks on `m6BveFwdModule` (`24` owned `_m6` functions + `24` canonical
   externs, `0` exits), `checkAcyclic = true`, `PrintCpp`, `PrintQbe`, and `Fn.legal` across
   `aarch64`, `scalar64`, and `x64AVX2`.
2. Short root-namespace audit theorems covering `ModuleOk`, table invariants, canonical UNSAT
   soundness bridges, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs).
3. Single-line `#print axioms` audit (strictly `⊆ [propext, Classical.choice,
   Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeLegacyTest.KissatM6BveFwdTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.FullM6BveFwd

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m6BveFwdModule.checkAcyclic == true
#guard m6BveFwdModule.exits.isEmpty
#guard m6BveFwd_fns.length == 24
#guard m6BveFwdExterns.length == 24
#guard m6BveFwd_fns.map Fn.name ==
  [ "full_dense_prop_unit_m6", "full_dense_flush_units_m6", "full_fwd_flush_large_m6",
    "full_fwd_reconnect_irred_m6", "full_fwd_scan_lit_m6", "full_fwd_check_cl_m6",
    "full_fwd_connect_subsumer_m6", "full_fwd_collect_sort_m6", "full_forward_sub_m6",
    "full_bve_collect_m6", "full_bve_mark_and_m6", "full_bve_get_tern_m6",
    "full_bve_match_tern_m6", "full_bve_find_ite_m6", "full_bve_gates_m6",
    "full_bve_var_m6", "full_bve_var_key_m6", "full_bve_heap_up_m6",
    "full_bve_heap_down_m6", "full_bve_heap_push_m6", "full_bve_heap_pop_m6",
    "full_bve_collect_nbrs_m6", "full_elim_bve_m6", "full_eliminate_m6" ]
#guard (ppTModule m6BveFwdModule).isOk
#guard (PrintQbe.module m6BveFwdModule).isOk
#guard (ppModule (m6BveFwd_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6BveFwd_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6BveFwd_fns.map (Fn.legal .x64AVX2))).isOk

end LeanQbeLegacyTest.KissatM6BveFwdTest

/-! ## 2. Short Root-Namespace Audit Theorems & Single-Line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd

theorem m6bf_wf : ∀ f ∈ m6BveFwd_fns, f.Wf :=
  m6BveFwd_fns_wf

theorem m6bf_acyc : m6BveFwdModule.checkAcyclic = true :=
  m6BveFwdModule_acyclic

theorem m6bf_tbl_len : m6BveFwdSpecTable.length = 48 :=
  m6BveFwdSpecTable_len

theorem m6bf_nodup : (m6BveFwdSpecTable.map SpecEntry.name).Nodup :=
  m6BveFwdSpecTable_nodup

theorem m6bf_noExit : ∀ e ∈ m6BveFwdSpecTable, e.noExit = true :=
  m6BveFwdSpecTable_noExit

theorem m6bf_sigs :
    (m6BveFwdSpecTable.take 24).map (fun e => (e.name, e.as, e.rs)) =
      m6BveFwd_fns.map (fun f => (f.name, f.as, f.rs)) :=
  m6BveFwdSpecTable_sigs

theorem m6bf_ext_sigs :
    (m6BveFwdSpecTable.drop 24).map (fun e => ⟨e.name, e.as, e.rs⟩) = m6BveFwdExterns :=
  m6BveFwdSpecTable_ext_sigs

theorem m6bf_env_noExit :
    ∀ f as bs xs m Q X X',
      m6BveFwdEnv f as bs xs m Q X → m6BveFwdEnv f as bs xs m Q X' :=
  m6BveFwdEnv_noExit

theorem m6bf_mod_ok : ModuleOk m6BveFwdEnv m6BveFwdModule :=
  m6BveFwd_moduleOk

theorem m6bf_chk_canon_ok :
    ∀ a m Q X, fullFwdCheckClSpec a m Q X →
      Func.wp m6BveFwdEnv full_fwd_check_cl_m6_body a m Q X :=
  full_fwd_check_cl_m6_canon_ok

theorem m6bf_fwd_wp (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m6" [i64] [.bool] a m Q X)
    (hCollectSort : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Γ "full_fwd_collect_sort_m6" [i64] [i64] a m Q X)
    (hFlushLarge : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m6" [i64] [] a m Q X)
    (hCheckCl : ∀ a m Q X, fullFwdCheckClM6Spec a m Q X →
      Γ "full_fwd_check_cl_m6" [i64, i32] [.bool] a m Q X)
    (hConnectSub : ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Γ "full_fwd_connect_subsumer_m6" [i64, i32] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hReconnect : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Γ "full_fwd_reconnect_irred_m6" [i64] [] a m Q X) :
    ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Func.wp Γ full_forward_sub_m6_body a m Q X :=
  full_forward_sub_m6_wp Γ hDedup hFlushUnits hCollectSort hFlushLarge hCheckCl hConnectSub
    hArenaNext hReconnect

theorem m6bf_bve_var_wp (Γ : Env)
    (hCollect : ∀ a m Q X, fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m6" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGates : ∀ a m Q X, fullBveGatesM6Spec a m Q X →
      Γ "full_bve_gates_m6" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m6" [i64] [.bool] a m Q X)
    (hTryBce : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hExtPush2 : ∀ a m Q X, fullExtendPush2TmkSpec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hExtPushCl : ∀ a m Q X, fullExtendPushClTmkSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Func.wp Γ full_bve_var_m6_body a m Q X :=
  full_bve_var_m6_wp Γ hCollect hExtNeed hWeaken hSetInact hGates hResPair hDefrag hCommit
    hFlushUnits hTryBce hExtPush2 hDelBin hExtPushCl

theorem m6bf_elim_bve_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m6" [i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, fullBveHeapPushM6Spec a m Q X →
      Γ "full_bve_heap_push_m6" [i64, i64, i32] [i64] a m Q X)
    (hPop : ∀ a m Q X, fullBveHeapPopM6Spec a m Q X →
      Γ "full_bve_heap_pop_m6" [i64, i64] [i32] a m Q X)
    (hNbrs : ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Γ "full_bve_collect_nbrs_m6" [i64, i32] [i64] a m Q X)
    (hBveVar : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m6" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3ElimBveSpec a m Q X → Func.wp Γ full_elim_bve_m6_body a m Q X :=
  full_elim_bve_m6_wp Γ hFlush hPush hPop hNbrs hBveVar

theorem m6bf_eliminate_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m6" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X → Γ "full_elim_bve_m6" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorHeapSpec a m Q X → Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X → Func.wp Γ full_eliminate_m6_body a m Q X :=
  full_eliminate_m6_wp Γ hDticks hIlog hScale hEnter hMin hFwd hBve hFact hReb

theorem m6bf_nv_flush_units :
    Func.wp m6BveFwdEnv full_dense_flush_units_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, ())
      FullM4Sweep.nvM4SweepMem
      (fun (ok, ()) m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg nvOneLitF0 [[0], [1]] s' ∧
        (ok = true ∨ ok = false) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_dense_flush_units

theorem m6bf_nv_fwd_sub :
    Func.wp m6BveFwdEnv full_forward_sub_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_forward_sub

theorem m6bf_nv_fwd_sub_20 :
    let Γ20 : Env := fun f as bs xs m Q X =>
      if f = "full_fwd_dedup_bins" then
        ∃ (_ : as = [i64]) (h2 : bs = [.bool]), Q (h2 ▸ (false, ())) m
      else m6BveFwdEnv f as bs xs m Q X
    Func.wp Γ20 full_forward_sub_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => r = 20#64 ∧ nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState m')
      (fun _ _ _ _ => False) :=
  nv_m6_forward_sub_unsat20

theorem m6bf_nv_bve_gates :
    Func.wp m6BveFwdEnv full_bve_gates_m6_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, 0#32, 0#32, ()) FullM4Sweep.nvM4SweepMem
      (fun () m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_bve_gates

theorem m6bf_nv_bve_var :
    Func.wp m6BveFwdEnv full_bve_var_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_bve_var

theorem m6bf_nv_nbrs :
    Func.wp m6BveFwdEnv full_bve_collect_nbrs_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ())
      FullM4Sweep.nvM4SweepMem
      (fun (nn, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        nn.toNat ≤ 1 ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_bve_collect_nbrs

theorem m6bf_nv_elim_bve :
    Func.wp m6BveFwdEnv full_elim_bve_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, 100#64, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_elim_bve

theorem m6bf_nv_eliminate :
    Func.wp m6BveFwdEnv full_eliminate_m6_body (FullM4Sweep.nvM4SweepCfg.hdr, true, ())
      FullM4Sweep.nvM4SweepSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_eliminate

#print axioms m6bf_wf
#print axioms m6bf_acyc
#print axioms m6bf_tbl_len
#print axioms m6bf_nodup
#print axioms m6bf_noExit
#print axioms m6bf_sigs
#print axioms m6bf_ext_sigs
#print axioms m6bf_env_noExit
#print axioms m6bf_mod_ok
#print axioms m6bf_chk_canon_ok
#print axioms m6bf_fwd_wp
#print axioms m6bf_bve_var_wp
#print axioms m6bf_elim_bve_wp
#print axioms m6bf_eliminate_wp
#print axioms m6bf_nv_flush_units
#print axioms m6bf_nv_fwd_sub
#print axioms m6bf_nv_fwd_sub_20
#print axioms m6bf_nv_bve_gates
#print axioms m6bf_nv_bve_var
#print axioms m6bf_nv_nbrs
#print axioms m6bf_nv_elim_bve
#print axioms m6bf_nv_eliminate

end AxiomAudit
