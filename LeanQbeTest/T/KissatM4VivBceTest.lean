module

public import LeanQbe.T.Examples.Kissat.FullM4VivBce
public import LeanQbe.T.Examples.Kissat.FullM4VivBceProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM4VivBce
meta import LeanQbe.T.Examples.Kissat.FullM4VivBceProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Checks, and Axiom Audit for Kissat M4f (`FullM4VivBce`)

1. Executable `#guard` checks on `m4VivBceModule` (`16` new functions + `15` canonical externs,
   `0` exits), `checkAcyclic = true`, `m4VivBceSpecTable` (`31` rows), `PrintCpp`, `PrintQbe`,
   and `Fn.legal` across `aarch64`, `scalar64`, and `x64AVX2`.
2. Audit-ready restated theorem types (every type written explicitly in full) for `m4VivBce_fns_wf`,
   `m4VivBce_acyclic`, `full_viv_simplify_m4_wp`, `full_viv_commit_m4_wp`, all `16` parametric
   `Func.wp` UNSAT-soundness theorems (with `full_vivify_m4` matching canonical
   `FullFastBveBudgets.fullVivifyFastSpec`), `m4VivBce_moduleOk : ModuleOk m4VivBceEnv
   m4VivBceModule`, and all `16` concrete `Mem 64` UNSAT non-vacuity theorems (`nv_m4_*`,
   `XPost := False`, `0` SAT model proofs).
3. Single-line `< 115`-col `#print axioms` audit on all `37` restated theorems (strictly
   `⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM4VivBceTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4VivBce
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m4VivBceModule.checkAcyclic == true
#guard m4VivBceModule.exits.isEmpty
#guard m4VivBce_fns.length == 16
#guard m4VivBceExterns.length == 15
#guard m4VivBceSpecTable.length == 31
#guard (ppTModule m4VivBceModule).isOk
#guard (PrintQbe.module m4VivBceModule).isOk
#guard (ppModule (m4VivBce_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m4VivBce_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m4VivBce_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

/-- Every function in `m4VivBce_fns` (`16` M4f functions) is well-formed. -/
theorem m4f_wf : ∀ f ∈ m4VivBce_fns, f.Wf :=
  m4VivBce_fns_wf

/-- Standalone M4f module `m4VivBceModule` passes `checkAcyclic = true`. -/
theorem m4f_acyc : m4VivBceModule.checkAcyclic = true :=
  m4VivBce_acyclic

/-- Unmodified `Full3.full_viv_simplify_body` preserves `red_refs` under canonical callees. -/
theorem m4f_vsimp_wp (Γ : Env)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, Full.fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullVivSimplifyM4Spec a m Q X →
      Func.wp Γ Full.full_viv_simplify_body a m Q X :=
  full_viv_simplify_m4_wp Γ hUnwatch hAddUnit hAddBin hWatchPush

/-- Unmodified `Full3.full_viv_commit_body` preserves `red_refs` under canonical callees. -/
theorem m4f_vcom_wp (Γ : Env)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, Full.fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullVivCommitM4Spec a m Q X →
      Func.wp Γ Full.full_viv_commit_body a m Q X :=
  full_viv_commit_m4_wp Γ hUnwatch hAddUnit hAddBin hWatchPush

/-- `full_viv_sort_noccs_m4` satisfies `fullVivSortNoccsM4Spec` parametrically in `Γ`. -/
theorem m4f_snoc_wp (Γ : Env) :
    ∀ a m Q X, fullVivSortNoccsM4Spec a m Q X →
      Func.wp Γ full_viv_sort_noccs_m4_body a m Q X :=
  full_viv_sort_noccs_m4_wp Γ

/-- `full_viv_has_l0_m4` satisfies `fullVivHasL0M4Spec` parametrically in `Γ`. -/
theorem m4f_l0_wp (Γ : Env) :
    ∀ a m Q X, fullVivHasL0M4Spec a m Q X → Func.wp Γ full_viv_has_l0_m4_body a m Q X :=
  full_viv_has_l0_m4_wp Γ

/-- `full_viv_l0_simp_m4` satisfies `fullVivL0SimpM4Spec` parametrically in `Γ`. -/
theorem m4f_l0s_wp (Γ : Env)
    (hHasL0 : ∀ a m Q X, fullVivHasL0M4Spec a m Q X →
      Γ "full_viv_has_l0_m4" [i64, i32, i32] [.bool] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSimplify : ∀ a m Q X, fullVivSimplifyM4Spec a m Q X →
      Γ "full_viv_simplify" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullVivL0SimpM4Spec a m Q X → Func.wp Γ full_viv_l0_simp_m4_body a m Q X :=
  full_viv_l0_simp_m4_wp Γ hHasL0 hBacktrack hSimplify

/-- `full_viv_reuse_prefix_m4` satisfies `fullVivReusePrefixM4Spec` parametrically in `Γ`. -/
theorem m4f_pref_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullVivReusePrefixM4Spec a m Q X →
      Func.wp Γ full_viv_reuse_prefix_m4_body a m Q X :=
  full_viv_reuse_prefix_m4_wp Γ hBacktrack

/-- `full_viv_finish_m4` satisfies `fullVivFinishM4Spec` parametrically in `Γ`. -/
theorem m4f_fin_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hDeduce : ∀ a m Q X, Full.fullVivDeduceSpec a m Q X →
      Γ "full_viv_deduce" [i64, i32, i32, i64] [i32] a m Q X)
    (hCommit : ∀ a m Q X, fullVivCommitM4Spec a m Q X →
      Γ "full_viv_commit" [i64, i32, i64, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivFinishM4Spec a m Q X → Func.wp Γ full_viv_finish_m4_body a m Q X :=
  full_viv_finish_m4_wp Γ hBacktrack hDeduce hCommit

/-- `full_viv_clause_m4` satisfies `fullVivClauseM4Spec` parametrically in `Γ`. -/
theorem m4f_vcl_wp (Γ : Env)
    (hL0Simp : ∀ a m Q X, fullVivL0SimpM4Spec a m Q X →
      Γ "full_viv_l0_simp_m4" [i64, i32, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortNoccsM4Spec a m Q X →
      Γ "full_viv_sort_noccs_m4" [i64, i32] [] a m Q X)
    (hReuse : ∀ a m Q X, fullVivReusePrefixM4Spec a m Q X →
      Γ "full_viv_reuse_prefix_m4" [i64, i32, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFinish : ∀ a m Q X, fullVivFinishM4Spec a m Q X →
      Γ "full_viv_finish_m4" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivClauseM4Spec a m Q X → Func.wp Γ full_viv_clause_m4_body a m Q X :=
  full_viv_clause_m4_wp Γ hL0Simp hSort hReuse hAssign hPropIgn hBacktrack hFinish

/-- `full_viv_sort_sched_m4` satisfies `fullVivSortSchedM4Spec` parametrically in `Γ`. -/
theorem m4f_ssch_wp (Γ : Env) :
    ∀ a m Q X, fullVivSortSchedM4Spec a m Q X →
      Func.wp Γ full_viv_sort_sched_m4_body a m Q X :=
  full_viv_sort_sched_m4_wp Γ

/-- `full_viv_tier_match_m4` satisfies `fullVivTierMatchM4Spec` parametrically in `Γ`. -/
theorem m4f_tm_wp (Γ : Env) :
    ∀ a m Q X, fullVivTierMatchM4Spec a m Q X →
      Func.wp Γ full_viv_tier_match_m4_body a m Q X :=
  full_viv_tier_match_m4_wp Γ

/-- `full_viv_collect_m4` satisfies `fullVivCollectM4Spec` parametrically in `Γ`. -/
theorem m4f_col_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM4Spec a m Q X →
      Γ "full_viv_tier_match_m4" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullVivCollectM4Spec a m Q X →
      Func.wp Γ full_viv_collect_m4_body a m Q X :=
  full_viv_collect_m4_wp Γ hNext hTierMatch

/-- `full_viv_keys_m4` satisfies `fullVivKeysM4Spec` parametrically in `Γ`. -/
theorem m4f_key_wp (Γ : Env) :
    ∀ a m Q X, fullVivKeysM4Spec a m Q X →
      Func.wp Γ full_viv_keys_m4_body a m Q X :=
  full_viv_keys_m4_wp Γ

/-- `full_viv_clear_tier_m4` satisfies `fullVivClearTierM4Spec` parametrically in `Γ`. -/
theorem m4f_ct_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM4Spec a m Q X →
      Γ "full_viv_tier_match_m4" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullVivClearTierM4Spec a m Q X →
      Func.wp Γ full_viv_clear_tier_m4_body a m Q X :=
  full_viv_clear_tier_m4_wp Γ hNext hTierMatch

/-- `full_vivify_m4` satisfies canonical `FullFastBveBudgets.fullVivifyFastSpec` parametrically in
`Γ`. -/
theorem m4f_viv_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM4Spec a m Q X →
      Γ "full_viv_collect_m4" [i64, i64] [i64] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM4Spec a m Q X →
      Γ "full_viv_keys_m4" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM4Spec a m Q X →
      Γ "full_viv_sort_sched_m4" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM4Spec a m Q X →
      Γ "full_viv_clause_m4" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM4Spec a m Q X →
      Γ "full_viv_clear_tier_m4" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullVivifyFastSpec a m Q X →
      Func.wp Γ full_vivify_m4_body a m Q X :=
  full_vivify_m4_wp Γ hBacktrack hCollect hKeys hSortSched hVivClause hProp hClearTier

/-- `full_bce_side_m4` satisfies `fullBceSideM4Spec` parametrically in `Γ`. -/
theorem m4f_bs_wp (Γ : Env)
    (hTryBce : ∀ a m Q X, Full.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hExtPush2 : ∀ a m Q X, Full.fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hExtPushCl : ∀ a m Q X, Full.fullExtendPushClSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBceSideM4Spec a m Q X → Func.wp Γ full_bce_side_m4_body a m Q X :=
  full_bce_side_m4_wp Γ hTryBce hExtPush2 hExtPushCl hDelBin

/-- `full_bce_pair_m4` satisfies `fullBcePairM4Spec` parametrically in `Γ`. -/
theorem m4f_bp_wp (Γ : Env)
    (hSide : ∀ a m Q X, fullBceSideM4Spec a m Q X →
      Γ "full_bce_side_m4" [i64, i32, i32, i32, i32, i32] [i32] a m Q X) :
    ∀ a m Q X, fullBcePairM4Spec a m Q X → Func.wp Γ full_bce_pair_m4_body a m Q X :=
  full_bce_pair_m4_wp Γ hSide

/-- `full_bce_var_m4` satisfies `fullBceVarM4Spec` parametrically in `Γ`. -/
theorem m4f_bv_wp (Γ : Env)
    (hCollect : ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] a m Q X)
    (hPair : ∀ a m Q X, fullBcePairM4Spec a m Q X →
      Γ "full_bce_pair_m4" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBceVarM4Spec a m Q X → Func.wp Γ full_bce_var_m4_body a m Q X :=
  full_bce_var_m4_wp Γ hCollect hPair

/-- `full_bce_m4` satisfies `fullBceM4Spec` parametrically in `Γ`. -/
theorem m4f_bce_wp (Γ : Env)
    (hEnterDense : ∀ a m Q X, Full.fullEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hBceVar : ∀ a m Q X, fullBceVarM4Spec a m Q X →
      Γ "full_bce_var_m4" [i64, i32] [] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullBceM4Spec a m Q X → Func.wp Γ full_bce_m4_body a m Q X :=
  full_bce_m4_wp Γ hEnterDense hBceVar hRebuild hProp

/-- Closed `31`-row `ModuleOk` certifying all `16` M4f functions under `m4VivBceEnv`. -/
theorem m4f_mod_ok : ModuleOk m4VivBceEnv m4VivBceModule :=
  m4VivBce_moduleOk

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_sort_noccs_m4`. -/
theorem m4f_nv_sn :
    Func.wp m4VivBceEnv full_viv_sort_noccs_m4_body (nvM4Cfg.hdr, 3#32, ()) nvM4SparseMem
      (fun () m' => ∃ tmp',
        tmp'.length = 3 ∧ (tmp'.take 3).Perm (nvM4SparseState.core.tmp.take 3) ∧
        nvM4F0.Unsat ∧
        FullMem nvM4Cfg
          { nvM4SparseState with core := { nvM4SparseState.core with tmp := tmp' } } m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_sort_noccs

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_has_l0_m4`. -/
theorem m4f_nv_l0 :
    Func.wp m4VivBceEnv full_viv_has_l0_m4_body (nvM4Cfg.hdr, 0#32, 3#32, ()) nvM4SparseMem
      (fun (_r, ()) m' => nvM4F0.Unsat ∧ FullMem nvM4Cfg nvM4SparseState m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_has_l0

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_l0_simp_m4`. -/
theorem m4f_nv_l0s :
    Func.wp m4VivBceEnv full_viv_l0_simp_m4_body (nvM4Cfg.hdr, 0#32, 3#32, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_l0_simp

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_reuse_prefix_m4`. -/
theorem m4f_nv_pr :
    Func.wp m4VivBceEnv full_viv_reuse_prefix_m4_body (nvM4Cfg.hdr, 0#32, 3#32, ()) nvM4SparseMem
      (fun () m' => ∃ s',
        FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧
        s'.core.tmp = nvM4SparseState.core.tmp ∧
        nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_reuse_prefix

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_finish_m4`. -/
theorem m4f_nv_fn :
    Func.wp m4VivBceEnv full_viv_finish_m4_body
      (nvM4Cfg.hdr, 0#32, 3#32, false, 0xFFFFFFFF#32, false, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_finish

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_clause_m4`. -/
theorem m4f_nv_vc :
    Func.wp m4VivBceEnv full_viv_clause_m4_body (nvM4Cfg.hdr, 0#32, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_clause

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_sort_sched_m4`. -/
theorem m4f_nv_ss :
    Func.wp m4VivBceEnv full_viv_sort_sched_m4_body (nvM4Cfg.hdr, 0#64, ()) nvM4SparseMem
      (fun () m' => ∃ rr',
        rr'.length = 0 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg
          { nvM4SparseState with scratch := { nvM4SparseState.scratch with red_refs := rr' } } m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_sort_sched

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_tier_match_m4`. -/
theorem m4f_nv_tm :
    Func.wp m4VivBceEnv full_viv_tier_match_m4_body (nvM4Cfg.hdr, 0#32, 0#64, ()) nvM4SparseMem
      (fun (_r, ()) m' => nvM4F0.Unsat ∧ FullMem nvM4Cfg nvM4SparseState m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_tier_match

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_collect_m4`. -/
theorem m4f_nv_cl :
    Func.wp m4VivBceEnv full_viv_collect_m4_body (nvM4Cfg.hdr, 0#64, ()) nvM4SparseMem
      (fun (bn, ()) m' => ∃ tr' rr',
        bn = 0#64 ∧ tr'.length = 6 ∧ rr'.length = 0 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg
          { nvM4SparseState with
            scratch := { nvM4SparseState.scratch with tarjan_reach := tr', red_refs := rr' } } m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_collect

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_keys_m4`. -/
theorem m4f_nv_ky :
    Func.wp m4VivBceEnv full_viv_keys_m4_body (nvM4Cfg.hdr, 0#64, ()) nvM4SparseMem
      (fun () m' => ∃ rr',
        rr'.length = 0 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg
          { nvM4SparseState with scratch := { nvM4SparseState.scratch with red_refs := rr' } } m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_keys

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_clear_tier_m4`. -/
theorem m4f_nv_ct :
    Func.wp m4VivBceEnv full_viv_clear_tier_m4_body (nvM4Cfg.hdr, 0#64, ()) nvM4SparseMem
      (fun () m' => ∃ s',
        FullSparseInv nvM4Cfg nvM4F0 s' ∧ s'.core.cur_level = 0 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_viv_clear_tier

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_vivify_m4`. -/
theorem m4f_nv_vv :
    Func.wp m4VivBceEnv full_vivify_m4_body (nvM4Cfg.hdr, 0#64, 10#64, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM4Cfg nvM4F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_vivify

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bce_side_m4`. -/
theorem m4f_nv_bs :
    Func.wp m4VivBceEnv full_bce_side_m4_body (nvM4Cfg.hdr, 1#32, 64#32, 0#32, 0#32, 0#32, ())
      nvM4DenseMem
      (fun (rem, ()) m' => ∃ s',
        FullDenseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧ rem = 0#32 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_bce_side

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bce_pair_m4`. -/
theorem m4f_nv_bp :
    Func.wp m4VivBceEnv full_bce_pair_m4_body (nvM4Cfg.hdr, 0#32, 0#32, 0#32, ()) nvM4DenseMem
      (fun () m' => ∃ s',
        FullDenseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_bce_pair

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bce_var_m4`. -/
theorem m4f_nv_bv :
    Func.wp m4VivBceEnv full_bce_var_m4_body (nvM4Cfg.hdr, 0#32, ()) nvM4DenseMem
      (fun () m' => ∃ s',
        FullDenseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_bce_var

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bce_m4`. -/
theorem m4f_nv_bc :
    Func.wp m4VivBceEnv full_bce_m4_body (nvM4Cfg.hdr, 10#64, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM4Cfg nvM4F0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_bce

end AuditSpec

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms m4f_wf
#print axioms m4f_acyc
#print axioms m4f_vsimp_wp
#print axioms m4f_vcom_wp
#print axioms m4f_snoc_wp
#print axioms m4f_l0_wp
#print axioms m4f_l0s_wp
#print axioms m4f_pref_wp
#print axioms m4f_fin_wp
#print axioms m4f_vcl_wp
#print axioms m4f_ssch_wp
#print axioms m4f_tm_wp
#print axioms m4f_col_wp
#print axioms m4f_key_wp
#print axioms m4f_ct_wp
#print axioms m4f_viv_wp
#print axioms m4f_bs_wp
#print axioms m4f_bp_wp
#print axioms m4f_bv_wp
#print axioms m4f_bce_wp
#print axioms m4f_mod_ok
#print axioms m4f_nv_sn
#print axioms m4f_nv_l0
#print axioms m4f_nv_l0s
#print axioms m4f_nv_pr
#print axioms m4f_nv_fn
#print axioms m4f_nv_vc
#print axioms m4f_nv_ss
#print axioms m4f_nv_tm
#print axioms m4f_nv_cl
#print axioms m4f_nv_ky
#print axioms m4f_nv_ct
#print axioms m4f_nv_vv
#print axioms m4f_nv_bs
#print axioms m4f_nv_bp
#print axioms m4f_nv_bv
#print axioms m4f_nv_bc

end LeanQbeTest.T.KissatM4VivBceTest
