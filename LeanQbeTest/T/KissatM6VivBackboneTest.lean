module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
meta import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Checks, & Axiom Audit for Kissat Wave-2 `PR-W2C` (`FullM6VivBackbone`)

1. Executable `#guard` checks on `m6VivBackboneModule` (`40` new functions + `15` canonical
   externs, `0` exits), `checkAcyclic = true`, `m6VivBackboneSpecTable` (`55` rows), `PrintCpp`,
   `PrintQbe`, and `Fn.legal` across `aarch64`, `scalar64`, and `x64AVX2`.
2. Audit-ready restated theorem types (every type written explicitly in full) for
   `m6VivBackbone_fns_wf`, `m6VivBackbone_acyclic`, `m6VivBackboneSpecTable_nodup`,
   `m6VivBackboneModule_noExit`, canonical drop-in parametric `Func.wp` theorems
   (`full_vivify_m6`, `full_backbone_m6`, `full_transitive_m6`, `full_probe_assume_pair_m6`,
   `full_add_bin_m6`, `full_init_fresh_var_m6`, `full_prioritize_binaries_m6`,
   `full_viv_clause_m6`), unconditional `m6VivBackbone_moduleOk : ModuleOk m6VivBackboneEnv
   m6VivBackboneModule`, and concrete `Mem 64` UNSAT non-vacuity theorems (`XPost := False`,
   `nvM6F0.Unsat`, `0` SAT model proofs).
3. Single-line `< 115`-col `#print axioms` audit on all `25` restated theorems (strictly
   `⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM6VivBackboneTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m6VivBackboneModule.checkAcyclic == true
#guard m6VivBackboneModule.exits.isEmpty
#guard m6VivBackbone_fns.length == 40
#guard m6VivBackboneExterns.length == 15
#guard m6VivBackboneSpecTable.length == 55
#guard (ppTModule m6VivBackboneModule).isOk
#guard (PrintQbe.module m6VivBackboneModule).isOk
#guard (ppModule (m6VivBackbone_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6VivBackbone_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6VivBackbone_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

/-- Every function in `m6VivBackbone_fns` (`40` Wave-2 `PR-W2C` functions) is well-formed. -/
theorem m6_wf : ∀ f ∈ m6VivBackbone_fns, f.Wf :=
  m6VivBackbone_fns_wf

/-- Standalone `PR-W2C` module `m6VivBackboneModule` passes `checkAcyclic = true`. -/
theorem m6_acyc : m6VivBackboneModule.checkAcyclic = true :=
  m6VivBackbone_acyclic

/-- Closed spec table has exactly `55` rows (`40` owned + `15` externs). -/
theorem m6_tbl_len : m6VivBackboneSpecTable.length = 55 :=
  m6VivBackboneSpecTable_length

/-- All `55` entries in `m6VivBackboneSpecTable` have pairwise distinct names (`Nodup`). -/
theorem m6_tbl_nd : (m6VivBackboneSpecTable.map SpecEntry.name).Nodup :=
  m6VivBackboneSpecTable_nodup

/-- Standalone `PR-W2C` module has zero exits (`noExit = true`). -/
theorem m6_no_exit : m6VivBackboneModule.exits = [] :=
  m6VivBackboneModule_noExit

/-- Unconditional closed `55`-row `ModuleOk` certifying all `40` `PR-W2C` functions. -/
theorem m6_mod_ok : ModuleOk m6VivBackboneEnv m6VivBackboneModule :=
  m6VivBackbone_moduleOk

/-- `full_vivify_m6` satisfies exact canonical `FullFastBveBudgets.fullVivifyFastSpec`. -/
theorem m6_viv_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
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
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullVivifyFastSpec a m Q X →
      Func.wp Γ full_vivify_m6_body a m Q X :=
  full_vivify_m6_wp Γ hBacktrack hCollect hCount hKeys hSortSched hVivClause hProp hClearTier

/-- `full_backbone_m6` satisfies exact canonical `FullM3Backbone.fullBackboneSpec`. -/
theorem m6_bb_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSched : ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Γ "full_backbone_sched_m6" [i64] [i64] a m Q X)
    (hRound : ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
      Γ "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X)
    (hKeep : ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Γ "full_backbone_keep_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Func.wp Γ full_backbone_m6_body a m Q X :=
  full_backbone_m6_wp Γ hBacktrack hProp hAddUnit hPrio hSched hRound hKeep

/-- `full_transitive_m6` satisfies exact canonical `FullFastBveBudgets.fullTransitiveFastSpec`. -/
theorem m6_tr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSort : ∀ a m Q X, fullTransSortM6Spec a m Q X →
      Γ "full_trans_sort_m6" [i64, i64] [] a m Q X)
    (hTransLit : ∀ a m Q X, fullTransLitM6Spec a m Q X →
      Γ "full_trans_lit_m6" [i64, i32, .bool] [.bool] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Func.wp Γ full_transitive_m6_body a m Q X :=
  full_transitive_m6_wp Γ hBacktrack hPrio hSort hTransLit hProp hDefrag

/-- `full_probe_assume_pair_m6` satisfies exact canonical `Full.fullProbeAssumePairSpec`. -/
theorem m6_pr_wp (Γ : Env)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProbeProp : ∀ a m Q X, FullProbeTransSpecs.fullProbePropExtSpec a m Q X →
      Γ "full_probe_prop" [i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAnalyze : ∀ a m Q X, FullProbeTransSpecs.fullAnalyze20Spec a m Q X →
      Γ "full_analyze" [i64] [i64] a m Q X)
    (hPropagate : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hFlushHbr : ∀ a m Q X, FullProbeTransSpecs.fullProbeFlushHbrSpec a m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullProbeAssumePairSpec a m Q X →
      Func.wp Γ full_probe_assume_pair_m6_body a m Q X :=
  full_probe_assume_pair_m6_canon_wp Γ hAssign hProbeProp hBacktrack hAnalyze hPropagate
    hFlushHbr hAddUnit

/-- `full_add_bin_m6` satisfies exact canonical `Full.fullAddBinSpec`. -/
theorem m6_ab_wp (Γ : Env)
    (hHas : ∀ a m Q X, Full.fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hAlvl : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hWpush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullAddBinSpec a m Q X →
      Func.wp Γ full_add_bin_m6_body a m Q X :=
  full_add_bin_m6_wp Γ hHas hAlvl hWpush

/-- `full_init_fresh_var_m6` satisfies exact canonical `Full.fullInitFreshVarSpec`. -/
theorem m6_ifv_wp (Γ : Env) :
    ∀ a m Q X, Full.fullInitFreshVarSpec a m Q X →
      Func.wp Γ full_init_fresh_var_m6_body a m Q X :=
  full_init_fresh_var_m6_wp Γ

/-- `full_init_fresh_var_m6` satisfies `FullBvaHeap.fullInitFreshVarHeapSpec`. -/
theorem m6_ifvh_wp (Γ : Env) :
    ∀ a m Q X, FullBvaHeap.fullInitFreshVarHeapSpec a m Q X →
      Func.wp Γ full_init_fresh_var_m6_body a m Q X :=
  full_init_fresh_var_m6_heap_wp Γ

/-- `full_prioritize_binaries_m6` satisfies `fullPrioritizeBinariesM6Spec`. -/
theorem m6_prio_wp (Γ : Env) :
    ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Func.wp Γ full_prioritize_binaries_m6_body a m Q X :=
  full_prioritize_binaries_m6_wp Γ

/-- `full_viv_clause_m6` satisfies `fullVivClauseM6Spec`. -/
theorem m6_vcl_wp (Γ : Env)
    (hL0Simp : ∀ a m Q X, fullVivL0SimpM6Spec a m Q X →
      Γ "full_viv_l0_simp_m6" [i64, i32, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortCountsM6Spec a m Q X →
      Γ "full_viv_sort_counts_m6" [i64, i32] [] a m Q X)
    (hReuse : ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
      Γ "full_viv_reuse_prefix_m6" [i64, i32, i32] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFinish : ∀ a m Q X, fullVivFinishM6Spec a m Q X →
      Γ "full_viv_finish_m6" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Func.wp Γ full_viv_clause_m6_body a m Q X :=
  full_viv_clause_m6_wp Γ hL0Simp hSort hReuse hBestImpl hAssign hPropIgn hBacktrack hFinish

/-- Concrete UNSAT formula witness `{(x0), (¬x0)}` is unsatisfiable. -/
theorem m6_nv_unsat : nvM6F0.Unsat :=
  nvM6F0_unsat

/-- Concrete `2588`-byte heap satisfies `FullMem nvM6Cfg nvM6SparseState nvM6SparseMem`. -/
theorem m6_nv_mem : FullMem nvM6Cfg nvM6SparseState nvM6SparseMem :=
  nvM6SparseMem_ok

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_vivify_m6`. -/
theorem m6_nv_viv :
    Func.wp m6VivBackboneEnv full_vivify_m6_body (nvM6Cfg.hdr, 0#64, 10#64, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM6Cfg nvM6F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_vivify

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_backbone_m6`. -/
theorem m6_nv_bb :
    Func.wp m6VivBackboneEnv full_backbone_m6_body (nvM6Cfg.hdr, 10#64, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM6Cfg nvM6F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_backbone

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_transitive_m6`. -/
theorem m6_nv_tr :
    Func.wp m6VivBackboneEnv full_transitive_m6_body (nvM6Cfg.hdr, 10#64, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM6Cfg nvM6F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_transitive

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_probe_assume_pair_m6`. -/
theorem m6_nv_pr :
    Func.wp m6VivBackboneEnv full_probe_assume_pair_m6_body (nvM6Cfg.hdr, 0#32, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_probe_assume_pair

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_add_bin_m6`. -/
theorem m6_nv_ab :
    Func.wp m6VivBackboneEnv full_add_bin_m6_body (nvM6Cfg.hdr, 0#32, 2#32, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullWitnessInv nvM6Cfg nvM6F0 [[0], [1]] s'.core ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_add_bin

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_init_fresh_var_m6`. -/
theorem m6_nv_ifv :
    Func.wp m6VivBackboneEnv full_init_fresh_var_m6_body (nvM6Cfg.hdr, 0#32, ()) nvM6SparseMem
      (fun () m' => ∃ s', s'.LengthsOk nvM6Cfg ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_init_fresh_var

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_prioritize_binaries_m6`. -/
theorem m6_nv_prio :
    Func.wp m6VivBackboneEnv full_prioritize_binaries_m6_body (nvM6Cfg.hdr, ()) nvM6SparseMem
      (fun (_ok, ()) m' => ∃ s',
        FullSparseInvW nvM6Cfg nvM6F0 [[0], [1]] s' ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_prioritize_binaries

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_clause_m6`. -/
theorem m6_nv_vcl :
    Func.wp m6VivBackboneEnv full_viv_clause_m6_body (nvM6Cfg.hdr, 0#32, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM6Cfg nvM6F0 [[0], [1]] s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_viv_clause

end AuditSpec

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms m6_wf
#print axioms m6_acyc
#print axioms m6_tbl_len
#print axioms m6_tbl_nd
#print axioms m6_no_exit
#print axioms m6_mod_ok
#print axioms m6_viv_wp
#print axioms m6_bb_wp
#print axioms m6_tr_wp
#print axioms m6_pr_wp
#print axioms m6_ab_wp
#print axioms m6_ifv_wp
#print axioms m6_ifvh_wp
#print axioms m6_prio_wp
#print axioms m6_vcl_wp
#print axioms m6_nv_unsat
#print axioms m6_nv_mem
#print axioms m6_nv_viv
#print axioms m6_nv_bb
#print axioms m6_nv_tr
#print axioms m6_nv_pr
#print axioms m6_nv_ab
#print axioms m6_nv_ifv
#print axioms m6_nv_prio
#print axioms m6_nv_vcl

end LeanQbeTest.T.KissatM6VivBackboneTest
