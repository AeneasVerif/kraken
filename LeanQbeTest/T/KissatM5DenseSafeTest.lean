module

public import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof
public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
meta import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof
meta import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Splice Parity, Backend Guards, and Axiom Audit for Kissat M5 Wave 0B
(`FullM5DenseSafe`, covering `RC-02`, `RC-03`, `RC-04`)

1. Executable `#guard` checks on `m5DenseSafeModule` (`7` fns + `27` externs, `0` exits),
   `checkAcyclic = true`, `m5DenseSafeSpecTable` (`34` rows), exact signature parity and closed
   `231`-fn acyclicity when splicing all `7` drop-in handles (`m5EnterDenseFn..m5BvaCommitFn`)
   into `FullM4.m4Fns`, `PrintCpp`, `PrintQbe`, and `Fn.legal` across `aarch64`, `scalar64`,
   and `x64AVX2`.
2. Audit-ready restated headline theorems for `m5DenseSafe_fns_wf`, `m5DenseSafe_acyclic`, all
   `8` parametric `Func.wp` proofs, closed `34`-row `m5DenseSafe_moduleOk`, and concrete `Mem 64`
   UNSAT non-vacuity (`XPost := False`, `0` SAT proofs).
3. Single-line `< 115`-col `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

namespace M5DsAudit

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Examples.Kissat.FullM4Bva
open LeanQbe.T.Examples.Kissat.FullM5DenseSafe
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks, `FullM4` Splice Parity & Backend Compilation Guards -/

private def m5DenseSafeSpliceHandles : List Fn :=
  [ m5EnterDenseFn, m5SubstRewriteBinsFn, m5SubstRewriteArFn, m5SubstituteFn
  , m5FwdCheckClFn, m5BveVarFn, m5BvaCommitFn ]

private def spliceIntoM4 (fn : Fn) : Fn :=
  match m5DenseSafeSpliceHandles.find? (fun h => h.name == fn.name) with
  | some h => h
  | none => fn

private def splicedM4Module : LeanQbe.T.Module :=
  { fns := FullM4.m4Fns.map spliceIntoM4, externs := [], exits := [] }

#guard m5DenseSafeModule.checkAcyclic == true
#guard m5DenseSafeModule.exits.isEmpty
#guard m5DenseSafe_fns.length == 7
#guard m5DenseSafeExterns.length == 27
#guard m5DenseSafeSpecTable.length == 34
#guard m5DenseSafeSpliceHandles.all (fun h =>
  FullM4.m4Fns.any (fun f => f.name == h.name && f.as == h.as && f.rs == h.rs))
#guard splicedM4Module.fns.length == 231
#guard splicedM4Module.checkAcyclic == true
#guard (ppTModule m5DenseSafeModule).isOk
#guard (PrintQbe.module m5DenseSafeModule).isOk
#guard (ppModule (m5DenseSafe_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5DenseSafe_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5DenseSafe_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

/-- Every function in `m5DenseSafe_fns` (`7` upgraded M5 functions) is well-formed. -/
public theorem m5ds_wf : ∀ f ∈ m5DenseSafe_fns, f.Wf :=
  m5DenseSafe_fns_wf

/-- Standalone Wave-0B module `m5DenseSafeModule` passes `checkAcyclic = true`. -/
public theorem m5ds_acyc : m5DenseSafeModule.checkAcyclic = true :=
  m5DenseSafe_acyclic

/-- `full_enter_dense_m5` satisfies canonical `FullFastSched.schedEnterDenseSpec`. -/
public theorem m5ds_enter_dense_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X → Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, schedEnterDenseSpec a m Q X → Func.wp Γ full_enter_dense_m5_body a m Q X :=
  full_enter_dense_m5_wp Γ hBacktrack hProp hSweepBins hWatchPush hSweep hArenaNext

/-- `full_subst_rewrite_bins_m5` satisfies canonical `Full.fullSubstRewriteBinsSpec`. -/
public theorem m5ds_subst_bins_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Func.wp Γ full_subst_rewrite_bins_m5_body a m Q X :=
  full_subst_rewrite_bins_m5_wp Γ hAddUnit hAddBin

/-- `full_subst_rewrite_ar_m5` satisfies canonical `Full.fullSubstRewriteArSpec`. -/
public theorem m5ds_subst_ar_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSubstRewriteArSpec a m Q X →
      Func.wp Γ full_subst_rewrite_ar_m5_body a m Q X :=
  full_subst_rewrite_ar_m5_wp Γ hArenaNext hAddUnit hAddBin

/-- `full_substitute_m5` satisfies canonical `Full.fullSubstituteSpec`. -/
public theorem m5ds_substitute_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hTarjan : ∀ a m Q X, fullTarjanSccSpec a m Q X → Γ "full_tarjan_scc" [i64] [i64] a m Q X)
    (hElimVars : ∀ a m Q X, fullSubstElimVarsSpec a m Q X →
      Γ "full_subst_elim_vars" [i64, i64] [.bool] a m Q X)
    (hRewriteBins : ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Γ "full_subst_rewrite_bins" [i64] [.bool] a m Q X)
    (hRewriteAr : ∀ a m Q X, fullSubstRewriteArSpec a m Q X →
      Γ "full_subst_rewrite_ar" [i64] [.bool] a m Q X)
    (hArenaSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSubstituteSpec a m Q X → Func.wp Γ full_substitute_m5_body a m Q X :=
  full_substitute_m5_wp Γ hBacktrack hTarjan hElimVars hRewriteBins hRewriteAr hArenaSweep hProp

/-- `full_fwd_check_cl_m5` satisfies canonical `Full.fullFwdCheckClSpec`. -/
public theorem m5ds_fwd_check_wp (Γ : Env)
    (hUnwatchLarge : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullFwdCheckClSpec a m Q X → Func.wp Γ full_fwd_check_cl_m5_body a m Q X :=
  full_fwd_check_cl_m5_wp Γ hUnwatchLarge hAddUnit hAddBin

/-- `full_bve_var_m5` satisfies canonical `Full.fullBveVarSpec`. -/
public theorem m5ds_bve_var_wp (Γ : Env)
    (hDefrag : ∀ xs m Q X, fullWstackDefragSpec xs m Q X →
      Γ "full_wstack_defrag" [i64] [] xs m Q X)
    (hCollect : ∀ xs m Q X, fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (hExtNeed : ∀ xs m Q X, fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hWeaken : ∀ xs m Q X, fullBveWeakenSpec xs m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hSetInact : ∀ xs m Q X, fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (hGates : ∀ xs m Q X, fullBveGatesSpec xs m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] xs m Q X)
    (hResolve : ∀ xs m Q X, fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hCommitRes : ∀ xs m Q X, fullBveCommitResSpec xs m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] xs m Q X)
    (hTryBce : ∀ xs m Q X, fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2Spec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ a m Q X, fullBveVarSpec a m Q X → Func.wp Γ full_bve_var_m5_body a m Q X :=
  full_bve_var_m5_wp Γ hDefrag hCollect hExtNeed hWeaken hSetInact hGates hResolve hCommitRes
    hTryBce hExtPush2 hDelBin hExtPushCl

/-- `full_bve_var_m5` satisfies `TmkZero`-preserving `FullFastBveBudgets.fullBveVarDefSpec`. -/
public theorem m5ds_bve_var_def_wp (Γ : Env)
    (hDefrag : ∀ xs m Q X, fullWstackDefragSpec xs m Q X →
      Γ "full_wstack_defrag" [i64] [] xs m Q X)
    (hCollect : ∀ xs m Q X, fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (hExtNeed : ∀ xs m Q X, fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hWeaken : ∀ xs m Q X, fullBveWeakenTmkSpec xs m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hSetInact : ∀ xs m Q X, fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (hGates : ∀ xs m Q X, fullBveGatesDefFastSpec xs m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] xs m Q X)
    (hResolve : ∀ xs m Q X, fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hCommitRes : ∀ xs m Q X, fullBveCommitResTmkSpec xs m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] xs m Q X)
    (hTryBce : ∀ xs m Q X, fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2TmkSpec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClTmkSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ a m Q X, fullBveVarDefSpec a m Q X → Func.wp Γ full_bve_var_m5_body a m Q X :=
  full_bve_var_m5_def_wp Γ hDefrag hCollect hExtNeed hWeaken hSetInact hGates hResolve hCommitRes
    hTryBce hExtPush2 hDelBin hExtPushCl

/-- `full_bva_commit_m5` satisfies canonical `FullM4Bva.m4BvaCommitSpec`. -/
public theorem m5ds_bva_commit_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hInitFresh : ∀ a m Q X, fullInitFreshVarHeapSpec a m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAllocCl : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, m4BvaCommitSpec a m Q X → Func.wp Γ full_bva_commit_m5_body a m Q X :=
  full_bva_commit_m5_wp Γ hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch

/-- Closed `34`-row `ModuleOk` certifying `m5DenseSafeModule` under `m5DenseSafeEnv`. -/
public theorem m5ds_mod_ok : ModuleOk m5DenseSafeEnv m5DenseSafeModule :=
  m5DenseSafe_moduleOk

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_enter_dense_m5`. -/
public theorem m5ds_nv_enter :
    Func.wp m5DenseSafeEnv full_enter_dense_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (ok, ()) m' => ∃ s',
        (if ok then FullDenseInv nvOneLitCfg nvOneLitF0 s'
         else FullSparseInv nvOneLitCfg nvOneLitF0 s') ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_enter_dense

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_substitute_m5`. -/
public theorem m5ds_nv_subst :
    Func.wp m5DenseSafeEnv full_substitute_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_substitute

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bve_var_m5`. -/
public theorem m5ds_nv_bve :
    Func.wp m5DenseSafeEnv full_bve_var_m5_body (nvOneLitCfg.hdr, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_bve_var

/-- Concrete `Mem 64` `TmkZero` UNSAT non-vacuity (`XPost := False`) for `full_bve_var_m5`. -/
public theorem m5ds_nv_bve_def :
    let Γdef : Env := fun f as bs xs m Q X =>
      if f = "full_bve_gates" then
        ∃ (h1 : as = [i64, i32, i32, i32]) (h2 : bs = []),
          fullBveGatesDefFastSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_bve_weaken" then
        ∃ (h1 : as = [i64, i32, i32, i32]) (h2 : bs = [.bool]),
          fullBveWeakenTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_bve_commit_res" then
        ∃ (h1 : as = [i64, i64, i64]) (h2 : bs = [i64]),
          fullBveCommitResTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_extend_push2" then
        ∃ (h1 : as = [i64, i32, i32]) (h2 : bs = [.bool]),
          fullExtendPush2TmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_extend_push_cl" then
        ∃ (h1 : as = [i64, i32, i32]) (h2 : bs = [.bool]),
          fullExtendPushClTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else m5DenseSafeEnv f as bs xs m Q X
    Func.wp Γdef full_bve_var_m5_body (nvOneLitCfg.hdr, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_bve_var_def

end AuditSpec

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms m5ds_wf
#print axioms m5ds_acyc
#print axioms m5ds_enter_dense_wp
#print axioms m5ds_subst_bins_wp
#print axioms m5ds_subst_ar_wp
#print axioms m5ds_substitute_wp
#print axioms m5ds_fwd_check_wp
#print axioms m5ds_bve_var_wp
#print axioms m5ds_bve_var_def_wp
#print axioms m5ds_bva_commit_wp
#print axioms m5ds_mod_ok
#print axioms m5ds_nv_enter
#print axioms m5ds_nv_subst
#print axioms m5ds_nv_bve
#print axioms m5ds_nv_bve_def

end M5DsAudit
