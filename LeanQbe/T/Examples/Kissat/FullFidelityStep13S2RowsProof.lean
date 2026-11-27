/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatchProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatchProof2d
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof0a
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof0b2
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof0c
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof2
public import LeanQbe.T.Examples.Kissat.FullSpec

/-!
# Kissat Fidelity Step 13 Shard S2 Proof Rows & Parametric `Impl` Barrel
(`FullFidelityStep13S2RowsProof`)

Exports the `8` replacement specification rows (`fidStep13S2ReplRows`), the `2` inserted-helper
specification rows (`fidStep13S2BeforeRows`), name/signature/`noExit` alignment theorems,
`10/10` kernel-checked `checkCallsOk` certificates, and `10/10` parametric `SpecEntry.Impl` lemmas
(`0` `import all`, `0` `@[expose]` on theorems/lemmas, `0` new `FullWitnessInv` conjuncts,
`XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7V2Robust
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- The `8` sig-preserving replacement specification rows aligned 1-to-1 with
`fidStep13S2Repls`. -/
def fidStep13S2ReplRows : List SpecEntry :=
  [ ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_propagate_ignore_hot", [i64, i64], [i64], step13PropagateIgnoreM6Spec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], step13PropagateIgnoreM6Spec, true⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool], step13OtfsLargeSpec, true⟩
  , ⟨"full_one_lit_confl", [i64], [i64], Full.fullOneLitConflSpec, true⟩
  , ⟨"full_eager_subsume", [i64, i64], [], step13EagerSubsumeSpec, true⟩
  , ⟨"full_learn_clause_m6", [i64, i64], [i64], step13LearnClauseM6Spec, true⟩ ]

/-- The `2` inserted-helper specification rows aligned 1-to-1 with
`fidStep13S2Befores.flatMap Prod.snd`. -/
def fidStep13S2BeforeRows : List SpecEntry :=
  [ ⟨"full_update_classify_fid", [i64], [], step13UpdateClassifyM6Spec, true⟩
  , ⟨"full_propagate_beyond_m7", [i64], [i64], step13PropagateBeyondM6Spec, true⟩ ]

end

public section

/-! ## 1. Name, Signature, & `noExit` Alignment -/

theorem fidStep13S2ReplRows_names :
    fidStep13S2ReplRows.map SpecEntry.name = fidStep13S2ReplNames :=
  rfl

theorem fidStep13S2ReplRows_sigs :
    fidStep13S2ReplRows.map (fun e => (e.name, e.as, e.rs)) = fidStep13S2Repls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S2ReplRows_noExit :
    fidStep13S2ReplRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep13S2BeforeRows_names :
    fidStep13S2BeforeRows.map SpecEntry.name = fidStep13S2BeforeNames :=
  rfl

theorem fidStep13S2BeforeRows_sigs :
    fidStep13S2BeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (fidStep13S2Befores.flatMap Prod.snd).map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S2BeforeRows_noExit :
    fidStep13S2BeforeRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

/-! ## 2. Per-Function `checkCallsOk` (`10/10`) -/

theorem full_watch_push_slow_m6_s13_callsOk :
    fidStep13S2WatchPushSlowM6Fn.checkCallsOk
      [ ("full_wstack_defrag_m6", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_watch_push_m6_s13_callsOk :
    fidStep13S2WatchPushM6Fn.checkCallsOk
      [ ("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_propagate_ignore_hot_s13_callsOk :
    fidStep13S2PropIgnoreHotFn.checkCallsOk
      [ ("m6_wm4_get", [i64], [i64])
      , ("m6_hdr_add_ticks", [i64, i64], [])
      , ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
      , ("full_prop_flush_del_fid", [i64, i64], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_propagate_ignore_s13_callsOk :
    fidStep13S2PropIgnoreFn.checkCallsOk
      [ ("m6_wm4_get", [i64], [i64])
      , ("m6_hdr_add_ticks", [i64, i64], [])
      , ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
      , ("full_prop_flush_del_fid", [i64, i64], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_otfs_large_s13_callsOk :
    fidStep13S2OtfsLargeFn.checkCallsOk
      [ ("full_wstack_defrag", [i64], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
      , ("full_unwatch_large", [i64, i32, i32], []) ] [] = true := by
  t_kernel_rfl

theorem full_one_lit_confl_s13_callsOk :
    fidStep13S2OneLitConflFn.checkCallsOk
      [ ("full_wstack_defrag", [i64], [])
      , ("full_det_new_level", [i64, i64], [i64])
      , ("full_backtrack_ac_fid", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_unwatch_large", [i64, i32, i32], [])
      , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by
  t_kernel_rfl

theorem full_eager_subsume_s13_callsOk :
    fidStep13S2EagerSubsumeFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem full_learn_clause_m6_s13_callsOk :
    fidStep13S2LearnClauseM6Fn.checkCallsOk
      [ ("full_backtrack_ac_fid", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_det_new_level", [i64, i64], [i64])
      , ("full_wstack_defrag", [i64], [])
      , ("full_reduce_m6", [i64, .bool], [i64])
      , ("full_reduce_purge_c0", [i64], [i64])
      , ("full_add_clause", [i64, i32, i32, .bool], [i64])
      , ("full_eager_subsume", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_update_classify_fid_s13_callsOk :
    fidStep13S2UpdateClassifyFn.checkCallsOk
      [ ("m6_wm4_get", [i64], [i64])
      , ("m6_wm4_set", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem full_propagate_beyond_m7_s13_callsOk :
    fidStep13S2PropBeyondM7Fn.checkCallsOk
      [ ("m6_wm4_get", [i64], [i64])
      , ("m6_hdr_add_ticks", [i64, i64], [])
      , ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
      , ("full_prop_flush_del_fid", [i64, i64], [.bool]) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `SpecEntry.Impl` Lemmas (`10/10`) -/

theorem full_watch_push_slow_m6_s13_impl (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag_m6" [i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S2WatchPushSlowM6Fn (fidStep13S2ReplRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_watch_push_slow_m6_step13_wp Γ hDefrag)

theorem full_watch_push_m6_s13_impl (Γ : Env)
    (hSlow : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_slow_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S2WatchPushM6Fn (fidStep13S2ReplRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_watch_push_m6_step13_wp Γ hSlow)

theorem full_propagate_ignore_hot_s13_impl (Γ : Env)
    (hWm4Get : ∀ args m Q X, step13Wm4GetSpec args m Q X →
      Γ "m6_wm4_get" [i64] [i64] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, FullFidelityBcp.fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X) :
    SpecEntry.Impl Γ fidStep13S2PropIgnoreHotFn (fidStep13S2ReplRows[2]'(by decide)) :=
  SpecEntry.Impl.of (full_propagate_ignore_hot_step13_wp Γ hWm4Get hAddTicks hOvf hFlush)

theorem full_propagate_ignore_s13_impl (Γ : Env)
    (hWm4Get : ∀ args m Q X, step13Wm4GetSpec args m Q X →
      Γ "m6_wm4_get" [i64] [i64] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, FullFidelityBcp.fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X) :
    SpecEntry.Impl Γ fidStep13S2PropIgnoreFn (fidStep13S2ReplRows[3]'(by decide)) :=
  SpecEntry.Impl.of (full_propagate_ignore_step13_wp Γ hWm4Get hAddTicks hOvf hFlush)

theorem full_otfs_large_s13_impl (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    SpecEntry.Impl Γ fidStep13S2OtfsLargeFn (fidStep13S2ReplRows[4]'(by decide)) :=
  SpecEntry.Impl.of (full_otfs_large_step13_wp Γ hDefrag hUnw hPush)

theorem full_one_lit_confl_s13_impl (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hDet : ∀ args m Q X, Full.fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hUnw : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    SpecEntry.Impl Γ fidStep13S2OneLitConflFn (fidStep13S2ReplRows[5]'(by decide)) :=
  SpecEntry.Impl.of (full_one_lit_confl_step13_wp Γ hDefrag hDet hBt hAss hUnw hPush)

theorem full_eager_subsume_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ fidStep13S2EagerSubsumeFn (fidStep13S2ReplRows[6]'(by decide)) :=
  SpecEntry.Impl.of (full_eager_subsume_step13_wp Γ)

theorem full_learn_clause_m6_s13_impl (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, step13ReduceM6Spec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hRedPurge : ∀ a m Q X, step13ReducePurgeC0M6Spec a m Q X →
      Γ "full_reduce_purge_c0" [i64] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, step13AddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, step13EagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S2LearnClauseM6Fn (fidStep13S2ReplRows[7]'(by decide)) :=
  SpecEntry.Impl.of
    (full_learn_clause_m6_step13_wp Γ hBt hAsgn hDnl hDefrag hRedM6 hRedPurge hAddCl hEsub)

theorem full_update_classify_fid_s13_impl (Γ : Env)
    (hGet : ∀ a m Q X, step13Wm4GetSpec a m Q X → Γ "m6_wm4_get" [i64] [i64] a m Q X)
    (hSet : ∀ a m Q X, step13Wm4SetSpec a m Q X → Γ "m6_wm4_set" [i64, i64] [] a m Q X) :
    SpecEntry.Impl Γ fidStep13S2UpdateClassifyFn (fidStep13S2BeforeRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_update_classify_fid_step13_wp Γ hGet hSet)

theorem full_propagate_beyond_m7_s13_impl (Γ : Env)
    (hWm4Get : ∀ args m Q X, step13Wm4GetSpec args m Q X →
      Γ "m6_wm4_get" [i64] [i64] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, FullFidelityBcp.fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X) :
    SpecEntry.Impl Γ fidStep13S2PropBeyondM7Fn (fidStep13S2BeforeRows[1]'(by decide)) :=
  SpecEntry.Impl.of (full_propagate_beyond_m7_step13_wp Γ hWm4Get hAddTicks hOvf hFlush)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2
