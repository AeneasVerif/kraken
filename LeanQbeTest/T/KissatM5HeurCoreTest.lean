module

public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5HeurCore
meta import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Backend Compilation Guards, and Axiom Audit for Kissat M5 Wave 1 (`PR-W1A`)

1. Executable `#guard` checks on `m5HeurCoreModule` (`11` fns + `24` externs, `0` exits),
   `checkAcyclic = true`, `m5HeurCoreSpecTable` (`35` rows), drop-in replacement `Fn` handles,
   `PrintCpp`, `PrintQbe`, and `Fn.legal` across `aarch64`, `scalar64`, and `x64AVX2`.
2. Audit-ready restated headline theorems for `m5HeurCore_fns_wf`, `m5HeurCore_acyclic`, all `11`
   parametric `Func.wp` contracts, closed `35`-row `m5HeurCore_moduleOk`, and concrete `Mem 64`
   UNSAT non-vacuity (`XPost := False`, `0` SAT proofs).
3. Single-line `< 115`-col `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM5HeurCoreTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m5HeurCoreModule.checkAcyclic == true
#guard m5HeurCoreModule.exits.isEmpty
#guard m5HeurCore_fns.length == 11
#guard m5HeurCoreExterns.length == 24
#guard m5HeurCoreSpecTable.length == 35
#guard m5SaveTargetBestFn.name == "full_save_target_best"
#guard m5BacktrackRawFn.name == "full_backtrack_raw_m5"
#guard m5BacktrackFn.name == "full_backtrack"
#guard m5AnalyzeRsnFn.name == "full_analyze_rsn"
#guard m5OtfsSubsumeFn.name == "full_otfs_subsume"
#guard m5BumpAnalyzedFn.name == "full_bump_analyzed"
#guard m5RestoreBumpAnaFn.name == "full_restore_bump_ana_m5"
#guard m5EagerSubsumeFn.name == "full_eager_subsume"
#guard m5LearnClauseFn.name == "full_learn_clause"
#guard m5AnalyzeFn.name == "full_analyze"
#guard m5WarmupFn.name == "full_warmup"
#guard (ppTModule m5HeurCoreModule).isOk
#guard (PrintQbe.module m5HeurCoreModule).isOk
#guard (ppModule (m5HeurCore_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5HeurCore_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5HeurCore_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m5hc_wf : ∀ f ∈ m5HeurCore_fns, f.Wf :=
  m5HeurCore_fns_wf

theorem m5hc_acyc : m5HeurCoreModule.checkAcyclic = true :=
  m5HeurCore_acyclic

theorem m5hc_save_wp (Γ : Env) :
    ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Func.wp Γ full_save_target_best_m5_body a m Q X :=
  full_save_target_best_m5_wp Γ

theorem m5hc_bt_raw_wp (Γ : Env)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Func.wp Γ full_backtrack_raw_m5_body a m Q X :=
  full_backtrack_raw_m5_wp Γ hSave hHeapPush

theorem m5hc_bt_wp (Γ : Env)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X) :
    ∀ a m Q X, fullBacktrackSpec a m Q X →
      Func.wp Γ full_backtrack_m5_body a m Q X :=
  full_backtrack_m5_wp Γ hBtRaw hSave

theorem m5hc_warmup_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWarmupSpec a m Q X → Func.wp Γ full_warmup_m5_body a m Q X :=
  full_warmup_m5_wp Γ hNextDec hAssign hProp hBtRaw

theorem m5hc_rsn_wp (Γ : Env)
    (hAnaLit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAnalyzeRsnSpec a m Q X →
      Func.wp Γ full_analyze_rsn_m5_body a m Q X :=
  full_analyze_rsn_m5_wp Γ hAnaLit

theorem m5hc_otfs_wp (Γ : Env) :
    ∀ a m Q X, fullOtfsSubsumeSpec a m Q X →
      Func.wp Γ full_otfs_subsume_m5_body a m Q X :=
  full_otfs_subsume_m5_wp Γ

theorem m5hc_bump_wp (Γ : Env)
    (hBump : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpAnalyzedSpec a m Q X →
      Func.wp Γ full_bump_analyzed_m5_body a m Q X :=
  full_bump_analyzed_m5_wp Γ hBump hMtf hDecay

theorem m5hc_restore_wp (Γ : Env)
    (hBumpAna : ∀ a m Q X, fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed" [i64] [] a m Q X)
    (hClearAna : ∀ a m Q X, fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
      Func.wp Γ full_restore_bump_ana_m5_body a m Q X :=
  full_restore_bump_ana_m5_wp Γ hBumpAna hClearAna

theorem m5hc_esub_wp (Γ : Env) :
    ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Func.wp Γ full_eager_subsume_m5_body a m Q X :=
  full_eager_subsume_m5_wp Γ

theorem m5hc_learn_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullLearnClauseSpec a m Q X →
      Func.wp Γ full_learn_clause_m5_body a m Q X :=
  full_learn_clause_m5_wp Γ hBt hAsgn hDnl hDefrag hRed hAddCl hEsub

theorem m5hc_ana_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
      Γ "full_deduce_1uip" [i64] [i64] a m Q X)
    (hRestoreBump : ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m5" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, fullMinShrinkSpec a m Q X →
      Γ "full_min_shrink" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, fullTickRelSpec a m Q X →
      Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullAnalyzeSpec a m Q X →
      Func.wp Γ full_analyze_m5_body a m Q X :=
  full_analyze_m5_wp Γ hOneLit hDeduce hRestoreBump hMinShrink hTickRel hEma hLearnCl

theorem m5hc_mod_ok : ModuleOk m5HeurCoreEnv m5HeurCoreModule :=
  m5HeurCore_moduleOk

theorem m5hc_nv_save :
    Func.wp m5HeurCoreEnv full_save_target_best_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_save_target_best

theorem m5hc_nv_bt :
    Func.wp m5HeurCoreEnv full_backtrack_m5_body (nvOneLitCfg.hdr, 0#64, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ s'.core.cur_level = 0 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_backtrack

theorem m5hc_nv_bump :
    Func.wp m5HeurCoreEnv full_bump_analyzed_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ FullAnaMarksCov nvOneLitCfg s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_bump_analyzed

theorem m5hc_nv_restore :
    Func.wp m5HeurCoreEnv full_restore_bump_ana_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ FullMrkZero nvOneLitCfg s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_restore_bump_ana

theorem m5hc_nv_warmup :
    Func.wp m5HeurCoreEnv full_warmup_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_warmup

theorem m5hc_nv_otfs :
    Func.wp m5HeurCoreEnv full_otfs_subsume_m5_body
      (nvOneLitCfg.hdr, 0#32, 1#64, 0xFFFFFFFF#64, true, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_otfs_subsume

theorem m5hc_nv_esub :
    Func.wp m5HeurCoreEnv full_eager_subsume_m5_body
      (nvOneLitCfg.hdr, 0xFFFFFFFF#64, ()) nvOneLitMem
      (fun () m' => ∃ s', FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_eager_subsume

theorem m5hc_nv_ana :
    Func.wp m5HeurCoreEnv full_analyze_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s', r = 20#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m5_analyze

end AuditSpec

end LeanQbeTest.T.KissatM5HeurCoreTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m5hc_a_wf := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_wf
abbrev m5hc_a_acyc := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_acyc
abbrev m5hc_a_save := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_save_wp
abbrev m5hc_a_bt_raw := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_bt_raw_wp
abbrev m5hc_a_bt := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_bt_wp
abbrev m5hc_a_warmup := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_warmup_wp
abbrev m5hc_a_rsn := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_rsn_wp
abbrev m5hc_a_otfs := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_otfs_wp
abbrev m5hc_a_bump := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_bump_wp
abbrev m5hc_a_restore := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_restore_wp
abbrev m5hc_a_esub := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_esub_wp
abbrev m5hc_a_learn := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_learn_wp
abbrev m5hc_a_ana := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_ana_wp
abbrev m5hc_a_mod := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_mod_ok
abbrev m5hc_a_nv_save := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_nv_save
abbrev m5hc_a_nv_bt := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_nv_bt
abbrev m5hc_a_nv_bump := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_nv_bump
abbrev m5hc_a_nv_rst := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_nv_restore
abbrev m5hc_a_nv_wrm := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_nv_warmup
abbrev m5hc_a_nv_otfs := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_nv_otfs
abbrev m5hc_a_nv_esub := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_nv_esub
abbrev m5hc_a_nv_ana := @LeanQbeTest.T.KissatM5HeurCoreTest.m5hc_nv_ana

#print axioms m5hc_a_wf
#print axioms m5hc_a_acyc
#print axioms m5hc_a_save
#print axioms m5hc_a_bt_raw
#print axioms m5hc_a_bt
#print axioms m5hc_a_warmup
#print axioms m5hc_a_rsn
#print axioms m5hc_a_otfs
#print axioms m5hc_a_bump
#print axioms m5hc_a_restore
#print axioms m5hc_a_esub
#print axioms m5hc_a_learn
#print axioms m5hc_a_ana
#print axioms m5hc_a_mod
#print axioms m5hc_a_nv_save
#print axioms m5hc_a_nv_bt
#print axioms m5hc_a_nv_bump
#print axioms m5hc_a_nv_rst
#print axioms m5hc_a_nv_wrm
#print axioms m5hc_a_nv_otfs
#print axioms m5hc_a_nv_esub
#print axioms m5hc_a_nv_ana
