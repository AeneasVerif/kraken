module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrink
public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6MinShrink
meta import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Backend Compilation Guards, and Axiom Audit for Kissat M6 (`FullM6MinShrink`)

1. Executable `#guard` checks on `m6MinShrinkModule` (`17` fns + `19` externs, `0` exits),
   `checkAcyclic = true`, canonical handles (`m6DecideFn`..`m6AnalyzeFn`), `PrintCpp`, `PrintQbe`,
   and `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems for `m6MinShrink_fns_wf`, `m6MinShrink_acyclic`, all `17`
   parametric UNSAT-only `Func.wp` contracts, closed `36`-row `m6MinShrink_moduleOk`, and
   concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, zero SAT proofs).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeLegacyTest.KissatM6MinShrinkTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding full_decide_body full_decide_wf
  full_bump_analyzed_body full_bump_analyzed_wf
  full_min_lit_body full_min_lit_wf
  full_shrink_lower_body full_shrink_lower_wf
  full_shrink_blk_body full_shrink_blk_wf
  full_min_shrink_body full_min_shrink_wf
  full_deduce_1uip_body full_deduce_1uip_wf
  full_analyze_body full_analyze_wf
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m6MinShrinkModule.checkAcyclic == true
#guard m6MinShrinkModule.exits.isEmpty == true
#guard m6MinShrink_fns.length == 17
#guard m6MinShrinkExterns.length == 19
#guard m6DecideFn.name == "full_decide"
#guard m6BumpAnalyzedFn.name == "full_bump_analyzed"
#guard m6MinLitFn.name == "full_min_lit"
#guard m6ShrinkLowerFn.name == "full_shrink_lower"
#guard m6ShrinkBlkFn.name == "full_shrink_blk"
#guard m6MinShrinkFn.name == "full_min_shrink"
#guard m6Deduce1uipFn.name == "full_deduce_1uip"
#guard m6AnalyzeFn.name == "full_analyze"
#guard (ppTModule m6MinShrinkModule).isOk
#guard (PrintQbe.module m6MinShrinkModule).isOk
#guard (ppModule (m6MinShrink_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6MinShrink_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6MinShrink_fns.map (Fn.legal .x64AVX2))).isOk
#guard m6MinShrink_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m6ms_wf : ∀ f ∈ m6MinShrink_fns, f.Wf :=
  m6MinShrink_fns_wf

theorem m6ms_acyc : m6MinShrinkModule.checkAcyclic = true :=
  m6MinShrink_acyclic

theorem m6ms_spec_len : m6MinShrinkSpecTable.length = 36 :=
  m6MinShrinkSpecTable_length

theorem m6ms_spec_no_exit : m6MinShrinkSpecTable.all (·.noExit) = true :=
  m6MinShrinkSpecTable_allNoExit

theorem m6ms_dr_init_wp (Γ : Env) :
    ∀ a m Q X, m6DrInitSpec a m Q X → Func.wp Γ full_dr_init_m6_body a m Q X :=
  full_dr_init_m6_wp Γ

theorem m6ms_dr_upd_wp (Γ : Env)
    (hDrInit : ∀ a m Q X, m6DrInitSpec a m Q X → Γ "full_dr_init_m6" [i64] [] a m Q X) :
    ∀ a m Q X, m6DrUpdateSpec a m Q X → Func.wp Γ full_dr_update_m6_body a m Q X :=
  full_dr_update_m6_wp Γ hDrInit

theorem m6ms_dr_allow_wp (Γ : Env) :
    ∀ a m Q X, m6DrAllowSpec a m Q X → Func.wp Γ full_dr_allow_m6_body a m Q X :=
  full_dr_allow_m6_wp Γ

theorem m6ms_decide_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, Full.fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hDrInit : ∀ a m Q X, m6DrInitSpec a m Q X → Γ "full_dr_init_m6" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullDecideSpec a m Q X → Func.wp Γ full_decide_m6_body a m Q X :=
  full_decide_m6_wp Γ hNextDec hAssign hDrInit

theorem m6ms_sift_wp (Γ : Env) :
    ∀ a m Q X, m6AnaSiftSpec a m Q X → Func.wp Γ full_ana_sift_m6_body a m Q X :=
  full_ana_sift_m6_wp Γ

theorem m6ms_sort_qs_wp (Γ : Env)
    (hSift : ∀ a m Q X, m6AnaSiftSpec a m Q X →
      Γ "full_ana_sift_m6" [i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m6SortAnaQsSpec a m Q X → Func.wp Γ full_sort_ana_qs_m6_body a m Q X :=
  full_sort_ana_qs_m6_wp Γ hSift

theorem m6ms_bump_wp (Γ : Env)
    (hDrAllow : ∀ a m Q X, m6DrAllowSpec a m Q X → Γ "full_dr_allow_m6" [i64] [.bool] a m Q X)
    (hSortQs : ∀ a m Q X, m6SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hBump : ∀ a m Q X, Full.fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, Full.fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, Full.fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullBumpAnalyzedSpec a m Q X →
      Func.wp Γ full_bump_analyzed_m6_body a m Q X :=
  full_bump_analyzed_m6_wp Γ hDrAllow hSortQs hBump hMtf hDecay

theorem m6ms_restore_wp (Γ : Env)
    (hBumpAna : ∀ a m Q X, Full.fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6" [i64] [] a m Q X)
    (hClearAna : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X) :
    ∀ a m Q X, m6RestoreBumpAnaSpec a m Q X →
      Func.wp Γ full_restore_bump_ana_m6_body a m Q X :=
  full_restore_bump_ana_m6_wp Γ hBumpAna hClearAna

theorem m6ms_min_dfs_wp (Γ : Env)
    (hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X) :
    ∀ a m Q X, m6MinLitDfsSpec a m Q X → Func.wp Γ full_min_lit_dfs_m6_body a m Q X :=
  full_min_lit_dfs_m6_wp Γ hMm

theorem m6ms_min_lit_wp (Γ : Env)
    (hDfs : ∀ a m Q X, m6MinLitDfsSpec a m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullMinLitSpec a m Q X → Func.wp Γ full_min_lit_m6_body a m Q X :=
  full_min_lit_m6_wp Γ hDfs

theorem m6ms_shrink_lower_wp (Γ : Env)
    (hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X)
    (hDfs : ∀ a m Q X, m6MinLitDfsSpec a m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullShrinkLowerSpec a m Q X → Func.wp Γ full_shrink_lower_m6_body a m Q X :=
  full_shrink_lower_m6_wp Γ hMm hDfs

theorem m6ms_shrink_blk_bool_wp (Γ : Env)
    (hSl : ∀ a m Q X, Full.fullShrinkLowerSpec a m Q X →
      Γ "full_shrink_lower_m6" [i64, i32, i32] [.bool] a m Q X)
    (hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X) :
    ∀ a m Q X, m6ShrinkBlkBoolSpec a m Q X → Func.wp Γ full_shrink_blk_bool_m6_body a m Q X :=
  full_shrink_blk_bool_m6_wp Γ hSl hMm

theorem m6ms_shrink_blk_wp (Γ : Env)
    (hSb : ∀ a m Q X, m6ShrinkBlkBoolSpec a m Q X →
      Γ "full_shrink_blk_bool_m6" [i64, i64, i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullShrinkBlkSpec a m Q X → Func.wp Γ full_shrink_blk_m6_body a m Q X :=
  full_shrink_blk_m6_wp Γ hSb

theorem m6ms_min_shrink_wp (Γ : Env)
    (hSt : ∀ a m Q X, Full.fullSortTmpSpec a m Q X → Γ "full_sort_tmp" [i64] [] a m Q X)
    (hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X)
    (hDfs : ∀ a m Q X, m6MinLitDfsSpec a m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] a m Q X)
    (hSb : ∀ a m Q X, m6ShrinkBlkBoolSpec a m Q X →
      Γ "full_shrink_blk_bool_m6" [i64, i64, i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullMinShrinkSpec a m Q X → Func.wp Γ full_min_shrink_m6_body a m Q X :=
  full_min_shrink_m6_wp Γ hSt hMm hDfs hSb

theorem m6ms_deduce_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X → Func.wp Γ full_deduce_1uip_m6_body a m Q X :=
  full_deduce_1uip_m6_wp Γ hAlit hArsn hClear hOtfsLarge hOtfsBin hOtfsSub

theorem m6ms_failed_lit_wp (Γ : Env)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hBumpAna : ∀ a m Q X, Full.fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6" [i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, m6AnaFailedLitSpec a m Q X → Func.wp Γ full_ana_failed_lit_m6_body a m Q X :=
  full_ana_failed_lit_m6_wp Γ hClear hBumpAna hBacktrack hAssignLvl

theorem m6ms_analyze_wp (Γ : Env)
    (hDrUpdate : ∀ a m Q X, m6DrUpdateSpec a m Q X → Γ "full_dr_update_m6" [i64] [] a m Q X)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailedLit : ∀ a m Q X, m6AnaFailedLitSpec a m Q X →
      Γ "full_ana_failed_lit_m6" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
      Γ "full_deduce_1uip_m6" [i64] [i64] a m Q X)
    (hRestoreBump : ∀ a m Q X, m6RestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m6" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, Full.fullMinShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, Full.fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X → Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullAnalyzeSpec a m Q X → Func.wp Γ full_analyze_m6_body a m Q X :=
  full_analyze_m6_wp Γ hDrUpdate hOneLit hFailedLit hDeduce hRestoreBump hMinShrink hTickRel
    hEma hLearnCl

theorem m6ms_mod_ok : ModuleOk m6MinShrinkEnv m6MinShrinkModule :=
  m6MinShrink_moduleOk

theorem m6ms_nv_dr_init :
    Func.wp m6MinShrinkEnv full_dr_init_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_dr_init

theorem m6ms_nv_dr_allow :
    Func.wp m6MinShrinkEnv full_dr_allow_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => (r = true ∨ r = false) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_m6_dr_allow

theorem m6ms_nv_bump :
    Func.wp m6MinShrinkEnv full_bump_analyzed_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ FullAnaMarksCov nvOneLitCfg s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_bump_analyzed

theorem m6ms_nv_restore :
    Func.wp m6MinShrinkEnv full_restore_bump_ana_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ FullMrkZero nvOneLitCfg s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_restore_bump_ana

theorem m6ms_nv_ana :
    Func.wp m6MinShrinkEnv full_analyze_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s', r = 20#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_analyze

end AuditSpec

end LeanQbeLegacyTest.KissatM6MinShrinkTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m6ms_a_wf := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_wf
abbrev m6ms_a_acyc := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_acyc
abbrev m6ms_a_dr_init := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_dr_init_wp
abbrev m6ms_a_dr_upd := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_dr_upd_wp
abbrev m6ms_a_dr_allow := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_dr_allow_wp
abbrev m6ms_a_decide := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_decide_wp
abbrev m6ms_a_sift := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_sift_wp
abbrev m6ms_a_sort_qs := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_sort_qs_wp
abbrev m6ms_a_bump := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_bump_wp
abbrev m6ms_a_restore := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_restore_wp
abbrev m6ms_a_min_dfs := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_min_dfs_wp
abbrev m6ms_a_min_lit := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_min_lit_wp
abbrev m6ms_a_shrk_lo := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_shrink_lower_wp
abbrev m6ms_a_shrk_b := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_shrink_blk_bool_wp
abbrev m6ms_a_shrk_blk := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_shrink_blk_wp
abbrev m6ms_a_min_shrk := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_min_shrink_wp
abbrev m6ms_a_deduce := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_deduce_wp
abbrev m6ms_a_failed := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_failed_lit_wp
abbrev m6ms_a_ana := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_analyze_wp
abbrev m6ms_a_mod := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_mod_ok
abbrev m6ms_a_nv_dri := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_nv_dr_init
abbrev m6ms_a_nv_dra := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_nv_dr_allow
abbrev m6ms_a_nv_bump := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_nv_bump
abbrev m6ms_a_nv_rst := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_nv_restore
abbrev m6ms_a_nv_ana := @LeanQbeLegacyTest.KissatM6MinShrinkTest.m6ms_nv_ana

#print axioms m6ms_a_wf
#print axioms m6ms_a_acyc
#print axioms m6ms_a_dr_init
#print axioms m6ms_a_dr_upd
#print axioms m6ms_a_dr_allow
#print axioms m6ms_a_decide
#print axioms m6ms_a_sift
#print axioms m6ms_a_sort_qs
#print axioms m6ms_a_bump
#print axioms m6ms_a_restore
#print axioms m6ms_a_min_dfs
#print axioms m6ms_a_min_lit
#print axioms m6ms_a_shrk_lo
#print axioms m6ms_a_shrk_b
#print axioms m6ms_a_shrk_blk
#print axioms m6ms_a_min_shrk
#print axioms m6ms_a_deduce
#print axioms m6ms_a_failed
#print axioms m6ms_a_ana
#print axioms m6ms_a_mod
#print axioms m6ms_a_nv_dri
#print axioms m6ms_a_nv_dra
#print axioms m6ms_a_nv_bump
#print axioms m6ms_a_nv_rst
#print axioms m6ms_a_nv_ana
