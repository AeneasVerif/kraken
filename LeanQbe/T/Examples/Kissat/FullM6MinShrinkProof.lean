module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 `PR-W2B`: Closed `ModuleOk` & Concrete `Mem 64` UNSAT NV (`FullM6MinShrinkProof`)

Combines all `17` parametric UNSAT-only `Func.wp` proofs (`Proof0`..`Proof3`) into:
1. Closed `36`-row `m6MinShrinkSpecTable` (`17` defined functions + `19` canonical externs, all
   `noExit = true`, zero `FullHdr` edits, zero `@[expose]` attributes).
2. `m6MinShrinkEnv`, `m6MinShrink_tableImpl`, and headline
   `m6MinShrink_moduleOk : ModuleOk m6MinShrinkEnv m6MinShrinkModule`.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, zero SAT proofs) on `nvOneLitCfg` /
   `nvOneLitState` / `nvOneLitMem` / `nvOneLitF0` (`nv_m6_dr_init`, `nv_m6_dr_allow`,
   `nv_m6_bump_analyzed`, `nv_m6_restore_bump_ana`, `nv_m6_analyze`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding full_decide_body full_decide_wf
  full_bump_analyzed_body full_bump_analyzed_wf
  full_min_lit_body full_min_lit_wf
  full_shrink_lower_body full_shrink_lower_wf
  full_shrink_blk_body full_shrink_blk_wf
  full_min_shrink_body full_min_shrink_wf
  full_deduce_1uip_body full_deduce_1uip_wf
  full_analyze_body full_analyze_wf
open Kraken.Bedrock2.Test

/-! ## 1. Closed `36`-Row `m6MinShrinkSpecTable`, `m6MinShrinkEnv`, and `ModuleOk` -/

section ModuleOkSection

/-- Closed `36`-row specification table for `m6MinShrinkModule` (`17` defined functions + `19`
external callees, all `noExit = true`). -/
def m6MinShrinkSpecTable : List SpecEntry :=
  [ ⟨"full_dr_init_m6", [i64], [], m6DrInitSpec, true⟩
  , ⟨"full_dr_update_m6", [i64], [], m6DrUpdateSpec, true⟩
  , ⟨"full_dr_allow_m6", [i64], [.bool], m6DrAllowSpec, true⟩
  , ⟨"full_decide_m6", [i64], [i64], Full.fullDecideSpec, true⟩
  , ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], m6AnaSiftSpec, true⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], [], m6SortAnaQsSpec, true⟩
  , ⟨"full_bump_analyzed_m6", [i64], [], Full.fullBumpAnalyzedSpec, true⟩
  , ⟨"full_restore_bump_ana_m6", [i64], [], m6RestoreBumpAnaSpec, true⟩
  , ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool], m6MinLitDfsSpec, true⟩
  , ⟨"full_min_lit_m6", [i64, i32], [.bool], Full.fullMinLitSpec, true⟩
  , ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool], Full.fullShrinkLowerSpec, true⟩
  , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool], m6ShrinkBlkBoolSpec, true⟩
  , ⟨"full_shrink_blk_m6", [i64, i64, i64, i32, i64], [], Full.fullShrinkBlkSpec, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], Full.fullMinShrinkSpec, true⟩
  , ⟨"full_deduce_1uip_m6", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_ana_failed_lit_m6", [i64], [i64], m6AnaFailedLitSpec, true⟩
  , ⟨"full_analyze_m6", [i64], [i64], Full.fullAnalyzeSpec, true⟩
  , ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩
  , ⟨"full_sort_tmp", [i64], [], Full.fullSortTmpSpec, true⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  , ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩
  , ⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩
  , ⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩
  , ⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  , ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩
  , ⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩
  , ⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩
  , ⟨"full_one_lit_confl", [i64], [i64], Full.fullOneLitConflSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], Full.fullLearnClauseSpec, true⟩ ]

theorem m6MinShrinkSpecTable_length : m6MinShrinkSpecTable.length = 36 := by rfl

theorem m6MinShrinkSpecTable_nodup : (m6MinShrinkSpecTable.map SpecEntry.name).Nodup := by
  show ([ "full_dr_init_m6", "full_dr_update_m6", "full_dr_allow_m6", "full_decide_m6"
    , "full_ana_sift_m6", "full_sort_ana_qs_m6", "full_bump_analyzed_m6"
    , "full_restore_bump_ana_m6", "full_min_lit_dfs_m6", "full_min_lit_m6"
    , "full_shrink_lower_m6", "full_shrink_blk_bool_m6", "full_shrink_blk_m6"
    , "full_min_shrink_m6", "full_deduce_1uip_m6", "full_ana_failed_lit_m6"
    , "full_analyze_m6", "full_min_mark", "full_sort_tmp", "full_analyze_lit"
    , "full_analyze_rsn", "full_clear_ana", "full_otfs_large", "full_otfs_bin"
    , "full_otfs_subsume", "full_bump_var", "full_queue_mtf", "full_bump_decay"
    , "full_backtrack", "full_assign_lvl", "full_next_dec_var", "full_assign"
    , "full_tick_rel", "full_ema_update", "full_one_lit_confl"
    , "full_learn_clause" ] : List String).Nodup
  decide

theorem m6MinShrinkSpecTable_noExit : ∀ e ∈ m6MinShrinkSpecTable, e.noExit = true := by
  intro e he
  simp only [m6MinShrinkSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m6MinShrinkSpecTable_allNoExit : m6MinShrinkSpecTable.all (·.noExit) = true := by rfl

/-- Closed environment for `m6MinShrinkModule`. -/
def m6MinShrinkEnv : Env := Env.ofTable m6MinShrinkSpecTable

theorem m6MinShrinkEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6MinShrinkEnv f as bs xs m Q X → m6MinShrinkEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6MinShrinkSpecTable_noExit

private theorem m6MinShrinkEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m6MinShrinkSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by
      intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m6MinShrinkEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m6MinShrinkSpecTable_nodup
      (hno xs m Q X h)

private theorem m6MinShrink_dr_init_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_dr_init_m6", [i64], [], full_dr_init_m6_body⟩
      ⟨"full_dr_init_m6", [i64], [], m6DrInitSpec, true⟩ :=
  SpecEntry.Impl.of (full_dr_init_m6_wp m6MinShrinkEnv)

private theorem m6MinShrink_dr_update_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_dr_update_m6", [i64], [], full_dr_update_m6_body⟩
      ⟨"full_dr_update_m6", [i64], [], m6DrUpdateSpec, true⟩ :=
  SpecEntry.Impl.of (full_dr_update_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 0 ⟨"full_dr_init_m6", [i64], [], m6DrInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6DrInitSpec_monoX h)))

private theorem m6MinShrink_dr_allow_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_dr_allow_m6", [i64], [.bool], full_dr_allow_m6_body⟩
      ⟨"full_dr_allow_m6", [i64], [.bool], m6DrAllowSpec, true⟩ :=
  SpecEntry.Impl.of (full_dr_allow_m6_wp m6MinShrinkEnv)

private theorem m6MinShrink_decide_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_decide_m6", [i64], [i64], full_decide_m6_body⟩
      ⟨"full_decide_m6", [i64], [i64], Full.fullDecideSpec, true⟩ :=
  SpecEntry.Impl.of (full_decide_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 30 ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩)
    (m6MinShrinkEnv_row_at 31 ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩)
    (m6MinShrinkEnv_row_at 0 ⟨"full_dr_init_m6", [i64], [], m6DrInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6DrInitSpec_monoX h)))

private theorem m6MinShrink_ana_sift_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], full_ana_sift_m6_body⟩
      ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], m6AnaSiftSpec, true⟩ :=
  SpecEntry.Impl.of (full_ana_sift_m6_wp m6MinShrinkEnv)

private theorem m6MinShrink_sort_ana_qs_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_sort_ana_qs_m6", [i64, i64], [], full_sort_ana_qs_m6_body⟩
      ⟨"full_sort_ana_qs_m6", [i64, i64], [], m6SortAnaQsSpec, true⟩ :=
  SpecEntry.Impl.of (full_sort_ana_qs_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 4
      ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], m6AnaSiftSpec, true⟩
      (hno := fun _ _ _ _ h => m6AnaSiftSpec_monoX h)))

theorem m6MinShrink_bump_analyzed_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_bump_analyzed_m6", [i64], [], full_bump_analyzed_m6_body⟩
      ⟨"full_bump_analyzed_m6", [i64], [], Full.fullBumpAnalyzedSpec, true⟩ :=
  SpecEntry.Impl.of (full_bump_analyzed_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 2 ⟨"full_dr_allow_m6", [i64], [.bool], m6DrAllowSpec, true⟩
      (hno := fun _ _ _ _ h => m6DrAllowSpec_monoX h))
    (m6MinShrinkEnv_row_at 5 ⟨"full_sort_ana_qs_m6", [i64, i64], [], m6SortAnaQsSpec, true⟩
      (hno := fun _ _ _ _ h => m6SortAnaQsSpec_monoX h))
    (m6MinShrinkEnv_row_at 25 ⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩)
    (m6MinShrinkEnv_row_at 26 ⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩)
    (m6MinShrinkEnv_row_at 27 ⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩))

theorem m6MinShrink_restore_bump_ana_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_restore_bump_ana_m6", [i64], [], full_restore_bump_ana_m6_body⟩
      ⟨"full_restore_bump_ana_m6", [i64], [], m6RestoreBumpAnaSpec, true⟩ :=
  SpecEntry.Impl.of (full_restore_bump_ana_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 6
      ⟨"full_bump_analyzed_m6", [i64], [], Full.fullBumpAnalyzedSpec, true⟩)
    (m6MinShrinkEnv_row_at 21 ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩))

private theorem m6MinShrink_min_lit_dfs_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool], full_min_lit_dfs_m6_body⟩
      ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool], m6MinLitDfsSpec, true⟩ :=
  SpecEntry.Impl.of (full_min_lit_dfs_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 17 ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩))

private theorem m6MinShrink_min_lit_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_min_lit_m6", [i64, i32], [.bool], full_min_lit_m6_body⟩
      ⟨"full_min_lit_m6", [i64, i32], [.bool], Full.fullMinLitSpec, true⟩ :=
  SpecEntry.Impl.of (full_min_lit_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 8
      ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool], m6MinLitDfsSpec, true⟩
      (hno := fun _ _ _ _ h => m6MinLitDfsSpec_monoX h)))

private theorem m6MinShrink_shrink_lower_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool], full_shrink_lower_m6_body⟩
      ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool], Full.fullShrinkLowerSpec, true⟩ :=
  SpecEntry.Impl.of (full_shrink_lower_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 17 ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩)
    (m6MinShrinkEnv_row_at 8
      ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool], m6MinLitDfsSpec, true⟩
      (hno := fun _ _ _ _ h => m6MinLitDfsSpec_monoX h)))

private theorem m6MinShrink_shrink_blk_bool_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
        full_shrink_blk_bool_m6_body⟩
      ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool], m6ShrinkBlkBoolSpec, true⟩ :=
  SpecEntry.Impl.of (full_shrink_blk_bool_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 10
      ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool], Full.fullShrinkLowerSpec, true⟩)
    (m6MinShrinkEnv_row_at 17 ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩))

private theorem m6MinShrink_shrink_blk_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_shrink_blk_m6", [i64, i64, i64, i32, i64], [], full_shrink_blk_m6_body⟩
      ⟨"full_shrink_blk_m6", [i64, i64, i64, i32, i64], [], Full.fullShrinkBlkSpec, true⟩ :=
  SpecEntry.Impl.of (full_shrink_blk_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 11
      ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
        m6ShrinkBlkBoolSpec, true⟩
      (hno := fun _ _ _ _ h => m6ShrinkBlkBoolSpec_monoX h)))

private theorem m6MinShrink_min_shrink_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_min_shrink_m6", [i64], [], full_min_shrink_m6_body⟩
      ⟨"full_min_shrink_m6", [i64], [], Full.fullMinShrinkSpec, true⟩ :=
  SpecEntry.Impl.of (full_min_shrink_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 18 ⟨"full_sort_tmp", [i64], [], Full.fullSortTmpSpec, true⟩)
    (m6MinShrinkEnv_row_at 17 ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩)
    (m6MinShrinkEnv_row_at 8
      ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool], m6MinLitDfsSpec, true⟩
      (hno := fun _ _ _ _ h => m6MinLitDfsSpec_monoX h))
    (m6MinShrinkEnv_row_at 11
      ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
        m6ShrinkBlkBoolSpec, true⟩
      (hno := fun _ _ _ _ h => m6ShrinkBlkBoolSpec_monoX h)))

private theorem m6MinShrink_deduce_1uip_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_deduce_1uip_m6", [i64], [i64], full_deduce_1uip_m6_body⟩
      ⟨"full_deduce_1uip_m6", [i64], [i64], Full.fullDeduce1uipSpec, true⟩ :=
  SpecEntry.Impl.of (full_deduce_1uip_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 19
      ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩)
    (m6MinShrinkEnv_row_at 20
      ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩)
    (m6MinShrinkEnv_row_at 21 ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩)
    (m6MinShrinkEnv_row_at 22
      ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩)
    (m6MinShrinkEnv_row_at 23
      ⟨"full_otfs_bin", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩)
    (m6MinShrinkEnv_row_at 24
      ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩))

private theorem m6MinShrink_ana_failed_lit_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_ana_failed_lit_m6", [i64], [i64], full_ana_failed_lit_m6_body⟩
      ⟨"full_ana_failed_lit_m6", [i64], [i64], m6AnaFailedLitSpec, true⟩ :=
  SpecEntry.Impl.of (full_ana_failed_lit_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 21 ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩)
    (m6MinShrinkEnv_row_at 6
      ⟨"full_bump_analyzed_m6", [i64], [], Full.fullBumpAnalyzedSpec, true⟩)
    (m6MinShrinkEnv_row_at 28 ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩)
    (m6MinShrinkEnv_row_at 29
      ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩))

theorem m6MinShrink_analyze_impl :
    SpecEntry.Impl m6MinShrinkEnv
      ⟨"full_analyze_m6", [i64], [i64], full_analyze_m6_body⟩
      ⟨"full_analyze_m6", [i64], [i64], Full.fullAnalyzeSpec, true⟩ :=
  SpecEntry.Impl.of (full_analyze_m6_wp m6MinShrinkEnv
    (m6MinShrinkEnv_row_at 1 ⟨"full_dr_update_m6", [i64], [], m6DrUpdateSpec, true⟩
      (hno := fun _ _ _ _ h => m6DrUpdateSpec_monoX h))
    (m6MinShrinkEnv_row_at 34 ⟨"full_one_lit_confl", [i64], [i64], Full.fullOneLitConflSpec, true⟩)
    (m6MinShrinkEnv_row_at 15 ⟨"full_ana_failed_lit_m6", [i64], [i64], m6AnaFailedLitSpec, true⟩
      (hno := fun _ _ _ _ h => m6AnaFailedLitSpec_monoX h))
    (m6MinShrinkEnv_row_at 14 ⟨"full_deduce_1uip_m6", [i64], [i64], Full.fullDeduce1uipSpec, true⟩)
    (m6MinShrinkEnv_row_at 7
      ⟨"full_restore_bump_ana_m6", [i64], [], m6RestoreBumpAnaSpec, true⟩
      (hno := fun _ _ _ _ h => m6RestoreBumpAnaSpec_monoX h))
    (m6MinShrinkEnv_row_at 13 ⟨"full_min_shrink_m6", [i64], [], Full.fullMinShrinkSpec, true⟩)
    (m6MinShrinkEnv_row_at 32 ⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩)
    (m6MinShrinkEnv_row_at 33 ⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩)
    (m6MinShrinkEnv_row_at 35
      ⟨"full_learn_clause", [i64, i64], [i64], Full.fullLearnClauseSpec, true⟩))

theorem m6MinShrink_allFns_wf : AllFns Fn.Wf m6MinShrinkModule.fns :=
  ⟨full_dr_init_m6_wf, full_dr_update_m6_wf, full_dr_allow_m6_wf, full_decide_m6_wf,
    full_ana_sift_m6_wf, full_sort_ana_qs_m6_wf, full_bump_analyzed_m6_wf,
    full_restore_bump_ana_m6_wf, full_min_lit_dfs_m6_wf, full_min_lit_m6_wf,
    full_shrink_lower_m6_wf, full_shrink_blk_bool_m6_wf, full_shrink_blk_m6_wf,
    full_min_shrink_m6_wf, full_deduce_1uip_m6_wf, full_ana_failed_lit_m6_wf,
    full_analyze_m6_wf, trivial⟩

theorem m6MinShrink_tableImpl :
    TableImpl m6MinShrinkEnv m6MinShrinkModule.fns m6MinShrinkSpecTable :=
  ⟨m6MinShrink_dr_init_impl, m6MinShrink_dr_update_impl, m6MinShrink_dr_allow_impl,
    m6MinShrink_decide_impl, m6MinShrink_ana_sift_impl, m6MinShrink_sort_ana_qs_impl,
    m6MinShrink_bump_analyzed_impl, m6MinShrink_restore_bump_ana_impl,
    m6MinShrink_min_lit_dfs_impl, m6MinShrink_min_lit_impl, m6MinShrink_shrink_lower_impl,
    m6MinShrink_shrink_blk_bool_impl, m6MinShrink_shrink_blk_impl, m6MinShrink_min_shrink_impl,
    m6MinShrink_deduce_1uip_impl, m6MinShrink_ana_failed_lit_impl, m6MinShrink_analyze_impl,
    trivial⟩

/-- Headline `ModuleOk` certifying all `17` functions of `m6MinShrinkModule` under
`m6MinShrinkEnv` (`36` spec rows, `0` exits, fully closed). -/
theorem m6MinShrink_moduleOk : ModuleOk m6MinShrinkEnv m6MinShrinkModule :=
  Env.ofTable_moduleOk m6MinShrink_acyclic m6MinShrink_allFns_wf m6MinShrink_tableImpl

end ModuleOkSection

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvM6F0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvM6_mrkZero : FullMrkZero nvOneLitCfg nvOneLitState := fun v hv => by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl

private theorem nvM6_anaMarksCov : FullAnaMarksCov nvOneLitCfg nvOneLitState :=
  ⟨Nat.zero_le _, by simp [nvOneLitState], fun _ hk => by simp [nvOneLitState] at hk,
    fun v hv hnz => absurd (nvM6_mrkZero v hv) hnz⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_dr_init_m6`. -/
theorem nv_m6_dr_init :
    Func.wp m6MinShrinkEnv full_dr_init_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m6MinShrink_dr_init_impl.2 _ _ _ _
    (m6DrInitSpec_of nvOneLit_lengths hm fun _ _ m' hlen hm' => by
      rw [sep_emp] at hm'; exact ⟨_, hlen, nvM6F0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_dr_allow_m6`. -/
theorem nv_m6_dr_allow :
    Func.wp m6MinShrinkEnv full_dr_allow_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => (r = true ∨ r = false) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m6MinShrink_dr_allow_impl.2 _ _ _ _
    (m6DrAllowSpec_of nvOneLit_lengths hm fun r =>
      ⟨by cases r <;> simp, nvM6F0_unsat, nvOneLitMem_ok⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_bump_analyzed_m6`. -/
theorem nv_m6_bump_analyzed :
    Func.wp m6MinShrinkEnv full_bump_analyzed_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ FullAnaMarksCov nvOneLitCfg s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m6MinShrink_bump_analyzed_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvM6_anaMarksCov, hm, ?_⟩
  intro _ _ _ m' _ hlen hcov _ _ hm'
  rw [sep_emp] at hm'; exact ⟨_, hlen, hcov, nvM6F0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_restore_bump_ana_m6`. -/
theorem nv_m6_restore_bump_ana :
    Func.wp m6MinShrinkEnv full_restore_bump_ana_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ FullMrkZero nvOneLitCfg s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m6MinShrink_restore_bump_ana_impl.2 _ _ _ _
    (m6RestoreBumpAnaSpec_of nvOneLit_lengths nvM6_mrkZero hm
      fun _ _ _ m' hlen hm0 _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen, hm0, nvM6F0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_analyze_m6`: on the level-0 binary
conflict in `nvOneLitMem`, certifies `r = 20#64` and `nvOneLitF0.Unsat`. -/
theorem nv_m6_analyze :
    Func.wp m6MinShrinkEnv full_analyze_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s', r = 20#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  unfold Func.wp full_analyze_m6_body
  dsimp only
  rw [wp_let]
  refine wp_load_of (FullArenaTactics.load_full_cur_level hm) ?_
  refine wp_let_cmp _ _ _ _ _ _ rfl ?_
  refine wp_jnz_of (fun _ => ?_) (fun hf => absurd hf (by decide))
  rw [wp_ret]; exact ⟨nvOneLitState, rfl, nvM6F0_unsat, nvOneLitMem_ok⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM6MinShrink
