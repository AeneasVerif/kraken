module

public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof0
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof1
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof2a
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof2b
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas

/-!
# Kissat M5 Wave 1 (`PR-W1A`): `ModuleOk` & Concrete `Mem 64` UNSAT NV (`FullM5HeurCoreProof`)

Combines the `11` parametric UNSAT-only `Func.wp` proofs (`Proof0`, `Proof1`, `Proof2a`, `Proof2b`)
into:
1. Closed `35`-row `m5HeurCoreSpecTable` (`11` overrides + `24` canonical externs, all `noExit`).
2. `m5HeurCoreEnv` and headline `m5HeurCore_moduleOk : ModuleOk m5HeurCoreEnv m5HeurCoreModule`.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) on `nvOneLitCfg` /
   `nvOneLitState` / `nvOneLitMem` / `nvOneLitF0` (`nv_m5_save_target_best`, `nv_m5_backtrack`,
   `nv_m5_bump_analyzed`, `nv_m5_restore_bump_ana`, `nv_m5_warmup`, `nv_m5_otfs_subsume`,
   `nv_m5_eager_subsume`, `nv_m5_analyze`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5HeurCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Closed `35`-Row `m5HeurCoreSpecTable`, `m5HeurCoreEnv`, and `ModuleOk` -/

section ModuleOkSection

/-- Closed `35`-row specification table for `m5HeurCoreModule` (`11` defined functions +
`24` external callees, all `noExit = true`). -/
@[expose] def m5HeurCoreSpecTable : List SpecEntry :=
  [ ⟨"full_save_target_best_m5", [i64], [], fullSaveTargetBestSpec, true⟩
  , ⟨"full_backtrack_raw_m5", [i64, i64], [], fullBacktrackRawSpec, true⟩
  , ⟨"full_backtrack_m5", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_analyze_rsn_m5", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩
  , ⟨"full_otfs_subsume_m5", [i64, i32, i64, i64, .bool], [], fullOtfsSubsumeSpec, true⟩
  , ⟨"full_bump_analyzed_m5", [i64], [], fullBumpAnalyzedSpec, true⟩
  , ⟨"full_restore_bump_ana_m5", [i64], [], fullRestoreBumpAnaSpec, true⟩
  , ⟨"full_eager_subsume_m5", [i64, i64], [], fullEagerSubsumeSpec, true⟩
  , ⟨"full_learn_clause_m5", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  , ⟨"full_analyze_m5", [i64], [i64], fullAnalyzeSpec, true⟩
  , ⟨"full_warmup_m5", [i64], [], fullWarmupSpec, true⟩
  , ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  , ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  , ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  , ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  , ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  , ⟨"full_bump_analyzed", [i64], [], fullBumpAnalyzedSpec, true⟩
  , ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  , ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  , ⟨"full_eager_subsume", [i64, i64], [], fullEagerSubsumeSpec, true⟩
  , ⟨"full_one_lit_confl", [i64], [i64], fullOneLitConflSpec, true⟩
  , ⟨"full_deduce_1uip", [i64], [i64], fullDeduce1uipSpec, true⟩
  , ⟨"full_min_shrink", [i64], [], fullMinShrinkSpec, true⟩
  , ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩
  , ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  , ⟨"full_next_dec_var", [i64], [i64], fullNextDecVarSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩ ]

theorem m5HeurCoreSpecTable_nodup : (m5HeurCoreSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m5HeurCoreSpecTable_noExit : ∀ e ∈ m5HeurCoreSpecTable, e.noExit = true := by
  intro e he
  simp only [m5HeurCoreSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed environment for `m5HeurCoreModule`. -/
@[expose] def m5HeurCoreEnv : Env := Env.ofTable m5HeurCoreSpecTable

theorem m5HeurCoreEnv_noExit :
    ∀ f as bs xs m Q X X',
      m5HeurCoreEnv f as bs xs m Q X → m5HeurCoreEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m5HeurCoreSpecTable_noExit

private theorem m5HeurCoreEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m5HeurCoreSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m5HeurCoreEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m5HeurCoreSpecTable_nodup
      (hno xs m Q X hs)

theorem m5HeurCore_save_target_best_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_save_target_best_m5", [i64], [], full_save_target_best_m5_body⟩
      ⟨"full_save_target_best_m5", [i64], [], fullSaveTargetBestSpec, true⟩ :=
  SpecEntry.Impl.of (full_save_target_best_m5_wp m5HeurCoreEnv)

theorem m5HeurCore_backtrack_raw_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_backtrack_raw_m5", [i64, i64], [], full_backtrack_raw_m5_body⟩
      ⟨"full_backtrack_raw_m5", [i64, i64], [], fullBacktrackRawSpec, true⟩ :=
  SpecEntry.Impl.of (full_backtrack_raw_m5_wp m5HeurCoreEnv
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h)))

theorem m5HeurCore_backtrack_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_backtrack_m5", [i64, i64], [], full_backtrack_m5_body⟩
      ⟨"full_backtrack_m5", [i64, i64], [], fullBacktrackSpec, true⟩ :=
  SpecEntry.Impl.of (full_backtrack_m5_wp m5HeurCoreEnv
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h)))

theorem m5HeurCore_analyze_rsn_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_analyze_rsn_m5", [i64, i32, i32], [.bool], full_analyze_rsn_m5_body⟩
      ⟨"full_analyze_rsn_m5", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩ :=
  SpecEntry.Impl.of (full_analyze_rsn_m5_wp m5HeurCoreEnv
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h)))

theorem m5HeurCore_otfs_subsume_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_otfs_subsume_m5", [i64, i32, i64, i64, .bool], [], full_otfs_subsume_m5_body⟩
      ⟨"full_otfs_subsume_m5", [i64, i32, i64, i64, .bool], [], fullOtfsSubsumeSpec, true⟩ :=
  SpecEntry.Impl.of (full_otfs_subsume_m5_wp m5HeurCoreEnv)

theorem m5HeurCore_bump_analyzed_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_bump_analyzed_m5", [i64], [], full_bump_analyzed_m5_body⟩
      ⟨"full_bump_analyzed_m5", [i64], [], fullBumpAnalyzedSpec, true⟩ :=
  SpecEntry.Impl.of (full_bump_analyzed_m5_wp m5HeurCoreEnv
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h)))

theorem m5HeurCore_restore_bump_ana_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_restore_bump_ana_m5", [i64], [], full_restore_bump_ana_m5_body⟩
      ⟨"full_restore_bump_ana_m5", [i64], [], fullRestoreBumpAnaSpec, true⟩ :=
  SpecEntry.Impl.of (full_restore_bump_ana_m5_wp m5HeurCoreEnv
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h)))

theorem m5HeurCore_eager_subsume_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_eager_subsume_m5", [i64, i64], [], full_eager_subsume_m5_body⟩
      ⟨"full_eager_subsume_m5", [i64, i64], [], fullEagerSubsumeSpec, true⟩ :=
  SpecEntry.Impl.of (full_eager_subsume_m5_wp m5HeurCoreEnv)

theorem m5HeurCore_learn_clause_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_learn_clause_m5", [i64, i64], [i64], full_learn_clause_m5_body⟩
      ⟨"full_learn_clause_m5", [i64, i64], [i64], fullLearnClauseSpec, true⟩ :=
  SpecEntry.Impl.of (full_learn_clause_m5_wp m5HeurCoreEnv
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h)))

theorem m5HeurCore_analyze_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_analyze_m5", [i64], [i64], full_analyze_m5_body⟩
      ⟨"full_analyze_m5", [i64], [i64], fullAnalyzeSpec, true⟩ :=
  SpecEntry.Impl.of (full_analyze_m5_wp m5HeurCoreEnv
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h)))

theorem m5HeurCore_warmup_impl :
    SpecEntry.Impl m5HeurCoreEnv
      ⟨"full_warmup_m5", [i64], [], full_warmup_m5_body⟩
      ⟨"full_warmup_m5", [i64], [], fullWarmupSpec, true⟩ :=
  SpecEntry.Impl.of (full_warmup_m5_wp m5HeurCoreEnv
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h))
    (m5HeurCoreEnv_row (by simp [m5HeurCoreSpecTable]) (fun _ _ _ _ h => h)))

theorem m5HeurCore_allFns_wf : AllFns Fn.Wf m5HeurCoreModule.fns :=
  ⟨full_save_target_best_m5_wf, full_backtrack_raw_m5_wf, full_backtrack_m5_wf,
    full_analyze_rsn_m5_wf, full_otfs_subsume_m5_wf, full_bump_analyzed_m5_wf,
    full_restore_bump_ana_m5_wf, full_eager_subsume_m5_wf, full_learn_clause_m5_wf,
    full_analyze_m5_wf, full_warmup_m5_wf, trivial⟩

theorem m5HeurCore_tableImpl :
    TableImpl m5HeurCoreEnv m5HeurCoreModule.fns m5HeurCoreSpecTable :=
  ⟨m5HeurCore_save_target_best_impl, m5HeurCore_backtrack_raw_impl, m5HeurCore_backtrack_impl,
    m5HeurCore_analyze_rsn_impl, m5HeurCore_otfs_subsume_impl, m5HeurCore_bump_analyzed_impl,
    m5HeurCore_restore_bump_ana_impl, m5HeurCore_eager_subsume_impl, m5HeurCore_learn_clause_impl,
    m5HeurCore_analyze_impl, m5HeurCore_warmup_impl, trivial⟩

/-- Headline `ModuleOk` certifying all `11` functions of `m5HeurCoreModule` under `m5HeurCoreEnv`
(`35` spec rows, `0` exits, fully closed). -/
theorem m5HeurCore_moduleOk : ModuleOk m5HeurCoreEnv m5HeurCoreModule :=
  Env.ofTable_moduleOk m5HeurCore_acyclic m5HeurCore_allFns_wf m5HeurCore_tableImpl

end ModuleOkSection

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvM5HeurF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvM5_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvM5_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core := by
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nvM5_entails_0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

private theorem nvM5_mrkZero : FullMrkZero nvOneLitCfg nvOneLitState := fun v hv => by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl

private theorem nvM5_marksClear : FullLitMarksClear nvOneLitCfg nvOneLitState :=
  ⟨nvM5_mrkZero, fun l hl => by
    have hmv : nvOneLitCfg.max_vars = 1 := rfl
    rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl⟩

private theorem nvM5_nodup : FullArenaVarsNodup nvOneLitState := fun r hr => by
  have : fullArenaClauseRefs nvOneLitState = [] := rfl
  simp [this] at hr

private theorem nvM5_extOk : FullExtScratchOk nvOneLitCfg nvOneLitState :=
  ⟨FullLastLearnedWf.of_cleared fun i hi => by
    simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
      ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩

private theorem nvM5_sparse :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState :=
  ⟨nvOneLit_lengths, nvM5_witness, nvM5_marksClear, nvM5_nodup, nvM5_extOk, rfl⟩

private theorem nvM5_anaMarksCov : FullAnaMarksCov nvOneLitCfg nvOneLitState :=
  ⟨Nat.zero_le _, by simp [nvOneLitState], fun _ hk => by simp [nvOneLitState] at hk,
    fun v hv hnz => absurd (nvM5_mrkZero v hv) hnz⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_save_target_best_m5`. -/
theorem nv_m5_save_target_best :
    Func.wp m5HeurCoreEnv full_save_target_best_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m5HeurCore_save_target_best_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, hm, fun () s' m' hco hln hpr hm' => by
      rw [sep_emp] at hm'; exact ⟨s', hco, hln, hpr.1, nvM5HeurF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_backtrack_m5`. -/
theorem nv_m5_backtrack :
    Func.wp m5HeurCoreEnv full_backtrack_m5_body (nvOneLitCfg.hdr, 0#64, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ s'.core.cur_level = 0 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m5HeurCore_backtrack_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, by decide,
      (fun h => absurd h (by decide)), nvM5_witness.trail_lits_lt, hm, ?_⟩
  intro _ _ _ _ _ _ _ cl' _ _ m' _ hlen _ _ hcl _ _ _ _ _ _ hm'
  rw [sep_emp] at hm'
  have hcl0 : cl' = 0 := by rw [hcl]; rfl
  exact ⟨_, hlen, hcl0, nvM5HeurF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_bump_analyzed_m5`. -/
theorem nv_m5_bump_analyzed :
    Func.wp m5HeurCoreEnv full_bump_analyzed_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ FullAnaMarksCov nvOneLitCfg s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m5HeurCore_bump_analyzed_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvM5_anaMarksCov, hm, ?_⟩
  intro _ _ _ m' _ hlen hcov _ _ hm'
  rw [sep_emp] at hm'; exact ⟨_, hlen, hcov, nvM5HeurF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_restore_bump_ana_m5`. -/
theorem nv_m5_restore_bump_ana :
    Func.wp m5HeurCoreEnv full_restore_bump_ana_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧ FullMrkZero nvOneLitCfg s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m5HeurCore_restore_bump_ana_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvM5_mrkZero, hm, ?_⟩
  intro _ _ _ m' _ hlen hm0 _ _ hm'
  rw [sep_emp] at hm'; exact ⟨_, hlen, hm0, nvM5HeurF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_warmup_m5`. -/
theorem nv_m5_warmup :
    Func.wp m5HeurCoreEnv full_warmup_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m5HeurCore_warmup_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl,
      ⟨nvOneLit_lengths, [[0], [1]], nvM5_witness⟩, rfl, hm, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' _ hinv _ _ _ _ hm'
  rw [sep_emp] at hm'; exact ⟨_, hinv, nvM5HeurF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_otfs_subsume_m5`. -/
theorem nv_m5_otfs_subsume :
    Func.wp m5HeurCoreEnv full_otfs_subsume_m5_body
      (nvOneLitCfg.hdr, 0#32, 1#64, 0xFFFFFFFF#64, true, ()) nvOneLitMem
      (fun () m' => ∃ s', s'.LengthsOk nvOneLitCfg ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m5HeurCore_otfs_subsume_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], 1, nvOneLitState, emp, rfl, nvOneLit_lengths,
      nvM5_witness.toCut, nvM5_nodup, (fun h => absurd h (by decide)), hm, ?_⟩
  intro _ _ _ _ m' _ hlen _ _ _ _ hm'
  rw [sep_emp] at hm'; exact ⟨_, hlen, nvM5HeurF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_eager_subsume_m5`. -/
theorem nv_m5_eager_subsume :
    Func.wp m5HeurCoreEnv full_eager_subsume_m5_body
      (nvOneLitCfg.hdr, 0xFFFFFFFF#64, ()) nvOneLitMem
      (fun () m' => ∃ s', FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m5HeurCore_eager_subsume_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState, emp, rfl, nvM5_sparse,
      (fun _ hk => absurd hk (Nat.not_lt_zero _)), (fun h => absurd h (by decide)), hm, ?_⟩
  intro _ _ _ m' _ hsp _ hm'
  rw [sep_emp] at hm'; exact ⟨_, hsp, nvM5HeurF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_analyze_m5`: on the level-0 binary
conflict in `nvOneLitMem`, certifies `r = 20#64` and `nvOneLitF0.Unsat`. -/
theorem nv_m5_analyze :
    Func.wp m5HeurCoreEnv full_analyze_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s', r = 20#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  unfold Func.wp full_analyze_m5_body
  dsimp only
  rw [wp_let]
  refine wp_load_of (FullArenaTactics.load_full_cur_level hm) ?_
  refine wp_let_cmp _ _ _ _ _ _ rfl ?_
  refine wp_jnz_of (fun _ => ?_) (fun hf => absurd hf (by decide))
  rw [wp_ret]; exact ⟨nvOneLitState, rfl, nvM5HeurF0_unsat, nvOneLitMem_ok⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM5HeurCore
