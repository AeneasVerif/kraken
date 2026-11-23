module

public import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof0
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof1a
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof1b
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof2
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas

/-!
# Kissat M5 Dense-Safe Closed `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity

Top-level umbrella proof module for `FullM5DenseSafe` (dense-mode OOM, dedup, BVA headroom):
1. Publicly re-exports `FullM5DenseSafe` and all `8` parametric `Func.wp` proofs across
   `FullM5DenseSafeProof{0,1a,1b,2}` (`full_enter_dense_m5_wp`, `full_subst_rewrite_bins_m5_wp`,
   `full_subst_rewrite_ar_m5_wp`, `full_substitute_m5_wp`, `full_fwd_check_cl_m5_wp`,
   `full_bve_var_m5_wp`, `full_bve_var_m5_def_wp`, `full_bva_commit_m5_wp`).
2. Closes the `34`-row `m5DenseSafeSpecTable` (`7` upgraded functions + `27` external callees,
   all `noExit = true`), `m5DenseSafeEnv`, and `m5DenseSafe_moduleOk`.
3. Proves concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) on
   `nvOneLitMem` (sparse) and `nvBvaDenseMem` (dense).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM5DenseSafe

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM4Bva
open Kraken.Bedrock2.Test

/-! ## 1. Closed `34`-Row `m5DenseSafeSpecTable`, `m5DenseSafeEnv`, and `ModuleOk` -/

/-- Closed `34`-row specification table for `m5DenseSafeModule` (`7` upgraded M5 functions +
`27` canonical external callees, all `noExit = true`). -/
@[expose] public def m5DenseSafeSpecTable : List SpecEntry :=
  [ ⟨"full_enter_dense_m5", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_subst_rewrite_bins_m5", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  , ⟨"full_subst_rewrite_ar_m5", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  , ⟨"full_substitute_m5", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_fwd_check_cl_m5", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
  , ⟨"full_bve_var_m5", [i64, i32], [i64], fullBveVarSpec, true⟩
  , ⟨"full_bva_commit_m5", [i64, i32], [.bool], m4BvaCommitSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  , ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccSpec, true⟩
  , ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  , ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  , ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_gates", [i64, i32, i32, i32], [], fullBveGatesSpec, true⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenSpec, true⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResSpec, true⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarHeapSpec, true⟩ ]

public theorem m5DenseSafeSpecTable_nodup : (m5DenseSafeSpecTable.map SpecEntry.name).Nodup := by
  decide

public theorem m5DenseSafeSpecTable_noExit : ∀ e ∈ m5DenseSafeSpecTable, e.noExit = true := by
  intro e he
  simp only [m5DenseSafeSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed environment for `m5DenseSafeModule`. -/
@[expose] public def m5DenseSafeEnv : Env := Env.ofTable m5DenseSafeSpecTable

public theorem m5DenseSafeEnv_noExit :
    ∀ f as bs xs m Q X X',
      m5DenseSafeEnv f as bs xs m Q X → m5DenseSafeEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m5DenseSafeSpecTable_noExit

private theorem m5Env_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m5DenseSafeSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m5DenseSafeEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m5DenseSafeSpecTable_nodup
      (hno xs m Q X hs)

public theorem m5_enter_dense_impl :
    SpecEntry.Impl m5DenseSafeEnv
      ⟨"full_enter_dense_m5", [i64], [.bool], full_enter_dense_m5_body⟩
      ⟨"full_enter_dense_m5", [i64], [.bool], schedEnterDenseSpec, true⟩ :=
  SpecEntry.Impl.of (full_enter_dense_m5_wp m5DenseSafeEnv
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h)))

public theorem m5_subst_rewrite_bins_impl :
    SpecEntry.Impl m5DenseSafeEnv
      ⟨"full_subst_rewrite_bins_m5", [i64], [.bool], full_subst_rewrite_bins_m5_body⟩
      ⟨"full_subst_rewrite_bins_m5", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩ :=
  SpecEntry.Impl.of (full_subst_rewrite_bins_m5_wp m5DenseSafeEnv
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h)))

public theorem m5_subst_rewrite_ar_impl :
    SpecEntry.Impl m5DenseSafeEnv
      ⟨"full_subst_rewrite_ar_m5", [i64], [.bool], full_subst_rewrite_ar_m5_body⟩
      ⟨"full_subst_rewrite_ar_m5", [i64], [.bool], fullSubstRewriteArSpec, true⟩ :=
  SpecEntry.Impl.of (full_subst_rewrite_ar_m5_wp m5DenseSafeEnv
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h)))

public theorem m5_substitute_impl :
    SpecEntry.Impl m5DenseSafeEnv
      ⟨"full_substitute_m5", [i64], [i64], full_substitute_m5_body⟩
      ⟨"full_substitute_m5", [i64], [i64], fullSubstituteSpec, true⟩ :=
  SpecEntry.Impl.of (full_substitute_m5_wp m5DenseSafeEnv
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h)))

public theorem m5_fwd_check_cl_impl :
    SpecEntry.Impl m5DenseSafeEnv
      ⟨"full_fwd_check_cl_m5", [i64, i32], [.bool], full_fwd_check_cl_m5_body⟩
      ⟨"full_fwd_check_cl_m5", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩ :=
  SpecEntry.Impl.of (full_fwd_check_cl_m5_wp m5DenseSafeEnv
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h)))

public theorem m5_bve_var_impl :
    SpecEntry.Impl m5DenseSafeEnv
      ⟨"full_bve_var_m5", [i64, i32], [i64], full_bve_var_m5_body⟩
      ⟨"full_bve_var_m5", [i64, i32], [i64], fullBveVarSpec, true⟩ :=
  SpecEntry.Impl.of (full_bve_var_m5_wp m5DenseSafeEnv
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h)))

public theorem m5_bva_commit_impl :
    SpecEntry.Impl m5DenseSafeEnv
      ⟨"full_bva_commit_m5", [i64, i32], [.bool], full_bva_commit_m5_body⟩
      ⟨"full_bva_commit_m5", [i64, i32], [.bool], m4BvaCommitSpec, true⟩ :=
  SpecEntry.Impl.of (full_bva_commit_m5_wp m5DenseSafeEnv
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h))
    (m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h)))

public theorem m5DenseSafe_allFns_wf : AllFns Fn.Wf m5DenseSafeModule.fns :=
  ⟨full_enter_dense_m5_wf, full_subst_rewrite_bins_m5_wf, full_subst_rewrite_ar_m5_wf,
    full_substitute_m5_wf, full_fwd_check_cl_m5_wf, full_bve_var_m5_wf,
    full_bva_commit_m5_wf, trivial⟩

public theorem m5DenseSafe_tableImpl :
    TableImpl m5DenseSafeEnv m5DenseSafeModule.fns m5DenseSafeSpecTable :=
  ⟨m5_enter_dense_impl, m5_subst_rewrite_bins_impl, m5_subst_rewrite_ar_impl,
    m5_substitute_impl, m5_fwd_check_cl_impl, m5_bve_var_impl, m5_bva_commit_impl, trivial⟩

/-- Headline closed `ModuleOk` certifying all `7` upgraded M5 dense-safe functions in
`m5DenseSafeModule` under `m5DenseSafeEnv` (`0` gaps, `0` SAT proofs). -/
public theorem m5DenseSafe_moduleOk : ModuleOk m5DenseSafeEnv m5DenseSafeModule :=
  Env.ofTable_moduleOk m5DenseSafe_acyclic m5DenseSafe_allFns_wf m5DenseSafe_tableImpl

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteUnsatNonVacuity

private theorem nvM5F0_unsat : nvOneLitF0.Unsat := by
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

private theorem nvM5_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact WatchSliceOk.empty
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact hent0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · have : fullArenaClauseRefs nvOneLitState = [] := rfl; simp [this] at hr

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_enter_dense_m5`. -/
public theorem nv_m5_enter_dense :
    Func.wp m5DenseSafeEnv full_enter_dense_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (ok, ()) m' => ∃ s',
        (if ok then FullDenseInv nvOneLitCfg nvOneLitF0 s'
         else FullSparseInv nvOneLitCfg nvOneLitF0 s') ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m5_enter_dense_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvM5_sparseW.toSparse, hm,
      fun ok s' m' _ _ hd hf hm' => by
        rw [sep_emp] at hm'
        exact ⟨s', by cases ok <;> simp [hd, hf], nvM5F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_substitute_m5`. -/
public theorem nv_m5_substitute :
    Func.wp m5DenseSafeEnv full_substitute_m5_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m5_substitute_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvM5_sparseW.toSparse, hm,
      fun r s' m' hsp _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, nvM5F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bve_var_m5`. -/
public theorem nv_m5_bve_var :
    Func.wp m5DenseSafeEnv full_bve_var_m5_body (nvOneLitCfg.hdr, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact m5_bve_var_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, by decide, hm,
      fun r s' m' hd _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, hr, nvM5F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` `TmkZero`-preserving UNSAT non-vacuity (`XPost := False`) for
`full_bve_var_m5` (`fullBveVarDefSpec`). -/
public theorem nv_m5_bve_var_def :
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
      (fun _ _ _ _ => False) := by
  intro Γdef
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have htmk : TmkZero nvBvaDenseState := fun v hv => by
    change v < 1 at hv; obtain rfl : v = 0 := (by omega); rfl
  refine full_bve_var_m5_def_wp Γdef
    (fun xs m Q X h =>
      m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun xs m Q X h =>
      m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun xs m Q X h =>
      m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    (fun xs m Q X h =>
      m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    (fun xs m Q X h =>
      m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    (fun xs m Q X h =>
      m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    (fun xs m Q X h =>
      m5Env_row (by simp [m5DenseSafeSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, htmk,
      by decide, hm, fun r s' m' hd htm' _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, htm', hr, nvM5F0_unsat, hm'⟩⟩

end ConcreteUnsatNonVacuity

end LeanQbe.T.Examples.Kissat.FullM5DenseSafe
