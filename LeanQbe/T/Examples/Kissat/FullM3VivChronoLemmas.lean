module

public import LeanQbe.T.Examples.Kissat.FullM3VivChronoLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3VivChronoLemmas2
public import LeanQbe.T.Examples.Kissat.FullM3VivChronoLemmas3
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipNv
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M3a Combined `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity

Combines `FullM3VivChronoLemmas1`, `FullM3VivChronoLemmas2`, and `FullM3VivChronoLemmas3` into:
1. Closed `15`-row specification table `m3SpecTable` (`5` upgraded M3a functions + `10` externs, all
   `noExit = true`), `m3Env := Env.ofTable m3SpecTable`, `m3_tableImpl`, and
   `m3_moduleOk : ModuleOk m3Env m3Module`.
2. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for all `5` M3a
   functions (`full_tick_rel`, `full_analyze_rsn`, `full_prop_lit`, `full_vivify`,
   `full_probe_tail`) under `m3Env`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3VivChrono

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open Kraken.Bedrock2.Test

/-! ## 1. Closed `15`-Row `m3SpecTable`, `m3Env`, and `ModuleOk m3Env m3Module` -/

section ModuleOkSection

/-- Closed `15`-row `m3SpecTable` (`5` M3a functions + `10` external callees, all `noExit`). -/
def m3SpecTable : List SpecEntry :=
  [ ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩
  , ⟨"full_prop_lit", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  , ⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩
  , ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  , ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_viv_clause", [i64, i32], [i64], fullVivClauseSpec, true⟩
  , ⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩
  , ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩ ]

theorem m3SpecTable_nodup : (m3SpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m3SpecTable_noExit : ∀ e ∈ m3SpecTable, e.noExit = true := by
  intro e he
  simp only [m3SpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

/-- Closed environment for `m3Module` (`5` upgraded M3a functions + `10` externs). -/
def m3Env : Env := Env.ofTable m3SpecTable

theorem m3Env_noExit :
    ∀ f as bs xs m Q X X', m3Env f as bs xs m Q X → m3Env f as bs xs m Q X' :=
  Env.ofTable_noExit m3SpecTable_noExit

private theorem m3Env_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m3SpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m3Env nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m3SpecTable_nodup (hno xs m Q X hs)

theorem m3_tick_rel_impl :
    SpecEntry.Impl m3Env
      ⟨"full_tick_rel", [i64], [], full_tick_rel_body⟩
      ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩ :=
  SpecEntry.Impl.of (m3_tick_rel_wp m3Env)

theorem m3_analyze_rsn_impl :
    SpecEntry.Impl m3Env
      ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], full_analyze_rsn_body⟩
      ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩ :=
  SpecEntry.Impl.of (m3_analyze_rsn_wp m3Env
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h)))

theorem m3_prop_lit_impl :
    SpecEntry.Impl m3Env
      ⟨"full_prop_lit", [i64, i32, i64], [.bool], full_prop_lit_body⟩
      ⟨"full_prop_lit", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩ :=
  SpecEntry.Impl.of (m3_prop_lit_wp m3Env
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h))
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h)))

theorem m3_vivify_impl :
    SpecEntry.Impl m3Env
      ⟨"full_vivify", [i64, i64, i64], [i64], full_vivify_body⟩
      ⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩ :=
  SpecEntry.Impl.of (m3_vivify_wp m3Env
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h))
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h))
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h))
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h)))

theorem m3_probe_tail_impl :
    SpecEntry.Impl m3Env
      ⟨"full_probe_tail", [i64, i64], [i64], full_probe_tail_body⟩
      ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩ :=
  SpecEntry.Impl.of (m3_probe_tail_wp m3Env
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h))
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h))
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h))
    (m3Env_row (by simp [m3SpecTable]) (fun _ _ _ _ h => h)))

theorem m3_allFns_wf : AllFns Fn.Wf m3Module.fns :=
  ⟨full_tick_rel_wf, full_analyze_rsn_wf, full_prop_lit_wf, full_vivify_wf,
    full_probe_tail_wf, trivial⟩

theorem m3_tableImpl : TableImpl m3Env m3Module.fns m3SpecTable :=
  ⟨m3_tick_rel_impl, m3_analyze_rsn_impl, m3_prop_lit_impl, m3_vivify_impl,
    m3_probe_tail_impl, trivial⟩

/-- Headline `ModuleOk` certifying all `5` upgraded M3a functions in `m3Module` (`0` `sorry`). -/
theorem m3_moduleOk : ModuleOk m3Env m3Module :=
  Env.ofTable_moduleOk m3_acyclic m3_allFns_wf m3_tableImpl

end ModuleOkSection

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

section ConcreteNonVacuity

private theorem nvM3_sparseW :
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

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `m3VivChrono.full_tick_rel`. -/
theorem nv_m3_tick_rel :
    Func.wp m3Env full_tick_rel_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_tick_rel_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, hm, fun () s' m' hco hln hpr hm' => by
      rw [sep_emp] at hm'; exact ⟨s', hco, hln, hpr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `m3VivChrono.full_analyze_rsn`. -/
theorem nv_m3_analyze_rsn :
    Func.wp m3Env full_analyze_rsn_body (nvOneLitCfg.hdr, 0x80000000#32, 0#32, ()) nvOneLitMem
      (fun (_ok, ()) m' => ∃ mrk' tmp' tc' tl' mcl' arena' sc',
        let s' : FullState :=
          { nvOneLitState with
            core := { nvOneLitState.core with
              mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
              min_clr_len := mcl', arena := arena' }
            scratch := sc' }
        s'.LengthsOk nvOneLitCfg ∧
        FullWitnessCutInv nvOneLitCfg nvOneLitF0 [[0], [1]]
          nvOneLitState.core.trail_end s'.core ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have hcov : FullAnaMarksCov nvOneLitCfg nvOneLitState := by
    refine ⟨Nat.zero_le _, List.Pairwise.nil, (fun k hk => by cases hk), fun v hv hnz => ?_⟩
    have hv0 : v = 0 := by change v < 1 at hv; omega
    subst hv0; exact absurd rfl hnz
  refine m3_analyze_rsn_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState.core.trail_end, nvOneLitState, emp,
      rfl, nvOneLit_lengths, nvM3_sparseW.2.1.toCut, hcov, by decide, by decide,
      fun _ hlg => absurd hlg (by decide), hm,
      fun _ mrk' tmp' tc' tl' mcl' arena' sc' m' hlen' hw' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm' =>
        by rw [sep_emp] at hm'; exact ⟨mrk', tmp', tc', tl', mcl', arena', sc', hlen', hw',
          nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `m3VivChrono.full_prop_lit`. -/
theorem nv_m3_prop_lit :
    Func.wp m3Env full_prop_lit_body (nvOneLitCfg.hdr, 0#32, 0#64, ()) nvOneLitMem
      (fun (_ok, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧
        FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] s'.core ∧
        s'.core.dense_mode = 0#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_prop_lit_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState, emp, rfl, nvOneLit_lengths,
      nvM3_sparseW.2.1, rfl, rfl, hm,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' hlen' hw' _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen', hw', rfl, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for Tier-3 `m3VivChrono.full_vivify`. -/
theorem nv_m3_vivify :
    Func.wp m3Env full_vivify_body (nvOneLitCfg.hdr, 3#64, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_vivify_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvM3_sparseW.toSparse, hm,
      fun r s' m' hsp _ _ hnz _ hr _ hm' => by
        obtain ⟨hcl0, hpr0⟩ := hnz (by decide)
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl0, hpr0, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `m3VivChrono.full_probe_tail`. -/
theorem nv_m3_probe_tail :
    Func.wp m3Env full_probe_tail_body (nvOneLitCfg.hdr, 0#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_probe_tail_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvM3_sparseW.toSparse, rfl, hm,
      fun r s' m' hsp hcl0 _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl0, hr, nvDeduceF0_unsat, hm'⟩⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM3VivChrono
