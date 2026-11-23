module

public import LeanQbe.T.Examples.Kissat.FullM6WalkParse
public import LeanQbe.T.Examples.Kissat.FullM6WalkParseProof1
public import LeanQbe.T.Examples.Kissat.FullM6WalkParseProof2
public import LeanQbe.T.Examples.Kissat.FullM6WalkParseProof3
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Parse-BCP & Walk: `ModuleOk` & Concrete `Mem 64` UNSAT NV

Combines the `11` parametric UNSAT-only `Func.wp` proofs (`Proof1`, `Proof2`, `Proof3`) into:
1. Closed `18`-row `m6WalkParseSpecTable` (`11` defined functions + `7` canonical externs, all
   `noExit = true`).
2. `m6WalkParseEnv` and headline `m6WalkParse_moduleOk : ModuleOk m6WalkParseEnv m6WalkParseModule`.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs):
   - `nv_m6_rescale`, `nv_m6_walk_core`, `nv_m6_walk` on `nvOneLitCfg` / `nvOneLitMem`.
   - `nv_m6_parse_body` on concrete UNSAT DIMACS `"p cnf 1 2\n1 0\n-1 0\n"` certifying `r = 20#64`
     and `∃ cnf, parseDimacs m6NvUnsatBytes = some cnf ∧ cnf.Unsat`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6WalkParse

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Closed `18`-Row `m6WalkParseSpecTable`, `m6WalkParseEnv`, and `ModuleOk` -/

section ModuleOkSection

/-- Closed `18`-row specification table for `m6WalkParseModule` (`11` defined functions +
`7` external callees, all `noExit = true`). -/
@[expose] def m6WalkParseSpecTable : List SpecEntry :=
  [ ⟨"full_rescale_m6", [i64], [], fullRescaleSpec, true⟩
  , ⟨"full_parse_body_m6", [i64, i64], [i64], fullParseBodySpec, true⟩
  , ⟨"full_walk_cb_inv_m6", [i64, i64, i64], [i64], m6WalkCbInvSpec, true⟩
  , ⟨"full_walk_score_m6", [i64, i64], [i32], m6WalkScoreSpec, true⟩
  , ⟨"full_walk_collect_m6", [i64, i64, i64], [i64], m6WalkCollectSpec, true⟩
  , ⟨"full_walk_build_csr_m6", [i64, i64, i64, i64], [i64], m6WalkBuildCsrSpec, true⟩
  , ⟨"full_walk_break_m6", [i64, i32, i64, i64, i64], [i64], m6WalkBreakSpec, true⟩
  , ⟨"full_walk_pick_m6", [i64, i64, i64, i64, i64, i64], [i32], m6WalkPickSpec, true⟩
  , ⟨"full_walk_flip_m6", [i64, i32, i64, i64, i64, i64], [i64], m6WalkFlipSpec, true⟩
  , ⟨"full_walk_core_m6", [i64], [], fullWalkSpec, true⟩
  , ⟨"full_walk_m6", [i64], [], m6WalkSpec, true⟩
  , ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  , ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, true⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩ ]

theorem m6WalkParseSpecTable_nodup : (m6WalkParseSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m6WalkParseSpecTable_noExit : ∀ e ∈ m6WalkParseSpecTable, e.noExit = true := by
  intro e he
  dsimp only [m6WalkParseSpecTable] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed environment for `m6WalkParseModule`. -/
@[expose] def m6WalkParseEnv : Env := Env.ofTable m6WalkParseSpecTable

theorem m6WalkParseEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6WalkParseEnv f as bs xs m Q X → m6WalkParseEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6WalkParseSpecTable_noExit

private theorem m6WalkParseEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m6WalkParseSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m6WalkParseEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m6WalkParseSpecTable_nodup
      (hno xs m Q X hs)

theorem m6WalkParse_rescale_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_rescale_m6", [i64], [], full_rescale_m6_body⟩
      ⟨"full_rescale_m6", [i64], [], fullRescaleSpec, true⟩ :=
  SpecEntry.Impl.of (full_rescale_m6_wp m6WalkParseEnv)

theorem m6WalkParse_parse_body_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_parse_body_m6", [i64, i64], [i64], full_parse_body_m6_body⟩
      ⟨"full_parse_body_m6", [i64, i64], [i64], fullParseBodySpec, true⟩ :=
  SpecEntry.Impl.of (full_parse_body_m6_wp m6WalkParseEnv
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h)))

theorem m6WalkParse_cb_inv_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_cb_inv_m6", [i64, i64, i64], [i64], full_walk_cb_inv_m6_body⟩
      ⟨"full_walk_cb_inv_m6", [i64, i64, i64], [i64], m6WalkCbInvSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_cb_inv_m6_wp m6WalkParseEnv)

theorem m6WalkParse_score_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_score_m6", [i64, i64], [i32], full_walk_score_m6_body⟩
      ⟨"full_walk_score_m6", [i64, i64], [i32], m6WalkScoreSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_score_m6_wp m6WalkParseEnv)

theorem m6WalkParse_collect_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_collect_m6", [i64, i64, i64], [i64], full_walk_collect_m6_body⟩
      ⟨"full_walk_collect_m6", [i64, i64, i64], [i64], m6WalkCollectSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_collect_m6_wp m6WalkParseEnv
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h)))

theorem m6WalkParse_build_csr_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_build_csr_m6", [i64, i64, i64, i64], [i64], full_walk_build_csr_m6_body⟩
      ⟨"full_walk_build_csr_m6", [i64, i64, i64, i64], [i64], m6WalkBuildCsrSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_build_csr_m6_wp m6WalkParseEnv)

theorem m6WalkParse_break_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_break_m6", [i64, i32, i64, i64, i64], [i64], full_walk_break_m6_body⟩
      ⟨"full_walk_break_m6", [i64, i32, i64, i64, i64], [i64], m6WalkBreakSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_break_m6_wp m6WalkParseEnv)

theorem m6WalkParse_pick_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_pick_m6", [i64, i64, i64, i64, i64, i64], [i32], full_walk_pick_m6_body⟩
      ⟨"full_walk_pick_m6", [i64, i64, i64, i64, i64, i64], [i32], m6WalkPickSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_pick_m6_wp m6WalkParseEnv
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h)))

theorem m6WalkParse_flip_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_flip_m6", [i64, i32, i64, i64, i64, i64], [i64], full_walk_flip_m6_body⟩
      ⟨"full_walk_flip_m6", [i64, i32, i64, i64, i64, i64], [i64], m6WalkFlipSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_flip_m6_wp m6WalkParseEnv)

theorem m6WalkParse_walk_core_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_core_m6", [i64], [], full_walk_core_m6_body⟩
      ⟨"full_walk_core_m6", [i64], [], fullWalkSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_core_m6_wp m6WalkParseEnv
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h)))

theorem m6WalkParse_walk_impl :
    SpecEntry.Impl m6WalkParseEnv
      ⟨"full_walk_m6", [i64], [], full_walk_m6_body⟩
      ⟨"full_walk_m6", [i64], [], m6WalkSpec, true⟩ :=
  SpecEntry.Impl.of (full_walk_m6_wp m6WalkParseEnv
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h))
    (m6WalkParseEnv_row (by dsimp only [m6WalkParseSpecTable]; simp) (fun _ _ _ _ h => h)))

theorem m6WalkParse_allFns_wf : AllFns Fn.Wf m6WalkParseModule.fns :=
  ⟨full_rescale_m6_wf, full_parse_body_m6_wf, full_walk_cb_inv_m6_wf, full_walk_score_m6_wf,
    full_walk_collect_m6_wf, full_walk_build_csr_m6_wf, full_walk_break_m6_wf,
    full_walk_pick_m6_wf, full_walk_flip_m6_wf, full_walk_core_m6_wf, full_walk_m6_wf, trivial⟩

theorem m6WalkParse_tableImpl :
    TableImpl m6WalkParseEnv m6WalkParseModule.fns m6WalkParseSpecTable :=
  ⟨m6WalkParse_rescale_impl, m6WalkParse_parse_body_impl, m6WalkParse_cb_inv_impl,
    m6WalkParse_score_impl, m6WalkParse_collect_impl, m6WalkParse_build_csr_impl,
    m6WalkParse_break_impl, m6WalkParse_pick_impl, m6WalkParse_flip_impl,
    m6WalkParse_walk_core_impl, m6WalkParse_walk_impl, trivial⟩

/-- Headline `ModuleOk` certifying all `11` functions of `m6WalkParseModule` under
`m6WalkParseEnv` (`18` spec rows, `0` exits, fully closed). -/
theorem m6WalkParse_moduleOk : ModuleOk m6WalkParseEnv m6WalkParseModule :=
  Env.ofTable_moduleOk m6WalkParse_acyclic m6WalkParse_allFns_wf m6WalkParse_tableImpl

end ModuleOkSection

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvM6F0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0, cnfOfClauses]; simp))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0, cnfOfClauses]; simp))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvM6_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvM6_witness :
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
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nvM6_entails_0
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

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_rescale_m6`. -/
theorem nv_m6_rescale :
    Func.wp m6WalkParseEnv full_rescale_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m6WalkParse_rescale_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, hm, fun () s' m' hco hln hpr hm' => by
      rw [sep_emp] at hm'; exact ⟨s', hco, hln, hpr, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_walk_core_m6`. -/
theorem nv_m6_walk_core :
    Func.wp m6WalkParseEnv full_walk_core_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ fuel' sc',
        let s' := { nvOneLitState with core := { nvOneLitState.core with fuel := fuel' },
                                       scratch := sc' }
        FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have hinv0 : FullCoreInv nvOneLitCfg nvOneLitF0 nvOneLitState :=
    ⟨nvOneLit_lengths, [[0], [1]], nvM6_witness⟩
  refine m6WalkParse_walk_core_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, hinv0, hm, ?_⟩
  intro fuel' sc' m'
  dsimp only
  intro hlen' _ _ hm'
  rw [sep_emp] at hm'
  exact ⟨fuel', sc', hinv0.with_fuel_scratch_spec hlen' rfl, nvM6F0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_walk_m6`. -/
theorem nv_m6_walk :
    Func.wp m6WalkParseEnv full_walk_m6_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s', FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine m6WalkParse_walk_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl,
      ⟨nvOneLit_lengths, [[0], [1]], nvM6_witness⟩, rfl, hm, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' _ hinv _ _ _ _ hm'
  rw [sep_emp] at hm'; exact ⟨_, hinv, nvM6F0_unsat, hm'⟩

/-! ### Concrete UNSAT DIMACS Non-Vacuity for `full_parse_body_m6` -/

/-- Concrete UNSAT DIMACS byte buffer `"p cnf 1 2\n1 0\n-1 0\n"` (`19` bytes). -/
@[expose] def m6NvUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Concrete base address for `m6NvUnsatBytes` immediately after `nvOneLitCfg` (`0x16DC`). -/
@[expose] def m6NvCnfPtr : BitVec 64 := nvOneLitCfg.hdr + 1756#64

/-- Concrete initial pre-body state on `nvOneLitCfg`: `vals = [0, 0]`, `trail_end = 0`,
`d_cur = m6NvCnfPtr + 9` (right after `"p cnf 1 2"`). -/
@[expose] def nvM6ParseState : FullState :=
  { nvOneLitState with
    core :=
      { nvOneLitState.core with
        d_cur := m6NvCnfPtr + 9#64, unassigned := 1#64, trail_end := 0, confl_type := 0#64,
        vals := [0#8, 0#8] } }

/-- Concrete `1756`-byte solver image for `nvM6ParseState`. -/
@[expose] def nvM6ParseBytes : List UInt8 :=
  (bytes64 [1#64, 2#64, m6NvCnfPtr + 9#64, 0#64] ++
    bytes64 (Full.hdrTailWords nvOneLitCfg nvM6ParseState)) ++
  ((bytesOf (t := i8) nvM6ParseState.core.vals ++ List.replicate 6 0) ++
   (bytesOf (t := i8) nvOneLitState.scratch.walk_vals ++ List.replicate 6 0) ++
   (bytesOf (t := i8) nvOneLitState.core.lit_mark ++ List.replicate 6 0) ++
   (bytesOf (t := i8) nvOneLitState.core.mrk ++ List.replicate 7 0) ++
   (bytesOf (t := i8) nvOneLitState.scratch.phases ++ List.replicate 7 0) ++
   (bytesOf (t := i8) nvOneLitState.scratch.phases_target ++ List.replicate 7 0) ++
   (bytesOf (t := i8) nvOneLitState.scratch.phases_best ++ List.replicate 7 0) ++
   (bytesOf (t := i8) nvOneLitState.scratch.walk_best ++ List.replicate 7 0)) ++
  nvBlockU32A ++ nvBlockU32B ++ nvBlockU32C ++ nvBlockWvec ++ nvBlockTail

/-- Concrete `Mem 64` containing both `FullMem nvOneLitCfg nvM6ParseState` (at `0x1000..0x16DC`)
and `bytes m6NvCnfPtr m6NvUnsatBytes` (at `0x16DC..0x16EF`). -/
@[expose] def nvM6ParseMem : Mem 64 :=
  (nvM6ParseBytes ++ m6NvUnsatBytes).At nvOneLitCfg.hdr

private theorem nvM6_parseBytes_len : nvM6ParseBytes.length = 1756 := by
  dsimp only [nvM6ParseBytes, nvBlockU32A, nvBlockU32B, nvBlockU32C, nvBlockWvec, nvBlockTail,
    nvM6ParseState, nvOneLitState, nvOneLitScratch]
  simp only [List.length_append, List.length_replicate, bytesOf_length, bytes64_length,
    Full.hdrTailWords_length, List.length_cons, List.length_nil]
  decide

private theorem nvM6_parseState_lengths : nvM6ParseState.LengthsOk nvOneLitCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   nvOneLit_lengths.scratch_ok⟩

private theorem nvM6_parseState_sparse :
    FullSparseInv nvOneLitCfg (shiftDownCnf CNF.empty) nvM6ParseState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvM6ParseState.core.cur_vars = 1 := rfl
  have hcl0 : nvM6ParseState.core.cur_level = 0 := rfl
  have hdm : nvM6ParseState.core.dense_mode = 0#64 := rfl
  have hrefs : fullArenaClauseRefsCore nvM6ParseState.core = [] := rfl
  have hwat : ModeWatchesInv [] nvM6ParseState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (dsimp only [fullWatchSizeCore, nvM6ParseState, nvOneLitState] at hp; simp at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (dsimp only [fullWatchSizeCore, nvM6ParseState, nvOneLitState] at hp; simp at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  have hwit : FullWitnessInv nvOneLitCfg (shiftDownCnf CNF.empty) [] nvM6ParseState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 []).mp rfl, fun h _ => by
        have hs : (cnfOfClauses []).Sat (fun _ => false) :=
          CNF.sat_iff_all_mem_sat.mpr fun _ hc =>
            absurd (CNF.Internal.mem_iff.mp hc) (by simp [cnfOfClauses])
        have hf := h (fun _ => false)
        dsimp only [CNF.Sat] at hs
        rw [hs] at hf; cases hf⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun _ hi => absurd hi (Nat.not_lt_zero _)
      trail_vars_nodup := fun _ _ hi => absurd hi (Nat.not_lt_zero _)
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          exact Or.inl rfl
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨_, hi, _⟩; exact absurd hi (Nat.not_lt_zero _)
        · constructor
          · intro h; cases h
          · rintro ⟨_, hi, _⟩; exact absurd hi (Nat.not_lt_zero _)
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨_, hi, _⟩; exact absurd hi (Nat.not_lt_zero _)
        · constructor
          · intro h; cases h
          · rintro ⟨_, hi, _⟩; exact absurd hi (Nat.not_lt_zero _)
      lvl_le := fun _ hi => absurd hi (Nat.not_lt_zero _)
      dec_earliest := fun _ _ _ hj => absurd hj (Nat.not_lt_zero _)
      levels_inhabited := fun _ _ h2 => by rw [hcl0] at h2; omega
      level0_sound := fun _ hi => absurd hi (Nat.not_lt_zero _)
      trail_pos_inv := fun _ hi => absurd hi (Nat.not_lt_zero _)
      level0_rsn_none := fun _ hi => absurd hi (Nat.not_lt_zero _)
      frame_trail_lt := fun L hL => by
        rw [hcl0] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl0] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl0] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl0] at h2; omega
      reason_inv := fun _ hi => absurd hi (Nat.not_lt_zero _)
      reason_lit_mem := fun _ hi => absurd hi (Nat.not_lt_zero _) }
  have hmrk : FullMrkZero nvOneLitCfg nvM6ParseState := fun v hv => by
    rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  have hmc : FullLitMarksClear nvOneLitCfg nvM6ParseState :=
    ⟨hmrk, fun l hl => by rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl⟩
  have hnd : FullArenaVarsNodup nvM6ParseState := fun r hr => by
    have : fullArenaClauseRefs nvM6ParseState = [] := rfl; simp [this] at hr
  have hext : FullExtScratchOk nvOneLitCfg nvM6ParseState :=
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      dsimp only [nvM6ParseState, nvOneLitState, nvOneLitScratch]
      simp only [List.getElem?_replicate, show i < 16 by omega, ↓reduceIte, Option.getD_some],
      Nat.le_refl 0⟩
  exact ⟨⟨nvM6_parseState_lengths, [], hwit⟩, hmc, hnd, hext, rfl⟩

private theorem nvM6_parseMem_ok :
    (bytes m6NvCnfPtr m6NvUnsatBytes ⋆ FullMem nvOneLitCfg nvM6ParseState ⋆ emp)
      nvM6ParseMem := by
  let c := nvOneLitCfg; let s := nvM6ParseState
  have hfull : FullMem c s (nvM6ParseBytes.At c.hdr) := by
    let bHdr := bytes64 [1#64, 2#64, m6NvCnfPtr + 9#64, 0#64] ++
      bytes64 (Full.hdrTailWords c s)
    let bBytes := (bytesOf (t := i8) s.core.vals ++ List.replicate 6 0) ++
      (bytesOf (t := i8) nvOneLitState.scratch.walk_vals ++ List.replicate 6 0) ++
      (bytesOf (t := i8) nvOneLitState.core.lit_mark ++ List.replicate 6 0) ++
      (bytesOf (t := i8) nvOneLitState.core.mrk ++ List.replicate 7 0) ++
      (bytesOf (t := i8) nvOneLitState.scratch.phases ++ List.replicate 7 0) ++
      (bytesOf (t := i8) nvOneLitState.scratch.phases_target ++ List.replicate 7 0) ++
      (bytesOf (t := i8) nvOneLitState.scratch.phases_best ++ List.replicate 7 0) ++
      (bytesOf (t := i8) nvOneLitState.scratch.walk_best ++ List.replicate 7 0)
    have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
    have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
    have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
    have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
    have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
    have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
    have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
    have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
    have hHdr : bHdr.length = 1152 ∧
        (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
          (bHdr.At c.hdr) :=
      nv_join_pair
        (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, m6NvCnfPtr + 9#64, 0#64]) 32 rfl (by decide))
        (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
          (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
    have hBytes : bBytes.length = 64 ∧
        (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
          (bBytes.At c.pVals) := by
      have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
      have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
        (by decide)
      have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
        (by decide)
      have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
      have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
        (by decide)
      have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 1 7
        rfl (by decide)
      have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 1 7 rfl
        (by decide)
      have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 1 7 rfl
        (by decide)
      let pB1 : Mem 64 → Prop :=
        region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
        region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
      have h12 := nv_join_pair h1 h2 (by decide) (by decide)
      have h123 := nv_join_pair h12 h3 (by decide) (by decide)
      have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
        (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
        fun _ hm => nv_zip4 hm
      have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
      have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
      have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
      have hall := nv_join_pair h1234567 h8 (by decide) (by decide)
      exact nv_sep_reorg hall fun _ hm => by
        have hfin := nv_zip4_tail hm
        unfold FullScrByteArrs FullCfg.padBytes
        rw [hvb, hmb, hmv2, hmv1]
        simpa only [pB1, sep_assoc] using hfin
    have hU32A : nvBlockU32A.length = 40 ∧
        ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
          (nvBlockU32A.At c.pFlags) := by
      have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide)
      have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
      have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide)
      have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
      have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
        (by decide)
      have h12 := nv_join_pair h1 h2 (by decide) (by decide)
      have h123 := nv_join_pair h12 h3 (by decide) (by decide)
      have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
      exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
        unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
    have hU32B : nvBlockU32B.length = 40 ∧
        ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
          (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
           array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
          (nvBlockU32B.At c.pTmp) := by
      have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
      have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl (by decide)
      have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide)
      have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl
        (by decide)
      have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 4 4 rfl
        (by decide)
      have h12 := nv_join_pair h1 h2 (by decide) (by decide)
      have h123 := nv_join_pair h12 h3 (by decide) (by decide)
      have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
      exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
        unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
    have hU32C : nvBlockU32C.length = 40 ∧
        ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
          array (t := i32) c.pQNext s.scratch.q_next ⋆
          array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
          (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
           array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
          (nvBlockU32C.At c.pQPrev) := by
      have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
        (by decide)
      have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
        (by decide)
      have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
        (by decide)
      have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 8 0 rfl
        (by decide)
      have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
        (by decide)
      have h12 := nv_join_pair h1 h2 (by decide) (by decide)
      have h123 := nv_join_pair h12 h3 (by decide) (by decide)
      have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
      exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
        unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
    have hWvec : nvBlockWvec.length = 80 ∧
        ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
          FullScrWksArrs c s.scratch ⋆
          (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
          (nvBlockWvec.At c.pWvec) := by
      have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
      have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
      have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
      have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
        (by decide)
      have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
        (by decide)
      have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
        (by decide)
      have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 8 rfl
        (by decide)
      have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
      have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
      have h12 := nv_join_pair h1 h2 (by decide) (by decide)
      have h123 := nv_join_pair h12 h3 (by decide) (by decide)
      have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
      have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
      have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
      have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
      have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
      exact nv_sep_reorg (nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
        unfold FullScrWksArrs; exact sep_ac hm
    have hTail : nvBlockTail.length = 340 ∧
        (array (t := i32) c.pMinStk s.core.min_stk ⋆
          (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
           array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
          FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
          (nvBlockTail.At c.pMinStk) := by
      have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
      have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
        (by decide)
      have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
        (by decide)
      have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
      have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
      have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
      have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
      have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
        (by decide)
      have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
        (by decide)
      have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
          region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
        ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
      have h12 := nv_join_pair h1 h2 (by decide) (by decide)
      have h123 := nv_join_pair h12 h3 (by decide) (by decide)
      have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
      have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
      have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
      have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
      have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
      have h123456789 := nv_join_pair h12345678 h9 (by decide) (by decide)
      exact nv_sep_reorg (nv_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm => by
        unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
    have h01 := nv_join_pair hHdr hBytes (by decide) (by decide)
    have h02 := nv_join_pair h01 hU32A (by decide) (by decide)
    have h03 := nv_join_pair h02 hU32B (by decide) (by decide)
    have h04 := nv_join_pair h03 hU32C (by decide) (by decide)
    have h05 := nv_join_pair h04 hWvec (by decide) (by decide)
    exact (nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad
      exact sep_ac hm).2
  have hbytes : bytes m6NvCnfPtr m6NvUnsatBytes (m6NvUnsatBytes.At m6NvCnfPtr) := rfl
  have hjoin : (FullMem c s ⋆ bytes m6NvCnfPtr m6NvUnsatBytes) nvM6ParseMem :=
    nv_sep_append (by rw [nvM6_parseBytes_len]; rfl)
      (by rw [nvM6_parseBytes_len]; decide) hfull hbytes
  rw [sep_emp]; exact sep_ac hjoin

private theorem m6NvUnsat_header :
    parseHeader m6NvUnsatBytes = some (1, 2, m6NvUnsatBytes.drop 9) := by decide

private theorem m6NvUnsat_trace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (m6NvUnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (m6NvUnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], m6NvUnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (m6NvUnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], [10]) := rfl
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) ⟨CNF.empty, rfl⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_parse_body_m6` on concrete DIMACS
`"p cnf 1 2\n1 0\n-1 0\n"`: certifies `r = 20#64` and `cnf.Unsat`. -/
theorem nv_m6_parse_body :
    Func.wp m6WalkParseEnv full_parse_body_m6_body
      (nvOneLitCfg.hdr, m6NvCnfPtr + BitVec.ofNat 64 m6NvUnsatBytes.length, ()) nvM6ParseMem
      (fun (r, ()) m' =>
        r = 20#64 ∧ (∃ cnf, parseDimacs m6NvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        ∃ s', (bytes m6NvCnfPtr m6NvUnsatBytes ⋆ FullMem nvOneLitCfg s') m')
      (fun _ _ _ _ => False) := by
  refine m6WalkParse_parse_body_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvM6ParseState, m6NvCnfPtr, m6NvUnsatBytes, 9, emp,
      rfl, rfl, by decide, by decide, m6NvUnsat_header,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      nvM6_parseState_sparse, nvM6_parseMem_ok, ?_⟩
  intro r s' m' _ _ _ _ _ h20 _ hut hm'
  have hr20 : r = 20#64 := hut m6NvUnsat_trace
  subst hr20
  rw [sep_emp] at hm'
  exact ⟨rfl, h20 rfl, s', hm'⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM6WalkParse
