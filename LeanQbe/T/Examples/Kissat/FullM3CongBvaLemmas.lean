module

public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas6
import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
import LeanQbe.T.Examples.Kissat.FullProof

/-!
# Kissat `D-Full` M3b Congruence & BVA/BVE — `ModuleOk`, Soundness, & Non-Vacuity

Assembles:
1. Standalone `11`-function `m3Module` specification table (`m3SpecTable`, `31` rows with `20`
   `m3Externs`), `m3Env`, and **unconditional** `m3_moduleOk : ModuleOk m3Env m3Module` (`11 / 11`).
2. `201`-row spliced table `m3FullSpecTable` matching `m3Fns` index-for-index (`t_kernel_rfl`),
   `mkM3FullEnv`, `m3FullEnv`, `m3FullUnsatEnv`, and `m3Full_moduleOk_of_m2b` discharging
   `158 / 201` rows unconditionally (all `11` M3b fns, `full_probe_tail`, all `7` `FastBveBudgets`
   fns, all `14` reused `FullFastSched` + `kissat_solve_bytes`, and `125` `Full` fns), parameterized
   strictly by unlanded M2/M2b specs (`FastCore`, `FullKitten`, `FullDefSweep`, `FullBvaHeap`, and
   `4` `TmkZero`-preserving BVE helper adapters).
3. Headline UNSAT-only source soundness `m3_solve_bytes_correct` (`0 | 10 | 20`,
   `r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`) and concrete `Mem 64` UNSAT
   non-vacuity `m3_unsat_nonvacuous` (`XPost := fun _ _ _ _ => False`), plus concise aliases for
   single-line `< 115`-char `#print axioms`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM3CongBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open Kraken.Bedrock2.Test

/-! ## 1. Standalone `11`-Function `m3Module` Table & Unconditional `ModuleOk` -/

section StandaloneModule

/-- `31`-row specification table for standalone `m3Module` (`11` M3b fns ++ `20` `m3Externs`). -/
@[expose] def m3SpecTable : List SpecEntry :=
  [ ⟨"full_cong_mark_trail", [i64, i64, i32], [], m3CongMarkTrailSpec, true⟩
  , ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩
  , ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m3CongAndMatchSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m3CongWorkStepSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩
  , ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
  , ⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩
  , ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩
  , ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  , ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  , ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"full_sweep_dense", [i64, i64, i64], [i64], fullSweepDenseSpec, true⟩
  , ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩ ]

@[expose] def m3Env : Env := Env.ofTable m3SpecTable

theorem m3SpecTable_sigs :
    m3SpecTable.map (fun e => (e.name, e.as, e.rs)) = m3Module.sigs := by
  t_kernel_rfl

theorem m3SpecTable_nodup : (m3SpecTable.map SpecEntry.name).Nodup := by
  have hchk := m3_acyclic
  simp only [m3Module, Module.checkAcyclic, Bool.and_eq_true] at hchk
  have hnd := Module.namesNodup_of_checkNamesNodup hchk.1
  have hnames : m3SpecTable.map SpecEntry.name = m3Module.names := by
    have hm := congrArg (List.map Prod.fst) m3SpecTable_sigs
    simpa only [List.map_map, Function.comp_def, Module.sigs, Module.names, Fn.sig, Extern.sig,
      List.map_append] using hm
  rwa [hnames]

theorem m3SpecTable_noExit : ∀ e ∈ m3SpecTable, e.noExit = true := by
  intro e he
  have hall : m3SpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m3Env_noExit :
    ∀ f as bs xs m Q X X', m3Env f as bs xs m Q X → m3Env f as bs xs m Q X' :=
  Env.ofTable_noExit m3SpecTable_noExit

private theorem m3Env_row (i : Nat) (e : SpecEntry)
    (hi : m3SpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m3Env e.name e.as e.rs xs m Q X :=
  fun xs m Q X h => Env.ofTable_of_mem (List.mem_of_getElem? hi) m3SpecTable_nodup (hno xs m Q X h)

theorem m3_tableImpl : TableImpl m3Env m3Module.fns m3SpecTable := by
  have r0 := m3Env_row 0 ⟨"full_cong_mark_trail", [i64, i64, i32], [], m3CongMarkTrailSpec, true⟩
  have r1 := m3Env_row 1
    ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩
  have r2 := m3Env_row 2
    ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec, true⟩
  have r3 := m3Env_row 3
    ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m3CongAndMatchSpec, true⟩
  have r4 := m3Env_row 4
    ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m3CongWorkStepSpec, true⟩
  have r5 := m3Env_row 5
    ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩
  have r6 := m3Env_row 6
    ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
  have r7 := m3Env_row 7 ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
  have r8 := m3Env_row 8 ⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩
  have r9 := m3Env_row 9 ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
  have r11 := m3Env_row 11 ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  have r12 := m3Env_row 12 ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  have r13 := m3Env_row 13 ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  have r14 := m3Env_row 14 ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  have r15 := m3Env_row 15
    ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩
  have r16 := m3Env_row 16 ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩
  have r17 := m3Env_row 17
    ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
  have r18 := m3Env_row 18 ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  have r19 := m3Env_row 19 ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  have r20 := m3Env_row 20 ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  have r21 := m3Env_row 21 ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  have r22 := m3Env_row 22 ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  have r23 := m3Env_row 23
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  have r24 := m3Env_row 24
    ⟨"full_sweep_dense", [i64, i64, i64], [i64], fullSweepDenseSpec, true⟩
  have r25 := m3Env_row 25 ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
  have r26 := m3Env_row 26
    ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  have r27 := m3Env_row 27
    ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  have r28 := m3Env_row 28 ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  have r29 := m3Env_row 29 ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  have r30 := m3Env_row 30 ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  exact ⟨
    .of (m3_cong_mark_trail_wp m3Env r11),
    .of (m3_cong_unit_fold_wp m3Env r14 r0),
    .of (m3_cong_equiv_fold_wp m3Env r11 r14 r0 r12),
    .of (m3_cong_and_match_wp m3Env r11),
    .of (m3_cong_work_step_wp m3Env r11 r13 r1 r2 r3),
    .of (m3_congruence_dense_wp m3Env r15 r4),
    .of (m3_elim_collect_nbrs_wp m3Env),
    .of (m3_elim_bve_wp m3Env r6 r16),
    .of (m3_probe_wp m3Env r17 r18 r19 r21 r22 r20 r5 r24 r23 r25),
    .of (m3_eliminate_wp m3Env r26 r18 r19 r22 r27 r20 r7 r28 r23),
    .of (m3_preprocess_wp m3Env r29 r30 r19 r8 r9),
    trivial⟩

/-- Unconditional `ModuleOk` certifying all `11 / 11` M3b functions in standalone `m3Module`. -/
theorem m3_moduleOk : ModuleOk m3Env m3Module :=
  Env.ofTable_moduleOk m3_acyclic (m3_allFns_of_forall m3_fns_wf) m3_tableImpl

end StandaloneModule

/-! ## 2. Unified `201`-Row `m3FullSpecTable`, `mkM3FullEnv`, Soundness & Non-Vacuity -/

@[expose] def mkM3FullEnv (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (m3FullSpecTable ext mainSpec)

@[expose] def m3FullEnv : Env := mkM3FullEnv m3DefaultExtSpecs fullSolveBytesSpec
@[expose] def m3FullUnsatEnv : Env := mkM3FullEnv m3DefaultExtSpecs schedUnsatWitnessSpec

theorem m3FullSpecTable_sigs (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecTable ext mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      m3Fns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

theorem m3FullSpecTable_noExit (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ m3FullSpecTable ext mainSpec, e.noExit = true := by
  intro e he
  have hall : (m3FullSpecTable ext mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

private theorem m3Fns_nodup : (m3Fns.map Fn.name).Nodup := by
  have hchk := m3Full_acyclic
  simp only [m3FullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem m3FullSpecTable_nodup (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m3FullSpecTable ext mainSpec).map SpecEntry.name).Nodup := by
  have h : (m3FullSpecTable ext mainSpec).map SpecEntry.name = m3Fns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (m3FullSpecTable_sigs ext mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]
  exact m3Fns_nodup

theorem mkM3FullEnv_noExit (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkM3FullEnv ext mainSpec f as bs xs m Q X →
      mkM3FullEnv ext mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (m3FullSpecTable_noExit ext mainSpec)

theorem m3FullEnv_noExit :
    ∀ f as bs xs m Q X X', m3FullEnv f as bs xs m Q X → m3FullEnv f as bs xs m Q X' :=
  mkM3FullEnv_noExit m3DefaultExtSpecs fullSolveBytesSpec

theorem m3FullUnsatEnv_noExit :
    ∀ f as bs xs m Q X X',
      m3FullUnsatEnv f as bs xs m Q X → m3FullUnsatEnv f as bs xs m Q X' :=
  mkM3FullEnv_noExit m3DefaultExtSpecs schedUnsatWitnessSpec

private theorem mkM3FullEnv_row_at {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m3FullSpecTable ext mainSpec)[i]? = some e)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (m3FullSpecTable_nodup ext mainSpec)
      (hno xs m Q X h)

private theorem mkM3FullEnv_row_lt36 {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry) (hi : i < 36 := by omega)
    (hf : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  mkM3FullEnv_row_at i e
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      ((m3FullSpecPrefix_getElem?_lt36 mainSpec hi).trans hf)) hno

private theorem mkM3FullEnv_row_37_94 {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry) (h1 : 37 ≤ i := by omega) (h2 : i < 94 := by omega)
    (hf : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  mkM3FullEnv_row_at i e
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      ((m3FullSpecPrefix_getElem?_37_94 mainSpec h1 h2).trans hf)) hno

private theorem mkM3FullEnv_row_96_111 {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry) (h1 : 96 ≤ i := by omega) (h2 : i < 111 := by omega)
    (hf : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  mkM3FullEnv_row_at i e
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      ((m3FullSpecPrefix_getElem?_96_111 mainSpec h1 h2).trans hf)) hno

private theorem mkM3FullEnv_row_122_126 {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry) (h1 : 122 ≤ i := by omega) (h2 : i < 126 := by omega)
    (hf : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  mkM3FullEnv_row_at i e
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      ((m3FullSpecPrefix_getElem?_122_126 mainSpec h1 h2).trans hf)) hno

private theorem mkM3FullEnv_row_suf15 {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (k : Nat) (e : SpecEntry) (hk : k < 7 := by omega)
    (hf : (fullSpecTable mainSpec)[128 + k]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  mkM3FullEnv_row_at (128 + (15 + k)) e
    ((m3FullSpecTable_getElem?_suf ext mainSpec).trans
      ((m3FullSpecSuffix_getElem?_15_22 ext mainSpec hk).trans hf)) hno

private theorem mkM3FullEnv_row_suf23 {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (k : Nat) (e : SpecEntry) (hk : k < 6 := by omega) (ht : m3SufCong6[k]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  mkM3FullEnv_row_at (128 + (23 + k)) e
    ((m3FullSpecTable_getElem?_suf ext mainSpec).trans
      ((m3FullSpecSuffix_getElem?_23_29 ext mainSpec hk).trans ht)) hno

private theorem mkM3FullEnv_row_suf46 {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (k : Nat) (e : SpecEntry) (hk : k < 13 := by omega)
    (ht : (m3SufBvaHeap ext)[k]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  mkM3FullEnv_row_at (128 + (46 + k)) e
    ((m3FullSpecTable_getElem?_suf ext mainSpec).trans
      ((m3FullSpecSuffix_getElem?_46_59 ext mainSpec hk).trans ht)) hno

private theorem mkM3FullEnv_row_tail {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (k : Nat) (e : SpecEntry) (hk : k < 13 := by omega) (ht : m3SufTail[k]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3FullEnv ext mainSpec e.name e.as e.rs xs m Q X :=
  mkM3FullEnv_row_at (128 + (59 + k)) e
    ((m3FullSpecTable_getElem?_suf ext mainSpec).trans
      ((m3FullSpecSuffix_getElem?_59_72 ext mainSpec hk).trans ht)) hno

/-- Headline source-level UNSAT soundness of `kissat_solve_bytes` under `mkM3FullEnv ext`
(`0 | 10 | 20`, `r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`). -/
theorem mkM3Full_solve_bytes_correct (ext : M2bInternalSpecs)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM3FullEnv ext fullSolveBytesSpec) Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      X := by
  have r41 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := fullSolveBytesSpec) 41
    ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  have r44 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := fullSolveBytesSpec) 44
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  have r197 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := fullSolveBytesSpec) 10
    ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩
  have r199 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := fullSolveBytesSpec) 12
    ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  have r96 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := fullSolveBytesSpec) 96
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  have r7 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := fullSolveBytesSpec) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  exact sched_kissat_solve_bytes_wp (mkM3FullEnv ext fullSolveBytesSpec) r41 r44 r197 r199 r96 r7
    _ m _ X ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Specialized UNSAT soundness under `m3FullEnv` (`XPost := fun _ _ _ _ => False`). -/
theorem m3_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m3FullEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  mkM3Full_solve_bytes_correct m3DefaultExtSpecs hcfit hwfit hm

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`): executing `kissat_solve_bytes` under
`m3FullUnsatEnv` on `schedNvUnsatBytes` (`p cnf 1 2\n1 0\n-1 0\n`) with `4096`-byte workspace and
`fuel = 16` provably returns `20#64` and establishes `schedNvUnsatCnf.Unsat`. -/
theorem m3_unsat_nonvacuous :
    let m0 : Mem 64 := (schedPayload schedNvUnsatBytes).At schedNvCnfPtr
    Func.wp m3FullUnsatEnv Full.kissat_solve_bytes_body
      (schedNvCnfPtr, BitVec.ofNat 64 schedNvUnsatBytes.length,
        schedNvWorkPtr schedNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ schedNvUnsatCnf.Unsat ∧
        (bytes schedNvCnfPtr schedNvUnsatBytes ⋆
          region (schedNvWorkPtr schedNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  have r41 : ∀ xs m Q X, fullInitStateSpec xs m Q X →
      m3FullUnsatEnv "full_init_state" [i64, i64, i64, i64, i64] [.bool] xs m Q X :=
    mkM3FullEnv_row_37_94 (ext := m3DefaultExtSpecs) (mainSpec := schedUnsatWitnessSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  have r44 : ∀ xs m Q X, fullParseBodySpec xs m Q X →
      m3FullUnsatEnv "full_parse_body" [i64, i64] [i64] xs m Q X :=
    mkM3FullEnv_row_37_94 (ext := m3DefaultExtSpecs) (mainSpec := schedUnsatWitnessSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  have r197 : ∀ xs m Q X, m3PreprocessSpec xs m Q X →
      m3FullUnsatEnv "full_preprocess" [i64] [i64] xs m Q X :=
    mkM3FullEnv_row_tail (ext := m3DefaultExtSpecs) (mainSpec := schedUnsatWitnessSpec) 10
      ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩
  have r199 : ∀ xs m Q X, fullSearchSpec xs m Q X →
      m3FullUnsatEnv "full_search" [i64] [i64] xs m Q X :=
    mkM3FullEnv_row_tail (ext := m3DefaultExtSpecs) (mainSpec := schedUnsatWitnessSpec) 12
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  have r96 : ∀ xs m Q X, fullExtendSpec xs m Q X →
      m3FullUnsatEnv "full_extend" [i64] [] xs m Q X :=
    mkM3FullEnv_row_96_111 (ext := m3DefaultExtSpecs) (mainSpec := schedUnsatWitnessSpec) 96
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  have r7 : ∀ xs m Q X, kissatCheckModelExactSpec xs m Q X →
      m3FullUnsatEnv "kissat_check_model" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
    mkM3FullEnv_row_lt36 (ext := m3DefaultExtSpecs) (mainSpec := schedUnsatWitnessSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  exact sched_kissat_solve_bytes_core_wp m3FullUnsatEnv r41 r44 r197 r199 r96 r7 _ _ _ _
    (fullSolveBytesCoreSpec_of_schedUnsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact schedPayload_sep schedNvUnsatBytes (by decide),
        fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩)

/-! ## 3. `201`-Row `ModuleOk` Assembly Modulo Unlanded M2/M2b Callees (`158 / 201` Closed) -/

/-- Indices in `m3Fns` (`201` fns) of the `43` unlanded M2/M2b dependencies: `FastCore` (`3`),
`FullKitten` (`15`), `FullDefSweep` (`8`), `FullBvaHeap` (`13`), and the `4` `TmkZero`-preserving
BVE helper upgrades (`94, 95, 169, 171`). All remaining `158 / 201` rows are proved. -/
@[expose] def m3UnlandedIndices : List Nat :=
  [47, 48, 49, 94, 95] ++ List.range' 128 15 ++
  [150, 157, 158, 159, 160, 165, 166, 167, 169, 171] ++ List.range' 174 13

theorem m3UnlandedIndices_length : m3UnlandedIndices.length = 43 := by decide

private theorem m3Prefix_flatMap_eq :
    FullFast.fastFnsPrefix.flatMap m3Splice = FullFast.fastFnsPrefix := by
  t_kernel_rfl

private def m3SuffixList : List Fn :=
  Full.fullKitten_fns ++
  (Full.fullFns.drop 128).take 7 ++
  (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
  [m3MarkTrailFn, m3UnitFoldFn, m3EquivFoldFn, m3AndMatchFn, m3CongWorkStepFn,
   m3CongruenceDenseFn] ++
  FullDefSweep.full_def_sweep_fns.drop 5 ++
  (Full.fullFns.drop 145).take 2 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
  (Full.fullFns.drop 148).take 1 ++
  FullDefSweep.full_def_sweep_fns.take 3 ++
  (Full.fullFns.drop 151).take 5 ++
  FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
  FullBvaHeap.bvaHeap_fns ++
  (FullFastSched.sched_fns.drop 3).take 4 ++
  FullFast.fastOrch_fns.take 1 ++
  [m3ProbeFn] ++
  (FullFastSched.sched_fns.drop 9).take 1 ++
  [m3ElimCollectNbrsFn, m3ElimBveFn, m3EliminateFn, m3PreprocessFn] ++
  FullFastSched.sched_fns.drop 13 ++
  Full.fullFns.drop 165

private theorem m3Suffix_flatMap_eq :
    FullFast.fastFnsSuffix.flatMap m3Splice = m3SuffixList := by
  t_kernel_rfl

private theorem m3Fns_eq_blocks : m3Fns = FullFast.fastFnsPrefix ++ m3SuffixList := by
  rw [m3Fns, FullFast.fastFns, List.flatMap_append, m3Prefix_flatMap_eq, m3Suffix_flatMap_eq]

private theorem indexedImpl_slice_unlanded {ext : M2bInternalSpecs}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row)
    {base len : Nat} {fs : List Fn} {tbl : List SpecEntry}
    (hfl : fs.length = len) (htl : tbl.length = len)
    (hf_eq : ∀ i, i < len → m3Fns[base + i]? = fs[i]?)
    (ht_eq : ∀ i, i < len → (m3FullSpecTable ext mainSpec)[base + i]? = tbl[i]?)
    (hmem : ∀ i, i < len → base + i ∈ m3UnlandedIndices) :
    IndexedImpl (mkM3FullEnv ext mainSpec) fs tbl := by
  refine ⟨hfl.trans htl.symm, fun i hi => ?_⟩
  have hi' : i < len := hfl ▸ hi
  obtain ⟨fn, row, hfn, hrow, himpl⟩ := hUnl (base + i) (hmem i hi')
  rw [hf_eq i hi'] at hfn
  rw [ht_eq i hi'] at hrow
  exact ⟨fn, row, hfn, hrow, himpl⟩

private theorem m3_getElem?_skip {α : Type _} {pre rest : List α} {k i : Nat}
    (hp : pre.length = k) : (pre ++ rest)[k + i]? = rest[i]? := by
  subst hp; rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

private theorem m3_getElem?_head {α : Type _} {mid rest : List α} {i : Nat}
    (hi : i < mid.length) : (mid ++ rest)[i]? = mid[i]? :=
  List.getElem?_append_left hi

private theorem m3Fns_suf_at (k i : Nat) :
    m3Fns[(128 + k) + i]? = m3SuffixList[k + i]? := by
  rw [m3Fns_eq_blocks, show (128 + k) + i = 128 + (k + i) by omega,
    List.getElem?_append_right (by rw [m3_fastFnsPrefix_len]; omega),
    m3_fastFnsPrefix_len, show 128 + (k + i) - 128 = k + i by omega]

private theorem m3_unlanded_47 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec) FastCore.fastCore_fns
      (((fullSpecTable mainSpec).drop 47).take 3) := by
  refine indexedImpl_slice_unlanded hUnl (base := 47) (len := 3)
    m3_fastCore_len (by simp [fullSpecTable_len])
    (fun i hi => by
      rw [m3Fns_eq_blocks, List.getElem?_append_left (by rw [m3_fastFnsPrefix_len]; omega),
        m3_fastFnsPrefix_eq_chunks]
      simp only [List.append_assoc]
      rw [show 47 + i = 8 + (14 + (14 + (1 + (10 + i)))) by omega,
        m3_getElem?_skip m3_dimacs_len, m3_getElem?_skip (by simp [m3_full1_len]),
        m3_getElem?_skip (by simp [m3_full1_len]),
        m3_getElem?_skip (by simp [m3_fastBveBudgets_len]),
        m3_getElem?_skip (by simp [m3_full1_len]),
        m3_getElem?_head (by rw [m3_fastCore_len]; exact hi)])
    (fun i hi => by
      rw [m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega),
        m3FullSpecPrefix_getElem?_37_94 mainSpec (by omega) (by omega),
        List.getElem?_take, List.getElem?_drop]
      simp only [hi, ↓reduceIte])
    (fun i hi => by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide)

private theorem m3_unlanded_94 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec) ((Full.full2_fns.drop 35).take 2)
      [ ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
      , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClTmkSpec, true⟩ ] := by
  refine indexedImpl_slice_unlanded hUnl (base := 94) (len := 2)
    (by simp [m3_full2_len]) (by decide)
    (fun i hi => by
      rw [m3Fns_eq_blocks, List.getElem?_append_left (by rw [m3_fastFnsPrefix_len]; omega),
        m3_fastFnsPrefix_eq_chunks]
      simp only [List.append_assoc]
      rw [show 94 + i =
          8 + (14 + (14 + (1 + (10 + (3 + (7 + (1 + (1 + (17 + (18 + i)))))))))) by omega,
        m3_getElem?_skip m3_dimacs_len, m3_getElem?_skip (by simp [m3_full1_len]),
        m3_getElem?_skip (by simp [m3_full1_len]),
        m3_getElem?_skip (by simp [m3_fastBveBudgets_len]),
        m3_getElem?_skip (by simp [m3_full1_len]), m3_getElem?_skip m3_fastCore_len,
        m3_getElem?_skip (by simp [m3_full1_len]), m3_getElem?_skip (by simp [m3_sched_len]),
        m3_getElem?_skip (by simp [m3_full1_len]), m3_getElem?_skip (by simp [m3_full2_len]),
        m3_getElem?_skip (by simp [m3_full2_len]),
        m3_getElem?_head (by simp [m3_full2_len]; exact hi)])
    (fun i hi => by
      rw [m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega),
        m3FullSpecPrefix_getElem?_94_96 mainSpec hi])
    (fun i hi => by rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide)

private theorem m3_specPrefix_eq_chunks (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    m3FullSpecPrefix mainSpec =
      (fullSpecTable mainSpec).take 8 ++
      ((fullSpecTable mainSpec).drop 8).take 14 ++
      ((fullSpecTable mainSpec).drop 22).take 14 ++
      [⟨"full_init_hdr", [i64, i64, i64, i64], [], fullFastInitHdrSpec, true⟩] ++
      ((fullSpecTable mainSpec).drop 37).take 10 ++
      ((fullSpecTable mainSpec).drop 47).take 3 ++
      ((fullSpecTable mainSpec).drop 50).take 7 ++
      ((fullSpecTable mainSpec).drop 57).take 1 ++
      ((fullSpecTable mainSpec).drop 58).take 1 ++
      ((fullSpecTable mainSpec).drop 59).take 17 ++
      ((fullSpecTable mainSpec).drop 76).take 18 ++
      [ ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
      , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
          fullExtendPushClTmkSpec, true⟩ ] ++
      ((fullSpecTable mainSpec).drop 96).take 1 ++
      ((fullSpecTable mainSpec).drop 97).take 14 ++
      ([⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩] ++
       ((fullSpecTable mainSpec).drop 112).take 1 ++
       [⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩] ++
       ((fullSpecTable mainSpec).drop 114).take 5 ++
       [⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩] ++
       ((fullSpecTable mainSpec).drop 120).take 1 ++
       [⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccFastSpec, true⟩] ++
       ((fullSpecTable mainSpec).drop 122).take 3 ++
       (((fullSpecTable mainSpec).drop 125).take 1 ++
         [⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩]) ++
       ((fullSpecTable mainSpec).drop 127).take 1) := by
  have h0' : (fullSpecTable mainSpec).take 36 =
      (fullSpecTable mainSpec).take 8 ++ ((fullSpecTable mainSpec).drop 8).take 14 ++
      ((fullSpecTable mainSpec).drop 22).take 14 := by
    rw [show (36 : Nat) = 8 + 28 from rfl, m3_list_take_add,
      show (28 : Nat) = 14 + 14 from rfl, m3_list_drop_take_add]
    simp only [List.append_assoc]
  have h1' : ((fullSpecTable mainSpec).drop 37).take 57 =
      ((fullSpecTable mainSpec).drop 37).take 10 ++ ((fullSpecTable mainSpec).drop 47).take 3 ++
      ((fullSpecTable mainSpec).drop 50).take 7 ++ ((fullSpecTable mainSpec).drop 57).take 1 ++
      ((fullSpecTable mainSpec).drop 58).take 1 ++ ((fullSpecTable mainSpec).drop 59).take 17 ++
      ((fullSpecTable mainSpec).drop 76).take 18 := by
    rw [show (57 : Nat) = 10 + 47 from rfl, m3_list_drop_take_add,
      show (47 : Nat) = 3 + 44 from rfl, m3_list_drop_take_add,
      show (44 : Nat) = 7 + 37 from rfl, m3_list_drop_take_add,
      show (37 : Nat) = 1 + 36 from rfl, m3_list_drop_take_add,
      show (36 : Nat) = 1 + 35 from rfl, m3_list_drop_take_add,
      show (35 : Nat) = 17 + 18 from rfl, m3_list_drop_take_add]
    simp only [List.append_assoc]
  have h2' : ((fullSpecTable mainSpec).drop 96).take 15 =
      ((fullSpecTable mainSpec).drop 96).take 1 ++
      ((fullSpecTable mainSpec).drop 97).take 14 := by
    rw [show (15 : Nat) = 1 + 14 from rfl, m3_list_drop_take_add]
  have h3' : ((fullSpecTable mainSpec).drop 122).take 4 =
      ((fullSpecTable mainSpec).drop 122).take 3 ++
      ((fullSpecTable mainSpec).drop 125).take 1 := by
    rw [show (4 : Nat) = 3 + 1 from rfl, m3_list_drop_take_add]
  simp only [m3FullSpecPrefix, h0', h1', h2', h3', List.append_assoc]

private theorem m3Full_indexed_prefix_part1 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec)
      (dimacs_fns ++ Full.full1_fns.take 14 ++ (Full.full1_fns.drop 14).take 14 ++
        FullFastBveBudgets.fastBveBudgets_fns.take 1 ++ (Full.full1_fns.drop 29).take 10 ++
        FastCore.fastCore_fns ++ (Full.full1_fns.drop 42).take 7 ++
        FullFastSched.sched_fns.take 1 ++ Full.full1_fns.drop 50)
      ((fullSpecTable mainSpec).take 8 ++ ((fullSpecTable mainSpec).drop 8).take 14 ++
        ((fullSpecTable mainSpec).drop 22).take 14 ++
        [⟨"full_init_hdr", [i64, i64, i64, i64], [], fullFastInitHdrSpec, true⟩] ++
        ((fullSpecTable mainSpec).drop 37).take 10 ++
        ((fullSpecTable mainSpec).drop 47).take 3 ++
        ((fullSpecTable mainSpec).drop 50).take 7 ++
        ((fullSpecTable mainSpec).drop 57).take 1 ++
        ((fullSpecTable mainSpec).drop 58).take 1) := by
  have h0 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 0
    ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  have h1 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 1
    ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  have h2 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 2
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  have h3 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 3
    ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  have h4 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 4
    ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  have h5 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  have h6 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 6
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  have h12 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  have h13 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 13
    ⟨"full_wsort_sift", [i64, i64, i64, i64], [], fullWsortSiftSpec, true⟩
  have h14 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  have h15 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  have h16 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 16
    ⟨"full_heap_up", [i64, i32], [], fullHeapUpSpec, true⟩
  have h17 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  have h18 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 18
    ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  have h20 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 20
    ⟨"full_rescale", [i64], [], fullRescaleSpec, true⟩
  have h23 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 23
    ⟨"full_queue_renumber", [i64], [], fullQueueRenumberSpec, true⟩
  have h27 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  have h29 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 29
    ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  have h31 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 31
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  have h32 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 32
    ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩
  have h33 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 33
    ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  have h34 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 34
    ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  have h35 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 35
    ⟨"full_init_ptrs", [i64, i64, i64], [], fullInitPtrsSpec, true⟩
  have h36_f := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 36
    ⟨"full_init_hdr", [i64, i64, i64, i64], [], fullFastInitHdrSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_36 mainSpec))
  have h36 : ∀ xs m Q X, fullInitHdrSpec xs m Q X →
      mkM3FullEnv ext mainSpec "full_init_hdr" [i64, i64, i64, i64] [] xs m Q X :=
    fun xs m Q X h => h36_f xs m Q X (fullFastInitHdrSpec_of_canon h)
  have h37 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 37
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  have h38 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 38
    ⟨"full_calc_ext_cap", [i64], [i64], fullCalcExtCapSpec, true⟩
  have h39 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 39
    ⟨"full_calc_scr_cap", [i64], [i64], fullCalcScrCapSpec, true⟩
  have h40 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 40
    ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩
  have h42 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 42
    ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, true⟩
  have h43 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 43
    ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, true⟩
  have h52 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 52
    ⟨"full_red_less", [i64, i32, i32], [.bool], fullRedLessSpec, true⟩
  have h53 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 53
    ⟨"full_red_sift", [i64, i64, i64, i64], [], fullRedSiftSpec, true⟩
  have s0 := m3_indexedImpl_of_tableImpl (by simp [m3_dimacs_len, m3_fullSpecTable_len])
    (m3Full_impl_0_8_gen (mkM3FullEnv ext mainSpec) mainSpec h0 h1 h2 h3 h4 h5 h6)
  have s8 := m3_indexedImpl_of_tableImpl (by simp [m3_full1_len, m3_fullSpecTable_len])
    (m3Full_impl_8_22_gen (mkM3FullEnv ext mainSpec) mainSpec h13 h14 h16 h17 h20)
  have s22 := m3_indexedImpl_of_tableImpl (by simp [m3_full1_len, m3_fullSpecTable_len])
    (m3Full_impl_22_36_gen (mkM3FullEnv ext mainSpec) mainSpec h12 h15 h18 h20 h23 h27 h29)
  have s36 : IndexedImpl (mkM3FullEnv ext mainSpec)
      (FullFastBveBudgets.fastBveBudgets_fns.take 1)
      [⟨"full_init_hdr", [i64, i64, i64, i64], [], fullFastInitHdrSpec, true⟩] :=
    m3_indexedImpl_of_tableImpl (by simp [m3_fastBveBudgets_len])
      (m3_tableImpl_singleton rfl rfl (by simp [m3_fastBveBudgets_len]) rfl
        (.of (fast_init_hdr_wp (mkM3FullEnv ext mainSpec))))
  have s37 := m3_indexedImpl_of_tableImpl (by simp [m3_full1_len, m3_fullSpecTable_len])
    (m3Full_impl_37_47_gen (mkM3FullEnv ext mainSpec) mainSpec
      h2 h5 h6 h27 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h42 h43)
  have s47 := m3_unlanded_47 ext mainSpec hUnl
  have s50 := m3_indexedImpl_of_tableImpl (by simp [m3_full1_len, m3_fullSpecTable_len])
    (m3Full_impl_50_57_gen (mkM3FullEnv ext mainSpec) mainSpec h52 h53)
  have s57 : IndexedImpl (mkM3FullEnv ext mainSpec) (FullFastSched.sched_fns.take 1)
      (((fullSpecTable mainSpec).drop 57).take 1) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_sched_len, m3_fullSpecTable_len]) ?_
    change TableImpl (mkM3FullEnv ext mainSpec) ((FullFastSched.sched_fns.take 1).drop 0)
      (((fullSpecTable mainSpec).drop (57 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (sched_sweep_bins_wp (mkM3FullEnv ext mainSpec) h14))
      (m3_tableImpl_fullSlice_nil (by simp [m3_sched_len]))
  have s58 : IndexedImpl (mkM3FullEnv ext mainSpec) (Full.full1_fns.drop 50)
      (((fullSpecTable mainSpec).drop 58).take 1) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full1_len, m3_fullSpecTable_len]) ?_
    change TableImpl (mkM3FullEnv ext mainSpec) ((Full.full1_fns.drop 50).drop 0)
      (((fullSpecTable mainSpec).drop (58 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_sweep_copy_bridge_wp (mkM3FullEnv ext mainSpec) h27 h15))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full1_len]))
  simp only [List.append_assoc]
  exact m3_indexedImpl_append s0 (m3_indexedImpl_append s8 (m3_indexedImpl_append s22
    (m3_indexedImpl_append s36 (m3_indexedImpl_append s37 (m3_indexedImpl_append s47
      (m3_indexedImpl_append s50 (m3_indexedImpl_append s57 s58)))))))

private theorem m3Full_indexed_prefix_part2 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec)
      (Full.full2_fns.take 17 ++ (Full.full2_fns.drop 17).take 18 ++
        (Full.full2_fns.drop 35).take 2 ++ Full.full2_fns.drop 37 ++ Full.full3_fns.take 14 ++
        ((FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
         (Full.full3_fns.drop 15).take 1 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
         (Full.full3_fns.drop 17).take 5 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
         (Full.full3_fns.drop 23).take 1 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
         (Full.full3_fns.drop 25).take 3 ++ (FullFastSched.sched_fns.drop 1).take 2 ++
         Full.full3_fns.drop 30))
      (((fullSpecTable mainSpec).drop 59).take 17 ++
        ((fullSpecTable mainSpec).drop 76).take 18 ++
        [ ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
        , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
            fullExtendPushClTmkSpec, true⟩ ] ++
        ((fullSpecTable mainSpec).drop 96).take 1 ++
        ((fullSpecTable mainSpec).drop 97).take 14 ++
        ([⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩] ++
         ((fullSpecTable mainSpec).drop 112).take 1 ++
         [⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩] ++
         ((fullSpecTable mainSpec).drop 114).take 5 ++
         [⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩] ++
         ((fullSpecTable mainSpec).drop 120).take 1 ++
         [⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccFastSpec, true⟩] ++
         ((fullSpecTable mainSpec).drop 122).take 3 ++
         (((fullSpecTable mainSpec).drop 125).take 1 ++
           [⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩]) ++
         ((fullSpecTable mainSpec).drop 127).take 1)) := by
  have h8 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 8
    ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  have h9 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  have h10 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 10
    ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
  have h11 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  have h14 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  have h15 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  have h17 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  have h19 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 19
    ⟨"full_heap_pop", [i64], [i64], fullHeapPopSpec, true⟩
  have h21 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 21
    ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  have h22 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 22
    ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  have h24 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 24
    ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  have h25 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 25
    ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩
  have h26 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 26
    ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  have h27 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  have h28 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  have h30 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  have h31 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 31
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  have h45 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 45
    ⟨"full_find_repl", [i64, i64], [i64], fullFindReplSpec, true⟩
  have h48 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 48
    ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  have h49 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  have h50 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 50
    ⟨"full_recompute_tiers", [i64], [], fullRecomputeTiersSpec, true⟩
  have h51 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 51
    ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  have h54 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 54
    ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  have h55 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 55
    ⟨"full_lit_rank", [i64, i64, i32], [i64], fullLitRankSpec, true⟩
  have h56 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 56
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  have h57 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 57
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  have h58 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 58
    ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩
  have h59 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 59
    ⟨"full_rewatch_arena", [i64, i64], [.bool], fullRewatchArenaSpec, true⟩
  have h60 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 60
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  have h61 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 61
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  have h62 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 62
    ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  have h63 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 63
    ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩
  have h64 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 64
    ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  have h65 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 65
    ⟨"full_bump_analyzed", [i64], [], fullBumpAnalyzedSpec, true⟩
  have h66 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 66
    ⟨"full_otfs_large", [i64, i32, i32], [.bool], fullOtfsLargeSpec, true⟩
  have h67 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 67
    ⟨"full_otfs_bin", [i64, i32, i32], [.bool], fullOtfsBinSpec, true⟩
  have h68 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 68
    ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], fullOtfsSubsumeSpec, true⟩
  have h69 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 69
    ⟨"full_min_mark", [i64, i32, i8], [], fullMinMarkSpec, true⟩
  have h70 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 70
    ⟨"full_min_lit", [i64, i32], [.bool], fullMinLitSpec, true⟩
  have h71 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 71
    ⟨"full_tmp_less", [i64, i64, i32, i32], [.bool], fullTmpLessSpec, true⟩
  have h72 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 72
    ⟨"full_sort_tmp_sift", [i64, i64, i64, i64, i64], [], fullSortTmpSiftSpec, true⟩
  have h73 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 73
    ⟨"full_sort_tmp", [i64], [], fullSortTmpSpec, true⟩
  have h74 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 74
    ⟨"full_shrink_lower", [i64, i32, i32], [.bool], fullShrinkLowerSpec, true⟩
  have h75 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 75
    ⟨"full_shrink_blk", [i64, i64, i64, i32, i64], [], fullShrinkBlkSpec, true⟩
  have h76 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 76
    ⟨"full_min_shrink", [i64], [], fullMinShrinkSpec, true⟩
  have h77 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 77
    ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  have h78 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 78
    ⟨"full_one_lit_confl", [i64], [i64], fullOneLitConflSpec, true⟩
  have h79 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 79
    ⟨"full_deduce_1uip", [i64], [i64], fullDeduce1uipSpec, true⟩
  have h80 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 80
    ⟨"full_eager_subsume", [i64, i64], [], fullEagerSubsumeSpec, true⟩
  have h81 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 81
    ⟨"full_learn_clause", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  have h82 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 82
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  have h83 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 83
    ⟨"full_next_dec_var", [i64], [i64], fullNextDecVarSpec, true⟩
  have h86 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 86
    ⟨"full_walk_collect", [i64], [i64], fullWalkCollectSpec, true⟩
  have h87 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 87
    ⟨"full_walk_cl_sat", [i64, i64, i64], [.bool], fullWalkClSatSpec, true⟩
  have h88 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 88
    ⟨"full_walk_pick_lit", [i64, i64, i64], [i32], fullWalkPickLitSpec, true⟩
  have h89 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 89
    ⟨"full_walk", [i64], [], fullWalkSpec, true⟩
  have h94_t := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 94
    ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_94_96 mainSpec (k := 0) (by omega)))
  have h94 : ∀ xs m Q X, fullExtendPush2Spec xs m Q X →
      mkM3FullEnv ext mainSpec "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X :=
    fun xs m Q X h => h94_t xs m Q X (m3_extPush2Tmk_of_canon h)
  have h97 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 97
    ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  have h98 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 98
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  have h99 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 99
    ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  have h101 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 101
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  have h102 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  have h103 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 103
    ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], fullLuckyScanSpec, true⟩
  have h104 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 104
    ⟨"full_lucky_polar", [i64], [i64], fullLuckyPolarSpec, true⟩
  have h106 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 106
    ⟨"full_hbr_dom", [i64, i32, i32], [i32], fullHbrDomSpec, true⟩
  have h107 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 107
    ⟨"full_probe_prop_lit", [i64, i32], [.bool], fullProbePropLitSpec, true⟩
  have h108 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 108
    ⟨"full_probe_prop", [i64], [i64], fullProbePropSpec, true⟩
  have h109 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 109
    ⟨"full_probe_flush_hbr", [i64, i64], [i64], fullProbeFlushHbrSpec, true⟩
  have h110 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 110
    ⟨"full_probe_assume_pair", [i64, i32], [i64], fullProbeAssumePairSpec, true⟩
  have h112 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 112
    ⟨"full_trans_lit", [i64, i32], [.bool], fullTransLitSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_112 mainSpec))
  have h114 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 114
    ⟨"full_viv_simplify", [i64, i32], [i64], fullVivSimplifySpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_114_119 mainSpec (by omega) (by omega)))
  have h115 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 115
    ⟨"full_viv_sort_lits", [i64, i64, i32], [], fullVivSortLitsSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_114_119 mainSpec (by omega) (by omega)))
  have h116 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 116
    ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_114_119 mainSpec (by omega) (by omega)))
  have h117 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 117
    ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64], fullVivCommitSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_114_119 mainSpec (by omega) (by omega)))
  have h118 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 118
    ⟨"full_viv_clause", [i64, i32], [i64], fullVivClauseSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_114_119 mainSpec (by omega) (by omega)))
  have h120 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 120
    ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool], fullTarjanPopSccSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_120 mainSpec))
  have h121_f := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 121
    ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccFastSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_121 mainSpec))
  have h121 : ∀ xs m Q X, fullTarjanSccSpec xs m Q X →
      mkM3FullEnv ext mainSpec "full_tarjan_scc" [i64] [i64] xs m Q X :=
    fun xs m Q X h => h121_f xs m Q X (fullTarjanSccFastSpec_of_canon h)
  have h122 := mkM3FullEnv_row_122_126 (ext := ext) (mainSpec := mainSpec) 122
    ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  have h123 := mkM3FullEnv_row_122_126 (ext := ext) (mainSpec := mainSpec) 123
    ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  have h124 := mkM3FullEnv_row_122_126 (ext := ext) (mainSpec := mainSpec) 124
    ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  have s59 := m3_indexedImpl_of_tableImpl (by simp [m3_full2_len, m3_fullSpecTable_len])
    (m3Full_impl_59_76_gen (mkM3FullEnv ext mainSpec) mainSpec
      h8 h9 h11 h15 h21 h22 h24 h30 h49 h50 h51 h54 h55 h56 h57 h58 h59 h60 h62 h69 h70 h71 h72
      h74)
  have s76 := m3_indexedImpl_of_tableImpl (by simp [m3_full2_len, m3_fullSpecTable_len])
    (m3Full_impl_76_94_gen (mkM3FullEnv ext mainSpec) mainSpec
      h9 h10 h11 h14 h15 h17 h19 h25 h26 h27 h28 h30 h31 h49 h56 h61 h62 h63 h64 h65 h66 h67 h68
      h69 h70 h73 h75 h76 h77 h78 h79 h80 h81 h83 h86 h87 h88 h89)
  have s94 := m3_unlanded_94 ext mainSpec hUnl
  have s96 : IndexedImpl (mkM3FullEnv ext mainSpec) (Full.full2_fns.drop 37)
      (((fullSpecTable mainSpec).drop 96).take 1) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full2_len, m3_fullSpecTable_len]) ?_
    change TableImpl (mkM3FullEnv ext mainSpec) ((Full.full2_fns.drop 37).drop 0)
      (((fullSpecTable mainSpec).drop (96 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_extend_bridge_wp (mkM3FullEnv ext mainSpec)))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full2_len]))
  have s97 := m3_indexedImpl_of_tableImpl (by simp [m3_full3_len, m3_fullSpecTable_len])
    (m3Full_impl_97_111_gen (mkM3FullEnv ext mainSpec) mainSpec
      h11 h15 h27 h28 h30 h45 h49 h82 h97 h98 h99 h102 h103 h104 h106 h107 h108 h109)
  have s111 := m3_indexedImpl_of_tableImpl
    (by simp [m3_fastBveBudgets_len, m3_full3_len, m3_sched_len, m3_fullSpecTable_len])
    (m3Full_impl_111_128_gen (mkM3FullEnv ext mainSpec) mainSpec h11 h14 h15 h28 h30 h48 h49
      h56 h57 h60 h94 h98 h99 h101 h102 h110 h112 h114 h115 h116 h117 h118 h120 h121 h122
      h123 h124)
  simp only [List.append_assoc]
  exact m3_indexedImpl_append s59 (m3_indexedImpl_append s76 (m3_indexedImpl_append s94
    (m3_indexedImpl_append s96 (m3_indexedImpl_append s97 s111))))

private theorem m3Full_indexed_prefix (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec) FullFast.fastFnsPrefix (m3FullSpecPrefix mainSpec) := by
  refine m3_indexedImpl_of_eq ?_ ?_ (m3_indexedImpl_append
    (m3Full_indexed_prefix_part1 ext mainSpec hUnl)
    (m3Full_indexed_prefix_part2 ext mainSpec hUnl))
  · rw [m3_fastFnsPrefix_eq_chunks]; simp only [List.append_assoc]
  · rw [m3_specPrefix_eq_chunks]; simp only [List.append_assoc]

private theorem m3_suffixList_eq_chunks : m3SuffixList =
    Full.fullKitten_fns ++ Full.full4_fns.take 7 ++
    (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
    [m3MarkTrailFn, m3UnitFoldFn, m3EquivFoldFn, m3AndMatchFn, m3CongWorkStepFn,
     m3CongruenceDenseFn] ++
    FullDefSweep.full_def_sweep_fns.drop 5 ++ (Full.full4_fns.drop 17).take 2 ++
    (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
    (Full.full4_fns.drop 20).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
    (Full.full4_fns.drop 23).take 1 ++ (Full.full4_fns.drop 24).take 1 ++
    (Full.full4_fns.drop 25).take 1 ++ (Full.full4_fns.drop 26).take 1 ++
    (Full.full4_fns.drop 27).take 1 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
    FullBvaHeap.bvaHeap_fns ++ (FullFastSched.sched_fns.drop 3).take 4 ++
    FullFast.fastOrch_fns.take 1 ++ [m3ProbeFn] ++ (FullFastSched.sched_fns.drop 9).take 1 ++
    [m3ElimCollectNbrsFn, m3ElimBveFn, m3EliminateFn, m3PreprocessFn] ++
    FullFastSched.sched_fns.drop 13 ++ Full.full4_fns.drop 37 := by
  have h23 : (Full.fullFns.drop 151).take 5 =
      (Full.full4_fns.drop 23).take 1 ++ (Full.full4_fns.drop 24).take 1 ++
      (Full.full4_fns.drop 25).take 1 ++ (Full.full4_fns.drop 26).take 1 ++
      (Full.full4_fns.drop 27).take 1 := by
    rw [m3_fullFns_drop_slice4 (i := 23) (k := 5),
      show (5 : Nat) = 1 + 4 from rfl, m3_list_drop_take_add,
      show (4 : Nat) = 1 + 3 from rfl, m3_list_drop_take_add,
      show (3 : Nat) = 1 + 2 from rfl, m3_list_drop_take_add,
      show (2 : Nat) = 1 + 1 from rfl, m3_list_drop_take_add]
    simp only [List.append_assoc]
  simp only [m3SuffixList, m3_fullFns_drop_slice4 (i := 0) (k := 7), List.drop_zero,
    m3_fullFns_drop_slice4 (i := 17) (k := 2), m3_fullFns_drop_slice4 (i := 20) (k := 1), h23,
    show Full.fullFns.drop 165 = Full.full4_fns.drop 37 by
      rw [show (165 : Nat) = 128 + 37 from rfl, m3_list_drop_add 128 37, m3_fullFns_drop128],
    List.append_assoc]

private theorem m3_specSuffix_eq_chunks (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    m3FullSpecSuffix ext mainSpec =
      fullKittenSpecTable ++ ((fullSpecTable mainSpec).drop 128).take 7 ++
      [ ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩ ] ++
      m3SufCong6 ++ m3SufSweep4 ext ++ ((fullSpecTable mainSpec).drop 145).take 2 ++
      [ ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ ] ++
      ((fullSpecTable mainSpec).drop 148).take 1 ++ m3SufDef3 ext ++
      ((fullSpecTable mainSpec).drop 151).take 1 ++
      [ ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩ ] ++
      ((fullSpecTable mainSpec).drop 153).take 1 ++
      [ ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩ ] ++
      ((fullSpecTable mainSpec).drop 155).take 1 ++
      [ ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩ ] ++
      m3SufBvaHeap ext ++
      ([ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
       , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
       , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
       , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩ ] ++
       [ ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩ ] ++
       [ ⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩ ] ++
       [ ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ ] ++
       [ ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
       , ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
       , ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
       , ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩ ] ++
       [ ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
       , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ]) ++
      ((fullSpecTable mainSpec).drop 165).take 1 := by
  have htail : ((fullSpecTable mainSpec).drop 165).take 1 =
      (fullSpecTable mainSpec).drop 165 :=
    List.take_of_length_le (by simp [fullSpecTable_len])
  have htail_s : m3SufTail =
      [ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
      , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
      , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
      , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩ ] ++
      [ ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩ ] ++
      [ ⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩ ] ++
      [ ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ ] ++
      [ ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
      , ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
      , ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
      , ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩ ] ++
      [ ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
      , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ] := rfl
  rw [m3FullSpecSuffix, htail_s, htail]

private theorem m3_cong6_len :
    ([m3MarkTrailFn, m3UnitFoldFn, m3EquivFoldFn, m3AndMatchFn, m3CongWorkStepFn,
      m3CongruenceDenseFn] : List Fn).length = 6 := rfl

private theorem m3Full_impl_suffix_part1_gen (Γ : Env) (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h11 : ∀ xs m Q X, fullArenaNextSpec xs m Q X → Γ "full_arena_next" [i64, i32] [i32] xs m Q X)
    (h56 : ∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] xs m Q X)
    (h94 : ∀ xs m Q X, fullExtendPush2TmkSpec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (h95 : ∀ xs m Q X, fullExtendPushClTmkSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X)
    (h98 : ∀ xs m Q X, fullAddBinSpec xs m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X)
    (h100 : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (h101 : ∀ xs m Q X, fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (h102 : ∀ xs m Q X, fullAddUnitSpec xs m Q X → Γ "full_add_unit" [i64, i32] [.bool] xs m Q X)
    (h143 : ∀ xs m Q X, fullCongFindSpec xs m Q X → Γ "full_cong_find" [i64, i32] [i32] xs m Q X)
    (h144 : ∀ xs m Q X, fullCongMergeSpec xs m Q X →
      Γ "full_cong_merge" [i64, i32, i32] [.bool] xs m Q X)
    (h145 : ∀ xs m Q X, fullHasTernarySpec xs m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] xs m Q X)
    (h146 : ∀ xs m Q X, fullSortU32Spec xs m Q X → Γ "full_sort_u32" [i64, i32] [] xs m Q X)
    (h147 : ∀ xs m Q X, fullCongExtractIteSpec xs m Q X →
      Γ "full_cong_extract_ite" [i64, i32, i32, i32, i64] [i64] xs m Q X)
    (h148 : ∀ xs m Q X, fullCongEmitXorSpec xs m Q X →
      Γ "full_cong_emit_xor" [i64, i64, i32, i32, i32] [i64] xs m Q X)
    (h150 : ∀ xs m Q X, fullCongExtractTickSpec xs m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] xs m Q X)
    (h151 : ∀ xs m Q X, m3CongMarkTrailSpec xs m Q X →
      Γ "full_cong_mark_trail" [i64, i64, i32] [] xs m Q X)
    (h152 : ∀ xs m Q X, m3CongUnitFoldSpec xs m Q X →
      Γ "full_cong_unit_fold" [i64, i32, i32] [i64] xs m Q X)
    (h153 : ∀ xs m Q X, m3CongEquivFoldSpec xs m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] xs m Q X)
    (h154 : ∀ xs m Q X, m3CongAndMatchSpec xs m Q X →
      Γ "full_cong_and_match" [i64, i32, i32] [.bool] xs m Q X)
    (h155 : ∀ xs m Q X, m3CongWorkStepSpec xs m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] xs m Q X)
    (h161 : ∀ xs m Q X, fullFwdDedupBinsSpec xs m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] xs m Q X)
    (h162 : ∀ xs m Q X, fullFwdCheckClSpec xs m Q X →
      Γ "full_fwd_check_cl" [i64, i32] [.bool] xs m Q X)
    (h164 : ∀ xs m Q X, fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (h167 : ∀ xs m Q X, fullBveGatesDefFastSpec xs m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] xs m Q X)
    (h168 : ∀ xs m Q X, fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (h169 : ∀ xs m Q X, fullBveWeakenTmkSpec xs m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] xs m Q X)
    (h170 : ∀ xs m Q X, fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (h171 : ∀ xs m Q X, fullBveCommitResTmkSpec xs m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] xs m Q X)
    (h172 : ∀ xs m Q X, fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hk128 : IndexedImpl Γ Full.fullKitten_fns fullKittenSpecTable)
    (hs150 : IndexedImpl Γ ((FullDefSweep.full_def_sweep_fns.drop 3).take 1)
      [⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩])
    (hs157 : IndexedImpl Γ (FullDefSweep.full_def_sweep_fns.drop 5) (m3SufSweep4 ext))
    (hs165 : IndexedImpl Γ (FullDefSweep.full_def_sweep_fns.take 3) (m3SufDef3 ext))
    (hs169 : IndexedImpl Γ ((Full.full4_fns.drop 24).take 1)
      [⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩])
    (hs171 : IndexedImpl Γ ((Full.full4_fns.drop 26).take 1)
      [⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩]) :
    IndexedImpl Γ
      (Full.fullKitten_fns ++ Full.full4_fns.take 7 ++
       (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
       [m3MarkTrailFn, m3UnitFoldFn, m3EquivFoldFn, m3AndMatchFn, m3CongWorkStepFn,
        m3CongruenceDenseFn] ++
       FullDefSweep.full_def_sweep_fns.drop 5 ++ (Full.full4_fns.drop 17).take 2 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
       (Full.full4_fns.drop 20).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
       (Full.full4_fns.drop 23).take 1 ++ (Full.full4_fns.drop 24).take 1 ++
       (Full.full4_fns.drop 25).take 1 ++ (Full.full4_fns.drop 26).take 1 ++
       (Full.full4_fns.drop 27).take 1 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6)
      (fullKittenSpecTable ++ ((fullSpecTable mainSpec).drop 128).take 7 ++
       [ ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩ ] ++
       m3SufCong6 ++ m3SufSweep4 ext ++ ((fullSpecTable mainSpec).drop 145).take 2 ++
       [ ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ ] ++
       ((fullSpecTable mainSpec).drop 148).take 1 ++ m3SufDef3 ext ++
       ((fullSpecTable mainSpec).drop 151).take 1 ++
       [ ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩ ] ++
       ((fullSpecTable mainSpec).drop 153).take 1 ++
       [ ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩ ] ++
       ((fullSpecTable mainSpec).drop 155).take 1 ++
       [ ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩ ]) := by
  have s143 : IndexedImpl Γ (Full.full4_fns.take 7)
      (((fullSpecTable mainSpec).drop 128).take 7) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full4_len, m3_fullSpecTable_len]) ?_
    change TableImpl Γ ((Full.full4_fns.take 7).drop 0)
      (((fullSpecTable mainSpec).drop (128 + 0)).take (7 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_cong_find_bridge_wp Γ)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_cong_merge_bridge_wp Γ h143 h98)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_has_ternary_bridge_wp Γ)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_sort_u32_bridge_wp Γ)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_cong_extract_ite_bridge_wp Γ h145)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_cong_emit_xor_bridge_wp Γ)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_cong_try_xor_ite_bridge_wp Γ h145 h148 h147)) ?_
    exact m3_tableImpl_fullSlice_nil (by simp [m3_full4_len])
  have s151 : IndexedImpl Γ [m3MarkTrailFn, m3UnitFoldFn, m3EquivFoldFn, m3AndMatchFn,
      m3CongWorkStepFn, m3CongruenceDenseFn] m3SufCong6 := by
    refine m3_indexedImpl_of_tableImpl rfl ?_
    change TableImpl Γ
      ([m3MarkTrailFn, m3UnitFoldFn, m3EquivFoldFn, m3AndMatchFn, m3CongWorkStepFn,
        m3CongruenceDenseFn].drop 0)
      (m3SufCong6.drop 0)
    refine m3_tableImpl_drop_step rfl rfl (.of (m3_cong_mark_trail_wp Γ h143)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (m3_cong_unit_fold_wp Γ h102 h151)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (m3_cong_equiv_fold_wp Γ h143 h102 h151 h144)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (m3_cong_and_match_wp Γ h143)) ?_
    refine m3_tableImpl_drop_step rfl rfl
      (.of (m3_cong_work_step_wp Γ h143 h146 h152 h153 h154)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (m3_congruence_dense_wp Γ h150 h155)) ?_
    exact m3_tableImpl_drop_nil rfl rfl
  have s161 : IndexedImpl Γ ((Full.full4_fns.drop 17).take 2)
      (((fullSpecTable mainSpec).drop 145).take 2) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full4_len, m3_fullSpecTable_len]) ?_
    change TableImpl Γ (((Full.full4_fns.drop 17).take 2).drop 0)
      (((fullSpecTable mainSpec).drop (145 + 0)).take (2 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_fwd_dedup_bins_bridge_wp Γ h102)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_fwd_check_cl_bridge_wp Γ h56 h102 h98)) ?_
    exact m3_tableImpl_fullSlice_nil (by simp [m3_full4_len])
  have s163 : IndexedImpl Γ ((FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1)
      [⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩] :=
    m3_indexedImpl_of_tableImpl (by simp [m3_fastBveBudgets_len])
      (m3_tableImpl_singleton rfl rfl (by simp [m3_fastBveBudgets_len]) rfl
        (.of (fast_forward_sub_wp Γ h161 h11 h162)))
  have s164 : IndexedImpl Γ ((Full.full4_fns.drop 20).take 1)
      (((fullSpecTable mainSpec).drop 148).take 1) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full4_len, m3_fullSpecTable_len]) ?_
    change TableImpl Γ (((Full.full4_fns.drop 20).take 1).drop 0)
      (((fullSpecTable mainSpec).drop (148 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_bve_collect_bridge_wp Γ))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full4_len]))
  have s168 : IndexedImpl Γ ((Full.full4_fns.drop 23).take 1)
      (((fullSpecTable mainSpec).drop 151).take 1) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full4_len, m3_fullSpecTable_len]) ?_
    change TableImpl Γ (((Full.full4_fns.drop 23).take 1).drop 0)
      (((fullSpecTable mainSpec).drop (151 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_bve_resolve_pair_bridge_wp Γ))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full4_len]))
  have s170 : IndexedImpl Γ ((Full.full4_fns.drop 25).take 1)
      (((fullSpecTable mainSpec).drop 153).take 1) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full4_len, m3_fullSpecTable_len]) ?_
    change TableImpl Γ (((Full.full4_fns.drop 25).take 1).drop 0)
      (((fullSpecTable mainSpec).drop (153 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_bve_try_bce_bridge_wp Γ))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full4_len]))
  have s172 : IndexedImpl Γ ((Full.full4_fns.drop 27).take 1)
      (((fullSpecTable mainSpec).drop 155).take 1) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full4_len, m3_fullSpecTable_len]) ?_
    change TableImpl Γ (((Full.full4_fns.drop 27).take 1).drop 0)
      (((fullSpecTable mainSpec).drop (155 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_bve_ext_need_bridge_wp Γ))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full4_len]))
  have s173 : IndexedImpl Γ (FullFastBveBudgets.fastBveBudgets_fns.drop 6)
      [⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩] :=
    m3_indexedImpl_of_tableImpl (by simp [m3_fastBveBudgets_len])
      (m3_tableImpl_singleton rfl rfl (by simp [m3_fastBveBudgets_len]) rfl
        (.of (fast_bve_var_def_wp Γ h164 h172 h169 h101 h167 h168 h171 h170 h94 h100 h95)))
  simp only [List.append_assoc]
  exact m3_indexedImpl_append hk128 (m3_indexedImpl_append s143 (m3_indexedImpl_append hs150
    (m3_indexedImpl_append s151 (m3_indexedImpl_append hs157 (m3_indexedImpl_append s161
      (m3_indexedImpl_append s163 (m3_indexedImpl_append s164 (m3_indexedImpl_append hs165
        (m3_indexedImpl_append s168 (m3_indexedImpl_append hs169 (m3_indexedImpl_append s170
          (m3_indexedImpl_append hs171 (m3_indexedImpl_append s172 s173)))))))))))))

private theorem m3Full_impl_suffix_part2_gen (Γ : Env) (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (h7 : ∀ xs m Q X, kissatCheckModelExactSpec xs m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] xs m Q X)
    (h9 : ∀ xs m Q X, fullIlog10Spec xs m Q X → Γ "full_ilog10" [i64] [i64] xs m Q X)
    (h30 : ∀ xs m Q X, fullBacktrackSpec xs m Q X → Γ "full_backtrack" [i64, i64] [] xs m Q X)
    (h41 : ∀ xs m Q X, fullInitStateSpec xs m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] xs m Q X)
    (h44 : ∀ xs m Q X, fullParseBodySpec xs m Q X → Γ "full_parse_body" [i64, i64] [i64] xs m Q X)
    (h49 : ∀ xs m Q X, fullPropagateSpec xs m Q X → Γ "full_propagate" [i64] [i64] xs m Q X)
    (h60 : ∀ xs m Q X, fullArenaSweepSpec xs m Q X → Γ "full_arena_sweep" [i64] [i64] xs m Q X)
    (h61 : ∀ xs m Q X, fullReduceSpec xs m Q X → Γ "full_reduce" [i64, .bool] [i64] xs m Q X)
    (h82 : ∀ xs m Q X, fullAnalyzeSpec xs m Q X → Γ "full_analyze" [i64] [i64] xs m Q X)
    (h84 : ∀ xs m Q X, fullDecideSpec xs m Q X → Γ "full_decide" [i64] [i64] xs m Q X)
    (h85 : ∀ xs m Q X, fullWarmupSpec xs m Q X → Γ "full_warmup" [i64] [] xs m Q X)
    (h90 : ∀ xs m Q X, fullRephaseSpec xs m Q X → Γ "full_rephase" [i64] [] xs m Q X)
    (h91 : ∀ xs m Q X, fullSwitchModeSpec xs m Q X → Γ "full_switch_mode" [i64] [] xs m Q X)
    (h92 : ∀ xs m Q X, fullRestartDueSpec xs m Q X → Γ "full_restart_due" [i64] [i64] xs m Q X)
    (h93 : ∀ xs m Q X, fullRestartSpec xs m Q X → Γ "full_restart" [i64] [] xs m Q X)
    (h96 : ∀ xs m Q X, fullExtendSpec xs m Q X → Γ "full_extend" [i64] [] xs m Q X)
    (h105 : ∀ xs m Q X, fullLuckySpec xs m Q X → Γ "full_lucky" [i64] [i64] xs m Q X)
    (h111 : ∀ xs m Q X, fullProbeRunFastSpec xs m Q X →
      Γ "full_probe_run" [i64, i64] [i64] xs m Q X)
    (h113 : ∀ xs m Q X, fullTransitiveFastSpec xs m Q X →
      Γ "full_transitive" [i64, i64] [i64] xs m Q X)
    (h119 : ∀ xs m Q X, fullVivifyFastSpec xs m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] xs m Q X)
    (h125 : ∀ xs m Q X, fullSubstituteSpec xs m Q X → Γ "full_substitute" [i64] [i64] xs m Q X)
    (h126 : ∀ xs m Q X, schedEnterDenseSpec xs m Q X →
      Γ "full_enter_dense" [i64] [.bool] xs m Q X)
    (h127 : ∀ xs m Q X, fullRebuildWatchesSpec xs m Q X →
      Γ "full_rebuild_watches" [i64] [i64] xs m Q X)
    (h156 : ∀ xs m Q X, m3CongruenceDenseSpec xs m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] xs m Q X)
    (h160 : ∀ xs m Q X, fullSweepDenseSpec xs m Q X →
      Γ "full_sweep_dense" [i64, i64, i64] [i64] xs m Q X)
    (h163 : ∀ xs m Q X, fullForwardSubFastSpec xs m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] xs m Q X)
    (h173 : ∀ xs m Q X, fullBveVarDefSpec xs m Q X → Γ "full_bve_var" [i64, i32] [i64] xs m Q X)
    (h186 : ∀ xs m Q X, fullFactorHeapSpec xs m Q X → Γ "full_factor" [i64, i64] [i64] xs m Q X)
    (h187 : ∀ xs m Q X, schedScaleDeltaSpec xs m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] xs m Q X)
    (h188 : ∀ xs m Q X, schedMinU64Spec xs m Q X → Γ "full_min_u64" [i64, i64] [i64] xs m Q X)
    (h189 : ∀ xs m Q X, schedMaxU64Spec xs m Q X → Γ "full_max_u64" [i64, i64] [i64] xs m Q X)
    (h190 : ∀ xs m Q X, schedProbeDticksSpec xs m Q X →
      Γ "full_probe_dticks" [i64, .bool] [i64] xs m Q X)
    (h191 : ∀ xs m Q X, schedProbeTailSpec xs m Q X → Γ "full_probe_tail" [i64, i64] [i64] xs m Q X)
    (h192 : ∀ xs m Q X, m3ProbeSpec xs m Q X → Γ "full_probe" [i64, .bool] [i64] xs m Q X)
    (h193 : ∀ xs m Q X, schedElimDticksSpec xs m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] xs m Q X)
    (h194 : ∀ xs m Q X, m3ElimCollectNbrsSpec xs m Q X →
      Γ "full_elim_collect_nbrs" [i64, i32] [i64] xs m Q X)
    (h195 : ∀ xs m Q X, m3ElimBveSpec xs m Q X → Γ "full_elim_bve" [i64, i64] [i64] xs m Q X)
    (h196 : ∀ xs m Q X, m3EliminateSpec xs m Q X → Γ "full_eliminate" [i64, .bool] [i64] xs m Q X)
    (h197 : ∀ xs m Q X, m3PreprocessSpec xs m Q X → Γ "full_preprocess" [i64] [i64] xs m Q X)
    (h198 : ∀ xs m Q X, schedSimplifySpec xs m Q X →
      Γ "full_simplify" [i64, .bool, .bool] [i64] xs m Q X)
    (h199 : ∀ xs m Q X, fullSearchSpec xs m Q X → Γ "full_search" [i64] [i64] xs m Q X)
    (hs174 : IndexedImpl Γ FullBvaHeap.bvaHeap_fns (m3SufBvaHeap ext)) :
    IndexedImpl Γ
      (FullBvaHeap.bvaHeap_fns ++ (FullFastSched.sched_fns.drop 3).take 4 ++
       FullFast.fastOrch_fns.take 1 ++ [m3ProbeFn] ++ (FullFastSched.sched_fns.drop 9).take 1 ++
       [m3ElimCollectNbrsFn, m3ElimBveFn, m3EliminateFn, m3PreprocessFn] ++
       FullFastSched.sched_fns.drop 13 ++ Full.full4_fns.drop 37)
      (m3SufBvaHeap ext ++
       ([ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
        , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
        , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
        , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩ ] ++
        [ ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩ ] ++
        [ ⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩ ] ++
        [ ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ ] ++
        [ ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
        , ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
        , ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
        , ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩ ] ++
        [ ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
        , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ]) ++
       ((fullSpecTable mainSpec).drop 165).take 1) := by
  have s187 : IndexedImpl Γ ((FullFastSched.sched_fns.drop 3).take 4)
      [ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
      , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
      , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
      , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩ ] := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_sched_len]) ?_
    change TableImpl Γ (((FullFastSched.sched_fns.drop 3).take 4).drop 0)
      (([ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
        , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
        , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
        , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩ ]).drop 0)
    refine m3_tableImpl_drop_step rfl rfl (.of (sched_scale_delta_wp Γ h9)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (sched_min_u64_wp Γ)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (sched_max_u64_wp Γ)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (sched_probe_dticks_wp Γ h189)) ?_
    exact m3_tableImpl_drop_nil rfl rfl
  have s191 : IndexedImpl Γ (FullFast.fastOrch_fns.take 1)
      [⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩] :=
    m3_indexedImpl_of_tableImpl (by simp [m3_fastOrch_len])
      (m3_tableImpl_singleton rfl rfl (by simp [m3_fastOrch_len]) rfl
        (.of (m3_fast_probe_tail_wp Γ h113 h188 h111 h119)))
  have s192 : IndexedImpl Γ [m3ProbeFn]
      [⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩] :=
    m3_indexedImpl_of_tableImpl rfl
      (m3_tableImpl_singleton rfl rfl rfl rfl
        (.of (m3_probe_wp Γ h190 h9 h187 h125 h126 h188 h156 h160 h127 h191)))
  have s193 : IndexedImpl Γ ((FullFastSched.sched_fns.drop 9).take 1)
      [⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩] :=
    m3_indexedImpl_of_tableImpl (by simp [m3_sched_len])
      (m3_tableImpl_singleton rfl rfl (by simp [m3_sched_len]) rfl
        (.of (sched_elim_dticks_wp Γ)))
  have s194 : IndexedImpl Γ [m3ElimCollectNbrsFn, m3ElimBveFn, m3EliminateFn, m3PreprocessFn]
      [ ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
      , ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
      , ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
      , ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩ ] := by
    refine m3_indexedImpl_of_tableImpl rfl ?_
    change TableImpl Γ
      ([m3ElimCollectNbrsFn, m3ElimBveFn, m3EliminateFn, m3PreprocessFn].drop 0)
      (([ ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
        , ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
        , ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
        , ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩ ]).drop 0)
    refine m3_tableImpl_drop_step rfl rfl (.of (m3_elim_collect_nbrs_wp Γ)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (m3_elim_bve_wp Γ h194 h173)) ?_
    refine m3_tableImpl_drop_step rfl rfl
      (.of (m3_eliminate_wp Γ h193 h9 h187 h126 h163 h188 h195 h186 h127)) ?_
    refine m3_tableImpl_drop_step rfl rfl (.of (m3_preprocess_wp Γ h49 h60 h187 h192 h196)) ?_
    exact m3_tableImpl_drop_nil rfl rfl
  have s198 : IndexedImpl Γ (FullFastSched.sched_fns.drop 13)
      [ ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
      , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ] := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_sched_len]) ?_
    change TableImpl Γ ((FullFastSched.sched_fns.drop 13).drop 0)
      (([ ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
        , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ]).drop 0)
    refine m3_tableImpl_drop_step rfl rfl (.of (sched_simplify_wp Γ h30 h61 h192 h196)) ?_
    refine m3_tableImpl_drop_step rfl rfl
      (.of (sched_search_wp Γ h105 h85 h49 h82 h91 h90 h61 h198 h92 h93 h84)) ?_
    exact m3_tableImpl_drop_nil (by simp [m3_sched_len]) rfl
  have s200 : IndexedImpl Γ (Full.full4_fns.drop 37)
      (((fullSpecTable mainSpec).drop 165).take 1) := by
    refine m3_indexedImpl_of_tableImpl (by simp [m3_full4_len, m3_fullSpecTable_len]) ?_
    change TableImpl Γ ((Full.full4_fns.drop 37).drop 0)
      (((fullSpecTable mainSpec).drop (165 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (fun a m Q X h =>
        sched_kissat_solve_bytes_core_wp Γ h41 h44 h197 h199 h96 h7 a m Q X
          (hweaken a m Q X h)))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full4_len]))
  simp only [List.append_assoc]
  exact m3_indexedImpl_append hs174 (m3_indexedImpl_append s187 (m3_indexedImpl_append s191
    (m3_indexedImpl_append s192 (m3_indexedImpl_append s193 (m3_indexedImpl_append s194
      (m3_indexedImpl_append s198 s200))))))

private theorem m3_unlanded_128 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec) Full.fullKitten_fns fullKittenSpecTable := by
  refine indexedImpl_slice_unlanded hUnl (base := 128) (len := 15)
    m3_kitten_len kittenSpecTable_len
    (fun i hi => by
      rw [show 128 + i = (128 + 0) + i by omega, m3Fns_suf_at, m3_suffixList_eq_chunks]
      simp only [List.append_assoc, Nat.zero_add]
      exact m3_getElem?_head (by rw [m3_kitten_len]; exact hi))
    (fun i hi => (m3FullSpecTable_getElem?_suf ext mainSpec).trans
      (m3FullSpecSuffix_getElem?_lt15 ext mainSpec hi))
    (fun i hi => by simp [m3UnlandedIndices]; omega)

private theorem m3_unlanded_150 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec)
      ((FullDefSweep.full_def_sweep_fns.drop 3).take 1)
      [⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩] := by
  refine indexedImpl_slice_unlanded hUnl (base := 150) (len := 1)
    (by simp [m3_defSweep_len]) (by decide)
    (fun i hi => by
      rw [show 150 + i = (128 + 22) + i by omega, m3Fns_suf_at, m3_suffixList_eq_chunks]
      simp only [List.append_assoc]
      rw [show 22 + i = 15 + (7 + i) by omega, m3_getElem?_skip m3_kitten_len,
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_head (by simp [m3_defSweep_len]; omega)])
    (fun i hi => by
      rcases (by omega : i = 0) with rfl
      rw [show (150 : Nat) + 0 = 128 + 22 from rfl]
      exact (m3FullSpecTable_getElem?_suf ext mainSpec).trans
        (m3FullSpecSuffix_getElem?_22 ext mainSpec))
    (fun i hi => by rcases (by omega : i = 0) with rfl; decide)

private theorem m3_unlanded_157 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec)
      (FullDefSweep.full_def_sweep_fns.drop 5) (m3SufSweep4 ext) := by
  refine indexedImpl_slice_unlanded hUnl (base := 157) (len := 4)
    (by simp [m3_defSweep_len]) (m3SufSweep4_len ext)
    (fun i hi => by
      rw [show 157 + i = (128 + 29) + i by omega, m3Fns_suf_at, m3_suffixList_eq_chunks]
      simp only [List.append_assoc]
      rw [show 29 + i = 15 + (7 + (1 + (6 + i))) by omega,
        m3_getElem?_skip m3_kitten_len, m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_defSweep_len]), m3_getElem?_skip m3_cong6_len,
        m3_getElem?_head (by simp [m3_defSweep_len]; omega)])
    (fun i hi => by
      rw [show 157 + i = 128 + (29 + i) by omega, m3FullSpecTable_getElem?_suf ext mainSpec]
      exact m3FullSpecSuffix_getElem?_29_33 ext mainSpec hi)
    (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> decide)

private theorem m3_unlanded_165 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec)
      (FullDefSweep.full_def_sweep_fns.take 3) (m3SufDef3 ext) := by
  refine indexedImpl_slice_unlanded hUnl (base := 165) (len := 3)
    (by simp [m3_defSweep_len]) (m3SufDef3_len ext)
    (fun i hi => by
      rw [show 165 + i = (128 + 37) + i by omega, m3Fns_suf_at, m3_suffixList_eq_chunks]
      simp only [List.append_assoc]
      rw [show 37 + i = 15 + (7 + (1 + (6 + (4 + (2 + (1 + (1 + i))))))) by omega,
        m3_getElem?_skip m3_kitten_len, m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_defSweep_len]), m3_getElem?_skip m3_cong6_len,
        m3_getElem?_skip (by simp [m3_defSweep_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_fastBveBudgets_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_head (by simp [m3_defSweep_len]; omega)])
    (fun i hi => by
      rw [show 165 + i = 128 + (37 + i) by omega, m3FullSpecTable_getElem?_suf ext mainSpec]
      exact m3FullSpecSuffix_getElem?_37_40 ext mainSpec hi)
    (fun i hi => by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide)

private theorem m3_unlanded_169 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec) ((Full.full4_fns.drop 24).take 1)
      [⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩] := by
  refine indexedImpl_slice_unlanded hUnl (base := 169) (len := 1)
    (by simp [m3_full4_len]) (by decide)
    (fun i hi => by
      rw [show 169 + i = (128 + 41) + i by omega, m3Fns_suf_at, m3_suffixList_eq_chunks]
      simp only [List.append_assoc]
      rw [show 41 + i = 15 + (7 + (1 + (6 + (4 + (2 + (1 + (1 + (3 + (1 + i))))))))) by omega,
        m3_getElem?_skip m3_kitten_len, m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_defSweep_len]), m3_getElem?_skip m3_cong6_len,
        m3_getElem?_skip (by simp [m3_defSweep_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_fastBveBudgets_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_defSweep_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_head (by simp [m3_full4_len]; omega)])
    (fun i hi => by
      rcases (by omega : i = 0) with rfl
      rw [show (169 : Nat) + 0 = 128 + 41 from rfl]
      exact (m3FullSpecTable_getElem?_suf ext mainSpec).trans
        (m3FullSpecSuffix_getElem?_41 ext mainSpec))
    (fun i hi => by rcases (by omega : i = 0) with rfl; decide)

private theorem m3_unlanded_171 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec) ((Full.full4_fns.drop 26).take 1)
      [⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩] := by
  refine indexedImpl_slice_unlanded hUnl (base := 171) (len := 1)
    (by simp [m3_full4_len]) (by decide)
    (fun i hi => by
      rw [show 171 + i = (128 + 43) + i by omega, m3Fns_suf_at, m3_suffixList_eq_chunks]
      simp only [List.append_assoc]
      rw [show 43 + i =
          15 + (7 + (1 + (6 + (4 + (2 + (1 + (1 + (3 + (1 + (1 + (1 + i))))))))))) by omega,
        m3_getElem?_skip m3_kitten_len, m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_defSweep_len]), m3_getElem?_skip m3_cong6_len,
        m3_getElem?_skip (by simp [m3_defSweep_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_fastBveBudgets_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_defSweep_len]),
        m3_getElem?_skip (by simp [m3_full4_len]), m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_head (by simp [m3_full4_len]; omega)])
    (fun i hi => by
      rcases (by omega : i = 0) with rfl
      rw [show (171 : Nat) + 0 = 128 + 43 from rfl]
      exact (m3FullSpecTable_getElem?_suf ext mainSpec).trans
        (m3FullSpecSuffix_getElem?_43 ext mainSpec))
    (fun i hi => by rcases (by omega : i = 0) with rfl; decide)

private theorem m3_unlanded_174 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec) FullBvaHeap.bvaHeap_fns (m3SufBvaHeap ext) := by
  refine indexedImpl_slice_unlanded hUnl (base := 174) (len := 13)
    m3_bvaHeap_len (m3SufBvaHeap_len ext)
    (fun i hi => by
      rw [show 174 + i = (128 + 46) + i by omega, m3Fns_suf_at, m3_suffixList_eq_chunks]
      simp only [List.append_assoc]
      rw [show 46 + i =
          15 + (7 + (1 + (6 + (4 + (2 + (1 + (1 + (3 + (1 + (1 + (1 + (1 + (1 +
            (1 + i)))))))))))))) by omega,
        m3_getElem?_skip m3_kitten_len, m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_defSweep_len]), m3_getElem?_skip m3_cong6_len,
        m3_getElem?_skip (by simp [m3_defSweep_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_fastBveBudgets_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_defSweep_len]),
        m3_getElem?_skip (by simp [m3_full4_len]), m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_full4_len]), m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_full4_len]),
        m3_getElem?_skip (by simp [m3_fastBveBudgets_len]),
        m3_getElem?_head (by rw [m3_bvaHeap_len]; exact hi)])
    (fun i hi => by
      rw [show 174 + i = 128 + (46 + i) by omega, m3FullSpecTable_getElem?_suf ext mainSpec]
      exact m3FullSpecSuffix_getElem?_46_59 ext mainSpec hi)
    (fun i hi => by simp [m3UnlandedIndices]; omega)

private theorem m3Full_indexed_suffix_part1 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec)
      (Full.fullKitten_fns ++ Full.full4_fns.take 7 ++
       (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
       [m3MarkTrailFn, m3UnitFoldFn, m3EquivFoldFn, m3AndMatchFn, m3CongWorkStepFn,
        m3CongruenceDenseFn] ++
       FullDefSweep.full_def_sweep_fns.drop 5 ++ (Full.full4_fns.drop 17).take 2 ++
       (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
       (Full.full4_fns.drop 20).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
       (Full.full4_fns.drop 23).take 1 ++ (Full.full4_fns.drop 24).take 1 ++
       (Full.full4_fns.drop 25).take 1 ++ (Full.full4_fns.drop 26).take 1 ++
       (Full.full4_fns.drop 27).take 1 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6)
      (fullKittenSpecTable ++ ((fullSpecTable mainSpec).drop 128).take 7 ++
       [ ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩ ] ++
       m3SufCong6 ++ m3SufSweep4 ext ++ ((fullSpecTable mainSpec).drop 145).take 2 ++
       [ ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ ] ++
       ((fullSpecTable mainSpec).drop 148).take 1 ++ m3SufDef3 ext ++
       ((fullSpecTable mainSpec).drop 151).take 1 ++
       [ ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩ ] ++
       ((fullSpecTable mainSpec).drop 153).take 1 ++
       [ ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩ ] ++
       ((fullSpecTable mainSpec).drop 155).take 1 ++
       [ ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩ ]) := by
  have h11 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  have h56 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 56
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  have h94 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 94
    ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_94_96 mainSpec (k := 0) (by omega)))
  have h95 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 95
    ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClTmkSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_94_96 mainSpec (k := 1) (by omega)))
  have h98 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 98
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  have h100 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 100
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  have h101 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 101
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  have h102 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  have h143 := mkM3FullEnv_row_suf15 (ext := ext) (mainSpec := mainSpec) 0
    ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  have h144 := mkM3FullEnv_row_suf15 (ext := ext) (mainSpec := mainSpec) 1
    ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  have h145 := mkM3FullEnv_row_suf15 (ext := ext) (mainSpec := mainSpec) 2
    ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  have h146 := mkM3FullEnv_row_suf15 (ext := ext) (mainSpec := mainSpec) 3
    ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  have h147 := mkM3FullEnv_row_suf15 (ext := ext) (mainSpec := mainSpec) 4
    ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], fullCongExtractIteSpec, true⟩
  have h148 := mkM3FullEnv_row_suf15 (ext := ext) (mainSpec := mainSpec) 5
    ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], fullCongEmitXorSpec, true⟩
  have h150 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 150
    ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 150 22).trans
      (m3FullSpecSuffix_getElem?_22 ext mainSpec))
  have h151 := mkM3FullEnv_row_suf23 (ext := ext) (mainSpec := mainSpec) 0
    ⟨"full_cong_mark_trail", [i64, i64, i32], [], m3CongMarkTrailSpec, true⟩
  have h152 := mkM3FullEnv_row_suf23 (ext := ext) (mainSpec := mainSpec) 1
    ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩
  have h153 := mkM3FullEnv_row_suf23 (ext := ext) (mainSpec := mainSpec) 2
    ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec, true⟩
  have h154 := mkM3FullEnv_row_suf23 (ext := ext) (mainSpec := mainSpec) 3
    ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m3CongAndMatchSpec, true⟩
  have h155 := mkM3FullEnv_row_suf23 (ext := ext) (mainSpec := mainSpec) 4
    ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m3CongWorkStepSpec, true⟩
  have h161 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 161
    ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 161 (33 + 0)).trans
      (m3FullSpecSuffix_getElem?_33_35 ext mainSpec (k := 0) (by omega)))
  have h162 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 162
    ⟨"full_fwd_check_cl", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 162 (33 + 1)).trans
      (m3FullSpecSuffix_getElem?_33_35 ext mainSpec (k := 1) (by omega)))
  have h164 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 164
    ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 164 36).trans
      (m3FullSpecSuffix_getElem?_36 ext mainSpec))
  have h167 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 167
    ⟨"full_bve_gates", [i64, i32, i32, i32], [], fullBveGatesDefFastSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 167 (37 + 2)).trans
      (m3FullSpecSuffix_getElem?_37_40 ext mainSpec (k := 2) (by omega)))
  have h168 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 168
    ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 168 40).trans
      (m3FullSpecSuffix_getElem?_40 ext mainSpec))
  have h169 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 169
    ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 169 41).trans
      (m3FullSpecSuffix_getElem?_41 ext mainSpec))
  have h170 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 170
    ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 170 42).trans
      (m3FullSpecSuffix_getElem?_42 ext mainSpec))
  have h171 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 171
    ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 171 43).trans
      (m3FullSpecSuffix_getElem?_43 ext mainSpec))
  have h172 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 172
    ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 172 44).trans
      (m3FullSpecSuffix_getElem?_44 ext mainSpec))
  exact m3Full_impl_suffix_part1_gen (mkM3FullEnv ext mainSpec) ext mainSpec
    h11 h56 h94 h95 h98 h100 h101 h102 h143 h144 h145 h146 h147 h148 h150 h151 h152 h153
    h154 h155 h161 h162 h164 h167 h168 h169 h170 h171 h172
    (m3_unlanded_128 ext mainSpec hUnl) (m3_unlanded_150 ext mainSpec hUnl)
    (m3_unlanded_157 ext mainSpec hUnl) (m3_unlanded_165 ext mainSpec hUnl)
    (m3_unlanded_169 ext mainSpec hUnl) (m3_unlanded_171 ext mainSpec hUnl)

private theorem m3Full_indexed_suffix_part2 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec)
      (FullBvaHeap.bvaHeap_fns ++ (FullFastSched.sched_fns.drop 3).take 4 ++
       FullFast.fastOrch_fns.take 1 ++ [m3ProbeFn] ++ (FullFastSched.sched_fns.drop 9).take 1 ++
       [m3ElimCollectNbrsFn, m3ElimBveFn, m3EliminateFn, m3PreprocessFn] ++
       FullFastSched.sched_fns.drop 13 ++ Full.full4_fns.drop 37)
      (m3SufBvaHeap ext ++
       ([ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
        , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
        , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
        , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩ ] ++
        [ ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩ ] ++
        [ ⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩ ] ++
        [ ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ ] ++
        [ ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
        , ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
        , ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
        , ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩ ] ++
        [ ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
        , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ]) ++
       ((fullSpecTable mainSpec).drop 165).take 1) := by
  have h7 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  have h9 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  have h30 := mkM3FullEnv_row_lt36 (ext := ext) (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  have h41 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 41
    ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  have h44 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 44
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  have h49 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  have h60 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 60
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  have h61 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 61
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  have h82 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 82
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  have h84 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 84
    ⟨"full_decide", [i64], [i64], fullDecideSpec, true⟩
  have h85 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 85
    ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩
  have h90 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 90
    ⟨"full_rephase", [i64], [], fullRephaseSpec, true⟩
  have h91 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 91
    ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
  have h92 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 92
    ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  have h93 := mkM3FullEnv_row_37_94 (ext := ext) (mainSpec := mainSpec) 93
    ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  have h96 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 96
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  have h105 := mkM3FullEnv_row_96_111 (ext := ext) (mainSpec := mainSpec) 105
    ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  have h111 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 111
    ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_111 mainSpec))
  have h113 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 113
    ⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_113 mainSpec))
  have h119 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 119
    ⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_119 mainSpec))
  have h125 := mkM3FullEnv_row_122_126 (ext := ext) (mainSpec := mainSpec) 125
    ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  have h126 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 126
    ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_126 mainSpec))
  have h127 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 127
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
    ((m3FullSpecTable_getElem?_lt128 ext mainSpec (by omega)).trans
      (m3FullSpecPrefix_getElem?_127 mainSpec))
  have h156 := mkM3FullEnv_row_suf23 (ext := ext) (mainSpec := mainSpec) 5
    ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩
  have h160 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 160
    ⟨"full_sweep_dense", [i64, i64, i64], [i64], fullSweepDenseSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 160 (29 + 3)).trans
      (m3FullSpecSuffix_getElem?_29_33 ext mainSpec (k := 3) (by omega)))
  have h163 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 163
    ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 163 35).trans
      (m3FullSpecSuffix_getElem?_35 ext mainSpec))
  have h173 := mkM3FullEnv_row_at (ext := ext) (mainSpec := mainSpec) 173
    ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩
    ((m3FullSpecTable_getElem?_suf_at ext mainSpec 173 45).trans
      (m3FullSpecSuffix_getElem?_45 ext mainSpec))
  have h186 := mkM3FullEnv_row_suf46 (ext := ext) (mainSpec := mainSpec) 12
    ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  have h187 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 0
    ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  have h188 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 1
    ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  have h189 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 2
    ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
  have h190 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 3
    ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
  have h191 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 4
    ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
  have h192 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 5
    ⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩
  have h193 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 6
    ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  have h194 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 7
    ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
  have h195 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 8
    ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
  have h196 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 9
    ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
  have h197 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 10
    ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩
  have h198 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 11
    ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
  have h199 := mkM3FullEnv_row_tail (ext := ext) (mainSpec := mainSpec) 12
    ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  exact m3Full_impl_suffix_part2_gen (mkM3FullEnv ext mainSpec) ext mainSpec hweaken
    h7 h9 h30 h41 h44 h49 h60 h61 h82 h84 h85 h90 h91 h92 h93 h96 h105 h111 h113 h119 h125 h126
    h127 h156 h160 h163 h173 h186 h187 h188 h189 h190 h191 h192 h193 h194 h195 h196 h197 h198 h199
    (m3_unlanded_174 ext mainSpec hUnl)

private theorem m3Full_indexed_suffix (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    IndexedImpl (mkM3FullEnv ext mainSpec) m3SuffixList (m3FullSpecSuffix ext mainSpec) := by
  refine m3_indexedImpl_of_eq ?_ ?_ (m3_indexedImpl_append
    (m3Full_indexed_suffix_part1 ext mainSpec hUnl)
    (m3Full_indexed_suffix_part2 ext mainSpec hweaken hUnl))
  · rw [m3_suffixList_eq_chunks]; simp only [List.append_assoc]
  · rw [m3_specSuffix_eq_chunks]; simp only [List.append_assoc]

/-- Row-by-row `TableImpl` for all `201` functions in `m3Fns` (`158 / 201` proved
unconditionally; parameterized strictly by `hUnl` over `m3UnlandedIndices`). -/
theorem m3Full_tableImpl_of_m2b (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    TableImpl (mkM3FullEnv ext mainSpec) m3Fns (m3FullSpecTable ext mainSpec) := by
  have hIdx : IndexedImpl (mkM3FullEnv ext mainSpec) m3Fns (m3FullSpecTable ext mainSpec) := by
    rw [m3Fns_eq_blocks, m3FullSpecTable]
    exact m3_indexedImpl_append (m3Full_indexed_prefix ext mainSpec hUnl)
      (m3Full_indexed_suffix ext mainSpec hweaken hUnl)
  exact m3_tableImpl_of_getElem? hIdx.1 hIdx.2

/-- Complete `201`-function `ModuleOk` for `m3FullModule` under `mkM3FullEnv ext mainSpec`,
discharging `158 / 201` rows unconditionally and parameterized strictly by `hUnl`. -/
theorem m3Full_moduleOk_of_m2b (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (hUnl : ∀ k ∈ m3UnlandedIndices,
      ∃ fn row, m3Fns[k]? = some fn ∧ (m3FullSpecTable ext mainSpec)[k]? = some row ∧
        SpecEntry.Impl (mkM3FullEnv ext mainSpec) fn row) :
    ModuleOk (mkM3FullEnv ext mainSpec) m3FullModule :=
  Env.ofTable_moduleOk m3Full_acyclic (m3_allFns_of_forall m3Fns_wf)
    (m3Full_tableImpl_of_m2b ext mainSpec hweaken hUnl)

/-! ## 4. Short Aliases for `< 115`-Char Single-Line `#print axioms` -/

abbrev m3FullAcyc := @m3Full_acyclic
abbrev m3ModOk := @m3_moduleOk
abbrev m3FullOk := @m3Full_moduleOk_of_m2b
abbrev m3SolveOk := @m3_solve_bytes_correct
abbrev m3UnsatNv := @m3_unsat_nonvacuous
abbrev m3MarkTrailWp := @m3_cong_mark_trail_wp
abbrev m3UnitFoldWp := @m3_cong_unit_fold_wp
abbrev m3EquivFoldWp := @m3_cong_equiv_fold_wp
abbrev m3AndMatchWp := @m3_cong_and_match_wp
abbrev m3WorkStepWp := @m3_cong_work_step_wp
abbrev m3CongDenseWp := @m3_congruence_dense_wp
abbrev m3ElimNbrsWp := @m3_elim_collect_nbrs_wp
abbrev m3ElimBveWp := @m3_elim_bve_wp
abbrev m3ProbeTailWp := @m3_fast_probe_tail_wp
abbrev m3ProbeWp := @m3_probe_wp
abbrev m3ElimWp := @m3_eliminate_wp
abbrev m3PreWp := @m3_preprocess_wp

end LeanQbe.T.Examples.Kissat.FullM3CongBva
