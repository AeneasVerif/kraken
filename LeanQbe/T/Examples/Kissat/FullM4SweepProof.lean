module

public import LeanQbe.T.Examples.Kissat.FullM4SweepLemmas2
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas

/-!
# Kissat M4b — `512`-Var `kitten` + Partition-Class Sweeping Packaging & Non-Vacuity

1. `fullM4SweepEnv_row`, `SpecEntry.Impl` witnesses for all `24/24` owned functions of
   `fullM4SweepModule`, and unconditional `fullM4SweepEnv_moduleOk : ModuleOk fullM4SweepEnv
   fullM4SweepModule`.
2. Headline UNSAT soundness theorems (`full_m4_sweep_sat_unsat_sound` preserving `FullSparseInv`
   and `full_m4_sweep_dense_unsat_sound` preserving `FullDenseInv`, `0` SAT proofs).
3. Concrete `100060`-byte `Mem 64` UNSAT instances (`nvM4SweepCfg` with `scratch_cap = 24576`,
   dense-mode `nvM4SweepMem`, sparse-mode `nvM4SweepSparseMem`, and embedded inconsistent
   `K512State` slab) giving unconditional `XPost := fun _ _ _ _ => False` non-vacuity witnesses
   for `full_k512_init`, `full_k512_solve` (`r = 20#64`), `full_m4_sweep_cone`,
   `full_m4_sweep_var`, `full_m4_sweep_dense`, and `full_m4_sweep_sat`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `fullM4SweepEnv` Row Lookup, `24/24` `SpecEntry.Impl`, & `ModuleOk` -/

theorem fullM4SweepEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ fullM4SweepSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    M4EnvSpec fullM4SweepEnv nm sp :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem fullM4SweepSpecTable_nodup
      (hno xs m Q X hs)

private theorem fullM4Sweep_allFns_wf : AllFns Fn.Wf fullM4SweepModule.fns :=
  ⟨full_k512_init_wf, full_k512_watch_wf, full_k512_assign_wf, full_k512_add_clause_wf,
   full_k512_mtf_wf, full_k512_backtrack_wf, full_k512_propagate_wf, full_k512_ana_clause_wf,
   full_k512_analyze_wf, full_k512_solve_wf, full_k512_flip_wf, full_k512_add_live_wf,
   full_m4_sweep_cone_wf, full_m4_sweep_refine_sig_wf, full_m4_sweep_rand_phases_wf,
   full_m4_sweep_flip_round_wf, full_m4_sweep_sim_wf, full_m4_sweep_rearm_wf,
   full_m4_sweep_build_pht_wf, full_m4_sweep_units_wf, full_m4_sweep_classes_wf,
   full_m4_sweep_var_wf, full_m4_sweep_dense_wf, full_m4_sweep_sat_wf, trivial⟩

private theorem m4_row_k5_watch : M4EnvSpec fullM4SweepEnv "full_k512_watch" k5WatchSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_assign : M4EnvSpec fullM4SweepEnv "full_k512_assign" k5AssignSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_mtf : M4EnvSpec fullM4SweepEnv "full_k512_mtf" k5MtfSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_bt : M4EnvSpec fullM4SweepEnv "full_k512_backtrack" k5BacktrackSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_prop : M4EnvSpec fullM4SweepEnv "full_k512_propagate" k5PropagateSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_anacl :
    M4EnvSpec fullM4SweepEnv "full_k512_ana_clause" k5AnaClauseSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_ana : M4EnvSpec fullM4SweepEnv "full_k512_analyze" k5AnalyzeSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_init : M4EnvSpec fullM4SweepEnv "full_k512_init" k5InitSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_addcl :
    M4EnvSpec fullM4SweepEnv "full_k512_add_clause" k5AddClauseSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_solve : M4EnvSpec fullM4SweepEnv "full_k512_solve" k5SolveSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_flip : M4EnvSpec fullM4SweepEnv "full_k512_flip" k5FlipSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_k5_live : M4EnvSpec fullM4SweepEnv "full_k512_add_live" k5AddLiveSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_cone : M4EnvSpec fullM4SweepEnv "full_m4_sweep_cone" m4SweepConeSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_ref :
    M4EnvSpec fullM4SweepEnv "full_m4_sweep_refine_sig" m4SweepRefineSigSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_rand :
    M4EnvSpec fullM4SweepEnv "full_m4_sweep_rand_phases" m4SweepRandPhasesSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_flipr :
    M4EnvSpec fullM4SweepEnv "full_m4_sweep_flip_round" m4SweepFlipRoundSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_sim : M4EnvSpec fullM4SweepEnv "full_m4_sweep_sim" m4SweepSimSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_rearm : M4EnvSpec fullM4SweepEnv "full_m4_sweep_rearm" m4SweepRearmSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_pht :
    M4EnvSpec fullM4SweepEnv "full_m4_sweep_build_pht" m4SweepBuildPhtSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_units : M4EnvSpec fullM4SweepEnv "full_m4_sweep_units" m4SweepUnitsSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_classes :
    M4EnvSpec fullM4SweepEnv "full_m4_sweep_classes" m4SweepClassesSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_var : M4EnvSpec fullM4SweepEnv "full_m4_sweep_var" m4SweepVarSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_dense : M4EnvSpec fullM4SweepEnv "full_m4_sweep_dense" m4SweepDenseSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_rng : M4EnvSpec fullM4SweepEnv "full_rng_next" Full.fullRngNextSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_fbt : M4EnvSpec fullM4SweepEnv "full_backtrack" Full.fullBacktrackSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_fprop : M4EnvSpec fullM4SweepEnv "full_propagate" Full.fullPropagateSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_addu : M4EnvSpec fullM4SweepEnv "full_add_unit" Full.fullAddUnitSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_addb : M4EnvSpec fullM4SweepEnv "full_add_bin" Full.fullAddBinSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_enter : M4EnvSpec fullM4SweepEnv "full_enter_dense" Full.fullEnterDenseSpec
  :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

private theorem m4_row_reb :
    M4EnvSpec fullM4SweepEnv "full_rebuild_watches" Full.fullRebuildWatchesSpec :=
  fullM4SweepEnv_row (by simp [fullM4SweepSpecTable]) (fun _ _ _ _ h => h)

theorem m4Sweep_k512_init_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_init", [i64, i32], [], full_k512_init_body⟩
      ⟨"full_k512_init", [i64, i32], [], k5InitSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_init_wp fullM4SweepEnv)

theorem m4Sweep_k512_watch_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_watch", [i64, i32, i32, i32], [], full_k512_watch_body⟩
      ⟨"full_k512_watch", [i64, i32, i32, i32], [], k5WatchSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_watch_wp fullM4SweepEnv)

theorem m4Sweep_k512_assign_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_assign", [i64, i32, i32], [], full_k512_assign_body⟩
      ⟨"full_k512_assign", [i64, i32, i32], [], k5AssignSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_assign_wp fullM4SweepEnv)

theorem m4Sweep_k512_add_clause_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_add_clause", [i64, i64, i32], [.bool], full_k512_add_clause_body⟩
      ⟨"full_k512_add_clause", [i64, i64, i32], [.bool], k5AddClauseSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_add_clause_wp fullM4SweepEnv m4_row_k5_assign m4_row_k5_watch)

theorem m4Sweep_k512_mtf_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_mtf", [i64, i32], [], full_k512_mtf_body⟩
      ⟨"full_k512_mtf", [i64, i32], [], k5MtfSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_mtf_wp fullM4SweepEnv)

theorem m4Sweep_k512_backtrack_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_backtrack", [i64, i32], [], full_k512_backtrack_body⟩
      ⟨"full_k512_backtrack", [i64, i32], [], k5BacktrackSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_backtrack_wp fullM4SweepEnv)

theorem m4Sweep_k512_propagate_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_propagate", [i64], [i32], full_k512_propagate_body⟩
      ⟨"full_k512_propagate", [i64], [i32], k5PropagateSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_propagate_wp fullM4SweepEnv m4_row_k5_assign)

theorem m4Sweep_k512_ana_clause_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_ana_clause", [i64, i32, i32], [], full_k512_ana_clause_body⟩
      ⟨"full_k512_ana_clause", [i64, i32, i32], [], k5AnaClauseSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_ana_clause_wp fullM4SweepEnv)

theorem m4Sweep_k512_analyze_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_analyze", [i64, i32], [.bool], full_k512_analyze_body⟩
      ⟨"full_k512_analyze", [i64, i32], [.bool], k5AnalyzeSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_analyze_wp fullM4SweepEnv
    m4_row_k5_anacl m4_row_k5_bt m4_row_k5_mtf m4_row_k5_watch m4_row_k5_assign)

theorem m4Sweep_k512_solve_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_solve", [i64, i64], [i64], full_k512_solve_body⟩
      ⟨"full_k512_solve", [i64, i64], [i64], k5SolveSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_solve_wp fullM4SweepEnv
    m4_row_k5_bt m4_row_k5_assign m4_row_k5_prop m4_row_k5_ana)

theorem m4Sweep_k512_flip_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_flip", [i64, i32], [.bool], full_k512_flip_body⟩
      ⟨"full_k512_flip", [i64, i32], [.bool], k5FlipSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_flip_wp fullM4SweepEnv)

theorem m4Sweep_k512_add_live_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_k512_add_live", [i64, i32, i32], [], full_k512_add_live_body⟩
      ⟨"full_k512_add_live", [i64, i32, i32], [], k5AddLiveSpec, true⟩ :=
  SpecEntry.Impl.of (full_k512_add_live_wp fullM4SweepEnv
    m4_row_k5_bt m4_row_k5_assign m4_row_k5_watch)

theorem m4Sweep_cone_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_cone", [i64, i32], [i64], full_m4_sweep_cone_body⟩
      ⟨"full_m4_sweep_cone", [i64, i32], [i64], m4SweepConeSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_cone_wp fullM4SweepEnv m4_row_k5_init m4_row_k5_addcl)

theorem m4Sweep_refine_sig_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_refine_sig", [i64, i32, i32], [], full_m4_sweep_refine_sig_body⟩
      ⟨"full_m4_sweep_refine_sig", [i64, i32, i32], [], m4SweepRefineSigSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_refine_sig_wp fullM4SweepEnv)

theorem m4Sweep_rand_phases_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_rand_phases", [i64, i32], [], full_m4_sweep_rand_phases_body⟩
      ⟨"full_m4_sweep_rand_phases", [i64, i32], [], m4SweepRandPhasesSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_rand_phases_wp fullM4SweepEnv m4_row_rng)

theorem m4Sweep_flip_round_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_flip_round", [i64, i32], [i32], full_m4_sweep_flip_round_body⟩
      ⟨"full_m4_sweep_flip_round", [i64, i32], [i32], m4SweepFlipRoundSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_flip_round_wp fullM4SweepEnv m4_row_rng m4_row_k5_flip)

theorem m4Sweep_sim_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_sim", [i64, i32, i64], [i32], full_m4_sweep_sim_body⟩
      ⟨"full_m4_sweep_sim", [i64, i32, i64], [i32], m4SweepSimSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_sim_wp fullM4SweepEnv
    m4_row_k5_solve m4_row_ref m4_row_flipr m4_row_rand)

theorem m4Sweep_rearm_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_rearm", [i64, i32], [], full_m4_sweep_rearm_body⟩
      ⟨"full_m4_sweep_rearm", [i64, i32], [], m4SweepRearmSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_rearm_wp fullM4SweepEnv)

theorem m4Sweep_build_pht_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_build_pht", [i64, i32, i64], [], full_m4_sweep_build_pht_body⟩
      ⟨"full_m4_sweep_build_pht", [i64, i32, i64], [], m4SweepBuildPhtSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_build_pht_wp fullM4SweepEnv)

theorem m4Sweep_units_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_units", [i64, i32, i32, i64], [i64], full_m4_sweep_units_body⟩
      ⟨"full_m4_sweep_units", [i64, i32, i32, i64], [i64], m4SweepUnitsSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_units_wp fullM4SweepEnv
    m4_row_k5_flip m4_row_ref m4_row_k5_solve m4_row_addu m4_row_k5_live m4_row_rearm)

theorem m4Sweep_classes_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_classes", [i64, i32, i32, i64], [i64], full_m4_sweep_classes_body⟩
      ⟨"full_m4_sweep_classes", [i64, i32, i32, i64], [i64], m4SweepClassesSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_classes_wp fullM4SweepEnv
    m4_row_pht m4_row_k5_flip m4_row_k5_solve m4_row_ref m4_row_addb m4_row_k5_live m4_row_rearm)

theorem m4Sweep_var_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_var", [i64, i32, i64], [i64], full_m4_sweep_var_body⟩
      ⟨"full_m4_sweep_var", [i64, i32, i64], [i64], m4SweepVarSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_var_wp fullM4SweepEnv
    m4_row_cone m4_row_sim m4_row_units m4_row_classes)

theorem m4Sweep_dense_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_dense", [i64, i64, i64], [i64], full_m4_sweep_dense_body⟩
      ⟨"full_m4_sweep_dense", [i64, i64, i64], [i64], m4SweepDenseSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_dense_wp fullM4SweepEnv m4_row_var)

theorem m4Sweep_sat_impl :
    SpecEntry.Impl fullM4SweepEnv
      ⟨"full_m4_sweep_sat", [i64, i64, i64], [i64], full_m4_sweep_sat_body⟩
      ⟨"full_m4_sweep_sat", [i64, i64, i64], [i64], m4SweepSatSpec, true⟩ :=
  SpecEntry.Impl.of (full_m4_sweep_sat_wp fullM4SweepEnv
    m4_row_fbt m4_row_enter m4_row_dense m4_row_reb m4_row_fprop)

theorem fullM4Sweep_tableImpl :
    TableImpl fullM4SweepEnv fullM4SweepModule.fns fullM4SweepSpecTable :=
  ⟨m4Sweep_k512_init_impl, m4Sweep_k512_watch_impl, m4Sweep_k512_assign_impl,
   m4Sweep_k512_add_clause_impl, m4Sweep_k512_mtf_impl, m4Sweep_k512_backtrack_impl,
   m4Sweep_k512_propagate_impl, m4Sweep_k512_ana_clause_impl, m4Sweep_k512_analyze_impl,
   m4Sweep_k512_solve_impl, m4Sweep_k512_flip_impl, m4Sweep_k512_add_live_impl,
   m4Sweep_cone_impl, m4Sweep_refine_sig_impl, m4Sweep_rand_phases_impl,
   m4Sweep_flip_round_impl, m4Sweep_sim_impl, m4Sweep_rearm_impl,
   m4Sweep_build_pht_impl, m4Sweep_units_impl, m4Sweep_classes_impl,
   m4Sweep_var_impl, m4Sweep_dense_impl, m4Sweep_sat_impl, trivial⟩

/-- Unconditional `ModuleOk` certifying all `24/24` functions of `fullM4SweepModule` against
`fullM4SweepEnv`. -/
theorem fullM4SweepEnv_moduleOk : ModuleOk fullM4SweepEnv fullM4SweepModule :=
  Env.ofTable_moduleOk fullM4Sweep_acyclic fullM4Sweep_allFns_wf fullM4Sweep_tableImpl

/-! ## 2. Headline UNSAT Soundness Theorems (`FullSparseInv` & `FullDenseInv`) -/

/-- Headline sparse-mode UNSAT soundness for `full_m4_sweep_sat`: preserves `FullSparseInv`
at decision level `0` without exceeding fuel, and `r = 20#64` entails `F0.Unsat`. -/
theorem full_m4_sweep_sat_unsat_sound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {budget tick_lim : BitVec 64} {m : Mem 64}
    (hinv : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m) :
    Func.wp fullM4SweepEnv full_m4_sweep_sat_body (c.hdr, budget, tick_lim, ()) m
      (fun (r, ()) m' => ∃ s',
        FullSparseInv c F0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m4Sweep_sat_impl.2 _ _ _ _
    ⟨c, F0, s, R, rfl, hinv, hm, fun _ s' _ hsp hlvl hfl hdom huns hm' =>
      ⟨s', hsp, hlvl, hfl, hdom, huns, hm'⟩⟩

/-- Headline dense-mode UNSAT soundness for `full_m4_sweep_dense`: preserves `FullDenseInv`,
and `r = 20#64` entails `F0.Unsat`. -/
theorem full_m4_sweep_dense_unsat_sound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {budget tick_lim : BitVec 64} {m : Mem 64}
    (hinv : FullDenseInv c F0 s) (hm : (FullMem c s ⋆ R) m) :
    Func.wp fullM4SweepEnv full_m4_sweep_dense_body (c.hdr, budget, tick_lim, ()) m
      (fun (r, ()) m' => ∃ s',
        FullDenseInv c F0 s' ∧ s'.core.cur_vars = s.core.cur_vars ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m4Sweep_dense_impl.2 _ _ _ _
    ⟨c, F0, s, R, rfl, hinv, hm, fun _ s' _ hd hcv hfl hdom huns hm' =>
      ⟨s', hd, hcv, hfl, hdom, huns, hm'⟩⟩

/-! ## 3. Concrete `100060`-Byte `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

/-- Concrete `FullCfg` (`max_vars = 1`, `wcap = 1`, `scratch_cap = 24576`, `avail = 100060`). -/
def nvM4SweepCfg : FullCfg where
  hdr := 0x1000#64
  avail := 100060
  mv := 1
  max_vars := 1
  bva_cap := 0
  nc := 2
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 24576
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

/-- Concrete inconsistent `K512State` (`nv = 1`, `nc = 0`, `incons = 1`, `acap = 2784`). -/
def nvM4K512State : K512State where
  nv := 1#32
  nc := 0#32
  lvl := 0#32
  prop := 0#32
  trl_end := 0#32
  unass := 1#32
  incons := 1#32
  qfirst := 0#32
  qlast := 0#32
  qsearch := 0#32
  qstamp := 1#32
  ticks := 0#32
  tick_lim := 0#32
  alen := 0#32
  acap := 2784#32
  nassump := 0#32
  nkl := 0#32
  nana := 0#32
  status := 0#32
  phase := 0#32
  hdrTail := List.replicate 12 0#32
  lvlArr := List.replicate 512 0#32
  rsn := List.replicate 512 0xFFFFFFFF#32
  qprev := List.replicate 512 0xFFFFFFFF#32
  qnext := List.replicate 512 0xFFFFFFFF#32
  qstampArr := List.replicate 512 0#32
  trl := List.replicate 512 0#32
  flags := List.replicate 512 0#32
  ana := List.replicate 512 0#32
  kl := List.replicate 512 0#32
  assump := List.replicate 512 0#32
  vals := List.replicate 1024 0#32
  whead := List.replicate 1024 0xFFFFFFFF#32
  wnext := List.replicate 4096 0xFFFFFFFF#32
  wblit := List.replicate 4096 0#32
  clOff := List.replicate 2048 0#32
  clSz := List.replicate 2048 0#32
  arena := List.replicate 2784 0#32

theorem nvM4K512State_shapes : nvM4K512State.ShapesOk 2784 :=
  ⟨List.length_replicate, List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate, List.length_replicate, List.length_replicate,
   List.length_replicate, List.length_replicate⟩

/-- Concrete `24576`-word `scratch_buf` embedding `nvM4K512State` at `K512_BASE = 2304`. -/
def nvM4SweepScratchBuf : List (BitVec 32) :=
  List.replicate 2304 0#32 ++ nvM4K512State.toSlab

theorem nvM4SweepScratchBuf_length : nvM4SweepScratchBuf.length = 24576 := by
  unfold nvM4SweepScratchBuf
  rw [List.length_append, List.length_replicate, nvM4K512State.toSlab_length nvM4K512State_shapes]

theorem nvM4SweepScratchBuf_k5State :
    k5StateOfScratch nvM4SweepScratchBuf = nvM4K512State := by
  unfold k5StateOfScratch nvM4SweepScratchBuf k5Base
  rw [List.drop_append_of_le_length (by rw [List.length_replicate]; exact le_refl _),
    List.drop_replicate, Nat.sub_self, List.replicate_zero, List.nil_append]
  exact K512State.ofSlab_toSlab nvM4K512State_shapes

theorem nvM4SweepScratchBuf_k5Inv :
    K512ScratchInv (fun _ => False) nvM4SweepScratchBuf := by
  refine ⟨by rw [nvM4SweepScratchBuf_length]; decide,
    by rw [nvM4SweepScratchBuf_length]; decide, ?_⟩
  rw [nvM4SweepScratchBuf_length, nvM4SweepScratchBuf_k5State]
  have hsh : nvM4K512State.ShapesOk (24576 - (k5Base + k5SlabFixed)) := nvM4K512State_shapes
  have hcl : K512ClausesOk (24576 - (k5Base + k5SlabFixed)) (fun _ => False) nvM4K512State :=
    { acap_ge := by decide
      acap_lt := by decide
      acap_eq := rfl
      nv_le := by decide
      nc_le := by decide
      alen_le := by decide
      nassump_le := by decide
      nkl_le := by decide
      nana_le := by decide
      cl_wf := fun _ h => by simp [-List.reduceReplicate, nvM4K512State] at h
      cl_mono := fun _ _ _ h => by simp [-List.reduceReplicate, nvM4K512State] at h
      incons_ok := fun _ _ h => h
      assump_ok := fun _ h => by simp [-List.reduceReplicate, nvM4K512State] at h
      flags_clean := fun v hv => by
        have hv1 : v < 1 := hv
        simp [-List.reduceReplicate, nvM4K512State, show v < 512 by omega] }
  have hwat : K512WatchesOk nvM4K512State := by
    refine ⟨[[], []], rfl, by decide, fun l hl => ?_, fun l hl w hw => ?_⟩
    · have hl2 : l < 2 := hl
      rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
      · simp only [nvM4K512State, List.getElem?_replicate, show (0 : Nat) < 1024 by decide,
          ↓reduceIte, Option.getD_some, List.getElem?_cons_zero]
        exact K5WChain.nil
      · simp only [nvM4K512State, List.getElem?_replicate, show (1 : Nat) < 1024 by decide,
          ↓reduceIte, Option.getD_some, List.getElem?_cons_succ, List.getElem?_cons_zero]
        exact K5WChain.nil
    · have hl2 : l < 2 := hl
      rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;> simp at hw
  have hasg : K512BaseAssignOk (fun _ => False) nvM4K512State :=
    { trl_end_le := by decide
      prop_le := by decide
      unass_eq := by decide
      vals_dom := fun l hl => by
        have hl2 : l < 2 := hl
        simp [-List.reduceReplicate, nvM4K512State, show l < 1024 by omega]
      vals_neg_iff := fun l hl => by
        have hl2 : l < 2 := hl
        have hnl : l ^^^ 1 < 1024 := by
          rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;> decide
        simp [-List.reduceReplicate, nvM4K512State, show l < 1024 by omega, hnl]
      vals_nz_iff_trl := fun l hl => by
        have hl2 : l < 2 := hl
        simp [-List.reduceReplicate, nvM4K512State, show l < 1024 by omega]
      trl_nodup := by decide
      trl_lt := fun l hl => by simp [-List.reduceReplicate, k5TrailLits, nvM4K512State] at hl
      trl_lvl_le := fun v hv => by
        have hv1 : v < 1 := hv
        simp [-List.reduceReplicate, nvM4K512State, show v < 512 by omega]
      unass_lvl_zero := fun v hv _ => by
        have hv1 : v < 1 := hv
        simp [-List.reduceReplicate, nvM4K512State, show v < 512 by omega]
      trl_lvl_mono := fun _ _ _ h => by simp [-List.reduceReplicate, nvM4K512State] at h
      dec_earliest := fun _ _ _ h => by simp [-List.reduceReplicate, nvM4K512State] at h
      lvl0_ok := fun _ h => by simp [-List.reduceReplicate, nvM4K512State] at h }
  exact ⟨hsh, hcl, hwat, hasg, fun _ h => by simp [-List.reduceReplicate, nvM4K512State] at h⟩

/-- Zero-initialized `FullScratch` for `nvM4SweepCfg` carrying `nvM4SweepScratchBuf`. -/
def nvM4SweepScratch : FullScratch where
  heap_len := 0
  scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64
  learned_lits := 0#64; min_removed := 0#64; delayed_len := 0; stable := 0#64
  switched := 0#64; mode_count := 0#64; mode_confl_lim := 0#64; mode_tick_lim := 0#64
  mode_saved_ticks := 0#64; search_ticks := 0#64; q_first := 0#64; q_last := 0#64
  q_search_idx := 0#64; q_search_stamp := 0#64; q_cur_stamp := 0#64
  target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64; rephased := 0#64
  reduce_limit := 0#64; reductions := 0#64; tier1 := 0#64; tier2 := 0#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64
  subst_cnt := 0#64; cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64
  bce_cnt := 0#64; bva_cnt := 0#64; walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 2 0#8
  phases := List.replicate 1 0#8
  phases_target := List.replicate 1 0#8
  phases_best := List.replicate 1 0#8
  walk_best := List.replicate 1 0#8
  heap := List.replicate 1 0#32
  pos := List.replicate 1 0#32
  shrink_stk := List.replicate 1 0#32
  q_prev := List.replicate 1 0#32
  q_next := List.replicate 1 0#32
  q_stamp := List.replicate 1 0#32
  wsort := List.replicate 2 0#32
  work_stk1 := List.replicate 2 0#32
  work_stk2 := List.replicate 2 0#32
  tarjan_mark := List.replicate 2 0#32
  tarjan_reach := List.replicate 2 0#32
  score := List.replicate 1 0#64
  sim_sig := List.replicate 1 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := nvM4SweepScratchBuf

/-- Concrete dense-mode UNSAT `FullState` (`FL_ACTIVE | FL_SWEEP`, `dense_mode = 1`,
`inconsistent = 1`, `fuel = 1`, zero trail & `M4TmkZero`) for `nvOneLitF0 = {(x0), (¬x0)}`. -/
def nvM4SweepState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 1, unassigned := 1#64
      arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
      cur_level := 0, fuel := 1#64, confl_ref := 0#64, confl_type := 1#64
      confl_lit0 := 1#64, confl_lit1 := 1#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 1#64
      inconsistent := 1#64
      vals := [0#8, 0#8]
      lit_mark := [0#8, 0#8]
      mrk := [0#8]
      flags := [1025#32]
      lvl := [0#32]
      rsns := [0xFFFFFFFF#32]
      trl := [0#32]
      trail_pos := [0#32]
      tmp := [0#32]
      min_clr := [0#32]
      frame_trail := [0#32, 0#32]
      frame_dec := [0#32, 0#32]
      wvec := [0#32, 0#32, 0#32, 0#32]
      repr := [0#32, 0#32]
      min_stk := [0#32, 0#32, 0#32, 0#32]
      arena := []
      wstk := [0#32] }
  scratch := nvM4SweepScratch

/-- Concrete sparse-mode UNSAT `FullState` (`dense_mode = 0`, `inconsistent = 1`, `fuel = 1`)
for `nvOneLitF0 = {(x0), (¬x0)}`. -/
def nvM4SweepSparseState : FullState :=
  { nvM4SweepState with core := { nvM4SweepState.core with dense_mode := 0#64 } }

theorem nvM4SweepState_lengths : nvM4SweepState.LengthsOk nvM4SweepCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, nvM4SweepScratchBuf_length⟩⟩

def nvM4BlockHdr (s : FullState) : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++
  bytes64 (Full.hdrTailWords nvM4SweepCfg s)

def nvM4BlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM4SweepState.core.vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM4SweepState.scratch.walk_vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM4SweepState.core.lit_mark ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM4SweepState.core.mrk ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM4SweepState.scratch.phases ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM4SweepState.scratch.phases_target ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM4SweepState.scratch.phases_best ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM4SweepState.scratch.walk_best ++ List.replicate 7 0)

def nvM4BlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM4SweepState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.core.trail_pos ++ List.replicate 4 0)

def nvM4BlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM4SweepState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.scratch.shrink_stk ++ List.replicate 4 0)

def nvM4BlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM4SweepState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SweepState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvM4SweepState.core.frame_dec ++ List.replicate 0 0)

def nvM4BlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM4SweepState.core.wvec ++
  bytesOf (t := i32) nvM4SweepState.core.repr ++
  bytesOf (t := i32) nvM4SweepState.scratch.wsort ++
  bytesOf (t := i32) nvM4SweepState.scratch.work_stk1 ++
  bytesOf (t := i32) nvM4SweepState.scratch.work_stk2 ++
  bytesOf (t := i32) nvM4SweepState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvM4SweepState.scratch.tarjan_reach ++
  bytes64 nvM4SweepState.scratch.score ++
  bytes64 nvM4SweepState.scratch.sim_sig

def nvM4BlockTail : List UInt8 :=
  bytesOf (t := i32) nvM4SweepState.core.min_stk ++
  bytesOf (t := i32) nvM4SweepState.scratch.glue_used ++
  bytesOf (t := i32) nvM4SweepState.scratch.last_learned ++
  bytesOf (t := i32) nvM4SweepState.core.arena ++
  bytesOf (t := i32) nvM4SweepState.core.wstk ++
  bytesOf (t := i32) nvM4SweepState.scratch.delayed ++
  bytesOf (t := i32) nvM4SweepState.scratch.red_refs ++
  bytesOf (t := i32) nvM4SweepState.scratch.extend_stk ++
  bytesOf (t := i32) nvM4SweepState.scratch.scratch_buf ++
  List.replicate 0 0

/-- Concrete `100060`-byte dense-mode image encoding `nvM4SweepCfg` and `nvM4SweepState`. -/
def nvM4SweepBytes : List UInt8 :=
  nvM4BlockHdr nvM4SweepState ++ nvM4BlockBytes ++ nvM4BlockU32A ++ nvM4BlockU32B ++
  nvM4BlockU32C ++ nvM4BlockWvec ++ nvM4BlockTail

/-- Concrete `100060`-byte sparse-mode image encoding `nvM4SweepCfg` and
`nvM4SweepSparseState`. -/
def nvM4SweepSparseBytes : List UInt8 :=
  nvM4BlockHdr nvM4SweepSparseState ++ nvM4BlockBytes ++ nvM4BlockU32A ++ nvM4BlockU32B ++
  nvM4BlockU32C ++ nvM4BlockWvec ++ nvM4BlockTail

/-- Concrete dense-mode `Mem 64` heap mapped at `nvM4SweepCfg.hdr` (`0x1000#64`). -/
def nvM4SweepMem : Mem 64 := nvM4SweepBytes.At nvM4SweepCfg.hdr

/-- Concrete sparse-mode `Mem 64` heap mapped at `nvM4SweepCfg.hdr` (`0x1000#64`). -/
def nvM4SweepSparseMem : Mem 64 := nvM4SweepSparseBytes.At nvM4SweepCfg.hdr

theorem nvM4SweepBytes_length : nvM4SweepBytes.length = 100060 := by
  simp only [nvM4SweepBytes, nvM4BlockHdr, nvM4BlockBytes, nvM4BlockU32A, nvM4BlockU32B,
    nvM4BlockU32C, nvM4BlockWvec, nvM4BlockTail, nvM4SweepState, nvM4SweepScratch,
    List.length_append, List.length_replicate, bytesOf_length, bytes64_length,
    Full.hdrTailWords_length, nvM4SweepScratchBuf_length, List.length_cons, List.length_nil]
  rfl

theorem nvM4SweepSparseBytes_length : nvM4SweepSparseBytes.length = 100060 := by
  simp only [nvM4SweepSparseBytes, nvM4BlockHdr, nvM4BlockBytes, nvM4BlockU32A, nvM4BlockU32B,
    nvM4BlockU32C, nvM4BlockWvec, nvM4BlockTail, nvM4SweepSparseState, nvM4SweepState,
    nvM4SweepScratch, List.length_append, List.length_replicate, bytesOf_length, bytes64_length,
    Full.hdrTailWords_length, nvM4SweepScratchBuf_length, List.length_cons, List.length_nil]
  rfl

theorem nvM4SweepF0_unsat : Full.nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [Full.nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [Full.nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvM4SweepMem_ok_of_dense_mode (dm : BitVec 64) :
    let s : FullState :=
      { nvM4SweepState with core := { nvM4SweepState.core with dense_mode := dm } }
    FullMem nvM4SweepCfg s
      ((nvM4BlockHdr s ++ nvM4BlockBytes ++ nvM4BlockU32A ++ nvM4BlockU32B ++
        nvM4BlockU32C ++ nvM4BlockWvec ++ nvM4BlockTail).At nvM4SweepCfg.hdr) := by
  intro s
  let c := nvM4SweepCfg
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : (nvM4BlockHdr s).length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        ((nvM4BlockHdr s).At c.hdr) :=
    Full.nv_join_pair
      (Full.nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (Full.nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvM4BlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvM4BlockBytes.At c.pVals) := by
    have h1 := Full.nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesTarget)
      (xs := s.scratch.phases_target) 1 7 rfl (by decide)
    have h7 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best)
      1 7 rfl (by decide)
    have h8 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best)
      1 7 rfl (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_sep_reorg (Full.nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => Full.nv_zip4 hm
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg hall fun _ hm => by
      have hfin := Full.nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvM4BlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvM4BlockU32A.At c.pFlags) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvM4BlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvM4BlockU32B.At c.pTmp) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl
      (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk)
      4 4 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvM4BlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvM4BlockU32C.At c.pQPrev) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail)
      8 0 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
      (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvM4BlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvM4BlockWvec.At c.pWvec) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach)
      8 rfl (by decide)
    have h8 := Full.nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := Full.nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM4BlockTail.length = 98644 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvM4BlockTail.At c.pMinStk) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned)
      64 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl
      (by decide)
    have h8 := Full.nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := Full.nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 98304
      (by show 4 * nvM4SweepScratchBuf.length = 98304; rw [nvM4SweepScratchBuf_length])
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := Full.nv_join_pair h12345678 h9 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm =>
      by unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := Full.nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := Full.nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := Full.nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := Full.nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := Full.nv_join_pair h04 hWvec (by decide) (by decide)
  exact (Full.nv_sep_reorg (Q := FullMem c s) (Full.nv_join_pair h05 hTail (by decide) (by decide))
    fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad
      exact sep_ac hm).2

theorem nvM4SweepMem_ok : FullMem nvM4SweepCfg nvM4SweepState nvM4SweepMem :=
  nvM4SweepMem_ok_of_dense_mode 1#64

theorem nvM4SweepSparseMem_ok :
    FullMem nvM4SweepCfg nvM4SweepSparseState nvM4SweepSparseMem :=
  nvM4SweepMem_ok_of_dense_mode 0#64

theorem nvM4Sweep_invW :
    FullDenseInvW nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] nvM4SweepState := by
  have hmv : nvM4SweepCfg.max_vars = 1 := rfl
  have hcv : nvM4SweepState.core.cur_vars = 1 := rfl
  have hte : nvM4SweepState.core.trail_end = 0 := rfl
  have hcl : nvM4SweepState.core.cur_level = 0 := rfl
  have hdm : nvM4SweepState.core.dense_mode ≠ 0#64 := by decide
  have hrefs : fullArenaClauseRefsCore nvM4SweepState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvM4SweepState.core := by
    unfold ModeWatchesInv; rw [ite_eq_right hdm]
    refine DenseWatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvM4SweepState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvM4SweepState] at hp
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact DenseWatchSliceOk.empty
  have hw : FullWitnessInv nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] nvM4SweepState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun _ => nvM4SweepF0_unsat
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; omega
      trail_vars_nodup := fun i _ hi => by rw [hte] at hi; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [nvM4SweepState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          exact ⟨(fun h => by cases h), (fun ⟨_, hi, _⟩ => by rw [hte] at hi; omega)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          exact ⟨(fun h => by cases h), (fun ⟨_, hi, _⟩ => by rw [hte] at hi; omega)⟩
      lvl_le := fun i hi => by rw [hte] at hi; omega
      dec_earliest := fun i _ hi => by rw [hte] at hi; omega
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi => by rw [hte] at hi; omega
      trail_pos_inv := fun i hi => by rw [hte] at hi; omega
      level0_rsn_none := fun i hi => by rw [hte] at hi; omega
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; obtain rfl : L = 0 := (by omega); exact Nat.zero_le _
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi => by rw [hte] at hi; omega
      reason_lit_mem := fun i hi => by rw [hte] at hi; omega }
  refine ⟨nvM4SweepState_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvM4SweepState, nvM4SweepScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl, hdm⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · have : fullArenaClauseRefs nvM4SweepState = [] := rfl; simp [this] at hr

theorem nvM4SweepSparse_inv :
    FullSparseInv nvM4SweepCfg Full.nvOneLitF0 nvM4SweepSparseState :=
  nvM4Sweep_invW.toSparse_clear_dense.toSparse

theorem nvM4Sweep_tmkZero : M4TmkZero nvM4SweepState := fun v hv => by
  change v < 1 at hv; obtain rfl : v = 0 := (by omega); rfl

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `full_k512_init`. -/
theorem nv_m4_k512_init :
    Func.wp fullM4SweepEnv full_k512_init_body (nvM4SweepCfg.hdr, 1#32, ()) nvM4SweepMem
      (fun () m' => ∃ scr',
        (∀ P, K512ScratchInv P scr') ∧ (k5StateOfScratch scr').nv = 1#32 ∧
        FullMem nvM4SweepCfg
          { nvM4SweepState with scratch := { nvM4SweepState.scratch with scratch_buf := scr' } }
          m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4SweepCfg nvM4SweepState ⋆ emp) nvM4SweepMem := by
    rw [sep_emp]; exact nvM4SweepMem_ok
  refine m4Sweep_k512_init_impl.2 _ _ _ _
    ⟨nvM4SweepCfg, nvM4SweepState, emp, rfl, nvM4SweepState_lengths, hm, ?_⟩
  rw [ite_eq_right (by decide)]
  intro scr' m' _ _ _ _ hK _ hnv _ _ _ _ _ _ _ hm'
  rw [sep_emp] at hm'; exact ⟨scr', hK, hnv, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_k512_solve` on the embedded
inconsistent `K512State` slab. -/
theorem nv_m4_k512_solve :
    Func.wp fullM4SweepEnv full_k512_solve_body (nvM4SweepCfg.hdr, 100#64, ()) nvM4SweepMem
      (fun (r, ()) m' => ∃ fuel' scr',
        K512ScratchInv (fun _ => False) scr' ∧ (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧
        FullMem nvM4SweepCfg
          { nvM4SweepState with
            core := { nvM4SweepState.core with fuel := fuel' }
            scratch := { nvM4SweepState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4SweepCfg nvM4SweepState ⋆ emp) nvM4SweepMem := by
    rw [sep_emp]; exact nvM4SweepMem_ok
  exact m4Sweep_k512_solve_impl.2 _ _ _ _
    ⟨nvM4SweepCfg, nvM4SweepState, (fun _ => False), emp, rfl, nvM4SweepState_lengths,
     nvM4SweepScratchBuf_k5Inv, hm,
     fun r fuel' scr' m' _ _ _ hK _ _ _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨fuel', scr', hK, hdom, nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_m4_sweep_cone`. -/
theorem nv_m4_sweep_cone :
    Func.wp fullM4SweepEnv full_m4_sweep_cone_body (nvM4SweepCfg.hdr, 0#32, ()) nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M4SweepConeOk [[0], [1]] s' (r &&& 0xFFFF#64).toNat ∧
        Full.nvOneLitF0.Unsat ∧ FullMem nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4SweepCfg nvM4SweepState ⋆ emp) nvM4SweepMem := by
    rw [sep_emp]; exact nvM4SweepMem_ok
  exact m4Sweep_cone_impl.2 _ _ _ _
    ⟨nvM4SweepCfg, Full.nvOneLitF0, [[0], [1]], nvM4SweepState, emp, rfl,
     nvM4Sweep_invW, by decide, by decide, nvM4Sweep_tmkZero, hm,
     fun _ _ _ _ _ m' hd _ _ _ _ hcone _ hm' => by
       rw [sep_emp] at hm'; exact ⟨_, hd, hcone, nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_m4_sweep_var`. -/
theorem nv_m4_sweep_var :
    Func.wp fullM4SweepEnv full_m4_sweep_var_body
      (nvM4SweepCfg.hdr, 0#32, 8192#64, ()) nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M4TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4SweepCfg nvM4SweepState ⋆ emp) nvM4SweepMem := by
    rw [sep_emp]; exact nvM4SweepMem_ok
  exact m4Sweep_var_impl.2 _ _ _ _
    ⟨nvM4SweepCfg, Full.nvOneLitF0, [[0], [1]], nvM4SweepState, emp, rfl,
     nvM4Sweep_invW, by decide, by decide, nvM4Sweep_tmkZero, hm,
     fun r s' m' hd _ _ ht hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, ht, hdom, nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_m4_sweep_dense`. -/
theorem nv_m4_sweep_dense :
    Func.wp fullM4SweepEnv full_m4_sweep_dense_body
      (nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvM4SweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ FullMem nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4SweepCfg nvM4SweepState ⋆ emp) nvM4SweepMem := by
    rw [sep_emp]; exact nvM4SweepMem_ok
  exact m4Sweep_dense_impl.2 _ _ _ _
    ⟨nvM4SweepCfg, Full.nvOneLitF0, nvM4SweepState, emp, rfl,
     nvM4Sweep_invW.toDense, hm, fun r s' m' hd _ _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, hdom, nvM4SweepF0_unsat, hm'⟩⟩

/-- Headline concrete `100060`-byte `Mem 64` sparse-mode UNSAT non-vacuity witness
(`XPost := False`, `0` SAT proofs) for `full_m4_sweep_sat` under `fullM4SweepEnv`. -/
theorem nv_m4_sweep_sat :
    Func.wp fullM4SweepEnv full_m4_sweep_sat_body
      (nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM4SweepSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM4SweepCfg Full.nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ FullMem nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4SweepCfg nvM4SweepSparseState ⋆ emp) nvM4SweepSparseMem := by
    rw [sep_emp]; exact nvM4SweepSparseMem_ok
  exact m4Sweep_sat_impl.2 _ _ _ _
    ⟨nvM4SweepCfg, Full.nvOneLitF0, nvM4SweepSparseState, emp, rfl,
     nvM4SweepSparse_inv, hm, fun r s' m' hsp hlvl _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hsp, hlvl, hdom, nvM4SweepF0_unsat, hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullM4Sweep
