module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofDriver
meta import LeanQbe.T.Examples.Kissat.FullM6Sweep
meta import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
meta import LeanQbe.T.Examples.Kissat.FullM4SweepProof
meta import LeanQbe.T.Examples.Kissat.FullM6SweepProofDriver
meta import LeanQbe.T.CoreHub

/-!
# Tests of `LeanQbe.T.Examples.Kissat.FullM6Sweep`

Verifies:
1. Structural module invariants (`checkAcyclic`, empty `exits`, function/extern/table counts,
   distinct names).
2. Backend emission & legalization (`PrintCpp.ppTModule`, `PrintCpp.ppModule`, `PrintQbe.module`,
   and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, `.x64AVX512`).
3. Parametric `ModuleOk` assembly, driver WP specs, concrete `Mem 64` UNSAT non-vacuity, and
   single-line `< 115c` `std3` `#print axioms` audit.
-/

set_option autoImplicit false

public section

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM6Sweep

#guard m6SweepModule.checkAcyclic
#guard m6SweepModule.exits.isEmpty
#guard m6SweepModule.fns.length == 39
#guard m6SweepModule.externs.length == 12
#guard m6SweepSpecTable.length == 51
#guard ((m6SweepModule.fns.map Fn.name ++ m6SweepModule.externs.map Extern.name).eraseDups.length ==
  51)

#guard (PrintCpp.ppTModule m6SweepModule).isOk
#guard (PrintCpp.ppModule m6Sweep_fns).isOk
#guard (PrintQbe.module m6SweepModule).isOk

#guard (PrintCpp.ppModule (m6Sweep_fns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (m6Sweep_fns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (m6Sweep_fns.map (Fn.legal .x64AVX2))).isOk
#guard m6Sweep_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard nvM6SweepState.core.inconsistent == 0#64
#guard nvM6SweepState.core.dense_mode == 1#64
#guard nvM6SweepSparseState.core.inconsistent == 0#64
#guard nvM6SweepSparseState.core.dense_mode == 0#64
#guard nvM6K6State.max_v == 512#32
#guard nvM6K6State.incons == 1#32
#guard nvM6SweepBytes.length == FullM4Sweep.nvM4SweepCfg.avail
#guard nvM6SweepSparseBytes.length == FullM4Sweep.nvM4SweepCfg.avail

section AxiomAudit

theorem m6sw_sigs :
    List.map (fun e => (e.name, e.as, e.rs)) (List.take 39 m6SweepSpecTable) =
      List.map (fun f => (f.name, f.as, f.rs)) m6Sweep_fns :=
  m6SweepSpecTable_sigs

theorem m6sw_nodup : (List.map SpecEntry.name m6SweepSpecTable).Nodup :=
  m6SweepSpecTable_nodup

theorem m6sw_noex : ∀ e ∈ m6SweepSpecTable, e.noExit = true :=
  m6SweepSpecTable_noExit

theorem m6sw_acyc : m6SweepModule.checkAcyclic = true :=
  m6Sweep_acyclic

theorem m6sw_wf : AllFns Fn.Wf m6SweepModule.fns :=
  m6Sweep_allFns_wf

theorem m6sw_dense (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSweepVars : M6EnvSpec Γ "full_m6_sweep_vars" m6SweepVarsSpec) :
    ∀ args m Q X, FullM4Sweep.m4SweepDenseSpec args m Q X →
      Func.wp Γ full_m6_sweep_dense_body args m Q X :=
  full_m6_sweep_dense_wp Γ hMaxV hSweepVars

theorem m6sw_canon (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSweepVars : M6EnvSpec Γ "full_m6_sweep_vars" m6SweepVarsSpec) :
    ∀ args m Q X, FullDefSweep.fullSweepDenseSpec args m Q X →
      Func.wp Γ full_m6_sweep_dense_body args m Q X :=
  full_m6_sweep_dense_canon_wp Γ hMaxV hSweepVars

theorem m6sw_sat (Γ : Env)
    (hBt : M6EnvSpec Γ "full_backtrack" Full.fullBacktrackSpec)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hEnter : M6EnvSpec Γ "full_enter_dense" Full.fullEnterDenseSpec)
    (hDense : M6EnvSpec Γ "full_m6_sweep_dense" FullM4Sweep.m4SweepDenseSpec)
    (hReb : M6EnvSpec Γ "full_rebuild_watches" Full.fullRebuildWatchesSpec)
    (hProp : M6EnvSpec Γ "full_propagate" Full.fullPropagateSpec)
    (hSubst : M6EnvSpec Γ "full_substitute" Full.fullSubstituteSpec) :
    ∀ args m Q X, FullM4Sweep.m4SweepSatSpec args m Q X →
      Func.wp Γ full_m6_sweep_sat_body args m Q X :=
  full_m6_sweep_sat_wp Γ hBt hMaxV hEnter hDense hReb hProp hSubst

theorem m6sw_top (Γ : Env)
    (hSat : M6EnvSpec Γ "full_m6_sweep_sat" FullM4Sweep.m4SweepSatSpec) :
    ∀ args m Q X, Full.fullSweepSatSpec args m Q X →
      Func.wp Γ full_sweep_sat_m6_body args m Q X :=
  full_sweep_sat_m6_wp Γ hSat

theorem m6sw_tbl
    (hUnits : ∀ args m Q X, m6SweepUnitsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_units_body args m Q X)
    (hClasses : ∀ args m Q X, m6SweepClassesSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_classes_body args m Q X)
    (hVar : ∀ args m Q X, m6SweepVarSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_var_body args m Q X)
    (hSift : ∀ args m Q X, m6CandSiftSpec args m Q X →
      Func.wp m6SweepEnv full_m6_cand_sift_body args m Q X)
    (hCollect : ∀ args m Q X, m6CollectCandsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_collect_cands_body args m Q X)
    (hVars : ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_vars_body args m Q X) :
    TableImpl m6SweepEnv m6SweepModule.fns m6SweepSpecTable :=
  m6Sweep_tableImpl_of_parts hUnits hClasses hVar hSift hCollect hVars

theorem m6sw_mod
    (hUnits : ∀ args m Q X, m6SweepUnitsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_units_body args m Q X)
    (hClasses : ∀ args m Q X, m6SweepClassesSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_classes_body args m Q X)
    (hVar : ∀ args m Q X, m6SweepVarSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_var_body args m Q X)
    (hSift : ∀ args m Q X, m6CandSiftSpec args m Q X →
      Func.wp m6SweepEnv full_m6_cand_sift_body args m Q X)
    (hCollect : ∀ args m Q X, m6CollectCandsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_collect_cands_body args m Q X)
    (hVars : ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_vars_body args m Q X) :
    ModuleOk m6SweepEnv m6SweepModule :=
  m6Sweep_moduleOk_of_parts hUnits hClasses hVar hSift hCollect hVars

theorem m6sw_nv_m :
    Full.FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState nvM6SweepMem :=
  nvM6SweepMem_ok

theorem m6sw_nv_ms :
    Full.FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepSparseState nvM6SweepSparseMem :=
  nvM6SweepSparseMem_ok

theorem m6sw_nv_k6i :
    Func.wp m6SweepEnv full_k6_init_body (FullM4Sweep.nvM4SweepCfg.hdr, 1#32, ()) nvM6SweepMem
      (fun () m' => ∃ scr',
        (∀ P, K6ScratchInv P scr') ∧ (k6StateOfScratch nvM6K6Layout scr').nv = 1#32 ∧
        Full.FullMem FullM4Sweep.nvM4SweepCfg
          { nvM6SweepState with scratch := { nvM6SweepState.scratch with scratch_buf := scr' } }
          m')
      (fun _ _ _ _ => False) :=
  nv_m6_k6_init

theorem m6sw_nv_k6s :
    Func.wp m6SweepEnv full_k6_solve_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 100#64, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ fuel' scr',
        K6ScratchInv (fun _ => False) scr' ∧ (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧
        Full.FullMem FullM4Sweep.nvM4SweepCfg
          { nvM6SweepState with
            core := { nvM6SweepState.core with fuel := fuel' }
            scratch := { nvM6SweepState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) :=
  nv_m6_k6_solve

theorem m6sw_nv_c :
    Func.wp m6SweepEnv full_m6_sweep_cone_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        Full.FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M6SweepConeOk [[0], [1]] s' (r &&& 0xFFFF#64).toNat ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_sweep_cone

theorem m6sw_nv_v
    (hVar : ∀ args m Q X, m6SweepVarSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_var_body args m Q X) :
    Func.wp m6SweepEnv full_m6_sweep_var_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, 8192#64, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        Full.FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M6TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_sweep_var_of hVar

theorem m6sw_nv_vs
    (hVars : ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_vars_body args m Q X) :
    Func.wp m6SweepEnv full_m6_sweep_vars_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        Full.FullDenseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
        M6TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_sweep_vars_of hVars

theorem m6sw_nv_d :
    Func.wp m6SweepEnv full_m6_sweep_dense_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM6SweepMem
      (fun x m' =>
        match x with
        | (r, ()) =>
          ∃ s',
            Full.FullDenseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
              (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧
                Full.FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_sweep_dense

theorem m6sw_nv_s :
    Func.wp m6SweepEnv full_m6_sweep_sat_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM6SweepSparseMem
      (fun x m' =>
        match x with
        | (r, ()) =>
          ∃ s',
            Full.FullSparseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
              s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧
                Full.nvOneLitF0.Unsat ∧ Full.FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_sweep_sat

theorem m6sw_nv_t :
    Func.wp m6SweepEnv full_sweep_sat_m6_body
      (FullM4Sweep.nvM4SweepCfg.hdr, ()) nvM6SweepSparseMem
      (fun x m' =>
        match x with
        | (r, ()) =>
          ∃ s',
            Full.FullSparseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
              s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧
                Full.nvOneLitF0.Unsat ∧ Full.FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_sweep_sat_m6

#print axioms m6sw_sigs
#print axioms m6sw_nodup
#print axioms m6sw_noex
#print axioms m6sw_acyc
#print axioms m6sw_wf
#print axioms m6sw_dense
#print axioms m6sw_canon
#print axioms m6sw_sat
#print axioms m6sw_top
#print axioms m6sw_tbl
#print axioms m6sw_mod
#print axioms m6sw_nv_m
#print axioms m6sw_nv_ms
#print axioms m6sw_nv_k6i
#print axioms m6sw_nv_k6s
#print axioms m6sw_nv_c
#print axioms m6sw_nv_v
#print axioms m6sw_nv_vs
#print axioms m6sw_nv_d
#print axioms m6sw_nv_s
#print axioms m6sw_nv_t

end AxiomAudit
