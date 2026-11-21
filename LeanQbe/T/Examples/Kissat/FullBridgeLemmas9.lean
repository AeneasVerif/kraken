module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullProof1

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Top Orchestrators (`Stage 4`, 6 fns)

Bridges all `6` top-level Stage-4 orchestrator functions (`indices 160..165`, strictly UNSAT-only,
zero SAT model-reconstruction proofs) directly onto canonical `FullSpec` (`mkFullEnv` / `fullEnv`):
- `160`: `full_probe` (`full_probe_bridge_wp`)
- `161`: `full_eliminate` (`full_eliminate_bridge_wp`)
- `162`: `full_preprocess` (`full_preprocess_bridge_wp`)
- `163`: `full_simplify` (`full_simplify_bridge_wp`)
- `164`: `full_search` (`full_search_bridge_wp`)
- `165`: `kissat_solve_bytes` (`kissat_solve_bytes_core_bridge_wp`, `kissat_solve_bytes_bridge_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat

/-! ## Part 1: Parametric `(Γ : Env)` canonical bridge lemmas (`6` fns) -/

theorem full_probe_bridge_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hCong : ∀ a m Q X, fullCongruenceSpec a m Q X → Γ "full_congruence" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullSweepSatSpec a m Q X → Γ "full_sweep_sat" [i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveSpec a m Q X → Γ "full_transitive" [i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunSpec a m Q X → Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifySpec a m Q X → Γ "full_vivify" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullProbeSpec a m Q X → Func.wp Γ full_probe_body a m Q X :=
  full_probe_wp Γ hIsqrt hSubst hCong hSweep hTrans hPRun hViv

theorem full_eliminate_bridge_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, fullEnterDenseSpec a m Q X → Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubSpec a m Q X → Γ "full_forward_sub" [i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, fullBveVarSpec a m Q X → Γ "full_bve_var" [i64, i32] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorSpec a m Q X → Γ "full_factor" [i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullEliminateSpec a m Q X → Func.wp Γ full_eliminate_body a m Q X :=
  full_eliminate_wp Γ hIsqrt hEnter hFwd hBve hFact hReb

theorem full_preprocess_bridge_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, fullProbeSpec a m Q X → Γ "full_probe" [i64] [i64] a m Q X)
    (hElim : ∀ a m Q X, fullEliminateSpec a m Q X → Γ "full_eliminate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullPreprocessSpec a m Q X → Func.wp Γ full_preprocess_body a m Q X :=
  full_preprocess_wp Γ hProp hProbe hElim

theorem full_simplify_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hProbe : ∀ a m Q X, fullProbeSpec a m Q X → Γ "full_probe" [i64] [i64] a m Q X)
    (hElim : ∀ a m Q X, fullEliminateSpec a m Q X → Γ "full_eliminate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSimplifySpec a m Q X → Func.wp Γ full_simplify_body a m Q X :=
  full_simplify_wp Γ hBt hRed hProbe hElim

theorem full_search_bridge_wp (Γ : Env)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hWarm : ∀ a m Q X, fullWarmupSpec a m Q X → Γ "full_warmup" [i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullSwitchModeSpec a m Q X → Γ "full_switch_mode" [i64] [] a m Q X)
    (hReph : ∀ a m Q X, fullRephaseSpec a m Q X → Γ "full_rephase" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hSimp : ∀ a m Q X, fullSimplifySpec a m Q X → Γ "full_simplify" [i64] [i64] a m Q X)
    (hRdue : ∀ a m Q X, fullRestartDueSpec a m Q X → Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hDec : ∀ a m Q X, fullDecideSpec a m Q X → Γ "full_decide" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSearchSpec a m Q X → Func.wp Γ full_search_body a m Q X :=
  full_search_wp Γ hLucky hWarm hProp hAna hSw hReph hRed hSimp hRdue hRst hDec

theorem kissat_solve_bytes_core_bridge_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesCoreSpec a m Q X → Func.wp Γ kissat_solve_bytes_body a m Q X :=
  kissat_solve_bytes_core_wp Γ hInit hParse hPre hSearch hExt hCheck

theorem kissat_solve_bytes_bridge_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesSpec a m Q X → Func.wp Γ kissat_solve_bytes_body a m Q X :=
  kissat_solve_bytes_wp Γ hInit hParse hPre hSearch hExt hCheck

/-! ## Part 2: Index-verified `SpecEntry.Impl (mkFullEnv mainSpec)` summary (`6` fns) -/

private theorem fullFns_nodup : (fullFns.map Fn.name).Nodup := by
  have hchk := full_acyclic
  simp only [fullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem fullSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((fullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (fullSpecTable mainSpec).map SpecEntry.name = fullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (fullSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]
  exact fullFns_nodup

private theorem mkFullEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (fullSpecTable_nodup mainSpec) (hno xs m Q X h)

/-- Canonical `fullFns` / `fullSpecTable` indices of the `6` top orchestrator functions. -/
def fullBridge9Indices : List Nat :=
  [160, 161, 162, 163, 164, 165]

/-- Index-verified `SpecEntry.Impl (mkFullEnv mainSpec)` summary covering all `6` top orchestrators
(`full_probe`, `full_eliminate`, `full_preprocess`, `full_simplify`, `full_search`,
`kissat_solve_bytes`) for any `mainSpec` strengthening `fullSolveBytesCoreSpec`. -/
theorem full_bridge_9_mk_ok
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ∀ n ∈ fullBridge9Indices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row := by
  let Γ := mkFullEnv mainSpec
  let hCheck := mkFullEnv_row_at (mainSpec := mainSpec) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  let hIsqrt := mkFullEnv_row_at (mainSpec := mainSpec) 8
    ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  let hBt := mkFullEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let hInit := mkFullEnv_row_at (mainSpec := mainSpec) 41
    ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  let hParse := mkFullEnv_row_at (mainSpec := mainSpec) 44
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  let hProp := mkFullEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let hRed := mkFullEnv_row_at (mainSpec := mainSpec) 61
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  let hAna := mkFullEnv_row_at (mainSpec := mainSpec) 82
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  let hDec := mkFullEnv_row_at (mainSpec := mainSpec) 84
    ⟨"full_decide", [i64], [i64], fullDecideSpec, true⟩
  let hWarm := mkFullEnv_row_at (mainSpec := mainSpec) 85
    ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩
  let hReph := mkFullEnv_row_at (mainSpec := mainSpec) 90
    ⟨"full_rephase", [i64], [], fullRephaseSpec, true⟩
  let hSw := mkFullEnv_row_at (mainSpec := mainSpec) 91
    ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
  let hRdue := mkFullEnv_row_at (mainSpec := mainSpec) 92
    ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  let hRst := mkFullEnv_row_at (mainSpec := mainSpec) 93
    ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  let hExt := mkFullEnv_row_at (mainSpec := mainSpec) 96
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  let hLucky := mkFullEnv_row_at (mainSpec := mainSpec) 105
    ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  let hPRun := mkFullEnv_row_at (mainSpec := mainSpec) 111
    ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunSpec, true⟩
  let hTrans := mkFullEnv_row_at (mainSpec := mainSpec) 113
    ⟨"full_transitive", [i64], [i64], fullTransitiveSpec, true⟩
  let hViv := mkFullEnv_row_at (mainSpec := mainSpec) 119
    ⟨"full_vivify", [i64, i64], [i64], fullVivifySpec, true⟩
  let hSubst := mkFullEnv_row_at (mainSpec := mainSpec) 125
    ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  let hEnter := mkFullEnv_row_at (mainSpec := mainSpec) 126
    ⟨"full_enter_dense", [i64], [.bool], fullEnterDenseSpec, true⟩
  let hReb := mkFullEnv_row_at (mainSpec := mainSpec) 127
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  let hCong := mkFullEnv_row_at (mainSpec := mainSpec) 137
    ⟨"full_congruence", [i64], [i64], fullCongruenceSpec, true⟩
  let hSweep := mkFullEnv_row_at (mainSpec := mainSpec) 144
    ⟨"full_sweep_sat", [i64], [i64], fullSweepSatSpec, true⟩
  let hFwd := mkFullEnv_row_at (mainSpec := mainSpec) 147
    ⟨"full_forward_sub", [i64], [i64], fullForwardSubSpec, true⟩
  let hBve := mkFullEnv_row_at (mainSpec := mainSpec) 156
    ⟨"full_bve_var", [i64, i32], [i64], fullBveVarSpec, true⟩
  let hFact := mkFullEnv_row_at (mainSpec := mainSpec) 159
    ⟨"full_factor", [i64], [i64], fullFactorSpec, true⟩
  let hProbe := mkFullEnv_row_at (mainSpec := mainSpec) 160
    ⟨"full_probe", [i64], [i64], fullProbeSpec, true⟩
  let hElim := mkFullEnv_row_at (mainSpec := mainSpec) 161
    ⟨"full_eliminate", [i64], [i64], fullEliminateSpec, true⟩
  let hPre := mkFullEnv_row_at (mainSpec := mainSpec) 162
    ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  let hSimp := mkFullEnv_row_at (mainSpec := mainSpec) 163
    ⟨"full_simplify", [i64], [i64], fullSimplifySpec, true⟩
  let hSearch := mkFullEnv_row_at (mainSpec := mainSpec) 164
    ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  intro n hn
  simp only [fullBridge9Indices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨full_probe, _, rfl, rfl,
      .of (full_probe_bridge_wp Γ hIsqrt hSubst hCong hSweep hTrans hPRun hViv)⟩
  · exact ⟨full_eliminate, _, rfl, rfl,
      .of (full_eliminate_bridge_wp Γ hIsqrt hEnter hFwd hBve hFact hReb)⟩
  · exact ⟨full_preprocess, _, rfl, rfl, .of (full_preprocess_bridge_wp Γ hProp hProbe hElim)⟩
  · exact ⟨full_simplify, _, rfl, rfl, .of (full_simplify_bridge_wp Γ hBt hRed hProbe hElim)⟩
  · exact ⟨full_search, _, rfl, rfl,
      .of (full_search_bridge_wp Γ hLucky hWarm hProp hAna hSw hReph hRed hSimp hRdue hRst hDec)⟩
  · exact ⟨kissat_solve_bytes, _, rfl, rfl,
      .of fun a m Q X h =>
        kissat_solve_bytes_core_bridge_wp Γ hInit hParse hPre hSearch hExt hCheck a m Q X
          (hweaken a m Q X h)⟩

/-- Index-verified `SpecEntry.Impl fullEnv` summary covering all `6` top orchestrators against
`fullSpecTable fullSolveBytesSpec`. -/
theorem full_bridge_9_ok :
    ∀ n ∈ fullBridge9Indices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl fullEnv fn row :=
  full_bridge_9_mk_ok fullSolveBytesSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec)

/-- Index-verified `SpecEntry.Impl (mkFullEnv fullSolveBytesCoreSpec)` summary covering all `6`
top orchestrators against `fullSpecTable fullSolveBytesCoreSpec`. -/
theorem full_bridge_9_core_ok :
    ∀ n ∈ fullBridge9Indices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable fullSolveBytesCoreSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv fullSolveBytesCoreSpec) fn row :=
  full_bridge_9_mk_ok fullSolveBytesCoreSpec (fun _ _ _ _ h => h)

end LeanQbe.T.Examples.Kissat.Full
