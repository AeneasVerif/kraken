module

public import LeanQbe.T.Examples.Kissat.FullM7Search
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7Search
meta import LeanQbe.T.Examples.Kissat.FullM7SearchProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Checks, and Axiom Audit for Kissat `M7` Search Parity

1. Executable `#guard` checks on `m7SearchModule` (`15` owned `_m7` functions + `8` canonical
   `FullSpec` externs, `0` exits), `m7SearchSpecTable` (`23` rows), `checkAcyclic = true`,
   `PrintCpp`, `PrintQbe`, and `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX512`, and
   `.x64AVX2`.
2. Root-namespace audit theorems covering `Wf`, `checkAcyclic`, `noExit`, `TableImpl`,
   `ModuleOk`, parametric `Func.wp` + canonical `FullSpec*` drop-in bridges, and concrete `Mem 64`
   UNSAT non-vacuity (`XPost := False`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).

> **Solver Loop Integration Guard**: `full_lucky_late_m7` must run **once** before the main
> solver search loop starts (at root initialization), never inside the inner decision loop.
> Running it inside the inner loop triggers full restarts/backtracking per step.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7SearchTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.FullM7Search

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m7SearchModule.checkAcyclic == true
#guard m7SearchModule.exits.isEmpty
#guard m7Search_fns.length == 15
#guard m7SearchExterns.length == 8
#guard m7SearchSpecTable.length == 23
#guard m7Search_fns.map Fn.name ==
  [ "full_lcg_next_m7", "full_m7_get64", "full_m7_set64", "full_m7_state_init",
    "full_log10_q16_m7", "full_tumble_clause_m7", "full_tumble_clauses_m7", "full_tumble_m7",
    "full_lucky_polar_m7", "full_lucky_late_m7", "full_randec_step_m7", "full_randec_var_m7",
    "full_decide_m7", "full_ema_swap_m7", "full_switch_mode_m7" ]
#guard m7SearchExterns.map Extern.name ==
  [ "full_arena_next", "full_ilog10", "full_heap_down", "full_next_dec_var",
    "full_assign", "full_backtrack", "full_propagate", "full_lucky_scan" ]
#guard (ppTModule m7SearchModule).isOk
#guard (PrintQbe.module m7SearchModule).isOk
#guard (ppModule (m7Search_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7Search_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7Search_fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7Search_fns.map (Fn.legal .x64AVX2))).isOk

end LeanQbeTest.T.KissatM7SearchTest

/-! ## 2. Root-Namespace Audit Theorems & Single-Line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7Search
open Kraken.Bedrock2.Test

theorem m7sr_wf : ∀ f ∈ m7Search_fns, f.Wf :=
  m7Search_fns_wf

theorem m7sr_acyc : m7SearchModule.checkAcyclic = true :=
  m7Search_acyclic

theorem m7sr_tbl_len : m7SearchSpecTable.length = 23 :=
  m7SearchSpecTable_length

theorem m7sr_noExit_tbl : ∀ e ∈ m7SearchSpecTable, e.noExit = true :=
  m7SearchSpecTable_noExit

theorem m7sr_env_noExit :
    ∀ f as bs xs m Q X X',
      m7SearchEnv f as bs xs m Q X → m7SearchEnv f as bs xs m Q X' :=
  m7SearchEnv_noExit

theorem m7sr_tblImpl :
    TableImpl m7SearchEnv m7Search_fns m7SearchSpecTable :=
  m7Search_tableImpl

theorem m7sr_modOk : ModuleOk m7SearchEnv m7SearchModule :=
  m7Search_moduleOk

theorem m7sr_randec_var_wp (Γ : Env)
    (hLcg : EnvSpec Γ "full_lcg_next_m7" m7LcgNextSpec)
    (hInit : EnvSpec Γ "full_m7_state_init" m7StateInitSpec)
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, m7RandecVarSpec a m Q X → Func.wp Γ full_randec_var_m7_body a m Q X :=
  full_randec_var_m7_wp Γ hLcg hInit hGet hSet hLog10

theorem m7sr_randec_dropin (Γ : Env)
    (hLcg : EnvSpec Γ "full_lcg_next_m7" m7LcgNextSpec)
    (hInit : EnvSpec Γ "full_m7_state_init" m7StateInitSpec)
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, Full.fullNextDecVarSpec a m Q X →
      Func.wp Γ full_randec_var_m7_body a m Q X :=
  m7RandecVarFn_dropin_wp Γ hLcg hInit hGet hSet hLog10

theorem m7sr_decide_wp (Γ : Env)
    (hRandec : EnvSpec Γ "full_randec_var_m7" m7RandecVarSpec)
    (hNextDec : EnvSpec Γ "full_next_dec_var" fullNextDecVarSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec) :
    ∀ a m Q X, m7DecideSpec a m Q X → Func.wp Γ full_decide_m7_body a m Q X :=
  full_decide_m7_wp Γ hRandec hNextDec hAssign

theorem m7sr_decide_dropin (Γ : Env)
    (hRandec : EnvSpec Γ "full_randec_var_m7" m7RandecVarSpec)
    (hNextDec : EnvSpec Γ "full_next_dec_var" fullNextDecVarSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec) :
    ∀ a m Q X, Full.fullDecideSpec a m Q X → Func.wp Γ full_decide_m7_body a m Q X :=
  m7DecideFn_dropin_wp Γ hRandec hNextDec hAssign

theorem m7sr_lucky_late_wp (Γ : Env)
    (hPolar : EnvSpec Γ "full_lucky_polar_m7" fullLuckyPolarSpec)
    (hScan : EnvSpec Γ "full_lucky_scan" fullLuckyScanSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec)
    (hBt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hProp : EnvSpec Γ "full_propagate" fullPropagateSpec) :
    ∀ a m Q X, m7LuckyLateSpec a m Q X → Func.wp Γ full_lucky_late_m7_body a m Q X :=
  full_lucky_late_m7_wp Γ hPolar hScan hAssign hBt hProp

/-- Integration guard: invoke `full_lucky_late_m7` once before the search loop, never inside it. -/
theorem m7sr_lucky_dropin (Γ : Env)
    (hPolar : EnvSpec Γ "full_lucky_polar_m7" fullLuckyPolarSpec)
    (hScan : EnvSpec Γ "full_lucky_scan" fullLuckyScanSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec)
    (hBt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hProp : EnvSpec Γ "full_propagate" fullPropagateSpec) :
    ∀ a m Q X, Full.fullLuckySpec a m Q X → Func.wp Γ full_lucky_late_m7_body a m Q X :=
  m7LuckyLateFn_dropin_wp Γ hPolar hScan hAssign hBt hProp

theorem m7sr_switch_dropin (Γ : Env)
    (hIlog : EnvSpec Γ "full_ilog10" fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" fullHeapDownSpec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, Full.fullSwitchModeSpec a m Q X →
      Func.wp Γ full_switch_mode_m7_body a m Q X :=
  m7SwitchModeFn_dropin_wp Γ hIlog hHeapDown hEmaSwap hLog10

theorem m7sr_nv_tumble :
    Func.wp m7SearchEnv full_tumble_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (_, ()) m' => ∃ ar' rng',
        let s' : FullState :=
          { core := { nvOneLitState.core with arena := ar' }
            scratch := { nvOneLitState.scratch with rng_state := rng' } }
        FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        FullArenaPermEq nvOneLitState.core s'.core ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_tumble

theorem m7sr_nv_lucky :
    Func.wp m7SearchEnv full_lucky_late_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s' : FullState,
        s'.LengthsOk nvOneLitCfg ∧ (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        s'.core.fuel.toNat ≤ nvOneLitState.core.fuel.toNat ∧ s'.core.probing = 0#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_lucky_late

theorem m7sr_nv_randec :
    Func.wp m7SearchEnv full_randec_step_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s' : FullState,
        s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        M7StateInitOk s'.scratch.glue_used ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_randec_step

theorem m7sr_nv_decide :
    Func.wp m7SearchEnv full_decide_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s' : FullState,
        FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 0#64 ∨ r = 1#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_decide

theorem m7sr_nv_switch :
    Func.wp m7SearchEnv full_switch_mode_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s' : FullState,
        s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        FullProbeScratchPres nvOneLitState s' ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_switch_mode

#print axioms m7sr_wf
#print axioms m7sr_acyc
#print axioms m7sr_tbl_len
#print axioms m7sr_noExit_tbl
#print axioms m7sr_env_noExit
#print axioms m7sr_tblImpl
#print axioms m7sr_modOk
#print axioms m7sr_randec_var_wp
#print axioms m7sr_randec_dropin
#print axioms m7sr_decide_wp
#print axioms m7sr_decide_dropin
#print axioms m7sr_lucky_late_wp
#print axioms m7sr_lucky_dropin
#print axioms m7sr_switch_dropin
#print axioms m7sr_nv_tumble
#print axioms m7sr_nv_lucky
#print axioms m7sr_nv_randec
#print axioms m7sr_nv_decide
#print axioms m7sr_nv_switch

end AxiomAudit
