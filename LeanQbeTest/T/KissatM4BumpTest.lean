module

public import LeanQbe.T.Examples.Kissat.FullM4Bump
public import LeanQbe.T.Examples.Kissat.FullM4BumpProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM4Bump
meta import LeanQbe.T.Examples.Kissat.FullM4BumpProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, Backend Compilation Guards, and Axiom Audit for Kissat M4 (`FullM4Bump`)

1. Executable `#guard` checks on `m4BumpModule` (`1` fn + `2` externs, `0` exits),
   `checkAcyclic = true`, `m4BumpSpecTable` (`3` rows), `PrintCpp`, `PrintQbe`, and `Fn.legal`
   across `aarch64`, `scalar64`, and `x64AVX2`.
2. Audit-ready restated headline theorems for `m4Bump_fns_wf`, `m4BumpVarFn_wf`, `m4Bump_acyclic`,
   parametric `full_bump_var_m4_wp`, `m4Bump_moduleOk`, and concrete `Mem 64` UNSAT non-vacuity
   `nv_m4_bump_var` (`XPost := False`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM4BumpTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Bump
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m4BumpModule.checkAcyclic == true
#guard m4BumpModule.exits.isEmpty
#guard m4Bump_fns.length == 1
#guard m4BumpExterns.length == 2
#guard m4BumpSpecTable.length == 3
#guard m4BumpVarFn.name == "full_bump_var"
#guard (ppTModule m4BumpModule).isOk
#guard (PrintQbe.module m4BumpModule).isOk
#guard (ppModule (m4Bump_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m4Bump_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m4Bump_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

/-- Every function in `m4Bump_fns` (`full_bump_var_m4`) is well-formed. -/
theorem m4g_wf : ∀ f ∈ m4Bump_fns, f.Wf :=
  m4Bump_fns_wf

/-- Spliced replacement `m4BumpVarFn` (`"full_bump_var"`) is well-formed. -/
theorem m4g_fn_wf : m4BumpVarFn.Wf :=
  m4BumpVarFn_wf

/-- Standalone M4 bump module `m4BumpModule` passes `checkAcyclic = true`. -/
theorem m4g_acyc : m4BumpModule.checkAcyclic = true :=
  m4Bump_acyclic

/-- Mode-guarded `full_bump_var_m4` satisfies `Full.fullBumpVarSpec` parametrically in `Γ`. -/
theorem m4g_bump_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hRes : ∀ a m Q X, fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpVarSpec a m Q X → Func.wp Γ full_bump_var_m4_body a m Q X :=
  full_bump_var_m4_wp Γ hUp hRes

/-- Closed `3`-row `ModuleOk` certifying `m4BumpModule` under `m4BumpEnv`. -/
theorem m4g_mod_ok : ModuleOk m4BumpEnv m4BumpModule :=
  m4Bump_moduleOk

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bump_var_m4`. -/
theorem m4g_nv_bump :
    Func.wp m4BumpEnv full_bump_var_m4_body (nvOneLitCfg.hdr, 0#32, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_bump_var

end AuditSpec

end LeanQbeTest.T.KissatM4BumpTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m4g_a_wf := @LeanQbeTest.T.KissatM4BumpTest.m4g_wf
abbrev m4g_a_fn_wf := @LeanQbeTest.T.KissatM4BumpTest.m4g_fn_wf
abbrev m4g_a_acyc := @LeanQbeTest.T.KissatM4BumpTest.m4g_acyc
abbrev m4g_a_bump_wp := @LeanQbeTest.T.KissatM4BumpTest.m4g_bump_wp
abbrev m4g_a_mod_ok := @LeanQbeTest.T.KissatM4BumpTest.m4g_mod_ok
abbrev m4g_a_nv_bump := @LeanQbeTest.T.KissatM4BumpTest.m4g_nv_bump

#print axioms m4g_a_wf
#print axioms m4g_a_fn_wf
#print axioms m4g_a_acyc
#print axioms m4g_a_bump_wp
#print axioms m4g_a_mod_ok
#print axioms m4g_a_nv_bump
