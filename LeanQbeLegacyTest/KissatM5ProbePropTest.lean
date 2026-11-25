module

public import LeanQbe.T.Examples.Kissat.FullM5ProbePropProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5ProbeProp
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification and Axiom Audit for Kissat M5 Probing Propagation (`FullM5ProbeProp`)

1. Executable `#guard` checks on `m5ProbeProp_fns` (`1` fn: `full_probe_prop_lit_m5`), signature
   parity, `PrintCpp`, `PrintQbe`, and `Legal` across `.aarch64`, `.scalar64`, `.x64AVX2`.
2. Direct `Func.Wf` + `Func.wp` verification against canonical `Full.fullProbePropLitSpec`.
3. Closed `ModuleOk` (`m5ProbeProp_moduleOk`) and `Mem 64` UNSAT non-vacuity (`XPost := False`).
4. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeLegacyTest.KissatM5ProbePropTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full (fullProbePropLitSpec fullFindReplSpec fullWatchPushSpec
  fullHbrDomSpec fullAssignLvlSpec)
open LeanQbe.T.Examples.Kissat.FullM5ProbeProp

#guard m5ProbeProp_fns.length == 1
#guard full_probe_prop_lit_m5.name == "full_probe_prop_lit_m5"
#guard full_probe_prop_lit_m5.as == [i64, i32]
#guard full_probe_prop_lit_m5.rs == [Ty.bool]
#guard m5ProbePropModule.checkAcyclic == true
#guard (ppTModule m5ProbePropModule).isOk
#guard (PrintQbe.module m5ProbePropModule).isOk
#guard (ppModule (m5ProbeProp_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5ProbeProp_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5ProbeProp_fns.map (Fn.legal .x64AVX2))).isOk

theorem full_probe_prop_lit_m5_spec_ok (Γ : Env)
    (hFindRepl : ∀ a m Q X, fullFindReplSpec a m Q X →
      Γ "full_find_repl" [i64, i64] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hHbrDom : ∀ a m Q X, fullHbrDomSpec a m Q X →
      Γ "full_hbr_dom" [i64, i32, i32] [i32] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullProbePropLitSpec a m Q X →
      Func.wp Γ full_probe_prop_lit_m5_body a m Q X :=
  full_probe_prop_lit_m5_wp Γ hFindRepl hWatchPush hHbrDom hAssignLvl

theorem nv_m5_probe_prop_sound_ok :
    Func.wp m5ProbePropEnv full_probe_prop_lit_m5_body (FastCore.nvFastPropCfg.hdr, 0#32, ())
      nvProbePropMem
      (fun (ok, ()) m' =>
        (ok = true ∨ ok = false) ∧ Full.nvOneLitF0.Unsat ∧
        ∃ s', (Full.FullMem FastCore.nvFastPropCfg s' ⋆ Std.ExtHashMap.emp) m')
      (fun _ _ _ _ => False) :=
  nv_m5_probe_prop_sound

end LeanQbeLegacyTest.KissatM5ProbePropTest

abbrev m5pp_wf := @LeanQbe.T.Examples.Kissat.FullM5ProbeProp.full_probe_prop_lit_m5_wf
abbrev m5pp_fns_wf := @LeanQbe.T.Examples.Kissat.FullM5ProbeProp.m5ProbeProp_fns_wf
abbrev m5pp_acyc := @LeanQbe.T.Examples.Kissat.FullM5ProbeProp.m5ProbeProp_acyclic
abbrev m5pp_wp := @LeanQbe.T.Examples.Kissat.FullM5ProbeProp.full_probe_prop_lit_m5_wp
abbrev m5pp_mod_ok := @LeanQbe.T.Examples.Kissat.FullM5ProbeProp.m5ProbeProp_moduleOk
abbrev m5pp_spec_ok := @LeanQbeLegacyTest.KissatM5ProbePropTest.full_probe_prop_lit_m5_spec_ok
abbrev m5pp_nv_ok := @LeanQbeLegacyTest.KissatM5ProbePropTest.nv_m5_probe_prop_sound_ok

#print axioms m5pp_wf
#print axioms m5pp_fns_wf
#print axioms m5pp_acyc
#print axioms m5pp_wp
#print axioms m5pp_mod_ok
#print axioms m5pp_spec_ok
#print axioms m5pp_nv_ok
