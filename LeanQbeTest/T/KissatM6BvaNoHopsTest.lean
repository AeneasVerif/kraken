module

public import LeanQbe.T.Examples.Kissat.FullM6BvaNoHops
public import LeanQbe.T.Examples.Kissat.FullM6BvaNoHopsProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6BvaNoHops
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M6 `FullM6BvaNoHops`

1. Executable `#guard` checks on `m6BvaNoHopsModule` (`1` fn, `0` externs, `0` exits), canonical
   drop-in handle `m6BvaPickCandFn`, `checkAcyclic = true`, `PrintCpp`, `PrintQbe`, and 4-ISA
   `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, callee-free `Func.wp`
   against canonical `FullBvaHeap.fullBvaPickCandSpec`, closed `ModuleOk`, and concrete `Mem 64`
   UNSAT non-vacuity (`XPost := False`, zero SAT proofs).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM6BvaNoHopsTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullM6BvaNoHops
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m6BvaNoHopsFns.length == 1
#guard m6BvaNoHops_fns.length == 1
#guard m6BvaPickCandFn.name == "full_bva_pick_cand"
#guard m6BvaPickCandFn.as == [i64, i32, i32]
#guard m6BvaPickCandFn.rs == [i32]
#guard m6BvaNoHopsModule.checkAcyclic == true
#guard m6BvaNoHopsModule.externs.isEmpty == true
#guard m6BvaNoHopsModule.exits.isEmpty == true
#guard (ppTModule m6BvaNoHopsModule).isOk
#guard (PrintQbe.module m6BvaNoHopsModule).isOk
#guard (ppModule (m6BvaNoHopsFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6BvaNoHopsFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6BvaNoHopsFns.map (Fn.legal .x64AVX2))).isOk
#guard m6BvaNoHopsFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem bva_nh_wf : Func.Wf full_bva_pick_cand_no_hops_body :=
  full_bva_pick_cand_no_hops_wf

theorem bva_nh_fns_wf : ∀ f ∈ m6BvaNoHopsFns, f.Wf :=
  m6BvaNoHopsFns_wf

theorem bva_nh_acyc : m6BvaNoHopsModule.checkAcyclic = true :=
  m6BvaNoHops_acyclic

theorem bva_nh_wp (Γ : Env) :
    ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Func.wp Γ full_bva_pick_cand_no_hops_body args m Q X :=
  m6_bva_pick_cand_no_hops_wp Γ

theorem bva_nh_noExit :
    ∀ f as bs xs m Q X X',
      m6BvaNoHopsEnv f as bs xs m Q X → m6BvaNoHopsEnv f as bs xs m Q X' :=
  m6BvaNoHopsEnv_noExit

theorem bva_nh_tbl : TableImpl m6BvaNoHopsEnv m6BvaNoHopsFns m6BvaNoHopsSpecTable :=
  m6BvaNoHops_tableImpl

theorem bva_nh_mod_ok : ModuleOk m6BvaNoHopsEnv m6BvaNoHopsModule :=
  m6BvaNoHops_moduleOk

theorem bva_nh_nv :
    Func.wp m6BvaNoHopsEnv full_bva_pick_cand_no_hops_body
      (nvOneLitCfg.hdr, 2#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_bva_pick_cand_no_hops

end LeanQbeTest.T.KissatM6BvaNoHopsTest

/-! ## 3. Single-Line `#print axioms` Audit (Standard Axioms) -/

abbrev m6bnh_wf := @LeanQbeTest.T.KissatM6BvaNoHopsTest.bva_nh_wf
abbrev m6bnh_fns_wf := @LeanQbeTest.T.KissatM6BvaNoHopsTest.bva_nh_fns_wf
abbrev m6bnh_acyc := @LeanQbeTest.T.KissatM6BvaNoHopsTest.bva_nh_acyc
abbrev m6bnh_wp := @LeanQbeTest.T.KissatM6BvaNoHopsTest.bva_nh_wp
abbrev m6bnh_noExit := @LeanQbeTest.T.KissatM6BvaNoHopsTest.bva_nh_noExit
abbrev m6bnh_tbl := @LeanQbeTest.T.KissatM6BvaNoHopsTest.bva_nh_tbl
abbrev m6bnh_modOk := @LeanQbeTest.T.KissatM6BvaNoHopsTest.bva_nh_mod_ok
abbrev m6bnh_nv := @LeanQbeTest.T.KissatM6BvaNoHopsTest.bva_nh_nv

#print axioms m6bnh_wf
#print axioms m6bnh_fns_wf
#print axioms m6bnh_acyc
#print axioms m6bnh_wp
#print axioms m6bnh_noExit
#print axioms m6bnh_tbl
#print axioms m6bnh_modOk
#print axioms m6bnh_nv

end
