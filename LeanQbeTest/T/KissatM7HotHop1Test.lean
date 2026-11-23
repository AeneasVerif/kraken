module

public import LeanQbe.T.Examples.Kissat.FullM7HotHop1
public import LeanQbe.T.Examples.Kissat.FullM7HotHop1Proof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7HotHop1
meta import LeanQbe.T.Examples.Kissat.FullM7HotHop1Proof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M7 `FullM7HotHop1`

1. Executable `#guard` checks on `m7HotHop1Module` (`2` fns, `0` externs, `0` exits), canonical
   drop-in handles `m7Hop1Fn` (`"full_bva_hop1"`) and `m7Hop2Fn` (`"full_bva_hop2"`),
   `checkAcyclic = true`, `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`,
   `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, parametric `Func.wp`
   against canonical `fullBvaHop1Spec` / `fullBvaHop2Spec`, `m7HotHop1Env_noExit`, closed
   `ModuleOk`, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, zero SAT proofs).
3. Single-line `< 115`-col `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7HotHop1Test

open Std.Sat
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullM7HotHop1
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m7HotHop1Fns.length == 2
#guard m7HotHop1_fns.length == 2
#guard m7Hop1Fn.name == "full_bva_hop1"
#guard m7Hop1Fn.as == [i64, i32, i32]
#guard m7Hop1Fn.rs == [i64]
#guard m7Hop2Fn.name == "full_bva_hop2"
#guard m7Hop2Fn.as == [i64, i32, i32]
#guard m7Hop2Fn.rs == [i64]
#guard m7HotHop1Module.checkAcyclic == true
#guard m7HotHop1Module.externs.isEmpty == true
#guard m7HotHop1Module.exits.isEmpty == true
#guard m7HotHop1SpecTable.length == 2
#guard m7HotHop1SpecTable.all (·.noExit) == true
#guard (ppTModule m7HotHop1Module).isOk
#guard (PrintQbe.module m7HotHop1Module).isOk
#guard (ppModule (m7HotHop1Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7HotHop1Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7HotHop1Fns.map (Fn.legal .x64AVX2))).isOk
#guard m7HotHop1Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem m7_hop1_wf : Func.Wf full_bva_hop1_m7_body :=
  full_bva_hop1_m7_wf

theorem m7_hop2_wf : Func.Wf full_bva_hop2_m7_body :=
  full_bva_hop2_m7_wf

theorem m7_fns_wf : ∀ f ∈ m7HotHop1Fns, f.Wf :=
  m7HotHop1Fns_wf

theorem m7_acyc : m7HotHop1Module.checkAcyclic = true :=
  m7HotHop1_acyclic

theorem m7_hop1_wp (Γ : Env) :
    ∀ a m Q X, fullBvaHop1Spec a m Q X → Func.wp Γ m7Hop1Fn.body a m Q X :=
  m7Hop1Fn_wp Γ

theorem m7_hop2_wp (Γ : Env)
    (hHop1 : ∀ a m Q X, fullBvaHop1Spec a m Q X →
      Γ "full_bva_hop1" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullBvaHop2Spec a m Q X → Func.wp Γ m7Hop2Fn.body a m Q X :=
  m7Hop2Fn_wp Γ hHop1

theorem m7_noExit :
    ∀ f as bs xs m Q X X',
      m7HotHop1Env f as bs xs m Q X → m7HotHop1Env f as bs xs m Q X' :=
  m7HotHop1Env_noExit

theorem m7_tbl : TableImpl m7HotHop1Env m7HotHop1Fns m7HotHop1SpecTable :=
  m7HotHop1_tableImpl

theorem m7_mod_ok : ModuleOk m7HotHop1Env m7HotHop1Module :=
  m7HotHop1_moduleOk

theorem m7_nv_hop1 :
    Func.wp m7HotHop1Env full_bva_hop1_m7_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_bva_hop1

theorem m7_nv_hop2 :
    Func.wp m7HotHop1Env full_bva_hop2_m7_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_bva_hop2

end LeanQbeTest.T.KissatM7HotHop1Test

/-! ## 3. Single-Line `#print axioms` Audit (`std3` Only) -/

abbrev m7hh_hop1_wf := @LeanQbeTest.T.KissatM7HotHop1Test.m7_hop1_wf
abbrev m7hh_hop2_wf := @LeanQbeTest.T.KissatM7HotHop1Test.m7_hop2_wf
abbrev m7hh_fns_wf := @LeanQbeTest.T.KissatM7HotHop1Test.m7_fns_wf
abbrev m7hh_acyc := @LeanQbeTest.T.KissatM7HotHop1Test.m7_acyc
abbrev m7hh_hop1_wp := @LeanQbeTest.T.KissatM7HotHop1Test.m7_hop1_wp
abbrev m7hh_hop2_wp := @LeanQbeTest.T.KissatM7HotHop1Test.m7_hop2_wp
abbrev m7hh_noExit := @LeanQbeTest.T.KissatM7HotHop1Test.m7_noExit
abbrev m7hh_tbl := @LeanQbeTest.T.KissatM7HotHop1Test.m7_tbl
abbrev m7hh_modOk := @LeanQbeTest.T.KissatM7HotHop1Test.m7_mod_ok
abbrev m7hh_nv1 := @LeanQbeTest.T.KissatM7HotHop1Test.m7_nv_hop1
abbrev m7hh_nv2 := @LeanQbeTest.T.KissatM7HotHop1Test.m7_nv_hop2

#print axioms m7hh_hop1_wf
#print axioms m7hh_hop2_wf
#print axioms m7hh_fns_wf
#print axioms m7hh_acyc
#print axioms m7hh_hop1_wp
#print axioms m7hh_hop2_wp
#print axioms m7hh_noExit
#print axioms m7hh_tbl
#print axioms m7hh_modOk
#print axioms m7hh_nv1
#print axioms m7hh_nv2

end
