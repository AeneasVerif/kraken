module

public import LeanQbe.T.Examples.Kissat.FullM7HotTernary
public import LeanQbe.T.Examples.Kissat.FullM7HotTernaryProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7HotTernary
meta import LeanQbe.T.Examples.Kissat.FullM7HotTernaryProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit (`FullM7HotTernary`)

1. Executable `#guard` checks on `m7HotTernaryModule` (`1` fn, `0` externs, `0` exits),
   drop-in `m7HasTernaryFn` (`"full_has_ternary"`), `checkAcyclic = true`, `PrintCpp`, `PrintQbe`,
   and 4-ISA `Fn.legal` checks (`.aarch64`, `.scalar64`, `.x64AVX2`, `.x64AVX512`).
2. Audit-ready restated headline theorems for `Wf`, `checkAcyclic`, `Full.fullHasTernarySpec`
   `Func.wp`, `m7HotTernaryEnv_noExit`, closed `ModuleOk`, and concrete `Mem 64` UNSAT
   non-vacuity (`XPost := False`, `nvOneLitF0.Unsat`).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7HotTernaryTest

open Std.Sat
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7HotTernary

/-! ## 1. Module Structure, Codegen & 4-ISA Legalization Guards -/

#guard m7HotTernary_fns.length == 1
#guard m7HotTernaryModule.checkAcyclic == true
#guard m7HotTernaryModule.externs.isEmpty == true
#guard m7HotTernaryModule.exits.isEmpty == true
#guard m7HotTernarySpecTable.length == 1
#guard m7HotTernarySpecTable.all (·.noExit) == true
#guard m7HasTernaryFn.name == "full_has_ternary"
#guard m7HasTernaryFn.as == [i64, i32, i32, i32]
#guard m7HasTernaryFn.rs == [.bool]
#guard (ppTModule m7HotTernaryModule).isOk
#guard (PrintQbe.module m7HotTernaryModule).isOk
#guard (ppModule (m7HotTernary_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7HotTernary_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7HotTernary_fns.map (Fn.legal .x64AVX2))).isOk
#guard m7HotTernary_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Restated Headline Soundness, `ModuleOk`, & Non-Vacuity Theorems -/

theorem m7ht_wf : Func.Wf full_has_ternary_m7_body := full_has_ternary_m7_wf
theorem m7ht_fn_wf : m7HasTernaryFn.Wf := m7HasTernaryFn_wf
theorem m7ht_fns : ∀ f ∈ m7HotTernary_fns, f.Wf := m7HotTernary_fns_wf
theorem m7ht_acyc : m7HotTernaryModule.checkAcyclic = true := m7HotTernary_acyclic

theorem m7ht_wp (Γ : Env) :
    ∀ args m Q X, Full.fullHasTernarySpec args m Q X →
      Func.wp Γ full_has_ternary_m7_body args m Q X :=
  full_has_ternary_m7_wp Γ

theorem m7ht_fn_wp (Γ : Env) :
    ∀ args m Q X, Full.fullHasTernarySpec args m Q X →
      Func.wp Γ m7HasTernaryFn.body args m Q X :=
  m7HasTernaryFn_wp Γ

theorem m7ht_sigs :
    m7HotTernarySpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m7HotTernary_fns.map (fun f => (f.name, f.as, f.rs)) :=
  m7HotTernarySpecTable_sigs

theorem m7ht_noex :
    ∀ f as bs xs m Q X X',
      m7HotTernaryEnv f as bs xs m Q X → m7HotTernaryEnv f as bs xs m Q X' :=
  m7HotTernaryEnv_noExit

theorem m7ht_all : AllFns Fn.Wf m7HotTernaryModule.fns := m7HotTernary_allFns_wf

theorem m7ht_tbl :
    TableImpl m7HotTernaryEnv m7HotTernaryModule.fns m7HotTernarySpecTable :=
  m7HotTernary_tableImpl

theorem m7ht_mod : ModuleOk m7HotTernaryEnv m7HotTernaryModule := m7HotTernary_moduleOk

theorem m7ht_nv :
    Func.wp m7HotTernaryEnv full_has_ternary_m7_body
      (nvOneLitCfg.hdr, 0#32, 0#32, 0#32, ()) nvOneLitMem
      (fun (ok, ()) _ => nvOneLitF0.Unsat ∧ (ok = true → (0#32 : BitVec 32) ≠ 0#32 → False))
      (fun _ _ _ _ => False) :=
  nv_m7_has_ternary

end LeanQbeTest.T.KissatM7HotTernaryTest

/-! ## 3. Single-Line `< 115c` `#print axioms` Audit (`std3`) -/

abbrev m7ht_a_wf := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_wf
abbrev m7ht_a_fwf := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_fn_wf
abbrev m7ht_a_fns := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_fns
abbrev m7ht_a_acy := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_acyc
abbrev m7ht_a_wp := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_wp
abbrev m7ht_a_fwp := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_fn_wp
abbrev m7ht_a_sig := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_sigs
abbrev m7ht_a_nex := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_noex
abbrev m7ht_a_all := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_all
abbrev m7ht_a_tbl := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_tbl
abbrev m7ht_a_mod := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_mod
abbrev m7ht_a_nv := @LeanQbeTest.T.KissatM7HotTernaryTest.m7ht_nv

#print axioms m7ht_a_wf
#print axioms m7ht_a_fwf
#print axioms m7ht_a_fns
#print axioms m7ht_a_acy
#print axioms m7ht_a_wp
#print axioms m7ht_a_fwp
#print axioms m7ht_a_sig
#print axioms m7ht_a_nex
#print axioms m7ht_a_all
#print axioms m7ht_a_tbl
#print axioms m7ht_a_mod
#print axioms m7ht_a_nv
