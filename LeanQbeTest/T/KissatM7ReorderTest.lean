module

public import LeanQbe.T.Examples.Kissat.FullM7Reorder
public import LeanQbe.T.Examples.Kissat.FullM7ReorderProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7Reorder
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M7 `FullM7Reorder`

1. Executable `#guard` checks on `m7ReorderModule` (`3` fns, `1` extern `full_arena_next`,
   `0` exits), drop-in handle `m7ReorderQueueFn`, `checkAcyclic = true`, `PrintCpp`, `PrintQbe`,
   and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, `Func.wp` against
   canonical `FullM4Ternary.fullReorderQueueSpec`, `m7ReorderEnv_noExit`, closed `ModuleOk`, and
   concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, zero SAT proofs).
3. Single-line `< 115`-col `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7ReorderTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Ternary
open LeanQbe.T.Examples.Kissat.FullM7Reorder
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m7ReorderFns.length == 3
#guard m7_reorder_fns.length == 3
#guard m7ReorderQueueFn.name == "full_reorder_queue"
#guard m7ReorderQueueFn.as == [i64]
#guard m7ReorderQueueFn.rs == [i64]
#guard m7ReorderModule.checkAcyclic == true
#guard m7ReorderExterns.length == 1
#guard m7ReorderModule.externs.length == 1
#guard m7ReorderModule.exits.isEmpty == true
#guard (ppTModule m7ReorderModule).isOk
#guard (PrintQbe.module m7ReorderModule).isOk
#guard (ppModule (m7ReorderFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7ReorderFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7ReorderFns.map (Fn.legal .x64AVX2))).isOk
#guard m7ReorderFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem m7_wf_weight : Func.Wf full_reorder_weight_m7_body :=
  full_reorder_weight_m7_wf

theorem m7_wf_sift : Func.Wf full_reorder_sift_m7_body :=
  full_reorder_sift_m7_wf

theorem m7_wf_queue : Func.Wf full_reorder_queue_m7_body :=
  full_reorder_queue_m7_wf

theorem m7_fns_wf : ∀ f ∈ m7ReorderFns, f.Wf :=
  m7ReorderFns_wf

theorem m7_acyc : m7ReorderModule.checkAcyclic = true :=
  m7Reorder_acyclic

theorem m7_queue_wp (Γ : Env)
    (hWeight : EnvSpec Γ "full_reorder_weight_m7" m7ReorderWeightSpec)
    (hArenaNext : EnvSpec Γ "full_arena_next" fullArenaNextSpec)
    (hSift : EnvSpec Γ "full_reorder_sift_m7" m7ReorderSiftSpec) :
    ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Func.wp Γ full_reorder_queue_m7_body a m Q X :=
  full_reorder_queue_m7_wp Γ hWeight hArenaNext hSift

theorem m7_queueFn_wp :
    ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Func.wp m7ReorderEnv m7ReorderQueueFn.body a m Q X :=
  m7ReorderQueueFn_wp

theorem m7_noExit :
    ∀ f as bs xs m Q X X',
      m7ReorderEnv f as bs xs m Q X → m7ReorderEnv f as bs xs m Q X' :=
  m7ReorderEnv_noExit

theorem m7_tbl : TableImpl m7ReorderEnv m7ReorderFns m7ReorderSpecTable :=
  m7Reorder_tableImpl

theorem m7_mod_ok : ModuleOk m7ReorderEnv m7ReorderModule :=
  m7Reorder_moduleOk

theorem m7_nv :
    Func.wp m7ReorderEnv m7ReorderQueueFn.body (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem
      (fun _ m' => ∃ s' : FullState,
        PreservesCoreSlice FullState.core nvM4TernaryState s' ∧
        s'.LengthsOk nvM4TernaryCfg ∧
        FullExtScratchPres nvM4TernaryState s' ∧
        FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_reorder_queue _ (fun _ s' _ hc hl he hm => ⟨s', hc, hl, he, hm⟩)

end LeanQbeTest.T.KissatM7ReorderTest

/-! ## 3. Single-Line `#print axioms` Audit (`std3` Only) -/

abbrev m7r_wf_weight := @LeanQbeTest.T.KissatM7ReorderTest.m7_wf_weight
abbrev m7r_wf_sift := @LeanQbeTest.T.KissatM7ReorderTest.m7_wf_sift
abbrev m7r_wf_queue := @LeanQbeTest.T.KissatM7ReorderTest.m7_wf_queue
abbrev m7r_fns_wf := @LeanQbeTest.T.KissatM7ReorderTest.m7_fns_wf
abbrev m7r_acyc := @LeanQbeTest.T.KissatM7ReorderTest.m7_acyc
abbrev m7r_queue_wp := @LeanQbeTest.T.KissatM7ReorderTest.m7_queue_wp
abbrev m7r_queueFn_wp := @LeanQbeTest.T.KissatM7ReorderTest.m7_queueFn_wp
abbrev m7r_noExit := @LeanQbeTest.T.KissatM7ReorderTest.m7_noExit
abbrev m7r_tbl := @LeanQbeTest.T.KissatM7ReorderTest.m7_tbl
abbrev m7r_modOk := @LeanQbeTest.T.KissatM7ReorderTest.m7_mod_ok
abbrev m7r_nv := @LeanQbeTest.T.KissatM7ReorderTest.m7_nv

#print axioms m7r_wf_weight
#print axioms m7r_wf_sift
#print axioms m7r_wf_queue
#print axioms m7r_fns_wf
#print axioms m7r_acyc
#print axioms m7r_queue_wp
#print axioms m7r_queueFn_wp
#print axioms m7r_noExit
#print axioms m7r_tbl
#print axioms m7r_modOk
#print axioms m7r_nv

end
