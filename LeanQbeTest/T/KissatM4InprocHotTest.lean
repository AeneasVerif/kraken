module

public import LeanQbe.T.Examples.Kissat.FullM4InprocHotProof
meta import LeanQbe.T.Examples.Kissat.FullM4InprocHotProof

/-!
# Verification, Non-Vacuity, and Axiom Audit for Kissat M4 Inprocessing (`FullM4InprocHot`)

1. Executable `#guard` checks on `m4InprocHot_fns` (`3` fns), `m4InprocHotModule.checkAcyclic`,
   `m4InprocHotSpecTable`, canonical `FullM4` / `FullM3` `Fn` wrappers, and `nvM4Cfg` bounds.
2. Concrete `Mem 64` `Func.wp` sanity check (`nv_test_wstack_defrag`, `XPost := False`,
   `42716`-byte image under closed `m4InprocHotEnv`).
3. Single-line `#print axioms` audit on all exported `FullM4InprocHot` soundness,
   `ModuleOk`, and concrete non-vacuity theorems (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM4InprocHotTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM4InprocHot

/-! ## 1. Executable `#guard` checks -/

#guard m4InprocHot_fns.length == 3
#guard m4InprocHotModule.checkAcyclic == true
#guard m4InprocHotSpecTable.length == 3
#guard m4HasTernaryFn.name == "full_has_ternary"
#guard m4KittenInitFn.name == "full_kitten_init"
#guard m4WstackDefragFn.name == "full_wstack_defrag"
#guard nvM4Cfg.avail == 42716

/-! ## 2. Source-level `Func.wp` check (`XPost := False`, closed `m4InprocHotEnv`) -/

theorem nv_test_wstack_defrag :
    Func.wp m4InprocHotEnv full_wstack_defrag_m4_body (nvM4Cfg.hdr, ()) nvM4Mem
      (fun _ _ => True) (fun _ _ _ _ => False) :=
  nv_m4_wstack_defrag

/-! ## 3. Single-line `#print axioms` audit -/

theorem m4ih_wf0 : Func.Wf full_has_ternary_m4_body := full_has_ternary_m4_wf
theorem m4ih_wf1 : Func.Wf full_kitten_init_m4_body := full_kitten_init_m4_wf
theorem m4ih_wf2 : Func.Wf full_wstack_defrag_m4_body := full_wstack_defrag_m4_wf
theorem m4ih_fns : ∀ f ∈ m4InprocHot_fns, f.Wf := m4InprocHot_fns_wf
theorem m4ih_acyc : m4InprocHotModule.checkAcyclic = true := m4InprocHot_acyclic
theorem m4ih_wp0 (Γ : Env) :
    ∀ args m Q X, Full.fullHasTernarySpec args m Q X →
      Func.wp Γ full_has_ternary_m4_body args m Q X := full_has_ternary_m4_wp Γ
theorem m4ih_wp1 (Γ : Env) :
    ∀ a m Q X, Full.fullKittenInitSpec a m Q X →
      Func.wp Γ full_kitten_init_m4_body a m Q X := full_kitten_init_m4_wp Γ
theorem m4ih_wp2 (Γ : Env) :
    ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Func.wp Γ full_wstack_defrag_m4_body a m Q X := full_wstack_defrag_m4_wp Γ
theorem m4ih_sigs :
    m4InprocHotSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m4InprocHot_fns.map (fun f => (f.name, f.as, f.rs)) := m4InprocHotSpecTable_sigs
theorem m4ih_noex :
    ∀ f as bs xs m Q X X',
      m4InprocHotEnv f as bs xs m Q X →
      m4InprocHotEnv f as bs xs m Q X' := m4InprocHotEnv_noExit
theorem m4ih_all : AllFns Fn.Wf m4InprocHotModule.fns := m4InprocHot_allFns_wf
theorem m4ih_tbl :
    TableImpl m4InprocHotEnv m4InprocHotModule.fns m4InprocHotSpecTable :=
  m4InprocHot_tableImpl
theorem m4ih_mod : ModuleOk m4InprocHotEnv m4InprocHotModule := m4InprocHot_moduleOk
theorem m4ih_len : nvM4State.LengthsOk nvM4Cfg := nvM4State_lengths
theorem m4ih_mem : Full.FullMem nvM4Cfg nvM4State nvM4Mem := nvM4Mem_ok
theorem m4ih_nv0 :
    Func.wp m4InprocHotEnv full_has_ternary_m4_body (nvM4Cfg.hdr, 0#32, 0#32, 0#32, ()) nvM4Mem
      (fun (ok, ()) _ => ok = true → (0#32 : BitVec 32) ≠ 0#32 → False)
      (fun _ _ _ _ => False) := nv_m4_has_ternary
theorem m4ih_nv1 :
    Func.wp m4InprocHotEnv full_kitten_init_m4_body (nvM4Cfg.hdr, 1#32, 0#32, ()) nvM4Mem
      (fun _ _ => True) (fun _ _ _ _ => False) := nv_m4_kitten_init
theorem m4ih_nv2 :
    Func.wp m4InprocHotEnv full_wstack_defrag_m4_body (nvM4Cfg.hdr, ()) nvM4Mem
      (fun _ _ => True) (fun _ _ _ _ => False) := nv_m4_wstack_defrag
theorem m4ih_nvt :
    Func.wp m4InprocHotEnv full_wstack_defrag_m4_body (nvM4Cfg.hdr, ()) nvM4Mem
      (fun _ _ => True) (fun _ _ _ _ => False) := nv_test_wstack_defrag

#print axioms m4ih_wf0
#print axioms m4ih_wf1
#print axioms m4ih_wf2
#print axioms m4ih_fns
#print axioms m4ih_acyc
#print axioms m4ih_wp0
#print axioms m4ih_wp1
#print axioms m4ih_wp2
#print axioms m4ih_sigs
#print axioms m4ih_noex
#print axioms m4ih_all
#print axioms m4ih_tbl
#print axioms m4ih_mod
#print axioms m4ih_len
#print axioms m4ih_mem
#print axioms m4ih_nv0
#print axioms m4ih_nv1
#print axioms m4ih_nv2
#print axioms m4ih_nvt

end LeanQbeTest.T.KissatM4InprocHotTest
