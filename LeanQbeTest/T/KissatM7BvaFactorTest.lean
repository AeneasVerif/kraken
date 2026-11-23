module

public import LeanQbe.T.Examples.Kissat.FullM7BvaFactor
public import LeanQbe.T.Examples.Kissat.FullM7BvaFactorProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7BvaFactor
meta import LeanQbe.T.Examples.Kissat.FullM7BvaFactorProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M7 (`FullM7BvaFactor`)

1. Executable `#guard` checks on `m7BvaFactorModule` (`3` fns, `6` externs, `0` exits),
   `m7BvaFullModule` (`270` fns, `0` externs, `0` exits), `PrintCpp`, `PrintQbe`, and 4-ISA
   `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, parametric `Func.wp`
   contracts, closed standalone `m7BvaFactor_moduleOk`, concrete `Mem 64` UNSAT non-vacuity
   (`XPost := False`), and `270`-fn spliced `FullM5` compatibility (`m7BvaFull_acyclic`,
   `m7BvaFull_fns_wf`, `m7BvaFull_moduleOk_of`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7BvaFactorTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullM7BvaFactor
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m7BvaFactorFns.length == 3
#guard m7BvaFactor_fns.length == 3
#guard m7InitFreshVarFn.name == "full_init_fresh_var"
#guard m7BvaTryLitFn.name == "full_bva_try_lit"
#guard m7FactorFn.name == "full_factor"
#guard m7BvaFactorModule.checkAcyclic == true
#guard m7BvaFactorModule.externs.length == 6
#guard m7BvaFactorModule.exits.isEmpty == true
#guard (ppTModule m7BvaFactorModule).isOk
#guard (PrintQbe.module m7BvaFactorModule).isOk
#guard (ppModule (m7BvaFactorFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7BvaFactorFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7BvaFactorFns.map (Fn.legal .x64AVX2))).isOk
#guard m7BvaFactorFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m7BvaFullFns.length == 270
#guard m7BvaFullModule.checkAcyclic == true
#guard m7BvaFullModule.externs.isEmpty == true
#guard m7BvaFullModule.exits.isEmpty == true

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem init_wf : Func.Wf full_init_fresh_var_m7_body :=
  full_init_fresh_var_m7_wf

theorem trylit_wf : Func.Wf full_bva_try_lit_m7_body :=
  full_bva_try_lit_m7_wf

theorem factor_wf : Func.Wf full_factor_m7_body :=
  full_factor_m7_wf

theorem fns_wf : ∀ f ∈ m7BvaFactorFns, f.Wf :=
  m7BvaFactorFns_wf

theorem mod_acyc : m7BvaFactorModule.checkAcyclic = true :=
  m7BvaFactor_acyclic

theorem init_wp (Γ : Env) :
    ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Func.wp Γ full_init_fresh_var_m7_body args m Q X :=
  full_init_fresh_var_m7_heap_wp Γ

theorem trylit_wp (Γ : Env)
    (hScan : ∀ args m Q X, FullM4Bva.m4BvaScanCandsSpec args m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] args m Q X)
    (hPick : ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] args m Q X)
    (hFilter : ∀ args m Q X, FullM4Bva.m4BvaFilterRowSpec args m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] args m Q X)
    (hCommit : ∀ args m Q X, FullM4Bva.m4BvaCommitSpec args m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullBvaTryLitHeapSpec args m Q X →
      Func.wp Γ full_bva_try_lit_m7_body args m Q X :=
  full_bva_try_lit_m7_wp Γ hScan hPick hFilter hCommit

theorem factor_wp (Γ : Env)
    (hUp : ∀ args m Q X, fullFheapUpSpec args m Q X →
      Γ "full_fheap_up" [i64, i64, i64, i32] [] args m Q X)
    (hDown : ∀ args m Q X, fullFheapDownSpec args m Q X →
      Γ "full_fheap_down" [i64, i64, i64, i32, i32] [] args m Q X)
    (hTryLit : ∀ args m Q X, fullBvaTryLitHeapSpec args m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullFactorHeapSpec args m Q X →
      Func.wp Γ full_factor_m7_body args m Q X :=
  full_factor_m7_wp Γ hUp hDown hTryLit

theorem env_noExit :
    ∀ f as bs xs m Q X X',
      m7BvaFactorEnv f as bs xs m Q X → m7BvaFactorEnv f as bs xs m Q X' :=
  m7BvaFactorEnv_noExit

theorem mod_ok : ModuleOk m7BvaFactorEnv m7BvaFactorModule :=
  m7BvaFactor_moduleOk

theorem nv_init :
    Func.wp m7BvaFactorEnv full_init_fresh_var_m7_body
      (nvOneLitCfg.hdr, 0#32, ()) nvBvaDenseMem
      (fun () m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ s'.core.vals[0]?.getD 1#8 = 0#8 ∧
        s'.core.vals[1]?.getD 1#8 = 0#8 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_init_fresh_var

theorem nv_trylit :
    Func.wp m7BvaFactorEnv full_bva_try_lit_m7_body
      (nvOneLitCfg.hdr, 0#32, 1#64, ()) nvBvaDenseMem
      (fun (_ok, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_bva_try_lit

theorem nv_factor :
    Func.wp m7BvaFactorEnv full_factor_m7_body
      (nvOneLitCfg.hdr, 10#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ r = 1#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_factor

theorem full_len : m7BvaFullFns.length = 270 :=
  m7BvaFullFns_length

theorem full_acyc : m7BvaFullModule.checkAcyclic = true :=
  m7BvaFull_acyclic

theorem full_wf : ∀ f ∈ m7BvaFullFns, f.Wf :=
  m7BvaFull_fns_wf

theorem full_mod_of (Γ : Env)
    (hM5 : ∀ fn ∈ FullM5.m5Fns, ∀ xs m Q X,
      Γ fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X)
    (hScan : ∀ a m' Q' X', FullM4Bva.m4BvaScanCandsSpec a m' Q' X' →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m' Q' X')
    (hPick : ∀ a m' Q' X', fullBvaPickCandSpec a m' Q' X' →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m' Q' X')
    (hFilter : ∀ a m' Q' X', FullM4Bva.m4BvaFilterRowSpec a m' Q' X' →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m' Q' X')
    (hCommit : ∀ a m' Q' X', FullM4Bva.m4BvaCommitSpec a m' Q' X' →
      Γ "full_bva_commit" [i64, i32] [.bool] a m' Q' X')
    (hTryLit : ∀ a m' Q' X', fullBvaTryLitHeapSpec a m' Q' X' →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m' Q' X')
    (hUp : ∀ a m' Q' X', fullFheapUpSpec a m' Q' X' →
      Γ "full_fheap_up" [i64, i64, i64, i32] [] a m' Q' X')
    (hDown : ∀ a m' Q' X', fullFheapDownSpec a m' Q' X' →
      Γ "full_fheap_down" [i64, i64, i64, i32, i32] [] a m' Q' X')
    (hElimInit : ∀ xs m Q X, Γ "full_init_fresh_var" [i64, i32] [] xs m Q X →
      fullInitFreshVarHeapSpec xs m Q (fun _ _ _ _ => False))
    (hElimTry : ∀ xs m Q X, Γ "full_bva_try_lit" [i64, i32, i64] [.bool] xs m Q X →
      fullBvaTryLitHeapSpec xs m Q (fun _ _ _ _ => False))
    (hElimFac : ∀ xs m Q X, Γ "full_factor" [i64, i64] [i64] xs m Q X →
      fullFactorHeapSpec xs m Q (fun _ _ _ _ => False)) :
    ModuleOk Γ m7BvaFullModule :=
  m7BvaFull_moduleOk_of Γ hM5 hScan hPick hFilter hCommit hTryLit hUp hDown
    hElimInit hElimTry hElimFac

end LeanQbeTest.T.KissatM7BvaFactorTest

/-! ## 3. Single-Line `#print axioms` Audit (Standard Axioms) -/

abbrev m7bf_init_wf := @LeanQbeTest.T.KissatM7BvaFactorTest.init_wf
abbrev m7bf_try_wf := @LeanQbeTest.T.KissatM7BvaFactorTest.trylit_wf
abbrev m7bf_fac_wf := @LeanQbeTest.T.KissatM7BvaFactorTest.factor_wf
abbrev m7bf_fns_wf := @LeanQbeTest.T.KissatM7BvaFactorTest.fns_wf
abbrev m7bf_acyc := @LeanQbeTest.T.KissatM7BvaFactorTest.mod_acyc
abbrev m7bf_init_wp := @LeanQbeTest.T.KissatM7BvaFactorTest.init_wp
abbrev m7bf_try_wp := @LeanQbeTest.T.KissatM7BvaFactorTest.trylit_wp
abbrev m7bf_fac_wp := @LeanQbeTest.T.KissatM7BvaFactorTest.factor_wp
abbrev m7bf_noExit := @LeanQbeTest.T.KissatM7BvaFactorTest.env_noExit
abbrev m7bf_modOk := @LeanQbeTest.T.KissatM7BvaFactorTest.mod_ok
abbrev m7bf_nv_init := @LeanQbeTest.T.KissatM7BvaFactorTest.nv_init
abbrev m7bf_nv_try := @LeanQbeTest.T.KissatM7BvaFactorTest.nv_trylit
abbrev m7bf_nv_fac := @LeanQbeTest.T.KissatM7BvaFactorTest.nv_factor
abbrev m7bf_fullLen := @LeanQbeTest.T.KissatM7BvaFactorTest.full_len
abbrev m7bf_fullAcyc := @LeanQbeTest.T.KissatM7BvaFactorTest.full_acyc
abbrev m7bf_fullWf := @LeanQbeTest.T.KissatM7BvaFactorTest.full_wf
abbrev m7bf_fullModOf := @LeanQbeTest.T.KissatM7BvaFactorTest.full_mod_of

#print axioms m7bf_init_wf
#print axioms m7bf_try_wf
#print axioms m7bf_fac_wf
#print axioms m7bf_fns_wf
#print axioms m7bf_acyc
#print axioms m7bf_init_wp
#print axioms m7bf_try_wp
#print axioms m7bf_fac_wp
#print axioms m7bf_noExit
#print axioms m7bf_modOk
#print axioms m7bf_nv_init
#print axioms m7bf_nv_try
#print axioms m7bf_nv_fac
#print axioms m7bf_fullLen
#print axioms m7bf_fullAcyc
#print axioms m7bf_fullWf
#print axioms m7bf_fullModOf

end
