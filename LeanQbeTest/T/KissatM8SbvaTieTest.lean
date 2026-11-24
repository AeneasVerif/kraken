module

public import LeanQbe.T.Examples.Kissat.FullM8SbvaTie
public import LeanQbe.T.Examples.Kissat.FullM8SbvaTieProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM8SbvaTie
meta import LeanQbe.T.Examples.Kissat.FullM8SbvaTieProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M8 `FullM8SbvaTie`

1. Executable `#guard` checks on `m8SbvaTieModule` (`1` fn `"full_bva_pick_cand"`, `0` externs,
   `0` exits), `m8SbvaTieSpecTable` (`1` row, `noExit = true`), `m8SbvaTiePatchFns`/`PatchRows`,
   `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and
   `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, parametric `Func.wp`,
   `fullBvaPickPres`, closed `TableImpl` / `ModuleOk`, `PatchRows` bridges, and concrete `Mem 64`
   UNSAT non-vacuity (`XPost := False`, both base and active 3-hop SBVA tie-breaking
   `wsort = [2, 2]`).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM8SbvaTieTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullM8SbvaTie
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m8SbvaTieFns.length == 1
#guard m8SbvaTieModule.externs.isEmpty == true
#guard m8SbvaTieModule.exits.isEmpty == true
#guard m8SbvaTieModule.checkAcyclic == true
#guard m8SbvaTieSpecTable.length == 1
#guard m8SbvaTieSpecTable.all (·.noExit) == true
#guard m8SbvaTieSpecTable.map (fun e => (e.name, e.as, e.rs)) == m8SbvaTieModule.sigs
#guard m8SbvaTieFns.map Fn.name == ["full_bva_pick_cand"]
#guard m8SbvaTiePatchFns.map Fn.name == ["full_bva_pick_cand"]
#guard m8SbvaTiePatchRows.map (fun e => (e.name, e.as, e.rs)) == m8SbvaTiePatchFns.map Fn.sig
#guard m8SbvaTiePatchRows.all (·.noExit) == true
#guard (ppTModule m8SbvaTieModule).isOk
#guard (PrintQbe.module m8SbvaTieModule).isOk
#guard (ppModule (m8SbvaTieFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m8SbvaTieFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m8SbvaTieFns.map (Fn.legal .x64AVX2))).isOk
#guard m8SbvaTieFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem sbva_pick_wf : Func.Wf full_bva_pick_sbva3_m8_body := full_bva_pick_sbva3_m8_wf
theorem sbva_fn_wf : m8SbvaPickCandFn.Wf := m8SbvaPickCandFn_wf
theorem sbva_fns_wf : ∀ f ∈ m8SbvaTieFns, f.Wf := m8SbvaTieFns_wf
theorem sbva_patch_fns_wf : ∀ f ∈ m8SbvaTiePatchFns, f.Wf := m8SbvaTiePatchFns_wf
theorem sbva_acyc : m8SbvaTieModule.checkAcyclic = true := m8SbvaTie_acyclic
theorem sbva_tbl_len : m8SbvaTieSpecTable.length = 1 := m8SbvaTieSpecTable_len

theorem sbva_noExit :
    ∀ f as bs xs m Q X X',
      m8SbvaTieEnv f as bs xs m Q X → m8SbvaTieEnv f as bs xs m Q X' :=
  m8SbvaTieEnv_noExit

theorem sbva_pick_wp (Γ : Env) :
    ∀ a m Q X, fullBvaPickCandSpec a m Q X →
      Func.wp Γ full_bva_pick_sbva3_m8_body a m Q X :=
  full_bva_pick_sbva3_m8_wp Γ

theorem sbva_pick_pres_wp (Γ : Env)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {ncntd f0 : BitVec 32}
    (hinv : FullDenseInvNoLm c F0 F_cur s)
    (hf0 : f0.toNat < 2 * s.core.cur_vars) (hnc : ncntd.toNat ≤ 2 * s.core.cur_vars)
    (hcntd : ∀ i < ncntd.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    {Q : Post [i32]} {X : XPost}
    (hPost : ∀ (r : BitVec 32) (s' : FullState) (m' : Mem 64),
      FullDenseInvNoLm c F0 F_cur s' → fullBvaPickPres s s' →
      (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bva_pick_sbva3_m8_body (c.hdr, ncntd, f0, ()) m Q X :=
  full_bva_pick_sbva3_m8_pres_wp Γ hinv hf0 hnc hcntd hm hPost

theorem sbva_tbl_impl :
    TableImpl m8SbvaTieEnv m8SbvaTieModule.fns m8SbvaTieSpecTable :=
  m8SbvaTie_tableImpl

theorem sbva_mod_ok : ModuleOk m8SbvaTieEnv m8SbvaTieModule :=
  m8SbvaTie_moduleOk

theorem sbva_patch_tbl_impl :
    TableImpl m8SbvaTieEnv m8SbvaTiePatchFns m8SbvaTiePatchRows :=
  m8SbvaTiePatch_tableImpl

theorem sbva_patch_tbl_of (Γ : Env) :
    TableImpl Γ m8SbvaTiePatchFns m8SbvaTiePatchRows :=
  m8SbvaTiePatch_tableImpl_of Γ

theorem sbva_pick_fn_impl : SpecEntry.Impl m8SbvaTieEnv m8SbvaPickCandFn
    ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩ :=
  m8SbvaPickCandFn_impl

theorem sbva_nv_pick :
    Func.wp m8SbvaTieEnv full_bva_pick_sbva3_m8_body
      (nvOneLitCfg.hdr, 2#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_bva_pick_sbva3

theorem sbva_nv_tie_3hop :
    Func.wp m8SbvaTieEnv full_bva_pick_sbva3_m8_body
      (nvOneLitCfg.hdr, 2#32, 0#32, ()) nvSbvaTieMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_bva_pick_sbva3_tie_3hop

end LeanQbeTest.T.KissatM8SbvaTieTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m8sbva_wf := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_pick_wf
abbrev m8sbva_fn_wf := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_fn_wf
abbrev m8sbva_fns_wf := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_fns_wf
abbrev m8sbva_pat_wf := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_patch_fns_wf
abbrev m8sbva_acyc := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_acyc
abbrev m8sbva_tbl_len := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_tbl_len
abbrev m8sbva_nx := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_noExit
abbrev m8sbva_wp := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_pick_wp
abbrev m8sbva_pres := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_pick_pres_wp
abbrev m8sbva_tbl := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_tbl_impl
abbrev m8sbva_mod := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_mod_ok
abbrev m8sbva_ptbl := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_patch_tbl_impl
abbrev m8sbva_ptbl_of := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_patch_tbl_of
abbrev m8sbva_fn := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_pick_fn_impl
abbrev m8sbva_nv := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_nv_pick
abbrev m8sbva_nv3 := @LeanQbeTest.T.KissatM8SbvaTieTest.sbva_nv_tie_3hop

#print axioms m8sbva_wf
#print axioms m8sbva_fn_wf
#print axioms m8sbva_fns_wf
#print axioms m8sbva_pat_wf
#print axioms m8sbva_acyc
#print axioms m8sbva_tbl_len
#print axioms m8sbva_nx
#print axioms m8sbva_wp
#print axioms m8sbva_pres
#print axioms m8sbva_tbl
#print axioms m8sbva_mod
#print axioms m8sbva_ptbl
#print axioms m8sbva_ptbl_of
#print axioms m8sbva_fn
#print axioms m8sbva_nv
#print axioms m8sbva_nv3
