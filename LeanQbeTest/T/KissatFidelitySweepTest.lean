/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelitySweep
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofCone1
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofVar
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofVar2
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProof
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullFidelitySweep
meta import LeanQbe.T.Examples.Kissat.FullFidelitySweepProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for `FullFidelitySweep` (`GAP-SWP-01..03`)

1. Executable `#guard` checks on `fidSweepStandModule` (`4` fns, `9` externs, `0` exits),
   `fidSweepModule` (`449` fns, `0` externs, `0` exits), `fidSweepCoreParityModule` (`471` fns,
   `0` externs, `0` exits), `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`,
   `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems for `fid_sweep_cone_wp`, `fid_sweep_sim_wp`,
   `fid_collect_cands_wp`, `fid_sweep_vars_wp`, closed `449/449` & `471/471` `ModuleOk` /
   `TableImpl` / byte-level UNSAT soundness / host-framed lift, and concrete non-bailout `Mem 64`
   UNSAT non-vacuity witnesses (`XPost := False`, `comp = 0` fresh + escalated `comp = 1` resume).
3. Single-line `<= 100`c `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelitySweepTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard fidSweepRepls.length == 4
#guard fidSweepStandModule.checkAcyclic == true
#guard fidSweepStandModule.fns.length == 4
#guard fidSweepStandModule.externs.length == 9
#guard fidSweepStandModule.exits.isEmpty == true
#guard fidSweepFns.length == 449
#guard (fidSweepFns.map Fn.name).eraseDups.length == 449
#guard fidSweepModule.checkAcyclic == true
#guard fidSweepModule.externs.isEmpty == true
#guard fidSweepModule.exits.isEmpty == true
#guard fidSweepCoreParityFns.length == 471
#guard (fidSweepCoreParityFns.map Fn.name).eraseDups.length == 471
#guard fidSweepCoreParityModule.checkAcyclic == true
#guard fidSweepCoreParityModule.externs.isEmpty == true
#guard fidSweepCoreParityModule.exits.isEmpty == true
#guard (ppTModule fidSweepStandModule).isOk
#guard (PrintQbe.module fidSweepStandModule).isOk
#guard (ppTModule fidSweepModule).isOk
#guard (ppTModule fidSweepCoreParityModule).isOk
#guard (ppModule (fidSweepRepls.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidSweepRepls.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidSweepRepls.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (fidSweepRepls.map (Fn.legal .x64AVX512))).isOk
#guard fidSweepRepls.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidSweepRepls.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidSweepRepls.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidSweepRepls.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem fs_repls_wf : ∀ r ∈ fidSweepRepls, r.Wf := fidSweepRepls_wf
theorem fs_fns_wf : ∀ f ∈ fidSweepFns, f.Wf := fidSweepFns_wf
theorem fs_names_nodup : (fidSweepFns.map Fn.name).Nodup := fidSweepFns_names_nodup
theorem fs_acyclic : fidSweepModule.checkAcyclic = true := fidSweep_acyclic
theorem fs_cp_acyclic :
    fidSweepCoreParityModule.namesNodup ∧
    ∀ pre fn post, fidSweepCoreParityModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ fidSweepCoreParityModule.externs.map Extern.sig)
        fidSweepCoreParityModule.exits :=
  fidSweepCoreParity_callsOk

theorem fs_cone_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hInit : M6EnvSpec Γ "full_k6_init" k6InitSpec)
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" k6AddClauseSpec) :
    ∀ args m Q X, m6SweepConeSpec args m Q X →
      Func.wp Γ FullFidelitySweep.full_m6_sweep_cone_body args m Q X :=
  fid_sweep_cone_wp Γ hMaxV hInit hAddCl

theorem fs_sim_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hFlipR : M6EnvSpec Γ "full_m6_sweep_flip_round" m6SweepFlipRoundSpec) :
    ∀ args m Q X, m6SweepSimSpec args m Q X →
      Func.wp Γ FullFidelitySweep.full_m6_sweep_sim_body args m Q X :=
  fid_sweep_sim_wp Γ hMaxV hSolve hRef hFlipR

theorem fs_cands_wp (Γ : Env)
    (hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec) :
    ∀ args m Q X, m6CollectCandsSpec args m Q X →
      Func.wp Γ FullFidelitySweep.full_m6_collect_cands_body args m Q X :=
  fid_collect_cands_wp Γ hSift

theorem fs_vars_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDP : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec)
    (hCol : M6EnvSpec Γ "full_m6_collect_cands" m6CollectCandsSpec)
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec) :
    ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp Γ FullFidelitySweep.full_m6_sweep_vars_body args m Q X :=
  fid_sweep_vars_wp Γ hMaxV hDP hCol hSV

theorem fs_mod_ok : ModuleOk m8FidV123t2Env fidSweepModule := fidSweep_moduleOk

theorem fs_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8FidV123t2Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidSweep_solve_bytes_sound hcfit hwfit hm

theorem fs_solve_host
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  fidSweep_solve_bytes_host_sound hpost hhost

theorem fs_unsat_nv :
    Func.wp m8FidV123t2Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidSweep_unsat_nv

theorem fs_cp_mod_ok : ModuleOk m8SweepV2CoreParityEnv fidSweepCoreParityModule :=
  fidSweepCoreParity_moduleOk

theorem fs_cp_tbl_impl :
    TableImpl m8SweepV2CoreParityEnv fidSweepCoreParityModule.fns m8SweepV2CoreParitySpecTable :=
  fidSweepCoreParity_tableImpl

theorem fs_cp_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8SweepV2CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidSweepCoreParity_solve_bytes_sound hcfit hwfit hm

theorem fs_cp_solve_host
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  fidSweepCoreParity_solve_bytes_host_sound hpost hhost

theorem fs_cp_unsat_nv :
    Func.wp m8SweepV2CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidSweepCoreParity_unsat_nv

theorem fs_nv_cone0 :
    Func.wp m8FidV123t2Env FullFidelitySweep.full_m6_sweep_cone_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M6SweepConeOk [[0], [1]] s' (r &&& 0xFFFF#64).toNat ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_sweep_cone_comp0

theorem fs_nv_cone1 :
    Func.wp m8SweepV2CoreParityEnv FullFidelitySweep.full_m6_sweep_cone_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ()) nvFidEscMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M6SweepConeOk [[0], [1]] s' (r &&& 0xFFFF#64).toNat ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_sweep_cone_comp1

theorem fs_nv_cands :
    Func.wp m8SweepV2CoreParityEnv FullFidelitySweep.full_m6_collect_cands_body
      (FullM4Sweep.nvM4SweepCfg.hdr, ()) nvFidEscMem
      (fun (nc, ()) m' => ∃ trc' ws2',
        nc.toNat ≤ nvFidEscState.core.cur_vars ∧
        Full.nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg
          { nvFidEscState with scratch :=
            { nvFidEscState.scratch with tarjan_reach := trc', work_stk2 := ws2' } } m')
      (fun _ _ _ _ => False) :=
  nv_fid_collect_cands_esc

theorem fs_nv_vars_fresh :
    Func.wp m8FidV123t2Env FullFidelitySweep.full_m6_sweep_vars_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
        M6TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_sweep_vars_fresh

theorem fs_nv_vars_resume :
    Func.wp m8SweepV2CoreParityEnv FullFidelitySweep.full_m6_sweep_vars_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvFidEscMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
        M6TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_sweep_vars_resume

end LeanQbeTest.T.KissatFidelitySweepTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev fidsw_r_wf := @LeanQbeTest.T.KissatFidelitySweepTest.fs_repls_wf
abbrev fidsw_f_wf := @LeanQbeTest.T.KissatFidelitySweepTest.fs_fns_wf
abbrev fidsw_nd := @LeanQbeTest.T.KissatFidelitySweepTest.fs_names_nodup
abbrev fidsw_acyc := @LeanQbeTest.T.KissatFidelitySweepTest.fs_acyclic
abbrev fidsw_cp_acyc := @LeanQbeTest.T.KissatFidelitySweepTest.fs_cp_acyclic
abbrev fidsw_cone := @LeanQbeTest.T.KissatFidelitySweepTest.fs_cone_wp
abbrev fidsw_sim := @LeanQbeTest.T.KissatFidelitySweepTest.fs_sim_wp
abbrev fidsw_cands := @LeanQbeTest.T.KissatFidelitySweepTest.fs_cands_wp
abbrev fidsw_vars := @LeanQbeTest.T.KissatFidelitySweepTest.fs_vars_wp
abbrev fidsw_ok := @LeanQbeTest.T.KissatFidelitySweepTest.fs_mod_ok
abbrev fidsw_sb := @LeanQbeTest.T.KissatFidelitySweepTest.fs_solve_sound
abbrev fidsw_host := @LeanQbeTest.T.KissatFidelitySweepTest.fs_solve_host
abbrev fidsw_nv := @LeanQbeTest.T.KissatFidelitySweepTest.fs_unsat_nv
abbrev fidsw_cp_ok := @LeanQbeTest.T.KissatFidelitySweepTest.fs_cp_mod_ok
abbrev fidsw_cp_tbl := @LeanQbeTest.T.KissatFidelitySweepTest.fs_cp_tbl_impl
abbrev fidsw_cp_sb := @LeanQbeTest.T.KissatFidelitySweepTest.fs_cp_solve_sound
abbrev fidsw_cp_host := @LeanQbeTest.T.KissatFidelitySweepTest.fs_cp_solve_host
abbrev fidsw_cp_nv := @LeanQbeTest.T.KissatFidelitySweepTest.fs_cp_unsat_nv
abbrev fidsw_nvc0 := @LeanQbeTest.T.KissatFidelitySweepTest.fs_nv_cone0
abbrev fidsw_nvc1 := @LeanQbeTest.T.KissatFidelitySweepTest.fs_nv_cone1
abbrev fidsw_nvca := @LeanQbeTest.T.KissatFidelitySweepTest.fs_nv_cands
abbrev fidsw_nvvf := @LeanQbeTest.T.KissatFidelitySweepTest.fs_nv_vars_fresh
abbrev fidsw_nvvr := @LeanQbeTest.T.KissatFidelitySweepTest.fs_nv_vars_resume

#print axioms fidsw_r_wf
#print axioms fidsw_f_wf
#print axioms fidsw_nd
#print axioms fidsw_acyc
#print axioms fidsw_cp_acyc
#print axioms fidsw_cone
#print axioms fidsw_sim
#print axioms fidsw_cands
#print axioms fidsw_vars
#print axioms fidsw_ok
#print axioms fidsw_sb
#print axioms fidsw_host
#print axioms fidsw_nv
#print axioms fidsw_cp_ok
#print axioms fidsw_cp_tbl
#print axioms fidsw_cp_sb
#print axioms fidsw_cp_host
#print axioms fidsw_cp_nv
#print axioms fidsw_nvc0
#print axioms fidsw_nvc1
#print axioms fidsw_nvca
#print axioms fidsw_nvvf
#print axioms fidsw_nvvr
