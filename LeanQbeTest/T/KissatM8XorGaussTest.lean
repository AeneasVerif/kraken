/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.LayerAXorF2
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
public import LeanQbe.T.Examples.Kissat.FullM8XorGauss
public import LeanQbe.T.Examples.Kissat.FullM8XorAssembly
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof
public import LeanQbe.T.Examples.Kissat.FullM8XorAssemblyProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6SatNv
meta import LeanQbe.T.Examples.Kissat.FullM8XorGauss
meta import LeanQbe.T.Examples.Kissat.FullM8XorAssembly
meta import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof
meta import LeanQbe.T.Examples.Kissat.FullM8XorAssemblyProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M8 `FullM8XorGauss`

1. Executable `#guard` checks on `m8XorGaussModule` (`19` fns, `7` externs, `0` exits),
   `m8XorGaussSpecTable` (`19` rows, `noExit = true`), `m8XorFidelityModule` (`433` fns, `0`
   externs, `0` exits), `PrintCpp` (`m8XorGaussModule` and `m8XorFidelityModule`), and 4-ISA
   `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, standalone
   `m8XorGauss_moduleOk`, `m8ProbeWrap_wp`, closed `433/433` `m8XorFidelity_moduleOk`,
   `PatchModule` bridges, top-level `kissat_solve_bytes` UNSAT soundness, top-level UNSAT NV, and
   concrete `Mem 64` GF(2) RREF elimination + contradiction NV (`XPost := False`).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM8XorGaussTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM8XorGauss
open LeanQbe.T.Examples.Kissat.FullM8XorAssembly
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen, Legalization & Structural Checks -/

#guard m8XorGaussFns.length == 19
#guard m8XorGaussModule.externs.length == 7
#guard m8XorGaussModule.exits.isEmpty == true
#guard m8XorGaussModule.checkAcyclic == true
#guard m8XorGaussSpecTable.length == 19
#guard m8XorGaussSpecTable.all (·.noExit) == true
#guard (m8XorGaussSpecTable ++ m8XorGaussExternRows).map (fun e => (e.name, e.as, e.rs)) ==
  m8XorGaussModule.sigs
#guard m8XorFidelityFns.length == 433
#guard m8XorFidelityModule.externs.isEmpty == true
#guard m8XorFidelityModule.exits.isEmpty == true
#guard m8XorPatchReplRows.map (fun e => (e.name, e.as, e.rs)) == m8XorPatchRepls.map Fn.sig
#guard m8XorPatchBeforeRows.map (fun e => (e.name, e.as, e.rs)) ==
  (m8XorGaussFns ++ [fullProbeM7InnerFn]).map Fn.sig
#guard (ppTModule m8XorGaussModule).isOk
#guard (ppTModule m8XorFidelityModule).isOk
#guard (ppModule (m8XorGaussFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m8XorGaussFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m8XorGaussFns.map (Fn.legal .x64AVX2))).isOk
#guard m8XorGaussFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard (ppModule ([m8ProbeWrapFn].map (Fn.legal .aarch64))).isOk
#guard (ppModule ([m8ProbeWrapFn].map (Fn.legal .scalar64))).isOk
#guard (ppModule ([m8ProbeWrapFn].map (Fn.legal .x64AVX2))).isOk
#guard (Fn.legal .x64AVX512 m8ProbeWrapFn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem xor_gauss_fns_wf : ∀ f ∈ m8XorGaussFns, f.Wf := m8XorGaussFns_wf
theorem xor_gauss_acyc : m8XorGaussModule.checkAcyclic = true := m8XorGauss_acyclic
theorem xor_gauss_tbl_len : m8XorGaussSpecTable.length = 19 := m8XorGaussSpecTable_len
theorem xor_gauss_tbl_sigs :
    (m8XorGaussSpecTable ++ m8XorGaussExternRows).map (fun e => (e.name, e.as, e.rs)) =
      m8XorGaussModule.sigs :=
  m8XorGaussSpecTable_sigs
theorem xor_gauss_noExit :
    ∀ f as bs xs m Q X X',
      m8XorGaussEnv f as bs xs m Q X → m8XorGaussEnv f as bs xs m Q X' :=
  m8XorGaussEnv_noExit
theorem xor_gauss_tbl_impl :
    TableImpl m8XorGaussEnv m8XorGaussFns m8XorGaussSpecTable :=
  m8XorGauss_tableImpl
theorem xor_gauss_mod_ok : ModuleOk m8XorGaussEnv m8XorGaussModule := m8XorGauss_moduleOk

theorem xor_asm_fns_wf : ∀ f ∈ m8XorFidelityFns, f.Wf := m8XorFidelityFns_wf
theorem xor_asm_acyc : m8XorFidelityModule.checkAcyclic = true := m8XorFidelity_acyclic
theorem xor_asm_noExit :
    ∀ f as bs xs m Q X X',
      m8XorFidelityEnv f as bs xs m Q X → m8XorFidelityEnv f as bs xs m Q X' :=
  m8XorFidelityEnv_noExit
theorem xor_asm_probe_wrap_wp (Γ : Env)
    (hXorGauss : ∀ a m Q X, fullXorGaussSpec a m Q X →
      Γ "full_xor_gauss" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hInner : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m7_inner" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X → Func.wp Γ FullM8XorAssembly.full_probe_m6_body a m Q X :=
  m8ProbeWrap_wp Γ hXorGauss hSubst hSetWm hInner
theorem xor_asm_mod_ok : ModuleOk m8XorFidelityEnv m8XorFidelityModule := m8XorFidelity_moduleOk
theorem xor_asm_patch_repl :
    TableImpl m8XorFidelityEnv m8XorPatchRepls m8XorPatchReplRows :=
  m8XorPatchRepl_tableImpl
theorem xor_asm_patch_bef :
    TableImpl m8XorFidelityEnv (m8XorGaussFns ++ [fullProbeM7InnerFn]) m8XorPatchBeforeRows :=
  m8XorPatchBefore_tableImpl

theorem xor_asm_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8XorFidelityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8XorFidelity_solve_bytes_sound hcfit hwfit hm

theorem xor_asm_host_sound
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
  m8XorFidelity_solve_bytes_host_sound hpost hhost

theorem xor_asm_unsat_nv :
    Func.wp m8XorFidelityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8XorFidelity_unsat_nv

theorem xor_nv_rref :
    Func.wp m8XorFidelityEnv full_xor_rref_body
      (nvXor5Cfg.pScratchBuf, 0#64, 2#64, 5#64, ()) nvXor5PreMem
      (fun () m' => FullMem nvXor5Cfg nvXor5PostRrefState m')
      (fun _ _ _ _ => False) :=
  nv_m8_xor_rref_concrete

theorem xor_nv_rref_emit :
    Func.wp m8XorFidelityEnv full_xor_rref_body
      (nvXor5Cfg.pScratchBuf, 0#64, 2#64, 5#64, ()) nvXor5PreMem
      (fun () m1 =>
        FullMem nvXor5Cfg nvXor5PostRrefState m1 ∧
        Func.wp m8XorFidelityEnv full_xor_emit_mat_body
          (nvXor5Cfg.hdr, 0#64, 2#64, 5#64, ()) m1
          (fun (r, ()) m' =>
            r = 20#64 ∧ nvXor5F0.Unsat ∧ FullMem nvXor5Cfg nvXor5PostEmitState m')
          (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) :=
  nv_m8_xor_rref_then_emit_unsat

end LeanQbeTest.T.KissatM8XorGaussTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m8xor_g_wf := @LeanQbeTest.T.KissatM8XorGaussTest.xor_gauss_fns_wf
abbrev m8xor_g_acyc := @LeanQbeTest.T.KissatM8XorGaussTest.xor_gauss_acyc
abbrev m8xor_g_len := @LeanQbeTest.T.KissatM8XorGaussTest.xor_gauss_tbl_len
abbrev m8xor_g_sigs := @LeanQbeTest.T.KissatM8XorGaussTest.xor_gauss_tbl_sigs
abbrev m8xor_g_nx := @LeanQbeTest.T.KissatM8XorGaussTest.xor_gauss_noExit
abbrev m8xor_g_tbl := @LeanQbeTest.T.KissatM8XorGaussTest.xor_gauss_tbl_impl
abbrev m8xor_g_mod := @LeanQbeTest.T.KissatM8XorGaussTest.xor_gauss_mod_ok
abbrev m8xor_a_wf := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_fns_wf
abbrev m8xor_a_acyc := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_acyc
abbrev m8xor_a_nx := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_noExit
abbrev m8xor_a_wrap := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_probe_wrap_wp
abbrev m8xor_a_mod := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_mod_ok
abbrev m8xor_a_pr := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_patch_repl
abbrev m8xor_a_pb := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_patch_bef
abbrev m8xor_a_snd := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_solve_sound
abbrev m8xor_a_host := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_host_sound
abbrev m8xor_a_nv := @LeanQbeTest.T.KissatM8XorGaussTest.xor_asm_unsat_nv
abbrev m8xor_nv_rr := @LeanQbeTest.T.KissatM8XorGaussTest.xor_nv_rref
abbrev m8xor_nv_re := @LeanQbeTest.T.KissatM8XorGaussTest.xor_nv_rref_emit

#print axioms m8xor_g_wf
#print axioms m8xor_g_acyc
#print axioms m8xor_g_len
#print axioms m8xor_g_sigs
#print axioms m8xor_g_nx
#print axioms m8xor_g_tbl
#print axioms m8xor_g_mod
#print axioms m8xor_a_wf
#print axioms m8xor_a_acyc
#print axioms m8xor_a_nx
#print axioms m8xor_a_wrap
#print axioms m8xor_a_mod
#print axioms m8xor_a_pr
#print axioms m8xor_a_pb
#print axioms m8xor_a_snd
#print axioms m8xor_a_host
#print axioms m8xor_a_nv
#print axioms m8xor_nv_rr
#print axioms m8xor_nv_re
