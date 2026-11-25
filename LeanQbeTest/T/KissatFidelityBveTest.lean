/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBve
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofNv0
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofNv
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullFidelityBve
meta import LeanQbe.T.Examples.Kissat.FullFidelityBveProof
meta import LeanQbe.T.Examples.Kissat.FullFidelityBveProofNv0
meta import LeanQbe.T.Examples.Kissat.FullFidelityBveProofNv
meta import LeanQbe.T.Examples.Kissat.FullM6SatNv
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat `FullFidelityBve`

1. Executable `#guard` checks on `fidBveModule` (`469` fns, `0` externs, `0` exits),
   `fidBveCoreParityModule` (`472` fns, `0` externs, `0` exits), `fidBveSpecTable` (`469` rows),
   `fidBveCoreParitySpecTable` (`472` rows), ZERO beyond-upstream heuristics (`D-11`
   `full_bve_find_xor_m8` and `D-22` `full_bve_bce_side_m8` absent from both modules), `PrintCpp`,
   `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Restated headline theorems covering closed `ModuleOk` / `TableImpl` / byte-level UNSAT
   soundness / host-framed UNSAT soundness / concrete `r = 20#64` Tier-3b NV for both
   `fidBveModule` and `fidBveCoreParityModule`, plus concrete `Mem 64` `GAP-BVE-01..03` NV
   witnesses (`XPost := False`).
3. Single-line `<= 100`c `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityBveTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen, Purity & Legalization Checks -/

private def fidPatchedFns : List Fn := fidBveCoreParityRepls ++ m8MinHelpers ++ fidBveHelpers

#guard fidBveHelpers.length == 20
#guard fidBveRepls.length == 5
#guard fidBveBefores.length == 1
#guard fidBveFns.length == 469
#guard (fidBveFns.map Fn.name).eraseDups.length == 469
#guard fidBveModule.checkAcyclic == true
#guard fidBveModule.externs.isEmpty == true
#guard fidBveModule.exits.isEmpty == true
#guard fidBveSpecTable.length == 469
#guard fidBveSpecTable.all SpecEntry.noExit == true
#guard fidBveSpecTable.map (fun e => (e.name, e.as, e.rs)) == fidBveModule.sigs
#guard !(fidBveFns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidBveFns.map Fn.name).contains "full_bve_bce_side_m8"
#guard fidBveCoreParityRepls.length == 10
#guard fidBveCoreParityBefores.length == 2
#guard fidBveCoreParityFns.length == 472
#guard (fidBveCoreParityFns.map Fn.name).eraseDups.length == 472
#guard fidBveCoreParityModule.checkAcyclic == true
#guard fidBveCoreParityModule.externs.isEmpty == true
#guard fidBveCoreParityModule.exits.isEmpty == true
#guard fidBveCoreParitySpecTable.length == 472
#guard fidBveCoreParitySpecTable.all SpecEntry.noExit == true
#guard fidBveCoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) ==
    fidBveCoreParityModule.sigs
#guard !(fidBveCoreParityFns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidBveCoreParityFns.map Fn.name).contains "full_bve_bce_side_m8"
#guard (ppTModule fidBveModule).isOk
#guard (PrintQbe.module fidBveModule).isOk
#guard (ppTModule fidBveCoreParityModule).isOk
#guard (PrintQbe.module fidBveCoreParityModule).isOk
#guard (ppModule (fidPatchedFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidPatchedFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidPatchedFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (fidPatchedFns.map (Fn.legal .x64AVX512))).isOk
#guard fidPatchedFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidPatchedFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidPatchedFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidPatchedFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem fb_helpers_wf : ∀ f ∈ fidBveHelpers, f.Wf := fidBveHelpers_wf
theorem fb_repls_wf : ∀ r ∈ fidBveRepls, r.Wf := fidBveRepls_wf
theorem fb_core_repls_wf : ∀ r ∈ fidBveCoreParityRepls, r.Wf := fidBveCoreParityRepls_wf
theorem fb_fns_nodup : (fidBveFns.map Fn.name).Nodup := fidBveFns_names_nodup
theorem fb_core_fns_nodup : (fidBveCoreParityFns.map Fn.name).Nodup :=
  fidBveCoreParityFns_names_nodup
theorem fb_tbl_len : fidBveSpecTable.length = 469 := fidBveSpecTable_length
theorem fb_tbl_noExit : fidBveSpecTable.all SpecEntry.noExit = true := fidBveSpecTable_noExit
theorem fb_core_tbl_len : fidBveCoreParitySpecTable.length = 472 :=
  fidBveCoreParitySpecTable_length
theorem fb_core_tbl_noExit : fidBveCoreParitySpecTable.all SpecEntry.noExit = true :=
  fidBveCoreParitySpecTable_noExit

theorem fb_mod_ok : ModuleOk fidBveEnv fidBveModule := fidBve_moduleOk
theorem fb_tbl_impl : TableImpl fidBveEnv fidBveModule.fns fidBveSpecTable := fidBve_tableImpl

theorem fb_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidBveEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidBve_solve_bytes_sound hcfit hwfit hm

theorem fb_solve_host
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  fidBve_solve_bytes_host_sound hpost hhost

theorem fb_unsat_nv :
    Func.wp fidBveEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidBve_unsat_nv

theorem fb_core_ok : ModuleOk fidBveCoreParityEnv fidBveCoreParityModule :=
  fidBveCoreParity_moduleOk
theorem fb_core_tbl_impl :
    TableImpl fidBveCoreParityEnv fidBveCoreParityModule.fns fidBveCoreParitySpecTable :=
  fidBveCoreParity_tableImpl

theorem fb_core_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidBveCoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidBveCoreParity_solve_bytes_sound hcfit hwfit hm

theorem fb_core_solve_host
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  fidBveCoreParity_solve_bytes_host_sound hpost hhost

theorem fb_core_unsat_nv :
    Func.wp fidBveCoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidBveCoreParity_unsat_nv

theorem fb_nv_mv_zero (m : Mem 64) :
    Func.wp fidBveEnv full_bve_k6_mv_fid_body (0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_zero m

theorem fb_nv_mv_min (m : Mem 64) :
    Func.wp fidBveEnv full_bve_k6_mv_fid_body (16384#64, ()) m
      (fun (r, ()) m' => r = 256#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_min m

theorem fb_nv_mv_mid (m : Mem 64) :
    Func.wp fidBveEnv full_bve_k6_mv_fid_body (65536#64, ()) m
      (fun (r, ()) m' => r = 896#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_mid m

theorem fb_nv_mv_cap (m : Mem 64) :
    Func.wp fidBveEnv full_bve_k6_mv_fid_body (524288#64, ()) m
      (fun (r, ()) m' => r = 8192#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_cap m

theorem fb_nv_ticks_add :
    Func.wp fidBveEnv full_fid_k6_add_ticks_body (nvFidCfg.hdr, 1500#64, ()) nvFidCertMem
      (fun _ m' => ∃ s',
        s'.scratch.scratch_buf[4204]? = some 1500#32 ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_k6_add_ticks_add

theorem fb_nv_ticks_sat :
    Func.wp fidBveEnv full_fid_k6_add_ticks_body (nvFidCfg.hdr, 1000#64, ()) nvFidTicksMem
      (fun _ m' => ∃ s',
        s'.scratch.scratch_buf[4204]? = some 0xFFFFFFFF#32 ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_k6_add_ticks_sat

theorem fb_nv_cert_unit :
    Func.wp fidBveEnv full_bve_certify_unit_fid_body
      (nvFidCfg.hdr, 0#32, 0#32, 0#32, 1#32, 4002#32, ()) nvFidCertMem
      (fun (ok, ()) m' => ∃ s',
        ok = true ∧ s'.core.trail_end = 2 ∧
        s'.core.vals[0]? = some 1#8 ∧ s'.core.vals[1]? = some 0xFF#8 ∧
        s'.core.trl[1]? = some 0#32 ∧ FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧
        TmkZero s' ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_certify_unit_direct

theorem fb_nv_gates :
    Func.wp fidBveEnv full_bve_gates_fid_body (nvFidCfg.hdr, 0#32, 1#32, 0#32, ()) nvFidCertMem
      (fun () m' => ∃ s',
        FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧ TmkZero s' ∧
        s'.core.cur_vars = 4 ∧ s'.core.arena = List.replicate 6 0#32 ∧
        s'.core.arena_len = 0 ∧ s'.core.fuel.toNat ≤ 1 ∧
        s'.scratch.scratch_buf[0]? = some 2147483651#32 ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bve_gates

theorem fb_nv_bve_var_m7 :
    Func.wp fidBveEnv FullFidelityBve.full_bve_var_m7_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bve_var_m7

theorem fb_nv_bve_var :
    Func.wp fidBveEnv FullFidelityBve.full_bve_var_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bve_var

theorem fb_nv_elim_bve :
    Func.wp fidBveEnv full_elim_bve_m7_body (nvFidCfg.hdr, 0#64, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_elim_bve_m7

theorem fb_nv_eliminate :
    Func.wp fidBveEnv full_eliminate_m6_body (nvFidCfg.hdr, false, ()) nvFidSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvFidCfg nvFidF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_eliminate_m6

theorem fb_nv_gates_sw :
    Func.wp fidBveCoreParityEnv full_bve_gates_fid_body (nvFidCfg.hdr, 0#32, 1#32, 0#32, ())
      nvFidCertMem
      (fun () m' => ∃ s',
        FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧ TmkZero s' ∧
        s'.core.cur_vars = 4 ∧ s'.core.arena = List.replicate 6 0#32 ∧
        s'.core.arena_len = 0 ∧ s'.core.fuel.toNat ≤ 1 ∧
        s'.scratch.scratch_buf[0]? = some 2147483651#32 ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bve_gates_sw

theorem fb_nv_eliminate_sw :
    Func.wp fidBveCoreParityEnv full_eliminate_m6_body (nvFidCfg.hdr, false, ()) nvFidSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvFidCfg nvFidF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_eliminate_m6_sw

end LeanQbeTest.T.KissatFidelityBveTest

/-! ## 3. Single-Line Kernel Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev fb_a_hwf := @LeanQbeTest.T.KissatFidelityBveTest.fb_helpers_wf
abbrev fb_a_rwf := @LeanQbeTest.T.KissatFidelityBveTest.fb_repls_wf
abbrev fb_a_cwf := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_repls_wf
abbrev fb_a_nd := @LeanQbeTest.T.KissatFidelityBveTest.fb_fns_nodup
abbrev fb_a_cnd := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_fns_nodup
abbrev fb_a_tl := @LeanQbeTest.T.KissatFidelityBveTest.fb_tbl_len
abbrev fb_a_tne := @LeanQbeTest.T.KissatFidelityBveTest.fb_tbl_noExit
abbrev fb_a_ctl := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_tbl_len
abbrev fb_a_ctne := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_tbl_noExit
abbrev fb_a_ok := @LeanQbeTest.T.KissatFidelityBveTest.fb_mod_ok
abbrev fb_a_tbl := @LeanQbeTest.T.KissatFidelityBveTest.fb_tbl_impl
abbrev fb_a_sb := @LeanQbeTest.T.KissatFidelityBveTest.fb_solve_sound
abbrev fb_a_sh := @LeanQbeTest.T.KissatFidelityBveTest.fb_solve_host
abbrev fb_a_nv := @LeanQbeTest.T.KissatFidelityBveTest.fb_unsat_nv
abbrev fb_a_cok := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_ok
abbrev fb_a_ctbl := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_tbl_impl
abbrev fb_a_csb := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_solve_sound
abbrev fb_a_csh := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_solve_host
abbrev fb_a_cnv := @LeanQbeTest.T.KissatFidelityBveTest.fb_core_unsat_nv
abbrev fb_a_mv0 := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_mv_zero
abbrev fb_a_mv1 := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_mv_min
abbrev fb_a_mv2 := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_mv_mid
abbrev fb_a_mv3 := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_mv_cap
abbrev fb_a_ta := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_ticks_add
abbrev fb_a_ts := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_ticks_sat
abbrev fb_a_cert := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_cert_unit
abbrev fb_a_gt := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_gates
abbrev fb_a_vm7 := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_bve_var_m7
abbrev fb_a_var := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_bve_var
abbrev fb_a_ebve := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_elim_bve
abbrev fb_a_elim := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_eliminate
abbrev fb_a_gtsw := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_gates_sw
abbrev fb_a_elsw := @LeanQbeTest.T.KissatFidelityBveTest.fb_nv_eliminate_sw
abbrev fb_a_certsw := @LeanQbe.T.Examples.Kissat.FullFidelityBve.nv_fid_certify_unit_direct_sw
abbrev fb_a_vm7sw := @LeanQbe.T.Examples.Kissat.FullFidelityBve.nv_fid_bve_var_m7_sw
abbrev fb_a_varsw := @LeanQbe.T.Examples.Kissat.FullFidelityBve.nv_fid_bve_var_sw
abbrev fb_a_ebvesw := @LeanQbe.T.Examples.Kissat.FullFidelityBve.nv_fid_elim_bve_m7_sw
abbrev fb_a_wp_mv := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_bve_k6_mv_fid_wp
abbrev fb_a_wp_ext := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_k6_extract_and_solve_fid_wp
abbrev fb_a_wp_cu := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_bve_certify_unit_fid_wp
abbrev fb_a_wp_dk6 := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_bve_def_k6_fid_wp
abbrev fb_a_wp_gt := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_bve_gates_fid_wp
abbrev fb_a_wp_vm7 := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_bve_var_m7_fid_wp
abbrev fb_a_wp_var := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_bve_var_fid_wp
abbrev fb_a_wp_eb := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_elim_bve_m7_fid_wp
abbrev fb_a_wp_el := @LeanQbe.T.Examples.Kissat.FullFidelityBve.full_eliminate_m6_fid_wp

#print axioms fb_a_hwf
#print axioms fb_a_rwf
#print axioms fb_a_cwf
#print axioms fb_a_nd
#print axioms fb_a_cnd
#print axioms fb_a_tl
#print axioms fb_a_tne
#print axioms fb_a_ctl
#print axioms fb_a_ctne
#print axioms fb_a_ok
#print axioms fb_a_tbl
#print axioms fb_a_sb
#print axioms fb_a_sh
#print axioms fb_a_nv
#print axioms fb_a_cok
#print axioms fb_a_ctbl
#print axioms fb_a_csb
#print axioms fb_a_csh
#print axioms fb_a_cnv
#print axioms fb_a_mv0
#print axioms fb_a_mv1
#print axioms fb_a_mv2
#print axioms fb_a_mv3
#print axioms fb_a_ta
#print axioms fb_a_ts
#print axioms fb_a_cert
#print axioms fb_a_gt
#print axioms fb_a_vm7
#print axioms fb_a_var
#print axioms fb_a_ebve
#print axioms fb_a_elim
#print axioms fb_a_gtsw
#print axioms fb_a_elsw
#print axioms fb_a_certsw
#print axioms fb_a_vm7sw
#print axioms fb_a_varsw
#print axioms fb_a_ebvesw
#print axioms fb_a_wp_mv
#print axioms fb_a_wp_ext
#print axioms fb_a_wp_cu
#print axioms fb_a_wp_dk6
#print axioms fb_a_wp_gt
#print axioms fb_a_wp_vm7
#print axioms fb_a_wp_var
#print axioms fb_a_wp_eb
#print axioms fb_a_wp_el
