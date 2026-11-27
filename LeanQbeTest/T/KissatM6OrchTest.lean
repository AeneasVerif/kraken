/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6Orch
meta import LeanQbe.T.Examples.Kissat.FullM6OrchProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat `D-Full` M6 Orchestration Verification & Axiom Audit (`KissatM6OrchTest`)

1. Executable `#guard` checks on `FullM6Orch.m6OrchModule` (`29` fns, `65` externs, `0` exits,
   `94` sigs), `PrintCpp`, `PrintQbe`, and `Fn.legal` / `isLegal` across `.aarch64`, `.scalar64`,
   `.x64AVX512`, and `.x64AVX2`.
2. Restated headline theorems (`m6OrchPfxSpecTable`, `m6OrchSpecTable`, `m6Orch_moduleOk`,
   `m6OrchCore_moduleOk`, `m6Orch_solve_bytes_sound`, `m6Orch_solve_bytes_m6_sound`,
   `m6Orch_unsat_nv`, `m6Orch_sat_nv`).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM6OrchTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.FullM6Orch

/-! ## 1. Static Checks & Backend Compilation / ISA-Legality Guards -/

#guard m6OrchModule.checkAcyclic == true
#guard m6OrchModule.exits.isEmpty
#guard m6Orch_fns.length == 29
#guard m6OrchExterns.length == 65
#guard m6OrchModule.sigs.length == 94
#guard m6Orch_fns.map Fn.name ==
  [ "full_wstack_defrag", "full_watch_push", "full_rescale", "full_parse_body"
  , "full_lit_rank", "full_sweep_bins", "full_rewatch_arena", "full_arena_sweep"
  , "full_mark_reasons", "full_reduce_m6", "full_analyze_rsn_m6_hdr"
  , "full_min_shrink", "full_deduce_1uip", "full_deduce_1uip_m6_hdr"
  , "full_analyze_core_m6", "full_walk", "full_ema_swap_m6", "full_switch_mode_m6"
  , "full_sweep_dense_m6", "full_reorder_m6", "full_probe_tail_m6", "full_probe_m6"
  , "full_preprocess_m6", "full_simplify_m6", "full_search_m6"
  , "kissat_solve_bytes_m6", "full_preprocess", "full_search", "kissat_solve_bytes" ]
#guard (ppTModule m6OrchModule).isOk
#guard (PrintQbe.module m6OrchModule).isOk
#guard (ppModule (m6Orch_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6Orch_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6Orch_fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m6Orch_fns.map (Fn.legal .x64AVX2))).isOk
#guard m6Orch_fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m6Orch_fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m6Orch_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m6Orch_fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end LeanQbeTest.T.KissatM6OrchTest

/-! ## 2. Audit-Ready Headline Theorems & Single-Line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch

theorem m6o_wf : ∀ f ∈ m6Orch_fns, f.Wf := m6Orch_fns_wf
theorem m6o_acyclic : m6OrchModule.checkAcyclic = true := m6Orch_acyclic
theorem m6o_pfx_sigs :
    m6OrchPfxSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      (m6Orch_fns.take 24).map Fn.sig := m6OrchPfxSpecTable_sigs
theorem m6o_pfx_len : m6OrchPfxSpecTable.length = 24 := m6OrchPfxSpecTable_length
theorem m6o_pfx_noExit : m6OrchPfxSpecTable.all SpecEntry.noExit = true :=
  m6OrchPfxSpecTable_noExit
theorem m6o_pfx_nodup : (m6OrchPfxSpecTable.map SpecEntry.name).Nodup :=
  m6OrchPfxSpecTable_nodup
theorem m6o_sigs :
    (m6OrchSpecTable fullM6SolveBytesSpec).map (fun e => (e.name, e.as, e.rs)) =
      m6OrchModule.sigs := m6OrchSpecTable_sigs fullM6SolveBytesSpec
theorem m6o_len : (m6OrchSpecTable fullM6SolveBytesSpec).length = 94 :=
  m6OrchSpecTable_length fullM6SolveBytesSpec
theorem m6o_nodup : ((m6OrchSpecTable fullM6SolveBytesSpec).map SpecEntry.name).Nodup :=
  m6OrchSpecTable_nodup fullM6SolveBytesSpec
theorem m6o_noExit : (m6OrchSpecTable fullM6SolveBytesSpec).all SpecEntry.noExit = true :=
  m6OrchSpecTable_noExit fullM6SolveBytesSpec
theorem m6o_mod_ok : ModuleOk m6OrchEnv m6OrchModule := m6Orch_moduleOk
theorem m6o_core_ok : ModuleOk m6OrchCoreEnv m6OrchModule := m6OrchCore_moduleOk

theorem m6o_solve_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m6OrchEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m6Orch_solve_bytes_sound hcfit hwfit hm

theorem m6o_solve_m6_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m6OrchEnv kissat_solve_bytes_m6_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m6Orch_solve_bytes_m6_sound hcfit hwfit hm

theorem m6o_unsat_nv :
    Func.wp m6OrchCoreEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m6Orch_unsat_nv

theorem m6o_sat_nv :
    Func.wp m6OrchEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,
        nvM6SatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64) ∧ r ≠ 20#64 ∧
          (r = 10#64 →
            ¬ nvM6SatCnf.Unsat ∧
            (∀ (F : Mem 64 → Prop) (M : Mem 64),
              (Eq m' ⋆ F) M → nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr))) ∧
          (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m6Orch_sat_nv

#print axioms m6o_wf
#print axioms m6o_acyclic
#print axioms m6o_pfx_sigs
#print axioms m6o_pfx_len
#print axioms m6o_pfx_noExit
#print axioms m6o_pfx_nodup
#print axioms m6o_sigs
#print axioms m6o_len
#print axioms m6o_nodup
#print axioms m6o_noExit
#print axioms m6o_mod_ok
#print axioms m6o_core_ok
#print axioms m6o_solve_ok
#print axioms m6o_solve_m6_ok
#print axioms m6o_unsat_nv
#print axioms m6o_sat_nv

end AxiomAudit
