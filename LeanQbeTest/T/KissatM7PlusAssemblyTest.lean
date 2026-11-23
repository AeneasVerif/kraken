/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyPart1
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyPart1
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof0
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards & Axiom Audit for Kissat M7Plus Assembly

Zero `@[expose]`, zero `@[local]`, zero `import all`, zero SAT model proofs, UNSAT-only:
1. Executable `#guard` checks on `m7PlusRepls` (`17`), `m7PlusModule` (`410` fns, `0` exits/externs,
   `checkAcyclic = true`), `m7PlusBaseTable` (`410` rows, `noExit = true`), `PrintCpp`,
   `PrintQbe`, and 4-ISA `Fn.legal` (`aarch64`, `scalar64`, `x64AVX2`, `x64AVX512`).
2. Audit-ready restated UNSAT-only headline theorems (`m7Plus_checkAcyclic`, `m7Plus_noExit`,
   `m7Plus_moduleOk`, `m7Plus_solve_bytes_sound`, `m7Plus_solve_bytes_host_sound`,
   `m7Plus_unsat_nv` with `XPost := False`).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7PlusAssemblyTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Plus
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & 4-ISA Legalization Checks -/

#guard m7PlusRepls.length == 17
#guard (m7PlusRepls.map Fn.name).eraseDups.length == 17
#guard m7PlusFns.length == 410
#guard (m7PlusFns.map Fn.name).eraseDups.length == 410
#guard m7PlusFns.map Fn.sig == m7Fns.map Fn.sig
#guard m7PlusModule.checkAcyclic == true
#guard m7PlusModule.exits.isEmpty && m7PlusModule.externs.isEmpty
#guard m7PlusBaseTable.length == 410
#guard m7PlusBaseTable.all (·.noExit) == true
#guard m7PlusBaseTable.map (fun e => (e.name, e.as, e.rs)) == m7Fns.map Fn.sig
#guard (ppTModule m7PlusModule).isOk
#guard (PrintQbe.module m7PlusModule).isOk
#guard (ppModule (m7PlusFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7PlusFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7PlusFns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7PlusFns.map (Fn.legal .x64AVX2))).isOk
#guard m7PlusFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7PlusFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7PlusFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m7PlusFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

/-! ## 2. Audit-Ready UNSAT-Only Headline Theorems -/

theorem hp_len : m7PlusFns.length = 410 := m7PlusFns_length
theorem hp_wf : ∀ f ∈ m7PlusModule.fns, f.Wf := m7PlusFns_wf
theorem hp_acyc : m7PlusModule.checkAcyclic = true := m7Plus_checkAcyclic

theorem hp_noExit : m7PlusModule.exits = [] := m7Plus_noExit

theorem hp_envNoExit :
    ∀ f as bs xs m Q X X',
      m7PlusEnv f as bs xs m Q X → m7PlusEnv f as bs xs m Q X' :=
  m7PlusEnv_noExit

theorem hp_modOk : ModuleOk m7PlusEnv m7PlusModule := m7Plus_moduleOk

theorem hp_solveSound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m7PlusEnv m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m7Plus_solve_bytes_sound hcfit hwfit hm

theorem hp_hostSound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  m7Plus_solve_bytes_host_sound hq hdmem

theorem hp_unsatNv :
    Func.wp m7PlusEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m7Plus_unsat_nv

end LeanQbeTest.T.KissatM7PlusAssemblyTest

/-! ## 3. Single-Line `< 115c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7pa_len := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_len
abbrev m7pa_wf := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_wf
abbrev m7pa_acyc := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_acyc
abbrev m7pa_nx := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_noExit
abbrev m7pa_enx := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_envNoExit
abbrev m7pa_mod := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_modOk
abbrev m7pa_sb := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_solveSound
abbrev m7pa_host := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_hostSound
abbrev m7pa_nv := @LeanQbeTest.T.KissatM7PlusAssemblyTest.hp_unsatNv

#print axioms m7pa_len
#print axioms m7pa_wf
#print axioms m7pa_acyc
#print axioms m7pa_nx
#print axioms m7pa_enx
#print axioms m7pa_mod
#print axioms m7pa_sb
#print axioms m7pa_host
#print axioms m7pa_nv
