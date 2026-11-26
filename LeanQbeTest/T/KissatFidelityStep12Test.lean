/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Step-12 Top-Level Source Audit (`KissatFidelityStep12Test`)

Architecture-independent C0 IR verification & 4-ISA `#guard` suite of
`FullFidelityAssemblyStep12.fidStep12Module` (`517` fns, `0` externs, `0` exits):
1. Executable DIMACS parser guards (`parseDimacs`, `nvM6UnsatBytes`).
2. Module shape, SysV `<= 6`-arg ABI, Gate-1 purity, acyclicity, Cpp/QBE printing, & 4-ISA
   legalization `#guard`s for all `46` Step-11/Step-12 replacements and `12` inserted helpers.
3. `ModuleOk fidStep12Env fidStep12Module`, `fidStep12Env_noExit`, top-level `kissat_solve_bytes`
   `Func.wp` UNSAT soundness + caller memory framing (`XPost := False`) and `(Eq m' ⋆ F_host)`
   host-framed lift, plus concrete `Mem 64` UNSAT non-vacuity (`fidStep12_unsat_nv`, `r = 20#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityStep12Test

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem fidStep12_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def fidStep12AuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard fidStep12AuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome
#guard (parseDimacs "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList).isSome

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep12Fns.length == 517
#guard (fidStep12Fns.map Fn.name).eraseDups.length == 517
#guard fidStep12Fns.all fun fn => fn.as.length <= 6
#guard fidStep12Module.checkAcyclic == true
#guard fidStep12Module.externs.isEmpty && fidStep12Module.exits.isEmpty
#guard fidStep12Repls.length == 46
#guard (fidStep12Befores.flatMap Prod.snd).length == 12
#guard (PrintCpp.ppTModule fidStep12Module).isOk
#guard (PrintQbe.module fidStep12Module).isOk
#guard (PrintCpp.ppModule (fidStep12Repls.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep12Repls.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep12Repls.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep12Repls.map (Fn.legal .x64AVX512))).isOk
#guard (PrintCpp.ppModule ((fidStep12Befores.flatMap Prod.snd).map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule ((fidStep12Befores.flatMap Prod.snd).map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule ((fidStep12Befores.flatMap Prod.snd).map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule ((fidStep12Befores.flatMap Prod.snd).map (Fn.legal .x64AVX512))).isOk
#guard fidStep12Repls.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidStep12Repls.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidStep12Repls.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidStep12Repls.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard (fidStep12Befores.flatMap Prod.snd).all fun fn =>
  (Fn.legal .aarch64 fn).body.isLegal .aarch64 &&
  (Fn.legal .scalar64 fn).body.isLegal .scalar64 &&
  (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2 &&
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. `fidStep12Module` (`517` fns) Shape, Acyclicity, `Fn.Wf`, & `ModuleOk` -/

/-- `fidStep12Module` has `517` functions, `0` externs, and `0` exits. -/
theorem fidStep12_shape :
    fidStep12Module.fns.length = 517 ∧
    fidStep12Module.externs = [] ∧
    fidStep12Module.exits = [] :=
  ⟨fidStep12Fns_length, fidStep12_externs_empty, fidStep12_noExit⟩

/-- Every function in `fidStep12Module` satisfies `Fn.Wf`. -/
theorem fidStep12_wf : ∀ f ∈ fidStep12Module.fns, f.Wf :=
  fidStep12Module_wf

/-- `fidStep12Module` has an acyclic call graph (`checkAcyclic = true`). -/
theorem fidStep12_acyc : fidStep12Module.checkAcyclic = true :=
  fidStep12Module_acyclic

/-- Every specification in `fidStep12Env` is exit-free (`XPost`-monotone). -/
theorem fidStep12_env_nx :
    ∀ f as bs xs m Q X X',
      fidStep12Env f as bs xs m Q X → fidStep12Env f as bs xs m Q X' :=
  fidStep12Env_noExit

/-- Closed `0`-hook `ModuleOk` for all `517` functions of `fidStep12Module`. -/
theorem fidStep12_mod_ok : ModuleOk fidStep12Env fidStep12Module :=
  fidStep12_moduleOk

/-- Canonical Step-12 `KissatUnsatPkg` supplies a verified `ModuleOk` bundle. -/
theorem fidStep12_pkg_ok :
    ModuleOk fidStep12UnsatPkg.env fidStep12UnsatPkg.mod :=
  fidStep12UnsatPkg.moduleOk

/-! ## 4. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness & Host Lift -/

/-- Source-level UNSAT soundness + caller memory framing on `fidStep12Module` (`XPost := False`). -/
theorem fidStep12_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep12Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidStep12_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `fidStep12Module`. -/
theorem fidStep12_host_ok
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
  fidStep12_solve_bytes_host_sound hq hdmem

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`fidStep12Module`) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidStep12Module` on `nvM6UnsatInitMem`. -/
theorem fidStep12_nv :
    Func.wp fidStep12Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidStep12_unsat_nv

/-! ## 6. Single-Line `< 120c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms fidStep12_cnf_def
#print axioms fidStep12_shape
#print axioms fidStep12_wf
#print axioms fidStep12_acyc
#print axioms fidStep12_env_nx
#print axioms fidStep12_mod_ok
#print axioms fidStep12_pkg_ok
#print axioms fidStep12_unsat
#print axioms fidStep12_host_ok
#print axioms fidStep12_nv

end LeanQbeTest.T.KissatFidelityStep12Test
