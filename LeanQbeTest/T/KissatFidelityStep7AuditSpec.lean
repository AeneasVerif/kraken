/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
meta import LeanQbe.T.Examples.LratBytes

/-!
# Canonical Gate-1 `KissatFidelity` Step-7 Top-Level Source Audit (`KissatFidelityStep7AuditSpec`)

Architecture-independent C0 IR verification of `FullFidelityAssemblyStep7.fidStep7Module`
(`501` functions: Step 6 `fidModule` + `FullFidelityStep7`, `0` externs, `0` exits, UNSAT-only,
zero SAT model proofs, zero `@[expose]` on theorems/lemmas, zero target imports):
1. Module shape & `0`-hook closure (`fidStep7Module`, `501` fns): `0` externs, `0` exits,
   `checkAcyclic = true`, all `501` functions `Fn.Wf`, `fidStep7Env_noExit`, and closed
   `ModuleOk fidStep7Env fidStep7Module`.
2. Top-level `kissat_solve_bytes` `Func.wp` UNSAT soundness + caller memory framing
   (`XPost := False`) and `(Eq m' ⋆ F_host) st_dmem` host-framed lift.
3. Concrete `8,192 B` `Mem 64` UNSAT non-vacuity (`r = 20#64 ∧ nvM6UnsatCnf.Unsat`,
   `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityStep7AuditSpec

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem fidStep7_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def fidStep7AuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard fidStep7AuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome

/-! ## 2. `fidStep7Module` (`501` fns) Shape, Acyclicity, `Fn.Wf`, & `ModuleOk` -/

/-- `fidStep7Module` has `501` functions, `0` externs, and `0` exits. -/
theorem fidStep7_shape :
    fidStep7Module.fns.length = 501 ∧
    fidStep7Module.externs = [] ∧
    fidStep7Module.exits = [] :=
  ⟨fidStep7Fns_length, fidStep7_externs_empty, fidStep7_noExit⟩

/-- Every function in `fidStep7Module` satisfies `Fn.Wf`. -/
theorem fidStep7_wf : ∀ f ∈ fidStep7Module.fns, f.Wf :=
  fidStep7Module_wf

/-- `fidStep7Module` has an acyclic call graph (`checkAcyclic = true`). -/
theorem fidStep7_acyc : fidStep7Module.checkAcyclic = true :=
  fidStep7Module_acyclic

/-- Every specification in `fidStep7Env` is exit-free (`XPost`-monotone). -/
theorem fidStep7_env_nx :
    ∀ f as bs xs m Q X X',
      fidStep7Env f as bs xs m Q X → fidStep7Env f as bs xs m Q X' :=
  fidStep7Env_noExit

/-- Closed `0`-hook `ModuleOk` for all `501` functions of `fidStep7Module`. -/
theorem fidStep7_mod_ok : ModuleOk fidStep7Env fidStep7Module :=
  fidStep7_moduleOk

/-! ## 3. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness & Host Lift -/

/-- Source-level UNSAT soundness + caller memory framing on `fidStep7Module` (`XPost := False`). -/
theorem fidStep7_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep7Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidStep7_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `fidStep7Module`. -/
theorem fidStep7_host_ok
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
  fidStep7_solve_bytes_host_sound hq hdmem

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidStep7Module` on `nvM6UnsatInitMem`. -/
theorem fidStep7_nv :
    Func.wp fidStep7Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidStep7_unsat_nv

/-! ## 5. Single-Line `<= 100c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms fidStep7_cnf_def
#print axioms fidStep7_shape
#print axioms fidStep7_wf
#print axioms fidStep7_acyc
#print axioms fidStep7_env_nx
#print axioms fidStep7_mod_ok
#print axioms fidStep7_unsat
#print axioms fidStep7_host_ok
#print axioms fidStep7_nv

end LeanQbeTest.T.KissatFidelityStep7AuditSpec
