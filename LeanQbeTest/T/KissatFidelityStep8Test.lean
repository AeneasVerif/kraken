/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep8
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep8
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Step-8 Top-Level Source Audit (`KissatFidelityStep8Test`)

Architecture-independent C0 IR verification & 4-ISA `#guard` suite of
`FullFidelityAssemblyStep8.fidStep8Module` (`501` functions: Step 7 `fidStep7Module` +
`FullFidelityStep8`, `0` externs, `0` exits, UNSAT-only, zero SAT model proofs, zero `@[expose]`
on theorems/lemmas, zero target imports, zero `import all`):
1. Executable DIMACS parser guards (`parseDimacs`, `nvM6UnsatBytes`).
2. Module shape, Gate-1 purity, acyclicity, Cpp/QBE printing, & 4-ISA legalization `#guard`s.
3. `ModuleOk fidStep8Env fidStep8Module`, `fidStep8Env_noExit`, top-level `kissat_solve_bytes`
   `Func.wp` UNSAT soundness + caller memory framing (`XPost := False`) and `(Eq m' ⋆ F_host)`
   host-framed lift, plus concrete `8,192 B` `Mem 64` UNSAT non-vacuity (`r = 20#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityStep8Test

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep8
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem fidStep8_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def fidStep8AuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard fidStep8AuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep8Fns.length == 501
#guard (fidStep8Fns.map Fn.name).eraseDups.length == 501
#guard fidStep8Module.checkAcyclic == true
#guard fidStep8Module.externs.isEmpty && fidStep8Module.exits.isEmpty
#guard (FullFidelityStep8.fidStep8Repls.map Fn.name) ==
  [ "full_walk_effort_m7", "full_watch_push_slow_m6", "full_watch_push_m6"
  , "full_delete_bin_side", "full_bva_commit" ]
#guard !(fidStep8Fns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidStep8Fns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidStep8Fns.map Fn.name).contains "full_xor_gauss"
#guard (PrintCpp.ppTModule fidStep8Module).isOk
#guard (PrintQbe.module fidStep8Module).isOk
#guard (PrintCpp.ppModule (FullFidelityStep8.fidStep8Repls.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep8.fidStep8Repls.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep8.fidStep8Repls.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep8.fidStep8Repls.map (Fn.legal .x64AVX512))).isOk
#guard FullFidelityStep8.fidStep8Repls.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard FullFidelityStep8.fidStep8Repls.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard FullFidelityStep8.fidStep8Repls.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard FullFidelityStep8.fidStep8Repls.all fun fn =>
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. `fidStep8Module` (`501` fns) Shape, Acyclicity, `Fn.Wf`, & `ModuleOk` -/

/-- `fidStep8Module` has `501` functions, `0` externs, and `0` exits. -/
theorem fidStep8_shape :
    fidStep8Module.fns.length = 501 ∧
    fidStep8Module.externs = [] ∧
    fidStep8Module.exits = [] :=
  ⟨fidStep8Fns_length, fidStep8_externs_empty, fidStep8_noExit⟩

/-- Every function in `fidStep8Module` satisfies `Fn.Wf`. -/
theorem fidStep8_wf : ∀ f ∈ fidStep8Module.fns, f.Wf :=
  fidStep8Module_wf

/-- `fidStep8Module` has an acyclic call graph (`checkAcyclic = true`). -/
theorem fidStep8_acyc : fidStep8Module.checkAcyclic = true :=
  fidStep8Module_acyclic

/-- Every specification in `fidStep8Env` is exit-free (`XPost`-monotone). -/
theorem fidStep8_env_nx :
    ∀ f as bs xs m Q X X',
      fidStep8Env f as bs xs m Q X → fidStep8Env f as bs xs m Q X' :=
  fidStep8Env_noExit

/-- Closed `0`-hook `ModuleOk` for all `501` functions of `fidStep8Module`. -/
theorem fidStep8_mod_ok : ModuleOk fidStep8Env fidStep8Module :=
  fidStep8_moduleOk

/-! ## 4. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness & Host Lift -/

/-- Source-level UNSAT soundness + caller memory framing on `fidStep8Module` (`XPost := False`). -/
theorem fidStep8_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep8Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidStep8_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `fidStep8Module`. -/
theorem fidStep8_host_ok
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
  fidStep8_solve_bytes_host_sound hq hdmem

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidStep8Module` on `nvM6UnsatInitMem`. -/
theorem fidStep8_nv :
    Func.wp fidStep8Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidStep8_unsat_nv

/-! ## 6. Single-Line `<= 100c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms fidStep8_cnf_def
#print axioms fidStep8_shape
#print axioms fidStep8_wf
#print axioms fidStep8_acyc
#print axioms fidStep8_env_nx
#print axioms fidStep8_mod_ok
#print axioms fidStep8_unsat
#print axioms fidStep8_host_ok
#print axioms fidStep8_nv

end LeanQbeTest.T.KissatFidelityStep8Test
