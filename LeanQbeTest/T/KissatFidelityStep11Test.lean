/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep11
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Step-11 Top-Level Source Audit (`KissatFidelityStep11Test`)

Architecture-independent C0 IR verification & 4-ISA `#guard` suite of
`FullFidelityAssemblyStep11.fidStep11Module` (`505` fns, `0` externs, `0` exits):
1. Executable DIMACS parser guards (`parseDimacs`, `nvM6UnsatBytes`).
2. Module shape, SysV `<= 6`-arg ABI, Gate-1 purity, acyclicity, Cpp/QBE printing, & 4-ISA
   legalization `#guard`s for Step-11 PR 1 (`8` fns covering `S11-1`, `S11-2`, `S11-4`).
3. `ModuleOk fidStep11Env fidStep11Module`, `fidStep11Env_noExit`, top-level `kissat_solve_bytes`
   `Func.wp` UNSAT soundness + caller memory framing (`XPost := False`) and `(Eq m' ⋆ F_host)`
   host-framed lift, plus concrete `Mem 64` UNSAT non-vacuity (`fidStep11_unsat_nv`, `r = 20#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityStep11Test

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem fidStep11_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def fidStep11AuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard fidStep11AuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome
#guard (parseDimacs "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList).isSome

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep11Fns.length == 505
#guard (fidStep11Fns.map Fn.name).eraseDups.length == 505
#guard fidStep11Fns.all fun fn => fn.as.length <= 6
#guard fidStep11Module.checkAcyclic == true
#guard fidStep11Module.externs.isEmpty && fidStep11Module.exits.isEmpty
#guard (FullFidelityStep11.fidStep11Pr1Repls.map Fn.name) ==
  [ "full_analyze_rsn_m6_hdr", "full_ana_failed_lit_m6_hdr", "full_min_shrink_m6"
  , "full_analyze", "full_analyze_core_m6", "full_vivify_tier_m6_hdr"
  , "full_switch_mode_m7", "full_preprocess_m6" ]
#guard fidStep11AllBefores.isEmpty
#guard (PrintCpp.ppTModule fidStep11Module).isOk
#guard (PrintQbe.module fidStep11Module).isOk
#guard (PrintCpp.ppModule (FullFidelityStep11.fidStep11Pr1Repls.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep11.fidStep11Pr1Repls.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep11.fidStep11Pr1Repls.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep11.fidStep11Pr1Repls.map (Fn.legal .x64AVX512))).isOk
#guard FullFidelityStep11.fidStep11Pr1Repls.all fun fn =>
  (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard FullFidelityStep11.fidStep11Pr1Repls.all fun fn =>
  (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard FullFidelityStep11.fidStep11Pr1Repls.all fun fn =>
  (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard FullFidelityStep11.fidStep11Pr1Repls.all fun fn =>
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. `fidStep11Module` (`505` fns) Shape, Acyclicity, `Fn.Wf`, & `ModuleOk` -/

/-- `fidStep11Module` has `505` functions, `0` externs, and `0` exits. -/
theorem fidStep11_shape :
    fidStep11Module.fns.length = 505 ∧
    fidStep11Module.externs = [] ∧
    fidStep11Module.exits = [] :=
  ⟨fidStep11Fns_length, fidStep11_externs_empty, fidStep11_noExit⟩

/-- Every function in `fidStep11Module` satisfies `Fn.Wf`. -/
theorem fidStep11_wf : ∀ f ∈ fidStep11Module.fns, f.Wf :=
  fidStep11Module_wf

/-- `fidStep11Module` has an acyclic call graph (`checkAcyclic = true`). -/
theorem fidStep11_acyc : fidStep11Module.checkAcyclic = true :=
  fidStep11Module_acyclic

/-- Every specification in `fidStep11Env` is exit-free (`XPost`-monotone). -/
theorem fidStep11_env_nx :
    ∀ f as bs xs m Q X X',
      fidStep11Env f as bs xs m Q X → fidStep11Env f as bs xs m Q X' :=
  fidStep11Env_noExit

/-- Closed `0`-hook `ModuleOk` for all `505` functions of `fidStep11Module`. -/
theorem fidStep11_mod_ok : ModuleOk fidStep11Env fidStep11Module :=
  fidStep11_moduleOk

/-- Canonical Step-11 `KissatUnsatPkg` supplies a verified `ModuleOk` bundle. -/
theorem fidStep11_pkg_ok :
    ModuleOk fidStep11UnsatPkg.env fidStep11UnsatPkg.mod :=
  fidStep11UnsatPkg.moduleOk

/-! ## 4. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness & Host Lift -/

/-- Source-level UNSAT soundness + caller memory framing on `fidStep11Module` (`XPost := False`). -/
theorem fidStep11_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep11Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidStep11_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `fidStep11Module`. -/
theorem fidStep11_host_ok
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
  fidStep11_solve_bytes_host_sound hq hdmem

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`fidStep11Module`) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidStep11Module` on `nvM6UnsatInitMem`. -/
theorem fidStep11_nv :
    Func.wp fidStep11Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidStep11_unsat_nv

/-! ## 6. Single-Line `< 120c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms fidStep11_cnf_def
#print axioms fidStep11_shape
#print axioms fidStep11_wf
#print axioms fidStep11_acyc
#print axioms fidStep11_env_nx
#print axioms fidStep11_mod_ok
#print axioms fidStep11_pkg_ok
#print axioms fidStep11_unsat
#print axioms fidStep11_host_ok
#print axioms fidStep11_nv

end LeanQbeTest.T.KissatFidelityStep11Test
