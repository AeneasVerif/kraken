/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep10
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Step-10 Top-Level Source Audit (`KissatFidelityStep10Test`)

Architecture-independent C0 IR verification & 4-ISA `#guard` suite of
`FullFidelityAssemblyStep10.fidStep10Module` (`505` fns, `0` externs, `0` exits):
1. Executable DIMACS parser guards (`parseDimacs`, `nvM6UnsatBytes`).
2. Module shape, SysV `<= 6`-arg ABI, Gate-1 purity, acyclicity, Cpp/QBE printing, & 4-ISA
   legalization `#guard`s for Step-10 replacements (`5` fns) and inserted helper (`1` fn).
3. `ModuleOk fidStep10Env fidStep10Module`, `fidStep10Env_noExit`, top-level `kissat_solve_bytes`
   `Func.wp` UNSAT soundness + caller memory framing (`XPost := False`) and `(Eq m' ⋆ F_host)`
   host-framed lift, plus concrete `Mem 64` UNSAT non-vacuity (`fidStep10_unsat_nv`, `r = 20#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityStep10Test

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem fidStep10_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def fidStep10AuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard fidStep10AuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome
#guard (parseDimacs "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList).isSome

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep10Fns.length == 505
#guard (fidStep10Fns.map Fn.name).eraseDups.length == 505
#guard fidStep10Fns.all fun fn => fn.as.length <= 6
#guard fidStep10Module.checkAcyclic == true
#guard fidStep10Module.externs.isEmpty && fidStep10Module.exits.isEmpty
#guard (FullFidelityStep10.fidStep10Repls.map Fn.name) ==
  [ "full_analyze_core_m6", "full_vivify_tier_m6_hdr", "full_rebuild_watches_nosort_fid"
  , "full_cong_has_clause_k", "full_bve_def_k6_fid" ]
#guard (FullFidelityStep10.fidStep10Befores.flatMap (fun p => p.2.map Fn.name)) ==
  [ "full_learn_clause_m6" ]
#guard (PrintCpp.ppTModule fidStep10Module).isOk
#guard (PrintQbe.module fidStep10Module).isOk
#guard (PrintCpp.ppModule (FullFidelityStep10.fidStep10Repls.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep10.fidStep10Repls.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep10.fidStep10Repls.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep10.fidStep10Repls.map (Fn.legal .x64AVX512))).isOk
#guard FullFidelityStep10.fidStep10Repls.all fun fn =>
  (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard FullFidelityStep10.fidStep10Repls.all fun fn =>
  (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard FullFidelityStep10.fidStep10Repls.all fun fn =>
  (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard FullFidelityStep10.fidStep10Repls.all fun fn =>
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard (FullFidelityStep10.fidStep10Befores.flatMap Prod.snd).all fun fn =>
  (Fn.legal .aarch64 fn).body.isLegal .aarch64 &&
  (Fn.legal .scalar64 fn).body.isLegal .scalar64 &&
  (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2 &&
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. `fidStep10Module` (`505` fns) Shape, Acyclicity, `Fn.Wf`, & `ModuleOk` -/

/-- `fidStep10Module` has `505` functions, `0` externs, and `0` exits. -/
theorem fidStep10_shape :
    fidStep10Module.fns.length = 505 ∧
    fidStep10Module.externs = [] ∧
    fidStep10Module.exits = [] :=
  ⟨fidStep10Fns_length, fidStep10_externs_empty, fidStep10_noExit⟩

/-- Every function in `fidStep10Module` satisfies `Fn.Wf`. -/
theorem fidStep10_wf : ∀ f ∈ fidStep10Module.fns, f.Wf :=
  fidStep10Module_wf

/-- `fidStep10Module` has an acyclic call graph (`checkAcyclic = true`). -/
theorem fidStep10_acyc : fidStep10Module.checkAcyclic = true :=
  fidStep10Module_acyclic

/-- Every specification in `fidStep10Env` is exit-free (`XPost`-monotone). -/
theorem fidStep10_env_nx :
    ∀ f as bs xs m Q X X',
      fidStep10Env f as bs xs m Q X → fidStep10Env f as bs xs m Q X' :=
  fidStep10Env_noExit

/-- Closed `0`-hook `ModuleOk` for all `505` functions of `fidStep10Module`. -/
theorem fidStep10_mod_ok : ModuleOk fidStep10Env fidStep10Module :=
  fidStep10_moduleOk

/-- Canonical Step-10 `KissatUnsatPkg` supplies a verified `ModuleOk` bundle. -/
theorem fidStep10_pkg_ok :
    ModuleOk fidStep10UnsatPkg.env fidStep10UnsatPkg.mod :=
  fidStep10UnsatPkg.moduleOk

/-! ## 4. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness & Host Lift -/

/-- Source-level UNSAT soundness + caller memory framing on `fidStep10Module` (`XPost := False`). -/
theorem fidStep10_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep10Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidStep10_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `fidStep10Module`. -/
theorem fidStep10_host_ok
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
  fidStep10_solve_bytes_host_sound hq hdmem

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`fidStep10Module`) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidStep10Module` on `nvM6UnsatInitMem`. -/
theorem fidStep10_nv :
    Func.wp fidStep10Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidStep10_unsat_nv

/-! ## 6. Single-Line `< 120c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms fidStep10_cnf_def
#print axioms fidStep10_shape
#print axioms fidStep10_wf
#print axioms fidStep10_acyc
#print axioms fidStep10_env_nx
#print axioms fidStep10_mod_ok
#print axioms fidStep10_pkg_ok
#print axioms fidStep10_unsat
#print axioms fidStep10_host_ok
#print axioms fidStep10_nv

end LeanQbeTest.T.KissatFidelityStep10Test
