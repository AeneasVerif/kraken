/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep9
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Canonical Gate-1 `KissatFidelity` Step-9 Top-Level Source Audit (`KissatFidelityStep9Test`)

Architecture-independent C0 IR verification & 4-ISA `#guard` suite of
`FullFidelityAssemblyStep9.fidStep9Module` (`504` fns, `0` externs, `0` exits):
1. Executable DIMACS parser guards (`parseDimacs`, `nvM6UnsatBytes`).
2. Module shape, Gate-1 purity, acyclicity, Cpp/QBE printing, & 4-ISA legalization `#guard`s
   for Step-9 replacements (`11` fns) and inserted helpers (`3` fns).
3. `ModuleOk fidStep9Env fidStep9Module`, `fidStep9Env_noExit`, top-level `kissat_solve_bytes`
   `Func.wp` UNSAT soundness + caller memory framing (`XPost := False`) and `(Eq m' ⋆ F_host)`
   host-framed lift, plus concrete `Mem 64` UNSAT non-vacuity (`fidStep9_unsat_nv`, `r = 20#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityStep9Test

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem fidStep9_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def fidStep9AuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard fidStep9AuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome
#guard (parseDimacs "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList).isSome

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep9Fns.length == 504
#guard (fidStep9Fns.map Fn.name).eraseDups.length == 504
#guard fidStep9Module.checkAcyclic == true
#guard fidStep9Module.externs.isEmpty && fidStep9Module.exits.isEmpty
#guard (FullFidelityStep9.fidStep9Repls.map Fn.name) ==
  [ "full_prop_flush_del_fid", "full_arena_sweep_m6", "full_reduce_m6"
  , "full_congruence_dense", "full_rebuild_watches", "full_bva_commit"
  , "full_bva_upd_lit_fid", "full_factor", "full_compact_needed"
  , "full_compact_flush", "full_probe_m6" ]
#guard (FullFidelityStep9.fidStep9Befores.flatMap (fun p => p.2.map Fn.name)) ==
  [ "full_fill_u64_m7", "full_prop_flush_slow_fid", "full_rebuild_watches_nosort_fid" ]
#guard (PrintCpp.ppTModule fidStep9Module).isOk
#guard (PrintQbe.module fidStep9Module).isOk
#guard (PrintCpp.ppModule (FullFidelityStep9.fidStep9Repls.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep9.fidStep9Repls.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep9.fidStep9Repls.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep9.fidStep9Repls.map (Fn.legal .x64AVX512))).isOk
#guard FullFidelityStep9.fidStep9Repls.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard FullFidelityStep9.fidStep9Repls.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard FullFidelityStep9.fidStep9Repls.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard FullFidelityStep9.fidStep9Repls.all fun fn =>
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard (FullFidelityStep9.fidStep9Befores.flatMap Prod.snd).all fun fn =>
  (Fn.legal .aarch64 fn).body.isLegal .aarch64 &&
  (Fn.legal .scalar64 fn).body.isLegal .scalar64 &&
  (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2 &&
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. `fidStep9Module` (`504` fns) Shape, Acyclicity, `Fn.Wf`, & `ModuleOk` -/

/-- `fidStep9Module` has `504` functions, `0` externs, and `0` exits. -/
theorem fidStep9_shape :
    fidStep9Module.fns.length = 504 ∧
    fidStep9Module.externs = [] ∧
    fidStep9Module.exits = [] :=
  ⟨fidStep9Fns_length, fidStep9_externs_empty, fidStep9_noExit⟩

/-- Every function in `fidStep9Module` satisfies `Fn.Wf`. -/
theorem fidStep9_wf : ∀ f ∈ fidStep9Module.fns, f.Wf :=
  fidStep9Module_wf

/-- `fidStep9Module` has an acyclic call graph (`checkAcyclic = true`). -/
theorem fidStep9_acyc : fidStep9Module.checkAcyclic = true :=
  fidStep9Module_acyclic

/-- Every specification in `fidStep9Env` is exit-free (`XPost`-monotone). -/
theorem fidStep9_env_nx :
    ∀ f as bs xs m Q X X',
      fidStep9Env f as bs xs m Q X → fidStep9Env f as bs xs m Q X' :=
  fidStep9Env_noExit

/-- Closed `0`-hook `ModuleOk` for all `504` functions of `fidStep9Module`. -/
theorem fidStep9_mod_ok : ModuleOk fidStep9Env fidStep9Module :=
  fidStep9_moduleOk

/-- Canonical Step-9 `KissatUnsatPkg` supplies a verified `ModuleOk` bundle. -/
theorem fidStep9_pkg_ok :
    ModuleOk fidStep9UnsatPkg.env fidStep9UnsatPkg.mod :=
  fidStep9UnsatPkg.moduleOk

/-! ## 4. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness & Host Lift -/

/-- Source-level UNSAT soundness + caller memory framing on `fidStep9Module` (`XPost := False`). -/
theorem fidStep9_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep9Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidStep9_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `fidStep9Module`. -/
theorem fidStep9_host_ok
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
  fidStep9_solve_bytes_host_sound hq hdmem

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`fidStep9Module`) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidStep9Module` on `nvM6UnsatInitMem`. -/
theorem fidStep9_nv :
    Func.wp fidStep9Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidStep9_unsat_nv

/-! ## 6. Single-Line `< 120c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms fidStep9_cnf_def
#print axioms fidStep9_shape
#print axioms fidStep9_wf
#print axioms fidStep9_acyc
#print axioms fidStep9_env_nx
#print axioms fidStep9_mod_ok
#print axioms fidStep9_pkg_ok
#print axioms fidStep9_unsat
#print axioms fidStep9_host_ok
#print axioms fidStep9_nv

end LeanQbeTest.T.KissatFidelityStep9Test
