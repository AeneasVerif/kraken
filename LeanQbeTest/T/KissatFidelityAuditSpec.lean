/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityInl
public import LeanQbe.T.MainInline
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
meta import LeanQbe.T.Examples.LratBytes

/-!
# Canonical Gate-1 `KissatFidelity` Top-Level Source & Inline-Policy WP Audit

Architecture-independent C0 + PGO-inlined IR verification of Step 2 (`FullFidelityAssemblyStep2` =
`FullFidelityBase` + `FullFidelitySweep` + Option-A `FullFidelityBcp`, `471` functions,
`0` externs, `0` exits, UNSAT-only, zero SAT model proofs, zero `@[expose]`, zero target imports):

1. **Module shape & `0`-hook closure (`fidStep2Module`, `471` fns):** `0` externs, `0` exits,
   `checkAcyclic = true`, all `471` functions `Fn.Wf`, `fidStep2Env_noExit`, and closed
   `ModuleOk fidStep2Env fidStep2Module`.
2. **Verified PGO inlining + renormalization (`fidInlMod`):** `fidInlMod =
   fidStep2Module.optInlinePolicy fidInlPolicy`, preserving `471` fns, `0` externs/exits,
   `checkAcyclic = true`, `Fn.Wf`, and `ModuleOk fidStep2Env fidInlMod`.
3. **Top-level `kissat_solve_bytes` `Func.wp` UNSAT soundness on both modules** (`XPost := False`).
4. **Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`):** `8,192 B` `nvM6UnsatInitMem`
   reaches `r = 20#64 ∧ nvM6UnsatCnf.Unsat` on both `fidStep2Module` and `fidInlMod`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityAuditSpec

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityInl

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem fid_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def fidAuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard fidAuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome

/-! ## 2. `fidStep2Module` (`471` fns) & `fidInlMod` (`optInlinePolicy`) `ModuleOk` -/

/-- `fidStep2Module` has `471` functions, `0` externs, and `0` exits. -/
theorem fid_shape :
    fidStep2Module.fns.length = 471 ∧
    fidStep2Module.externs = [] ∧
    fidStep2Module.exits = [] :=
  ⟨fidStep2Fns_length, fidStep2_externs_empty, fidStep2_noExit⟩

/-- Every function in `fidStep2Module` satisfies `Fn.Wf`. -/
theorem fid_wf : ∀ f ∈ fidStep2Module.fns, f.Wf :=
  fidStep2Module_wf

/-- `fidStep2Module` has an acyclic call graph (`checkAcyclic = true`). -/
theorem fid_acyc : fidStep2Module.checkAcyclic = true :=
  fidStep2Module_acyclic

/-- Every specification in `fidStep2Env` is exit-free (`XPost`-monotone). -/
theorem fid_env_nx :
    ∀ f as bs xs m Q X X',
      fidStep2Env f as bs xs m Q X → fidStep2Env f as bs xs m Q X' :=
  fidStep2Env_noExit

/-- Closed `0`-hook `ModuleOk` for all `471` functions of `fidStep2Module`. -/
theorem fid_mod_ok : ModuleOk fidStep2Env fidStep2Module :=
  fidStep2_moduleOk

/-- `fidInlMod` equals `fidStep2Module.optInlinePolicy fidInlPolicy` (`471` fns). -/
theorem fid_inl_eq :
    fidInlMod = fidStep2Module.optInlinePolicy fidInlPolicy :=
  fidInlMod_eq

/-- `fidInlMod` preserves exact function count (`471`), `0` externs, and `0` exits. -/
theorem fid_inl_fns :
    fidInlMod.fns.length = 471 ∧
    fidInlMod.externs = [] ∧
    fidInlMod.exits = [] :=
  ⟨fidInlFns_length, fidInlMod_externs, fidInlMod_exits⟩

/-- `fidInlMod` preserves `checkAcyclic = true`. -/
theorem fid_inl_ac : fidInlMod.checkAcyclic = true :=
  fidInlMod_acyclic

/-- Every function in `fidInlMod` satisfies `Fn.Wf`. -/
theorem fid_inl_wf : ∀ f ∈ fidInlMod.fns, f.Wf :=
  fidInlMod_wf

/-- Closed `0`-hook `ModuleOk` lifted across `fidInlPolicy` + `Fn.renorm` to `fidInlMod`. -/
theorem fid_inl_ok : ModuleOk fidStep2Env fidInlMod :=
  fidInlMod_ok

/-! ## 3. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness (Both Modules) -/

/-- Source-level UNSAT soundness + caller memory framing on `fidStep2Module` (`XPost := False`). -/
theorem fid_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep2Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidStep2_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `fidStep2Module`. -/
theorem fid_host_ok
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
  fidStep2_solve_bytes_host_sound hq hdmem

/-- `fidInlSolveBytesBody` is the `"kissat_solve_bytes"` entry point inside `fidInlMod.fns`. -/
theorem fid_inl_mem :
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fidInlSolveBytesBody⟩ : Fn) ∈
      fidInlMod.fns :=
  fidInl_solveBytes_mem

/-- PGO-inlined UNSAT soundness + caller memory framing on `fidInlMod` (`XPost := False`). -/
theorem fid_inl_wp
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep2Env fidInlSolveBytesBody
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of_fn fid_inl_ok fid_inl_mem
    (fun _ _ _ _ hs => fidStep2Env_solve_bytes_of hs) hcfit hwfit hm

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidStep2Module` on `8,192 B`
`nvM6UnsatInitMem`. -/
theorem fid_nv :
    Func.wp fidStep2Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidStep2_unsat_nv

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidInlMod` (`fidInlSolveBytesBody`) on
`8,192 B` `nvM6UnsatInitMem`. -/
theorem fid_inl_nv :
    Func.wp fidStep2Env fidInlSolveBytesBody
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of_fn fid_inl_ok fid_inl_mem
    (fun _ _ _ _ hs => fidStep2Env_solve_bytes_of hs)

/-! ## 5. Single-Line `<= 100c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms fid_cnf_def
#print axioms fid_shape
#print axioms fid_wf
#print axioms fid_acyc
#print axioms fid_env_nx
#print axioms fid_mod_ok
#print axioms fid_inl_eq
#print axioms fid_inl_fns
#print axioms fid_inl_ac
#print axioms fid_inl_wf
#print axioms fid_inl_ok
#print axioms fid_unsat
#print axioms fid_host_ok
#print axioms fid_inl_mem
#print axioms fid_inl_wp
#print axioms fid_nv
#print axioms fid_inl_nv

end LeanQbeTest.T.KissatFidelityAuditSpec
