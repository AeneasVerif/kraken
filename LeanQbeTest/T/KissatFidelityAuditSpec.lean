/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityInl
public import LeanQbe.T.MainInline
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
meta import LeanQbe.T.Examples.LratBytes

/-!
# Canonical Gate-1 `KissatFidelity` Top-Level Source & Inline-Policy WP Audit

Architecture-independent C0 + PGO-inlined IR verification of Step 1 (`FullFidelityAssemblyStep1` =
`FullFidelityBase` + `FullFidelitySweep`, `469` functions, `0` externs, `0` exits, UNSAT-only,
zero SAT model proofs, zero `@[expose]`, zero target-architecture imports):

1. **Module shape & `0`-hook closure (`fidStep1Module`, `469` fns):** `0` externs, `0` exits,
   `checkAcyclic = true`, all `469` functions `Fn.Wf`, `fidStep1Env_noExit`, and closed
   `ModuleOk fidStep1Env fidStep1Module`.
2. **Verified PGO inlining + renormalization (`fidInlMod`):** `fidInlMod =
   fidStep1Module.optInlinePolicy fidInlPolicy`, preserving `469` fns, `0` externs/exits,
   `checkAcyclic = true`, `Fn.Wf`, and `ModuleOk fidStep1Env fidInlMod`.
3. **Top-level `kissat_solve_bytes` `Func.wp` UNSAT soundness on both modules** (`XPost := False`).
4. **Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`):** `8,192 B` `nvM6UnsatInitMem`
   reaches `r = 20#64 ∧ nvM6UnsatCnf.Unsat` on both `fidStep1Module` and `fidInlMod`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityAuditSpec

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
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

/-! ## 2. `fidStep1Module` (`469` fns) & `fidInlMod` (`optInlinePolicy`) `ModuleOk` -/

/-- `fidStep1Module` has `469` functions, `0` externs, and `0` exits. -/
theorem fid_shape :
    fidStep1Module.fns.length = 469 ∧
    fidStep1Module.externs = [] ∧
    fidStep1Module.exits = [] :=
  ⟨fidStep1Fns_length, fidStep1_externs_empty, fidStep1_noExit⟩

/-- Every function in `fidStep1Module` satisfies `Fn.Wf`. -/
theorem fid_wf : ∀ f ∈ fidStep1Module.fns, f.Wf :=
  fidStep1Module_wf

/-- `fidStep1Module` has an acyclic call graph (`checkAcyclic = true`). -/
theorem fid_acyc : fidStep1Module.checkAcyclic = true :=
  fidStep1Module_acyclic

/-- Every specification in `fidStep1Env` is exit-free (`XPost`-monotone). -/
theorem fid_env_nx :
    ∀ f as bs xs m Q X X',
      fidStep1Env f as bs xs m Q X → fidStep1Env f as bs xs m Q X' :=
  fidStep1Env_noExit

/-- Closed `0`-hook `ModuleOk` for all `469` functions of `fidStep1Module`. -/
theorem fid_mod_ok : ModuleOk fidStep1Env fidStep1Module :=
  fidStep1_moduleOk

/-- `fidInlMod` equals `fidStep1Module.optInlinePolicy fidInlPolicy` (`469` fns). -/
theorem fid_inl_eq :
    fidInlMod = fidStep1Module.optInlinePolicy fidInlPolicy :=
  fidInlMod_eq

/-- `fidInlMod` preserves exact function count (`469`), `0` externs, and `0` exits. -/
theorem fid_inl_fns :
    fidInlMod.fns.length = 469 ∧
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
theorem fid_inl_ok : ModuleOk fidStep1Env fidInlMod :=
  fidInlMod_ok

/-! ## 3. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness (Both Modules) -/

/-- Source-level UNSAT soundness + caller memory framing on `fidStep1Module` (`XPost := False`). -/
theorem fid_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep1Env m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidStep1_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `fidStep1Module`. -/
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
  fidStep1_solve_bytes_host_sound hq hdmem

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
    Func.wp fidStep1Env fidInlSolveBytesBody
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of_fn fid_inl_ok fid_inl_mem
    (fun _ _ _ _ hs => fidStep1Env_solve_bytes_of hs) hcfit hwfit hm

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidStep1Module` on `8,192 B`
`nvM6UnsatInitMem`. -/
theorem fid_nv :
    Func.wp fidStep1Env m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidStep1_unsat_nv

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `fidInlMod` (`fidInlSolveBytesBody`) on
`8,192 B` `nvM6UnsatInitMem`. -/
theorem fid_inl_nv :
    Func.wp fidStep1Env fidInlSolveBytesBody
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
    (fun _ _ _ _ hs => fidStep1Env_solve_bytes_of hs)

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
