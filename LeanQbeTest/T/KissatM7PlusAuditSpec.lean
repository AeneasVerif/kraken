/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyPart1
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl
public import LeanQbe.T.MainInline
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl
meta import LeanQbe.T.Examples.LratBytes

/-!
# Kissat M7Plus (`FullM7Plus`, `410` fns) Top-Level Source & Inline-Policy WP Audit

This standalone audit file covers the **architecture-independent C0 + PGO-inlined IR verification**
of Target B (`FullM7Plus` / `PLUS_T8_tie1_bb20`, `410` functions, UNSAT-only, zero SAT model proofs,
zero `@[expose]`, zero target-architecture imports):

1. **Module shape & `0`-hook closure (`m7PlusModule`, `410` fns):** `0` externs, `0` exits,
   `checkAcyclic = true`, all `410` functions `Fn.Wf`, `m7PlusEnv_noExit`, and closed
   `ModuleOk m7PlusEnv m7PlusModule`.
2. **Verified PGO inlining + renormalization (`m7PlusInlMod`):** `m7PlusInlMod =
   m7PlusModule.optInlinePolicy m7InlPolicy`, preserving `410` functions, `0` externs/exits,
   `checkAcyclic = true`, `Fn.Wf`, and `ModuleOk m7PlusEnv m7PlusInlMod` via
   `Module.optInlinePolicy_ok`.
3. **Top-level `kissat_solve_bytes` `Func.wp` UNSAT soundness on both modules:** On both
   `m7PlusModule` (`FullM6Orch.kissat_solve_bytes_body`) and `m7PlusInlMod`
   (`m7PlusInlC12.fn.f19.body`), for any caller DIMACS bytes, workspace, fuel, and frame `R`:
   the return code satisfies `r = 0#64 ∨ r = 10#64 ∨ r = 20#64`, `r = 20#64` proves
   `∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`, and the caller memory frame
   `(bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R)` is preserved (`XPost := False`).
4. **Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`):** Deterministic concrete execution of
   `kissat_solve_bytes` on `nvM6UnsatInitMem` (`8,192 B`) reaches `r = 20#64 ∧ nvM6UnsatCnf.Unsat`
   on both `m7PlusModule` and `m7PlusInlMod`.

## Explicit Scope Boundary (No Machine-Code / `LinkedCert` Claims Here)

* **Not claimed here:** This file proves **WP + PGO-inlining IR correctness only**. It makes
  **zero claims of kernel-checked native compilation (`compileModule` / `LinkedCert`) or x86-64 /
  AArch64 machine-code execution**. Those dual-arch certificates (`LeanQbe/T/{Amd64,Arm64}/
  KissatM7Plus*.lean`, audited in `KissatM7PlusAudit{X64,Arm64}.lean`) are delivered separately.
* **TCB for this file:** Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`),
  `Std.Sat.CNF.Unsat`, `LeanQbe.T.Examples.LratBytes.parseDimacs`, and typed-IR `Func.wp` /
  `ModuleOk` semantics.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7PlusAuditSpec

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof LeanQbe.T.Examples.Kissat.FullM7InlPolicy
open LeanQbe.T.Examples.Kissat.FullM7Plus LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem audit_m7p_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def specAuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard specAuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome

/-! ## 2. `m7PlusModule` (`410` fns) & `m7PlusInlMod` (`optInlinePolicy`) `ModuleOk` -/

/-- `m7PlusModule` has `410` functions, `0` externs, and `0` exits. -/
theorem audit_m7p_shape :
    m7PlusModule.fns.length = 410 ∧
    m7PlusModule.externs = [] ∧
    m7PlusModule.exits = [] :=
  ⟨m7PlusFns_length, rfl, m7Plus_noExit⟩

/-- Every function in `m7PlusModule` satisfies `Fn.Wf`. -/
theorem audit_m7p_wf : ∀ f ∈ m7PlusModule.fns, f.Wf :=
  m7PlusFns_wf

/-- `m7PlusModule` has an acyclic call graph (`checkAcyclic = true`). -/
theorem audit_m7p_acyc : m7PlusModule.checkAcyclic = true :=
  m7Plus_checkAcyclic

/-- Every specification in `m7PlusEnv` is exit-free (`XPost`-monotone). -/
theorem audit_m7p_env_nx :
    ∀ f as bs xs m Q X X',
      m7PlusEnv f as bs xs m Q X → m7PlusEnv f as bs xs m Q X' :=
  m7PlusEnv_noExit

/-- Closed `0`-hook `ModuleOk` for all `410` functions of `m7PlusModule`. -/
theorem audit_m7p_mod_ok : ModuleOk m7PlusEnv m7PlusModule :=
  m7Plus_moduleOk

/-- `m7PlusInlMod` equals `m7PlusModule.optInlinePolicy m7InlPolicy` (`410` fns). -/
theorem audit_m7p_inl_eq :
    m7PlusInlMod = m7PlusModule.optInlinePolicy m7InlPolicy :=
  m7PlusInlMod.eq

/-- `m7PlusInlMod` preserves exact function count (`410`), `0` externs, and `0` exits. -/
theorem audit_m7p_inl_fns :
    m7PlusInlMod.fns.length = 410 ∧
    m7PlusInlMod.externs = [] ∧
    m7PlusInlMod.exits = [] :=
  ⟨m7PlusInlFns_length, rfl, rfl⟩

/-- `m7PlusInlMod` preserves `checkAcyclic = true`. -/
theorem audit_m7p_inl_ac : m7PlusInlMod.checkAcyclic = true :=
  m7PlusInlMod.eq ▸
    Module.optInlinePolicy_checkAcyclic m7InlPolicy m7Plus_checkAcyclic m7PlusFns_wf

/-- Every function in `m7PlusInlMod` satisfies `Fn.Wf`. -/
theorem audit_m7p_inl_wf : ∀ f ∈ m7PlusInlMod.fns, f.Wf :=
  m7PlusInlMod.eq ▸
    Module.optInlinePolicy_wf m7InlPolicy m7Plus_checkAcyclic m7PlusFns_wf

/-- Closed `0`-hook `ModuleOk` lifted across `m7InlPolicy` + `Fn.renorm` to `m7PlusInlMod`. -/
theorem audit_m7p_inl_ok : ModuleOk m7PlusEnv m7PlusInlMod :=
  m7PlusInlMod.eq ▸ Module.optInlinePolicy_ok m7InlPolicy m7Plus_moduleOk

/-! ## 3. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness (Both Modules) -/

/-- Source-level UNSAT soundness + caller memory framing on `m7PlusModule` (`XPost := False`). -/
theorem audit_m7p_unsat
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

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `m7PlusModule`. -/
theorem audit_m7p_host_ok
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

/-- `m7PlusInlC12.fn.f19` is the `"kissat_solve_bytes"` entry point inside `m7PlusInlMod.fns`. -/
theorem audit_m7p_inl_mem :
    m7PlusInlC12.fn.f19 ∈ m7PlusInlMod.fns ∧
    m7PlusInlC12.fn.f19.name = "kissat_solve_bytes" ∧
    m7PlusInlC12.fn.f19.as = [i64, i64, i64, i64, i64] ∧
    m7PlusInlC12.fn.f19.rs = [i64] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  have h1 : m7PlusInlC12.fn.f19 ∈ m7PlusInlC12.fns := by
    unfold m7PlusInlC12.fns; simp only [List.mem_cons, or_true, true_or]
  have h2 : m7PlusInlC12.fns ⊆ m7PlusInlMod.fns := by
    intro x hx
    change x ∈ m7PlusInlFns
    unfold m7PlusInlFns
    iterate 12 apply List.mem_append_right
    exact hx
  exact h2 h1

/-- PGO-inlined UNSAT soundness + caller memory framing on `m7PlusInlMod` (`m7PlusInlC12.fn.f19`,
`XPost := False`). -/
theorem audit_m7p_inl_wp
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m7PlusEnv m7PlusInlC12.fn.f19.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem audit_m7p_inl_mem.1
  have hfn := (audit_m7p_inl_ok.fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (m7PlusEnv_solve_bytes (m7PlusSolveBytesSpec_intro hcfit hwfit hm ?_))
  intro r m' hdom h20 _ hmem
  exact ⟨hdom, h20, hmem⟩

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `m7PlusModule` on `8,192 B` `nvM6UnsatInitMem`. -/
theorem audit_m7p_nv :
    Func.wp m7PlusEnv m6oSolveBytesFn.body
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

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `m7PlusInlMod` (`m7PlusInlC12.fn.f19.body`) on
`8,192 B` `nvM6UnsatInitMem`. -/
theorem audit_m7p_inl_nv :
    Func.wp m7PlusEnv m7PlusInlC12.fn.f19.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem audit_m7p_inl_mem.1
  have hfn := (audit_m7p_inl_ok.fnsOk pre _ post hsplit).2.2
  have hm0 : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ _ _ (fun _ _ _ _ => False)
    (m7PlusEnv_solve_bytes (m7PlusSolveBytesSpec_intro (by decide) (by decide) hm0 ?_))
  intro r m' _ _ htr hm'
  have hr20 : r = 20#64 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound
    (by decide) nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

/-! ## 5. Single-Line `< 115c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms audit_m7p_cnf_def
#print axioms audit_m7p_shape
#print axioms audit_m7p_wf
#print axioms audit_m7p_acyc
#print axioms audit_m7p_env_nx
#print axioms audit_m7p_mod_ok
#print axioms audit_m7p_inl_eq
#print axioms audit_m7p_inl_fns
#print axioms audit_m7p_inl_ac
#print axioms audit_m7p_inl_wf
#print axioms audit_m7p_inl_ok
#print axioms audit_m7p_unsat
#print axioms audit_m7p_host_ok
#print axioms audit_m7p_inl_mem
#print axioms audit_m7p_inl_wp
#print axioms audit_m7p_nv
#print axioms audit_m7p_inl_nv

end LeanQbeTest.T.KissatM7PlusAuditSpec
