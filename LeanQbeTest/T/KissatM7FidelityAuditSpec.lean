/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyPart1
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl
public import LeanQbe.T.MainInline
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation
import Std.Sat.CNF.Basic
import Std.Sat.CNF.Sat
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl
meta import LeanQbe.T.Examples.LratBytes

/-!
# Kissat M7Fidelity (`FullM7Fidelity`, `413` fns) Top-Level Source & Inline-Policy WP Audit

This standalone audit file covers the **architecture-independent C0 + PGO-inlined IR verification**
of Target A (`FullM7Fidelity`, high-fidelity C0 replica of upstream Kissat 4.0.4 on `FullCfg`/
`FullMem`, `413` functions = `410` base + `2` `FullM7FidelityCore` leaf helpers + `1`
`FullM7FidelitySearch` `m6_hdr_decide_fid` helper, omitting `MemShrink` per Option A; UNSAT-only,
zero SAT model proofs, zero `@[expose]`, zero target-architecture imports):

1. **Module shape & `0`-hook closure (`m7FidelityModule`, `413` fns):** `0` externs, `0` exits,
   `checkAcyclic = true`, all `413` functions `Fn.Wf`, `m7FidelityEnv_noExit`, and closed
   `ModuleOk m7FidelityEnv m7FidelityModule`.
2. **Verified PGO inlining + renormalization (`m7FidInlMod`):** `m7FidInlMod =
   m7FidelityModule.optInlinePolicy m7InlPolicy`, preserving `413` functions, `0` externs/exits,
   `checkAcyclic = true`, `Fn.Wf`, and `ModuleOk m7FidelityEnv m7FidInlMod` via
   `Module.optInlinePolicy_ok`.
3. **Top-level `kissat_solve_bytes` `Func.wp` UNSAT soundness on both modules:** On both
   `m7FidelityModule` (`FullM6Orch.kissat_solve_bytes_body`) and `m7FidInlMod`
   (`m7FidInlC12.fn.f22.body`), for any caller DIMACS bytes, workspace, fuel, and frame `R`:
   the return code satisfies `r = 0#64 ∨ r = 10#64 ∨ r = 20#64`, `r = 20#64` proves
   `∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`, and the caller memory frame
   `(bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R)` is preserved (`XPost := False`).
4. **Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`):** Deterministic concrete execution of
   `kissat_solve_bytes` on `nvM6UnsatInitMem` (`8,192 B`) reaches `r = 20#64 ∧ nvM6UnsatCnf.Unsat`
   on both `m7FidelityModule` and `m7FidInlMod`.

## Explicit Scope Boundary (No Machine-Code / `LinkedCert` Claims Here)

* **Not claimed here:** This file proves **WP + PGO-inlining IR correctness only**. It makes
  **zero claims of kernel-checked native compilation (`compileModule` / `LinkedCert`) or x86-64 /
  AArch64 machine-code execution**. Those dual-arch certificates (`LeanQbe/T/{Amd64,Arm64}/
  KissatM7Fidelity*.lean`, audited in `KissatM7FidelityAudit{X64,Arm64}.lean`) are delivered
  separately in Commit 2.
* **TCB for this file:** Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`),
  `Std.Sat.CNF.Unsat`, `LeanQbe.T.Examples.LratBytes.parseDimacs`, and typed-IR `Func.wp` /
  `ModuleOk` semantics.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7FidelityAuditSpec

open Std Std.Sat Std.ExtHashMap Kraken Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof LeanQbe.T.Examples.Kissat.FullM7InlPolicy
open LeanQbe.T.Examples.Kissat.FullM7Fidelity LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-! ## 1. Trusted `Unsat` & DIMACS Parsing Boundary -/

/-- `cnf.Unsat` means every Boolean assignment falsifies `cnf`. -/
theorem m7f_cnf_def (cnf : CNF Nat) :
    cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- Concrete `parseDimacs` executable sanity checks. -/
def specAuditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

#guard specAuditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs nvM6UnsatBytes).isSome

/-! ## 2. `m7FidelityModule` (`413` fns) & `m7FidInlMod` (`optInlinePolicy`) `ModuleOk` -/

/-- `m7FidelityModule` has `413` functions, `0` externs, and `0` exits. -/
theorem m7f_shape :
    m7FidelityModule.fns.length = 413 ∧
    m7FidelityModule.externs = [] ∧
    m7FidelityModule.exits = [] :=
  ⟨m7FidelityFns_length, rfl, m7Fidelity_noExit⟩

/-- Every function in `m7FidelityModule` satisfies `Fn.Wf`. -/
theorem m7f_wf : ∀ f ∈ m7FidelityModule.fns, f.Wf :=
  m7FidelityFns_wf

/-- `m7FidelityModule` has an acyclic call graph (`checkAcyclic = true`). -/
theorem m7f_acyc : m7FidelityModule.checkAcyclic = true :=
  m7Fidelity_checkAcyclic

/-- Every specification in `m7FidelityEnv` is exit-free (`XPost`-monotone). -/
theorem m7f_env_nx :
    ∀ f as bs xs m Q X X',
      m7FidelityEnv f as bs xs m Q X → m7FidelityEnv f as bs xs m Q X' :=
  m7FidelityEnv_noExit

/-- Closed `0`-hook `ModuleOk` for all `413` functions of `m7FidelityModule`. -/
theorem m7f_mod_ok : ModuleOk m7FidelityEnv m7FidelityModule :=
  m7Fidelity_moduleOk

/-- `m7FidInlMod` equals `m7FidelityModule.optInlinePolicy m7InlPolicy` (`413` fns). -/
theorem m7f_inl_eq :
    m7FidInlMod = m7FidelityModule.optInlinePolicy m7InlPolicy :=
  m7FidInlMod.eq

/-- `m7FidInlMod` preserves exact function count (`413`), `0` externs, and `0` exits. -/
theorem m7f_inl_fns :
    m7FidInlMod.fns.length = 413 ∧
    m7FidInlMod.externs = [] ∧
    m7FidInlMod.exits = [] :=
  ⟨m7FidInlFns_length, rfl, rfl⟩

/-- `m7FidInlMod` preserves `checkAcyclic = true`. -/
theorem m7f_inl_ac : m7FidInlMod.checkAcyclic = true :=
  m7FidInlMod.eq ▸
    Module.optInlinePolicy_checkAcyclic m7InlPolicy m7Fidelity_checkAcyclic m7FidelityFns_wf

/-- Every function in `m7FidInlMod` satisfies `Fn.Wf`. -/
theorem m7f_inl_wf : ∀ f ∈ m7FidInlMod.fns, f.Wf :=
  m7FidInlMod.eq ▸
    Module.optInlinePolicy_wf m7InlPolicy m7Fidelity_checkAcyclic m7FidelityFns_wf

/-- Closed `0`-hook `ModuleOk` lifted across `m7InlPolicy` + `Fn.renorm` to `m7FidInlMod`. -/
theorem m7f_inl_ok : ModuleOk m7FidelityEnv m7FidInlMod :=
  m7FidInlMod.eq ▸ Module.optInlinePolicy_ok m7InlPolicy m7Fidelity_moduleOk

/-! ## 3. Top-Level `kissat_solve_bytes` `Func.wp` UNSAT Soundness (Both Modules) -/

/-- Source-level UNSAT soundness + caller memory framing on `m7FidelityModule`
(`XPost := False`). -/
theorem m7f_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m7FidelityEnv m6oSolveBytesFn.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m7Fidelity_solve_bytes_sound hcfit hwfit hm

/-- Host-framed `(Eq m' ⋆ F_host) st_dmem` UNSAT soundness lift for `m7FidelityModule`. -/
theorem m7f_host_ok
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
  m7Fidelity_solve_bytes_host_sound hq hdmem

/-- `m7FidInlC12.fn.f22` is the `"kissat_solve_bytes"` entry point inside `m7FidInlMod.fns`. -/
theorem m7f_inl_mem :
    m7FidInlC12.fn.f22 ∈ m7FidInlMod.fns ∧
    m7FidInlC12.fn.f22.name = "kissat_solve_bytes" ∧
    m7FidInlC12.fn.f22.as = [i64, i64, i64, i64, i64] ∧
    m7FidInlC12.fn.f22.rs = [i64] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  have h1 : m7FidInlC12.fn.f22 ∈ m7FidInlC12.fns := by
    unfold m7FidInlC12.fns; simp only [List.mem_cons, or_true, true_or]
  have h2 : m7FidInlC12.fns ⊆ m7FidInlMod.fns := by
    intro x hx
    change x ∈ m7FidInlFns
    unfold m7FidInlFns
    iterate 12 apply List.mem_append_right
    exact hx
  exact h2 h1

/-- PGO-inlined UNSAT soundness + caller memory framing on `m7FidInlMod` (`m7FidInlC12.fn.f22`,
`XPost := False`). -/
theorem m7f_inl_wp
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m7FidelityEnv m7FidInlC12.fn.f22.body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7f_inl_mem.1
  have hfn := (m7f_inl_ok.fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (m7FidelityEnv_solve_bytes (m7FidSolveBytesSpec_intro hcfit hwfit hm ?_))
  intro r m' hdom h20 _ hmem
  exact ⟨hdom, h20, hmem⟩

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `m7FidelityModule` on `8,192 B`
`nvM6UnsatInitMem`. -/
theorem m7f_nv :
    Func.wp m7FidelityEnv m6oSolveBytesFn.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m7Fidelity_unsat_nv

/-- Concrete UNSAT non-vacuity (`r = 20#64`) for `m7FidInlMod` (`m7FidInlC12.fn.f22.body`) on
`8,192 B` `nvM6UnsatInitMem`. -/
theorem m7f_inl_nv :
    Func.wp m7FidelityEnv m7FidInlC12.fn.f22.body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7f_inl_mem.1
  have hfn := (m7f_inl_ok.fnsOk pre _ post hsplit).2.2
  have hm0 : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ _ _ (fun _ _ _ _ => False)
    (m7FidelityEnv_solve_bytes (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0 ?_))
  intro r m' _ _ htr hm'
  have hr20 : r = 20#64 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound
    (by decide) nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

/-! ## 5. Single-Line `< 115c` `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms m7f_cnf_def
#print axioms m7f_shape
#print axioms m7f_wf
#print axioms m7f_acyc
#print axioms m7f_env_nx
#print axioms m7f_mod_ok
#print axioms m7f_inl_eq
#print axioms m7f_inl_fns
#print axioms m7f_inl_ac
#print axioms m7f_inl_wf
#print axioms m7f_inl_ok
#print axioms m7f_unsat
#print axioms m7f_host_ok
#print axioms m7f_inl_mem
#print axioms m7f_inl_wp
#print axioms m7f_nv
#print axioms m7f_inl_nv

end LeanQbeTest.T.KissatM7FidelityAuditSpec
