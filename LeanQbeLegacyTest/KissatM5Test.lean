module

public import LeanQbe.T.Examples.Kissat.FullM5Proof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5Proof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import Kraken.Mem
import Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for Unified Kissat M5 (`FullM5`, `270/270`)

1. Executable `#guard` checks on `m5Fns` (`270` functions), `m5Module.checkAcyclic`, empty
   exits/externs, concrete `fullNvUnsatBytes` payload bounds, `PrintCpp`, `PrintQbe`, and
   `Fn.legal` / `isLegal` across `.aarch64`, `.scalar64`, `.x64AVX512`, and `.x64AVX2`.
2. Concrete `Mem 64` source-level `Func.wp` sanity check (`m5_unsat_payload`, `XPost := False`,
   canonical `270`-function `m5Env`, strictly UNSAT-only — no SAT / model-finding proofs).
3. Root-namespace short aliases for single-line `#print axioms` audit covering
   `Func.Wf`, acyclicity, `270`-row table metadata, unconditional `270/270` `ModuleOk`
   (`m5Env` & `m5UnsatEnv`), `m5_solve_bytes_correct`, `m5_unsat_nonvacuous`, and
   `m5_fwd_unsat_nonvacuous` (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeLegacyTest.KissatM5Test

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Sanity Checks & Backend Compilation / ISA-Legality Guards -/

#guard m5Fns.length == 270
#guard m5Module.checkAcyclic == true
#guard m5Module.exits.isEmpty && m5Module.externs.isEmpty
#guard m5Module.sigs.length == 270
#guard fullNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard fullFixedBytes 1 + 2 * 40 + 136 + 8 <= 4096
#guard (ppTModule m5Module).isOk
#guard (PrintQbe.module m5Module).isOk
#guard (ppModule (m5Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5Fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m5Fns.map (Fn.legal .x64AVX2))).isOk
#guard m5Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m5Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m5Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m5Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

/-! ## 2. Source-Level `Func.wp` Sanity Check (`XPost = False`, UNSAT-only, `m5Env`) -/

/-- General `m5_solve_bytes_correct` instantiated on `fullNvUnsatBytes` payload (`4096` B). -/
theorem m5_unsat_payload :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m5Env FullM5.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs fullNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m5_solve_bytes_correct (R := emp) (by decide) (by decide)
    (by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide))

end LeanQbeLegacyTest.KissatM5Test

/-! ## 3. Root-Namespace Short Aliases for Single-Line `#print axioms` Audit -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5
open LeanQbeLegacyTest.KissatM5Test

theorem m5_wf_ok : ∀ f ∈ m5Fns, f.Wf := m5Fns_wf

theorem m5_acyclic_ok : m5Module.checkAcyclic = true := m5_acyclic

theorem m5_tbl_noExit : ∀ e ∈ m5SpecTable fullSolveBytesSpec, e.noExit = true :=
  m5SpecTable_noExit fullSolveBytesSpec

theorem m5_tbl_sigs :
    (m5SpecTable fullSolveBytesSpec).map (fun e => (e.name, e.as, e.rs)) =
      m5Fns.map (fun f => (f.name, f.as, f.rs)) :=
  m5SpecTable_sigs fullSolveBytesSpec

theorem m5_tbl_len : (m5SpecTable fullSolveBytesSpec).length = 270 :=
  m5SpecTable_length fullSolveBytesSpec

theorem m5_tbl_nodup : ((m5SpecTable fullSolveBytesSpec).map SpecEntry.name).Nodup :=
  m5SpecTable_nodup fullSolveBytesSpec

theorem m5_mod_ok : ModuleOk m5Env m5Module := m5Env_moduleOk

theorem m5_unsat_mod_ok : ModuleOk m5UnsatEnv m5Module := m5UnsatEnv_moduleOk

theorem m5_solve_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m5Env FullM5.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m5_solve_bytes_correct hcfit hwfit hm

theorem m5_unsat_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m5UnsatEnv FullM5Orch.kissat_solve_bytes_m5_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m5_unsat_nonvacuous

theorem m5_fwd_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m5UnsatEnv FullM5.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m5_fwd_unsat_nonvacuous

theorem m5_unsat_pay :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m5Env FullM5.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs fullNvUnsatBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m5_unsat_payload

#print axioms m5_wf_ok
#print axioms m5_acyclic_ok
#print axioms m5_tbl_noExit
#print axioms m5_tbl_sigs
#print axioms m5_tbl_len
#print axioms m5_tbl_nodup
#print axioms m5_mod_ok
#print axioms m5_unsat_mod_ok
#print axioms m5_solve_ok
#print axioms m5_unsat_nv
#print axioms m5_fwd_nv
#print axioms m5_unsat_pay

end AxiomAudit
