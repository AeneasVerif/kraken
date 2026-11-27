module

public import LeanQbe.T.Examples.LratBytesLemmas
public import LeanQbe.T.PrintCpp
import LeanQbe.T.Logic.MemLemmas
meta import LeanQbe.T.Legal
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.LratBytesSpec

/-!
# Untrusted-Bytes LRAT Proof Checker (`LratBytes`) — Source & Pure Specification Audit

Self-contained specification and typed-IR correctness audit for the 6-function untrusted-bytes
DIMACS + Binary LRAT proof checker `lratBytesModule`. Architecture-independent (imports neither
`Kraken.X64` nor `Kraken.AArch64`).

## What This Workstream Proves
1. **DIMACS encoder/parser round-trip (`audit_parse_enc`)**: for any `ValidDimacsCnf cnf`,
   `parseDimacs (encodeDimacs cnf) = some cnf`.
2. **Pure checker soundness (`audit_pure_sound`)**: whenever `runLratCheckBytes` accepts raw
   DIMACS bytes `cnfBytes` and raw Binary LRAT bytes `prfBytes` within `work_len` bytes of
   scratch memory, `parseDimacs cnfBytes = some cnf` and `cnf.Unsat` (`Std.Sat.CNF.Unsat`).
3. **Typed-IR functional correctness (`audit_ir_correct`, `audit_ir_encoded`, `audit_ir_exact`)**:
   executing `lratCheckBytes` in `lratBytesEnv` on raw byte arrays in memory terminates without
   abnormal exits (`X = False`), returns `r ∈ {0, 1}`, proves `r = 1 → ∃ cnf, parseDimacs
   cnfBytes = some cnf ∧ cnf.Unsat` (or directly `r = 1 → cnf.Unsat` for `encodeDimacs cnf`),
   and preserves both input buffers and the caller frame `R`.
4. **Closed module soundness & well-formedness (`audit_wf`, `audit_module_ok`)**: every function in
   `lratBytesFns` satisfies `Fn.Wf`, and `lratBytesModule` satisfies `ModuleOk lratBytesEnv`.
5. **Non-vacuity (`audit_accepts`, `audit_rejects`, `audit_nv_unsat`)**: concrete accepting
   (`r = 1 ∧ nvBytesCnf.Unsat`) and rejecting (`r = 0`) source executions on concrete memory.

## Inputs / Assumptions
* Arbitrary raw byte slices `cnfBytes`, `prfBytes` and scratch buffer `work_len` laid out in
  non-wrapping 64-bit address ranges (`ptr + len < 2 ^ 64`) in disjoint memory regions.
* No trusted parsing outside the verified code: malformed DIMACS headers, out-of-range variables,
  use-after-delete hints, bad tags, SAT formulas, and undersized scratch buffers all return `0`.

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`).
* `Std.Sat.CNF.Unsat` definition from Lean's standard library.
* `parseDimacs` (or `encodeDimacs` for the `ValidDimacsCnf` corollary) defining how raw bytes
  represent a `CNF Nat`, plus `LeanQbe.T.Semantics.wp` (discharged to machine code in
  `LratAuditX64.lean` and `LratAuditArm64.lean`).
-/

set_option autoImplicit false

public section

namespace LratAuditSpec

open Std.ExtHashMap Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Pure Soundness & DIMACS Round-Trip -/

theorem audit_wf : ∀ f ∈ lratBytesFns, Fn.Wf f :=
  lratBytesFns_wf

theorem audit_parse_enc {cnf : CNF Nat} (h : ValidDimacsCnf cnf) :
    parseDimacs (encodeDimacs cnf) = some cnf :=
  parseDimacs_encodeDimacs h

theorem audit_pure_sound {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (hrun : runLratCheckBytes cnfBytes prfBytes work_len = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat :=
  runLratCheckBytes_sound hrun

/-! ## 2. Typed-IR Module & Entry-Point Correctness -/

theorem audit_module_ok : ModuleOk lratBytesEnv lratBytesModule :=
  lratBytesEnv_moduleOk

theorem audit_ir_correct (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat) (R : Mem 64 → Prop) (m : Mem 64)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (hm : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
      region work_ptr work_len) ⋆ R) m) :
    Func.spec lratBytesEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len, ())
      m
      (fun rs m' => ∃ r : BitVec 64, rs = (r, ()) ∧ (r = 0 ∨ r = 1) ∧
        (r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
          region work_ptr work_len) ⋆ R) m')
      (fun _ _ _ _ => False) :=
  lratBytesEnv_sound
    ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩
    (by simp [lratBytesFns]) _ m _ _
    ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, R,
      rfl, hcnf, hprf, hwork, hm, fun r _ hr01 hunsat hm' => ⟨r, rfl, hr01, hunsat, hm'⟩⟩

theorem audit_ir_encoded (cnf : CNF Nat) (hvalid : ValidDimacsCnf cnf)
    (cnf_ptr prf_ptr work_ptr : BitVec 64) (prfBytes : List UInt8) (work_len : Nat)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hcnf : cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (hm : ((Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
      region work_ptr work_len) ⋆ R) m) :
    Func.spec lratBytesEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 (encodeDimacs cnf).length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len, ())
      m
      (fun rs m' => ∃ r : BitVec 64, rs = (r, ()) ∧ (r = 0 ∨ r = 1) ∧
        (r = 1 → cnf.Unsat) ∧
        ((Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
          region work_ptr work_len) ⋆ R) m')
      (fun _ _ _ _ => False) :=
  lratCheckBytes_encoded_correct cnf _ m _ _
    ⟨hvalid, cnf_ptr, prf_ptr, work_ptr, prfBytes, work_len, R,
      rfl, hcnf, hprf, hwork, hm, fun r _ hr01 hunsat hm' => ⟨r, rfl, hr01, hunsat, hm'⟩⟩

theorem audit_ir_exact (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat) (R : Mem 64 → Prop) (m : Mem 64)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (hm : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
      region work_ptr work_len) ⋆ R) m) :
    Func.spec lratBytesExactEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len, ())
      m
      (fun rs m' =>
        rs = (if runLratCheckBytes cnfBytes prfBytes work_len then 1 else 0, ()) ∧
        ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
          region work_ptr work_len) ⋆ R) m')
      (fun _ _ _ _ => False) :=
  lratBytesExactEnv_sound
    ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩
    (by simp [lratBytesFns]) _ m _ _
    ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, R,
      rfl, hcnf, hprf, hwork, hm, fun _ _ hr hm' => ⟨by rw [hr], hm'⟩⟩

/-! ## 3. Non-Vacuous Accepting & Rejecting Source Witnesses -/

theorem audit_nv_unsat : nvBytesCnf.Unsat :=
  nvBytesCnf_unsat

theorem audit_accepts :
    let cnf_ptr : BitVec 64 := 0x1000#64
    let prf_ptr : BitVec 64 := cnf_ptr + BitVec.ofNat 64 nvDimacsBytes.length
    let work_ptr : BitVec 64 := prf_ptr + BitVec.ofNat 64 nvLratAcceptBytes.length
    let m0 : Mem 64 := ((nvDimacsBytes ++ nvLratAcceptBytes) ++ List.replicate 512 0).At cnf_ptr
    Func.spec lratBytesAcceptEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
       work_ptr, 512#64, ())
      m0
      (fun rs m' => rs = (1, ()) ∧ nvBytesCnf.Unsat ∧
        ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆
          region work_ptr 512) ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  lratCheckBytes_accepts

theorem audit_rejects :
    let cnf_ptr : BitVec 64 := 0x1000#64
    let prf_ptr : BitVec 64 := cnf_ptr + BitVec.ofNat 64 nvDimacsBytes.length
    let work_ptr : BitVec 64 := prf_ptr + BitVec.ofNat 64 nvLratRejectBytes.length
    let m0 : Mem 64 := ((nvDimacsBytes ++ nvLratRejectBytes) ++ List.replicate 512 0).At cnf_ptr
    Func.spec lratBytesRejectEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
       work_ptr, 512#64, ())
      m0
      (fun rs m' => rs = (0, ()) ∧
        ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆
          region work_ptr 512) ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  lratCheckBytes_rejects

/-! ## 4. Concrete Symbolic Evaluation Proofs on `encodeDimacs` -/

def cnfEmpty : CNF Nat := CNF.empty

theorem cnfEmpty_dimacs_eq :
    encodeDimacs cnfEmpty = [112, 32, 99, 110, 102, 32, 48, 32, 48, 10] := by
  simp [cnfEmpty, encodeDimacs, cnfMaxVar, natToBytes, natToBytesAux, CNF.empty]

theorem nvBytesCnf_dimacs_eq :
    encodeDimacs nvBytesCnf =
      [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10] := by
  simp [nvBytesCnf, encodeDimacs, cnfMaxVar, encodeDimacsClause, encodeDimacsLit,
    natToBytes, natToBytesAux, CNF.empty, CNF.add]

/-! ## 5. Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_wf
#print axioms audit_parse_enc
#print axioms audit_pure_sound
#print axioms audit_module_ok
#print axioms audit_ir_correct
#print axioms audit_ir_encoded
#print axioms audit_ir_exact
#print axioms audit_nv_unsat
#print axioms audit_accepts
#print axioms audit_rejects

end LratAuditSpec
