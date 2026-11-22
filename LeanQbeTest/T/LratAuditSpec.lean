module

public import LeanQbe.T.Examples.LratBytesLemmas
public import LeanQbe.T.PrintCpp
import all Kraken.Mem
import all Kraken.Separation
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

@[expose] public section

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

/-! ## 4. Concrete `#guard` Sanity Checks (SAT / UNSAT / Malformed / `parseDimacs`) -/

private def unsat2Dimacs : List UInt8 :=
  ("c 2-var unsat\np cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n").toUTF8.toList

private def unsat2AcceptPrf : List UInt8 :=
  [ 0x61, 10, 2, 0, 2, 4, 0
  , 0x64, 2, 4, 0
  , 0x61, 12, 3, 0, 6, 8, 0
  , 0x61, 14, 0, 10, 12, 0 ]

private def unsat2UseAfterDelPrf : List UInt8 :=
  [ 0x64, 2, 0
  , 0x61, 10, 2, 0, 2, 4, 0
  , 0x61, 12, 3, 0, 6, 8, 0
  , 0x61, 14, 0, 10, 12, 0 ]

private def unsat2BadHintPrf : List UInt8 :=
  [ 0x61, 10, 2, 0, 2, 4, 0
  , 0x61, 12, 3, 0, 6, 8, 0
  , 0x61, 14, 0, 10, 0 ]

private def var64Dimacs : List UInt8 :=
  ("p cnf 64 2\n64 0\n-64 0\n").toUTF8.toList

private def var64Leb2AcceptPrf : List UInt8 :=
  [ 0x61, 0x06, 0x80, 0x01, 0x00, 0x02, 0x00
  , 0x61, 0x08, 0x00, 0x06, 0x04, 0x00 ]

private def malformedDimacs : List UInt8 :=
  ("p sat 1 2\n1 0\n-1 0\n").toUTF8.toList

private def oobVarDimacs : List UInt8 :=
  ("p cnf 1 2\n2 0\n-1 0\n").toUTF8.toList

private def sat2Dimacs : List UInt8 :=
  ("p cnf 2 2\n1 2 0\n-1 2 0\n").toUTF8.toList

private def badTagPrf : List UInt8 :=
  [0x78, 0x06, 0x00, 0x02, 0x04, 0x00]

#guard (parseDimacs (encodeDimacs nvBytesCnf)).isSome == true
#guard (parseDimacs malformedDimacs).isNone == true
#guard runLratCheckBytes nvDimacsBytes nvLratAcceptBytes 512 == true
#guard runLratCheckBytes nvDimacsBytes nvLratRejectBytes 512 == false
#guard runLratCheckBytes nvDimacsBytes nvLratAcceptBytes 127 == false
#guard runLratCheckBytes unsat2Dimacs unsat2AcceptPrf 1024 == true
#guard runLratCheckBytes unsat2Dimacs unsat2UseAfterDelPrf 1024 == false
#guard runLratCheckBytes unsat2Dimacs unsat2BadHintPrf 1024 == false
#guard runLratCheckBytes var64Dimacs var64Leb2AcceptPrf 2048 == true
#guard runLratCheckBytes sat2Dimacs nvLratAcceptBytes 512 == false
#guard runLratCheckBytes malformedDimacs nvLratAcceptBytes 512 == false
#guard runLratCheckBytes oobVarDimacs nvLratAcceptBytes 512 == false
#guard runLratCheckBytes nvDimacsBytes badTagPrf 512 == false

/-! ### Skeptical-Auditor Ground-Truth Checks on `encodeDimacs` -/

-- Ground-truth ASCII constant definitional equality verified by the Lean kernel:
example : asciiSpace = (32 : UInt8) := rfl
example : asciiNewline = (10 : UInt8) := rfl
example : asciiMinus = (45 : UInt8) := rfl
example : asciiZero = (48 : UInt8) := rfl
example : dimacsHeaderPrefix = [112, 32, 99, 110, 102, 32] := rfl
example : [asciiZero, asciiNewline] = [48, 10] := rfl

-- Test CNF 1: Empty formula (0 clauses, maxVar 0) ↦ "p cnf 0 0\n"
def cnfEmpty : CNF Nat := CNF.empty

-- Test CNF 2: Multi-digit variable (12 ≥ 10) & mixed polarities ((1 ∨ ¬12) ∧ ¬1)
def cnfMultiDigit : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true), (12, false)])).add
    (CNF.Clause.ofLiterals [(1, false)])

-- Test CNF 3: 3 variables, 3 clauses ((1 ∨ ¬2 ∨ 3) ∧ (2 ∨ ¬3) ∧ ¬1)
def cnf3Var : CNF Nat :=
  ((CNF.empty.add (CNF.Clause.ofLiterals [(1, true), (2, false), (3, true)])).add
    (CNF.Clause.ofLiterals [(2, true), (3, false)])).add
    (CNF.Clause.ofLiterals [(1, false)])

-- Test CNF 4: Empty clause in CNF (immediate UNSAT clause 0\n)
def cnfEmptyClause : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [])

-- Test CNF 5: Large variable indices (≥ 100)
def cnfLargeVar : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(100, true), (250, false)])

-- Helper: extract structural literal lists for deep equality checking
def cnfLits (cnf : CNF Nat) : List (List (Nat × Bool)) :=
  cnf.clauses.toList.map (·.literals)

-- 1. Exact UTF-8 string decoding checks (human-readable standard DIMACS text)
#guard String.fromUTF8? (encodeDimacs cnfEmpty).toByteArray == some "p cnf 0 0\n"
#guard String.fromUTF8? (encodeDimacs nvBytesCnf).toByteArray == some "p cnf 1 2\n1 0\n-1 0\n"
#guard String.fromUTF8? (encodeDimacs cnfMultiDigit).toByteArray ==
  some "p cnf 12 2\n1 -12 0\n-1 0\n"
#guard String.fromUTF8? (encodeDimacs cnf3Var).toByteArray ==
  some "p cnf 3 3\n1 -2 3 0\n2 -3 0\n-1 0\n"
#guard String.fromUTF8? (encodeDimacs cnfEmptyClause).toByteArray == some "p cnf 0 1\n0\n"
#guard String.fromUTF8? (encodeDimacs cnfLargeVar).toByteArray ==
  some "p cnf 250 1\n100 -250 0\n"

-- 2. Exact byte-list equality against String.toUTF8.toList
#guard encodeDimacs cnfEmpty == ("p cnf 0 0\n").toUTF8.toList
#guard encodeDimacs nvBytesCnf == ("p cnf 1 2\n1 0\n-1 0\n").toUTF8.toList
#guard encodeDimacs cnfMultiDigit == ("p cnf 12 2\n1 -12 0\n-1 0\n").toUTF8.toList
#guard encodeDimacs cnf3Var == ("p cnf 3 3\n1 -2 3 0\n2 -3 0\n-1 0\n").toUTF8.toList
#guard encodeDimacs cnfEmptyClause == ("p cnf 0 1\n0\n").toUTF8.toList
#guard encodeDimacs cnfLargeVar == ("p cnf 250 1\n100 -250 0\n").toUTF8.toList

-- 3. Exact symbolic evaluation proofs on ground-truth concrete outputs
theorem cnfEmpty_dimacs_eq :
    encodeDimacs cnfEmpty = [112, 32, 99, 110, 102, 32, 48, 32, 48, 10] := by
  simp [cnfEmpty, encodeDimacs, cnfMaxVar, natToBytes, natToBytesAux, CNF.empty]

theorem nvBytesCnf_dimacs_eq :
    encodeDimacs nvBytesCnf =
      [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10] := by
  simp [nvBytesCnf, encodeDimacs, cnfMaxVar, encodeDimacsClause, encodeDimacsLit,
    natToBytes, natToBytesAux, CNF.empty, CNF.add]

-- 4. Round-trip parser/encoder consistency with structural literal extraction
#guard match parseDimacs (encodeDimacs cnfEmpty) with
  | some res => cnfLits res == cnfLits cnfEmpty
  | none => false
#guard match parseDimacs (encodeDimacs nvBytesCnf) with
  | some res => cnfLits res == cnfLits nvBytesCnf
  | none => false
#guard match parseDimacs (encodeDimacs cnfMultiDigit) with
  | some res => cnfLits res == cnfLits cnfMultiDigit
  | none => false
#guard match parseDimacs (encodeDimacs cnf3Var) with
  | some res => cnfLits res == cnfLits cnf3Var
  | none => false
#guard match parseDimacs (encodeDimacs cnfEmptyClause) with
  | some res => cnfLits res == cnfLits cnfEmptyClause
  | none => false
#guard match parseDimacs (encodeDimacs cnfLargeVar) with
  | some res => cnfLits res == cnfLits cnfLargeVar
  | none => false

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
