module

public import LeanQbe.T.Arm64.LratBytes
import LeanQbe.T.Logic.MemLemmas

/-!
# Untrusted-Bytes LRAT Proof Checker (`LratBytes`) — AAPCS64 AArch64 Machine Audit

Self-contained machine-level correctness audit for the compiled 6-function untrusted-bytes
DIMACS + Binary LRAT checker (`lrat_check_bytes`) on AAPCS64 AArch64 (`Kraken.AArch64`).
This module imports only `Kraken.AArch64` (`LeanQbe.T.Arm64.*`), never `Kraken.X64`.

## What This Workstream Proves
1. **Kernel-checked compilation (`audit_compile`)**: `checkCompile` succeeds in a single kernel
   reduction on `lratBytesFns` for `armTarget` within a 2048-byte stack bound.
2. **End-to-end AArch64 soundness (`audit_correct`)**: starting at label `"lrat_check_bytes"` in
   any Kraken AArch64 `Host` containing `compiled.code` with unique labels, given raw DIMACS bytes
   at `X0`/`X1`, raw Binary LRAT bytes at `X2`/`X3`, and scratch space at `X4`/`X5`, execution
   eventually returns to `X30 = ra` with `X0 ∈ {0, 1}`, restores callee-saved registers
   (`X19`..`X29`) and `SP`, preserves both input byte buffers and caller memory frame `R`, and
   guarantees: `X0 = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`.
3. **Parser-free postcondition corollary (`audit_unsat`)**: for any `ValidDimacsCnf cnf` encoded
   with `encodeDimacs cnf`, `X0 = 1 → cnf.Unsat`.
4. **Concrete non-vacuous AArch64 witnesses (`audit_accepts`, `audit_rejects`)**: concrete runs in
   `compiled.host` returning `X0 = 1` (with `nvBytesCnf.Unsat`) on a valid proof and `X0 = 0` on
   an invalid proof.

## Inputs / Assumptions
* Any `Host` containing `compiled.code` as an infix with `Host.LabelsUnique`.
* Non-wrapping buffer bounds (`ptr + len < 2 ^ 64`), AAPCS64 16-byte stack alignment
  (`SP % 16 = 0`), return address `ra` in `X30`, and disjoint buffer/stack/frame memory.

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`).
* Kraken AArch64 operational semantics (`Kraken.AArch64.step1`, `Host.exe`, `MachineData`,
  `Mem 64`).
* `Std.Sat.CNF.Unsat` and `parseDimacs` (or `encodeDimacs` for `audit_unsat`).
* The entire compiler pipeline (`earlyOpt`, `legal`, `lateOpt`, `Rega.lowerFn`, `armTarget`) is
  **verified**, not in the TCB.
-/

set_option autoImplicit false

public section

namespace LratAuditArm64

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Arm64 Kraken

theorem audit_compile :
    checkCompile armTarget armLayout armLegalTarget [] [] 0
      lratBytesFns Arm64.LratBytes.lratBytesHints 2048 = true :=
  Arm64.LratBytes.compiled_check

theorem audit_correct [hh : Host] (k₀ : Nat)
    (hc : Arm64.LratBytes.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.LratBytes.compiled.bound "lrat_check_bytes"))
        (Arm64.LratBytes.compiled.bound "lrat_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨
          (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.LratBytes.compiled.bound "lrat_check_bytes"))
            (Arm64.LratBytes.compiled.bound "lrat_check_bytes") ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  Arm64.LratBytes.lrat_check_bytes_arm64_correct (hh := hh) k₀ hc hu
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem

theorem audit_unsat [hh : Host] (k₀ : Nat)
    (hc : Arm64.LratBytes.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf : CNF Nat) (hvalid : ValidDimacsCnf cnf)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 (encodeDimacs cnf).length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
        region work_ptr work_len) ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.LratBytes.compiled.bound "lrat_check_bytes"))
        (Arm64.LratBytes.compiled.bound "lrat_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨
          (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  Arm64.LratBytes.lrat_check_bytes_arm64_unsat (hh := hh) k₀ hc hu cnf hvalid
    cnf_ptr prf_ptr work_ptr prfBytes work_len
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem

attribute [local instance] Arm64.LratBytes.lratBytesHost in
theorem audit_accepts :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1 ∧ nvBytesCnf.Unsat)
      ⟨Arm64.LratBytes.lratBytesAcceptState0, Labels.label "lrat_check_bytes"⟩ :=
  Arm64.LratBytes.lrat_check_bytes_arm64_accepts

attribute [local instance] Arm64.LratBytes.lratBytesHost in
theorem audit_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0)
      ⟨Arm64.LratBytes.lratBytesRejectState0, Labels.label "lrat_check_bytes"⟩ :=
  Arm64.LratBytes.lrat_check_bytes_arm64_rejects

/-! ## Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_compile
#print axioms audit_correct
#print axioms audit_unsat
#print axioms audit_accepts
#print axioms audit_rejects

end LratAuditArm64
