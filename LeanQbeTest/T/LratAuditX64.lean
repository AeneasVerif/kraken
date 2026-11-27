module

public import LeanQbe.T.Amd64.LratBytes
import LeanQbe.T.Logic.MemLemmas

/-!
# Untrusted-Bytes LRAT Proof Checker (`LratBytes`) — SysV x86-64 Machine Audit

Self-contained machine-level correctness audit for the compiled 6-function untrusted-bytes
DIMACS + Binary LRAT checker (`lrat_check_bytes`) on SysV x86-64 (`Kraken.X64`).
This module imports only `Kraken.X64` (`LeanQbe.T.Amd64.*`), never `Kraken.AArch64`.

## What This Workstream Proves
1. **Kernel-checked compilation (`audit_compile`)**: `checkCompile` succeeds in a single kernel
   reduction on `lratBytesFns` for `x64Target` within a 2048-byte stack bound.
2. **End-to-end x86-64 soundness (`audit_correct`)**: starting at label `"lrat_check_bytes"` in
   any Kraken x64 `Host` containing `compiled.code` with unique labels, given raw DIMACS bytes at
   `rdi`/`rsi`, raw Binary LRAT bytes at `rdx`/`rcx`, and scratch space at `r8`/`r9`, execution
   eventually returns to `ra` with `rax ∈ {0, 1}`, restores callee-saved registers
   (`rbx`, `rbp`, `r12`..`r15`), restores `rsp := rsp + 8`, preserves both input byte buffers and
   caller memory frame `R`, and guarantees:
   `rax = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`.
3. **Parser-free postcondition corollary (`audit_unsat`)**: for any `ValidDimacsCnf cnf` encoded
   with `encodeDimacs cnf`, `rax = 1 → cnf.Unsat`.
4. **Concrete non-vacuous x86-64 witnesses (`audit_accepts`, `audit_rejects`)**: concrete runs in
   `compiled.host` returning `rax = 1` (with `nvBytesCnf.Unsat`) on a valid proof and `rax = 0` on
   an invalid proof.

## Inputs / Assumptions
* Any `Host` containing `compiled.code` as an infix with `Host.LabelsUnique`.
* Non-wrapping buffer bounds (`ptr + len < 2 ^ 64`), SysV 16-byte stack alignment
  (`(rsp + 8) % 16 = 0`), return address `ra` at `rsp`, and disjoint buffer/stack/frame memory.

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`).
* Kraken x86-64 operational semantics (`Kraken.X64.step1`, `Host.exe`, `MachineData`, `Mem 64`).
* `Std.Sat.CNF.Unsat` and `parseDimacs` (or `encodeDimacs` for `audit_unsat`).
* The entire compiler pipeline (`earlyOpt`, `legal`, `lateOpt`, `Rega.lowerFn`, `x64Target`) is
  **verified**, not in the TCB.
-/

set_option autoImplicit false

public section

namespace LratAuditX64

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Amd64 Kraken

theorem audit_compile :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      lratBytesFns Amd64.LratBytes.lratBytesHints 2048 = true :=
  Amd64.LratBytes.compiled_check

theorem audit_correct [hh : Host] (k₀ : Nat)
    (hc : Amd64.LratBytes.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = prf_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 prfBytes.length)
    (hr8 : s.regs.get64 .r8 = work_ptr)
    (hr9 : s.regs.get64 .r9 = BitVec.ofNat 64 work_len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.LratBytes.compiled.bound "lrat_check_bytes"))
          (Amd64.LratBytes.compiled.bound "lrat_check_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.LratBytes.compiled.bound "lrat_check_bytes"))
            (Amd64.LratBytes.compiled.bound "lrat_check_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  Amd64.LratBytes.lrat_check_bytes_x64_correct (hh := hh) k₀ hc hu
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

theorem audit_unsat [hh : Host] (k₀ : Nat)
    (hc : Amd64.LratBytes.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf : CNF Nat) (hvalid : ValidDimacsCnf cnf)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 (encodeDimacs cnf).length)
    (hrdx : s.regs.get64 .rdx = prf_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 prfBytes.length)
    (hr8 : s.regs.get64 .r8 = work_ptr)
    (hr9 : s.regs.get64 .r9 = BitVec.ofNat 64 work_len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
        region work_ptr work_len) ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.LratBytes.compiled.bound "lrat_check_bytes"))
          (Amd64.LratBytes.compiled.bound "lrat_check_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  Amd64.LratBytes.lrat_check_bytes_x64_unsat (hh := hh) k₀ hc hu cnf hvalid
    cnf_ptr prf_ptr work_ptr prfBytes work_len
    hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

attribute [local instance] Amd64.LratBytes.lratBytesHost in
theorem audit_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1 ∧ nvBytesCnf.Unsat)
      ⟨Amd64.LratBytes.lratBytesAcceptState0, Labels.label "lrat_check_bytes"⟩ :=
  Amd64.LratBytes.lrat_check_bytes_x64_accepts

attribute [local instance] Amd64.LratBytes.lratBytesHost in
theorem audit_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0)
      ⟨Amd64.LratBytes.lratBytesRejectState0, Labels.label "lrat_check_bytes"⟩ :=
  Amd64.LratBytes.lrat_check_bytes_x64_rejects

/-! ## Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_compile
#print axioms audit_correct
#print axioms audit_unsat
#print axioms audit_accepts
#print axioms audit_rejects

end LratAuditX64
