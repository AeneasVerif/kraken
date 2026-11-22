module

public import LeanQbe.T.Amd64.KissatM4
meta import LeanQbe.T.Examples.Kissat.FullM4

/-!
# Kissat M4 (`D-Full M4`, 231 functions) Audit: SysV x86-64 machine-code theorems

Standalone audit restating, with every hypothesis and postcondition written out in full (no wrapper
`abbrev`s introduced here), the end-to-end theorems about the **x86-64 machine code** that the
`LeanQbe.T` compiler emits for Unified Kissat M4 (`kissat_solve_bytes`, `231` functions). It imports
`Kraken.X64` only (never `Kraken.AArch64`); `KissatM4AuditArm64.lean` is the AArch64 mirror.

* **`D-Full M4`** (`LeanQbe.T.Amd64.KissatM4`, `231` functions): **UNSAT (`20`)** soundness +
  both arbitrary-host and closed concrete-host (`kissatM4_compiled_x64.host`) non-vacuity,
  unconditional (no SAT/model proofs).
-/

set_option autoImplicit false

public section

open Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM4 (m4Env m4Module)
open LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatM4
  (kissatM4_compiled_x64 m4_module_fnspec m4_solve_bytes_unsat_x64
    m4_solve_bytes_unsat_sound_x64 m4_x64_unsat_nonvacuous)

/-- **`D-Full M4` x86-64 whole-module `Defined` + `FnSpec`** (`231/231`, unconditional). -/
theorem audit_m4_x64_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM4_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m4Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (m4Env f.name f.as f.rs)
        (kissatM4_compiled_x64.bound f.name) 0 :=
  m4_module_fnspec k₀ hc hu hf

/-- **`D-Full M4` x86-64 end-to-end UNSAT soundness + framing** (`231` fns, unconditional). -/
theorem audit_m4_x64_unsat [hh : Host] (k₀ : Nat)
    (hc : kissatM4_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64
          (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM4_compiled_x64.bound "kissat_solve_bytes") ⋆
      cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM4_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m4_solve_bytes_unsat_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full M4` x86-64 answer-only UNSAT soundness** (`231` fns, unconditional). -/
theorem audit_m4_x64_sound [hh : Host] (k₀ : Nat)
    (hc : kissatM4_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64
          (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM4_compiled_x64.bound "kissat_solve_bytes") ⋆
      cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m4_solve_bytes_unsat_sound_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full M4` x86-64 UNSAT non-vacuity** (`231` fns, unconditional). -/
theorem audit_m4_x64_nv [hh : Host] (k₀ : Nat)
    (hc : kissatM4_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      s.regs.get64 .rdi = cnf_ptr ∧
      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧
      s.regs.get64 .rdx = work_ptr ∧
      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧
      s.regs.get64 .r8 = fuel ∧
      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        (region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM4_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m4_x64_unsat_nonvacuous k₀ hc hu

/-- **`D-Full M4` x86-64 closed concrete-host UNSAT non-vacuity** (`231` fns): instantiates
`audit_m4_x64_nv` on the concrete compiled host `kissatM4_compiled_x64.host` (`k₀ = 0`). -/
theorem audit_m4_x64_nv_closed :
    letI : Host := kissatM4_compiled_x64.host
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      s.regs.get64 .rdi = cnf_ptr ∧
      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧
      s.regs.get64 .rdx = work_ptr ∧
      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧
      s.regs.get64 .r8 = fuel ∧
      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        (region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM4_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  letI : Host := kissatM4_compiled_x64.host
  m4_x64_unsat_nonvacuous 0
    kissatM4_compiled_x64.code_infix_host kissatM4_compiled_x64.labelsUnique

#guard FullM4.m4Fns.length == 231

#print axioms audit_m4_x64_fnspec
#print axioms audit_m4_x64_unsat
#print axioms audit_m4_x64_sound
#print axioms audit_m4_x64_nv
#print axioms audit_m4_x64_nv_closed
