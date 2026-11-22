module

public import LeanQbe.T.Arm64.KissatM5
meta import LeanQbe.T.Examples.Kissat.FullM5
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# Kissat M5 (`D-Full M5`, `270` fns, Inlined-`b5`) Audit: AAPCS64 AArch64 machine-code theorems

Standalone audit restating, with every hypothesis and postcondition written out in full (no wrapper
`abbrev`s introduced here), the end-to-end theorems about the **inlined `InlinePolicy.b5` AArch64
machine code** emitted by `LeanQbe.T` for Unified Kissat M5 (`kissat_solve_bytes`, `270`
functions). It imports `Kraken.AArch64` only (zero x86-64 imports); `KissatM5AuditX64.lean` is the
x86-64 mirror.

* **`D-Full M5` (`InlinePolicy.b5`)** (`LeanQbe.T.Arm64.KissatM5`, `270` functions): **UNSAT
  (`20`)** soundness (`Eventually (step1 Host.exe)` + `cnf.Unsat`) + both arbitrary-host and closed
  concrete-host (`kissatM5_compiled_arm64.host`) non-vacuity (`XPost := False`, `std3` axioms),
  unconditional (no SAT/model proofs).
-/

set_option autoImplicit false

public section

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM5 (m5Env m5Module)
open LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Arm64.KissatM5
  (kissatM5_compiled_arm64 m5_module_fnspec m5_solve_bytes_unsat_arm64
    kissat_m5_arm64_unsat_correct m5_arm64_unsat_nonvacuous)

/-- **`D-Full M5` (`b5`) AArch64 whole-module `Defined` + `FnSpec`** (`270/270`, unconditional). -/
theorem audit_m5_arm_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM5_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m5Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (m5Env f.name f.as f.rs)
        (kissatM5_compiled_arm64.bound f.name) 0 :=
  m5_module_fnspec k₀ hc hu hf

/-- **`D-Full M5` (`b5`) AArch64 end-to-end UNSAT soundness + framing** (`270` fns). -/
theorem audit_m5_arm_unsat [hh : Host] (k₀ : Nat)
    (hc : kissatM5_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m5_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full M5` (`b5`) AArch64 answer-only UNSAT soundness** (`270` fns). -/
theorem audit_m5_arm_sound [hh : Host] (k₀ : Nat)
    (hc : kissatM5_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  kissat_m5_arm64_unsat_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full M5` (`b5`) AArch64 arbitrary-host UNSAT non-vacuity** (`270` fns). -/
theorem audit_m5_arm_nv [hh : Host] (k₀ : Nat)
    (hc : kissatM5_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - BitVec.ofNat 64
            (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m5_arm64_unsat_nonvacuous k₀ hc hu

/-- **`D-Full M5` (`b5`) AArch64 closed concrete-host UNSAT non-vacuity** (`270` fns): instantiates
`audit_m5_arm_nv` on the concrete compiled host `kissatM5_compiled_arm64.host` (`k₀ = 0`). -/
theorem audit_m5_arm_nv_closed :
    letI : Host := kissatM5_compiled_arm64.host
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - BitVec.ofNat 64
            (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  letI : Host := kissatM5_compiled_arm64.host
  m5_arm64_unsat_nonvacuous 0
    kissatM5_compiled_arm64.code_infix_host kissatM5_compiled_arm64.labelsUnique

#guard FullM5.m5Fns.length == 270
#guard FullM5InlB5.m5InlB5Fns.length == 270

#print axioms audit_m5_arm_fnspec
#print axioms audit_m5_arm_unsat
#print axioms audit_m5_arm_sound
#print axioms audit_m5_arm_nv
#print axioms audit_m5_arm_nv_closed
