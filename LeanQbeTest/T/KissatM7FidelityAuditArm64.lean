/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Arm64.KissatM7Fidelity
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-!
# Kissat M7Fidelity (`413` fns, `m7InlPolicy`) Audit: AAPCS64 AArch64 machine-code theorems

Standalone UNSAT-only audit restating, with every hypothesis and postcondition written out in
full, the end-to-end theorems about the **inlined `m7InlPolicy` AArch64 machine code** emitted by
`LeanQbe.T` for `FullM7Fidelity` (`kissat_solve_bytes`, `413` functions). Imports `Kraken.AArch64`
only (`0` x64 imports, zero expose attributes, `0` SAT model proofs).
-/

set_option autoImplicit false

public section

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM6 (nvM6CnfPtr nvM6UnsatBytes nvM6UnsatCnf nvM6UnsatWorkPtr)
open LeanQbe.T.Examples.Kissat.FullM7Fidelity (m7FidelityEnv m7FidelityModule)
open LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Arm64.KissatM7Fidelity
  (kissatM7Fidelity_compiled_arm64 m7Fidelity_module_fnspec m7Fidelity_solve_bytes_unsat_arm64
    kissat_m7Fidelity_arm64_unsat_correct m7Fidelity_arm64_unsat_nonvacuous
    m7Fidelity_arm64_run_unsat m7FidelityNvWorkLen_eq m7FidelityNvPayload_eq)

/-- Compiled `LinkedCert` alias for `< 115c` Arm64 axiom audit. -/
noncomputable abbrev audit_m7f_arm_compiled := kissatM7Fidelity_compiled_arm64

/-- **`FullM7Fidelity` (`m7InlPolicy`) AArch64 whole-module `Defined` + `FnSpec`** (`413/413`). -/
theorem audit_m7f_arm_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m7FidelityModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (m7FidelityEnv f.name f.as f.rs)
        (kissatM7Fidelity_compiled_arm64.bound f.name) 0 :=
  m7Fidelity_module_fnspec k₀ hc hu hf

/-- **`FullM7Fidelity` (`m7InlPolicy`) AArch64 end-to-end UNSAT soundness + framing**
(`413` fns). -/
theorem audit_m7f_arm_unsat [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
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
              (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m7Fidelity_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`FullM7Fidelity` (`m7InlPolicy`) AArch64 answer-only UNSAT soundness** (`413` fns). -/
theorem audit_m7f_arm_sound [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  kissat_m7Fidelity_arm64_unsat_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`FullM7Fidelity` (`m7InlPolicy`) AArch64 arbitrary-host UNSAT non-vacuity** (`413` fns). -/
theorem audit_m7f_arm_nv [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m7Fidelity_arm64_unsat_nonvacuous k₀ hc hu

/-- **`FullM7Fidelity` (`m7InlPolicy`) AArch64 closed concrete-host UNSAT non-vacuity**
(`413` fns). -/
theorem audit_m7f_arm_nv_closed :
    letI : Host := kissatM7Fidelity_compiled_arm64.host
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
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  letI : Host := kissatM7Fidelity_compiled_arm64.host
  m7Fidelity_arm64_unsat_nonvacuous 0
    kissatM7Fidelity_compiled_arm64.code_infix_host kissatM7Fidelity_compiled_arm64.labelsUnique

/-- **`FullM7Fidelity` (`m7InlPolicy`) AArch64 closed-host concrete UNSAT execution**
(`413` fns). -/
theorem audit_m7f_arm_run_unsat :
    Eventually (armTarget.mach.step kissatM7Fidelity_compiled_arm64.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr 6144 ⋆ emp) m') ⋆
          armTarget.Exit armInit.sp0
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64, i64, i64])
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes")
          (nvM6UnsatBytes ++ List.replicate 6144 0)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 6144, 16#64, ()))
        (armTarget.mach.labelAddr kissatM7Fidelity_compiled_arm64.host "kissat_solve_bytes")) := by
  simpa only [m7FidelityNvWorkLen_eq, m7FidelityNvPayload_eq] using m7Fidelity_arm64_run_unsat

#guard LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityFns.length == 413
example : LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns.length = 413 :=
  LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns_length

#print axioms audit_m7f_arm_compiled
#print axioms audit_m7f_arm_fnspec
#print axioms audit_m7f_arm_unsat
#print axioms audit_m7f_arm_sound
#print axioms audit_m7f_arm_nv
#print axioms audit_m7f_arm_nv_closed
#print axioms audit_m7f_arm_run_unsat
