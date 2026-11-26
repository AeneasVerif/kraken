/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Arm64.KissatM5Sound
meta import LeanQbe.T.Examples.Kissat.FullM5
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# Kissat M5 (`D-Full M5`, `270` fns, `InlinePolicy.b5`) UNSAT + SAT Soundness Audit: AAPCS64 Arm64

Standalone audit restating, with every hypothesis and postcondition written out in full, the
end-to-end **AArch64 machine-code** UNSAT (`20`) and constructive SAT (`10`) soundness theorems
for Unified Kissat M5 (`kissat_solve_bytes`, `270` functions). Imports `Kraken.AArch64` only
(never x86-64); `KissatM5SoundAuditX64.lean` is the x86-64 mirror.
-/

set_option autoImplicit false

public section

open Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full (fullAlignPad)
open LeanQbe.T.Examples.Kissat.FullM5 (m5Module)
open LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Arm64.KissatM5 (kissatM5_compiled_arm64)
open LeanQbe.T.Arm64.KissatM5Sound
  (m5_sound_module_fnspec m5_solve_bytes_model_arm64 m5_solve_bytes_sound_arm64
    m5_solve_bytes_model_only_arm64 m5_solve_bytes_sound_only_arm64)

/-- **`D-Full M5` (`b5`)** AArch64 `Defined` + `FnSpec` (`270/270`, UNSAT + SAT `m5SoundEnv`). -/
theorem audit_m5_arm_sat_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM5_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m5Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (m5SoundEnv f.name f.as f.rs)
        (kissatM5_compiled_arm64.bound f.name) 0 :=
  m5_sound_module_fnspec k₀ hc hu hf

/-- **`D-Full M5` (`b5`)** AArch64 UNSAT + constructive SAT model soundness + framing
(`270` fns). -/
theorem audit_m5_arm_model [hh : Host] (k₀ : Nat)
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
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            cnf.Sat (readModelFromWork st.data.dmem work_ptr)) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
            .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m5_solve_bytes_model_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full M5` (`b5`)** AArch64 UNSAT + existential SAT soundness + framing (`270` fns). -/
theorem audit_m5_arm_sat_sound [hh : Host] (k₀ : Nat)
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
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
            .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m5_solve_bytes_sound_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full M5` (`b5`)** AArch64 answer-only UNSAT + constructive SAT model soundness
corollary. -/
theorem audit_m5_arm_model_only [hh : Host] (k₀ : Nat)
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
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            cnf.Sat (readModelFromWork st.data.dmem work_ptr)))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m5_solve_bytes_model_only_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full M5` (`b5`)** AArch64 answer-only UNSAT + existential SAT soundness corollary. -/
theorem audit_m5_arm_sound_only [hh : Host] (k₀ : Nat)
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
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m5_solve_bytes_sound_only_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

#guard FullM5.m5Fns.length == 270
example : FullM5InlB5.m5InlB5Fns.length = 270 := FullM5InlB5.m5InlB5Fns_length

#print axioms audit_m5_arm_sat_fnspec
#print axioms audit_m5_arm_model
#print axioms audit_m5_arm_sat_sound
#print axioms audit_m5_arm_model_only
#print axioms audit_m5_arm_sound_only
