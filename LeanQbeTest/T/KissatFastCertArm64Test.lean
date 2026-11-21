module

public import LeanQbe.T.Arm64.KissatFast
meta import LeanQbe.T.Arm64.KissatFast

/-!
# Kissat M2 Unified Fast (`FullFast`, `196` fns) AAPCS64 Arm64 Certificate Test & Axiom Audit

Verifies unconditional `LeanQbe.T.Arm64.KissatFastCert` and `LeanQbe.T.Arm64.KissatFast`
(`fastCert`, `196` functions, `fast_legalSig`, `mk_module_fnspec`, `solve_arm64_of_fnspec`,
`fast_module_fnspec`, `fast_solve_bytes_unsat_arm64`, `fast_solve_bytes_unsat_sound_arm64`,
`fast_unsat_nonvacuous_arm64`) with zero `Kraken.X64` co-imports and single-line `#print axioms`
checks.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatFastCertArm64Test

open Std.Sat
open LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Arm64.KissatFastCert
open LeanQbe.T.Arm64.KissatFast
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFast

#guard fastFns.length == 196
#guard fastCert.numChunks > 0
#guard fastCert.bound "kissat_solve_bytes" == 1184
#guard fastCert.bound "full_prop_lit" == 480
#guard fastCert.bound "full_propagate" == 576
#guard fastCert.bound "full_sweep_bins" == 128
#guard fastCert.bound "full_kitten_solve" == 160
#guard fastCert.bound "full_find_definition" == 320
#guard fastCert.bound "full_bve_var" == 576
#guard fastCert.bound "full_factor" == 720
#guard fastCert.bound "full_preprocess" == 1152
#guard fastCert.bound "full_search" == 1152

theorem audit_unsat [Host] (k₀ : Nat)
    (hc : kissatFast_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatFast_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatFast_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
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
              (kissatFast_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatFast_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  fast_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

theorem audit_sound [Host] (k₀ : Nat)
    (hc : kissatFast_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatFast_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatFast_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  fast_solve_bytes_unsat_sound_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

theorem audit_nonvac [Host] (k₀ : Nat)
    (hc : kissatFast_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
            (kissatFast_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatFast_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  fast_unsat_nonvacuous_arm64 k₀ hc hu

#print axioms KissatFastCert.fastCert
#print axioms KissatFastCert.fast_legalSig
#print axioms KissatFastCert.mk_module_fnspec
#print axioms KissatFastCert.solve_arm64_of_fnspec
#print axioms KissatFast.fast_module_fnspec
#print axioms KissatFast.fast_solve_bytes_unsat_arm64
#print axioms KissatFast.fast_unsat_nonvacuous_arm64
#print axioms audit_unsat
#print axioms audit_sound
#print axioms audit_nonvac

end LeanQbeTest.T.KissatFastCertArm64Test
