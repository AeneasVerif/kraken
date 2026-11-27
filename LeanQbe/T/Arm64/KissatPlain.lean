module

public import LeanQbe.T.Arm64.KissatPlainCert
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# End-to-End AAPCS64 Arm64 Native Correctness for Kissat `D-Plain`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatPlain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.Kissat.KissatPlainCertCommon
open LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatPlainCert Kraken

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `plainModule` under `plainEnv` on `armTarget`. -/
theorem module_fnspec (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (plainEnv f.name f.as f.rs) (plainCert.bound f.name) 0 :=
  plain_module_fnspec_abi arm64KissatAbi plainCert plain_legalSig hh k₀ hc hu hf

/-- Closed end-to-end AAPCS64 Arm64 native machine-code correctness of `plainModule`. -/
theorem solve_arm64_correct (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
        (plainCert.bound "kissat_solve_bytes") ⋆ R) :
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
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
            (plainCert.bound "kissat_solve_bytes") ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hdom, hu', hs, ⟨hcs, hsp'⟩, hm'⟩ =>
      ⟨hpc, hdom, hu', hs, hcs, hsp', hm'⟩)
    (plain_solve_correct_abi arm64KissatAbi plainCert plain_legalSig hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem)

/-- Concise AAPCS64 Arm64 soundness corollary of `solve_arm64_correct`. -/
theorem solve_arm64_sound (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
        (plainCert.bound "kissat_solve_bytes") ⋆ R) :
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
  plain_solve_sound_abi arm64KissatAbi plainCert plain_legalSig hh k₀ hc hu
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
    ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem

end Generic

noncomputable abbrev plainHost : Host := plainCert.host
attribute [local instance] plainHost

abbrev plainArgs (cnfBytes : List UInt8) : Tup Val [i64, i64, i64, i64, i64] :=
  KissatPlainCertCommon.plainArgs cnfBytes

@[expose] noncomputable def plainMachState (cnfBytes : List UInt8) : MachineData :=
  armInit.initState (as := [i64, i64, i64, i64, i64])
    (plainCert.bound "kissat_solve_bytes") (plainPayload cnfBytes) (plainArgs cnfBytes)

@[expose] noncomputable def plainUnsatState0 : MachineData :=
  plainMachState plainNvUnsatBytes

/-- Concrete UNSAT execution of compiled `kissat_solve_bytes` on Kraken AArch64 (`X0 = 20`). -/
theorem arm64_unsat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧ plainNvUnsatCnf.Unsat)
      ⟨plainUnsatState0, Labels.label "kissat_solve_bytes"⟩ :=
  plain_unsat_nv_abi arm64KissatAbi plainCert plain_legalSig

@[expose] noncomputable def plainSatState0 : MachineData :=
  plainMachState plainNvSatBytes

/-- Concrete SAT execution of compiled `kissat_solve_bytes` on Kraken AArch64 (`X0 = 10`). -/
theorem arm64_sat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 10#64 ∧
        ¬ plainNvSatCnf.Unsat ∧ ∃ α, plainNvSatCnf.Sat α)
      ⟨plainSatState0, Labels.label "kissat_solve_bytes"⟩ :=
  plain_sat_nv_abi arm64KissatAbi plainCert plain_legalSig

#guard plainFns.length == 59
#guard plainModule.checkAcyclic == true

end LeanQbe.T.Arm64.KissatPlain
