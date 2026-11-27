module

public import LeanQbe.T.Amd64.KissatPlainCert
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# End-to-End SysV x64 Native Correctness for Kissat `D-Plain`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatPlain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.Kissat.KissatPlainCertCommon
open LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatPlainCert Kraken

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `plainModule` under `plainEnv` on `x64Target`. -/
theorem module_fnspec (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (plainEnv f.name f.as f.rs) (plainCert.bound f.name) 0 :=
  plain_module_fnspec_abi x64KissatAbi plainCert plain_legalSig hh k₀ hc hu hf

/-- Closed end-to-end SysV x64 native machine-code correctness of `plainModule`. -/
theorem solve_x64_correct (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
          (plainCert.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (st.data.regs.get64 .rax = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
            (plainCert.bound "kissat_solve_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hdom, hu', hs, ⟨hcs, hsp'⟩, hm'⟩ =>
      ⟨hpc, hdom, hu', hs, hcs, hsp', hm'⟩)
    (plain_solve_correct_abi x64KissatAbi plainCert plain_legalSig hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

/-- Concise SysV x64 soundness corollary of `solve_x64_correct`. -/
theorem solve_x64_sound (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
          (plainCert.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (st.data.regs.get64 .rax = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  plain_solve_sound_abi x64KissatAbi plainCert plain_legalSig hh k₀ hc hu
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem

end Generic

noncomputable abbrev plainHost : Host := plainCert.host
attribute [local instance] plainHost

abbrev plainArgs (cnfBytes : List UInt8) : Tup Val [i64, i64, i64, i64, i64] :=
  KissatPlainCertCommon.plainArgs cnfBytes

@[expose] noncomputable def plainMachState (cnfBytes : List UInt8) : MachineData :=
  x64Init.initState (as := [i64, i64, i64, i64, i64])
    (plainCert.bound "kissat_solve_bytes") (plainPayload cnfBytes) (plainArgs cnfBytes)

@[expose] noncomputable def plainUnsatState0 : MachineData :=
  plainMachState plainNvUnsatBytes

/-- Concrete UNSAT execution of compiled `kissat_solve_bytes` on Kraken x64 (`rax = 20`). -/
theorem x64_unsat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 20#64 ∧ plainNvUnsatCnf.Unsat)
      ⟨plainUnsatState0, Labels.label "kissat_solve_bytes"⟩ :=
  plain_unsat_nv_abi x64KissatAbi plainCert plain_legalSig

@[expose] noncomputable def plainSatState0 : MachineData :=
  plainMachState plainNvSatBytes

/-- Concrete SAT execution of compiled `kissat_solve_bytes` on Kraken x64 (`rax = 10`). -/
theorem x64_sat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 10#64 ∧
        ¬ plainNvSatCnf.Unsat ∧ ∃ α, plainNvSatCnf.Sat α)
      ⟨plainSatState0, Labels.label "kissat_solve_bytes"⟩ :=
  plain_sat_nv_abi x64KissatAbi plainCert plain_legalSig

#guard plainFns.length == 59
#guard plainModule.checkAcyclic == true

end LeanQbe.T.Amd64.KissatPlain
