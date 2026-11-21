module

public import LeanQbe.T.Amd64.KissatFastSched
meta import LeanQbe.T.Amd64.KissatFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) SysV x64 Certificate Test & Axiom Audit

Verifies `LeanQbe.T.Amd64.KissatFastSchedCert` and `LeanQbe.T.Amd64.KissatFastSched` (`schedCert`,
`173` functions, `sched_legalSig`, `mk_module_fnspec`, `solve_x64_of_fnspec`,
`sched_solve_bytes_unsat_x64`, `sched_solve_bytes_unsat_sound_x64`, `sched_unsat_nonvacuous_x64`)
with zero `Kraken.AArch64` co-imports and single-line `#print axioms` checks.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatFastSchedCertTest

open Std.Sat
open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatFastSchedCert
open LeanQbe.T.Amd64.KissatFastSched
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched

#guard schedCert.numChunks > 0
#guard schedCert.bound "kissat_solve_bytes" == 1112
#guard schedCert.bound "full_sweep_bins" == 232
#guard schedCert.bound "full_substitute" == 616
#guard schedCert.bound "full_enter_dense" == 568
#guard schedCert.bound "full_search" == 1080
#guard schedCert.bound "full_preprocess" == 1080

theorem audit_unsat [Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
            (kissatFastSched_compiled_x64.bound "kissat_solve_bytes"))
          (kissatFastSched_compiled_x64.bound "kissat_solve_bytes") ⋆
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
              (kissatFastSched_compiled_x64.bound "kissat_solve_bytes"))
            (kissatFastSched_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  sched_solve_bytes_unsat_x64 hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

theorem audit_unsat_sound [Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
            (kissatFastSched_compiled_x64.bound "kissat_solve_bytes"))
          (kissatFastSched_compiled_x64.bound "kissat_solve_bytes") ⋆
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
  sched_solve_bytes_unsat_sound_x64 hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

theorem audit_nonvac [Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
              (kissatFastSched_compiled_x64.bound "kissat_solve_bytes"))
            (kissatFastSched_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  sched_unsat_nonvacuous_x64 hmok k₀ hc hu

#print axioms KissatFastSchedCert.schedCert
#print axioms KissatFastSchedCert.sched_legalSig
#print axioms KissatFastSchedCert.mk_module_fnspec
#print axioms KissatFastSchedCert.solve_x64_of_fnspec
#print axioms KissatFastSched.sched_module_fnspec
#print axioms audit_unsat
#print axioms audit_unsat_sound
#print axioms audit_nonvac

end LeanQbeTest.T.KissatFastSchedCertTest
