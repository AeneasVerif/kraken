module

public import LeanQbe.T.Amd64.KissatFast
meta import LeanQbe.T.Amd64.KissatFast

/-!
# Kissat M2 Unified Fast (`FullFast`, `196` fns) SysV x64 Certificate Test & Axiom Audit

Verifies unconditional `LeanQbe.T.Amd64.KissatFastCert` and `LeanQbe.T.Amd64.KissatFast`
(`fastCert`, `196` functions, `fast_legalSig`, `mk_module_fnspec`, `solve_x64_of_fnspec`,
`fast_module_fnspec`, `fast_solve_bytes_unsat_x64`, `fast_solve_bytes_unsat_sound_x64`,
`fast_unsat_nonvacuous_x64`) with zero `Kraken.AArch64` co-imports and single-line
`#print axioms` checks.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeLegacyTest.KissatFastCertTest

open Std.Sat
open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatFastCert
open LeanQbe.T.Amd64.KissatFast
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFast

#guard fastFns.length == 196
example : fastCert.numChunks > 0 := by decide
example : fastCert.bound "kissat_solve_bytes" = 1080 := by decide
example : fastCert.bound "full_prop_lit" = 472 := by decide
example : fastCert.bound "full_propagate" = 536 := by decide
example : fastCert.bound "full_sweep_bins" = 168 := by decide
example : fastCert.bound "full_kitten_solve" = 200 := by decide
example : fastCert.bound "full_find_definition" = 392 := by decide
example : fastCert.bound "full_bve_var" = 632 := by decide
example : fastCert.bound "full_factor" = 728 := by decide
example : fastCert.bound "full_preprocess" = 1000 := by decide
example : fastCert.bound "full_search" = 1032 := by decide

theorem audit_unsat [Host] (k₀ : Nat)
    (hc : kissatFast_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
            (kissatFast_compiled_x64.bound "kissat_solve_bytes"))
          (kissatFast_compiled_x64.bound "kissat_solve_bytes") ⋆
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
              (kissatFast_compiled_x64.bound "kissat_solve_bytes"))
            (kissatFast_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  fast_solve_bytes_unsat_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

theorem audit_unsat_sound [Host] (k₀ : Nat)
    (hc : kissatFast_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
            (kissatFast_compiled_x64.bound "kissat_solve_bytes"))
          (kissatFast_compiled_x64.bound "kissat_solve_bytes") ⋆
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
  fast_solve_bytes_unsat_sound_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

theorem audit_nonvac [Host] (k₀ : Nat)
    (hc : kissatFast_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
              (kissatFast_compiled_x64.bound "kissat_solve_bytes"))
            (kissatFast_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  fast_unsat_nonvacuous_x64 k₀ hc hu

#print axioms KissatFastCert.fastCert
#print axioms KissatFastCert.fast_legalSig
#print axioms KissatFastCert.mk_module_fnspec
#print axioms KissatFastCert.solve_x64_of_fnspec
#print axioms KissatFast.fast_module_fnspec
#print axioms KissatFast.fast_solve_bytes_unsat_x64
#print axioms KissatFast.fast_unsat_nonvacuous_x64
#print axioms audit_unsat
#print axioms audit_unsat_sound
#print axioms audit_nonvac

end LeanQbeLegacyTest.KissatFastCertTest
