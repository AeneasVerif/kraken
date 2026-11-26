/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.KissatM7Fidelity
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl

/-!
# Kissat M7Fidelity (`413` fns, `m7InlPolicy`) Audit: SysV x86-64 machine-code theorems

Standalone UNSAT-only audit restating, with every hypothesis and postcondition written out in
full, the end-to-end theorems about the **inlined `m7InlPolicy` x86-64 machine code** emitted by
`LeanQbe.T` for `FullM7Fidelity` (`kissat_solve_bytes`, `413` functions). Imports `Kraken.X64`
only (`0` Arm64 imports, zero expose attributes, `0` SAT model proofs).
-/

set_option autoImplicit false

public section

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM6 (nvM6CnfPtr nvM6UnsatBytes nvM6UnsatCnf nvM6UnsatWorkPtr)
open LeanQbe.T.Examples.Kissat.FullM7Fidelity (m7FidelityEnv m7FidelityModule)
open LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatM7Fidelity
  (kissatM7Fidelity_compiled_x64 m7Fidelity_module_fnspec m7Fidelity_solve_bytes_unsat_x64
    kissat_m7Fidelity_x64_unsat_correct m7Fidelity_x64_unsat_nonvacuous
    m7Fidelity_x64_run_unsat m7FidelityNvWorkLen_eq m7FidelityNvPayload_eq)

/-- Compiled `LinkedCert` alias for `< 115c` x64 axiom audit. -/
noncomputable abbrev audit_m7f_x64_compiled := kissatM7Fidelity_compiled_x64

/-- **`FullM7Fidelity` (`m7InlPolicy`) x86-64 whole-module `Defined` + `FnSpec`** (`413/413`). -/
theorem audit_m7f_x64_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m7FidelityModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (m7FidelityEnv f.name f.as f.rs)
        (kissatM7Fidelity_compiled_x64.bound f.name) 0 :=
  m7Fidelity_module_fnspec k₀ hc hu hf

/-- **`FullM7Fidelity` (`m7InlPolicy`) x86-64 end-to-end UNSAT soundness + framing**
(`413` fns). -/
theorem audit_m7f_x64_unsat [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes") ⋆
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
              (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m7Fidelity_solve_bytes_unsat_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`FullM7Fidelity` (`m7InlPolicy`) x86-64 answer-only UNSAT soundness** (`413` fns). -/
theorem audit_m7f_x64_sound [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes") ⋆
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
  kissat_m7Fidelity_x64_unsat_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`FullM7Fidelity` (`m7InlPolicy`) x86-64 arbitrary-host UNSAT non-vacuity** (`413` fns). -/
theorem audit_m7f_x64_nv [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
              (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m7Fidelity_x64_unsat_nonvacuous k₀ hc hu

/-- **`FullM7Fidelity` (`m7InlPolicy`) x86-64 closed concrete-host UNSAT non-vacuity**
(`413` fns). -/
theorem audit_m7f_x64_nv_closed :
    letI : Host := kissatM7Fidelity_compiled_x64.host
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
              (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  letI : Host := kissatM7Fidelity_compiled_x64.host
  m7Fidelity_x64_unsat_nonvacuous 0
    kissatM7Fidelity_compiled_x64.code_infix_host kissatM7Fidelity_compiled_x64.labelsUnique

/-- **`FullM7Fidelity` (`m7InlPolicy`) x86-64 closed-host concrete UNSAT execution**
(`413` fns). -/
theorem audit_m7f_x64_run_unsat :
    Eventually (x64Target.mach.step kissatM7Fidelity_compiled_x64.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr 6144 ⋆ emp) m') ⋆
          x64Target.Exit x64Init.sp0
            (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i64, i64, i64])
          (kissatM7Fidelity_compiled_x64.bound "kissat_solve_bytes")
          (nvM6UnsatBytes ++ List.replicate 6144 0)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 6144, 16#64, ()))
        (x64Target.mach.labelAddr kissatM7Fidelity_compiled_x64.host "kissat_solve_bytes")) := by
  simpa only [m7FidelityNvWorkLen_eq, m7FidelityNvPayload_eq] using m7Fidelity_x64_run_unsat

#guard LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityFns.length == 413
example : LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns.length = 413 :=
  LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns_length

#print axioms audit_m7f_x64_compiled
#print axioms audit_m7f_x64_fnspec
#print axioms audit_m7f_x64_unsat
#print axioms audit_m7f_x64_sound
#print axioms audit_m7f_x64_nv
#print axioms audit_m7f_x64_nv_closed
#print axioms audit_m7f_x64_run_unsat
