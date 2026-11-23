/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.KissatM7Plus
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# Kissat M7Plus (`410` fns, `m7InlPolicy`) Audit: SysV x86-64 machine-code theorems

Standalone UNSAT-only audit restating, with every hypothesis and postcondition written out in
full, the end-to-end theorems about the **inlined `m7InlPolicy` x86-64 machine code** emitted by
`LeanQbe.T` for `FullM7Plus` (`kissat_solve_bytes`, `410` functions). Imports `Kraken.X64` only
(`0` Arm64 imports, `0` `@[expose]`, `0` SAT model proofs).
-/

set_option autoImplicit false

public section

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM7Plus (m7PlusEnv m7PlusModule)
open LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatM7Plus
  (kissatM7Plus_compiled_x64 m7Plus_module_fnspec m7Plus_solve_bytes_unsat_x64
    kissat_m7Plus_x64_unsat_correct m7Plus_x64_unsat_nonvacuous m7Plus_x64_run_unsat
    m7PlusNvWorkLen_eq m7PlusNvPayload_eq)

/-- Compiled `LinkedCert` alias for `< 115c` x64 axiom audit. -/
noncomputable abbrev audit_m7p_x64_compiled := kissatM7Plus_compiled_x64

/-- **`FullM7Plus` (`m7InlPolicy`) x86-64 whole-module `Defined` + `FnSpec`** (`410/410`). -/
theorem audit_m7p_x64_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM7Plus_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m7PlusModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (m7PlusEnv f.name f.as f.rs)
        (kissatM7Plus_compiled_x64.bound f.name) 0 :=
  m7Plus_module_fnspec k₀ hc hu hf

/-- **`FullM7Plus` (`m7InlPolicy`) x86-64 end-to-end UNSAT soundness + framing** (`410` fns). -/
theorem audit_m7p_x64_unsat [hh : Host] (k₀ : Nat)
    (hc : kissatM7Plus_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes") ⋆
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
              (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m7Plus_solve_bytes_unsat_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`FullM7Plus` (`m7InlPolicy`) x86-64 answer-only UNSAT soundness** (`410` fns). -/
theorem audit_m7p_x64_sound [hh : Host] (k₀ : Nat)
    (hc : kissatM7Plus_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes") ⋆
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
  kissat_m7Plus_x64_unsat_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`FullM7Plus` (`m7InlPolicy`) x86-64 arbitrary-host UNSAT non-vacuity** (`410` fns). -/
theorem audit_m7p_x64_nv [hh : Host] (k₀ : Nat)
    (hc : kissatM7Plus_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
              (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m7Plus_x64_unsat_nonvacuous k₀ hc hu

/-- **`FullM7Plus` (`m7InlPolicy`) x86-64 closed concrete-host UNSAT non-vacuity** (`410` fns). -/
theorem audit_m7p_x64_nv_closed :
    letI : Host := kissatM7Plus_compiled_x64.host
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
              (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  letI : Host := kissatM7Plus_compiled_x64.host
  m7Plus_x64_unsat_nonvacuous 0
    kissatM7Plus_compiled_x64.code_infix_host kissatM7Plus_compiled_x64.labelsUnique

/-- **`FullM7Plus` (`m7InlPolicy`) x86-64 closed-host concrete UNSAT execution** (`410` fns). -/
theorem audit_m7p_x64_run_unsat :
    Eventually (x64Target.mach.step kissatM7Plus_compiled_x64.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr 6144 ⋆ emp) m') ⋆
          x64Target.Exit x64Init.sp0
            (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i64, i64, i64])
          (kissatM7Plus_compiled_x64.bound "kissat_solve_bytes")
          (nvM6UnsatBytes ++ List.replicate 6144 0)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 6144, 16#64, ()))
        (x64Target.mach.labelAddr kissatM7Plus_compiled_x64.host "kissat_solve_bytes")) := by
  have h := m7Plus_x64_run_unsat
  rw [m7PlusNvPayload_eq, m7PlusNvWorkLen_eq] at h
  exact h

#guard LeanQbe.T.Examples.Kissat.FullM7Plus.m7PlusFns.length == 410
#guard LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns.length == 410

#print axioms audit_m7p_x64_compiled
#print axioms audit_m7p_x64_fnspec
#print axioms audit_m7p_x64_unsat
#print axioms audit_m7p_x64_sound
#print axioms audit_m7p_x64_nv
#print axioms audit_m7p_x64_nv_closed
#print axioms audit_m7p_x64_run_unsat
