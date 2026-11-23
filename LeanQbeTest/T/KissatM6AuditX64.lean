module

public import LeanQbe.T.Amd64.KissatM6
meta import LeanQbe.T.Examples.Kissat.FullM6
meta import LeanQbe.T.Examples.Kissat.FullM6Inl

/-!
# Kissat M6 (`D-Full M6`, `382` fns, Inlined-`m6InlPolicy`) Audit: SysV x86-64 machine code

Standalone audit restating, with every hypothesis and postcondition written out in full (no wrapper
`abbrev`s introduced here), the end-to-end theorems about the **inlined `m6InlPolicy` x86-64
machine code** emitted by `LeanQbe.T` for Unified Kissat M6 (`kissat_solve_bytes`, `382`
functions). It imports `Kraken.X64` only (zero AArch64 imports); `KissatM6AuditArm64.lean` is the
AArch64 mirror.

* **`D-Full M6` (`m6InlPolicy`)** (`LeanQbe.T.Amd64.KissatM6`, `382` functions): **UNSAT (`20`)**
  soundness (`Eventually (step1 Host.exe)` + `cnf.Unsat`) + both arbitrary-host and closed
  concrete-host (`kissatM6_compiled_x64.host`) non-vacuity (`XPost := False`, `std3` axioms),
  parameterized over `tPfx` (`FullM6Proof`).
-/

set_option autoImplicit false

public section

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full (fullWarmupSpec)
open LeanQbe.T.Examples.Kissat.FullM6 (m6Module fullM6SolveBytesCoreModelSpec)
open LeanQbe.T.Examples.Kissat.FullM6Orch (m6Orch_fns)
open LeanQbe.T.Examples.Kissat.FullM6Proof (mkM6Env M6OrchPfxTblSpecs)
open LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatM6
  (kissatM6_compiled_x64 m6_module_fnspec m6_solve_bytes_unsat_x64
    kissat_m6_x64_unsat_correct m6_x64_unsat_nonvacuous)

/-- **`D-Full M6` x86-64 whole-module `Defined` + `FnSpec`** (`382/382`, parameterized on `tPfx`).
-/
theorem audit_m6_x64_fnspec
    (tPfx : List SpecEntry)
    (hN : tPfx.all SpecEntry.noExit = true)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X)
    [hh : Host] (k₀ : Nat)
    (hc : kissatM6_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m6Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name
        (mkM6Env tPfx fullM6SolveBytesCoreModelSpec f.name f.as f.rs)
        (kissatM6_compiled_x64.bound f.name) 0 :=
  m6_module_fnspec tPfx hN hS hP hO hK k₀ hc hu hf

/-- **`D-Full M6` x86-64 end-to-end UNSAT soundness + framing** (`382` fns). -/
theorem audit_m6_x64_unsat
    (tPfx : List SpecEntry)
    (hN : tPfx.all SpecEntry.noExit = true)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X)
    [hh : Host] (k₀ : Nat)
    (hc : kissatM6_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆
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
              (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
            ((kissatM6_compiled_x64.bound "kissat_solve_bytes") + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m6_solve_bytes_unsat_x64 tPfx hN hS hP hO hK k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
    hcfit hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full M6` x86-64 answer-only UNSAT soundness** (`382` fns). -/
theorem audit_m6_x64_sound
    (tPfx : List SpecEntry)
    (hN : tPfx.all SpecEntry.noExit = true)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X)
    [hh : Host] (k₀ : Nat)
    (hc : kissatM6_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆
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
  kissat_m6_x64_unsat_correct tPfx hN hS hP hO hK k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
    hcfit hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full M6` x86-64 arbitrary-host UNSAT non-vacuity** (`382` fns). -/
theorem audit_m6_x64_nv
    (tPfx : List SpecEntry)
    (hN : tPfx.all SpecEntry.noExit = true)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X)
    [hh : Host] (k₀ : Nat)
    (hc : kissatM6_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
              (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m6_x64_unsat_nonvacuous tPfx hN hS hP hO hK k₀ hc hu

/-- **`D-Full M6` x86-64 closed concrete-host UNSAT non-vacuity** (`382` fns): instantiates
`audit_m6_x64_nv` on the concrete compiled host `kissatM6_compiled_x64.host` (`k₀ = 0`). -/
theorem audit_m6_x64_nv_closed
    (tPfx : List SpecEntry)
    (hN : tPfx.all SpecEntry.noExit = true)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X) :
    letI : Host := kissatM6_compiled_x64.host
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
              (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  letI : Host := kissatM6_compiled_x64.host
  m6_x64_unsat_nonvacuous tPfx hN hS hP hO hK 0
    kissatM6_compiled_x64.code_infix_host kissatM6_compiled_x64.labelsUnique

#guard FullM6.m6Fns.length == 382
#guard FullM6Inl.m6InlFns.length == 382

#print axioms audit_m6_x64_fnspec
#print axioms audit_m6_x64_unsat
#print axioms audit_m6_x64_sound
#print axioms audit_m6_x64_nv
#print axioms audit_m6_x64_nv_closed
