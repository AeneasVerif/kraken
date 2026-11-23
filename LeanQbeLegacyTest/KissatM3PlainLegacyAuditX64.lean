module

public import LeanQbe.T.Amd64.KissatPlain
public import LeanQbe.T.Amd64.KissatM3
meta import LeanQbe.T.Examples.Kissat.PlainLemmas
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat legacy audit: retired `D-Plain` and `D-Full M3` SysV x86-64 machine-code theorems

Standalone legacy audit restating, with every hypothesis and postcondition written out in full
(no wrapper `abbrev`s introduced here), the end-to-end theorems about the **x86-64 machine code**
that `LeanQbe.T` emits for the retired `D-Plain` and `D-Full M3` Kissat builds
(`kissat_solve_bytes`). It imports `Kraken.X64` only (never `Kraken.AArch64`);
`KissatM3PlainLegacyAuditArm64.lean` is the AArch64 mirror, and `KissatLegacyAuditX64.lean` audits
the earlier `D-Full` and `D-Full M2 Fast` legacy builds.

* **`D-Plain`** (`LeanQbe.T.Amd64.KissatPlain`, `59` fns): **SAT (`10`) and UNSAT (`20`)**
  soundness + closed concrete-host non-vacuity (`plainCert.host`), unconditional.
* **`D-Full M3`** (`LeanQbe.T.Amd64.KissatM3`, `204` fns): **UNSAT (`20`)** soundness + both
  arbitrary-host and closed concrete-host (`kissatM3_compiled_x64.host`) non-vacuity, unconditional
  (model reconstruction after inprocessing is intentionally unverified on `D-Full M3`).
-/

set_option autoImplicit false

public section

open Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Amd64 Kraken

/-! ## 1. `D-Plain` (59 functions, CDCL): SAT and UNSAT, unconditional -/

/-- **`D-Plain` x86-64 end-to-end correctness** (`KissatPlain.solve_x64_correct`): for any host
containing the compiled module and any well-formed SysV call, the machine code returns to `ra`
with `rax ∈ {0, 10, 20}`; `20` certifies UNSAT and `10` certifies SAT of `parseDimacs cnfBytes`;
`rbx, rbp, r12..r15` are preserved, `rsp` is `+8`, `cnfBytes` are read-only, the workspace and
stack frame are restored as `region`s, and the frame `R` is preserved. -/
theorem audit_plain_x64_correct [Host] (k₀ : Nat)
    (hc : KissatPlainCert.plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
      (region (s.regs.get64 .rsp -
            BitVec.ofNat 64 (KissatPlainCert.plainCert.bound "kissat_solve_bytes"))
          (KissatPlainCert.plainCert.bound "kissat_solve_bytes") ⋆
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
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (KissatPlainCert.plainCert.bound "kissat_solve_bytes"))
            (KissatPlainCert.plainCert.bound "kissat_solve_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  KissatPlain.solve_x64_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
    hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Plain` x86-64 UNSAT non-vacuity** (`KissatPlain.x64_unsat_nonvacuous`): in the concrete
host `plainCert.host`, starting from the standard initial state with `p cnf 1 2 / 1 0 / -1 0` at
`0x1000`, a 2048-byte workspace right after it, fuel 16 and return address `0x1234`, the machine
code really returns `rax = 20`, and the input really parses to an unsatisfiable CNF. -/
theorem audit_plain_x64_unsat_nonvacuous :
    letI : Host := KissatPlainCert.plainCert.host
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 20#64 ∧
        parseDimacs Plain.plainNvUnsatBytes = some Plain.plainNvUnsatCnf ∧
        Plain.plainNvUnsatCnf.Unsat)
      ⟨x64Init.initState (as := [i64, i64, i64, i64, i64])
          (KissatPlainCert.plainCert.bound "kissat_solve_bytes")
          (Plain.plainNvUnsatBytes ++ List.replicate 2048 0)
          (0x1000#64, BitVec.ofNat 64 Plain.plainNvUnsatBytes.length,
            0x1000#64 + BitVec.ofNat 64 Plain.plainNvUnsatBytes.length, 2048#64, 16#64, ()),
        Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hrax, hu⟩ => ⟨hpc, hrax, Plain.parseDimacs_plainUnsat, hu⟩)
    KissatPlain.x64_unsat_nonvacuous

/-- **`D-Plain` x86-64 SAT non-vacuity** (`KissatPlain.x64_sat_nonvacuous`): same setting with
`p cnf 1 1 / 1 0`; the machine code really returns `rax = 10`, and the input really parses to a
satisfiable CNF. -/
theorem audit_plain_x64_sat_nonvacuous :
    letI : Host := KissatPlainCert.plainCert.host
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 10#64 ∧
        parseDimacs Plain.plainNvSatBytes = some Plain.plainNvSatCnf ∧
        ¬ Plain.plainNvSatCnf.Unsat ∧ ∃ α, Plain.plainNvSatCnf.Sat α)
      ⟨x64Init.initState (as := [i64, i64, i64, i64, i64])
          (KissatPlainCert.plainCert.bound "kissat_solve_bytes")
          (Plain.plainNvSatBytes ++ List.replicate 2048 0)
          (0x1000#64, BitVec.ofNat 64 Plain.plainNvSatBytes.length,
            0x1000#64 + BitVec.ofNat 64 Plain.plainNvSatBytes.length, 2048#64, 16#64, ()),
        Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hrax, hnu, hs⟩ => ⟨hpc, hrax, Plain.parseDimacs_plainSat, hnu, hs⟩)
    KissatPlain.x64_sat_nonvacuous

/-! ## 2. `D-Full M3` (`Amd64.KissatM3`, `204` fns): UNSAT soundness, unconditional -/

section M3X64

open Std.Sat LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM3 (m3Env m3Module)
open LeanQbe.T.Amd64.KissatM3
  (kissatM3_compiled_x64 m3_module_fnspec m3_solve_bytes_unsat_x64
    m3_solve_bytes_unsat_sound_x64 m3_x64_unsat_nonvacuous)

/-- **`D-Full M3` x86-64 whole-module `Defined` + `FnSpec`** (`204/204`, unconditional). -/
theorem audit_m3_x64_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM3_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m3Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (m3Env f.name f.as f.rs)
        (kissatM3_compiled_x64.bound f.name) 0 :=
  m3_module_fnspec k₀ hc hu hf

/-- **`D-Full M3` x86-64 end-to-end UNSAT soundness + framing** (`204` fns, unconditional). -/
theorem audit_m3_x64_unsat [hh : Host] (k₀ : Nat)
    (hc : kissatM3_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM3_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM3_compiled_x64.bound "kissat_solve_bytes") ⋆
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
              (kissatM3_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM3_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m3_solve_bytes_unsat_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full M3` x86-64 answer-only UNSAT soundness** (`204` fns, unconditional). -/
theorem audit_m3_x64_sound [hh : Host] (k₀ : Nat)
    (hc : kissatM3_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
          (kissatM3_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM3_compiled_x64.bound "kissat_solve_bytes") ⋆
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
  m3_solve_bytes_unsat_sound_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full M3` x86-64 UNSAT non-vacuity** (`204` fns, unconditional). -/
theorem audit_m3_x64_nv [hh : Host] (k₀ : Nat)
    (hc : kissatM3_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
              (kissatM3_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM3_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m3_x64_unsat_nonvacuous k₀ hc hu

/-- **`D-Full M3` x86-64 closed concrete-host UNSAT non-vacuity** (`204` fns): instantiates
`audit_m3_x64_nv` on the concrete compiled host `kissatM3_compiled_x64.host` (`k₀ = 0`). -/
theorem audit_m3_x64_nv_closed :
    letI : Host := kissatM3_compiled_x64.host
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
              (kissatM3_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM3_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  letI : Host := kissatM3_compiled_x64.host
  m3_x64_unsat_nonvacuous 0
    kissatM3_compiled_x64.code_infix_host kissatM3_compiled_x64.labelsUnique

end M3X64

/-! ## 3. Module shapes and `#print axioms` (one line each, standard axioms only) -/

#guard Plain.plainFns.length == 59
#guard FullM3.m3Fns.length == 204

#print axioms audit_plain_x64_correct
#print axioms audit_plain_x64_unsat_nonvacuous
#print axioms audit_plain_x64_sat_nonvacuous
#print axioms audit_m3_x64_fnspec
#print axioms audit_m3_x64_unsat
#print axioms audit_m3_x64_sound
#print axioms audit_m3_x64_nv
#print axioms audit_m3_x64_nv_closed
