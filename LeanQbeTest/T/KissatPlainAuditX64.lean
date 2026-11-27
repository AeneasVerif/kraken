module

public import LeanQbe.T.Amd64.KissatPlain
meta import LeanQbe.T.Examples.Kissat.PlainLemmas

/-!
# Kissat `D-Plain` SysV x86-64 Machine-Code Audit (`KissatPlainAuditX64`)

Standalone audit restating, with every hypothesis and postcondition written out in full
(no wrapper `abbrev`s introduced here), the end-to-end theorems about the **x86-64 machine code**
that `LeanQbe.T` emits for the `D-Plain` Kissat solver (`LeanQbe.T.Amd64.KissatPlain`, `59` fns,
entry `kissat_solve_bytes`): **SAT (`10`) and UNSAT (`20`)** soundness + closed concrete-host
non-vacuity (`plainCert.host`), unconditional. Imports `Kraken.X64` only (never `Kraken.AArch64`);
`KissatPlainAuditArm64.lean` is the AArch64 mirror.
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

/-! ## 2. Module shape and `#print axioms` (one line each, standard axioms only) -/

#guard Plain.plainFns.length == 59

#print axioms audit_plain_x64_correct
#print axioms audit_plain_x64_unsat_nonvacuous
#print axioms audit_plain_x64_sat_nonvacuous
