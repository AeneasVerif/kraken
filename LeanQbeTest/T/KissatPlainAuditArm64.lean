module

import LeanQbe.T.Arm64.KissatPlain
meta import LeanQbe.T.Examples.Kissat.PlainLemmas

/-!
# Kissat `D-Plain` AAPCS64 AArch64 Machine-Code Audit (`KissatPlainAuditArm64`)

Standalone audit restating, with every hypothesis and postcondition written out in full
(no wrapper `abbrev`s introduced here), the end-to-end theorems about the **AArch64 machine code**
that `LeanQbe.T` emits for the `D-Plain` Kissat solver (`LeanQbe.T.Arm64.KissatPlain`, `59` fns,
entry `kissat_solve_bytes`): **SAT (`10`) and UNSAT (`20`)** soundness + closed concrete-host
non-vacuity (`plainCert.host`), unconditional. Imports `Kraken.AArch64` only (never `Kraken.X64`);
`KissatPlainAuditX64.lean` is the x86-64 mirror.
-/

set_option autoImplicit false

section

open Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Arm64 Kraken

/-! ## 1. `D-Plain` (59 functions, CDCL): SAT and UNSAT, unconditional -/

/-- **`D-Plain` AArch64 end-to-end correctness** (`KissatPlain.solve_arm64_correct`): for any
host containing the compiled module and any well-formed AAPCS64 call, the machine code returns to
`ra` with `X0 ∈ {0, 10, 20}`; `20` certifies UNSAT and `10` certifies SAT of
`parseDimacs cnfBytes`; `X19..X29` and `SP` are preserved, `cnfBytes` are read-only, the
workspace and stack frame are restored as `region`s, and the frame `R` is preserved. -/
theorem audit_plain_arm64_correct [Host] (k₀ : Nat)
    (hc : KissatPlainCert.plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (KissatPlainCert.plainCert.bound "kissat_solve_bytes"))
        (KissatPlainCert.plainCert.bound "kissat_solve_bytes") ⋆ R) :
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
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (KissatPlainCert.plainCert.bound "kissat_solve_bytes"))
            (KissatPlainCert.plainCert.bound "kissat_solve_bytes") ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  KissatPlain.solve_arm64_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
    hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Plain` AArch64 UNSAT non-vacuity** (`KissatPlain.arm64_unsat_nonvacuous`): in the
concrete host `plainCert.host`, starting from the standard initial state with
`p cnf 1 2 / 1 0 / -1 0` at `0x1000`, a 2048-byte workspace right after it, fuel 16 and return
address `0x1234`, the machine code really returns `X0 = 20`, and the input really parses to an
unsatisfiable CNF. -/
theorem audit_plain_arm64_unsat_nonvacuous :
    letI : Host := KissatPlainCert.plainCert.host
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
        parseDimacs Plain.plainNvUnsatBytes = some Plain.plainNvUnsatCnf ∧
        Plain.plainNvUnsatCnf.Unsat)
      ⟨armInit.initState (as := [i64, i64, i64, i64, i64])
          (KissatPlainCert.plainCert.bound "kissat_solve_bytes")
          (Plain.plainNvUnsatBytes ++ List.replicate 2048 0)
          (0x1000#64, BitVec.ofNat 64 Plain.plainNvUnsatBytes.length,
            0x1000#64 + BitVec.ofNat 64 Plain.plainNvUnsatBytes.length, 2048#64, 16#64, ()),
        Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hx0, hu⟩ => ⟨hpc, hx0, Plain.parseDimacs_plainUnsat, hu⟩)
    KissatPlain.arm64_unsat_nonvacuous

/-- **`D-Plain` AArch64 SAT non-vacuity** (`KissatPlain.arm64_sat_nonvacuous`): same setting
with `p cnf 1 1 / 1 0`; the machine code really returns `X0 = 10`, and the input really parses
to a satisfiable CNF. -/
theorem audit_plain_arm64_sat_nonvacuous :
    letI : Host := KissatPlainCert.plainCert.host
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 10#64 ∧
        parseDimacs Plain.plainNvSatBytes = some Plain.plainNvSatCnf ∧
        ¬ Plain.plainNvSatCnf.Unsat ∧ ∃ α, Plain.plainNvSatCnf.Sat α)
      ⟨armInit.initState (as := [i64, i64, i64, i64, i64])
          (KissatPlainCert.plainCert.bound "kissat_solve_bytes")
          (Plain.plainNvSatBytes ++ List.replicate 2048 0)
          (0x1000#64, BitVec.ofNat 64 Plain.plainNvSatBytes.length,
            0x1000#64 + BitVec.ofNat 64 Plain.plainNvSatBytes.length, 2048#64, 16#64, ()),
        Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hx0, hnu, hs⟩ => ⟨hpc, hx0, Plain.parseDimacs_plainSat, hnu, hs⟩)
    KissatPlain.arm64_sat_nonvacuous

/-! ## 2. Module shape and `#print axioms` (one line each, standard axioms only) -/

#guard Plain.plainFns.length == 59

#print axioms audit_plain_arm64_correct
#print axioms audit_plain_arm64_unsat_nonvacuous
#print axioms audit_plain_arm64_sat_nonvacuous
