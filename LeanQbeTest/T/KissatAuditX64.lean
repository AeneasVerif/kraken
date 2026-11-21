module

public import LeanQbe.T.Amd64.KissatPlain
public import LeanQbe.T.Amd64.KissatFull
meta import LeanQbe.T.Examples.Kissat.PlainLemmas
meta import LeanQbe.T.Examples.Kissat.FullSpec

/-!
# Kissat audit, part 2: SysV x86-64 machine-code theorems

This file is meant to be read by a human auditor. It restates, with every hypothesis and
postcondition written out in full (no wrapper `abbrev`s introduced here), the end-to-end theorems
about the **x86-64 machine code** that the `LeanQbe.T` compiler emits for `kissat_solve_bytes`,
and proves each restatement by the corresponding library theorem. It imports `Kraken.X64` only
(never `Kraken.AArch64`); `KissatAuditArm64.lean` is the AArch64 mirror, and
`KissatAuditSpec.lean` audits `parseDimacs`, `CNF.Unsat` and `CNF.Sat`.

## How to read the statements

* `[Host]` is an arbitrary program image with its memory layout (`Host.prog`, `Host.exe`).
  `hc : cert.code.IsInfixAt Host.prog k₀` says the kernel-checked compiler output `cert.code` is
  linked somewhere inside it; `hu : Host.LabelsUnique` says its labels are unique. So the
  theorems hold for *any* executable that contains the compiled solver.
* `s : MachineData` is the register file and data memory at the call; execution starts at
  `Labels.label "kissat_solve_bytes"`. The SysV argument registers carry the C prototype
  `kissat_solve_bytes(cnf_ptr, cnf_len, work_ptr, work_len, fuel)`: `rdi, rsi, rdx, rcx, r8`.
  `hsp` is the SysV stack alignment at the call (`rsp + 8 ≡ 0 mod 16`).
* `hmem` describes memory in separation logic (`⋆` = disjoint union, `s.dmem =⋆ P` = `P` holds
  of the whole memory): the DIMACS bytes `bytes cnf_ptr cnfBytes`, a workspace of arbitrary
  content `region work_ptr wlen`, `bound` bytes of stack below `rsp` plus the return-address cell
  `cell64 rsp ra`, and an **arbitrary frame `R`** (everything else the caller owns).
* `Eventually (step1 Host.exe) P ⟨s, pc⟩`: every execution of the Kraken x86-64 semantics from
  `s` at `pc` reaches, after finitely many steps, a state satisfying `P` (no undefined behaviour,
  no getting stuck, termination for every fuel value).
* Postconditions: `st.pc = ra` (returned to the caller); `rax ∈ {0, 10, 20}`; `20 →` the input
  parses to an unsatisfiable CNF; (`D-Plain` only) `10 →` it parses to a satisfiable CNF; the
  callee-saved registers `rbx, rbp, r12..r15` are restored; `rsp` is popped by 8 (`ret`); the
  input bytes are unchanged (read-only), the workspace is again a `region`, the stack frame is
  again a `region`, and `R` is untouched.

## `D-Full` status

The `D-Full` (166-function) theorems take one hypothesis, `hmok : ModuleOk fullEnv fullModule`:
every function body of `fullModule` satisfies its row of `fullSpecTable` under `Func.wp`. This
is the single remaining Stage-4 hypothesis; it is discharged by the `FullProof` assembly once
the remaining per-function `Func.wp` leaves are finished. The compilation certificate, the
link-level reasoning and the top-level UNSAT argument are already fully proved. The `D-Plain`
(59-function) theorems are unconditional.
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

/-! ## 2. `D-Full` (166 functions, CDCL + inprocessing): UNSAT soundness, given `hmok` -/

/-- **`D-Full` x86-64 end-to-end UNSAT correctness** (`KissatFull.full_solve_bytes_unsat_x64`):
assuming `hmok : ModuleOk fullEnv fullModule` (the single remaining Stage-4 hypothesis), for any
host containing the compiled 166-function module and any well-formed SysV call, the machine code
returns to `ra` with `rax ∈ {0, 10, 20}`, `20` certifies UNSAT of `parseDimacs cnfBytes`,
`rbx, rbp, r12..r15` are preserved, `rsp` is `+8`, `cnfBytes` are read-only, the workspace and
stack frame are restored, and the frame `R` is preserved. No claim is made about `10`. -/
theorem audit_full_x64_unsat [Host] (hmok : ModuleOk Full.fullEnv Full.fullModule) (k₀ : Nat)
    (hc : KissatFull.kissatFull_compiled_x64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
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
      (region (s.regs.get64 .rsp -
            BitVec.ofNat 64 (KissatFull.kissatFull_compiled_x64.bound "kissat_solve_bytes"))
          (KissatFull.kissatFull_compiled_x64.bound "kissat_solve_bytes") ⋆
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
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (KissatFull.kissatFull_compiled_x64.bound "kissat_solve_bytes"))
            (KissatFull.kissatFull_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  KissatFull.full_solve_bytes_unsat_x64 hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit
    hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full` x86-64 UNSAT soundness** (`KissatFull.full_solve_bytes_unsat_sound_x64`): the
answer-only corollary of `audit_full_x64_unsat` (return to `ra`, `rax ∈ {0, 10, 20}`, and
`rax = 20 →` UNSAT). -/
theorem audit_full_x64_unsat_sound [Host] (hmok : ModuleOk Full.fullEnv Full.fullModule)
    (k₀ : Nat) (hc : KissatFull.kissatFull_compiled_x64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
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
      (region (s.regs.get64 .rsp -
            BitVec.ofNat 64 (KissatFull.kissatFull_compiled_x64.bound "kissat_solve_bytes"))
          (KissatFull.kissatFull_compiled_x64.bound "kissat_solve_bytes") ⋆
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
  KissatFull.full_solve_bytes_unsat_sound_x64 hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
    hcfit hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full` x86-64 UNSAT non-vacuity** (`KissatFull.full_unsat_nonvacuous_x64`): assuming
`hmok`, in any host containing the compiled module there is a concrete well-formed SysV call
(an UNSAT DIMACS input, a 2048-byte workspace, fuel 1, empty frame) on which the machine code
really returns `rax = 20`, so the UNSAT branch of `audit_full_x64_unsat` is reachable. -/
theorem audit_full_x64_unsat_nonvacuous [Host] (hmok : ModuleOk Full.fullEnv Full.fullModule)
    (k₀ : Nat) (hc : KissatFull.kissatFull_compiled_x64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
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
        (region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (KissatFull.kissatFull_compiled_x64.bound "kissat_solve_bytes"))
            (KissatFull.kissatFull_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st =>
          st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  KissatFull.full_unsat_nonvacuous_x64 hmok k₀ hc hu

/-! ## 3. Module shapes and `#print axioms` (one line each, standard axioms only) -/

#guard Plain.plainFns.length == 59
#guard Full.fullFns.length == 166

#print axioms audit_plain_x64_correct
#print axioms audit_plain_x64_unsat_nonvacuous
#print axioms audit_plain_x64_sat_nonvacuous
#print axioms audit_full_x64_unsat
#print axioms audit_full_x64_unsat_sound
#print axioms audit_full_x64_unsat_nonvacuous
