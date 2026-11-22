module

public import LeanQbe.T.Amd64.KissatFull
public import LeanQbe.T.Amd64.KissatFastSched
public import LeanQbe.T.Amd64.KissatFast
meta import LeanQbe.T.Examples.Kissat.FullSpec
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat legacy audit, part 2: SysV x86-64 machine-code theorems

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

The `D-Full` (166-function) theorems are **unconditional** (`166/166` `ModuleOk fullEnv fullModule`
discharged by `FullProof.fullEnv_moduleOk`, combining `FullBridgeLemmas1`–`9`,
`FullOneLitConflLemmas`, and `FullDeduce1UipLemmas`), matching `D-Plain`. Model reconstruction
after inprocessing is intentionally unverified, so `10` is not certified; only UNSAT (`20`) is.
-/

set_option autoImplicit false

public section

open Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Amd64 Kraken

/-! ## 1. `D-Full` (166 functions, CDCL + inprocessing): UNSAT soundness, unconditional -/

/-- **`D-Full` x86-64 end-to-end UNSAT correctness** (`KissatFull.full_solve_bytes_unsat_x64`):
for any host containing the compiled 166-function module and any well-formed SysV call, the machine
code returns to `ra` with `rax ∈ {0, 10, 20}`, `20` certifies UNSAT of `parseDimacs cnfBytes`,
`rbx, rbp, r12..r15` are preserved, `rsp` is `+8`, `cnfBytes` are read-only, the workspace and
stack frame are restored, and the frame `R` is preserved. No claim is made about `10`. -/
theorem audit_full_x64_unsat [Host] (k₀ : Nat)
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
  KissatFull.full_solve_bytes_unsat_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full` x86-64 UNSAT soundness** (`KissatFull.full_solve_bytes_unsat_sound_x64`): the
answer-only corollary of `audit_full_x64_unsat` (return to `ra`, `rax ∈ {0, 10, 20}`, and
`rax = 20 →` UNSAT). -/
theorem audit_full_x64_unsat_sound [Host]
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
  KissatFull.full_solve_bytes_unsat_sound_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit
    hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- **`D-Full` x86-64 UNSAT non-vacuity** (`KissatFull.full_unsat_nonvacuous_x64`): unconditionally,
in any host containing the compiled module there is a concrete well-formed SysV call (an UNSAT
DIMACS input, a 2048-byte workspace, fuel 1, empty frame) on which the machine code really returns
`rax = 20`, so the UNSAT branch of `audit_full_x64_unsat` is reachable. -/
theorem audit_full_x64_unsat_nonvacuous [Host]
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
  KissatFull.full_unsat_nonvacuous_x64 k₀ hc hu

/-! ## 2. M2a Fast Scheduler (`Amd64.KissatFastSched`, parameterized over `ModuleOk schedEnv`) -/

section M2aFastSchedX64

open Std.Sat LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullFastSched (schedEnv schedModule)
open LeanQbe.T.Amd64.KissatFastSched
  (kissatFastSched_compiled_x64 sched_module_fnspec sched_solve_bytes_unsat_x64
    sched_solve_bytes_unsat_sound_x64 sched_unsat_nonvacuous_x64)

theorem audit_sched_x64_fnspec [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ schedModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (schedEnv f.name f.as f.rs)
        (kissatFastSched_compiled_x64.bound f.name) 0 :=
  sched_module_fnspec hmok k₀ hc hu hf

theorem audit_sched_x64_unsat [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
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

theorem audit_sched_x64_sound [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
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

theorem audit_sched_x64_nv [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
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

end M2aFastSchedX64

/-! ## 3. `D-Full M2 Fast` (`Amd64.KissatFast`, `196` fns): UNSAT soundness, unconditional -/

section M2FastX64

open Std.Sat LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullFast (fastEnv fastModule)
open LeanQbe.T.Amd64.KissatFast
  (kissatFast_compiled_x64 fast_module_fnspec fast_solve_bytes_unsat_x64
    fast_solve_bytes_unsat_sound_x64 fast_unsat_nonvacuous_x64)

/-- **`D-Full M2 Fast` x86-64 whole-module `Defined` + `FnSpec`** (`196/196`, unconditional). -/
theorem audit_fast_x64_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatFast_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fastModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (fastEnv f.name f.as f.rs)
        (kissatFast_compiled_x64.bound f.name) 0 :=
  fast_module_fnspec k₀ hc hu hf

/-- **`D-Full M2 Fast` x86-64 end-to-end UNSAT soundness + framing** (`196` fns, unconditional). -/
theorem audit_fast_x64_unsat [hh : Host] (k₀ : Nat)
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

/-- **`D-Full M2 Fast` x86-64 answer-only UNSAT soundness** (`196` fns, unconditional). -/
theorem audit_fast_x64_sound [hh : Host] (k₀ : Nat)
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

/-- **`D-Full M2 Fast` x86-64 UNSAT non-vacuity** (`196` fns, unconditional). -/
theorem audit_fast_x64_nv [hh : Host] (k₀ : Nat)
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

end M2FastX64

/-! ## 4. Module shapes and `#print axioms` (one line each, standard axioms only) -/

#guard Full.fullFns.length == 166
#guard FullFast.fastFns.length == 196

#print axioms audit_full_x64_unsat
#print axioms audit_full_x64_unsat_sound
#print axioms audit_full_x64_unsat_nonvacuous
#print axioms audit_sched_x64_fnspec
#print axioms audit_sched_x64_unsat
#print axioms audit_sched_x64_sound
#print axioms audit_sched_x64_nv
#print axioms audit_fast_x64_fnspec
#print axioms audit_fast_x64_unsat
#print axioms audit_fast_x64_sound
#print axioms audit_fast_x64_nv
