module

public import LeanQbe.T.Arm64.KissatFull
public import LeanQbe.T.Arm64.KissatFastSched
public import LeanQbe.T.Arm64.KissatFast
meta import LeanQbe.T.Examples.Kissat.FullSpec
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat legacy audit, part 3: AAPCS64 AArch64 machine-code theorems

This file is meant to be read by a human auditor. It is the exact AArch64 mirror of
`KissatAuditX64.lean`: it restates, with every hypothesis and postcondition written out in full
(no wrapper `abbrev`s introduced here), the end-to-end theorems about the **AArch64 machine code**
that the `LeanQbe.T` compiler emits for `kissat_solve_bytes`, and proves each restatement by the
corresponding library theorem. It imports `Kraken.AArch64` only (never `Kraken.X64`);
`KissatAuditSpec.lean` audits `parseDimacs`, `CNF.Unsat` and `CNF.Sat`.

## How to read the statements

* `[Host]` is an arbitrary program image with its memory layout (`Host.prog`, `Host.exe`).
  `hc : cert.code.IsInfixAt Host.prog k₀` says the kernel-checked compiler output `cert.code` is
  linked somewhere inside it; `hu : Host.LabelsUnique` says its labels are unique. So the
  theorems hold for *any* executable that contains the compiled solver.
* `s : MachineData` is the register file and data memory at the call; execution starts at
  `Labels.label "kissat_solve_bytes"`. The AAPCS64 argument registers carry the C prototype
  `kissat_solve_bytes(cnf_ptr, cnf_len, work_ptr, work_len, fuel)`: `X0, X1, X2, X3, X4`; the
  link register `X30` holds the return address `ra`, and `SP` is 16-byte aligned.
* `hmem` describes memory in separation logic (`⋆` = disjoint union, `s.dmem =⋆ P` = `P` holds
  of the whole memory): the DIMACS bytes `bytes cnf_ptr cnfBytes`, a workspace of arbitrary
  content `region work_ptr wlen`, `bound` bytes of stack below `SP`, and an **arbitrary frame
  `R`** (everything else the caller owns).
* `Eventually (step1 Host.exe) P ⟨s, pc⟩`: every execution of the Kraken AArch64 semantics from
  `s` at `pc` reaches, after finitely many steps, a state satisfying `P` (no undefined behaviour,
  no getting stuck, termination for every fuel value).
* Postconditions: `st.pc = ra` (returned to `X30`); `X0 ∈ {0, 10, 20}`; `20 →` the input parses
  to an unsatisfiable CNF; (`D-Plain` only) `10 →` it parses to a satisfiable CNF; the
  callee-saved registers `X19..X29` are restored; `SP` is unchanged; the input bytes are
  unchanged (read-only), the workspace and the stack frame are again `region`s, and `R` is
  untouched.

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
open LeanQbe.T.Arm64 Kraken

/-! ## 1. `D-Full` (166 functions, CDCL + inprocessing): UNSAT soundness, unconditional -/

/-- **`D-Full` AArch64 end-to-end UNSAT correctness**
(`KissatFull.full_solve_bytes_unsat_arm64`): for any host containing the compiled 166-function
module and any well-formed AAPCS64 call, the machine code returns to `ra` with `X0 ∈ {0, 10, 20}`,
`20` certifies UNSAT of `parseDimacs cnfBytes`, `X19..X29` and `SP` are preserved, `cnfBytes` are
read-only, the workspace and stack frame are restored, and the frame `R` is preserved. No claim
is made about `10`. -/
theorem audit_full_arm64_unsat [Host] (k₀ : Nat)
    (hc : KissatFull.kissatFull_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
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
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (KissatFull.kissatFull_compiled_arm64.bound "kissat_solve_bytes"))
        (KissatFull.kissatFull_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (KissatFull.kissatFull_compiled_arm64.bound "kissat_solve_bytes"))
            (KissatFull.kissatFull_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  KissatFull.full_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full` AArch64 UNSAT soundness** (`KissatFull.full_solve_bytes_unsat_sound_arm64`): the
answer-only corollary of `audit_full_arm64_unsat` (return to `ra`, `X0 ∈ {0, 10, 20}`, and
`X0 = 20 →` UNSAT). -/
theorem audit_full_arm64_unsat_sound [Host]
    (k₀ : Nat) (hc : KissatFull.kissatFull_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
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
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (KissatFull.kissatFull_compiled_arm64.bound "kissat_solve_bytes"))
        (KissatFull.kissatFull_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  KissatFull.full_solve_bytes_unsat_sound_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit
    hwfit s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full` AArch64 UNSAT non-vacuity** (`KissatFull.full_unsat_nonvacuous_arm64`):
unconditionally, in any host containing the compiled module there is a concrete well-formed AAPCS64
call (an UNSAT DIMACS input, a 2048-byte workspace, fuel 1, empty frame) on which the machine code
really returns `X0 = 20`, so the UNSAT branch of `audit_full_arm64_unsat` is reachable. -/
theorem audit_full_arm64_unsat_nonvacuous [Host]
    (k₀ : Nat) (hc : KissatFull.kissatFull_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec -
            BitVec.ofNat 64 (KissatFull.kissatFull_compiled_arm64.bound "kissat_solve_bytes"))
          (KissatFull.kissatFull_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st =>
          st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  KissatFull.full_unsat_nonvacuous_arm64 k₀ hc hu

/-! ## 2. M2a Fast Scheduler (`Arm64.KissatFastSched`, parameterized over `ModuleOk schedEnv`) -/

section M2aFastSchedArm64

open Std.Sat LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullFastSched (schedEnv schedModule)
open LeanQbe.T.Arm64.KissatFastSched
  (kissatFastSched_compiled_arm64 sched_module_fnspec sched_solve_bytes_unsat_arm64
    sched_solve_bytes_unsat_sound_arm64 sched_unsat_nonvacuous_arm64)

theorem audit_sched_arm_fnspec [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ schedModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (schedEnv f.name f.as f.rs)
        (kissatFastSched_compiled_arm64.bound f.name) 0 :=
  sched_module_fnspec hmok k₀ hc hu hf

theorem audit_sched_arm_unsat [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatFastSched_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatFastSched_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatFastSched_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatFastSched_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  sched_solve_bytes_unsat_arm64 hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

theorem audit_sched_arm_sound [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatFastSched_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatFastSched_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  sched_solve_bytes_unsat_sound_arm64 hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit
    hwfit s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

theorem audit_sched_arm_nv [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - BitVec.ofNat 64
            (kissatFastSched_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatFastSched_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  sched_unsat_nonvacuous_arm64 hmok k₀ hc hu

end M2aFastSchedArm64

/-! ## 3. `D-Full M2 Fast` (`Arm64.KissatFast`, `196` fns): UNSAT soundness, unconditional -/

section M2FastArm64

open Std.Sat LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullFast (fastEnv fastModule)
open LeanQbe.T.Arm64.KissatFast
  (kissatFast_compiled_arm64 fast_module_fnspec fast_solve_bytes_unsat_arm64
    fast_solve_bytes_unsat_sound_arm64 fast_unsat_nonvacuous_arm64)

/-- **`D-Full M2 Fast` AArch64 whole-module `Defined` + `FnSpec`** (`196/196`, unconditional). -/
theorem audit_fast_arm_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatFast_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fastModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (fastEnv f.name f.as f.rs)
        (kissatFast_compiled_arm64.bound f.name) 0 :=
  fast_module_fnspec k₀ hc hu hf

/-- **`D-Full M2 Fast` AArch64 end-to-end UNSAT soundness + framing** (`196` fns, unconditional). -/
theorem audit_fast_arm_unsat [hh : Host] (k₀ : Nat)
    (hc : kissatFast_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatFast_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatFast_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatFast_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatFast_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  fast_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full M2 Fast` AArch64 answer-only UNSAT soundness** (`196` fns, unconditional). -/
theorem audit_fast_arm_sound [hh : Host] (k₀ : Nat)
    (hc : kissatFast_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatFast_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatFast_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  fast_solve_bytes_unsat_sound_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- **`D-Full M2 Fast` AArch64 UNSAT non-vacuity** (`196` fns, unconditional). -/
theorem audit_fast_arm_nv [hh : Host] (k₀ : Nat)
    (hc : kissatFast_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - BitVec.ofNat 64
            (kissatFast_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatFast_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  fast_unsat_nonvacuous_arm64 k₀ hc hu

end M2FastArm64

/-! ## 4. Module shapes and `#print axioms` (one line each, standard axioms only) -/

#guard Full.fullFns.length == 166
#guard FullFast.fastFns.length == 196

#print axioms audit_full_arm64_unsat
#print axioms audit_full_arm64_unsat_sound
#print axioms audit_full_arm64_unsat_nonvacuous
#print axioms audit_sched_arm_fnspec
#print axioms audit_sched_arm_unsat
#print axioms audit_sched_arm_sound
#print axioms audit_sched_arm_nv
#print axioms audit_fast_arm_fnspec
#print axioms audit_fast_arm_unsat
#print axioms audit_fast_arm_sound
#print axioms audit_fast_arm_nv
