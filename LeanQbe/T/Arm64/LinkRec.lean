module

public import LeanQbe.T.Arm64.BenchAbi
public import LeanQbe.T.LinkRecLemmas
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.LinkRec

/-!
# Cyclic & Mutual-Recursion Linking on AArch64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.LinkRec

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Arm64 Kraken

/-! ## 1. Hint Splicing and Kernel-Certified `CompiledRec` Bundles -/

splice_module_hints evenOddHints (armTarget.toIsa) armLegalTarget evenOddRecMod.fns
splice_module_hints recSumHints  (armTarget.toIsa) armLegalTarget recSumMod.fns

theorem evenOdd_compiled_check :
    checkCompileRec armTarget armLayout armLegalTarget [] [] 0 32
      evenOddRecMod.fns evenOddHints 2048 = true := by t_kernel_rfl

theorem evenOdd_compiled_check_withLabels :
    checkCompileRecWithLabels armTarget armLayout armLegalTarget [] [] 0 32
      evenOddRecMod.fns evenOddHints 2048 = true := by t_kernel_rfl

theorem recSum_compiled_check :
    checkCompileRec armTarget armLayout armLegalTarget [] ["out_of_fuel"] 16 16
      recSumMod.fns recSumHints 2048 = true := by t_kernel_rfl

/-- Undeclared exit `"out_of_fuel"` is rejected on AArch64. -/
theorem recSum_missing_exit_rejected :
    checkCompileRec armTarget armLayout armLegalTarget [] [] 16 16
      recSumMod.fns recSumHints 2048 = false := by t_kernel_rfl

/-- Excess fuel budget exceeding `maxBound = 2048` is rejected on AArch64. -/
theorem evenOdd_stack_overflow_rejected :
    checkCompileRec armTarget armLayout armLegalTarget [] [] 0 1000
      evenOddRecMod.fns evenOddHints 2048 = false := by t_kernel_rfl

/-- Closed AArch64 `CompiledRec` certificate for mutually recursive `isEven`/`isOdd`. -/
@[expose] def evenOddCompiled :
    CompiledRec armTarget armLegalTarget [] [] 0 32 evenOddRecMod.fns evenOddHints 2048 :=
  compileRecChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 32 evenOddRecMod.fns evenOddHints 2048 evenOdd_compiled_check

/-- Closed AArch64 `CompiledRec` certificate for fuel-guarded `recSum` with `"out_of_fuel"`. -/
@[expose] def recSumCompiled :
    CompiledRec armTarget armLegalTarget [] ["out_of_fuel"] 16 16 recSumMod.fns recSumHints 2048 :=
  compileRecChecked armTarget armLayout armLegalTarget armLabelClean
    [] ["out_of_fuel"] 16 16 recSumMod.fns recSumHints 2048 recSum_compiled_check

/-! ## 2. Linking & Generic Arbitrary-`Host` AArch64 `Eventually` Theorems -/

private theorem evenOdd_supports_all :
    evenOddRecMod.fns.all (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

private theorem recSum_supports_all :
    recSumMod.fns.all (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

section Generic

variable {hh : Host}

/-- Arbitrary-`Host` measure-indexed `FnSpec` linking for mutually recursive `{isEven, isOdd}`. -/
theorem evenOdd_module_fnspec (k₀ : Nat)
    (hc : evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) {fn : Fn} (hf : fn ∈ evenOddRecMod.fns) :
    armTarget.Defined hh fn.name ∧
      armTarget.FnSpec hh fn.name (evenOddRecEnv k fn.name fn.as fn.rs)
        (evenOddCompiled.boundAt k) 0 :=
  evenOdd_module_fnspec_gen evenOddCompiled hh rfl
    (fun _ hf => List.all_eq_true.mp evenOdd_supports_all _ hf) k₀ hc hu hk hf

/-- Arbitrary-`Host` measure-indexed `FnSpec` linking for fuel-guarded `recSum` with
`"out_of_fuel"` exit. -/
theorem recSum_module_fnspec (k₀ : Nat)
    (hc : recSumCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hexit : armTarget.Defined hh "out_of_fuel") {k : Nat} (hk : k ≤ 16) :
    armTarget.Defined hh "recSum" ∧
      armTarget.FnSpec hh "recSum" (recSumSpec k) (recSumCompiled.boundAt k) 16 :=
  recSum_module_fnspec_gen recSumCompiled hh rfl
    (fun _ hf => List.all_eq_true.mp recSum_supports_all _ hf) k₀ hc hu hexit hk

/-- End-to-end machine `Eventually` correctness for mutually recursive `isEven` on AArch64. -/
theorem isEven_arm64_correct (k₀ : Nat)
    (hc : evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) (n : BitVec 64) (hn : n.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
        (evenOddCompiled.boundAt k) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = isEvenVal n ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
            (evenOddCompiled.boundAt k) ⋆ R))
      ⟨s, Labels.label "isEven"⟩ :=
  linkrec_evenOdd_abi_correct arm64BenchAbi hh evenOddCompiled
    (fun _ hf => List.all_eq_true.mp evenOdd_supports_all _ hf) k₀ hc hu hk
    List.mem_cons_self ⟨rfl, rfl⟩ (spec := isEvenSpec k) rfl (valFn := isEvenVal)
    ⟨hn, rfl, rfl⟩ s ra R hx0 ⟨hra, hsp⟩ hmem

/-- End-to-end machine `Eventually` correctness for mutually recursive `isOdd` on AArch64. -/
theorem isOdd_arm64_correct (k₀ : Nat)
    (hc : evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) (n : BitVec 64) (hn : n.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
        (evenOddCompiled.boundAt k) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = isOddVal n ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
            (evenOddCompiled.boundAt k) ⋆ R))
      ⟨s, Labels.label "isOdd"⟩ :=
  linkrec_evenOdd_abi_correct arm64BenchAbi hh evenOddCompiled
    (fun _ hf => List.all_eq_true.mp evenOdd_supports_all _ hf) k₀ hc hu hk
    (List.mem_cons_of_mem _ List.mem_cons_self) ⟨rfl, rfl⟩ (spec := isOddSpec k) rfl
    (valFn := isOddVal) ⟨hn, rfl, rfl⟩ s ra R hx0 ⟨hra, hsp⟩ hmem

/-- End-to-end machine `Eventually` correctness for fuel-guarded `recSum` (both normal return and
`"out_of_fuel"` exit) on Kraken AArch64. -/
theorem recSum_arm64_correct (k₀ : Nat)
    (hc : recSumCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hexit : armTarget.Defined hh "out_of_fuel")
    {k : Nat} (hk : k ≤ 16) (n f : BitVec 64) (hf : f.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n) (hx1 : (s.regs.getXReg .X1).toBitVec = f)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (recSumCompiled.boundAt k))
        (recSumCompiled.boundAt k) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (∃ sum, recSumOutcome n f.toNat = .inl sum ∧
          st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = sum ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP) ∨
        (∃ rem, recSumOutcome n f.toNat = .inr rem ∧
          st.pc = Labels.label "out_of_fuel" ∧ (st.data.regs.getXReg .X0).toBitVec = rem ∧
          st.data.regs.SP.toNat % 16 = 0))
      ⟨s, Labels.label "recSum"⟩ :=
  linkrec_recSum_abi_correct arm64BenchAbi hh recSumCompiled
    (fun _ hf => List.all_eq_true.mp recSum_supports_all _ hf) k₀ hc hu hexit hk
    n f hf s ra R hx0 hx1 ⟨hra, hsp⟩ hmem

end Generic

/-! ## 3. Concrete Non-Vacuous AArch64 Execution Witnesses -/

abbrev evenOddHost : Host := evenOddCompiled.host
@[expose] def evenOddState (k : Nat) (n : BitVec 64) : MachineData :=
  armInit.initState (as := [i64]) (evenOddCompiled.boundAt k) [] (n, ())

private theorem arm64_pc_x0_weaken [Host] {k₀ : BitVec 64} {st₀} :
    Eventually (step1 Host.exe)
      (fun st => st.pc = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = k₀) st₀ →
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = k₀) st₀ :=
  eventually_weaken _ _ _ _ fun _ ⟨hpc, hx0⟩ => ⟨hpc, by simpa [armInit, get_reg] using hx0⟩

attribute [local instance] evenOddHost in
theorem isEven_4_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1#64)
      ⟨evenOddState 4 4#64, Labels.label "isEven"⟩ :=
  arm64_pc_x0_weaken <| evenOdd_target_nonvacuous armInit evenOddCompiled "isEven"
    (by decide : 4 ≤ 32) (n := 4#64)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 4 ≤ 32) List.mem_cons_self).2 rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isEven_5_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0#64)
      ⟨evenOddState 5 5#64, Labels.label "isEven"⟩ :=
  arm64_pc_x0_weaken <| evenOdd_target_nonvacuous armInit evenOddCompiled "isEven"
    (by decide : 5 ≤ 32) (n := 5#64)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 5 ≤ 32) List.mem_cons_self).2 rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isOdd_4_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0#64)
      ⟨evenOddState 4 4#64, Labels.label "isOdd"⟩ :=
  arm64_pc_x0_weaken <| evenOdd_target_nonvacuous armInit evenOddCompiled "isOdd"
    (by decide : 4 ≤ 32) (n := 4#64)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 4 ≤ 32) (List.mem_cons_of_mem _ List.mem_cons_self)).2 rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isOdd_5_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1#64)
      ⟨evenOddState 5 5#64, Labels.label "isOdd"⟩ :=
  arm64_pc_x0_weaken <| evenOdd_target_nonvacuous armInit evenOddCompiled "isOdd"
    (by decide : 5 ≤ 32) (n := 5#64)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 5 ≤ 32) (List.mem_cons_of_mem _ List.mem_cons_self)).2 rfl ⟨by decide, rfl⟩

abbrev recSumHost : Host := recSumCompiled.host
@[expose] def recSumState (k : Nat) (n f : BitVec 64) : MachineData :=
  armInit.initState (as := [i64, i64]) (recSumCompiled.boundAt k) [] (n, f, ())

attribute [local instance] recSumHost in
theorem recSum_normal_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 6#64)
      ⟨recSumState 5 3#64 5#64, Labels.label "recSum"⟩ :=
  linkrec_recSum_normal_abi_nv arm64BenchAbi recSumCompiled
    (fun _ hf => List.all_eq_true.mp recSum_supports_all _ hf)

attribute [local instance] recSumHost in
theorem recSum_out_of_fuel_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "out_of_fuel" ∧
        (st.data.regs.getXReg .X0).toBitVec = 3#64)
      ⟨recSumState 2 5#64 2#64, Labels.label "recSum"⟩ :=
  linkrec_recSum_exit_abi_nv arm64BenchAbi recSumCompiled
    (fun _ hf => List.all_eq_true.mp recSum_supports_all _ hf)

end LeanQbe.T.Arm64.LinkRec
