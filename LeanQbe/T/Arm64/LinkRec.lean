module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LinkRecLemmas
public import LeanQbe.T.Examples.LinkRec
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.LinkRec

/-!
# Cyclic & Mutual-Recursion Linking on AArch64

Instantiates measure/fuel-indexed cyclic & mutual-recursion compilation (`CompiledRec`,
`compileRecChecked`, `link_rec_compiled`) on `armTarget` (`armLegalTarget`, `armLayout`,
`armLabelClean`):
* Kernel-checked `CompiledRec` certificates for mutually recursive `evenOddRecMod`
  (`isEven`/`isOdd`, fuel `32`, max stack `2048`) and fuel-guarded `recSumMod` (`recSum`, exit
  `"out_of_fuel"`, fuel `16`, max stack `2048`), plus negative rejection tests.
* Generic arbitrary-`Host` linking theorems (`evenOdd_module_fnspec`, `recSum_module_fnspec`) and
  closed Kraken AArch64 `Eventually (step1 Host.exe)` correctness theorems (`isEven_arm64_correct`,
  `isOdd_arm64_correct`, `recSum_arm64_correct`).
* Concrete non-vacuous AArch64 execution witnesses via `armInit` (`4 -> 1`, `5 -> 0`, normal
  `recSum` return, and `"out_of_fuel"` exit).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.LinkRec

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.Arm64 Kraken

/-! ## 1. Hint Splicing and Kernel-Certified `CompiledRec` Bundles -/

splice_module_hints evenOddHints (armTarget.toIsa) armLegalTarget evenOddRecMod.fns
splice_module_hints recSumHints  (armTarget.toIsa) armLegalTarget recSumMod.fns

theorem evenOdd_compiled_check :
    checkCompileRec armTarget armLayout armLegalTarget [] [] 0 32
      evenOddRecMod.fns evenOddHints 2048 = true := by
  t_kernel_rfl

theorem evenOdd_compiled_check_withLabels :
    checkCompileRecWithLabels armTarget armLayout armLegalTarget [] [] 0 32
      evenOddRecMod.fns evenOddHints 2048 = true := by
  t_kernel_rfl

theorem recSum_compiled_check :
    checkCompileRec armTarget armLayout armLegalTarget [] ["out_of_fuel"] 16 16
      recSumMod.fns recSumHints 2048 = true := by
  t_kernel_rfl

/-- Undeclared exit `"out_of_fuel"` is rejected on AArch64. -/
theorem recSum_missing_exit_rejected :
    checkCompileRec armTarget armLayout armLegalTarget [] [] 16 16
      recSumMod.fns recSumHints 2048 = false := by
  t_kernel_rfl

/-- Excess fuel budget exceeding `maxBound = 2048` is rejected on AArch64. -/
theorem evenOdd_stack_overflow_rejected :
    checkCompileRec armTarget armLayout armLegalTarget [] [] 0 1000
      evenOddRecMod.fns evenOddHints 2048 = false := by
  t_kernel_rfl

/-- Closed AArch64 `CompiledRec` certificate for mutually recursive `isEven`/`isOdd`. -/
def evenOddCompiled :
    CompiledRec armTarget armLegalTarget [] [] 0 32 evenOddRecMod.fns evenOddHints 2048 :=
  compileRecChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 32 evenOddRecMod.fns evenOddHints 2048 evenOdd_compiled_check

/-- Closed AArch64 `CompiledRec` certificate for fuel-guarded `recSum` with `"out_of_fuel"`. -/
def recSumCompiled :
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
  Examples.BenchmarkCertKit.evenOdd_module_fnspec_gen evenOddCompiled hh rfl
    (fun _ hf => List.all_eq_true.mp evenOdd_supports_all _ hf) k₀ hc hu hk hf

/-- Arbitrary-`Host` measure-indexed `FnSpec` linking for fuel-guarded `recSum` with
`"out_of_fuel"` exit. -/
theorem recSum_module_fnspec (k₀ : Nat)
    (hc : recSumCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hexit : armTarget.Defined hh "out_of_fuel") {k : Nat} (hk : k ≤ 16) :
    armTarget.Defined hh "recSum" ∧
      armTarget.FnSpec hh "recSum" (recSumSpec k) (recSumCompiled.boundAt k) 16 :=
  Examples.BenchmarkCertKit.recSum_module_fnspec_gen recSumCompiled hh rfl
    (fun _ hf => List.all_eq_true.mp recSum_supports_all _ hf) k₀ hc hu hexit hk

private theorem evenOdd_arm64_lift {k : Nat} {nm : Sym} {spec : Spec [i64] [i64]}
    (n v : BitVec 64)
    (hfn : armTarget.FnSpec hh nm spec (evenOddCompiled.boundAt k) 0)
    (hspec : spec (n, ()) ∅ (fun r m' => r = (v, ()) ∧ emp m') (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
        (evenOddCompiled.boundAt k) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = v ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
            (evenOddCompiled.boundAt k) ⋆ R))
      ⟨s, Labels.label nm⟩ := by
  have hargs : armTarget.ArgsIn (as := [i64]) (n, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hx0⟩ .nil⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns_emp hfn hspec s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  have hret0 : (st.data.regs.getXReg .X0).toBitVec = v := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton v st.data hrets
  exact ⟨hpc, hret0, hcs, hsp', hm'⟩

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
      ⟨s, Labels.label "isEven"⟩ := by
  have hfn : armTarget.FnSpec hh "isEven" (isEvenSpec k) (evenOddCompiled.boundAt k) 0 :=
    (evenOdd_module_fnspec k₀ hc hu hk (fn := isEven) List.mem_cons_self).2
  exact evenOdd_arm64_lift n (isEvenVal n) hfn ⟨hn, rfl, rfl⟩ s ra R hx0 hra hsp hmem

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
      ⟨s, Labels.label "isOdd"⟩ := by
  have hfn : armTarget.FnSpec hh "isOdd" (isOddSpec k) (evenOddCompiled.boundAt k) 0 :=
    (evenOdd_module_fnspec k₀ hc hu hk (fn := isOdd)
      (List.mem_cons_of_mem _ List.mem_cons_self)).2
  exact evenOdd_arm64_lift n (isOddVal n) hfn ⟨hn, rfl, rfl⟩ s ra R hx0 hra hsp hmem

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
      ⟨s, Labels.label "recSum"⟩ := by
  have hargs : armTarget.ArgsIn (as := [i64, i64]) (n, f, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hx0⟩
      (.cons ⟨by decide, by simpa [get_reg] using hx1⟩ .nil)⟩
  have hmem' : s.dmem =⋆ Eq (∅ : Mem 64) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (recSumCompiled.boundAt k))
        (recSumCompiled.boundAt k) ⋆ R := by
    rw [eq_empty_eq_emp, emp_sep]; exact hmem
  have hfn := (recSum_module_fnspec k₀ hc hu hexit hk).2
  have hspec := Examples.BenchmarkCertKit.recSum_spec_ok (k := k) n f hf
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_call_emp hfn hspec s ra R hargs hra hsp hmem')
  rintro st (⟨hpc, hcs, hsp', _, _, ⟨sum, hsum, rfl⟩, hrets, _⟩ |
    ⟨_, _, _, _, ⟨rfl, rem, hrem, rfl, rfl⟩, _, hpc, has', hspE⟩)
  · refine Or.inl ⟨sum, hsum, hpc, ?_, hcs, hsp'⟩
    simpa [armInit, get_reg] using armInit.retsIn_singleton sum st.data hrets
  · refine Or.inr ⟨rem, hrem, hpc, ?_, hspE⟩
    simpa [armInit, get_reg] using armInit.argsIn_singleton rem st.data has'

end Generic

/-! ## 3. Concrete Non-Vacuous AArch64 Execution Witnesses -/

abbrev evenOddHost : Host := evenOddCompiled.host
def evenOddState (k : Nat) (n : BitVec 64) : MachineData :=
  armInit.initState (as := [i64]) (evenOddCompiled.boundAt k) [] (n, ())

private theorem arm64_pc_x0_weaken [Host] {k₀ : BitVec 64} {st₀} :
    Eventually (step1 Host.exe)
      (fun st => st.pc = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = k₀)
      st₀ →
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = k₀) st₀ :=
  eventually_weaken _ _ _ _ fun _ ⟨hpc, hx0⟩ => ⟨hpc, by simpa [armInit, get_reg] using hx0⟩

attribute [local instance] evenOddHost in
theorem isEven_4_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1#64)
      ⟨evenOddState 4 4#64, Labels.label "isEven"⟩ :=
  arm64_pc_x0_weaken <|
    Examples.BenchmarkCertKit.evenOdd_target_nonvacuous armInit evenOddCompiled "isEven"
      (by decide : 4 ≤ 32) (n := 4#64)
      (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
        (by decide : 4 ≤ 32) List.mem_cons_self).2
      rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isEven_5_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0#64)
      ⟨evenOddState 5 5#64, Labels.label "isEven"⟩ :=
  arm64_pc_x0_weaken <|
    Examples.BenchmarkCertKit.evenOdd_target_nonvacuous armInit evenOddCompiled "isEven"
      (by decide : 5 ≤ 32) (n := 5#64)
      (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
        (by decide : 5 ≤ 32) List.mem_cons_self).2
      rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isOdd_4_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0#64)
      ⟨evenOddState 4 4#64, Labels.label "isOdd"⟩ :=
  arm64_pc_x0_weaken <|
    Examples.BenchmarkCertKit.evenOdd_target_nonvacuous armInit evenOddCompiled "isOdd"
      (by decide : 4 ≤ 32) (n := 4#64)
      (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
        (by decide : 4 ≤ 32) (List.mem_cons_of_mem _ List.mem_cons_self)).2
      rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isOdd_5_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1#64)
      ⟨evenOddState 5 5#64, Labels.label "isOdd"⟩ :=
  arm64_pc_x0_weaken <|
    Examples.BenchmarkCertKit.evenOdd_target_nonvacuous armInit evenOddCompiled "isOdd"
      (by decide : 5 ≤ 32) (n := 5#64)
      (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
        (by decide : 5 ≤ 32) (List.mem_cons_of_mem _ List.mem_cons_self)).2
      rfl ⟨by decide, rfl⟩

abbrev recSumHost : Host := recSumCompiled.host
def recSumState (k : Nat) (n f : BitVec 64) : MachineData :=
  armInit.initState (as := [i64, i64]) (recSumCompiled.boundAt k) [] (n, f, ())

attribute [local instance] recSumHost in
theorem recSum_normal_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 6#64)
      ⟨recSumState 5 3#64 5#64, Labels.label "recSum"⟩ := by
  have hfn := (recSum_module_fnspec 0 recSumCompiled.code_infix_host recSumCompiled.labelsUnique
    (recSumCompiled.defined_exit_host (by simp)) (by decide : 5 ≤ 16)).2
  have ho : recSumOutcome 3#64 (5#64).toNat = .inl 6#64 := by decide
  exact arm64_pc_x0_weaken <|
    run_rec_ret1_i64 armInit recSumCompiled (by decide : 5 ≤ 16) hfn [] (3#64, 5#64, ())
      6#64 (by decide) rfl ⟨by decide, by
        change match recSumOutcome 3#64 (5#64).toNat with
          | .inl s => (s, ()) = (6#64, ()) | .inr _ => False
        rw [ho]⟩ fun _ _ h => h

attribute [local instance] recSumHost in
theorem recSum_out_of_fuel_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "out_of_fuel" ∧
        (st.data.regs.getXReg .X0).toBitVec = 3#64)
      ⟨recSumState 2 5#64 2#64, Labels.label "recSum"⟩ := by
  have hfn := (recSum_module_fnspec 0 recSumCompiled.code_infix_host recSumCompiled.labelsUnique
    (recSumCompiled.defined_exit_host (by simp)) (by decide : 2 ≤ 16)).2
  have ho : recSumOutcome 5#64 (2#64).toNat = .inr 3#64 := by decide
  refine run_rec_fnSpec armInit recSumCompiled (by decide : 2 ≤ 16) hfn [] (5#64, 2#64, ())
    (by decide) rfl (Q := fun _ _ => False) (X := fun g cs xs _ =>
      g = "out_of_fuel" ∧ cs = [i64] ∧ HEq xs ((3#64, ()) : Tup Val [i64]))
    ⟨by decide, by rw [ho]; exact ⟨rfl, rfl, HEq.rfl⟩⟩ ?_
  rintro st (⟨_, _, _, hq, _⟩ | ⟨_, _, _, _, ⟨rfl, rfl, hxs⟩, hpc, has⟩)
  · exact hq.elim
  · obtain rfl := eq_of_heq hxs
    exact ⟨hpc, by simpa [armInit, get_reg] using armInit.argsIn_singleton 3#64 _ has⟩

end LeanQbe.T.Arm64.LinkRec
