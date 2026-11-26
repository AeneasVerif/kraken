module

public import LeanQbe.T.Amd64.TargLemmas
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
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.LinkRec

/-!
# Cyclic & Mutual-Recursion Linking on SysV x64

Instantiates measure/fuel-indexed cyclic & mutual-recursion compilation (`CompiledRec`,
`compileRecChecked`, `link_rec_compiled`) on `x64Target` (`x64LegalTarget`, `x64Layout`,
`x64LabelClean`):
* Kernel-checked `CompiledRec` certificates for mutually recursive `evenOddRecMod`
  (`isEven`/`isOdd`, fuel `32`, max stack `2048`) and fuel-guarded `recSumMod` (`recSum`, exit
  `"out_of_fuel"`, fuel `16`, max stack `2048`), plus negative rejection tests.
* Generic arbitrary-`Host` linking theorems (`evenOdd_module_fnspec`, `recSum_module_fnspec`) and
  closed Kraken x64 `Eventually (step1 Host.exe)` correctness theorems (`isEven_x64_correct`,
  `isOdd_x64_correct`, `recSum_x64_correct`).
* Concrete non-vacuous x64 execution witnesses via `x64Init` (`4 -> 1`, `5 -> 0`, normal `recSum`
  return, and `"out_of_fuel"` exit).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.LinkRec

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.Amd64 Kraken

/-! ## 1. Hint Splicing and Kernel-Certified `CompiledRec` Bundles -/

splice_module_hints evenOddHints (x64Target.toIsa) x64LegalTarget evenOddRecMod.fns
splice_module_hints recSumHints  (x64Target.toIsa) x64LegalTarget recSumMod.fns

theorem evenOdd_compiled_check :
    checkCompileRec x64Target x64Layout x64LegalTarget [] [] 0 32
      evenOddRecMod.fns evenOddHints 2048 = true := by
  t_kernel_rfl

theorem evenOdd_compiled_check_withLabels :
    checkCompileRecWithLabels x64Target x64Layout x64LegalTarget [] [] 0 32
      evenOddRecMod.fns evenOddHints 2048 = true := by
  t_kernel_rfl

theorem recSum_compiled_check :
    checkCompileRec x64Target x64Layout x64LegalTarget [] ["out_of_fuel"] 16 16
      recSumMod.fns recSumHints 2048 = true := by
  t_kernel_rfl

/-- Undeclared exit `"out_of_fuel"` is rejected on x64. -/
theorem recSum_missing_exit_rejected :
    checkCompileRec x64Target x64Layout x64LegalTarget [] [] 16 16
      recSumMod.fns recSumHints 2048 = false := by
  t_kernel_rfl

/-- Excess fuel budget exceeding `maxBound = 2048` is rejected on x64. -/
theorem evenOdd_stack_overflow_rejected :
    checkCompileRec x64Target x64Layout x64LegalTarget [] [] 0 1000
      evenOddRecMod.fns evenOddHints 2048 = false := by
  t_kernel_rfl

/-- Closed x64 `CompiledRec` certificate for mutually recursive `isEven`/`isOdd`. -/
def evenOddCompiled :
    CompiledRec x64Target x64LegalTarget [] [] 0 32 evenOddRecMod.fns evenOddHints 2048 :=
  compileRecChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 32 evenOddRecMod.fns evenOddHints 2048 evenOdd_compiled_check

/-- Closed x64 `CompiledRec` certificate for fuel-guarded `recSum` with `"out_of_fuel"` exit. -/
def recSumCompiled :
    CompiledRec x64Target x64LegalTarget [] ["out_of_fuel"] 16 16 recSumMod.fns recSumHints 2048 :=
  compileRecChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] ["out_of_fuel"] 16 16 recSumMod.fns recSumHints 2048 recSum_compiled_check

/-! ## 2. Linking & Generic Arbitrary-`Host` x64 `Eventually` Theorems -/

private theorem evenOdd_supports_all :
    evenOddRecMod.fns.all (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

private theorem recSum_supports_all :
    recSumMod.fns.all (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

section Generic

variable {hh : Host}

/-- Arbitrary-`Host` measure-indexed `FnSpec` linking for mutually recursive `{isEven, isOdd}`. -/
theorem evenOdd_module_fnspec (k₀ : Nat)
    (hc : evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) {fn : Fn} (hf : fn ∈ evenOddRecMod.fns) :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (evenOddRecEnv k fn.name fn.as fn.rs)
        (evenOddCompiled.boundAt k) 0 :=
  Examples.BenchmarkCertKit.evenOdd_module_fnspec_gen evenOddCompiled hh rfl
    (fun _ hf => List.all_eq_true.mp evenOdd_supports_all _ hf) k₀ hc hu hk hf

/-- Arbitrary-`Host` measure-indexed `FnSpec` linking for fuel-guarded `recSum` with
`"out_of_fuel"` exit. -/
theorem recSum_module_fnspec (k₀ : Nat)
    (hc : recSumCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hexit : x64Target.Defined hh "out_of_fuel") {k : Nat} (hk : k ≤ 16) :
    x64Target.Defined hh "recSum" ∧
      x64Target.FnSpec hh "recSum" (recSumSpec k) (recSumCompiled.boundAt k) 16 :=
  Examples.BenchmarkCertKit.recSum_module_fnspec_gen recSumCompiled hh rfl
    (fun _ hf => List.all_eq_true.mp recSum_supports_all _ hf) k₀ hc hu hexit hk

private theorem evenOdd_x64_lift {k : Nat} {nm : Sym} {spec : Spec [i64] [i64]}
    (n v : BitVec 64)
    (hfn : x64Target.FnSpec hh nm spec (evenOddCompiled.boundAt k) 0)
    (hspec : spec (n, ()) ∅ (fun r m' => r = (v, ()) ∧ emp m') (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
          (evenOddCompiled.boundAt k) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = v ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
            (evenOddCompiled.boundAt k + 8) ⋆ R))
      ⟨s, Labels.label nm⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64]) (n, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ .nil⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns_emp hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton v st.data hrets, hcs, hsp', hm'⟩

/-- End-to-end machine `Eventually` correctness for mutually recursive `isEven` on Kraken x64. -/
theorem isEven_x64_correct (k₀ : Nat)
    (hc : evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) (n : BitVec 64) (hn : n.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
          (evenOddCompiled.boundAt k) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = isEvenVal n ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
            (evenOddCompiled.boundAt k + 8) ⋆ R))
      ⟨s, Labels.label "isEven"⟩ := by
  have hfn : x64Target.FnSpec hh "isEven" (isEvenSpec k) (evenOddCompiled.boundAt k) 0 :=
    (evenOdd_module_fnspec k₀ hc hu hk (fn := isEven) List.mem_cons_self).2
  exact evenOdd_x64_lift n (isEvenVal n) hfn ⟨hn, rfl, rfl⟩ s ra R hrdi hsp hmem

/-- End-to-end machine `Eventually` correctness for mutually recursive `isOdd` on Kraken x64. -/
theorem isOdd_x64_correct (k₀ : Nat)
    (hc : evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) (n : BitVec 64) (hn : n.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
          (evenOddCompiled.boundAt k) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = isOddVal n ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (evenOddCompiled.boundAt k))
            (evenOddCompiled.boundAt k + 8) ⋆ R))
      ⟨s, Labels.label "isOdd"⟩ := by
  have hfn : x64Target.FnSpec hh "isOdd" (isOddSpec k) (evenOddCompiled.boundAt k) 0 :=
    (evenOdd_module_fnspec k₀ hc hu hk (fn := isOdd)
      (List.mem_cons_of_mem _ List.mem_cons_self)).2
  exact evenOdd_x64_lift n (isOddVal n) hfn ⟨hn, rfl, rfl⟩ s ra R hrdi hsp hmem

/-- End-to-end machine `Eventually` correctness for fuel-guarded `recSum` (both normal return and
`"out_of_fuel"` exit) on Kraken x64. -/
theorem recSum_x64_correct (k₀ : Nat)
    (hc : recSumCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hexit : x64Target.Defined hh "out_of_fuel")
    {k : Nat} (hk : k ≤ 16) (n f : BitVec 64) (hf : f.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n) (hrsi : s.regs.get64 .rsi = f)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (recSumCompiled.boundAt k))
          (recSumCompiled.boundAt k) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (∃ sum, recSumOutcome n f.toNat = .inl sum ∧
          st.pc = ra ∧ st.data.regs.get64 .rax = sum ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
            st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64) ∨
        (∃ rem, recSumOutcome n f.toNat = .inr rem ∧
          st.pc = Labels.label "out_of_fuel" ∧ st.data.regs.get64 .rdi = rem ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0))
      ⟨s, Labels.label "recSum"⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (n, f, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ (.cons ⟨by decide, by simpa using hrsi⟩ .nil)⟩
  have hmem' : s.dmem =⋆ Eq (∅ : Mem 64) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (recSumCompiled.boundAt k))
          (recSumCompiled.boundAt k) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R := by
    rw [eq_empty_eq_emp, emp_sep]; exact hmem
  have hfn := (recSum_module_fnspec k₀ hc hu hexit hk).2
  have hspec := Examples.BenchmarkCertKit.recSum_spec_ok (k := k) n f hf
  refine eventually_weaken _ _ _ _ ?_ (x64_of_call_emp hfn hspec s ra R hargs hsp hmem')
  rintro st (⟨hpc, hcs, hsp', _, _, ⟨sum, hsum, rfl⟩, hrets, _⟩ |
    ⟨_, _, _, _, ⟨rfl, rem, hrem, rfl, rfl⟩, _, hpc, has', hspE⟩)
  · exact Or.inl ⟨sum, hsum, hpc, x64Init.retsIn_singleton sum st.data hrets, hcs, hsp'⟩
  · exact Or.inr ⟨rem, hrem, hpc, x64Init.argsIn_singleton rem st.data has', hspE⟩

end Generic

/-! ## 3. Concrete Non-Vacuous SysV x64 Execution Witnesses -/

abbrev evenOddHost : Host := evenOddCompiled.host
def evenOddState (k : Nat) (n : BitVec 64) : MachineData :=
  x64Init.initState (as := [i64]) (evenOddCompiled.boundAt k) [] (n, ())

attribute [local instance] evenOddHost in
theorem isEven_4_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1#64)
      ⟨evenOddState 4 4#64, Labels.label "isEven"⟩ :=
  Examples.BenchmarkCertKit.evenOdd_target_nonvacuous x64Init evenOddCompiled "isEven"
    (by decide : 4 ≤ 32)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 4 ≤ 32) List.mem_cons_self).2
    rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isEven_5_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0#64)
      ⟨evenOddState 5 5#64, Labels.label "isEven"⟩ :=
  Examples.BenchmarkCertKit.evenOdd_target_nonvacuous x64Init evenOddCompiled "isEven"
    (by decide : 5 ≤ 32)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 5 ≤ 32) List.mem_cons_self).2
    rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isOdd_4_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0#64)
      ⟨evenOddState 4 4#64, Labels.label "isOdd"⟩ :=
  Examples.BenchmarkCertKit.evenOdd_target_nonvacuous x64Init evenOddCompiled "isOdd"
    (by decide : 4 ≤ 32)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 4 ≤ 32) (List.mem_cons_of_mem _ List.mem_cons_self)).2
    rfl ⟨by decide, rfl⟩

attribute [local instance] evenOddHost in
theorem isOdd_5_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1#64)
      ⟨evenOddState 5 5#64, Labels.label "isOdd"⟩ :=
  Examples.BenchmarkCertKit.evenOdd_target_nonvacuous x64Init evenOddCompiled "isOdd"
    (by decide : 5 ≤ 32)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 5 ≤ 32) (List.mem_cons_of_mem _ List.mem_cons_self)).2
    rfl ⟨by decide, rfl⟩

abbrev recSumHost : Host := recSumCompiled.host
def recSumState (k : Nat) (n f : BitVec 64) : MachineData :=
  x64Init.initState (as := [i64, i64]) (recSumCompiled.boundAt k) [] (n, f, ())

attribute [local instance] recSumHost in
theorem recSum_normal_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 6#64)
      ⟨recSumState 5 3#64 5#64, Labels.label "recSum"⟩ := by
  have hfn := (recSum_module_fnspec 0 recSumCompiled.code_infix_host recSumCompiled.labelsUnique
    (recSumCompiled.defined_exit_host (by simp)) (by decide : 5 ≤ 16)).2
  have ho : recSumOutcome 3#64 (5#64).toNat = .inl 6#64 := by decide
  exact run_rec_ret1_i64 x64Init recSumCompiled (by decide : 5 ≤ 16) hfn [] (3#64, 5#64, ())
    6#64 (by decide) rfl ⟨by decide, by
      change match recSumOutcome 3#64 (5#64).toNat with
        | .inl s => (s, ()) = (6#64, ()) | .inr _ => False
      rw [ho]⟩ fun _ _ h => h

attribute [local instance] recSumHost in
theorem recSum_out_of_fuel_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "out_of_fuel" ∧ st.data.regs.get64 .rdi = 3#64)
      ⟨recSumState 2 5#64 2#64, Labels.label "recSum"⟩ := by
  have hfn := (recSum_module_fnspec 0 recSumCompiled.code_infix_host recSumCompiled.labelsUnique
    (recSumCompiled.defined_exit_host (by simp)) (by decide : 2 ≤ 16)).2
  have ho : recSumOutcome 5#64 (2#64).toNat = .inr 3#64 := by decide
  refine run_rec_fnSpec x64Init recSumCompiled (by decide : 2 ≤ 16) hfn [] (5#64, 2#64, ())
    (by decide) rfl (Q := fun _ _ => False) (X := fun g cs xs _ =>
      g = "out_of_fuel" ∧ cs = [i64] ∧ HEq xs ((3#64, ()) : Tup Val [i64]))
    ⟨by decide, by rw [ho]; exact ⟨rfl, rfl, HEq.rfl⟩⟩ ?_
  rintro st (⟨_, _, _, hq, _⟩ | ⟨_, _, _, _, ⟨rfl, rfl, hxs⟩, hpc, has⟩)
  · exact hq.elim
  · obtain rfl := eq_of_heq hxs; exact ⟨hpc, x64Init.argsIn_singleton 3#64 _ has⟩

end LeanQbe.T.Amd64.LinkRec
