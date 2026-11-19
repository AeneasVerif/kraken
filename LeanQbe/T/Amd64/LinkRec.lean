module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.LinkRecLemmas
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.LinkRecLemmas

/-!
# Cyclic & Mutual-Recursion Linking on SysV x64 (`B1.1`)

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

private theorem evenOdd_wf_mem : ∀ f ∈ evenOddRecMod.fns, f.Wf := by
  intro f hf
  simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> first | exact isEven_wf | exact isOdd_wf

private theorem evenOdd_supports_mem :
    ∀ f ∈ evenOddRecMod.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  fun f hf => List.all_eq_true.mp evenOdd_supports_all f hf

private theorem eq_empty_eq_emp : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
  funext m; exact propext eq_comm

private theorem legal_xpost_aux (X : XPost) (g : Sym) (m : Mem 64) {ts : List Ty}
    {xs : Tup Val ts} {ys : Tup Val [i64]} (h1 : ts = [i64]) (h2 : HEq xs ys)
    (hx : X g [i64] ys m) : X g ts xs m := by
  subst h1; cases eq_of_heq h2; exact hx

private theorem legal_xpost_i64 {lt : LegalTarget} (h : lt.legalSig [i64] = [i64])
    {X : XPost} {g : Sym} {v : BitVec 64} {m : Mem 64}
    (hx : X g [i64] (v, ()) m) :
    X g (lt.legalSig [i64]) (encodeTup lt [i64] (v, ())) m := by
  rw [encodeTup_eq_cast_of_legalSig_eq h]
  exact legal_xpost_aux X g m h (cast_heq _ _) hx

section Generic

variable {hh : Host}

/-- Arbitrary-`Host` measure-indexed `FnSpec` linking for mutually recursive `{isEven, isOdd}`. -/
theorem evenOdd_module_fnspec (k₀ : Nat)
    (hc : evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) {fn : Fn} (hf : fn ∈ evenOddRecMod.fns) :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (evenOddRecEnv k fn.name fn.as fn.rs)
        (evenOddCompiled.boundAt k) 0 := by
  have hmem := hf
  simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs, hnoex⟩ : x64LegalTarget.legalSig fn.as = fn.as ∧
      x64LegalTarget.legalSig fn.rs = fn.rs ∧
      (∀ args m Q X X', evenOddRecEnv k fn.name fn.as fn.rs args m Q X →
        evenOddRecEnv k fn.name fn.as fn.rs args m Q X') := by
    rcases hmem with rfl | rfl <;> exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
  have hrec := link_rec_compiled evenOddCompiled evenOddRecMod rfl hh evenOddRecEnv
    (fun _ _ _ _ _ _ _ => False) k₀ hc hu evenOddRecMod_checkCyclic evenOdd_wf_mem
    evenOdd_supports_mem (fun k' _ fn' hf' => evenOddRecMod_wp_step k' fn' hf')
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) k hk fn hf
  exact ⟨hrec.1, Target.FnSpec.of_spec x64Target (fnSpec_of_legalEnv_onlyFn has hrs hrec.2)
    fun args m Q X h => hnoex args m Q X _ h⟩

/-- Arbitrary-`Host` measure-indexed `FnSpec` linking for fuel-guarded `recSum` with
`"out_of_fuel"` exit. -/
theorem recSum_module_fnspec (k₀ : Nat)
    (hc : recSumCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hexit : x64Target.Defined hh "out_of_fuel") {k : Nat} (hk : k ≤ 16) :
    x64Target.Defined hh "recSum" ∧
      x64Target.FnSpec hh "recSum" (recSumSpec k) (recSumCompiled.boundAt k) 16 := by
  have hrec := link_rec_compiled recSumCompiled recSumMod rfl hh recSumRecEnv
    (fun _ _ _ _ _ _ _ => False) k₀ hc hu recSumMod_checkCyclic
    (fun f hf => by simp [recSumMod] at hf; subst hf; exact recSum_wf)
    (fun f hf => List.all_eq_true.mp recSum_supports_all f hf)
    (fun k' _ fn' hf' => recSumMod_wp_step k' fn' hf')
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun g hg => by simp at hg; subst hg; exact hexit)
    k hk recSum List.mem_cons_self
  have hfn' := fnSpec_of_legalEnv_onlyFn (f := recSum) (Γ := recSumRecEnv k) rfl rfl hrec.2
  refine ⟨hrec.1, Target.FnSpec.of_spec x64Target hfn' ?_⟩
  rintro ⟨n, f, ⟨⟩⟩ m Q X ⟨hf, hout⟩
  refine ⟨hf, ?_⟩
  cases ho : recSumOutcome n f.toNat with
  | inl s => rw [ho] at hout; exact hout
  | inr rem =>
    rw [ho] at hout
    exact legal_xpost_i64 (lt := x64LegalTarget) rfl hout

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
  have hargs : x64Target.ArgsIn (as := [i64]) (n, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ .nil⟩
  have hfn : x64Target.FnSpec hh "isEven" (isEvenSpec k) (evenOddCompiled.boundAt k) 0 :=
    (evenOdd_module_fnspec k₀ hc hu hk (fn := isEven) List.mem_cons_self).2
  have hspec : isEvenSpec k (n, ()) ∅ (fun r m' => r = (isEvenVal n, ()) ∧ emp m')
      (fun _ _ _ _ => False) := ⟨hn, rfl, rfl⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns_emp hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (isEvenVal n) st.data hrets, hcs, hsp', hm'⟩

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
  have hargs : x64Target.ArgsIn (as := [i64]) (n, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ .nil⟩
  have hfn : x64Target.FnSpec hh "isOdd" (isOddSpec k) (evenOddCompiled.boundAt k) 0 :=
    (evenOdd_module_fnspec k₀ hc hu hk (fn := isOdd)
      (List.mem_cons_of_mem _ List.mem_cons_self)).2
  have hspec : isOddSpec k (n, ()) ∅ (fun r m' => r = (isOddVal n, ()) ∧ emp m')
      (fun _ _ _ _ => False) := ⟨hn, rfl, rfl⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns_emp hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (isOddVal n) st.data hrets, hcs, hsp', hm'⟩

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
  have hspec : recSumSpec k (n, f, ()) ∅
      (fun r _ => ∃ sum, recSumOutcome n f.toNat = .inl sum ∧ r = (sum, ()))
      (fun g cs xs _ => ∃ h : cs = [i64], ∃ rem, recSumOutcome n f.toNat = .inr rem ∧
        g = "out_of_fuel" ∧ xs = h ▸ (rem, ())) := by
    refine ⟨hf, ?_⟩
    cases ho : recSumOutcome n f.toNat with
    | inl s' => exact ⟨s', rfl, rfl⟩
    | inr rem => exact ⟨rfl, rem, rfl, rfl, rfl⟩
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
  run_rec_ret1_i64 x64Init (as := [i64]) evenOddCompiled (by decide : 4 ≤ 32)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 4 ≤ 32) List.mem_cons_self).2
    [] (4#64, ()) 1#64 (by decide) rfl (Q := fun r _ => r = (1#64, ()))
    ⟨by decide, rfl⟩ fun _ _ h => h

attribute [local instance] evenOddHost in
theorem isEven_5_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0#64)
      ⟨evenOddState 5 5#64, Labels.label "isEven"⟩ :=
  run_rec_ret1_i64 x64Init (as := [i64]) evenOddCompiled (by decide : 5 ≤ 32)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 5 ≤ 32) List.mem_cons_self).2
    [] (5#64, ()) 0#64 (by decide) rfl (Q := fun r _ => r = (0#64, ()))
    ⟨by decide, rfl⟩ fun _ _ h => h

attribute [local instance] evenOddHost in
theorem isOdd_4_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0#64)
      ⟨evenOddState 4 4#64, Labels.label "isOdd"⟩ :=
  run_rec_ret1_i64 x64Init (as := [i64]) evenOddCompiled (by decide : 4 ≤ 32)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 4 ≤ 32) (List.mem_cons_of_mem _ List.mem_cons_self)).2
    [] (4#64, ()) 0#64 (by decide) rfl (Q := fun r _ => r = (0#64, ()))
    ⟨by decide, rfl⟩ fun _ _ h => h

attribute [local instance] evenOddHost in
theorem isOdd_5_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1#64)
      ⟨evenOddState 5 5#64, Labels.label "isOdd"⟩ :=
  run_rec_ret1_i64 x64Init (as := [i64]) evenOddCompiled (by decide : 5 ≤ 32)
    (evenOdd_module_fnspec 0 evenOddCompiled.code_infix_host evenOddCompiled.labelsUnique
      (by decide : 5 ≤ 32) (List.mem_cons_of_mem _ List.mem_cons_self)).2
    [] (5#64, ()) 1#64 (by decide) rfl (Q := fun r _ => r = (1#64, ()))
    ⟨by decide, rfl⟩ fun _ _ h => h

abbrev recSumHost : Host := recSumCompiled.host
def recSumState (k : Nat) (n f : BitVec 64) : MachineData :=
  x64Init.initState (as := [i64, i64]) (recSumCompiled.boundAt k) [] (n, f, ())

attribute [local instance] recSumHost in
theorem recSum_normal_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 6#64)
      ⟨recSumState 5 3#64 5#64, Labels.label "recSum"⟩ := by
  have ho : recSumOutcome 3#64 (5#64).toNat = .inl 6#64 := by decide
  refine run_rec_fnSpec x64Init (as := [i64, i64]) recSumCompiled (by decide : 5 ≤ 16)
    (recSum_module_fnspec 0 recSumCompiled.code_infix_host recSumCompiled.labelsUnique
      (recSumCompiled.defined_exit_host (by simp)) (by decide : 5 ≤ 16)).2
    [] (3#64, 5#64, ()) (by decide) rfl (Q := fun r _ => r = (6#64, ()))
    (X := fun _ _ _ _ => False) ⟨by decide, by change match recSumOutcome 3#64 (5#64).toNat with
      | .inl s => (s, ()) = (6#64, ()) | .inr _ => False; rw [ho]⟩ ?_
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · subst hq; exact ⟨hpc, x64Init.retsIn_singleton 6#64 _ hrets⟩
  · exact hx.elim

attribute [local instance] recSumHost in
theorem recSum_out_of_fuel_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "out_of_fuel" ∧ st.data.regs.get64 .rdi = 3#64)
      ⟨recSumState 2 5#64 2#64, Labels.label "recSum"⟩ := by
  have ho : recSumOutcome 5#64 (2#64).toNat = .inr 3#64 := by decide
  refine run_rec_fnSpec x64Init (as := [i64, i64]) recSumCompiled (by decide : 2 ≤ 16)
    (recSum_module_fnspec 0 recSumCompiled.code_infix_host recSumCompiled.labelsUnique
      (recSumCompiled.defined_exit_host (by simp)) (by decide : 2 ≤ 16)).2
    [] (5#64, 2#64, ()) (by decide) rfl (Q := fun _ _ => False)
    (X := fun g cs xs _ => g = "out_of_fuel" ∧ cs = [i64] ∧
      HEq xs ((3#64, ()) : Tup Val [i64]))
    ⟨by decide, by rw [ho]; exact ⟨rfl, rfl, HEq.rfl⟩⟩ ?_
  rintro st (⟨_, _, _, hq, _⟩ | ⟨_, _, _, _, ⟨rfl, rfl, hxs⟩, hpc, has⟩)
  · exact hq.elim
  · obtain rfl := eq_of_heq hxs; exact ⟨hpc, x64Init.argsIn_singleton 3#64 st.data has⟩

end LeanQbe.T.Amd64.LinkRec
