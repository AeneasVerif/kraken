module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.LitmusProgsLemmas
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
import LeanQbe.T.Logic.MemLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.LitmusProgs

/-!
# Scalar Litmus Suite on SysV x64

Instantiates all 10 scalar litmus modules (`tracer`, `ifelse`, `sumto`, `evenodd`, `nested`, `swap`,
`spill10`, `callinc`, `twice` with abnormal exit `"fail"`, `sumcall`) on `x64Target`
(`x64LegalTarget`, `x64Layout`, `x64LabelClean`):
* external meta hint splicing (`splice_module_hints`) + single `t_kernel_rfl` per module;
* `*_fnspec` over arbitrary Kraken `Host` instances;
* closed Kraken x64 correctness theorems (`tracer_x64_correct`, `sumto_x64_correct`,
  `callinc_x64_correct`, `twice_x64_correct`, `spill10_x64_correct`, `sumcall_x64_correct`);
* concrete non-vacuous execution witnesses on `*.host` via `x64Init`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.Litmus

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Litmus LeanQbe.T.Amd64 Kraken

splice_module_hints tracerHints  (x64Target.toIsa) x64LegalTarget tracerModule.fns
splice_module_hints ifelseHints  (x64Target.toIsa) x64LegalTarget ifelseModule.fns
splice_module_hints sumtoHints   (x64Target.toIsa) x64LegalTarget sumtoModule.fns
splice_module_hints evenoddHints (x64Target.toIsa) x64LegalTarget evenoddModule.fns
splice_module_hints nestedHints  (x64Target.toIsa) x64LegalTarget nestedModule.fns
splice_module_hints swapHints    (x64Target.toIsa) x64LegalTarget swapModule.fns
splice_module_hints spill10Hints (x64Target.toIsa) x64LegalTarget spill10Module.fns
splice_module_hints callincHints (x64Target.toIsa) x64LegalTarget callincModule.fns
splice_module_hints twiceHints   (x64Target.toIsa) x64LegalTarget twiceModule.fns
splice_module_hints sumcallHints (x64Target.toIsa) x64LegalTarget sumcallModule.fns

/-! ## 1. Compiled Kernel Certificates -/

theorem tracer_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 tracerModule.fns tracerHints 2048 =
      true := by t_kernel_rfl

theorem ifelse_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 ifelseModule.fns ifelseHints 2048 =
      true := by t_kernel_rfl

theorem sumto_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 sumtoModule.fns sumtoHints 2048 =
      true := by t_kernel_rfl

theorem evenodd_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 evenoddModule.fns evenoddHints 2048 =
      true := by t_kernel_rfl

theorem nested_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 nestedModule.fns nestedHints 2048 =
      true := by t_kernel_rfl

theorem swap_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 swapModule.fns swapHints 2048 =
      true := by t_kernel_rfl

theorem spill10_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 spill10Module.fns spill10Hints 2048 =
      true := by t_kernel_rfl

theorem callinc_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 callincModule.fns callincHints 2048 =
      true := by t_kernel_rfl

theorem twice_check :
    checkCompile x64Target x64Layout x64LegalTarget [] ["fail"] 0 twiceModule.fns twiceHints 2048 =
      true := by t_kernel_rfl

theorem sumcall_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 sumcallModule.fns sumcallHints 2048 =
      true := by t_kernel_rfl

def tracerCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 tracerModule.fns tracerHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 tracerModule.fns tracerHints 2048 tracer_check

def ifelseCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 ifelseModule.fns ifelseHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 ifelseModule.fns ifelseHints 2048 ifelse_check

def sumtoCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 sumtoModule.fns sumtoHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 sumtoModule.fns sumtoHints 2048 sumto_check

def evenoddCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 evenoddModule.fns evenoddHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 evenoddModule.fns evenoddHints 2048 evenodd_check

def nestedCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 nestedModule.fns nestedHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 nestedModule.fns nestedHints 2048 nested_check

def swapCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 swapModule.fns swapHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 swapModule.fns swapHints 2048 swap_check

def spill10Compiled :
    Compiled x64Target x64LegalTarget [] [] 0 spill10Module.fns spill10Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 spill10Module.fns spill10Hints 2048 spill10_check

def callincCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 callincModule.fns callincHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 callincModule.fns callincHints 2048 callinc_check

def twiceCompiled :
    Compiled x64Target x64LegalTarget [] ["fail"] 0 twiceModule.fns twiceHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] ["fail"] 0 twiceModule.fns twiceHints 2048 twice_check

def sumcallCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 sumcallModule.fns sumcallHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 sumcallModule.fns sumcallHints 2048 sumcall_check

/-! ## 2. Module Linking Helpers (`allFns` `Wf` & `supportsSource`) -/

private theorem allFns_supportsSource_all :
    allFns.all (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

private theorem litmus_single_x64 {hh : Host} {f : Fn} {hints : List x64Target.toIsa.Hints}
    (M : Compiled x64Target x64LegalTarget [] [] 0 [f] hints 2048)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hf : f ∈ allFns) (k₀ : Nat) (hc : M.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (has : x64LegalTarget.legalSig f.as = f.as)
    (hrs : x64LegalTarget.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X',
      litmusEnv f.name f.as f.rs args m Q X → litmusEnv f.name f.as f.rs args m Q X') :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (litmusEnv f.name f.as f.rs) (M.bound f.name) 0 :=
  Examples.BenchmarkCertKit.litmus_single_fnspec_gen M hh
    (supportsAll_to_forall allFns_supportsSource_all) hacyc hf k₀ hc hu has hrs hnoex

/-! ## 3. Generic `FnSpec` and Closed Kraken x64 Theorems -/

section Generic
variable [hh : Host]

theorem tracer_fnspec (k₀ : Nat) (hc : tracerCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "tracer" ∧
      x64Target.FnSpec hh "tracer" tracerContract (tracerCompiled.bound "tracer") 0 :=
  litmus_single_x64 tracerCompiled tracerModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem ifelse_fnspec (k₀ : Nat) (hc : ifelseCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "ifelse" ∧
      x64Target.FnSpec hh "ifelse" ifelseContract (ifelseCompiled.bound "ifelse") 0 :=
  litmus_single_x64 ifelseCompiled ifelseModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem sumto_fnspec (k₀ : Nat) (hc : sumtoCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "sumto" ∧
      x64Target.FnSpec hh "sumto" sumtoContract (sumtoCompiled.bound "sumto") 0 :=
  litmus_single_x64 sumtoCompiled sumtoModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem evenodd_fnspec (k₀ : Nat) (hc : evenoddCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "evenodd" ∧
      x64Target.FnSpec hh "evenodd" evenoddContract (evenoddCompiled.bound "evenodd") 0 :=
  litmus_single_x64 evenoddCompiled evenoddModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem nested_fnspec (k₀ : Nat) (hc : nestedCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "nested" ∧
      x64Target.FnSpec hh "nested" nestedContract (nestedCompiled.bound "nested") 0 :=
  litmus_single_x64 nestedCompiled nestedModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem swap_fnspec (k₀ : Nat) (hc : swapCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "swap" ∧
      x64Target.FnSpec hh "swap" swapContract (swapCompiled.bound "swap") 0 :=
  litmus_single_x64 swapCompiled swapModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem spill10_fnspec (k₀ : Nat) (hc : spill10Compiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "spill10" ∧
      x64Target.FnSpec hh "spill10" spill10Contract (spill10Compiled.bound "spill10") 0 :=
  litmus_single_x64 spill10Compiled spill10Module_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem callinc_module_fnspec (k₀ : Nat)
    (hc : callincCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hf : fn ∈ callincModule.fns) :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (callincCompiled.bound fn.name) 0 :=
  Examples.BenchmarkCertKit.litmus_twoFn_fnspec_gen callincModule rfl callincModule_acyclic
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (fun g hg => by simp [callincModule] at hg; rcases hg with rfl | rfl <;> simp [allFns])
    (fun g hg => by
      simp [callincModule] at hg; rcases hg with rfl | rfl <;> exact fun _ _ _ _ _ h => h)
    callincCompiled hh rfl (supportsAll_to_forall allFns_supportsSource_all) k₀ hc hu hf

theorem sumcall_module_fnspec (k₀ : Nat)
    (hc : sumcallCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hf : fn ∈ sumcallModule.fns) :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (sumcallCompiled.bound fn.name) 0 :=
  Examples.BenchmarkCertKit.litmus_twoFn_fnspec_gen sumcallModule rfl sumcallModule_acyclic
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (fun g hg => by simp [sumcallModule] at hg; rcases hg with rfl | rfl <;> simp [allFns])
    (fun g hg => by
      simp [sumcallModule] at hg; rcases hg with rfl | rfl <;> exact fun _ _ _ _ _ h => h)
    sumcallCompiled hh rfl (supportsAll_to_forall allFns_supportsSource_all) k₀ hc hu hf

theorem twice_module_fnspec (k₀ : Nat)
    (hc : twiceCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : x64Target.Defined hh "fail") {fn : Fn} (hf : fn ∈ twiceModule.fns) :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (twiceCompiled.bound fn.name) 0 :=
  Examples.BenchmarkCertKit.twice_module_fnspec_gen twiceCompiled hh rfl
    (supportsAll_to_forall allFns_supportsSource_all) k₀ hc hu hfail hf

/-- End-to-end correctness of `tracer` on Kraken x64 (`cell64 p v0 ↦ cell64 p (a + b)`). -/
theorem tracer_x64_correct (k₀ : Nat) (hc : tracerCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b p v0 : BitVec 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b) (hpp : s.regs.get64 .rdx = p)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v0 ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))
          (tracerCompiled.bound "tracer") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ cell64 p (a + b) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))
            (tracerCompiled.bound "tracer" + 8) ⋆ R))
      ⟨s, Labels.label "tracer"⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64, i64]) (a, b, p, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using ha⟩
      (.cons ⟨by decide, by simpa using hb⟩ (.cons ⟨by decide, by simpa using hpp⟩ .nil))⟩
  obtain ⟨m, hm, hmEq⟩ := BenchmarkCertKit.sep_extract_eq hmem
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns (tracer_fnspec k₀ hc hu).2
      (Examples.BenchmarkCertKit.tracer_spec_ok a b p v0 hm) s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', ⟨rfl, hcell⟩, hrets, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (a + b) st.data hrets, hcs, hsp',
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hcell)) hm'⟩

/-- End-to-end correctness of `sumto` on Kraken x64. -/
theorem sumto_x64_correct (k₀ : Nat) (hc : sumtoCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (n : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (sumtoCompiled.bound "sumto"))
          (sumtoCompiled.bound "sumto") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = tri n.toNat ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (sumtoCompiled.bound "sumto"))
            (sumtoCompiled.bound "sumto" + 8) ⋆ R))
      ⟨s, Labels.label "sumto"⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64]) (n, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ .nil⟩
  have hspec : sumtoContract (n, ()) ∅ (fun r m' => r = (tri n.toNat, ()) ∧ emp m')
      (fun _ _ _ _ => False) := ⟨hn, rfl, rfl⟩
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns_emp (sumto_fnspec k₀ hc hu).2 hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (tri n.toNat) st.data hrets, hcs, hsp', hm'⟩

private theorem litmus_ret2_x64_lift {sym : Sym} {b : Nat} {spec : Spec [i64, i64] [i64]}
    {x y v : BitVec 64}
    (hfn : x64Target.FnSpec hh sym spec b 0)
    (hspec : spec (x, y, ()) ∅ (fun r m' => r = (v, ()) ∧ emp m') (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx : s.regs.get64 .rdi = x) (hy : s.regs.get64 .rsi = y)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = v ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (x, y, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hx⟩ (.cons ⟨by decide, by simpa using hy⟩ .nil)⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns_emp hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton v st.data hrets, hcs, hsp', hm'⟩

/-- End-to-end correctness of `callinc` on Kraken x64. -/
theorem callinc_x64_correct (k₀ : Nat)
    (hc : callincCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (callincCompiled.bound "callinc"))
          (callincCompiled.bound "callinc") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = a + 1 + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (callincCompiled.bound "callinc"))
            (callincCompiled.bound "callinc" + 8) ⋆ R))
      ⟨s, Labels.label "callinc"⟩ := by
  have hfn : x64Target.FnSpec hh "callinc" callincContract (callincCompiled.bound "callinc") 0 :=
    (callinc_module_fnspec k₀ hc hu (fn := callinc) (by simp [callincModule])).2
  exact litmus_ret2_x64_lift hfn ⟨rfl, rfl⟩ s ra R ha hb hsp hmem

/-- End-to-end correctness of `twice` (including abnormal exit `"fail"`) on Kraken x64. -/
theorem twice_x64_correct (k₀ : Nat)
    (hc : twiceCompiled.code.IsInfixAt Host.prog k₀)
    (hfail : x64Target.Defined hh "fail") (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (twiceCompiled.bound "twice"))
          (twiceCompiled.bound "twice") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (Truthy a ∧ Truthy b ∧ st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
            st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64) ∨
        ((¬Truthy a ∧ st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = a ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0) ∨
         (Truthy a ∧ ¬Truthy b ∧ st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = b ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0)))
      ⟨s, Labels.label "twice"⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (a, b, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using ha⟩ (.cons ⟨by decide, by simpa using hb⟩ .nil)⟩
  have hmem' : s.dmem =⋆ Eq (∅ : Mem 64) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (twiceCompiled.bound "twice"))
          (twiceCompiled.bound "twice") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R := by
    rw [eq_empty_eq_emp, emp_sep]; exact hmem
  have hfn : x64Target.FnSpec hh "twice" twiceContract (twiceCompiled.bound "twice") 0 :=
    (twice_module_fnspec k₀ hc hu hfail (fn := twice) (by simp [twiceModule])).2
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_call_emp hfn (Examples.BenchmarkCertKit.twice_spec_ok a b) s ra R hargs hsp hmem')
  rintro st (⟨hpc, hcs, hsp', _, _, ⟨hta, htb, rfl, _⟩, hrets, _⟩ |
    ⟨_, _, _, _, ⟨rfl, rfl, _, hcase⟩, _, hpc, has', hspE⟩)
  · exact Or.inl ⟨hta, htb, hpc, x64Init.retsIn_singleton (a + b) st.data hrets, hcs, hsp'⟩
  · rcases hcase with ⟨hna, rfl⟩ | ⟨hta, hnb, rfl⟩
    · exact Or.inr (Or.inl ⟨hna, hpc, x64Init.argsIn_singleton a st.data has', hspE⟩)
    · exact Or.inr (Or.inr ⟨hta, hnb, hpc, x64Init.argsIn_singleton b st.data has', hspE⟩)

/-- End-to-end correctness of `spill10` on Kraken x64. -/
theorem spill10_x64_correct (k₀ : Nat) (hc : spill10Compiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b : BitVec 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (spill10Compiled.bound "spill10"))
          (spill10Compiled.bound "spill10") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = spill10Val a b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (spill10Compiled.bound "spill10"))
            (spill10Compiled.bound "spill10" + 8) ⋆ R))
      ⟨s, Labels.label "spill10"⟩ :=
  litmus_ret2_x64_lift (spill10_fnspec k₀ hc hu).2 ⟨rfl, rfl⟩ s ra R ha hb hsp hmem

/-- End-to-end correctness of `sumcall` (call in loop body) on Kraken x64. -/
theorem sumcall_x64_correct (k₀ : Nat)
    (hc : sumcallCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (n b : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n) (hrsi : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (sumcallCompiled.bound "sumcall"))
          (sumcallCompiled.bound "sumcall") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = tri n.toNat + n + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (sumcallCompiled.bound "sumcall"))
            (sumcallCompiled.bound "sumcall" + 8) ⋆ R))
      ⟨s, Labels.label "sumcall"⟩ := by
  have hfn : x64Target.FnSpec hh "sumcall" sumcallContract (sumcallCompiled.bound "sumcall") 0 :=
    (sumcall_module_fnspec k₀ hc hu (fn := sumcall) (by simp [sumcallModule])).2
  exact litmus_ret2_x64_lift hfn ⟨hn, rfl, rfl⟩ s ra R hrdi hrsi hsp hmem

end Generic

/-! ## 4. Concrete SysV x64 Execution Witnesses -/

abbrev zeros8 : List UInt8 := Examples.BenchmarkCertKit.zeros8

abbrev tracerHost : Host := tracerCompiled.host
def tracerState0 : MachineData :=
  x64Init.initState (as := [i64, i64, i64]) (tracerCompiled.bound "tracer") zeros8
    (40#64, 2#64, 0x1000#64, ())

attribute [local instance] tracerHost in
theorem tracer_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42#64 ∧
        (st.data.dmem =⋆ cell64 0x1000#64 42#64 ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))
            (tracerCompiled.bound "tracer" + 8) ⋆ emp))
      ⟨tracerState0, Labels.label "tracer"⟩ := by
  refine eventually_weaken _ _ _ _
    (fun st ⟨hpc, hrax, hm⟩ => ⟨hpc, hrax, by
      simpa only [Target.Exit, x64Target, x64FrameTarget, x64FramePreds, x64Frame, x64Init] using
        hm⟩)
    (x64Init.run_ret1_sep_i64 tracerCompiled
      (tracer_fnspec 0 tracerCompiled.code_infix_host tracerCompiled.labelsUnique).2
      zeros8 (40#64, 2#64, 0x1000#64, ()) 42#64 (cell64 0x1000#64 42#64) (by decide) rfl
      (Examples.BenchmarkCertKit.tracer_spec_ok 40#64 2#64 0x1000#64 0#64 rfl) fun _ _ h => h)

abbrev sumtoHost : Host := sumtoCompiled.host
def sumtoState : MachineData :=
  x64Init.initState (as := [i64]) (sumtoCompiled.bound "sumto") [] (3#64, ())

attribute [local instance] sumtoHost in
theorem sumto_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 6#64)
      ⟨sumtoState, Labels.label "sumto"⟩ :=
  x64Init.run_ret1_i64 sumtoCompiled
    (sumto_fnspec 0 sumtoCompiled.code_infix_host sumtoCompiled.labelsUnique).2
    [] (3#64, ()) 6#64 (by decide) rfl (Q := fun r _ => r = (6#64, ()))
    ⟨by decide, rfl⟩ fun _ _ h => h

abbrev callincHost : Host := callincCompiled.host
def callincState : MachineData :=
  x64Init.initState (as := [i64, i64]) (callincCompiled.bound "callinc") [] (40#64, 1#64, ())

attribute [local instance] callincHost in
theorem callinc_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42#64)
      ⟨callincState, Labels.label "callinc"⟩ := by
  have hfn : x64Target.FnSpec callincHost "callinc" callincContract
      (callincCompiled.bound "callinc") 0 :=
    (callinc_module_fnspec 0 callincCompiled.code_infix_host callincCompiled.labelsUnique
      (fn := callinc) (by simp [callincModule])).2
  exact x64Init.run_ret1_i64 callincCompiled hfn [] (40#64, 1#64, ()) 42#64 (by decide) rfl
    (Q := fun r _ => r = (42#64, ())) rfl fun _ _ h => h

abbrev twiceHost : Host := twiceCompiled.host
def twiceState (a b : BitVec 64) : MachineData :=
  x64Init.initState (as := [i64, i64]) (twiceCompiled.bound "twice") [] (a, b, ())

attribute [local instance] twiceHost in
theorem twice_x64_nonvacuous_exit :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = 0#64)
      ⟨twiceState 20#64 0#64, Labels.label "twice"⟩ := by
  have hfn : x64Target.FnSpec twiceHost "twice" twiceContract (twiceCompiled.bound "twice") 0 :=
    (twice_module_fnspec 0 twiceCompiled.code_infix_host twiceCompiled.labelsUnique
      (twiceCompiled.defined_exit_host (by simp)) (fn := twice) (by simp [twiceModule])).2
  refine x64Init.run_fnSpec twiceCompiled hfn [] (20#64, 0#64, ()) (by decide) rfl
    (Q := fun _ _ => False)
    (X := fun g cs xs _ => ∃ h : cs = [i64], g = "fail" ∧ xs = h ▸ (0#64, ()))
    ⟨fun _ h0 => absurd h0 (by simp [Truthy]),
      fun h20 => absurd (by simp [Truthy] : Truthy 20#64) h20, fun _ _ => ⟨rfl, rfl, rfl⟩⟩ ?_
  rintro st (⟨_, _, _, hq, _⟩ | ⟨_, _, _, _, ⟨rfl, rfl, rfl⟩, hpc, has⟩)
  · exact hq.elim
  · exact ⟨hpc, x64Init.argsIn_singleton 0#64 _ has⟩

abbrev spill10Host : Host := spill10Compiled.host
def spill10State : MachineData :=
  x64Init.initState (as := [i64, i64]) (spill10Compiled.bound "spill10") [] (10#64, 7#64, ())

attribute [local instance] spill10Host in
theorem spill10_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = spill10Val 10#64 7#64)
      ⟨spill10State, Labels.label "spill10"⟩ :=
  x64Init.run_ret1_i64 spill10Compiled
    (spill10_fnspec 0 spill10Compiled.code_infix_host spill10Compiled.labelsUnique).2
    [] (10#64, 7#64, ()) (spill10Val 10#64 7#64) (by decide) rfl
    (Q := fun r _ => r = (spill10Val 10#64 7#64, ())) rfl fun _ _ h => h

abbrev sumcallHost : Host := sumcallCompiled.host
def sumcallState : MachineData :=
  x64Init.initState (as := [i64, i64]) (sumcallCompiled.bound "sumcall") [] (3#64, 10#64, ())

attribute [local instance] sumcallHost in
theorem sumcall_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 19#64)
      ⟨sumcallState, Labels.label "sumcall"⟩ := by
  have hfn : x64Target.FnSpec sumcallHost "sumcall" sumcallContract
      (sumcallCompiled.bound "sumcall") 0 :=
    (sumcall_module_fnspec 0 sumcallCompiled.code_infix_host sumcallCompiled.labelsUnique
      (fn := sumcall) (by simp [sumcallModule])).2
  exact x64Init.run_ret1_i64 sumcallCompiled hfn [] (3#64, 10#64, ()) 19#64 (by decide) rfl
    (Q := fun r _ => r = (19#64, ())) ⟨by decide, rfl⟩ fun _ _ h => h

end LeanQbe.T.Amd64.Litmus
