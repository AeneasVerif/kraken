module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.LitmusProgsLemmas
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.LitmusProgs

/-!
# Scalar Litmus Suite on SysV x64 (`T12i`)

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

private theorem litmus_allFns_wf : ∀ fn ∈ allFns, fn.Wf := by
  intro fn hfn
  simp only [allFns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tracer_wf
  · exact ifelse_wf
  · exact sumto_wf
  · exact evenodd_wf
  · exact nested_wf
  · exact swap_wf
  · exact inc_wf
  · exact callinc_wf
  · exact check_wf
  · exact twice_wf
  · exact spill10_wf
  · exact sumcall_wf

private theorem allFns_supportsSource_all :
    allFns.all (fun f => (f.opt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

private theorem litmus_allFns_supports :
    ∀ fn ∈ allFns, (fn.opt).body.supportsSource x64LegalTarget = true :=
  fun fn h => List.all_eq_true.mp allFns_supportsSource_all fn h

private theorem noExit_module_fnspec {hh : Host} {mod : Module}
    {hints : List x64Target.toIsa.Hints}
    (M : Compiled x64Target x64LegalTarget [] [] 0 mod.fns hints 2048)
    (hacyc : mod.checkAcyclic = true) (hsub : ∀ fn ∈ mod.fns, fn ∈ allFns)
    (k₀ : Nat) (hc : M.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hf : fn ∈ mod.fns)
    (has : x64LegalTarget.legalSig fn.as = fn.as)
    (hrs : x64LegalTarget.legalSig fn.rs = fn.rs)
    (hnoex : ∀ args m Q X X',
      litmusEnv fn.name fn.as fn.rs args m Q X → litmusEnv fn.name fn.as fn.rs args m Q X') :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs) (M.bound fn.name) 0 := by
  obtain ⟨hdef, hspec⟩ := M.fnSpec mod rfl hh litmusEnv k₀ hc hu hacyc
    (fun g hg => litmus_allFns_wf g (hsub g hg))
    (fun g hg => litmus_allFns_supports g (hsub g hg))
    (fun g hg => litmusEnv_sound g (hsub g hg))
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

private theorem single_fnspec {hh : Host} {f : Fn}
    {hints : List x64Target.toIsa.Hints}
    (M : Compiled x64Target x64LegalTarget [] [] 0 [f] hints 2048)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hf : f ∈ allFns) (k₀ : Nat) (hc : M.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (has : x64LegalTarget.legalSig f.as = f.as)
    (hrs : x64LegalTarget.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X',
      litmusEnv f.name f.as f.rs args m Q X → litmusEnv f.name f.as f.rs args m Q X') :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (litmusEnv f.name f.as f.rs) (M.bound f.name) 0 :=
  noExit_module_fnspec (mod := ⟨[f], [], []⟩) M hacyc
    (fun g hg => by simp at hg; subst hg; exact hf) k₀ hc hu List.mem_cons_self has hrs hnoex

private theorem eq_empty_eq_emp : (Eq (∅ : Mem 64)) = emp := by
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

/-! ## 3. Generic `FnSpec` and Closed Kraken x64 Theorems -/

section Generic
variable [hh : Host]

theorem tracer_fnspec (k₀ : Nat) (hc : tracerCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "tracer" ∧
      x64Target.FnSpec hh "tracer" tracerContract (tracerCompiled.bound "tracer") 0 :=
  single_fnspec tracerCompiled tracerModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem ifelse_fnspec (k₀ : Nat) (hc : ifelseCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "ifelse" ∧
      x64Target.FnSpec hh "ifelse" ifelseContract (ifelseCompiled.bound "ifelse") 0 :=
  single_fnspec ifelseCompiled ifelseModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem sumto_fnspec (k₀ : Nat) (hc : sumtoCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "sumto" ∧
      x64Target.FnSpec hh "sumto" sumtoContract (sumtoCompiled.bound "sumto") 0 :=
  single_fnspec sumtoCompiled sumtoModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem evenodd_fnspec (k₀ : Nat) (hc : evenoddCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "evenodd" ∧
      x64Target.FnSpec hh "evenodd" evenoddContract (evenoddCompiled.bound "evenodd") 0 :=
  single_fnspec evenoddCompiled evenoddModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem nested_fnspec (k₀ : Nat) (hc : nestedCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "nested" ∧
      x64Target.FnSpec hh "nested" nestedContract (nestedCompiled.bound "nested") 0 :=
  single_fnspec nestedCompiled nestedModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem swap_fnspec (k₀ : Nat) (hc : swapCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "swap" ∧
      x64Target.FnSpec hh "swap" swapContract (swapCompiled.bound "swap") 0 :=
  single_fnspec swapCompiled swapModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem spill10_fnspec (k₀ : Nat) (hc : spill10Compiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    x64Target.Defined hh "spill10" ∧
      x64Target.FnSpec hh "spill10" spill10Contract (spill10Compiled.bound "spill10") 0 :=
  single_fnspec spill10Compiled spill10Module_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem callinc_module_fnspec (k₀ : Nat)
    (hc : callincCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hf : fn ∈ callincModule.fns) :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (callincCompiled.bound fn.name) 0 := by
  have hmem := hf
  simp only [callincModule, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs, hnoex⟩ :
      x64LegalTarget.legalSig fn.as = fn.as ∧ x64LegalTarget.legalSig fn.rs = fn.rs ∧
        (∀ args m Q X X', litmusEnv fn.name fn.as fn.rs args m Q X →
          litmusEnv fn.name fn.as fn.rs args m Q X') := by
    rcases hmem with rfl | rfl <;> exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
  exact noExit_module_fnspec callincCompiled callincModule_acyclic
    (fun g hg => by simp [callincModule] at hg; rcases hg with rfl | rfl <;> simp [allFns])
    k₀ hc hu hf has hrs hnoex

theorem sumcall_module_fnspec (k₀ : Nat)
    (hc : sumcallCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hf : fn ∈ sumcallModule.fns) :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (sumcallCompiled.bound fn.name) 0 := by
  have hmem := hf
  simp only [sumcallModule, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs, hnoex⟩ :
      x64LegalTarget.legalSig fn.as = fn.as ∧ x64LegalTarget.legalSig fn.rs = fn.rs ∧
        (∀ args m Q X X', litmusEnv fn.name fn.as fn.rs args m Q X →
          litmusEnv fn.name fn.as fn.rs args m Q X') := by
    rcases hmem with rfl | rfl <;> exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
  exact noExit_module_fnspec sumcallCompiled sumcallModule_acyclic
    (fun g hg => by simp [sumcallModule] at hg; rcases hg with rfl | rfl <;> simp [allFns])
    k₀ hc hu hf has hrs hnoex

theorem twice_module_fnspec (k₀ : Nat)
    (hc : twiceCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : x64Target.Defined hh "fail") {fn : Fn} (hf : fn ∈ twiceModule.fns) :
    x64Target.Defined hh fn.name ∧
      x64Target.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (twiceCompiled.bound fn.name) 0 := by
  have hsub : ∀ g ∈ twiceModule.fns, g ∈ allFns := fun g hg => by
    simp [twiceModule] at hg; rcases hg with rfl | rfl <;> simp [allFns]
  obtain ⟨hdef, hspec⟩ := twiceCompiled.fnSpec twiceModule rfl hh litmusEnv k₀ hc hu
    twiceModule_acyclic
    (fun g hg => litmus_allFns_wf g (hsub g hg))
    (fun g hg => litmus_allFns_supports g (hsub g hg))
    (fun g hg => litmusEnv_sound g (hsub g hg))
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun g hg => by simp at hg; subst hg; exact hfail) hf
  have hmem := hf
  simp only [twiceModule, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs⟩ :
      x64LegalTarget.legalSig fn.as = fn.as ∧ x64LegalTarget.legalSig fn.rs = fn.rs := by
    rcases hmem with rfl | rfl <;> exact ⟨rfl, rfl⟩
  have hfn' := fnSpec_of_legalEnv_legalSig_eq has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hspec
  refine ⟨hdef, fun args m Q X hs => hfn' args m Q X ?_⟩
  rcases hmem with rfl | rfl
  · exact ⟨hs.1, fun hna => legal_xpost_i64 (lt := x64LegalTarget) rfl (hs.2 hna)⟩
  · exact ⟨hs.1, fun hna => legal_xpost_i64 (lt := x64LegalTarget) rfl (hs.2.1 hna),
      fun ha hnb => legal_xpost_i64 (lt := x64LegalTarget) rfl (hs.2.2 ha hnb)⟩

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
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))
          (tracerCompiled.bound "tracer") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hspec : tracerContract (a, b, p, ()) m
      (fun r m' => r = (a + b, ()) ∧ cell64 p (a + b) m') (fun _ _ _ _ => False) :=
    ⟨v0, emp, by rw [sep_emp]; exact hm, fun m' hm' => ⟨rfl, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns (tracer_fnspec k₀ hc hu).2 hspec s ra R hargs hsp hmEq)
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
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (a, b, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using ha⟩ (.cons ⟨by decide, by simpa using hb⟩ .nil)⟩
  have hfn : x64Target.FnSpec hh "callinc" callincContract (callincCompiled.bound "callinc") 0 :=
    (callinc_module_fnspec k₀ hc hu (fn := callinc) (by simp [callincModule])).2
  have hspec : callincContract (a, b, ()) ∅ (fun r m' => r = (a + 1 + b, ()) ∧ emp m')
      (fun _ _ _ _ => False) := ⟨rfl, rfl⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns_emp hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (a + 1 + b) st.data hrets, hcs, hsp', hm'⟩

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
  have hspec : twiceContract (a, b, ()) ∅
      (fun r m' => Truthy a ∧ Truthy b ∧ r = (a + b, ()) ∧ m' = ∅)
      (fun sym cs xs m' => ∃ h : cs = [i64], sym = "fail" ∧ m' = ∅ ∧
        ((¬Truthy a ∧ xs = h ▸ (a, ())) ∨ (Truthy a ∧ ¬Truthy b ∧ xs = h ▸ (b, ())))) :=
    ⟨fun ha hb => ⟨ha, hb, rfl, rfl⟩,
     fun hna => ⟨rfl, rfl, rfl, Or.inl ⟨hna, rfl⟩⟩,
     fun ha hnb => ⟨rfl, rfl, rfl, Or.inr ⟨ha, hnb, rfl⟩⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_call_emp hfn hspec s ra R hargs hsp hmem')
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
      ⟨s, Labels.label "spill10"⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (a, b, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using ha⟩ (.cons ⟨by decide, by simpa using hb⟩ .nil)⟩
  have hspec : spill10Contract (a, b, ()) ∅ (fun r m' => r = (spill10Val a b, ()) ∧ emp m')
      (fun _ _ _ _ => False) := ⟨rfl, rfl⟩
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns_emp (spill10_fnspec k₀ hc hu).2 hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (spill10Val a b) st.data hrets, hcs, hsp', hm'⟩

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
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (n, b, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ (.cons ⟨by decide, by simpa using hrsi⟩ .nil)⟩
  have hfn : x64Target.FnSpec hh "sumcall" sumcallContract (sumcallCompiled.bound "sumcall") 0 :=
    (sumcall_module_fnspec k₀ hc hu (fn := sumcall) (by simp [sumcallModule])).2
  have hspec : sumcallContract (n, b, ()) ∅ (fun r m' => r = (tri n.toNat + n + b, ()) ∧ emp m')
      (fun _ _ _ _ => False) := ⟨hn, rfl, rfl⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns_emp hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', _, hrets, rfl, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (tri n.toNat + n + b) st.data hrets, hcs, hsp', hm'⟩

end Generic

/-! ## 4. Concrete SysV x64 Execution Witnesses -/

def zeros8 : List UInt8 := Int.toBytes 8 (0#64).toInt

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
  have hspec : tracerContract (40#64, 2#64, 0x1000#64, ()) (zeros8.At 0x1000#64)
      (fun r m' => r = (42#64, ()) ∧ cell64 0x1000#64 42#64 m') (fun _ _ _ _ => False) :=
    ⟨0#64, emp, by rw [sep_emp]; rfl, fun _ hm' => ⟨rfl, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _
    (fun st ⟨hpc, hrax, hm⟩ => ⟨hpc, hrax, by
      simpa only [Target.Exit, x64Target, x64FrameSpec, x64Frame, x64Init] using hm⟩)
    (x64Init.run_ret1_sep_i64 tracerCompiled
      (tracer_fnspec 0 tracerCompiled.code_infix_host tracerCompiled.labelsUnique).2
      zeros8 (40#64, 2#64, 0x1000#64, ()) 42#64 (cell64 0x1000#64 42#64) (by decide) rfl hspec
      fun _ _ h => h)

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
    [] (3#64, ()) 6#64 (by decide) rfl
    (Q := fun r _ => r = (6#64, ())) ⟨by decide, rfl⟩ fun _ _ h => h

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
  exact x64Init.run_ret1_i64 callincCompiled hfn [] (40#64, 1#64, ()) 42#64
    (by decide) rfl (Q := fun r _ => r = (42#64, ())) rfl fun _ _ h => h

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
      fun h20 => absurd (by simp [Truthy] : Truthy 20#64) h20,
      fun _ _ => ⟨rfl, rfl, rfl⟩⟩ ?_
  rintro st (⟨_, _, _, hq, _⟩ | ⟨_, _, _, _, ⟨rfl, rfl, rfl⟩, hpc, has⟩)
  · exact hq.elim
  · exact ⟨hpc, x64Init.argsIn_singleton 0#64 st.data has⟩

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
  exact x64Init.run_ret1_i64 sumcallCompiled hfn [] (3#64, 10#64, ()) 19#64
    (by decide) rfl (Q := fun r _ => r = (19#64, ())) ⟨by decide, rfl⟩ fun _ _ h => h

end LeanQbe.T.Amd64.Litmus
