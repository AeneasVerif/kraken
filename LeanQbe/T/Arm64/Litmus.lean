module

public import LeanQbe.T.Arm64.BenchAbi
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.LitmusProgs

/-!
# Scalar Litmus Suite on AArch64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.Litmus

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Litmus LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Arm64 Kraken

splice_module_hints tracerHints  (armTarget.toIsa) armLegalTarget tracerModule.fns
splice_module_hints ifelseHints  (armTarget.toIsa) armLegalTarget ifelseModule.fns
splice_module_hints sumtoHints   (armTarget.toIsa) armLegalTarget sumtoModule.fns
splice_module_hints evenoddHints (armTarget.toIsa) armLegalTarget evenoddModule.fns
splice_module_hints nestedHints  (armTarget.toIsa) armLegalTarget nestedModule.fns
splice_module_hints swapHints    (armTarget.toIsa) armLegalTarget swapModule.fns
splice_module_hints spill10Hints (armTarget.toIsa) armLegalTarget spill10Module.fns
splice_module_hints callincHints (armTarget.toIsa) armLegalTarget callincModule.fns
splice_module_hints twiceHints   (armTarget.toIsa) armLegalTarget twiceModule.fns
splice_module_hints sumcallHints (armTarget.toIsa) armLegalTarget sumcallModule.fns

/-! ## 1. Compiled Kernel Certificates -/

theorem tracer_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 tracerModule.fns tracerHints 2048 =
      true := by t_kernel_rfl
theorem ifelse_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 ifelseModule.fns ifelseHints 2048 =
      true := by t_kernel_rfl
theorem sumto_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 sumtoModule.fns sumtoHints 2048 =
      true := by t_kernel_rfl
theorem evenodd_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 evenoddModule.fns evenoddHints 2048 =
      true := by t_kernel_rfl
theorem nested_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 nestedModule.fns nestedHints 2048 =
      true := by t_kernel_rfl
theorem swap_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 swapModule.fns swapHints 2048 =
      true := by t_kernel_rfl
theorem spill10_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 spill10Module.fns spill10Hints 2048 =
      true := by t_kernel_rfl
theorem callinc_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 callincModule.fns callincHints 2048 =
      true := by t_kernel_rfl
theorem twice_check :
    checkCompile armTarget armLayout armLegalTarget [] ["fail"] 0 twiceModule.fns twiceHints 2048 =
      true := by t_kernel_rfl
theorem sumcall_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 sumcallModule.fns sumcallHints 2048 =
      true := by t_kernel_rfl

@[expose] def tracerCompiled :
    Compiled armTarget armLegalTarget [] [] 0 tracerModule.fns tracerHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 tracerModule.fns tracerHints 2048 tracer_check
@[expose] def ifelseCompiled :
    Compiled armTarget armLegalTarget [] [] 0 ifelseModule.fns ifelseHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 ifelseModule.fns ifelseHints 2048 ifelse_check
@[expose] def sumtoCompiled :
    Compiled armTarget armLegalTarget [] [] 0 sumtoModule.fns sumtoHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 sumtoModule.fns sumtoHints 2048 sumto_check
@[expose] def evenoddCompiled :
    Compiled armTarget armLegalTarget [] [] 0 evenoddModule.fns evenoddHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 evenoddModule.fns evenoddHints 2048 evenodd_check
@[expose] def nestedCompiled :
    Compiled armTarget armLegalTarget [] [] 0 nestedModule.fns nestedHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 nestedModule.fns nestedHints 2048 nested_check
@[expose] def swapCompiled :
    Compiled armTarget armLegalTarget [] [] 0 swapModule.fns swapHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 swapModule.fns swapHints 2048 swap_check
@[expose] def spill10Compiled :
    Compiled armTarget armLegalTarget [] [] 0 spill10Module.fns spill10Hints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 spill10Module.fns spill10Hints 2048 spill10_check
@[expose] def callincCompiled :
    Compiled armTarget armLegalTarget [] [] 0 callincModule.fns callincHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 callincModule.fns callincHints 2048 callinc_check
@[expose] def twiceCompiled :
    Compiled armTarget armLegalTarget [] ["fail"] 0 twiceModule.fns twiceHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] ["fail"] 0 twiceModule.fns twiceHints 2048 twice_check
@[expose] def sumcallCompiled :
    Compiled armTarget armLegalTarget [] [] 0 sumcallModule.fns sumcallHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 sumcallModule.fns sumcallHints 2048 sumcall_check

/-! ## 2. Module Linking Helpers (`allFns` `Wf` & `supportsSource`) -/

private theorem allFns_supportsSource_all :
    allFns.all (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

private theorem litmus_single_arm64 {hh : Host} {f : Fn} {hints : List armTarget.toIsa.Hints}
    (M : Compiled armTarget armLegalTarget [] [] 0 [f] hints 2048)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hf : f ∈ allFns) (k₀ : Nat) (hc : M.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (has : armLegalTarget.legalSig f.as = f.as)
    (hrs : armLegalTarget.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X',
      litmusEnv f.name f.as f.rs args m Q X → litmusEnv f.name f.as f.rs args m Q X') :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (litmusEnv f.name f.as f.rs) (M.bound f.name) 0 :=
  litmus_single_fnspec_gen M hh (supportsAll_to_forall allFns_supportsSource_all)
    hacyc hf k₀ hc hu has hrs hnoex

/-! ## 3. Generic `FnSpec` and Closed Kraken AArch64 Theorems -/

section Generic
variable [hh : Host]

theorem tracer_fnspec (k₀ : Nat) (hc : tracerCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    armTarget.Defined hh "tracer" ∧
      armTarget.FnSpec hh "tracer" tracerContract (tracerCompiled.bound "tracer") 0 :=
  litmus_single_arm64 tracerCompiled tracerModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem ifelse_fnspec (k₀ : Nat) (hc : ifelseCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    armTarget.Defined hh "ifelse" ∧
      armTarget.FnSpec hh "ifelse" ifelseContract (ifelseCompiled.bound "ifelse") 0 :=
  litmus_single_arm64 ifelseCompiled ifelseModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem sumto_fnspec (k₀ : Nat) (hc : sumtoCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    armTarget.Defined hh "sumto" ∧
      armTarget.FnSpec hh "sumto" sumtoContract (sumtoCompiled.bound "sumto") 0 :=
  litmus_single_arm64 sumtoCompiled sumtoModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem evenodd_fnspec (k₀ : Nat) (hc : evenoddCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    armTarget.Defined hh "evenodd" ∧
      armTarget.FnSpec hh "evenodd" evenoddContract (evenoddCompiled.bound "evenodd") 0 :=
  litmus_single_arm64 evenoddCompiled evenoddModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem nested_fnspec (k₀ : Nat) (hc : nestedCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    armTarget.Defined hh "nested" ∧
      armTarget.FnSpec hh "nested" nestedContract (nestedCompiled.bound "nested") 0 :=
  litmus_single_arm64 nestedCompiled nestedModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem swap_fnspec (k₀ : Nat) (hc : swapCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    armTarget.Defined hh "swap" ∧
      armTarget.FnSpec hh "swap" swapContract (swapCompiled.bound "swap") 0 :=
  litmus_single_arm64 swapCompiled swapModule_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem spill10_fnspec (k₀ : Nat) (hc : spill10Compiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    armTarget.Defined hh "spill10" ∧
      armTarget.FnSpec hh "spill10" spill10Contract (spill10Compiled.bound "spill10") 0 :=
  litmus_single_arm64 spill10Compiled spill10Module_acyclic (by simp [allFns]) k₀ hc hu rfl rfl
    (fun _ _ _ _ _ h => h)

theorem callinc_module_fnspec (k₀ : Nat)
    (hc : callincCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hf : fn ∈ callincModule.fns) :
    armTarget.Defined hh fn.name ∧
      armTarget.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (callincCompiled.bound fn.name) 0 :=
  litmus_twoFn_fnspec_gen callincModule rfl callincModule_acyclic ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (fun g hg => by simp [callincModule] at hg; rcases hg with rfl | rfl <;> simp [allFns])
    (fun g hg => by
      simp [callincModule] at hg; rcases hg with rfl | rfl <;> exact fun _ _ _ _ _ h => h)
    callincCompiled hh rfl (supportsAll_to_forall allFns_supportsSource_all) k₀ hc hu hf

theorem sumcall_module_fnspec (k₀ : Nat)
    (hc : sumcallCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hf : fn ∈ sumcallModule.fns) :
    armTarget.Defined hh fn.name ∧
      armTarget.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (sumcallCompiled.bound fn.name) 0 :=
  litmus_twoFn_fnspec_gen sumcallModule rfl sumcallModule_acyclic ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (fun g hg => by simp [sumcallModule] at hg; rcases hg with rfl | rfl <;> simp [allFns])
    (fun g hg => by
      simp [sumcallModule] at hg; rcases hg with rfl | rfl <;> exact fun _ _ _ _ _ h => h)
    sumcallCompiled hh rfl (supportsAll_to_forall allFns_supportsSource_all) k₀ hc hu hf

theorem twice_module_fnspec (k₀ : Nat)
    (hc : twiceCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : armTarget.Defined hh "fail") {fn : Fn} (hf : fn ∈ twiceModule.fns) :
    armTarget.Defined hh fn.name ∧
      armTarget.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs)
        (twiceCompiled.bound fn.name) 0 :=
  twice_module_fnspec_gen twiceCompiled hh rfl
    (supportsAll_to_forall allFns_supportsSource_all) k₀ hc hu hfail hf

/-- End-to-end correctness of `tracer` on Kraken AArch64 (`cell64 p v0 ↦ cell64 p (a + b)`). -/
theorem tracer_arm64_correct (k₀ : Nat) (hc : tracerCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b p v0 : BitVec 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hpp : (s.regs.getXReg .X2).toBitVec = p)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v0 ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))
        (tracerCompiled.bound "tracer") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ cell64 p (a + b) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))
            (tracerCompiled.bound "tracer") ⋆ R))
      ⟨s, Labels.label "tracer"⟩ :=
  litmus_tracer_abi_correct arm64BenchAbi hh tracerCompiled
    (supportsAll_to_forall allFns_supportsSource_all) k₀ hc hu a b p v0 s ra R
    ha hb hpp ⟨hra, hsp⟩ hmem

/-- End-to-end correctness of `sumto` on Kraken AArch64. -/
theorem sumto_arm64_correct (k₀ : Nat) (hc : sumtoCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (n : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (sumtoCompiled.bound "sumto"))
        (sumtoCompiled.bound "sumto") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = tri n.toNat ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (sumtoCompiled.bound "sumto"))
            (sumtoCompiled.bound "sumto") ⋆ R))
      ⟨s, Labels.label "sumto"⟩ :=
  litmus_ret1_abi_correct arm64BenchAbi hh (sumto_fnspec k₀ hc hu).2 ⟨hn, rfl, rfl⟩
    s ra R hx0 ⟨hra, hsp⟩ hmem

/-- End-to-end correctness of `callinc` on Kraken AArch64. -/
theorem callinc_arm64_correct (k₀ : Nat)
    (hc : callincCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (callincCompiled.bound "callinc"))
        (callincCompiled.bound "callinc") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + 1 + b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (callincCompiled.bound "callinc"))
            (callincCompiled.bound "callinc") ⋆ R))
      ⟨s, Labels.label "callinc"⟩ :=
  litmus_ret2_abi_correct arm64BenchAbi hh
    (sym := "callinc") (b := callincCompiled.bound "callinc") (spec := callincContract)
    (callinc_module_fnspec k₀ hc hu (fn := callinc) (by simp [callincModule])).2
    ⟨rfl, rfl⟩ s ra R ha hb ⟨hra, hsp⟩ hmem

/-- End-to-end correctness of `twice` (including abnormal exit `"fail"`) on Kraken AArch64. -/
theorem twice_arm64_correct (k₀ : Nat)
    (hc : twiceCompiled.code.IsInfixAt Host.prog k₀)
    (hfail : armTarget.Defined hh "fail") (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (twiceCompiled.bound "twice"))
        (twiceCompiled.bound "twice") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (Truthy a ∧ Truthy b ∧ st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + b ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP) ∨
        ((¬Truthy a ∧ st.pc = Labels.label "fail" ∧ (st.data.regs.getXReg .X0).toBitVec = a ∧
          st.data.regs.SP.toNat % 16 = 0) ∨
         (Truthy a ∧ ¬Truthy b ∧ st.pc = Labels.label "fail" ∧
          (st.data.regs.getXReg .X0).toBitVec = b ∧ st.data.regs.SP.toNat % 16 = 0)))
      ⟨s, Labels.label "twice"⟩ :=
  litmus_twice_abi_correct arm64BenchAbi hh twiceCompiled
    (supportsAll_to_forall allFns_supportsSource_all) k₀ hc hfail hu a b s ra R
    ha hb ⟨hra, hsp⟩ hmem

/-- End-to-end correctness of `spill10` on Kraken AArch64. -/
theorem spill10_arm64_correct (k₀ : Nat) (hc : spill10Compiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b : BitVec 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (spill10Compiled.bound "spill10"))
        (spill10Compiled.bound "spill10") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = spill10Val a b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (spill10Compiled.bound "spill10"))
            (spill10Compiled.bound "spill10") ⋆ R))
      ⟨s, Labels.label "spill10"⟩ :=
  litmus_ret2_abi_correct arm64BenchAbi hh (spill10_fnspec k₀ hc hu).2
    ⟨rfl, rfl⟩ s ra R ha hb ⟨hra, hsp⟩ hmem

/-- End-to-end correctness of `sumcall` (call in loop body) on Kraken AArch64. -/
theorem sumcall_arm64_correct (k₀ : Nat)
    (hc : sumcallCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (n b : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n) (hx1 : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (sumcallCompiled.bound "sumcall"))
        (sumcallCompiled.bound "sumcall") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = tri n.toNat + n + b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (sumcallCompiled.bound "sumcall"))
            (sumcallCompiled.bound "sumcall") ⋆ R))
      ⟨s, Labels.label "sumcall"⟩ :=
  litmus_ret2_abi_correct arm64BenchAbi hh
    (sym := "sumcall") (b := sumcallCompiled.bound "sumcall") (spec := sumcallContract)
    (sumcall_module_fnspec k₀ hc hu (fn := sumcall) (by simp [sumcallModule])).2
    ⟨hn, rfl, rfl⟩ s ra R hx0 hx1 ⟨hra, hsp⟩ hmem

end Generic

/-! ## 4. Concrete AArch64 Execution Witnesses -/

abbrev zeros8 : List UInt8 := Examples.BenchmarkCertKit.zeros8

abbrev tracerHost : Host := tracerCompiled.host
@[expose] def tracerState0 : MachineData :=
  armInit.initState (as := [i64, i64, i64]) (tracerCompiled.bound "tracer") zeros8
    (40#64, 2#64, 0x1000#64, ())

attribute [local instance] tracerHost in
theorem tracer_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 42#64 ∧
        (st.data.dmem =⋆ cell64 0x1000#64 42#64 ⋆
          region (0x1000#64 - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))
            (tracerCompiled.bound "tracer") ⋆ emp))
      ⟨tracerState0, Labels.label "tracer"⟩ :=
  abi_run_ret1_sep_i64 arm64BenchAbi tracerCompiled
    (tracer_fnspec 0 tracerCompiled.code_infix_host tracerCompiled.labelsUnique).2
    zeros8 (40#64, 2#64, 0x1000#64, ()) 42#64 (cell64 0x1000#64 42#64) (by decide)
    (arm64BenchAbi.assignArgs_i64 3 (by decide))
    (tracer_spec_ok 40#64 2#64 0x1000#64 0#64 rfl) fun _ _ h => h

abbrev sumtoHost : Host := sumtoCompiled.host
@[expose] def sumtoState : MachineData :=
  armInit.initState (as := [i64]) (sumtoCompiled.bound "sumto") [] (3#64, ())

attribute [local instance] sumtoHost in
theorem sumto_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 6#64)
      ⟨sumtoState, Labels.label "sumto"⟩ :=
  abi_run_ret1_i64 arm64BenchAbi sumtoCompiled
    (sumto_fnspec 0 sumtoCompiled.code_infix_host sumtoCompiled.labelsUnique).2
    [] (3#64, ()) 6#64 (by decide) (arm64BenchAbi.assignArgs_i64 1 (by decide))
    (Q := fun r _ => r = (6#64, ())) ⟨by decide, rfl⟩ fun _ _ h => h

abbrev callincHost : Host := callincCompiled.host
@[expose] def callincState : MachineData :=
  armInit.initState (as := [i64, i64]) (callincCompiled.bound "callinc") [] (40#64, 1#64, ())

attribute [local instance] callincHost in
theorem callinc_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 42#64)
      ⟨callincState, Labels.label "callinc"⟩ :=
  abi_run_ret1_i64 arm64BenchAbi callincCompiled
    (callinc_module_fnspec 0 callincCompiled.code_infix_host callincCompiled.labelsUnique
      (fn := callinc) (by simp [callincModule])).2
    [] (40#64, 1#64, ()) 42#64 (by decide) (arm64BenchAbi.assignArgs_i64 2 (by decide))
    (Q := fun r _ => r = (42#64, ())) rfl fun _ _ h => h

abbrev twiceHost : Host := twiceCompiled.host
@[expose] def twiceState (a b : BitVec 64) : MachineData :=
  armInit.initState (as := [i64, i64]) (twiceCompiled.bound "twice") [] (a, b, ())

attribute [local instance] twiceHost in
theorem twice_arm64_nonvacuous_exit :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "fail" ∧ (st.data.regs.getXReg .X0).toBitVec = 0#64)
      ⟨twiceState 20#64 0#64, Labels.label "twice"⟩ :=
  litmus_twice_exit_abi_nonvacuous arm64BenchAbi twiceCompiled
    (supportsAll_to_forall allFns_supportsSource_all)

abbrev spill10Host : Host := spill10Compiled.host
@[expose] def spill10State : MachineData :=
  armInit.initState (as := [i64, i64]) (spill10Compiled.bound "spill10") [] (10#64, 7#64, ())

attribute [local instance] spill10Host in
theorem spill10_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = spill10Val 10#64 7#64)
      ⟨spill10State, Labels.label "spill10"⟩ :=
  abi_run_ret1_i64 arm64BenchAbi spill10Compiled
    (spill10_fnspec 0 spill10Compiled.code_infix_host spill10Compiled.labelsUnique).2
    [] (10#64, 7#64, ()) (spill10Val 10#64 7#64) (by decide)
    (arm64BenchAbi.assignArgs_i64 2 (by decide))
    (Q := fun r _ => r = (spill10Val 10#64 7#64, ())) rfl fun _ _ h => h

abbrev sumcallHost : Host := sumcallCompiled.host
@[expose] def sumcallState : MachineData :=
  armInit.initState (as := [i64, i64]) (sumcallCompiled.bound "sumcall") [] (3#64, 10#64, ())

attribute [local instance] sumcallHost in
theorem sumcall_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 19#64)
      ⟨sumcallState, Labels.label "sumcall"⟩ :=
  abi_run_ret1_i64 arm64BenchAbi sumcallCompiled
    (sumcall_module_fnspec 0 sumcallCompiled.code_infix_host sumcallCompiled.labelsUnique
      (fn := sumcall) (by simp [sumcallModule])).2
    [] (3#64, 10#64, ()) 19#64 (by decide) (arm64BenchAbi.assignArgs_i64 2 (by decide))
    (Q := fun r _ => r = (19#64, ())) ⟨by decide, rfl⟩ fun _ _ h => h

end LeanQbe.T.Arm64.Litmus
