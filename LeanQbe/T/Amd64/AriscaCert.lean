/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.BenchAbi
public import LeanQbe.T.Examples.Arisca.Build.CertCommon
public import LeanQbe.T.Amd64.AriscaCertS0
public import LeanQbe.T.Amd64.AriscaCertS1
public import LeanQbe.T.Amd64.AriscaCertS2
public import LeanQbe.T.Amd64.AriscaCertS3
public import LeanQbe.T.Amd64.AriscaCertS4
public import LeanQbe.T.FlatLemmas

/-!
# Whole-Module SysV x86-64 `LinkedCert` for ARiSCA (`Amd64.AriscaCert`)

Assembles the five verified x64 compilation slices (`AriscaCertS0`..`S4`) via balanced
`LinkedCert.append` into `ariscaX64Cert` over all `44` functions of `ariscaModule` (`0` externs,
`0` exits, max stack bound `656` bytes), and exports:
* standalone compiler-cert theorems (`ariscaX64_compileModule`, `ariscaX64_checkLit`,
  `ariscaX64_checkCompile`, `ariscaX64_legalSigAll`, `ariscaX64_bounds_len`,
  `ariscaX64_bounds_le`, `ariscaX64_entry_bound`);
* `ModuleOk`-parameterized whole-module and entry (`arisca_check_bytes`) SysV x86-64 `FnSpec` and
  Kraken-x64 `Eventually` theorems ready for 5-line composition once `M1-C` `ModuleOk` lands.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.AriscaCert

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.BenchmarkCertKit LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Examples.Arisca.Src.Module
open LeanQbe.T.Examples.Arisca.Build
open LeanQbe.T.Examples.Arisca.Build.CertCommon

/-! ## 1. Whole-Module `LinkedCert` & `Compiled` Bundle -/

/-- Full 44-function kernel-checked SysV x86-64 compilation certificate for `ariscaModule`. -/
@[expose] noncomputable def ariscaX64Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      ariscaModule [] [] 0 2048 :=
  mkAriscaCertTree rfl rfl rfl rfl rfl
    ariscaX64CertS0 ariscaX64CertS1 ariscaX64CertS2 ariscaX64CertS3 ariscaX64CertS4
    (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)

/-- Concatenated SysV x86-64 register-allocation hints across all chunks of `ariscaX64Cert`. -/
@[expose] noncomputable def ariscaX64Hints : List x64Target.toIsa.Hints :=
  chunksHints ariscaX64Cert.chunks

/-- Literal-backed `Compiled` bundle for `ariscaFns` on SysV x86-64. -/
@[expose] noncomputable def ariscaX64Compiled :
    Compiled x64Target x64LegalTarget [] [] 0 ariscaFns ariscaX64Hints 2048 :=
  linkedCert_to_compiled ariscaX64Cert

/-! ## 2. Standalone Compiler-Cert, Legalization, & Stack-Bound Theorems -/

theorem ariscaX64_compileModule :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0
      ariscaFns ariscaX64Hints = .ok (ariscaX64Cert.code, ariscaX64Cert.bounds) :=
  arisca_compileModule_abi x64BenchAbi ariscaX64Cert

theorem ariscaX64_checkLit :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      ariscaX64Cert.code ariscaX64Cert.bounds (ariscaFns.map Fn.name) [] 2048 = true :=
  arisca_checkLit_abi x64BenchAbi ariscaX64Cert

theorem ariscaX64_checkCompile :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 ariscaFns ariscaX64Hints 2048 =
      true :=
  arisca_checkCompile_abi x64BenchAbi ariscaX64Cert

theorem ariscaX64_supportsSource :
    ∀ f ∈ ariscaModule.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  ariscaX64Cert.supportsAll

private theorem ariscaX64_legalSig_check :
    checkLegalSigAll x64LegalTarget ariscaModule.fns = true := by
  t_kernel_rfl

/-- Every function signature in `ariscaModule.fns` (`44` fns) is fixed by
`x64LegalTarget.legalSig`. -/
theorem ariscaX64_legalSigAll : LegalSigAll x64LegalTarget ariscaModule.fns :=
  legalSigAll_of_check ariscaX64_legalSig_check

/-- `ariscaX64Cert.bounds` covers all `44` functions of `ariscaModule`. -/
theorem ariscaX64_bounds_len : ariscaX64Cert.bounds.length = 44 :=
  ariscaX64Cert.bounds_length.trans ariscaModule_fns_len

/-- Every stack bound in `ariscaX64Cert.bounds` is at most `656` bytes. -/
theorem ariscaX64_bounds_le :
    ariscaX64Cert.bounds.all (fun p => Nat.ble p.2 656) = true := by
  t_kernel_rfl

/-- Exact SysV x86-64 stack bound (`656` bytes) for top-level `"arisca_check_bytes"`. -/
theorem ariscaX64_entry_bound :
    ariscaX64Cert.bound "arisca_check_bytes" = 656 :=
  arisca_entry_bound_of_getElem x64BenchAbi ariscaX64Cert (by t_kernel_rfl)

/-- Every function's stack bound in `ariscaX64Cert` is at most `2048` bytes. -/
theorem ariscaX64_bound_le_max (nm : Sym) : ariscaX64Cert.bound nm ≤ 2048 :=
  ariscaX64Cert.bound_le_max nm

/-! ## 3. `ModuleOk`-Parameterized SysV x86-64 `FnSpec` & `Eventually` Theorems -/

section Generic
variable [hh : Host]

/-- Whole-module `x64Target.Defined` + `x64Target.FnSpec` parameterized over any
`ModuleOk Γ ariscaModule`. -/
theorem ariscaX64_module_fnSpec_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : ariscaX64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ ariscaModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (Γ f.name f.as f.rs) (ariscaX64Cert.bound f.name) 0 :=
  arisca_module_fnSpec_of_moduleOk_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll
    hh Γ hM hnoex k₀ hc hu hf

/-- Entry-point `Defined` + `FnSpec` for `"arisca_check_bytes"` on any legal x64 host embedding
`ariscaX64Cert.code`, parameterized over any `ModuleOk Γ ariscaModule`. -/
theorem ariscaX64_entry_fnSpec_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : ariscaX64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    x64Target.Defined hh "arisca_check_bytes" ∧
      x64Target.FnSpec hh "arisca_check_bytes"
        (Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64])
        (ariscaX64Cert.bound "arisca_check_bytes") 0 :=
  arisca_entry_fnSpec_of_moduleOk_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll
    hh Γ hM hnoex k₀ hc hu

/-- Closed SysV x86-64 Kraken `Eventually` lift for `"arisca_check_bytes"` (`rdi..r9 → rax`),
parameterized over any `ModuleOk Γ ariscaModule`. -/
theorem ariscaX64_entry_eventually_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : ariscaX64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    {m : Mem 64} {Q : Post [i64]}
    (hspec : Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64]
      (aig_ptr, aig_len, art_ptr, art_len, work_ptr, work_len, ()) m Q
      (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = aig_ptr)
    (hrsi : s.regs.get64 .rsi = aig_len)
    (hrdx : s.regs.get64 .rdx = art_ptr)
    (hrcx : s.regs.get64 .rcx = art_len)
    (hr8 : s.regs.get64 .r8 = work_ptr)
    (hr9 : s.regs.get64 .r9 = work_len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (ariscaX64Cert.bound "arisca_check_bytes"))
          (ariscaX64Cert.bound "arisca_check_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ m', Q (st.data.regs.get64 .rax, ()) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp -
                BitVec.ofNat 64 (ariscaX64Cert.bound "arisca_check_bytes"))
              (ariscaX64Cert.bound "arisca_check_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "arisca_check_bytes"⟩ :=
  arisca_entry_eventually_of_moduleOk_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll
    hh Γ hM hnoex k₀ hc hu aig_ptr aig_len art_ptr art_len work_ptr work_len
    hspec s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

end Generic

/-- Self-contained `Defined` + `FnSpec` for every function on `ariscaX64Cert.host`. -/
theorem ariscaX64_host_module_fnSpec_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g) {f : Fn} (hf : f ∈ ariscaModule.fns) :
    x64Target.Defined ariscaX64Cert.host f.name ∧
      x64Target.FnSpec ariscaX64Cert.host f.name (Γ f.name f.as f.rs)
        (ariscaX64Cert.bound f.name) 0 :=
  arisca_host_module_fnSpec_of_moduleOk_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll
    Γ hM hnoex hf

/-- Self-contained `Defined` + `FnSpec` for `"arisca_check_bytes"` on `ariscaX64Cert.host`. -/
theorem ariscaX64_host_entry_fnSpec_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g) :
    x64Target.Defined ariscaX64Cert.host "arisca_check_bytes" ∧
      x64Target.FnSpec ariscaX64Cert.host "arisca_check_bytes"
        (Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64])
        (ariscaX64Cert.bound "arisca_check_bytes") 0 :=
  ariscaX64_host_module_fnSpec_of_moduleOk Γ hM hnoex ariscaCheckBytesFn_mem

/-- Concrete `x64Init` execution runner on `ariscaX64Cert.host`, ready for M1-C non-vacuity. -/
theorem ariscaX64_entry_run_ret1_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (bsMem : List UInt8) (args : Tup Val [i64, i64, i64, i64, i64, i64])
    (v : BitVec 64) (hlen : bsMem.length ≤ 8192)
    {Q : Post [i64]}
    (hspec : Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64]
      args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) :
    Eventually (x64Target.mach.step ariscaX64Cert.host)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = v)
      ⟨x64Init.initState (ariscaX64Cert.bound "arisca_check_bytes") bsMem args,
        x64Target.mach.labelAddr ariscaX64Cert.host "arisca_check_bytes"⟩ :=
  arisca_entry_run_ret1_of_moduleOk_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll
    Γ hM hnoex bsMem args v hlen hspec hQ

end LeanQbe.T.Amd64.AriscaCert
