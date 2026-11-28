/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Arm64.BenchAbi
public import LeanQbe.T.Examples.Arisca.Build.CertCommon
public import LeanQbe.T.Arm64.AriscaCertS0
public import LeanQbe.T.Arm64.AriscaCertS1
public import LeanQbe.T.Arm64.AriscaCertS2
public import LeanQbe.T.Arm64.AriscaCertS3
public import LeanQbe.T.Arm64.AriscaCertS4
public import LeanQbe.T.FlatLemmas

/-!
# Whole-Module AAPCS64 Arm64 `LinkedCert` for ARiSCA (`Arm64.AriscaCert`)

Assembles the five verified AArch64 compilation slices (`AriscaCertS0`..`S4`) via balanced
`LinkedCert.append` into `ariscaArm64Cert` over all `44` functions of `ariscaModule` (`0` externs,
`0` exits, max stack bound `624` bytes), and exports:
* standalone compiler-cert theorems (`ariscaArm64_compileModule`, `ariscaArm64_checkLit`,
  `ariscaArm64_checkCompile`, `ariscaArm64_legalSigAll`, `ariscaArm64_bounds_len`,
  `ariscaArm64_bounds_le`, `ariscaArm64_entry_bound`);
* `ModuleOk`-parameterized whole-module and entry (`arisca_check_bytes`) AAPCS64 Arm64 `FnSpec`
  and Kraken-AArch64 `Eventually` theorems ready for 5-line composition once `M1-C` `ModuleOk`
  lands.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.AriscaCert

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.BenchmarkCertKit LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Examples.Arisca.Src.Module
open LeanQbe.T.Examples.Arisca.Build
open LeanQbe.T.Examples.Arisca.Build.CertCommon

/-! ## 1. Whole-Module `LinkedCert` & `Compiled` Bundle -/

/-- Full 44-function kernel-checked AAPCS64 Arm64 compilation certificate for `ariscaModule`. -/
@[expose] noncomputable def ariscaArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      ariscaModule [] [] 0 2048 :=
  mkAriscaCertTree rfl rfl rfl rfl rfl
    ariscaArm64CertS0 ariscaArm64CertS1 ariscaArm64CertS2 ariscaArm64CertS3 ariscaArm64CertS4
    (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)

/-- Concatenated AAPCS64 register-allocation hints across all chunks of `ariscaArm64Cert`. -/
@[expose] noncomputable def ariscaArm64Hints : List armTarget.toIsa.Hints :=
  chunksHints ariscaArm64Cert.chunks

/-- Literal-backed `Compiled` bundle for `ariscaFns` on AAPCS64 Arm64. -/
@[expose] noncomputable def ariscaArm64Compiled :
    Compiled armTarget armLegalTarget [] [] 0 ariscaFns ariscaArm64Hints 2048 :=
  linkedCert_to_compiled ariscaArm64Cert

/-! ## 2. Standalone Compiler-Cert, Legalization, & Stack-Bound Theorems -/

theorem ariscaArm64_compileModule :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0
      ariscaFns ariscaArm64Hints = .ok (ariscaArm64Cert.code, ariscaArm64Cert.bounds) :=
  arisca_compileModule_abi arm64BenchAbi ariscaArm64Cert

theorem ariscaArm64_checkLit :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      ariscaArm64Cert.code ariscaArm64Cert.bounds (ariscaFns.map Fn.name) [] 2048 = true :=
  arisca_checkLit_abi arm64BenchAbi ariscaArm64Cert

theorem ariscaArm64_checkCompile :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 ariscaFns ariscaArm64Hints 2048 =
      true :=
  arisca_checkCompile_abi arm64BenchAbi ariscaArm64Cert

theorem ariscaArm64_supportsSource :
    ∀ f ∈ ariscaModule.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true :=
  ariscaArm64Cert.supportsAll

private theorem ariscaArm64_legalSig_check :
    checkLegalSigAll armLegalTarget ariscaModule.fns = true := by
  t_kernel_rfl

/-- Every function signature in `ariscaModule.fns` (`44` fns) is fixed by
`armLegalTarget.legalSig`. -/
theorem ariscaArm64_legalSigAll : LegalSigAll armLegalTarget ariscaModule.fns :=
  legalSigAll_of_check ariscaArm64_legalSig_check

/-- `ariscaArm64Cert.bounds` covers all `44` functions of `ariscaModule`. -/
theorem ariscaArm64_bounds_len : ariscaArm64Cert.bounds.length = 44 :=
  ariscaArm64Cert.bounds_length.trans ariscaModule_fns_len

/-- Every stack bound in `ariscaArm64Cert.bounds` is at most `624` bytes. -/
theorem ariscaArm64_bounds_le :
    ariscaArm64Cert.bounds.all (fun p => Nat.ble p.2 624) = true := by
  t_kernel_rfl

/-- Exact AAPCS64 Arm64 stack bound (`624` bytes) for top-level `"arisca_check_bytes"`. -/
theorem ariscaArm64_entry_bound :
    ariscaArm64Cert.bound "arisca_check_bytes" = 624 :=
  arisca_entry_bound_of_getElem arm64BenchAbi ariscaArm64Cert (by t_kernel_rfl)

/-- Every function's stack bound in `ariscaArm64Cert` is at most `2048` bytes. -/
theorem ariscaArm64_bound_le_max (nm : Sym) : ariscaArm64Cert.bound nm ≤ 2048 :=
  ariscaArm64Cert.bound_le_max nm

/-! ## 3. `ModuleOk`-Parameterized AAPCS64 Arm64 `FnSpec` & `Eventually` Theorems -/

section Generic
variable [hh : Host]

/-- Whole-module `armTarget.Defined` + `armTarget.FnSpec` parameterized over any
`ModuleOk Γ ariscaModule`. -/
theorem ariscaArm64_module_fnSpec_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : ariscaArm64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ ariscaModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (ariscaArm64Cert.bound f.name) 0 :=
  arisca_module_fnSpec_of_moduleOk_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll
    hh Γ hM hnoex k₀ hc hu hf

/-- Entry-point `Defined` + `FnSpec` for `"arisca_check_bytes"` on any legal AArch64 host
embedding `ariscaArm64Cert.code`, parameterized over any `ModuleOk Γ ariscaModule`. -/
theorem ariscaArm64_entry_fnSpec_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : ariscaArm64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    armTarget.Defined hh "arisca_check_bytes" ∧
      armTarget.FnSpec hh "arisca_check_bytes"
        (Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64])
        (ariscaArm64Cert.bound "arisca_check_bytes") 0 :=
  arisca_entry_fnSpec_of_moduleOk_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll
    hh Γ hM hnoex k₀ hc hu

/-- Closed AAPCS64 Arm64 Kraken `Eventually` lift for `"arisca_check_bytes"` (`X0..X5 → X0`),
parameterized over any `ModuleOk Γ ariscaModule`. -/
theorem ariscaArm64_entry_eventually_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : ariscaArm64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    {m : Mem 64} {Q : Post [i64]}
    (hspec : Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64]
      (aig_ptr, aig_len, art_ptr, art_len, work_ptr, work_len, ()) m Q
      (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = aig_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = aig_len)
    (hx2 : (s.regs.getXReg .X2).toBitVec = art_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = art_len)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (ariscaArm64Cert.bound "arisca_check_bytes"))
        (ariscaArm64Cert.bound "arisca_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m', Q ((st.data.regs.getXReg .X0).toBitVec, ()) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.SP.toBitVec -
                BitVec.ofNat 64 (ariscaArm64Cert.bound "arisca_check_bytes"))
              (ariscaArm64Cert.bound "arisca_check_bytes") ⋆ R))
      ⟨s, Labels.label "arisca_check_bytes"⟩ :=
  arisca_entry_eventually_of_moduleOk_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll
    hh Γ hM hnoex k₀ hc hu aig_ptr aig_len art_ptr art_len work_ptr work_len
    hspec s ra R hx0 hx1 hx2 hx3 hx4 hx5 ⟨hra, hsp⟩ hmem

end Generic

/-- Self-contained `Defined` + `FnSpec` for every function on `ariscaArm64Cert.host`. -/
theorem ariscaArm64_host_module_fnSpec_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g) {f : Fn} (hf : f ∈ ariscaModule.fns) :
    armTarget.Defined ariscaArm64Cert.host f.name ∧
      armTarget.FnSpec ariscaArm64Cert.host f.name (Γ f.name f.as f.rs)
        (ariscaArm64Cert.bound f.name) 0 :=
  arisca_host_module_fnSpec_of_moduleOk_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll
    Γ hM hnoex hf

/-- Self-contained `Defined` + `FnSpec` for `"arisca_check_bytes"` on `ariscaArm64Cert.host`. -/
theorem ariscaArm64_host_entry_fnSpec_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g) :
    armTarget.Defined ariscaArm64Cert.host "arisca_check_bytes" ∧
      armTarget.FnSpec ariscaArm64Cert.host "arisca_check_bytes"
        (Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64])
        (ariscaArm64Cert.bound "arisca_check_bytes") 0 :=
  ariscaArm64_host_module_fnSpec_of_moduleOk Γ hM hnoex ariscaCheckBytesFn_mem

/-- Concrete `armInit` execution runner on `ariscaArm64Cert.host`, ready for M1-C non-vacuity. -/
theorem ariscaArm64_entry_run_ret1_of_moduleOk (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (bsMem : List UInt8) (args : Tup Val [i64, i64, i64, i64, i64, i64])
    (v : BitVec 64) (hlen : bsMem.length ≤ 8192)
    {Q : Post [i64]}
    (hspec : Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64]
      args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) :
    Eventually (armTarget.mach.step ariscaArm64Cert.host)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = v)
      ⟨armInit.initState (ariscaArm64Cert.bound "arisca_check_bytes") bsMem args,
        armTarget.mach.labelAddr ariscaArm64Cert.host "arisca_check_bytes"⟩ :=
  arisca_entry_run_ret1_of_moduleOk_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll
    Γ hM hnoex bsMem args v hlen hspec hQ

end LeanQbe.T.Arm64.AriscaCert
