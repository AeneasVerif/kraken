/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Arm64.AriscaCert
public import LeanQbe.T.Examples.Arisca.Proof.CertBridge

/-!
# End-to-End AAPCS64 Arm64 Machine-Code Soundness for ARiSCA (`Arm64.Arisca`)

Composes the 45-function WP proof (`ariscaModule_ok`) with the kernel-checked AAPCS64 Arm64
compilation certificate (`ariscaArm64Cert`, entry stack bound `656` bytes) into:
* `module_fnspec` — whole-module `Defined` + `FnSpec` on any AArch64 host embedding
  `ariscaArm64Cert`;
* `check_bytes_arm64_correct` — full AAPCS64 Arm64 machine-code soundness (`XPost := False`) +
  callee-saved register, stack-pointer, and `Mem 64` separation-logic framing (`X0 = 20#64`
  (`AR_ACCEPT`) implies `ArtSound.checkArt_sound` multiplier or `SPEC_MITER` equivalence);
* `check_bytes_arm64_sound` — concise soundness corollary;
* `arm64_nonvacuous` — concrete closed-host `Mem 64` execution witness on `ariscaArm64Cert.host`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.Arisca

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.AriscaCert Kraken
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src.Module
open LeanQbe.T.Examples.Arisca.Proof
open LeanQbe.T.Examples.Arisca.Proof.CertBridge

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for all `45` functions of `ariscaModule` under `ariscaEnv` on `armTarget`. -/
theorem module_fnspec (k₀ : Nat)
    (hc : ariscaArm64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ ariscaModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (ariscaEnv f.name f.as f.rs) (ariscaArm64Cert.bound f.name) 0 :=
  arisca_module_fnspec_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll hh k₀ hc hu hf

/-- Closed end-to-end AAPCS64 Arm64 machine-code soundness and framing of `arisca_check_bytes`
(`X0..X5 → X0`, `AR_ACCEPT = 20#64`, entry stack bound `656` bytes). -/
theorem check_bytes_arm64_correct (k₀ : Nat)
    (hc : ariscaArm64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    (aigBytes artBytes : List UInt8)
    (haig : aig_len.toNat = aigBytes.length)
    (hart : art_len.toNat = artBytes.length)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = aig_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = aig_len)
    (hx2 : (s.regs.getXReg .X2).toBitVec = art_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = art_len)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (ariscaArm64Cert.bound "arisca_check_bytes"))
        (ariscaArm64Cert.bound "arisca_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes aigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (ariscaArm64Cert.bound "arisca_check_bytes"))
            (ariscaArm64Cert.bound "arisca_check_bytes") ⋆ R))
      ⟨s, Labels.label "arisca_check_bytes"⟩ :=
  arisca_check_bytes_correct_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll hh k₀ hc hu
    aig_ptr aig_len art_ptr art_len work_ptr work_len aigBytes artBytes haig hart
    s ra R hx0 hx1 hx2 hx3 hx4 hx5 ⟨hra, hsp⟩ hmem

/-- Concise AAPCS64 Arm64 machine-code soundness corollary of `check_bytes_arm64_correct`. -/
theorem check_bytes_arm64_sound (k₀ : Nat)
    (hc : ariscaArm64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    (aigBytes artBytes : List UInt8)
    (haig : aig_len.toNat = aigBytes.length)
    (hart : art_len.toNat = artBytes.length)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = aig_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = aig_len)
    (hx2 : (s.regs.getXReg .X2).toBitVec = art_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = art_len)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (ariscaArm64Cert.bound "arisca_check_bytes"))
        (ariscaArm64Cert.bound "arisca_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes aigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g))
      ⟨s, Labels.label "arisca_check_bytes"⟩ :=
  arisca_check_bytes_sound_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll hh k₀ hc hu
    aig_ptr aig_len art_ptr art_len work_ptr work_len aigBytes artBytes haig hart
    s ra R hx0 hx1 hx2 hx3 hx4 hx5 ⟨hra, hsp⟩ hmem

end Generic

/-! ## Concrete Closed-Host `Mem 64` Non-Vacuity Witness (`ariscaArm64Cert.host`) -/

noncomputable abbrev ariscaHost : Host := ariscaArm64Cert.host
attribute [local instance] ariscaHost

/-- Concrete initial Kraken AArch64 machine state for `arisca_check_bytes` non-vacuity. -/
@[expose] noncomputable def ariscaNvState0 : MachineData :=
  armInit.initState (as := [i64, i64, i64, i64, i64, i64])
    (ariscaArm64Cert.bound "arisca_check_bytes") ariscaNvPayload ariscaNvArgs

/-- Concrete `Mem 64` execution witness of compiled `arisca_check_bytes` on Kraken AArch64. -/
theorem arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes nvAigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt nvArtBytes 2)) g) ∧
        (st.data.dmem =⋆
          (bytes ariscaNvAigPtr nvAigBytes ⋆ bytes ariscaNvArtPtr nvArtBytes ⋆
            region ariscaNvWorkPtr ariscaNvWorkCap.toNat) ⋆
          region (0x1000#64 - BitVec.ofNat 64 (ariscaArm64Cert.bound "arisca_check_bytes"))
            (ariscaArm64Cert.bound "arisca_check_bytes") ⋆ emp))
      ⟨ariscaNvState0, Labels.label "arisca_check_bytes"⟩ :=
  arisca_check_bytes_nv_abi arm64BenchAbi ariscaArm64Cert ariscaArm64_legalSigAll

end LeanQbe.T.Arm64.Arisca
