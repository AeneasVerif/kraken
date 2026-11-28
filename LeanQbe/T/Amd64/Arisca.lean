/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.AriscaCert
public import LeanQbe.T.Examples.Arisca.Proof.CertBridge

/-!
# End-to-End SysV x86-64 Machine-Code Soundness for ARiSCA (`Amd64.Arisca`)

Composes the 45-function WP proof (`ariscaModule_ok`) with the kernel-checked SysV x86-64
compilation certificate (`ariscaX64Cert`, entry stack bound `688` bytes) into:
* `module_fnspec` — whole-module `Defined` + `FnSpec` on any x64 host embedding `ariscaX64Cert`;
* `check_bytes_x64_correct` — full SysV x86-64 machine-code soundness (`XPost := False`) +
  callee-saved register, stack-pointer, and `Mem 64` separation-logic framing (`rax = 20#64`
  (`AR_ACCEPT`) implies `ArtSound.checkArt_sound` multiplier or `SPEC_MITER` equivalence);
* `check_bytes_x64_sound` — concise soundness corollary;
* `x64_nonvacuous` — concrete closed-host `Mem 64` execution witness on `ariscaX64Cert.host`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.Arisca

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.AriscaCert Kraken
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src.Module
open LeanQbe.T.Examples.Arisca.Proof
open LeanQbe.T.Examples.Arisca.Proof.CertBridge

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for all `45` functions of `ariscaModule` under `ariscaEnv` on `x64Target`. -/
theorem module_fnspec (k₀ : Nat)
    (hc : ariscaX64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ ariscaModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (ariscaEnv f.name f.as f.rs) (ariscaX64Cert.bound f.name) 0 :=
  arisca_module_fnspec_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll hh k₀ hc hu hf

/-- Closed end-to-end SysV x86-64 machine-code soundness and framing of `arisca_check_bytes`
(`rdi..r9 → rax`, `AR_ACCEPT = 20#64`, entry stack bound `688` bytes). -/
theorem check_bytes_x64_correct (k₀ : Nat)
    (hc : ariscaX64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    (aigBytes artBytes : List UInt8)
    (haig : aig_len.toNat = aigBytes.length)
    (hart : art_len.toNat = artBytes.length)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = aig_ptr)
    (hrsi : s.regs.get64 .rsi = aig_len)
    (hrdx : s.regs.get64 .rdx = art_ptr)
    (hrcx : s.regs.get64 .rcx = art_len)
    (hr8 : s.regs.get64 .r8 = work_ptr)
    (hr9 : s.regs.get64 .r9 = work_len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (ariscaX64Cert.bound "arisca_check_bytes"))
          (ariscaX64Cert.bound "arisca_check_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes aigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (ariscaX64Cert.bound "arisca_check_bytes"))
            (ariscaX64Cert.bound "arisca_check_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "arisca_check_bytes"⟩ :=
  arisca_check_bytes_correct_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll hh k₀ hc hu
    aig_ptr aig_len art_ptr art_len work_ptr work_len aigBytes artBytes haig hart
    s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

/-- Concise SysV x86-64 machine-code soundness corollary of `check_bytes_x64_correct`. -/
theorem check_bytes_x64_sound (k₀ : Nat)
    (hc : ariscaX64Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    (aigBytes artBytes : List UInt8)
    (haig : aig_len.toNat = aigBytes.length)
    (hart : art_len.toNat = artBytes.length)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = aig_ptr)
    (hrsi : s.regs.get64 .rsi = aig_len)
    (hrdx : s.regs.get64 .rdx = art_ptr)
    (hrcx : s.regs.get64 .rcx = art_len)
    (hr8 : s.regs.get64 .r8 = work_ptr)
    (hr9 : s.regs.get64 .r9 = work_len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (ariscaX64Cert.bound "arisca_check_bytes"))
          (ariscaX64Cert.bound "arisca_check_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes aigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g))
      ⟨s, Labels.label "arisca_check_bytes"⟩ :=
  arisca_check_bytes_sound_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll hh k₀ hc hu
    aig_ptr aig_len art_ptr art_len work_ptr work_len aigBytes artBytes haig hart
    s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

end Generic

/-! ## Concrete Closed-Host `Mem 64` Non-Vacuity Witness (`ariscaX64Cert.host`) -/

noncomputable abbrev ariscaHost : Host := ariscaX64Cert.host
attribute [local instance] ariscaHost

/-- Concrete initial Kraken x86-64 machine state for `arisca_check_bytes` non-vacuity. -/
@[expose] noncomputable def ariscaNvState0 : MachineData :=
  x64Init.initState (as := [i64, i64, i64, i64, i64, i64])
    (ariscaX64Cert.bound "arisca_check_bytes") ariscaNvPayload ariscaNvArgs

/-- Concrete `Mem 64` execution witness of compiled `arisca_check_bytes` on Kraken x86-64. -/
theorem x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes nvAigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt nvArtBytes 2)) g) ∧
        (st.data.dmem =⋆
          (bytes ariscaNvAigPtr nvAigBytes ⋆ bytes ariscaNvArtPtr nvArtBytes ⋆
            region ariscaNvWorkPtr ariscaNvWorkCap.toNat) ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (ariscaX64Cert.bound "arisca_check_bytes"))
            (ariscaX64Cert.bound "arisca_check_bytes" + 8) ⋆ emp))
      ⟨ariscaNvState0, Labels.label "arisca_check_bytes"⟩ :=
  arisca_check_bytes_nv_abi x64BenchAbi ariscaX64Cert ariscaX64_legalSigAll

end LeanQbe.T.Amd64.Arisca
