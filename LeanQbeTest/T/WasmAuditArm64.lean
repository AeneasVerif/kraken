module

public import LeanQbeTest.T.WasmAuditSpec
public import LeanQbeTest.T.WasmCertKit
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainCertElab
public meta import LeanQbeTest.T.WasmAuditSpec
public meta import LeanQbe.T.Arm64.TargLemmas
public meta import LeanQbe.T.MainCertElab
public meta import Kraken.AArch64.Syntax

/-!
# Kraken AArch64 WebAssembly Memory Safety Audit (`WasmAuditArm64`)

Compiles the multi-function WebAssembly guest module `wasmQbeMod` (`mix32`, `write_hash`,
`sum_mix`) across 3 linked chunks (`chunkSize := 1`) onto AAPCS64 AArch64 (`armTarget`) via
`compile_linked_chunks!` and proves end-to-end Kraken AArch64 `Eventually (step1 Host.exe)`
host-memory preservation and sandboxed execution theorems.

This module imports only `Kraken.AArch64` (`LeanQbe.T.Arm64.*`), never `Kraken.X64`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.WasmAuditArm64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.Arm64 Kraken
open LeanQbeTest.T.WasmAuditSpec LeanQbeTest.T.WasmCertKit

/-! ## 1. Multi-Chunk AAPCS64 Compilation Certificate -/

compile_linked_chunks! armWasmCert
  armTarget armLayout armLegalTarget armLabelClean wasmQbeMod 1

theorem armWasmCert_chunks : armWasmCert.numChunks = 3 := rfl

theorem armWasmCert_bound_le : armWasmCert.bound "sum_mix" ≤ 2048 :=
  armWasmCert.bound_le_max "sum_mix"

theorem arm_wasm_legalSig : LegalSigAll armLegalTarget wasmQbeMod.fns :=
  wasm_legalSigAll wasmAuditMod rfl rfl

/-! ## 2. Whole-Module `FnSpec` & Kraken AArch64 `Eventually` Safety Theorems -/

/-- Arbitrary-`Host` whole-module `FnSpec` for all 3 Wasm guest functions on AArch64. -/
theorem arm_wasm_fnspec [hh : Host] (k₀ : Nat)
    (hc : armWasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ wasmQbeMod.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (WasmSandboxEnvAny wasmAuditMod f.name f.as f.rs)
        (armWasmCert.bound f.name) 0 :=
  wasm_fnSpec_noExit armWasmCert wasmAuditMod_valid wasmQbeMod_acyclic arm_wasm_legalSig
    hh k₀ hc hu hf

/-- Linked-host `FnSpec` for `sum_mix` on `armWasmCert.host`. -/
theorem arm_wasm_host :
    armTarget.Defined armWasmCert.host "sum_mix" ∧
      armTarget.FnSpec armWasmCert.host "sum_mix"
        (WasmSandboxEnvAny wasmAuditMod "sum_mix"
          [i64, i64, i32, i32] [i32, i64, i32])
        (armWasmCert.bound "sum_mix") 0 :=
  wasm_fnSpec_host armWasmCert wasmAuditMod_valid wasmQbeMod_acyclic arm_wasm_legalSig
    (wf := fnSumMix) (by simp [wasmAuditMod])

/-- Closed Kraken AArch64 memory safety theorem for Wasm loop kernel `sum_mix`. -/
theorem arm_wasm_sum_safe [hh : Host] (k₀ : Nat)
    (hc : armWasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (ptr len : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.setWidth 64 len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound "sum_mix"))
        (armWasmCert.bound "sum_mix") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound "sum_mix"))
              (armWasmCert.bound "sum_mix") ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status ∧
          (st.data.regs.getXReg .X1).toBitVec = remFuel ∧
          ((st.data.regs.getXReg .X2).toBitVec).truncate 32 = res)
      ⟨s, Labels.label "sum_mix"⟩ :=
  wasm_of_returns_ret1_i32 (T := armTarget) rfl
    (arm64_of_returns
      (wasm_fnSpec_wf armWasmCert wasmAuditMod_valid wasmQbeMod_acyclic arm_wasm_legalSig
        hh k₀ hc hu (wf := fnSumMix) (by simp [wasmAuditMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [wasmAuditMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (ptr, len, ()) hm₀)
      s ra R (wasm_argsIn_4 rfl hx0 hx1 hx2 hx3) hra hsp hmem)

/-- Closed Kraken AArch64 memory safety theorem for Wasm store/if kernel `write_hash`. -/
theorem arm_wasm_write_safe [hh : Host] (k₀ : Nat)
    (hc : armWasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (ptr word : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.setWidth 64 word)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound "write_hash"))
        (armWasmCert.bound "write_hash") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound "write_hash"))
              (armWasmCert.bound "write_hash") ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status ∧
          (st.data.regs.getXReg .X1).toBitVec = remFuel ∧
          ((st.data.regs.getXReg .X2).toBitVec).truncate 32 = res)
      ⟨s, Labels.label "write_hash"⟩ :=
  wasm_of_returns_ret1_i32 (T := armTarget) rfl
    (arm64_of_returns
      (wasm_fnSpec_wf armWasmCert wasmAuditMod_valid wasmQbeMod_acyclic arm_wasm_legalSig
        hh k₀ hc hu (wf := fnWriteHash) (by simp [wasmAuditMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [wasmAuditMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (ptr, word, ()) hm₀)
      s ra R (wasm_argsIn_4 rfl hx0 hx1 hx2 hx3) hra hsp hmem)

/-- Out-of-bounds Wasm guest call (`memLen = 4`, `len = 16`) still returns safely on AArch64 and
preserves arbitrary host memory `R`. -/
theorem arm_wasm_oob_safe [hh : Host] (k₀ : Nat)
    (hc : armWasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memCap fuel : BitVec 64)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 0#32)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.setWidth 64 16#32)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase 4#64 memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound "sum_mix"))
        (armWasmCert.bound "sum_mix") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∃ memLen', (4#64 : BitVec 64).toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound "sum_mix"))
              (armWasmCert.bound "sum_mix") ⋆ R) st.data.dmem) ∧
        ∃ status : BitVec 32,
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status)
      ⟨s, Labels.label "sum_mix"⟩ := by
  refine eventually_weaken _ _ _ _ ?_
    (arm_wasm_sum_safe k₀ hc hu vmCtx memBase 4#64 memCap fuel 0#32 16#32 s ra m₀ R
      hx0 hx1 hx2 hx3 hra hsp hm₀ hmem)
  rintro st ⟨hpc, _, _, hdmem, status, _, _, hst, _, hx0', _, _⟩
  exact ⟨hpc, hdmem, status, hst, hx0'⟩

/-! ## 3. Logical Foundations Audit (`#print axioms`) -/

#print axioms arm_wasm_legalSig
#print axioms arm_wasm_fnspec
#print axioms arm_wasm_host
#print axioms arm_wasm_sum_safe
#print axioms arm_wasm_write_safe
#print axioms arm_wasm_oob_safe

end LeanQbeTest.T.WasmAuditArm64
