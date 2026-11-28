module

import LeanQbeTest.T.WasmBulkMemTest
import LeanQbeTest.T.WasmCertKit
import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.MainCertElab
meta import LeanQbeTest.T.WasmBulkMemTest
meta import LeanQbe.T.Arm64.TargLemmas
meta import Kraken.AArch64.Syntax

/-!
# Kraken AArch64 WebAssembly Bulk-Memory & Growth Certificate (`WasmBulkMemArm64`)

Compiles the real clang-compiled WebAssembly guest module `bulkQbe` (`test_mem_size`,
`test_mem_grow`, `test_mem_fill`, `test_mem_copy`) across 4 linked chunks (`chunkSize := 1`)
onto AAPCS64 AArch64 (`armTarget`) via `compile_linked_chunks!` and proves end-to-end Kraken
AArch64 `Eventually (step1 Host.exe)` soundness and host-frame preservation for both valid and
adversarial OOB wraparound calls.

This module imports only `Kraken.AArch64` (`LeanQbe.T.Arm64.*`), never `Kraken.X64`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.WasmBulkMemArm64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.Arm64 Kraken
open LeanQbeTest.T.WasmBulkMemTest LeanQbeTest.T.WasmCertKit

/-! ## 1. Multi-Chunk AAPCS64 Compilation Certificate -/

compile_linked_chunks! armBulkCert
  armTarget armLayout armLegalTarget armLabelClean bulkQbe 1

theorem arm_bm_chunks : armBulkCert.numChunks = 4 := rfl

theorem arm_bm_bound : armBulkCert.bound "test_mem_copy" ≤ 2048 :=
  armBulkCert.bound_le_max "test_mem_copy"

theorem arm_bm_legalSig : LegalSigAll armLegalTarget bulkQbe.fns :=
  wasm_legalSigAll bulkMod rfl rfl

/-! ## 2. Whole-Module `FnSpec` & Kraken AArch64 `Eventually` Soundness -/

/-- Arbitrary-`Host` whole-module `FnSpec` for all 4 Wasm bulk-memory functions on AArch64. -/
theorem arm_bm_fnspec [hh : Host] (k₀ : Nat)
    (hc : armBulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ bulkQbe.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (WasmSandboxEnvAny bulkMod f.name f.as f.rs)
        (armBulkCert.bound f.name) 0 :=
  wasm_fnSpec_noExit armBulkCert bm_valid bm_acyclic arm_bm_legalSig hh k₀ hc hu hf

/-- Linked-host `FnSpec` for `test_mem_copy` on `armBulkCert.host`. -/
theorem arm_bm_host :
    armTarget.Defined armBulkCert.host "test_mem_copy" ∧
      armTarget.FnSpec armBulkCert.host "test_mem_copy"
        (WasmSandboxEnvAny bulkMod "test_mem_copy"
          [i64, i64, i32, i32, i32] [i32, i64])
        (armBulkCert.bound "test_mem_copy") 0 :=
  wasm_fnSpec_host armBulkCert bm_valid bm_acyclic arm_bm_legalSig
    (wf := fnCopy) (by simp [bulkMod])

/-- Closed Kraken AArch64 memory safety theorem for `test_mem_size`. -/
theorem arm_bm_size [hh : Host] (k₀ : Nat)
    (hc : armBulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_size"))
        (armBulkCert.bound "test_mem_size") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_size"))
              (armBulkCert.bound "test_mem_size") ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status ∧
          (st.data.regs.getXReg .X1).toBitVec = remFuel ∧
          ((st.data.regs.getXReg .X2).toBitVec).truncate 32 = res)
      ⟨s, Labels.label "test_mem_size"⟩ :=
  wasm_of_returns_ret1_i32 (T := armTarget) rfl
    (arm64_of_returns
      (wasm_fnSpec_wf armBulkCert bm_valid bm_acyclic arm_bm_legalSig
        hh k₀ hc hu (wf := fnSize) (by simp [bulkMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [bulkMod]) rfl rfl
        vmCtx memBase memLen memCap fuel () hm₀)
      s ra R (wasm_argsIn_2 rfl hx0 hx1) hra hsp hmem)

/-- Closed Kraken AArch64 memory safety theorem for `test_mem_grow`. -/
theorem arm_bm_grow [hh : Host] (k₀ : Nat)
    (hc : armBulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (delta : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 delta)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_grow"))
        (armBulkCert.bound "test_mem_grow") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_grow"))
              (armBulkCert.bound "test_mem_grow") ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status ∧
          (st.data.regs.getXReg .X1).toBitVec = remFuel ∧
          ((st.data.regs.getXReg .X2).toBitVec).truncate 32 = res)
      ⟨s, Labels.label "test_mem_grow"⟩ :=
  wasm_of_returns_ret1_i32 (T := armTarget) rfl
    (arm64_of_returns
      (wasm_fnSpec_wf armBulkCert bm_valid bm_acyclic arm_bm_legalSig
        hh k₀ hc hu (wf := fnGrow) (by simp [bulkMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [bulkMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (delta, ()) hm₀)
      s ra R (wasm_argsIn_3 rfl hx0 hx1 hx2) hra hsp hmem)

/-- Closed Kraken AArch64 memory safety theorem for `test_mem_fill`. -/
theorem arm_bm_fill [hh : Host] (k₀ : Nat)
    (hc : armBulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (dst val n : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 dst)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.setWidth 64 val)
    (hx4 : (s.regs.getXReg .X4).toBitVec = BitVec.setWidth 64 n)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_fill"))
        (armBulkCert.bound "test_mem_fill") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_fill"))
              (armBulkCert.bound "test_mem_fill") ⋆ R) st.data.dmem) ∧
        ∃ (status : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status ∧
          (st.data.regs.getXReg .X1).toBitVec = remFuel)
      ⟨s, Labels.label "test_mem_fill"⟩ :=
  wasm_of_returns_void (T := armTarget) rfl
    (arm64_of_returns
      (wasm_fnSpec_wf armBulkCert bm_valid bm_acyclic arm_bm_legalSig
        hh k₀ hc hu (wf := fnFill) (by simp [bulkMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [bulkMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (dst, val, n, ()) hm₀)
      s ra R (wasm_argsIn_5 rfl hx0 hx1 hx2 hx3 hx4) hra hsp hmem)

/-- Closed Kraken AArch64 memory safety theorem for `test_mem_copy`. -/
theorem arm_bm_copy [hh : Host] (k₀ : Nat)
    (hc : armBulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (dst src n : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 dst)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.setWidth 64 src)
    (hx4 : (s.regs.getXReg .X4).toBitVec = BitVec.setWidth 64 n)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_copy"))
        (armBulkCert.bound "test_mem_copy") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_copy"))
              (armBulkCert.bound "test_mem_copy") ⋆ R) st.data.dmem) ∧
        ∃ (status : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status ∧
          (st.data.regs.getXReg .X1).toBitVec = remFuel)
      ⟨s, Labels.label "test_mem_copy"⟩ :=
  wasm_of_returns_void (T := armTarget) rfl
    (arm64_of_returns
      (wasm_fnSpec_wf armBulkCert bm_valid bm_acyclic arm_bm_legalSig
        hh k₀ hc hu (wf := fnCopy) (by simp [bulkMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [bulkMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (dst, src, n, ()) hm₀)
      s ra R (wasm_argsIn_5 rfl hx0 hx1 hx2 hx3 hx4) hra hsp hmem)

/-- Adversarial `u32` wraparound call (`dst = 0xFFFFFFF0, n = 32`) on `test_mem_copy` returns
safely on AArch64 and preserves arbitrary host memory `R`. -/
theorem arm_bm_oob [hh : Host] (k₀ : Nat)
    (hc : armBulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memCap fuel : BitVec 64)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 0xFFFFFFF0#32)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.setWidth 64 0#32)
    (hx4 : (s.regs.getXReg .X4).toBitVec = BitVec.setWidth 64 32#32)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase 65536#64 memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_copy"))
        (armBulkCert.bound "test_mem_copy") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∃ memLen', (65536#64 : BitVec 64).toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_copy"))
              (armBulkCert.bound "test_mem_copy") ⋆ R) st.data.dmem) ∧
        ∃ status : BitVec 32,
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status)
      ⟨s, Labels.label "test_mem_copy"⟩ := by
  refine eventually_weaken _ _ _ _ ?_
    (arm_bm_copy k₀ hc hu vmCtx memBase 65536#64 memCap fuel 0xFFFFFFF0#32 0#32 32#32
      s ra m₀ R hx0 hx1 hx2 hx3 hx4 hra hsp hm₀ hmem)
  rintro st ⟨hpc, _, _, hdmem, status, _, hst, _, hx0', _⟩
  exact ⟨hpc, hdmem, status, hst, hx0'⟩

/-! ## 3. Logical Foundations Audit (Standard Axioms) -/

#print axioms arm_bm_legalSig
#print axioms arm_bm_fnspec
#print axioms arm_bm_host
#print axioms arm_bm_size
#print axioms arm_bm_grow
#print axioms arm_bm_fill
#print axioms arm_bm_copy
#print axioms arm_bm_oob

end LeanQbeTest.T.WasmBulkMemArm64
