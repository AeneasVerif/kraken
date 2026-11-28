module

import LeanQbeTest.T.WasmAuditSpec
import LeanQbeTest.T.WasmCertKit
import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.MainCertElab
meta import LeanQbeTest.T.WasmAuditSpec
meta import LeanQbe.T.Amd64.TargLemmas
meta import Kraken.X64.Syntax

/-!
# Kraken x86-64 WebAssembly Memory Safety Audit (`WasmAuditX64`)

Compiles the multi-function WebAssembly guest module `wasmQbeMod` (`mix32`, `write_hash`,
`sum_mix`) across 3 linked chunks (`chunkSize := 1`) onto SysV x86-64 (`x64Target`) via
`compile_linked_chunks!` and proves end-to-end Kraken x86-64 `Eventually (step1 Host.exe)`
host-memory preservation and sandboxed execution theorems.

This module imports only `Kraken.X64` (`LeanQbe.T.Amd64.*`), never `Kraken.AArch64`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.WasmAuditX64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.Amd64 Kraken
open LeanQbeTest.T.WasmAuditSpec LeanQbeTest.T.WasmCertKit

/-! ## 1. Multi-Chunk SysV x86-64 Compilation Certificate -/

compile_linked_chunks! x64WasmCert
  x64Target x64Layout x64LegalTarget x64LabelClean wasmQbeMod 1

theorem x64WasmCert_chunks : x64WasmCert.numChunks = 3 := rfl

theorem x64WasmCert_bound_le : x64WasmCert.bound "sum_mix" ≤ 2048 :=
  x64WasmCert.bound_le_max "sum_mix"

theorem x64_wasm_legalSig : LegalSigAll x64LegalTarget wasmQbeMod.fns :=
  wasm_legalSigAll wasmAuditMod rfl rfl

/-! ## 2. Whole-Module `FnSpec` & Kraken x86-64 `Eventually` Safety Theorems -/

/-- Arbitrary-`Host` whole-module `FnSpec` for all 3 Wasm guest functions on x86-64. -/
theorem x64_wasm_fnspec [hh : Host] (k₀ : Nat)
    (hc : x64WasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ wasmQbeMod.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (WasmSandboxEnvAny wasmAuditMod f.name f.as f.rs)
        (x64WasmCert.bound f.name) 0 :=
  wasm_fnSpec_noExit x64WasmCert wasmAuditMod_valid wasmQbeMod_acyclic x64_wasm_legalSig
    hh k₀ hc hu hf

/-- Linked-host `FnSpec` for `sum_mix` on `x64WasmCert.host`. -/
theorem x64_wasm_host :
    x64Target.Defined x64WasmCert.host "sum_mix" ∧
      x64Target.FnSpec x64WasmCert.host "sum_mix"
        (WasmSandboxEnvAny wasmAuditMod "sum_mix"
          [i64, i64, i32, i32] [i32, i64, i32])
        (x64WasmCert.bound "sum_mix") 0 :=
  wasm_fnSpec_host x64WasmCert wasmAuditMod_valid wasmQbeMod_acyclic x64_wasm_legalSig
    (wf := fnSumMix) (by simp [wasmAuditMod])

/-- Closed Kraken x86-64 memory safety theorem for Wasm loop kernel `sum_mix`. -/
theorem x64_wasm_sum_safe [hh : Host] (k₀ : Nat)
    (hc : x64WasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (ptr len : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hrdx : s.regs.get64 .rdx = BitVec.setWidth 64 ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.setWidth 64 len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64WasmCert.bound "sum_mix"))
          (x64WasmCert.bound "sum_mix") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64WasmCert.bound "sum_mix"))
              (x64WasmCert.bound "sum_mix" + 8) ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (st.data.regs.get64 .rax).truncate 32 = status ∧
          st.data.regs.get64 .rdx = remFuel ∧
          (st.data.regs.get64 .rcx).truncate 32 = res)
      ⟨s, Labels.label "sum_mix"⟩ :=
  wasm_of_returns_ret1_i32 (T := x64Target) rfl
    (x64_of_returns
      (wasm_fnSpec_wf x64WasmCert wasmAuditMod_valid wasmQbeMod_acyclic x64_wasm_legalSig
        hh k₀ hc hu (wf := fnSumMix) (by simp [wasmAuditMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [wasmAuditMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (ptr, len, ()) hm₀)
      s ra R (wasm_argsIn_4 rfl hrdi hrsi hrdx hrcx) hsp hmem)

/-- Closed Kraken x86-64 memory safety theorem for Wasm store/if kernel `write_hash`. -/
theorem x64_wasm_write_safe [hh : Host] (k₀ : Nat)
    (hc : x64WasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (ptr word : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hrdx : s.regs.get64 .rdx = BitVec.setWidth 64 ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.setWidth 64 word)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64WasmCert.bound "write_hash"))
          (x64WasmCert.bound "write_hash") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64WasmCert.bound "write_hash"))
              (x64WasmCert.bound "write_hash" + 8) ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (st.data.regs.get64 .rax).truncate 32 = status ∧
          st.data.regs.get64 .rdx = remFuel ∧
          (st.data.regs.get64 .rcx).truncate 32 = res)
      ⟨s, Labels.label "write_hash"⟩ :=
  wasm_of_returns_ret1_i32 (T := x64Target) rfl
    (x64_of_returns
      (wasm_fnSpec_wf x64WasmCert wasmAuditMod_valid wasmQbeMod_acyclic x64_wasm_legalSig
        hh k₀ hc hu (wf := fnWriteHash) (by simp [wasmAuditMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [wasmAuditMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (ptr, word, ()) hm₀)
      s ra R (wasm_argsIn_4 rfl hrdi hrsi hrdx hrcx) hsp hmem)

/-- Out-of-bounds Wasm guest call (`memLen = 4`, `len = 16`) still returns safely on x86-64 and
preserves arbitrary host memory `R`. -/
theorem x64_wasm_oob_safe [hh : Host] (k₀ : Nat)
    (hc : x64WasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memCap fuel : BitVec 64)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hrdx : s.regs.get64 .rdx = BitVec.setWidth 64 0#32)
    (hrcx : s.regs.get64 .rcx = BitVec.setWidth 64 16#32)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase 4#64 memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64WasmCert.bound "sum_mix"))
          (x64WasmCert.bound "sum_mix") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∃ memLen', (4#64 : BitVec 64).toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64WasmCert.bound "sum_mix"))
              (x64WasmCert.bound "sum_mix" + 8) ⋆ R) st.data.dmem) ∧
        ∃ status : BitVec 32,
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          (st.data.regs.get64 .rax).truncate 32 = status)
      ⟨s, Labels.label "sum_mix"⟩ := by
  refine eventually_weaken _ _ _ _ ?_
    (x64_wasm_sum_safe k₀ hc hu vmCtx memBase 4#64 memCap fuel 0#32 16#32 s ra m₀ R
      hrdi hrsi hrdx hrcx hsp hm₀ hmem)
  rintro st ⟨hpc, _, _, hdmem, status, _, _, hst, _, hrax, _, _⟩
  exact ⟨hpc, hdmem, status, hst, hrax⟩

/-! ## 3. Logical Foundations Audit (`#print axioms`) -/

#print axioms x64_wasm_legalSig
#print axioms x64_wasm_fnspec
#print axioms x64_wasm_host
#print axioms x64_wasm_sum_safe
#print axioms x64_wasm_write_safe
#print axioms x64_wasm_oob_safe

end LeanQbeTest.T.WasmAuditX64
