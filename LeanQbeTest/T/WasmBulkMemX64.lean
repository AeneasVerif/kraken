module

public import LeanQbeTest.T.WasmBulkMemTest
public import LeanQbeTest.T.WasmCertKit
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainCertElab
public meta import LeanQbeTest.T.WasmBulkMemTest
public meta import LeanQbe.T.Amd64.TargLemmas
public meta import LeanQbe.T.MainCertElab
public meta import Kraken.X64.Syntax

/-!
# Kraken x86-64 WebAssembly Bulk-Memory & Growth Certificate (`WasmBulkMemX64`)

Compiles the real clang-compiled WebAssembly guest module `bulkQbe` (`test_mem_size`,
`test_mem_grow`, `test_mem_fill`, `test_mem_copy`) across 4 linked chunks (`chunkSize := 1`)
onto SysV x86-64 (`x64Target`) via `compile_linked_chunks!` and proves end-to-end Kraken x86-64
`Eventually (step1 Host.exe)` soundness and host-frame preservation for both valid and
adversarial OOB wraparound calls.

This module imports only `Kraken.X64` (`LeanQbe.T.Amd64.*`), never `Kraken.AArch64`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.WasmBulkMemX64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.Amd64 Kraken
open LeanQbeTest.T.WasmBulkMemTest LeanQbeTest.T.WasmCertKit

/-! ## 1. Multi-Chunk SysV x86-64 Compilation Certificate -/

compile_linked_chunks! x64BulkCert
  x64Target x64Layout x64LegalTarget x64LabelClean bulkQbe 1

theorem x64_bm_chunks : x64BulkCert.numChunks = 4 := rfl

theorem x64_bm_bound : x64BulkCert.bound "test_mem_copy" ≤ 2048 :=
  x64BulkCert.bound_le_max "test_mem_copy"

theorem x64_bm_legalSig : LegalSigAll x64LegalTarget bulkQbe.fns :=
  wasm_legalSigAll bulkMod rfl rfl

/-! ## 2. Whole-Module `FnSpec` & Kraken x86-64 `Eventually` Soundness -/

/-- Arbitrary-`Host` whole-module `FnSpec` for all 4 Wasm bulk-memory functions on x86-64. -/
theorem x64_bm_fnspec [hh : Host] (k₀ : Nat)
    (hc : x64BulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ bulkQbe.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (WasmSandboxEnvAny bulkMod f.name f.as f.rs)
        (x64BulkCert.bound f.name) 0 :=
  wasm_fnSpec_noExit x64BulkCert bm_valid bm_acyclic x64_bm_legalSig hh k₀ hc hu hf

/-- Linked-host `FnSpec` for `test_mem_copy` on `x64BulkCert.host`. -/
theorem x64_bm_host :
    x64Target.Defined x64BulkCert.host "test_mem_copy" ∧
      x64Target.FnSpec x64BulkCert.host "test_mem_copy"
        (WasmSandboxEnvAny bulkMod "test_mem_copy"
          [i64, i64, i32, i32, i32] [i32, i64])
        (x64BulkCert.bound "test_mem_copy") 0 :=
  wasm_fnSpec_host x64BulkCert bm_valid bm_acyclic x64_bm_legalSig
    (wf := fnCopy) (by simp [bulkMod])

/-- Closed Kraken x86-64 memory safety theorem for `test_mem_size`. -/
theorem x64_bm_size [hh : Host] (k₀ : Nat)
    (hc : x64BulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_size"))
          (x64BulkCert.bound "test_mem_size") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_size"))
              (x64BulkCert.bound "test_mem_size" + 8) ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (st.data.regs.get64 .rax).truncate 32 = status ∧
          st.data.regs.get64 .rdx = remFuel ∧
          (st.data.regs.get64 .rcx).truncate 32 = res)
      ⟨s, Labels.label "test_mem_size"⟩ :=
  wasm_of_returns_ret1_i32 (T := x64Target) rfl
    (x64_of_returns
      (wasm_fnSpec_wf x64BulkCert bm_valid bm_acyclic x64_bm_legalSig
        hh k₀ hc hu (wf := fnSize) (by simp [bulkMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [bulkMod]) rfl rfl
        vmCtx memBase memLen memCap fuel () hm₀)
      s ra R (wasm_argsIn_2 rfl hrdi hrsi) hsp hmem)

/-- Closed Kraken x86-64 memory safety theorem for `test_mem_grow`. -/
theorem x64_bm_grow [hh : Host] (k₀ : Nat)
    (hc : x64BulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (delta : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hrdx : s.regs.get64 .rdx = BitVec.setWidth 64 delta)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_grow"))
          (x64BulkCert.bound "test_mem_grow") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_grow"))
              (x64BulkCert.bound "test_mem_grow" + 8) ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (st.data.regs.get64 .rax).truncate 32 = status ∧
          st.data.regs.get64 .rdx = remFuel ∧
          (st.data.regs.get64 .rcx).truncate 32 = res)
      ⟨s, Labels.label "test_mem_grow"⟩ :=
  wasm_of_returns_ret1_i32 (T := x64Target) rfl
    (x64_of_returns
      (wasm_fnSpec_wf x64BulkCert bm_valid bm_acyclic x64_bm_legalSig
        hh k₀ hc hu (wf := fnGrow) (by simp [bulkMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [bulkMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (delta, ()) hm₀)
      s ra R (wasm_argsIn_3 rfl hrdi hrsi hrdx) hsp hmem)

/-- Closed Kraken x86-64 memory safety theorem for `test_mem_fill`. -/
theorem x64_bm_fill [hh : Host] (k₀ : Nat)
    (hc : x64BulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (dst val n : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hrdx : s.regs.get64 .rdx = BitVec.setWidth 64 dst)
    (hrcx : s.regs.get64 .rcx = BitVec.setWidth 64 val)
    (hr8 : s.regs.get64 .r8 = BitVec.setWidth 64 n)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_fill"))
          (x64BulkCert.bound "test_mem_fill") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_fill"))
              (x64BulkCert.bound "test_mem_fill" + 8) ⋆ R) st.data.dmem) ∧
        ∃ (status : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (st.data.regs.get64 .rax).truncate 32 = status ∧
          st.data.regs.get64 .rdx = remFuel)
      ⟨s, Labels.label "test_mem_fill"⟩ :=
  wasm_of_returns_void (T := x64Target) rfl
    (x64_of_returns
      (wasm_fnSpec_wf x64BulkCert bm_valid bm_acyclic x64_bm_legalSig
        hh k₀ hc hu (wf := fnFill) (by simp [bulkMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [bulkMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (dst, val, n, ()) hm₀)
      s ra R (wasm_argsIn_5 rfl hrdi hrsi hrdx hrcx hr8) hsp hmem)

/-- Closed Kraken x86-64 memory safety theorem for `test_mem_copy`. -/
theorem x64_bm_copy [hh : Host] (k₀ : Nat)
    (hc : x64BulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (dst src n : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hrdx : s.regs.get64 .rdx = BitVec.setWidth 64 dst)
    (hrcx : s.regs.get64 .rcx = BitVec.setWidth 64 src)
    (hr8 : s.regs.get64 .r8 = BitVec.setWidth 64 n)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_copy"))
          (x64BulkCert.bound "test_mem_copy") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_copy"))
              (x64BulkCert.bound "test_mem_copy" + 8) ⋆ R) st.data.dmem) ∧
        ∃ (status : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (st.data.regs.get64 .rax).truncate 32 = status ∧
          st.data.regs.get64 .rdx = remFuel)
      ⟨s, Labels.label "test_mem_copy"⟩ :=
  wasm_of_returns_void (T := x64Target) rfl
    (x64_of_returns
      (wasm_fnSpec_wf x64BulkCert bm_valid bm_acyclic x64_bm_legalSig
        hh k₀ hc hu (wf := fnCopy) (by simp [bulkMod]) rfl rfl)
      (wasm_sandbox_spec rfl (by simp [bulkMod]) rfl rfl
        vmCtx memBase memLen memCap fuel (dst, src, n, ()) hm₀)
      s ra R (wasm_argsIn_5 rfl hrdi hrsi hrdx hrcx hr8) hsp hmem)

/-- Adversarial `u32` wraparound call (`dst = 0xFFFFFFF0, n = 32`) on `test_mem_copy` returns
safely on x86-64 and preserves arbitrary host memory `R`. -/
theorem x64_bm_oob [hh : Host] (k₀ : Nat)
    (hc : x64BulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (vmCtx memBase memCap fuel : BitVec 64)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hrdx : s.regs.get64 .rdx = BitVec.setWidth 64 0xFFFFFFF0#32)
    (hrcx : s.regs.get64 .rcx = BitVec.setWidth 64 0#32)
    (hr8 : s.regs.get64 .r8 = BitVec.setWidth 64 32#32)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase 65536#64 memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_copy"))
          (x64BulkCert.bound "test_mem_copy") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∃ memLen', (65536#64 : BitVec 64).toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_copy"))
              (x64BulkCert.bound "test_mem_copy" + 8) ⋆ R) st.data.dmem) ∧
        ∃ status : BitVec 32,
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          (st.data.regs.get64 .rax).truncate 32 = status)
      ⟨s, Labels.label "test_mem_copy"⟩ := by
  refine eventually_weaken _ _ _ _ ?_
    (x64_bm_copy k₀ hc hu vmCtx memBase 65536#64 memCap fuel 0xFFFFFFF0#32 0#32 32#32
      s ra m₀ R hrdi hrsi hrdx hrcx hr8 hsp hm₀ hmem)
  rintro st ⟨hpc, _, _, hdmem, status, _, hst, _, hrax, _⟩
  exact ⟨hpc, hdmem, status, hst, hrax⟩

/-! ## 3. Logical Foundations Audit (Standard Axioms) -/

#print axioms x64_bm_legalSig
#print axioms x64_bm_fnspec
#print axioms x64_bm_host
#print axioms x64_bm_size
#print axioms x64_bm_grow
#print axioms x64_bm_fill
#print axioms x64_bm_copy
#print axioms x64_bm_oob

end LeanQbeTest.T.WasmBulkMemX64
