module

public import LeanQbeTest.T.WasmBulkMemTest
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

This module imports ONLY `Kraken.X64` (`LeanQbe.T.Amd64.*`), never `Kraken.AArch64`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.WasmBulkMemX64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.Amd64 Kraken
open LeanQbeTest.T.WasmBulkMemTest

/-! ## 1. Multi-Chunk SysV x86-64 Compilation Certificate -/

compile_linked_chunks! x64BulkCert
  x64Target x64Layout x64LegalTarget x64LabelClean bulkQbe 1

theorem x64_bm_chunks : x64BulkCert.numChunks = 4 := rfl

theorem x64_bm_bound : x64BulkCert.bound "test_mem_copy" ≤ 2048 :=
  x64BulkCert.bound_le_max "test_mem_copy"

theorem x64_bm_legalSig : LegalSigAll x64LegalTarget bulkQbe.fns := by
  intro f hf
  exact lowerModule_legalSig bulkMod rfl rfl f hf

/-! ## 2. Whole-Module `FnSpec` & Kraken x86-64 `Eventually` Soundness -/

/-- Arbitrary-`Host` whole-module `FnSpec` for all 4 Wasm bulk-memory functions on x86-64. -/
theorem x64_bm_fnspec [hh : Host] (k₀ : Nat)
    (hc : x64BulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ bulkQbe.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (WasmSandboxEnvAny bulkMod f.name f.as f.rs)
        (x64BulkCert.bound f.name) 0 :=
  x64BulkCert.fnSpec_noExit_of_legalSigAll hh (WasmSandboxEnvAny bulkMod) k₀ hc hu
    bm_acyclic bm_wf x64_bm_legalSig bm_wp hf
    (fun args mem Q X X' h => bm_any_monoX f.name f.as f.rs args mem Q X X' h)

/-- Linked-host `FnSpec` for `test_mem_copy` on `x64BulkCert.host`. -/
theorem x64_bm_host :
    x64Target.Defined x64BulkCert.host "test_mem_copy" ∧
      x64Target.FnSpec x64BulkCert.host "test_mem_copy"
        (WasmSandboxEnvAny bulkMod "test_mem_copy"
          [i64, i64, i32, i32, i32] [i32, i64])
        (x64BulkCert.bound "test_mem_copy") 0 :=
  x64BulkCert.fnSpec_host_of_legalSigAll (WasmSandboxEnvAny bulkMod)
    bm_acyclic bm_wf x64_bm_legalSig bm_wp bm_fn_copy_qbe
    (fun args mem Q X X' h =>
      bm_any_monoX "test_mem_copy" [i64, i64, i32, i32, i32] [i32, i64]
        args mem Q X X' h)

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
      ⟨s, Labels.label "test_mem_size"⟩ := by
  have hfn : x64Target.FnSpec hh "test_mem_size"
      (WasmSandboxEnvAny bulkMod "test_mem_size" [i64, i64] [i32, i64, i32])
      (x64BulkCert.bound "test_mem_size") 0 :=
    (x64_bm_fnspec k₀ hc hu bm_fn_size_qbe).2
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (vmCtx, fuel, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ (.cons ⟨by decide, by simpa using hrsi⟩ .nil)⟩
  have hspec : WasmSandboxEnvAny bulkMod "test_mem_size" [i64, i64] [i32, i64, i32]
      (vmCtx, fuel, ()) m₀ (WasmPost true vmCtx memBase memLen memCap fuel [.i32] emp)
      (fun _ _ _ _ => False) :=
    ⟨fuel.toNat, fnSize, by simp [bulkMod], rfl, rfl, rfl, Nat.le_refl _,
      memBase, memLen, memCap, emp, hm₀, fun _ _ h => h⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcal, hrsp, ⟨st0, rf, r0, ⟨⟩⟩, m', hpost, hrets, hmem'⟩
  rcases hpost with ⟨hst, hrf, memLen', hlen', hcap', hsepInv⟩
  simp only [sep_emp] at hsepInv
  rcases hrets with ⟨locsR, hlocR, hrelR⟩
  have heqR : locsR = (.gpr .rax, .gpr .rdx, .gpr .rcx, ()) := by
    injection hlocR with h1; exact h1.symm
  subst heqR
  cases hrelR; rename_i hrax h1; cases h1; rename_i hrdx h2; cases h2; rename_i hrcx _
  refine ⟨hpc, hcal, hrsp, ⟨memLen', hlen', hcap', ?_⟩, st0, r0, rf, hst, hrf,
    by simpa [BitVec.truncate] using congrArg (BitVec.setWidth 32) hrax.2,
    by simpa using hrdx.2,
    by simpa [BitVec.truncate] using congrArg (BitVec.setWidth 32) hrcx.2⟩
  have hmem'' : ((cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen' ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat) ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_size"))
        (x64BulkCert.bound "test_mem_size" + 8) ⋆ R) st.data.dmem :=
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hsepInv)) hmem'
  exact sep_cast hmem'' (by ac_rfl)

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
      ⟨s, Labels.label "test_mem_grow"⟩ := by
  have hfn : x64Target.FnSpec hh "test_mem_grow"
      (WasmSandboxEnvAny bulkMod "test_mem_grow" [i64, i64, i32] [i32, i64, i32])
      (x64BulkCert.bound "test_mem_grow") 0 :=
    (x64_bm_fnspec k₀ hc hu bm_fn_grow_qbe).2
  have hargs : x64Target.ArgsIn (as := [i64, i64, i32]) (vmCtx, fuel, delta, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ (.cons ⟨by decide, by simpa using hrsi⟩
      (.cons ⟨by decide, by simpa using hrdx⟩ .nil))⟩
  have hspec : WasmSandboxEnvAny bulkMod "test_mem_grow" [i64, i64, i32] [i32, i64, i32]
      (vmCtx, fuel, delta, ()) m₀ (WasmPost true vmCtx memBase memLen memCap fuel [.i32] emp)
      (fun _ _ _ _ => False) :=
    ⟨fuel.toNat, fnGrow, by simp [bulkMod], rfl, rfl, rfl, Nat.le_refl _,
      memBase, memLen, memCap, emp, hm₀, fun _ _ h => h⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcal, hrsp, ⟨st0, rf, r0, ⟨⟩⟩, m', hpost, hrets, hmem'⟩
  rcases hpost with ⟨hst, hrf, memLen', hlen', hcap', hsepInv⟩
  simp only [sep_emp] at hsepInv
  rcases hrets with ⟨locsR, hlocR, hrelR⟩
  have heqR : locsR = (.gpr .rax, .gpr .rdx, .gpr .rcx, ()) := by
    injection hlocR with h1; exact h1.symm
  subst heqR
  cases hrelR; rename_i hrax h1; cases h1; rename_i hrdx h2; cases h2; rename_i hrcx _
  refine ⟨hpc, hcal, hrsp, ⟨memLen', hlen', hcap', ?_⟩, st0, r0, rf, hst, hrf,
    by simpa [BitVec.truncate] using congrArg (BitVec.setWidth 32) hrax.2,
    by simpa using hrdx.2,
    by simpa [BitVec.truncate] using congrArg (BitVec.setWidth 32) hrcx.2⟩
  have hmem'' : ((cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen' ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat) ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound "test_mem_grow"))
        (x64BulkCert.bound "test_mem_grow" + 8) ⋆ R) st.data.dmem :=
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hsepInv)) hmem'
  exact sep_cast hmem'' (by ac_rfl)

private theorem x64_bm_void3_eventually [hh : Host] (k₀ : Nat)
    (hc : x64BulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (wf : WFunc) (hwf : wf ∈ bulkMod.funcs) (htidx : wf.typeIdx = 2)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (a0 a1 a2 : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = vmCtx)
    (hrsi : s.regs.get64 .rsi = fuel)
    (hrdx : s.regs.get64 .rdx = BitVec.setWidth 64 a0)
    (hrcx : s.regs.get64 .rcx = BitVec.setWidth 64 a1)
    (hr8 : s.regs.get64 .r8 = BitVec.setWidth 64 a2)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound wf.name))
          (x64BulkCert.bound wf.name) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound wf.name))
              (x64BulkCert.bound wf.name + 8) ⋆ R) st.data.dmem) ∧
        ∃ (status : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (st.data.regs.get64 .rax).truncate 32 = status ∧
          st.data.regs.get64 .rdx = remFuel)
      ⟨s, Labels.label wf.name⟩ := by
  rcases wf with ⟨nm, ti, locs, bd⟩
  dsimp only at hwf htidx hmem ⊢
  subst htidx
  have hfnMem : lowerFn bulkMod ⟨nm, 2, locs, bd⟩ ∈ bulkQbe.fns :=
    List.mem_map.mpr ⟨⟨nm, 2, locs, bd⟩, hwf, rfl⟩
  have hfn : x64Target.FnSpec hh nm
      (WasmSandboxEnvAny bulkMod nm [i64, i64, i32, i32, i32] [i32, i64])
      (x64BulkCert.bound nm) 0 :=
    (x64_bm_fnspec k₀ hc hu hfnMem).2
  have hargs : x64Target.ArgsIn (as := [i64, i64, i32, i32, i32])
      (vmCtx, fuel, a0, a1, a2, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ (.cons ⟨by decide, by simpa using hrsi⟩
      (.cons ⟨by decide, by simpa using hrdx⟩ (.cons ⟨by decide, by simpa using hrcx⟩
        (.cons ⟨by decide, by simpa using hr8⟩ .nil))))⟩
  have hspec : WasmSandboxEnvAny bulkMod nm [i64, i64, i32, i32, i32] [i32, i64]
      (vmCtx, fuel, a0, a1, a2, ()) m₀
      (WasmPost true vmCtx memBase memLen memCap fuel [] emp)
      (fun _ _ _ _ => False) :=
    ⟨fuel.toNat, ⟨nm, 2, locs, bd⟩, hwf, rfl, rfl, rfl, Nat.le_refl _, memBase, memLen, memCap,
      emp, hm₀, fun _ _ h => h⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcal, hrsp, ⟨st0, rf, ⟨⟩⟩, m', hpost, hrets, hmem'⟩
  rcases hpost with ⟨hst, hrf, memLen', hlen', hcap', hsepInv⟩
  simp only [sep_emp] at hsepInv
  rcases hrets with ⟨locsR, hlocR, hrelR⟩
  have heqR : locsR = (.gpr .rax, .gpr .rdx, ()) := by
    injection hlocR with h1; exact h1.symm
  subst heqR
  cases hrelR; rename_i hrax h1; cases h1; rename_i hrdx _
  refine ⟨hpc, hcal, hrsp, ⟨memLen', hlen', hcap', ?_⟩, st0, rf, hst, hrf,
    by simpa [BitVec.truncate] using congrArg (BitVec.setWidth 32) hrax.2,
    by simpa using hrdx.2⟩
  have hmem'' : ((cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen' ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat) ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64BulkCert.bound nm))
        (x64BulkCert.bound nm + 8) ⋆ R) st.data.dmem :=
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hsepInv)) hmem'
  exact sep_cast hmem'' (by ac_rfl)

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
  x64_bm_void3_eventually k₀ hc hu fnFill (by simp [bulkMod]) rfl
    vmCtx memBase memLen memCap fuel dst val n s ra m₀ R hrdi hrsi hrdx hrcx hr8 hsp hm₀ hmem

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
  x64_bm_void3_eventually k₀ hc hu fnCopy (by simp [bulkMod]) rfl
    vmCtx memBase memLen memCap fuel dst src n s ra m₀ R hrdi hrsi hrdx hrcx hr8 hsp hm₀ hmem

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

/-! ## 3. Logical Foundations Audit (`< 115c` Single-Line `std3`) -/

#print axioms x64_bm_legalSig
#print axioms x64_bm_fnspec
#print axioms x64_bm_host
#print axioms x64_bm_size
#print axioms x64_bm_grow
#print axioms x64_bm_fill
#print axioms x64_bm_copy
#print axioms x64_bm_oob

end LeanQbeTest.T.WasmBulkMemX64
