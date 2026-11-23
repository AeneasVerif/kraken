module

public import LeanQbeTest.T.WasmBulkMemTest
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainCertElab
public meta import LeanQbeTest.T.WasmBulkMemTest
public meta import LeanQbe.T.Arm64.TargLemmas
public meta import LeanQbe.T.MainCertElab
public meta import Kraken.AArch64.Syntax

/-!
# Kraken AArch64 WebAssembly Bulk-Memory & Growth Certificate (`WasmBulkMemArm64`)

Compiles the real clang-compiled WebAssembly guest module `bulkQbe` (`test_mem_size`,
`test_mem_grow`, `test_mem_fill`, `test_mem_copy`) across 4 linked chunks (`chunkSize := 1`)
onto AAPCS64 AArch64 (`armTarget`) via `compile_linked_chunks!` and proves end-to-end Kraken
AArch64 `Eventually (step1 Host.exe)` soundness and host-frame preservation for both valid and
adversarial OOB wraparound calls.

This module imports ONLY `Kraken.AArch64` (`LeanQbe.T.Arm64.*`), never `Kraken.X64`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.WasmBulkMemArm64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.Arm64 Kraken
open LeanQbeTest.T.WasmBulkMemTest

/-! ## 1. Multi-Chunk AAPCS64 Compilation Certificate -/

compile_linked_chunks! armBulkCert
  armTarget armLayout armLegalTarget armLabelClean bulkQbe 1

theorem arm_bm_chunks : armBulkCert.numChunks = 4 := rfl

theorem arm_bm_bound : armBulkCert.bound "test_mem_copy" ≤ 2048 :=
  armBulkCert.bound_le_max "test_mem_copy"

theorem arm_bm_legalSig : LegalSigAll armLegalTarget bulkQbe.fns := by
  intro f hf
  exact lowerModule_legalSig bulkMod rfl rfl f hf

/-! ## 2. Whole-Module `FnSpec` & Kraken AArch64 `Eventually` Soundness -/

/-- Arbitrary-`Host` whole-module `FnSpec` for all 4 Wasm bulk-memory functions on AArch64. -/
theorem arm_bm_fnspec [hh : Host] (k₀ : Nat)
    (hc : armBulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ bulkQbe.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (WasmSandboxEnvAny bulkMod f.name f.as f.rs)
        (armBulkCert.bound f.name) 0 :=
  armBulkCert.fnSpec_noExit_of_legalSigAll hh (WasmSandboxEnvAny bulkMod) k₀ hc hu
    bm_acyclic bm_wf arm_bm_legalSig bm_wp hf
    (fun args mem Q X X' h => bm_any_monoX f.name f.as f.rs args mem Q X X' h)

/-- Linked-host `FnSpec` for `test_mem_copy` on `armBulkCert.host`. -/
theorem arm_bm_host :
    armTarget.Defined armBulkCert.host "test_mem_copy" ∧
      armTarget.FnSpec armBulkCert.host "test_mem_copy"
        (WasmSandboxEnvAny bulkMod "test_mem_copy"
          [i64, i64, i32, i32, i32] [i32, i64])
        (armBulkCert.bound "test_mem_copy") 0 :=
  armBulkCert.fnSpec_host_of_legalSigAll (WasmSandboxEnvAny bulkMod)
    bm_acyclic bm_wf arm_bm_legalSig bm_wp bm_fn_copy_qbe
    (fun args mem Q X X' h =>
      bm_any_monoX "test_mem_copy" [i64, i64, i32, i32, i32] [i32, i64]
        args mem Q X X' h)

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
      ⟨s, Labels.label "test_mem_size"⟩ := by
  have hfn : armTarget.FnSpec hh "test_mem_size"
      (WasmSandboxEnvAny bulkMod "test_mem_size" [i64, i64] [i32, i64, i32])
      (armBulkCert.bound "test_mem_size") 0 :=
    (arm_bm_fnspec k₀ hc hu bm_fn_size_qbe).2
  have hargs : armTarget.ArgsIn (as := [i64, i64]) (vmCtx, fuel, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hx0⟩
      (.cons ⟨by decide, by simpa [get_reg] using hx1⟩ .nil)⟩
  have hspec : WasmSandboxEnvAny bulkMod "test_mem_size" [i64, i64] [i32, i64, i32]
      (vmCtx, fuel, ()) m₀ (WasmPost true vmCtx memBase memLen memCap fuel [.i32] emp)
      (fun _ _ _ _ => False) :=
    ⟨fuel.toNat, fnSize, by simp [bulkMod], rfl, rfl, rfl, Nat.le_refl _,
      memBase, memLen, memCap, emp, hm₀, fun _ _ h => h⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcal, hspr, ⟨st0, rf, r0, ⟨⟩⟩, m', hpost, hrets, hmem'⟩
  rcases hpost with ⟨hst, hrf, memLen', hlen', hcap', hsepInv⟩
  simp only [sep_emp] at hsepInv
  rcases hrets with ⟨locsR, hlocR, hrelR⟩
  have heqR : locsR = (.gpr (.reg .X0), .gpr (.reg .X1), .gpr (.reg .X2), ()) := by
    injection hlocR with h1; exact h1.symm
  subst heqR
  cases hrelR; rename_i hx0' h1; cases h1; rename_i hx1' h2; cases h2; rename_i hx2' _
  refine ⟨hpc, hcal, hspr, ⟨memLen', hlen', hcap', ?_⟩, st0, r0, rf, hst, hrf,
    by simpa [get_reg, BitVec.truncate] using congrArg (BitVec.setWidth 32) hx0'.2,
    by simpa [get_reg] using hx1'.2,
    by simpa [get_reg, BitVec.truncate] using congrArg (BitVec.setWidth 32) hx2'.2⟩
  have hmem'' : ((cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen' ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_size"))
        (armBulkCert.bound "test_mem_size") ⋆ R) st.data.dmem :=
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hsepInv)) hmem'
  exact sep_cast hmem'' (by ac_rfl)

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
      ⟨s, Labels.label "test_mem_grow"⟩ := by
  have hfn : armTarget.FnSpec hh "test_mem_grow"
      (WasmSandboxEnvAny bulkMod "test_mem_grow" [i64, i64, i32] [i32, i64, i32])
      (armBulkCert.bound "test_mem_grow") 0 :=
    (arm_bm_fnspec k₀ hc hu bm_fn_grow_qbe).2
  have hargs : armTarget.ArgsIn (as := [i64, i64, i32]) (vmCtx, fuel, delta, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hx0⟩
      (.cons ⟨by decide, by simpa [get_reg] using hx1⟩
        (.cons ⟨by decide, by simpa [get_reg] using hx2⟩ .nil))⟩
  have hspec : WasmSandboxEnvAny bulkMod "test_mem_grow" [i64, i64, i32] [i32, i64, i32]
      (vmCtx, fuel, delta, ()) m₀ (WasmPost true vmCtx memBase memLen memCap fuel [.i32] emp)
      (fun _ _ _ _ => False) :=
    ⟨fuel.toNat, fnGrow, by simp [bulkMod], rfl, rfl, rfl, Nat.le_refl _,
      memBase, memLen, memCap, emp, hm₀, fun _ _ h => h⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcal, hspr, ⟨st0, rf, r0, ⟨⟩⟩, m', hpost, hrets, hmem'⟩
  rcases hpost with ⟨hst, hrf, memLen', hlen', hcap', hsepInv⟩
  simp only [sep_emp] at hsepInv
  rcases hrets with ⟨locsR, hlocR, hrelR⟩
  have heqR : locsR = (.gpr (.reg .X0), .gpr (.reg .X1), .gpr (.reg .X2), ()) := by
    injection hlocR with h1; exact h1.symm
  subst heqR
  cases hrelR; rename_i hx0' h1; cases h1; rename_i hx1' h2; cases h2; rename_i hx2' _
  refine ⟨hpc, hcal, hspr, ⟨memLen', hlen', hcap', ?_⟩, st0, r0, rf, hst, hrf,
    by simpa [get_reg, BitVec.truncate] using congrArg (BitVec.setWidth 32) hx0'.2,
    by simpa [get_reg] using hx1'.2,
    by simpa [get_reg, BitVec.truncate] using congrArg (BitVec.setWidth 32) hx2'.2⟩
  have hmem'' : ((cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen' ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound "test_mem_grow"))
        (armBulkCert.bound "test_mem_grow") ⋆ R) st.data.dmem :=
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hsepInv)) hmem'
  exact sep_cast hmem'' (by ac_rfl)

private theorem arm_bm_void3_eventually [hh : Host] (k₀ : Nat)
    (hc : armBulkCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (wf : WFunc) (hwf : wf ∈ bulkMod.funcs) (htidx : wf.typeIdx = 2)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (a0 a1 a2 : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 a0)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.setWidth 64 a1)
    (hx4 : (s.regs.getXReg .X4).toBitVec = BitVec.setWidth 64 a2)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound wf.name))
        (armBulkCert.bound wf.name) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound wf.name))
              (armBulkCert.bound wf.name) ⋆ R) st.data.dmem) ∧
        ∃ (status : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status ∧
          (st.data.regs.getXReg .X1).toBitVec = remFuel)
      ⟨s, Labels.label wf.name⟩ := by
  rcases wf with ⟨nm, ti, locs, bd⟩
  dsimp only at hwf htidx hmem ⊢
  subst htidx
  have hfnMem : lowerFn bulkMod ⟨nm, 2, locs, bd⟩ ∈ bulkQbe.fns :=
    List.mem_map.mpr ⟨⟨nm, 2, locs, bd⟩, hwf, rfl⟩
  have hfn : armTarget.FnSpec hh nm
      (WasmSandboxEnvAny bulkMod nm [i64, i64, i32, i32, i32] [i32, i64])
      (armBulkCert.bound nm) 0 :=
    (arm_bm_fnspec k₀ hc hu hfnMem).2
  have hargs : armTarget.ArgsIn (as := [i64, i64, i32, i32, i32])
      (vmCtx, fuel, a0, a1, a2, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hx0⟩
      (.cons ⟨by decide, by simpa [get_reg] using hx1⟩
        (.cons ⟨by decide, by simpa [get_reg] using hx2⟩
          (.cons ⟨by decide, by simpa [get_reg] using hx3⟩
            (.cons ⟨by decide, by simpa [get_reg] using hx4⟩ .nil))))⟩
  have hspec : WasmSandboxEnvAny bulkMod nm [i64, i64, i32, i32, i32] [i32, i64]
      (vmCtx, fuel, a0, a1, a2, ()) m₀
      (WasmPost true vmCtx memBase memLen memCap fuel [] emp)
      (fun _ _ _ _ => False) :=
    ⟨fuel.toNat, ⟨nm, 2, locs, bd⟩, hwf, rfl, rfl, rfl, Nat.le_refl _, memBase, memLen, memCap,
      emp, hm₀, fun _ _ h => h⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcal, hspr, ⟨st0, rf, ⟨⟩⟩, m', hpost, hrets, hmem'⟩
  rcases hpost with ⟨hst, hrf, memLen', hlen', hcap', hsepInv⟩
  simp only [sep_emp] at hsepInv
  rcases hrets with ⟨locsR, hlocR, hrelR⟩
  have heqR : locsR = (.gpr (.reg .X0), .gpr (.reg .X1), ()) := by
    injection hlocR with h1; exact h1.symm
  subst heqR
  cases hrelR; rename_i hx0' h1; cases h1; rename_i hx1' _
  refine ⟨hpc, hcal, hspr, ⟨memLen', hlen', hcap', ?_⟩, st0, rf, hst, hrf,
    by simpa [get_reg, BitVec.truncate] using congrArg (BitVec.setWidth 32) hx0'.2,
    by simpa [get_reg] using hx1'.2⟩
  have hmem'' : ((cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen' ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armBulkCert.bound nm))
        (armBulkCert.bound nm) ⋆ R) st.data.dmem :=
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hsepInv)) hmem'
  exact sep_cast hmem'' (by ac_rfl)

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
  arm_bm_void3_eventually k₀ hc hu fnFill (by simp [bulkMod]) rfl
    vmCtx memBase memLen memCap fuel dst val n s ra m₀ R hx0 hx1 hx2 hx3 hx4 hra hsp hm₀ hmem

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
  arm_bm_void3_eventually k₀ hc hu fnCopy (by simp [bulkMod]) rfl
    vmCtx memBase memLen memCap fuel dst src n s ra m₀ R hx0 hx1 hx2 hx3 hx4 hra hsp hm₀ hmem

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

/-! ## 3. Logical Foundations Audit (`< 115c` Single-Line `std3`) -/

#print axioms arm_bm_legalSig
#print axioms arm_bm_fnspec
#print axioms arm_bm_host
#print axioms arm_bm_size
#print axioms arm_bm_grow
#print axioms arm_bm_fill
#print axioms arm_bm_copy
#print axioms arm_bm_oob

end LeanQbeTest.T.WasmBulkMemArm64
