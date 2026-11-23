module

public import LeanQbeTest.T.WasmAuditSpec
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
open LeanQbeTest.T.WasmAuditSpec

/-! ## 1. Multi-Chunk AAPCS64 Compilation Certificate -/

compile_linked_chunks! armWasmCert
  armTarget armLayout armLegalTarget armLabelClean wasmQbeMod 1

theorem armWasmCert_chunks : armWasmCert.numChunks = 3 := rfl

theorem armWasmCert_bound_le : armWasmCert.bound "sum_mix" ≤ 2048 :=
  armWasmCert.bound_le_max "sum_mix"

theorem arm_wasm_legalSig : LegalSigAll armLegalTarget wasmQbeMod.fns := by
  intro f hf
  exact lowerModule_legalSig wasmAuditMod rfl rfl f hf

/-! ## 2. Whole-Module `FnSpec` & Kraken AArch64 `Eventually` Safety Theorems -/

/-- Arbitrary-`Host` whole-module `FnSpec` for all 3 Wasm guest functions on AArch64. -/
theorem arm_wasm_fnspec [hh : Host] (k₀ : Nat)
    (hc : armWasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ wasmQbeMod.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (WasmSandboxEnvAny wasmAuditMod f.name f.as f.rs)
        (armWasmCert.bound f.name) 0 :=
  armWasmCert.fnSpec_noExit_of_legalSigAll hh (WasmSandboxEnvAny wasmAuditMod) k₀ hc hu
    wasmQbeMod_acyclic wasmQbeMod_wf arm_wasm_legalSig wasmQbeMod_wp hf
    (fun args mem Q X X' h => wasmSandboxEnvAny_monoX f.name f.as f.rs args mem Q X X' h)

/-- Linked-host `FnSpec` for `sum_mix` on `armWasmCert.host`. -/
theorem arm_wasm_host :
    armTarget.Defined armWasmCert.host "sum_mix" ∧
      armTarget.FnSpec armWasmCert.host "sum_mix"
        (WasmSandboxEnvAny wasmAuditMod "sum_mix"
          [i64, i64, i32, i32] [i32, i64, i32])
        (armWasmCert.bound "sum_mix") 0 :=
  armWasmCert.fnSpec_host_of_legalSigAll (WasmSandboxEnvAny wasmAuditMod)
    wasmQbeMod_acyclic wasmQbeMod_wf arm_wasm_legalSig wasmQbeMod_wp
    (f := lowerFn wasmAuditMod fnSumMix) (by simp [wasmQbeMod, lowerModule, wasmAuditMod])
    (fun args mem Q X X' h =>
      wasmSandboxEnvAny_monoX "sum_mix" [i64, i64, i32, i32] [i32, i64, i32]
        args mem Q X X' h)

private theorem arm_wasm_entry_eventually [hh : Host] (k₀ : Nat)
    (hc : armWasmCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (wf : WFunc) (hwf : wf ∈ wasmAuditMod.funcs) (htidx : wf.typeIdx = 0)
    (vmCtx memBase memLen memCap fuel : BitVec 64) (a0 a1 : BitVec 32)
    (s : MachineData) (ra : Int64) (m₀ : Mem 64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = vmCtx)
    (hx1 : (s.regs.getXReg .X1).toBitVec = fuel)
    (hx2 : (s.regs.getXReg .X2).toBitVec = BitVec.setWidth 64 a0)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.setWidth 64 a1)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀)
    (hmem : s.dmem =⋆ Eq m₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound wf.name))
        (armWasmCert.bound wf.name) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap
            (region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound wf.name))
              (armWasmCert.bound wf.name) ⋆ R) st.data.dmem) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          ((st.data.regs.getXReg .X0).toBitVec).truncate 32 = status ∧
          (st.data.regs.getXReg .X1).toBitVec = remFuel ∧
          ((st.data.regs.getXReg .X2).toBitVec).truncate 32 = res)
      ⟨s, Labels.label wf.name⟩ := by
  rcases wf with ⟨nm, ti, locs, bd⟩
  dsimp only at hwf htidx hmem ⊢
  subst htidx
  have hfnMem : lowerFn wasmAuditMod ⟨nm, 0, locs, bd⟩ ∈ wasmQbeMod.fns :=
    List.mem_map.mpr ⟨⟨nm, 0, locs, bd⟩, hwf, rfl⟩
  have hfn : armTarget.FnSpec hh nm
      (WasmSandboxEnvAny wasmAuditMod nm [i64, i64, i32, i32] [i32, i64, i32])
      (armWasmCert.bound nm) 0 :=
    (arm_wasm_fnspec k₀ hc hu hfnMem).2
  have hargs : armTarget.ArgsIn (as := [i64, i64, i32, i32])
      (vmCtx, fuel, a0, a1, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hx0⟩
      (.cons ⟨by decide, by simpa [get_reg] using hx1⟩
        (.cons ⟨by decide, by simpa [get_reg] using hx2⟩
          (.cons ⟨by decide, by simpa [get_reg] using hx3⟩ .nil)))⟩
  have hspec : WasmSandboxEnvAny wasmAuditMod nm [i64, i64, i32, i32] [i32, i64, i32]
      (vmCtx, fuel, a0, a1, ()) m₀
      (WasmPost true vmCtx memBase memLen memCap fuel [.i32] emp)
      (fun _ _ _ _ => False) :=
    ⟨fuel.toNat, ⟨nm, 0, locs, bd⟩, hwf, rfl, rfl, rfl, Nat.le_refl _, memBase, memLen, memCap,
      emp, hm₀, fun _ _ h => h⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcal, hspr, ⟨st0, rf, r0, ⟨⟩⟩, m', hpost, hrets, hmem'⟩
  rcases hpost with ⟨hst, hrf, memLen', hlen', hmInv⟩
  rcases hmInv with ⟨hcap', hsepInv⟩
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
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armWasmCert.bound nm))
        (armWasmCert.bound nm) ⋆ R) st.data.dmem :=
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hsepInv)) hmem'
  exact sep_cast hmem'' (by ac_rfl)

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
  arm_wasm_entry_eventually k₀ hc hu fnSumMix (by simp [wasmAuditMod]) rfl
    vmCtx memBase memLen memCap fuel ptr len s ra m₀ R hx0 hx1 hx2 hx3 hra hsp hm₀ hmem

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
  arm_wasm_entry_eventually k₀ hc hu fnWriteHash (by simp [wasmAuditMod]) rfl
    vmCtx memBase memLen memCap fuel ptr word s ra m₀ R hx0 hx1 hx2 hx3 hra hsp hm₀ hmem

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
