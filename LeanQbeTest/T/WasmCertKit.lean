module

public import LeanQbe.T.Wasm.Safety
public import LeanQbe.T.Main
public import LeanQbe.T.MainLinkScc
public import LeanQbe.T.MainCertProof
meta import LeanQbe.T.Main
meta import LeanQbe.T.MainLinkScc

/-!
# Target-Abstract WebAssembly Certification Helpers (`WasmCertKit`)

Arch-neutral bridge (importing neither `Kraken.X64` nor `Kraken.AArch64`) factoring shared
`LinkedCert`, `WasmSandboxEnvAny`, `ArgsIn`, `RetsIn`, and `WasmMemInv` postcondition unpacking
across dual-ISA Wasm audit and bulk-memory test suites.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.WasmCertKit

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Wasm

/-! ## 1. Whole-Module `LegalSigAll` & `FnSpec` Helpers -/

theorem wasm_legalSigAll (wm : WModule) {lt : LegalTarget}
    (h32 : lt.legalTys i32 = [i32]) (h64 : lt.legalTys i64 = [i64]) :
    LegalSigAll lt (lowerModule wm).fns :=
  fun f hf => lowerModule_legalSig wm h32 h64 f hf

private theorem wasm_wp_all {wm : WModule} (hvalid : validateModule wm = true)
    (hacyc : (lowerModule wm).checkAcyclic = true) :
    ∀ f ∈ (lowerModule wm).fns, ∀ (xs : Tup Val f.as) (m : Mem 64)
      (Q : Post f.rs) (X : XPost),
      WasmSandboxEnvAny wm f.name f.as f.rs xs m Q X →
      Func.wp (WasmSandboxEnvAny wm) f.body xs m Q X := by
  have hok : ModuleOk (WasmSandboxEnvAny wm) (lowerModule wm) :=
    lowerModule_moduleOk hvalid hacyc
  intro f hf
  rcases List.mem_iff_append.mp hf with ⟨pre, post, hsp⟩
  exact (hok.fnsOk pre f post hsp).2.2

theorem wasm_fnSpec_noExit {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {maxB : Nat} {wm : WModule}
    (cert : LinkedCert T L lt hcl (lowerModule wm) [] [] 0 maxB)
    (hvalid : validateModule wm = true) (hacyc : (lowerModule wm).checkAcyclic = true)
    (hleg : LegalSigAll lt (lowerModule wm).fns)
    (h : T.mach.Host) (k₀ : Nat) (hc : cert.code.IsInfixAt (T.mach.prog h) k₀)
    (hu : T.LabelsUnique h) {f : Fn} (hf : f ∈ (lowerModule wm).fns) :
    T.Defined h f.name ∧
      T.FnSpec h f.name (WasmSandboxEnvAny wm f.name f.as f.rs) (cert.bound f.name) 0 :=
  cert.fnSpec_noExit_of_legalSigAll h (WasmSandboxEnvAny wm) k₀ hc hu
    hacyc (lowerModule_wf wm) hleg (wasm_wp_all hvalid hacyc) hf (fun _ _ _ _ _ x => x)

theorem wasm_fnSpec_host {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {maxB : Nat} {wm : WModule}
    (cert : LinkedCert T L lt hcl (lowerModule wm) [] [] 0 maxB)
    (hvalid : validateModule wm = true) (hacyc : (lowerModule wm).checkAcyclic = true)
    (hleg : LegalSigAll lt (lowerModule wm).fns)
    {wf : WFunc} (hwf : wf ∈ wm.funcs) :
    T.Defined cert.host wf.name ∧
      T.FnSpec cert.host wf.name
        (WasmSandboxEnvAny wm wf.name (lowerFn wm wf).as (lowerFn wm wf).rs)
        (cert.bound wf.name) 0 :=
  cert.fnSpec_host_of_legalSigAll (WasmSandboxEnvAny wm)
    hacyc (lowerModule_wf wm) hleg (wasm_wp_all hvalid hacyc)
    (List.mem_map.mpr ⟨wf, hwf, rfl⟩) (fun _ _ _ _ _ x => x)

theorem wasm_fnSpec_wf {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {maxB : Nat} {wm : WModule}
    (cert : LinkedCert T L lt hcl (lowerModule wm) [] [] 0 maxB)
    (hvalid : validateModule wm = true) (hacyc : (lowerModule wm).checkAcyclic = true)
    (hleg : LegalSigAll lt (lowerModule wm).fns)
    (h : T.mach.Host) (k₀ : Nat) (hc : cert.code.IsInfixAt (T.mach.prog h) k₀)
    (hu : T.LabelsUnique h) {wf : WFunc} (hwf : wf ∈ wm.funcs)
    {params results : List WValTy}
    (hparams : ((wm.types[wf.typeIdx]?).getD {}).params = params)
    (hresults : ((wm.types[wf.typeIdx]?).getD {}).results = results) :
    T.FnSpec h wf.name
      (WasmSandboxEnvAny wm wf.name
        (wasmAbiParams ⟨params, results⟩) (wasmAbiResults ⟨params, results⟩))
      (cert.bound wf.name) 0 := by
  have hfn := (wasm_fnSpec_noExit cert hvalid hacyc hleg h k₀ hc hu
    (List.mem_map.mpr ⟨wf, hwf, rfl⟩)).2
  have hftEq : (wm.types[wf.typeIdx]?).getD {} = ⟨params, results⟩ := by
    cases hft : (wm.types[wf.typeIdx]?).getD {}; simp_all
  dsimp only [lowerFn] at hfn
  rw [hftEq] at hfn
  exact hfn

/-! ## 2. Target-Abstract `ArgsIn`, `WasmSandboxEnvAny`, & `RetsIn` Unpacking -/

theorem wasm_argsIn_2 {T : Target} {s : T.mach.MData} {r0 r1 : T.Reg}
    (ha : T.toIsa.assignArgs [i64, i64] = some (.gpr r0, .gpr r1, ()))
    {v0 v1 : BitVec 64} (h0 : T.mach.getGpr s r0 = v0) (h1 : T.mach.getGpr s r1 = v1) :
    T.ArgsIn (as := [i64, i64]) (v0, v1, ()) s :=
  ⟨_, ha, .cons ⟨by decide, h0⟩ (.cons ⟨by decide, h1⟩ .nil)⟩

theorem wasm_argsIn_3 {T : Target} {s : T.mach.MData} {r0 r1 r2 : T.Reg}
    (ha : T.toIsa.assignArgs [i64, i64, i32] = some (.gpr r0, .gpr r1, .gpr r2, ()))
    {v0 v1 : BitVec 64} {v2 : BitVec 32}
    (h0 : T.mach.getGpr s r0 = v0) (h1 : T.mach.getGpr s r1 = v1)
    (h2 : T.mach.getGpr s r2 = BitVec.setWidth 64 v2) :
    T.ArgsIn (as := [i64, i64, i32]) (v0, v1, v2, ()) s :=
  ⟨_, ha, .cons ⟨by decide, h0⟩ (.cons ⟨by decide, h1⟩ (.cons ⟨by decide, h2⟩ .nil))⟩

theorem wasm_argsIn_4 {T : Target} {s : T.mach.MData} {r0 r1 r2 r3 : T.Reg}
    (ha : T.toIsa.assignArgs [i64, i64, i32, i32] =
      some (.gpr r0, .gpr r1, .gpr r2, .gpr r3, ()))
    {v0 v1 : BitVec 64} {v2 v3 : BitVec 32}
    (h0 : T.mach.getGpr s r0 = v0) (h1 : T.mach.getGpr s r1 = v1)
    (h2 : T.mach.getGpr s r2 = BitVec.setWidth 64 v2)
    (h3 : T.mach.getGpr s r3 = BitVec.setWidth 64 v3) :
    T.ArgsIn (as := [i64, i64, i32, i32]) (v0, v1, v2, v3, ()) s :=
  ⟨_, ha, .cons ⟨by decide, h0⟩ (.cons ⟨by decide, h1⟩
    (.cons ⟨by decide, h2⟩ (.cons ⟨by decide, h3⟩ .nil)))⟩

theorem wasm_argsIn_5 {T : Target} {s : T.mach.MData} {r0 r1 r2 r3 r4 : T.Reg}
    (ha : T.toIsa.assignArgs [i64, i64, i32, i32, i32] =
      some (.gpr r0, .gpr r1, .gpr r2, .gpr r3, .gpr r4, ()))
    {v0 v1 : BitVec 64} {v2 v3 v4 : BitVec 32}
    (h0 : T.mach.getGpr s r0 = v0) (h1 : T.mach.getGpr s r1 = v1)
    (h2 : T.mach.getGpr s r2 = BitVec.setWidth 64 v2)
    (h3 : T.mach.getGpr s r3 = BitVec.setWidth 64 v3)
    (h4 : T.mach.getGpr s r4 = BitVec.setWidth 64 v4) :
    T.ArgsIn (as := [i64, i64, i32, i32, i32]) (v0, v1, v2, v3, v4, ()) s :=
  ⟨_, ha, .cons ⟨by decide, h0⟩ (.cons ⟨by decide, h1⟩
    (.cons ⟨by decide, h2⟩ (.cons ⟨by decide, h3⟩ (.cons ⟨by decide, h4⟩ .nil))))⟩

theorem wasm_sandbox_spec {wm : WModule} (hhasMem : wm.memory.isSome = true)
    {wf : WFunc} (hwf : wf ∈ wm.funcs)
    {params results : List WValTy}
    (hparams : ((wm.types[wf.typeIdx]?).getD {}).params = params)
    (hresults : ((wm.types[wf.typeIdx]?).getD {}).results = results)
    (vmCtx memBase memLen memCap fuel : BitVec 64)
    (wargs : Tup Val (params.map WValTy.toTy))
    {m₀ : Mem 64} (hm₀ : WasmMemInv true vmCtx memBase memLen memCap emp m₀) :
    WasmSandboxEnvAny wm wf.name
      (wasmAbiParams ⟨params, results⟩) (wasmAbiResults ⟨params, results⟩)
      (vmCtx, fuel, wargs) m₀
      (WasmPost true vmCtx memBase memLen memCap fuel results emp)
      (fun _ _ _ _ => False) := by
  have hft : (wm.types[wf.typeIdx]?).getD {} = ⟨params, results⟩ := by
    cases h : (wm.types[wf.typeIdx]?).getD {}; simp_all
  refine ⟨fuel.toNat, wf, hwf, ?_⟩
  rw [hft]
  exact ⟨rfl, rfl, rfl, Nat.le_refl _, memBase, memLen, memCap, emp,
    by simpa [hhasMem] using hm₀, by rw [hhasMem]; exact fun _ _ x => x⟩

private theorem wasm_post_mem {vmCtx memBase memLen memCap fuel : BitVec 64}
    {resTys : List WValTy} {rets : Tup Val (wasmRetSig resTys)} {m' : Mem 64}
    {exitFrame R : Mem 64 → Prop} {dmem : Mem 64}
    (hpost : WasmPost true vmCtx memBase memLen memCap fuel resTys emp rets m')
    (hmem : dmem =⋆ Eq m' ⋆ exitFrame ⋆ R) :
    (rets.1 = 0#32 ∨ rets.1 = 1#32 ∨ rets.1 = 2#32) ∧
    rets.2.1.toNat ≤ fuel.toNat ∧
    ∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
      WasmMemInv true vmCtx memBase memLen' memCap (exitFrame ⋆ R) dmem := by
  rcases hpost with ⟨hst, hrf, memLen', hlen', hcap', hsepInv⟩
  simp only [sep_emp] at hsepInv
  have hmem' : ((cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen' ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat) ⋆
      exitFrame ⋆ R) dmem :=
    sep_mono (fun _ => sep_mono fun _ e => e ▸ hsepInv) hmem
  exact ⟨hst, hrf, memLen', hlen', hcap', sep_cast hmem' (by ac_rfl)⟩

theorem wasm_of_returns_ret1_i32 {T : Target} {State : Type}
    {step : State → (State → Prop) → Prop} {pc : State → T.mach.Addr}
    {data : State → T.mach.MData} {mem : State → Mem 64}
    {calPred spPred : State → Prop} {init : State} {ra : T.mach.Addr}
    {vmCtx memBase memLen memCap fuel : BitVec 64}
    {exitFrame R : Mem 64 → Prop} {r0 r1 r2 : T.Reg}
    (hassignRets : T.toIsa.assignRets [i32, i64, i32] = some (.gpr r0, .gpr r1, .gpr r2, ()))
    (hrun : Eventually step
      (fun st => pc st = ra ∧ calPred st ∧ spPred st ∧
        ∃ (rets : Tup Val [i32, i64, i32]) (m' : Mem 64),
          WasmPost true vmCtx memBase memLen memCap fuel [.i32] emp rets m' ∧
          T.RetsIn rets (data st) ∧ (mem st =⋆ Eq m' ⋆ exitFrame ⋆ R))
      init) :
    Eventually step
      (fun st => pc st = ra ∧ calPred st ∧ spPred st ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap (exitFrame ⋆ R) (mem st)) ∧
        ∃ (status res : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (T.mach.getGpr (data st) r0).truncate 32 = status ∧
          T.mach.getGpr (data st) r1 = remFuel ∧
          (T.mach.getGpr (data st) r2).truncate 32 = res)
      init := by
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, hcal, hsp, ⟨st0, rf, r0v, ⟨⟩⟩, m', hpost, ⟨locsR, hlocR, hrelR⟩, hmem'⟩
  obtain ⟨hst, hrf, hdmem⟩ := wasm_post_mem hpost hmem'
  rw [hassignRets] at hlocR
  injection hlocR with h1; subst h1
  cases hrelR; rename_i hr0 h1; cases h1; rename_i hr1 h2; cases h2; rename_i hr2 _
  exact ⟨hpc, hcal, hsp, hdmem, st0, r0v, rf, hst, hrf,
    by simpa [BitVec.truncate] using congrArg (BitVec.setWidth 32) hr0.2,
    by simpa using hr1.2,
    by simpa [BitVec.truncate] using congrArg (BitVec.setWidth 32) hr2.2⟩

theorem wasm_of_returns_void {T : Target} {State : Type}
    {step : State → (State → Prop) → Prop} {pc : State → T.mach.Addr}
    {data : State → T.mach.MData} {mem : State → Mem 64}
    {calPred spPred : State → Prop} {init : State} {ra : T.mach.Addr}
    {vmCtx memBase memLen memCap fuel : BitVec 64}
    {exitFrame R : Mem 64 → Prop} {r0 r1 : T.Reg}
    (hassignRets : T.toIsa.assignRets [i32, i64] = some (.gpr r0, .gpr r1, ()))
    (hrun : Eventually step
      (fun st => pc st = ra ∧ calPred st ∧ spPred st ∧
        ∃ (rets : Tup Val [i32, i64]) (m' : Mem 64),
          WasmPost true vmCtx memBase memLen memCap fuel [] emp rets m' ∧
          T.RetsIn rets (data st) ∧ (mem st =⋆ Eq m' ⋆ exitFrame ⋆ R))
      init) :
    Eventually step
      (fun st => pc st = ra ∧ calPred st ∧ spPred st ∧
        (∃ memLen', memLen.toNat ≤ memLen'.toNat ∧
          WasmMemInv true vmCtx memBase memLen' memCap (exitFrame ⋆ R) (mem st)) ∧
        ∃ (status : BitVec 32) (remFuel : BitVec 64),
          (status = 0#32 ∨ status = 1#32 ∨ status = 2#32) ∧
          remFuel.toNat ≤ fuel.toNat ∧
          (T.mach.getGpr (data st) r0).truncate 32 = status ∧
          T.mach.getGpr (data st) r1 = remFuel)
      init := by
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, hcal, hsp, ⟨st0, rf, ⟨⟩⟩, m', hpost, ⟨locsR, hlocR, hrelR⟩, hmem'⟩
  obtain ⟨hst, hrf, hdmem⟩ := wasm_post_mem hpost hmem'
  rw [hassignRets] at hlocR
  injection hlocR with h1; subst h1
  cases hrelR; rename_i hr0 h1; cases h1; rename_i hr1 _
  exact ⟨hpc, hcal, hsp, hdmem, st0, rf, hst, hrf,
    by simpa [BitVec.truncate] using congrArg (BitVec.setWidth 32) hr0.2,
    by simpa using hr1.2⟩

/-! ## 3. Shared Target-Neutral Test ISA & Compile Drivers -/

/-- Pure target-neutral GPR ISA configuration supporting all 64-bit scalar operations. -/
@[expose] def wasmTestGpr : GprIsa Nat Empty Nat Unit :=
  { condReads := fun _ => 0#8, negCond := fun c => c, zeroFlags := [], clearFlags := [],
    mov := fun _ _ => [()], movi := fun _ _ => [()], setcc := fun _ _ => [()],
    jmp := fun _ => [()], jcc := fun _ _ => [()], jnzGpr := fun _ _ => ([()], 0#8),
    op := fun _ _ _ _ => some ([()], 0#8), load := fun _ _ _ => some ([()], 0#8),
    store := fun _ _ _ => some ([()], 0#8),
    supportsScalarOp := defaultSupportsScalarOp [8, 16, 32, 64] true true true }

/-- Pure target-neutral Frame ISA configuration with 8 arg/return registers. -/
@[expose] def wasmTestFrame : FrameIsa Nat Unit :=
  { label := fun _ => (), sp := 100, scratch := [10, 11],
    allocatable := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], calleeSaved := [8, 9], raRegs := [],
    argRegs := [0, 1, 2, 3, 4, 5, 6, 7], retRegs := [0, 1, 2, 3, 4, 5, 6, 7], raBytes := 8,
    frameSize := fun n => n * 8, prologue := fun _ => ([()], 0#8),
    epilogue := fun _ => ([()], 0#8), slotSt := fun _ _ => [()], slotLd := fun _ _ => [()],
    canonAbi := fun _ _ => ([()], 0#8), call := fun _ => [()],
    exitJmp := fun _ => [()], ret := [()] }

/-- Target-neutral `Isa` for verified end-to-end compilation tests across legal targets. -/
@[expose] def wasmTestIsa : Isa :=
  { Reg := Nat, VReg := Empty, Cond := Nat, Directive := Unit,
    gpr := wasmTestGpr, vec := VecIsa.empty Nat Nat Unit, frame := wasmTestFrame }

/-- Check acyclic compilation of `qm` against `lt` on `wasmTestIsa`. -/
@[expose] def wasmCheckCompile (lt : LegalTarget) (qm : Module) : Bool :=
  let hints : List wasmTestIsa.Hints := qm.fns.map (Fn.computeHints wasmTestIsa lt)
  (compileModule wasmTestIsa lt wasmTestIsa.frame.raBytes [] [] 0 qm.fns hints).isOk

open LeanQbe.T.LinkScc in
/-- Check that `qm` compiles under `compileModuleBudgetRec` for cyclic/recursive code. -/
@[expose] def wasmCheckBudgetRecCompile
    (lt : LegalTarget) (qm : Module) (maxBound : Nat := 4096) : Bool :=
  let bfs : List BudgetFn := qm.fns.map fun f => ⟨f, 1024, 2048⟩
  let hints : List wasmTestIsa.Hints := qm.fns.map (Fn.computeHints wasmTestIsa lt)
  (compileModuleBudgetRec wasmTestIsa lt wasmTestIsa.frame.raBytes [] [] 0
    maxBound bfs hints).isOk

end LeanQbeTest.T.WasmCertKit
