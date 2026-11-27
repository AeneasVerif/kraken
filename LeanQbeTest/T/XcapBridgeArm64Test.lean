module

public import LeanQbe.T.Xcap.Bridge
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainSplice
public import LeanQbe.T.MainLinkSplice
public import LeanQbe.T.Logic.ProofKit
public import LeanQbeTest.T.XcapBridgeTest
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.MemLemmas
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbeTest.T.XcapBridgeTest

/-!
# Concrete AAPCS64 Arm64 Dual-Direction `Xcap.Bridge` Test (`XcapBridgeArm64Test`)

Exercises `LeanQbe.T.Xcap.Bridge` end-to-end on `armTarget` (`armLegalTarget`, `armLayout`,
`armLabelClean`, `armInit`):

1. `armAddrCodec : AddrCodec armTarget` (`Int64.toBitVec` / `Int64.ofBitVec` + `BitVec.ofNat 64`
   round-trip).
2. **Direction 1 (`Compiled` / `LinkedCert` → `T.FnSpec` → `Xcap.cptr`):** compiles `selfMod`
   (`add_ten`, `double_add_ten`), lifts `double_add_ten` to `Xcap.cptr` via
   `linkedCert_host_to_cptr_src` & `fnSpec_to_cptr`, and executes `double_add_ten(7) = 34` via
   `run_i64_of_cptr` on `armInit`.
3. **Direction 2 (Opaque Arm64 `add x0, x0, #1; ret` XCAP block → `cptr_to_Γ` /
   `cptr_specTable_to_extCallees` → `Compiled` / `LinkedCert` caller → `Xcap.cptr`):** links a
   hand-assembled Arm64 `"opaque_inc"` block with compiled `"call_opaque"` in one concrete Kraken
   AArch64 `Host`, feeds `opaqueInc_xcap_cptr` into `compiled_ofTable_cptr_src` and
   `linkedCert_ofTable_cptr_src`, and executes `call_opaque(20) = 41` in `x0`.
4. `check_std_axioms!` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.XcapBridgeArm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Xcap LeanQbe.T.ProofKit Kraken
open LeanQbeTest.T.XcapBridgeTest

/-! ## 1. `AddrCodec armTarget` & `BitVec 64` / `Int64` Round-Trips -/

/-- Canonical injective `AddrCodec` for `armTarget` (`armMach.Addr = Int64`). -/
@[expose] def armAddrCodec : AddrCodec armTarget where
  toBits := Int64.toBitVec
  ofBits := Int64.ofBitVec
  of_to := Int64.ofBitVec_toBitVec

theorem armAddrCodec_to_of (bv : BitVec 64) :
    armAddrCodec.toBits (armAddrCodec.ofBits bv) = bv :=
  Int64.toBitVec_ofBitVec bv

theorem armAddrCodec_ofNat_roundtrip (n : Nat) :
    armAddrCodec.toBits (armAddrCodec.ofBits (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n :=
  armAddrCodec_to_of (BitVec.ofNat 64 n)

/-! ## 2. Direction 1: `LinkedCert` / `Compiled` → `T.FnSpec` → `Xcap.cptr` on Arm64 -/

compile_linked_chunks! armSelfCert
  armTarget armLayout armLegalTarget armLabelClean selfMod 2

/-- Direction 1 (`LinkedCert` → `Xcap.cptr`): `"double_add_ten"` compiled in `armSelfCert` exports
an XCAP `cptr` for every `TargetClosed` machine spec `Ψ`. -/
theorem armSelf_doubleAddTen_cptr {Ψ : CodeSpec armTarget.mach.MData}
    {H : armTarget.mach.State → Prop}
    (hcl : TargetClosed armTarget armAddrCodec armSelfCert.host Ψ H) :
    armTarget.Defined armSelfCert.host "double_add_ten" ∧
      cptr Ψ (armAddrCodec.toBits (armTarget.mach.labelAddr armSelfCert.host "double_add_ten"))
        (targetCallPre armTarget armAddrCodec armSelfCert.host
          (Env.ofTable selfTbl "double_add_ten" [i64] [i64])
          (armSelfCert.bound "double_add_ten") 0 Ψ) :=
  linkedCert_host_to_cptr_src armAddrCodec armSelfCert (Env.ofTable selfTbl)
    selfMod_acyclic selfMod_moduleOk (f := fnDoubleAddTen)
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl rfl
    (Env.ofTable_noExit selfTbl_noExit "double_add_ten" [i64] [i64]) hcl

/-- Concrete Kraken Arm64 execution driven directly through Seam 1's `Xcap.cptr`:
`double_add_ten(7) = 34#64` in `x0` at return address `0x1234`. -/
theorem armSelf_doubleAddTen_run_via_cptr :
    Eventually (armTarget.mach.step armSelfCert.host)
      (fun st => st.pc = 0x1234 ∧ get st.data (.reg .X0) = 34#64)
      (armTarget.mach.mkState
        (armInit.initState (as := [i64]) (armSelfCert.bound "double_add_ten") [] (7#64, ()))
        (armTarget.mach.labelAddr armSelfCert.host "double_add_ten")) := by
  have hcptr := (armSelf_doubleAddTen_cptr
    (TargetSafe.closed armTarget armAddrCodec armSelfCert.host
      (fun st => st.pc = 0x1234 ∧ get st.data (.reg .X0) = 34#64))).2
  refine run_i64_of_cptr armAddrCodec armInit hcptr [] (7#64, ())
    (armSelfCert.bound_le_max "double_add_ten") (by decide) rfl
    (Q := fun rets _ => rets = (34#64, ())) ?_ (fun _ _ h => h)
  exact Or.inr ⟨(fun h => absurd h.1 (by decide)), Or.inl ⟨⟨rfl, rfl, rfl⟩, rfl⟩⟩

/-! ## 3. Direction 2: Opaque Arm64 XCAP Block → `cptr_to_Γ` → Compiled Caller → `Xcap.cptr` -/

/-- Hand-assembled Arm64 opaque callee body (`add x0, x0, #1`). -/
@[expose] def armOpaqueIncBody : List Directive :=
  (armTarget.gpr.op (.add i64) (.gpr (.reg .X0), .imm 1#64, ()) (.gpr (.reg .X0), ()) .default
    |>.map Prod.fst).getD []

theorem armOpaqueIncBody_op :
    armTarget.gpr.op (.add i64) (.gpr (.reg .X0), .imm 1#64, ()) (.gpr (.reg .X0), ()) .default =
      some (armOpaqueIncBody, maskNone) :=
  rfl

@[expose] def armOpaqueIncCode : List Directive :=
  opaqueIncCode armTarget armOpaqueIncBody

splice_module_hints armCallerHints armTarget.toIsa armLegalTarget callerFns

splice_chunk_literals armCallerCode armCallerBounds armCallerSigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  opaqueExtCallees [] 0 callerFns armCallerHints

theorem armCaller_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      (extCalleesOfTable armLegalTarget opaqueExtRows) [] 0 callerFns armCallerHints =
      .ok (armCallerCode, armCallerBounds) := by
  t_kernel_rfl

theorem armCaller_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      armCallerCode armCallerBounds (callerFns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

@[expose] def armCallerCompiled :
    Compiled armTarget armLegalTarget (extCalleesOfTable armLegalTarget opaqueExtRows)
      [] 0 callerFns armCallerHints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    (extCalleesOfTable armLegalTarget opaqueExtRows) [] 0
    callerFns armCallerHints 2048 armCallerCode armCallerBounds armCaller_cm armCaller_meta

@[expose] def armCallerChunk :
    CompiledChunk armTarget armLegalTarget [] 0 :=
  ⟨extCalleesOfTable armLegalTarget opaqueExtRows, callerFns, armCallerHints, 2048,
    armCallerCompiled⟩

theorem armCallerCert_linkCheck :
    checkLinkList armLayout (extCalleesOfTable armLegalTarget opaqueExtRows) [armCallerChunk] =
      true := by
  t_kernel_rfl

@[expose] def armCallerCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean callerMod
      (extCalleesOfTable armLegalTarget opaqueExtRows) [] 0 2048 where
  chunks := [armCallerChunk]
  linkCheck := armCallerCert_linkCheck
  fns_eq := rfl
  supportsAll := armCallerCompiled.supportsSource
  maxBound_le := Nat.le_refl 2048

/-- Combined Kraken Arm64 program: opaque `"opaque_inc"` + compiled `"call_opaque"`. -/
@[expose] def armCombinedProg : List Directive :=
  armOpaqueIncCode ++ armCallerCode

theorem armCombinedProg_small : armLayout.progSmall armCombinedProg = true := by t_kernel_rfl
theorem armCombinedProg_nodup : armLayout.labelsNodup armCombinedProg = true := by t_kernel_rfl

/-- Concrete Kraken Arm64 `Host` laying out both the opaque XCAP block and compiled caller. -/
@[expose, instance_reducible] def armCombinedHost : armTarget.mach.Host :=
  armLayout.layoutOf armCombinedProg armCombinedProg_small

theorem armCombinedHost_labelsUnique : armTarget.LabelsUnique armCombinedHost :=
  armLayout.labelsUnique_layoutOf armCombinedProg_small armCombinedProg_nodup

theorem armOpaqueInc_infix :
    armOpaqueIncCode.IsInfixAt (armTarget.mach.prog armCombinedHost) 0 :=
  ⟨armCallerCode, rfl⟩

theorem armCaller_infix :
    armCallerCompiled.code.IsInfixAt (armTarget.mach.prog armCombinedHost)
      armOpaqueIncCode.length := by
  have h : (armOpaqueIncCode ++ armCallerCode).IsInfixAt
      (armTarget.mach.prog armCombinedHost) 0 :=
    ⟨[], List.append_nil _⟩
  simpa [armCallerCompiled, compileCheckedLit, Nat.zero_add] using (List.IsInfixAt.append h).2

/-- Pure XCAP `cptr` proof for the hand-assembled Arm64 `"opaque_inc"` block in
`armCombinedHost`. -/
theorem armOpaqueInc_cptr {Ψ : CodeSpec armTarget.mach.MData} {H : armTarget.mach.State → Prop}
    (hcl : TargetClosed armTarget armAddrCodec armCombinedHost Ψ H) :
    cptr Ψ (armAddrCodec.toBits (armTarget.mach.labelAddr armCombinedHost "opaque_inc"))
      (targetCallPre armTarget armAddrCodec armCombinedHost opaqueIncRow.eff 0 0 Ψ) :=
  opaqueInc_xcap_cptr armAddrCodec (arg0 := .reg .X0) (ret0 := .reg .X0) (vh := .default)
    rfl rfl (by simp [armScratch]) (by simp [armScratch])
    (by decide) (by simp) (by simp) (by decide)
    armOpaqueIncBody_op armOpaqueInc_infix armCombinedHost_labelsUnique hcl

theorem armExtTableOk :
    XcapExtTableOk armAddrCodec armLegalTarget armCombinedHost callerMod callerTbl 0
      opaqueExtRows where
  tbl_nodup := callerTbl_nodup
  tbl_noExit := callerTbl_noExit
  sub r hr := by simp only [opaqueExtRows, List.mem_singleton] at hr; subst hr; simp [callerTbl]
  sigs r hr := by
    simp only [opaqueExtRows, List.mem_singleton] at hr; subst hr
    simp [callerMod, Module.sigs, Extern.sig, opaqueIncRow]
  legal r hr := by
    simp only [opaqueExtRows, List.mem_singleton] at hr; subst hr; exact ⟨rfl, rfl⟩
  ext_nodup := by decide
  ext_disj r hr := by
    simp only [opaqueExtRows, List.mem_singleton] at hr; subst hr
    simp [callerMod, callerFns, fnCallOpaque, opaqueIncRow]
  cptrs r hr H := by
    simp only [opaqueExtRows, List.mem_singleton] at hr; subst hr
    exact armOpaqueInc_cptr (TargetSafe.closed armTarget armAddrCodec armCombinedHost H)

/-- Direction 2 (`cptr_to_Γ` + `cptr_specTable_to_extCallees` + `Env.ofTable_moduleOk` →
`Compiled` caller `"call_opaque"` → `T.FnSpec` on `armCombinedHost`). -/
theorem armCaller_fnSpec_via_xcap :
    armTarget.Defined armCombinedHost "call_opaque" ∧
      armTarget.FnSpec armCombinedHost "call_opaque"
        (Env.ofTable callerTbl "call_opaque" [i64] [i64])
        (armCallerCompiled.bound "call_opaque") 0 :=
  compiled_ofTable_fnSpec_src armAddrCodec armCallerCompiled callerMod rfl callerTbl
    armCombinedHost armOpaqueIncCode.length armCaller_infix armCombinedHost_labelsUnique
    callerMod_acyclic callerMod_allWf callerTbl_impl armExtTableOk
    (fun _ hx => nomatch hx) (f := fnCallOpaque) List.mem_cons_self rfl rfl

/-- Full round-trip on `LinkedCert` (`armCallerCert`): opaque Arm64 XCAP callee → `cptr_to_Γ` →
compiled `"call_opaque"` → `fnSpec_to_cptr` → XCAP `cptr` on `armCombinedHost`. -/
theorem armCallerCert_cptr_roundtrip {Ψ : CodeSpec armTarget.mach.MData}
    {H : armTarget.mach.State → Prop}
    (hcl : TargetClosed armTarget armAddrCodec armCombinedHost Ψ H) :
    armTarget.Defined armCombinedHost "call_opaque" ∧
      cptr Ψ (armAddrCodec.toBits (armTarget.mach.labelAddr armCombinedHost "call_opaque"))
        (targetCallPre armTarget armAddrCodec armCombinedHost
          (Env.ofTable callerTbl "call_opaque" [i64] [i64])
          (armCallerCert.bound "call_opaque") 0 Ψ) :=
  linkedCert_ofTable_cptr_src armAddrCodec armCallerCert callerTbl
    armCombinedHost armOpaqueIncCode.length
    (by simpa [LinkedCert.code, LinkedCert.compiled, linkCompiledList, chunksCode,
      armCallerCert, armCallerChunk] using armCaller_infix)
    armCombinedHost_labelsUnique callerMod_acyclic callerMod_allWf callerTbl_impl armExtTableOk
    (fun _ hx => nomatch hx) (f := fnCallOpaque) List.mem_cons_self rfl rfl hcl

/-- Closed concrete Kraken Arm64 execution of compiled `"call_opaque"` calling hand-assembled XCAP
`"opaque_inc"`: `call_opaque(20) = (20 + 1) + 20 = 41#64` in `x0`. -/
theorem armCaller_run_via_cptr :
    Eventually (armTarget.mach.step armCombinedHost)
      (fun st => st.pc = 0x1234 ∧ get st.data (.reg .X0) = 41#64)
      (armTarget.mach.mkState
        (armInit.initState (as := [i64]) (armCallerCert.bound "call_opaque") [] (20#64, ()))
        (armTarget.mach.labelAddr armCombinedHost "call_opaque")) := by
  have hcptr := (armCallerCert_cptr_roundtrip
    (TargetSafe.closed armTarget armAddrCodec armCombinedHost
      (fun st => st.pc = 0x1234 ∧ get st.data (.reg .X0) = 41#64))).2
  refine run_i64_of_cptr armAddrCodec armInit hcptr [] (20#64, ())
    (armCallerCert.bound_le_max "call_opaque") (by decide) rfl
    (Q := fun rets _ => rets = (41#64, ())) ?_ (fun _ _ h => h)
  exact Or.inl ⟨⟨rfl, rfl, rfl⟩, rfl⟩

check_std_axioms!
  LeanQbeTest.T.XcapBridgeArm64Test.armAddrCodec_to_of
  LeanQbeTest.T.XcapBridgeArm64Test.armAddrCodec_ofNat_roundtrip
  LeanQbeTest.T.XcapBridgeArm64Test.armSelf_doubleAddTen_cptr
  LeanQbeTest.T.XcapBridgeArm64Test.armSelf_doubleAddTen_run_via_cptr
  LeanQbeTest.T.XcapBridgeArm64Test.armOpaqueInc_cptr
  LeanQbeTest.T.XcapBridgeArm64Test.armCaller_fnSpec_via_xcap
  LeanQbeTest.T.XcapBridgeArm64Test.armCallerCert_cptr_roundtrip
  LeanQbeTest.T.XcapBridgeArm64Test.armCaller_run_via_cptr

end LeanQbeTest.T.XcapBridgeArm64Test
