module

public import LeanQbe.T.Xcap.Bridge
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainSplice
public import LeanQbe.T.MainLinkSplice
public import LeanQbe.T.Logic.ProofKit
public import LeanQbeTest.T.XcapBridgeTest
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbeTest.T.XcapBridgeTest

/-!
# Concrete SysV x86-64 Dual-Direction `Xcap.Bridge` Test (`XcapBridgeX64Test`)

Exercises `LeanQbe.T.Xcap.Bridge` end-to-end on `x64Target` (`x64LegalTarget`, `x64Layout`,
`x64LabelClean`, `x64Init`):

1. `x64AddrCodec : AddrCodec x64Target` (`Int64.toBitVec` / `Int64.ofBitVec` + `BitVec.ofNat 64`
   round-trip).
2. **Direction 1 (`Compiled` / `LinkedCert` → `T.FnSpec` → `Xcap.cptr`):** compiles `selfMod`
   (`add_ten`, `double_add_ten`), lifts `double_add_ten` to `Xcap.cptr` via
   `linkedCert_host_to_cptr_src` & `fnSpec_to_cptr`, and executes `double_add_ten(7) = 34` via
   `run_i64_of_cptr` on `x64Init`.
3. **Direction 2 (Opaque x64 `lea rax, [rdi + 1]; ret` XCAP block → `cptr_to_Γ` /
   `cptr_specTable_to_extCallees` → `Compiled` / `LinkedCert` caller → `Xcap.cptr`):** links a
   hand-assembled x64 `"opaque_inc"` block with compiled `"call_opaque"` in one concrete Kraken
   x64 `Host`, feeds `opaqueInc_xcap_cptr` into `compiled_ofTable_cptr_src` and
   `linkedCert_ofTable_cptr_src`, and executes `call_opaque(20) = 41` in `%rax`.
4. `check_std_axioms!` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.XcapBridgeX64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Xcap LeanQbe.T.ProofKit Kraken
open LeanQbeTest.T.XcapBridgeTest

/-! ## 1. `AddrCodec x64Target` & `BitVec 64` / `Int64` Round-Trips -/

/-- Canonical injective `AddrCodec` for `x64Target` (`x64Mach.Addr = Int64`). -/
@[expose] def x64AddrCodec : AddrCodec x64Target where
  toBits := Int64.toBitVec
  ofBits := Int64.ofBitVec
  of_to := Int64.ofBitVec_toBitVec

theorem x64AddrCodec_to_of (bv : BitVec 64) :
    x64AddrCodec.toBits (x64AddrCodec.ofBits bv) = bv :=
  Int64.toBitVec_ofBitVec bv

theorem x64AddrCodec_ofNat_roundtrip (n : Nat) :
    x64AddrCodec.toBits (x64AddrCodec.ofBits (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n :=
  x64AddrCodec_to_of (BitVec.ofNat 64 n)

/-! ## 2. Direction 1: `LinkedCert` / `Compiled` → `T.FnSpec` → `Xcap.cptr` on x64 -/

compile_linked_chunks! x64SelfCert
  x64Target x64Layout x64LegalTarget x64LabelClean selfMod 2

/-- Direction 1 (`LinkedCert` → `Xcap.cptr`): `"double_add_ten"` compiled in `x64SelfCert` exports
an XCAP `cptr` for every `TargetClosed` machine spec `Ψ`. -/
theorem x64Self_doubleAddTen_cptr {Ψ : CodeSpec x64Target.mach.MData}
    {H : x64Target.mach.State → Prop}
    (hcl : TargetClosed x64Target x64AddrCodec x64SelfCert.host Ψ H) :
    x64Target.Defined x64SelfCert.host "double_add_ten" ∧
      cptr Ψ (x64AddrCodec.toBits (x64Target.mach.labelAddr x64SelfCert.host "double_add_ten"))
        (targetCallPre x64Target x64AddrCodec x64SelfCert.host
          (Env.ofTable selfTbl "double_add_ten" [i64] [i64])
          (x64SelfCert.bound "double_add_ten") 0 Ψ) :=
  linkedCert_host_to_cptr_src x64AddrCodec x64SelfCert (Env.ofTable selfTbl)
    selfMod_acyclic selfMod_moduleOk (f := fnDoubleAddTen)
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl rfl
    (Env.ofTable_noExit selfTbl_noExit "double_add_ten" [i64] [i64]) hcl

/-- Concrete Kraken x64 execution driven directly through Seam 1's `Xcap.cptr`:
`double_add_ten(7) = 34#64` in `%rax` at return address `0x1234`. -/
theorem x64Self_doubleAddTen_run_via_cptr :
    Eventually (x64Target.mach.step x64SelfCert.host)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 34#64)
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64]) (x64SelfCert.bound "double_add_ten") [] (7#64, ()))
        (x64Target.mach.labelAddr x64SelfCert.host "double_add_ten")) := by
  have hcptr := (x64Self_doubleAddTen_cptr
    (TargetSafe.closed x64Target x64AddrCodec x64SelfCert.host
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 34#64))).2
  refine run_i64_of_cptr x64AddrCodec x64Init hcptr [] (7#64, ())
    (x64SelfCert.bound_le_max "double_add_ten") (by decide) rfl
    (Q := fun rets _ => rets = (34#64, ())) ?_ (fun _ _ h => h)
  exact Or.inr ⟨(fun h => absurd h.1 (by decide)), Or.inl ⟨⟨rfl, rfl, rfl⟩, rfl⟩⟩

/-! ## 3. Direction 2: Opaque x64 XCAP Block → `cptr_to_Γ` → Compiled Caller → `Xcap.cptr` -/

/-- Hand-assembled x64 opaque callee (`lea rax, [rdi + 1]; ret`). -/
@[expose] def x64OpaqueIncBody : List Directive :=
  [ins (.lea (q .rax) (atDisp .rdi 1))]

theorem x64OpaqueIncBody_op :
    x64Target.gpr.op (.add i64) (.gpr .rdi, .imm 1#64, ()) (.gpr .rax, ()) (.disp 1) =
      some (x64OpaqueIncBody, maskNone) :=
  rfl

@[expose] def x64OpaqueIncCode : List Directive :=
  opaqueIncCode x64Target x64OpaqueIncBody

splice_module_hints x64CallerHints x64Target.toIsa x64LegalTarget callerFns

splice_chunk_literals x64CallerCode x64CallerBounds x64CallerSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  opaqueExtCallees [] 0 callerFns x64CallerHints

theorem x64Caller_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      (extCalleesOfTable x64LegalTarget opaqueExtRows) [] 0 callerFns x64CallerHints =
      .ok (x64CallerCode, x64CallerBounds) := by
  t_kernel_rfl

theorem x64Caller_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      x64CallerCode x64CallerBounds (callerFns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

@[expose] def x64CallerCompiled :
    Compiled x64Target x64LegalTarget (extCalleesOfTable x64LegalTarget opaqueExtRows)
      [] 0 callerFns x64CallerHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    (extCalleesOfTable x64LegalTarget opaqueExtRows) [] 0
    callerFns x64CallerHints 2048 x64CallerCode x64CallerBounds x64Caller_cm x64Caller_meta

@[expose] def x64CallerChunk :
    CompiledChunk x64Target x64LegalTarget [] 0 :=
  ⟨extCalleesOfTable x64LegalTarget opaqueExtRows, callerFns, x64CallerHints, 2048,
    x64CallerCompiled⟩

theorem x64CallerCert_linkCheck :
    checkLinkList x64Layout (extCalleesOfTable x64LegalTarget opaqueExtRows) [x64CallerChunk] =
      true := by
  t_kernel_rfl

@[expose] def x64CallerCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean callerMod
      (extCalleesOfTable x64LegalTarget opaqueExtRows) [] 0 2048 where
  chunks := [x64CallerChunk]
  linkCheck := x64CallerCert_linkCheck
  fns_eq := rfl
  supportsAll := x64CallerCompiled.supportsSource
  maxBound_le := Nat.le_refl 2048

/-- Combined Kraken x64 program: opaque hand-assembled `"opaque_inc"` + compiled `"call_opaque"`. -/
@[expose] def x64CombinedProg : List Directive :=
  x64OpaqueIncCode ++ x64CallerCode

theorem x64CombinedProg_small : x64Layout.progSmall x64CombinedProg = true := by t_kernel_rfl
theorem x64CombinedProg_nodup : x64Layout.labelsNodup x64CombinedProg = true := by t_kernel_rfl

/-- Concrete Kraken x64 `Host` laying out both the opaque XCAP block and compiled caller. -/
@[expose, instance_reducible] def x64CombinedHost : x64Target.mach.Host :=
  x64Layout.layoutOf x64CombinedProg x64CombinedProg_small

theorem x64CombinedHost_labelsUnique : x64Target.LabelsUnique x64CombinedHost :=
  x64Layout.labelsUnique_layoutOf x64CombinedProg_small x64CombinedProg_nodup

theorem x64OpaqueInc_infix :
    x64OpaqueIncCode.IsInfixAt (x64Target.mach.prog x64CombinedHost) 0 :=
  ⟨x64CallerCode, rfl⟩

theorem x64Caller_infix :
    x64CallerCompiled.code.IsInfixAt (x64Target.mach.prog x64CombinedHost)
      x64OpaqueIncCode.length := by
  have h : (x64OpaqueIncCode ++ x64CallerCode).IsInfixAt
      (x64Target.mach.prog x64CombinedHost) 0 :=
    ⟨[], List.append_nil _⟩
  simpa [x64CallerCompiled, compileCheckedLit, Nat.zero_add] using (List.IsInfixAt.append h).2

/-- Pure XCAP `cptr` proof for the hand-assembled x64 `"opaque_inc"` block in `x64CombinedHost`. -/
theorem x64OpaqueInc_cptr {Ψ : CodeSpec x64Target.mach.MData} {H : x64Target.mach.State → Prop}
    (hcl : TargetClosed x64Target x64AddrCodec x64CombinedHost Ψ H) :
    cptr Ψ (x64AddrCodec.toBits (x64Target.mach.labelAddr x64CombinedHost "opaque_inc"))
      (targetCallPre x64Target x64AddrCodec x64CombinedHost opaqueIncRow.eff 0 0 Ψ) :=
  opaqueInc_xcap_cptr x64AddrCodec (arg0 := .rdi) (ret0 := .rax) (vh := .disp 1)
    rfl rfl (by simp [x64Scratch]) (by simp [x64Scratch])
    (by decide) (by simp) (by simp) (by decide)
    x64OpaqueIncBody_op x64OpaqueInc_infix x64CombinedHost_labelsUnique hcl

theorem x64ExtTableOk :
    XcapExtTableOk x64AddrCodec x64LegalTarget x64CombinedHost callerMod callerTbl 0
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
    exact x64OpaqueInc_cptr (TargetSafe.closed x64Target x64AddrCodec x64CombinedHost H)

/-- Direction 2 (`cptr_to_Γ` + `cptr_specTable_to_extCallees` + `Env.ofTable_moduleOk` →
`Compiled` caller `"call_opaque"` → `T.FnSpec` on `x64CombinedHost`). -/
theorem x64Caller_fnSpec_via_xcap :
    x64Target.Defined x64CombinedHost "call_opaque" ∧
      x64Target.FnSpec x64CombinedHost "call_opaque"
        (Env.ofTable callerTbl "call_opaque" [i64] [i64])
        (x64CallerCompiled.bound "call_opaque") 0 :=
  compiled_ofTable_fnSpec_src x64AddrCodec x64CallerCompiled callerMod rfl callerTbl
    x64CombinedHost x64OpaqueIncCode.length x64Caller_infix x64CombinedHost_labelsUnique
    callerMod_acyclic callerMod_allWf callerTbl_impl x64ExtTableOk
    (fun _ hx => nomatch hx) (f := fnCallOpaque) List.mem_cons_self rfl rfl

/-- Full round-trip on `LinkedCert` (`x64CallerCert`): opaque x64 XCAP callee → `cptr_to_Γ` →
compiled `"call_opaque"` → `fnSpec_to_cptr` → XCAP `cptr` on `x64CombinedHost`. -/
theorem x64CallerCert_cptr_roundtrip {Ψ : CodeSpec x64Target.mach.MData}
    {H : x64Target.mach.State → Prop}
    (hcl : TargetClosed x64Target x64AddrCodec x64CombinedHost Ψ H) :
    x64Target.Defined x64CombinedHost "call_opaque" ∧
      cptr Ψ (x64AddrCodec.toBits (x64Target.mach.labelAddr x64CombinedHost "call_opaque"))
        (targetCallPre x64Target x64AddrCodec x64CombinedHost
          (Env.ofTable callerTbl "call_opaque" [i64] [i64])
          (x64CallerCert.bound "call_opaque") 0 Ψ) :=
  linkedCert_ofTable_cptr_src x64AddrCodec x64CallerCert callerTbl
    x64CombinedHost x64OpaqueIncCode.length
    (by simpa [LinkedCert.code, LinkedCert.compiled, linkCompiledList, chunksCode,
      x64CallerCert, x64CallerChunk] using x64Caller_infix)
    x64CombinedHost_labelsUnique callerMod_acyclic callerMod_allWf callerTbl_impl x64ExtTableOk
    (fun _ hx => nomatch hx) (f := fnCallOpaque) List.mem_cons_self rfl rfl hcl

/-- Closed concrete Kraken x64 execution of compiled `"call_opaque"` calling hand-assembled XCAP
`"opaque_inc"`: `call_opaque(20) = (20 + 1) + 20 = 41#64` in `%rax`. -/
theorem x64Caller_run_via_cptr :
    Eventually (x64Target.mach.step x64CombinedHost)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 41#64)
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64]) (x64CallerCert.bound "call_opaque") [] (20#64, ()))
        (x64Target.mach.labelAddr x64CombinedHost "call_opaque")) := by
  have hcptr := (x64CallerCert_cptr_roundtrip
    (TargetSafe.closed x64Target x64AddrCodec x64CombinedHost
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 41#64))).2
  refine run_i64_of_cptr x64AddrCodec x64Init hcptr [] (20#64, ())
    (x64CallerCert.bound_le_max "call_opaque") (by decide) rfl
    (Q := fun rets _ => rets = (41#64, ())) ?_ (fun _ _ h => h)
  exact Or.inl ⟨⟨rfl, rfl, rfl⟩, rfl⟩

check_std_axioms!
  LeanQbeTest.T.XcapBridgeX64Test.x64AddrCodec_to_of
  LeanQbeTest.T.XcapBridgeX64Test.x64AddrCodec_ofNat_roundtrip
  LeanQbeTest.T.XcapBridgeX64Test.x64Self_doubleAddTen_cptr
  LeanQbeTest.T.XcapBridgeX64Test.x64Self_doubleAddTen_run_via_cptr
  LeanQbeTest.T.XcapBridgeX64Test.x64OpaqueInc_cptr
  LeanQbeTest.T.XcapBridgeX64Test.x64Caller_fnSpec_via_xcap
  LeanQbeTest.T.XcapBridgeX64Test.x64CallerCert_cptr_roundtrip
  LeanQbeTest.T.XcapBridgeX64Test.x64Caller_run_via_cptr

end LeanQbeTest.T.XcapBridgeX64Test
