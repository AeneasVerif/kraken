module

public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemoProof
public import LeanQbe.T.MainCertFlat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemo

/-!
# AAPCS64 AArch64 `LinkedCert` & Execution Witnesses for `ArrayDemo` (`LcnfC0ArrayDemoCertArm64`)

Acyclically compiles `arrayDemoProgMod` (`ArrayDemo.{arrayPushSetGet, baPushSetGet, baCowSetGet}`,
`3` fns) via `compile_linked_chunks!`, appends onto `rtC0CoreArm64Cert` (`80` pure-C0 runtime fns,
`0` externs, `0` C runtime) via `LcnfC0LinkKit.linkRtC0Cert` (`83` fns total, `maxBound = 2048`),
bridges `arrayDemoLinkedMod_moduleOk` to `armTarget.Defined` + `armTarget.FnSpec`, and proves
closed concrete AAPCS64 AArch64 `Eventually` execution witnesses (`0` `import all`):

1. `arrayDemoArm64_arrayPushSetGet_run`: `(10, 20, 42) → boxNat 62 = 125#64` in `X0` (`0` leaks).
2. `arrayDemoArm64_baPushSetGet_run`: `(4, 10, 20, 42) → 62#8` in `W0` (`0` leaks).
3. `arrayDemoArm64_baCowSetGet_shared_run`: shared `rc = 2` `ByteArray` `[10, 20]` updated with
   `42#8` → returns `62#8` in `W0` **and** preserves the original `[10, 20]` object with `rc = 1`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

/-! ## 1. `compile_linked_chunks!` & Compositional `linkRtC0Cert` -/

compile_linked_chunks! arrayDemoArm64ProgCert armTarget armLayout armLegalTarget armLabelClean
  arrayDemoProgMod 3 (ext := rtC0CoreArm64AllExt) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 600) (flat := true)

/-- Full `83`-function AAPCS64 AArch64 `LinkedCert` combining `rtC0CoreArm64Cert` (`80` fns) and
`arrayDemoArm64ProgCert` (`3` R2 container client fns, `maxBound = 2048`, `0` externs). -/
@[expose] noncomputable def arrayDemoArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      arrayDemoLinkedMod [] rtExitSyms 64 (Nat.max 2048 2048) :=
  linkRtC0Cert rtC0CoreArm64Cert arrayDemoArm64ProgCert (by t_kernel_rfl)

theorem arrayDemoArm64Cert_bounds_len : arrayDemoArm64Cert.bounds.length = 83 :=
  arrayDemoArm64Cert.bounds_length.trans (by decide)

theorem arrayDemoArm64Cert_bounds_le :
    arrayDemoArm64Cert.bounds.all (fun p => Nat.ble p.2 2048) = true := by
  t_kernel_rfl

private theorem arrayDemoLinkedMod_arm_legalSig :
    LegalSigAll armLegalTarget arrayDemoLinkedMod.fns :=
  linkLcnfWithRtC0_legalSigAll armLegalTarget arrayDemoTfs (by t_kernel_rfl) (by decide)

/-! ## 2. Machine-Level `armTarget.Defined` + `armTarget.FnSpec` Bridges -/

private theorem arrayDemo_mem_tf0 :
    arrayDemoTfs.tf_0.toFn ∈ (lcnfProgMod arrayDemoTfs).fns := by
  rw [arrayDemoProgMod_fns_eq]; exact List.mem_cons_self

private theorem arrayDemo_mem_tf1 :
    arrayDemoTfs.tf_1.toFn ∈ (lcnfProgMod arrayDemoTfs).fns := by
  rw [arrayDemoProgMod_fns_eq]; simp

private theorem arrayDemo_mem_tf2 :
    arrayDemoTfs.tf_2.toFn ∈ (lcnfProgMod arrayDemoTfs).fns := by
  rw [arrayDemoProgMod_fns_eq]; simp

theorem arrayDemoArm64_arrayPushSetGet_fnSpec :
    armTarget.Defined arrayDemoArm64Cert.host arrayDemoArrName ∧
      armTarget.FnSpec arrayDemoArm64Cert.host arrayDemoArrName arrayPushSetGetSpec
        (arrayDemoArm64Cert.bound arrayDemoArrName) 64 :=
  linkRtC0Cert_fnSpec_of_spec arrayDemoArm64Cert arrayDemoEnv
    arrayDemoLinkedMod_checkAcyclic arrayDemoLinkedMod_arm_legalSig arrayDemoProgMod_wp
    arrayDemo_mem_tf0 (fun _ _ _ _ _ h => arrayDemoEnv_arrayPushSetGet_noex h)
    (fun _ _ _ _ h => arrayDemoEnv_arrayPushSetGet h)

theorem arrayDemoArm64_baPushSetGet_fnSpec :
    armTarget.Defined arrayDemoArm64Cert.host arrayDemoBaName ∧
      armTarget.FnSpec arrayDemoArm64Cert.host arrayDemoBaName baPushSetGetSpec
        (arrayDemoArm64Cert.bound arrayDemoBaName) 64 :=
  linkRtC0Cert_fnSpec_of_spec arrayDemoArm64Cert arrayDemoEnv
    arrayDemoLinkedMod_checkAcyclic arrayDemoLinkedMod_arm_legalSig arrayDemoProgMod_wp
    arrayDemo_mem_tf1 (fun _ _ _ _ _ h => arrayDemoEnv_baPushSetGet_noex h)
    (fun _ _ _ _ h => arrayDemoEnv_baPushSetGet h)

theorem arrayDemoArm64_baCowSetGet_fnSpec :
    armTarget.Defined arrayDemoArm64Cert.host arrayDemoBaCowName ∧
      armTarget.FnSpec arrayDemoArm64Cert.host arrayDemoBaCowName baCowSetGetSpec
        (arrayDemoArm64Cert.bound arrayDemoBaCowName) 64 :=
  linkRtC0Cert_fnSpec_of_spec arrayDemoArm64Cert arrayDemoEnv
    arrayDemoLinkedMod_checkAcyclic arrayDemoLinkedMod_arm_legalSig arrayDemoProgMod_wp
    arrayDemo_mem_tf2 (fun _ _ _ _ _ h => arrayDemoEnv_baCowSetGet_noex h)
    (fun _ _ _ _ h => arrayDemoEnv_baCowSetGet h)

/-! ## 3. `TargetInit` for `64KiB` Payload Slabs (`0` `import all`) & Concrete `Eventually` Runs -/

theorem armInitMem_entry_64k (n : Nat) (bs : List UInt8)
    (hn : n ≤ 2048) (hbs : bs.length ≤ 65536) :
    (Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 n ⋆ Std.ExtHashMap.emp)
      (armInitMem n bs) := by
  have hzs : (stackZeros n).length = n := stackZeros_length n
  have h1 := Mem.At_append_sep (stackZeros n) bs (0x1000#64 - BitVec.ofNat 64 n)
    (by rw [hzs]; exact Nat.le_trans (Nat.add_le_add hn hbs) (by decide))
  have e1 : 0x1000#64 - BitVec.ofNat 64 n + BitVec.ofNat 64 (stackZeros n).length = 0x1000#64 := by
    rw [hzs, BitVec.sub_add_cancel]
  rw [e1] at h1
  have h0 : (Eq (bs.At 0x1000#64) ⋆
      Eq ((stackZeros n).At (0x1000#64 - BitVec.ofNat 64 n)) ⋆
      Std.ExtHashMap.emp) (armInitMem n bs) := by
    rw [Std.ExtHashMap.sep_emp]
    refine sep_cast (show Eq (armInitMem n bs) (armInitMem n bs) from rfl) ?_
    change Eq ((stackZeros n ++ bs).At (0x1000#64 - BitVec.ofNat 64 n)) = _
    rw [h1, Std.ExtHashMap.sep_comm]
  refine sep_mono_mid (fun _ hm => ?_) h0
  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds]
  simp only [region_zero, Std.ExtHashMap.sep_emp]
  exact ⟨stackZeros n, hzs, hm.symm⟩

/-- `TargetInit` extending `armInit` to `64KiB` payload slabs (`arrayRtBytes` / `arrayCowBytes`).
-/
@[expose] def arrayDemoArm64Init : TargetInit armTarget 2048 65536 where
  sp0 := armInit.sp0
  ra0 := armInit.ra0
  ret0 := armInit.ret0
  arg0 := armInit.arg0
  initState := armInit.initState
  get_sp := armInit.get_sp
  argsIn := armInit.argsIn
  raReg := armInit.raReg
  spEntry := armInit.spEntry
  mem_entry n bs {_} _ hn hbs := armInitMem_entry_64k n bs hn hbs
  retsIn_singleton := armInit.retsIn_singleton
  argsIn_singleton := armInit.argsIn_singleton

private theorem arm_retsIn_i8 {v : BitVec 8} {s : MachineData}
    (h : armTarget.RetsIn (bs := [i8]) (v, ()) s) :
    (s.regs.getXReg .X0).toBitVec.setWidth 8 = v := by
  obtain ⟨locs, hlocs, hrel⟩ := h
  change some (AbiReg.gpr (.reg .X0), ()) = some locs at hlocs
  injection hlocs with hlocs; subst hlocs
  cases hrel with
  | cons h1 _ =>
    have h64 : (s.regs.getXReg .X0).toBitVec = v.setWidth 64 := by simpa [get_reg] using h1.2
    rw [h64]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide)), Nat.mod_eq_of_lt v.isLt]

/-- Closed AArch64 machine execution of `ArrayDemo.arrayPushSetGet (10, 20, 42)` on `arrayRtBytes`
(`0x1000#64`), returning `boxNat 62 = 125#64` in `X0` and preserving `rtC0Inv` (`0` leaks). -/
theorem arrayDemoArm64_arrayPushSetGet_run :
    letI : Host := arrayDemoArm64Cert.host
    Eventually (step1 arrayDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 62 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ st' : RtC0State, rtC0Inv arrayRtBase st' m') ⋆
          armTarget.Exit 0x1000#64 (arrayDemoArm64Cert.bound arrayDemoArrName) ⋆ emp))
      ⟨armInitState (as := [i64, i64, i64, i64])
          (arrayDemoArm64Cert.bound arrayDemoArrName) arrayRtBytes
          (arrayRtBase, boxNat 10, boxNat 20, boxNat 42, ()),
        Labels.label arrayDemoArrName⟩ := by
  let P : Mem 64 → Prop := fun m' => ∃ st' : RtC0State, rtC0Inv arrayRtBase st' m'
  let Q : Post [i64] := fun r m' => r = (boxNat 62, ()) ∧ P m'
  have hrem : arrAllocBytes 4 ≤ arrayRtState.rem := by
    unfold RtC0State.rem
    simp only [arrayRtState, initRtC0State, arrayRtBase, arrayRtWorkCap, arrayRtRem]
    decide
  have hspec : arrayPushSetGetSpec (arrayRtBase, boxNat 10, boxNat 20, boxNat 42, ())
      (arrayRtBytes.At 0x1000#64) Q (fun _ _ _ _ => False) :=
    ⟨10, 20, 42, arrayRtState, emp, rfl, rfl, rfl, by decide, by decide, by decide,
      Or.inr hrem, by rw [sep_emp]; exact arrayRtBytes_ok.2,
      fun st' m' _ _ hm' => by rw [sep_emp] at hm'; exact ⟨rfl, st', hm'⟩⟩
  have hrun := arrayDemoArm64Cert.run_ret1_sep_i64 arrayDemoArm64Init
    arrayDemoArm64_arrayPushSetGet_fnSpec.2 arrayRtBytes
    (arrayRtBase, boxNat 10, boxNat 20, boxNat 42, ()) (boxNat 62) P
    (by rw [arrayRtBytes_ok.1]; decide) (by decide) hspec (fun _ _ h => h) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hx0, hmem⟩ =>
      ⟨hpc, by simpa [arrayDemoArm64Init, armInit, get_reg] using hx0, hmem⟩) hrun

/-- Closed AArch64 machine execution of `ArrayDemo.baPushSetGet (4, 10, 20, 42)` on `arrayRtBytes`
(`0x1000#64`), returning `62#8` in `W0` and preserving `rtC0Inv` (`0` leaks). -/
theorem arrayDemoArm64_baPushSetGet_run :
    letI : Host := arrayDemoArm64Cert.host
    Eventually (step1 arrayDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec.setWidth 8 = 62#8 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ st' : RtC0State, rtC0Inv arrayRtBase st' m') ⋆
          armTarget.Exit 0x1000#64 (arrayDemoArm64Cert.bound arrayDemoBaName) ⋆ emp))
      ⟨armInitState (as := [i64, i64, i8, i8, i8])
          (arrayDemoArm64Cert.bound arrayDemoBaName) arrayRtBytes
          (arrayRtBase, boxNat 4, 10#8, 20#8, 42#8, ()),
        Labels.label arrayDemoBaName⟩ := by
  let P : Mem 64 → Prop := fun m' => ∃ st' : RtC0State, rtC0Inv arrayRtBase st' m'
  let Q : Post [i8] := fun r m' => r = (62#8, ()) ∧ P m'
  have hrem : baAllocBytes 4 ≤ arrayRtState.rem := by
    unfold RtC0State.rem
    simp only [arrayRtState, initRtC0State, arrayRtBase, arrayRtWorkCap, arrayRtRem]
    decide
  have hspec : baPushSetGetSpec (arrayRtBase, boxNat 4, 10#8, 20#8, 42#8, ())
      (arrayRtBytes.At 0x1000#64) Q (fun _ _ _ _ => False) :=
    ⟨4, arrayRtState, emp, rfl, by decide, by decide, by decide, Or.inr hrem,
      by rw [sep_emp]; exact arrayRtBytes_ok.2,
      fun st' m' _ _ hm' => by
        rw [sep_emp] at hm'; rw [baPushSetGet_eq]; exact ⟨rfl, st', hm'⟩⟩
  have hrun := arrayDemoArm64Cert.run_ret1_sep arrayDemoArm64Init
    arrayDemoArm64_baPushSetGet_fnSpec.2 arrayRtBytes
    (arrayRtBase, boxNat 4, 10#8, 20#8, 42#8, ()) 62#8 P
    (by rw [arrayRtBytes_ok.1]; decide) (by decide) hspec (fun _ _ h => h) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hrets, hmem⟩ =>
      ⟨hpc, arm_retsIn_i8 hrets, hmem⟩) hrun

/-- Closed AArch64 machine execution of `ArrayDemo.baCowSetGet` on a **shared (`rc = 2`)**
`ByteArray` `[10, 20]` with `v = 42#8` (`arrayCowBytes` @ `0x1000#64`): returns `62#8` in `W0`
**and** preserves the untouched original `[10, 20]` object (`sharedBaObjAfter`, `rc = 1`). -/
theorem arrayDemoArm64_baCowSetGet_shared_run :
    letI : Host := arrayDemoArm64Cert.host
    Eventually (step1 arrayDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec.setWidth 8 = 62#8 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ st' : RtC0State,
            (rtC0Inv arrayRtBase st' ⋆ lcnfObjMem sharedBaObjAfter) m') ⋆
          armTarget.Exit 0x1000#64 (arrayDemoArm64Cert.bound arrayDemoBaCowName) ⋆ emp))
      ⟨armInitState (as := [i64, i64, i8])
          (arrayDemoArm64Cert.bound arrayDemoBaCowName) arrayCowBytes
          (arrayRtBase, sharedBaAddr, 42#8, ()),
        Labels.label arrayDemoBaCowName⟩ := by
  let P : Mem 64 → Prop := fun m' =>
    ∃ st' : RtC0State, (rtC0Inv arrayRtBase st' ⋆ lcnfObjMem sharedBaObjAfter) m'
  let Q : Post [i8] := fun r m' => r = (62#8, ()) ∧ P m'
  have hrem : baAllocBytes sharedBaObj.cap ≤ arrayRtState.rem := by
    unfold RtC0State.rem
    simp only [arrayRtState, initRtC0State, arrayRtBase, arrayRtWorkCap, arrayRtRem, sharedBaObj,
      mkBaObj]
    decide
  have hspec : baCowSetGetSpec (arrayRtBase, sharedBaAddr, 42#8, ())
      (arrayCowBytes.At 0x1000#64) Q (fun _ _ _ _ => False) := by
    refine ⟨arrayRtState, sharedBaObj, 10, 20, [], emp, rfl, sharedBaObj_canon, rfl, by decide,
      fun _ => Or.inr hrem, by rw [sep_emp]; exact arrayCowBytes_ok.2, ?_⟩
    dsimp only
    intro st' m' _ _ hm'
    rw [sep_emp] at hm'
    have hne : sharedBaObj.rc ≠ 1#32 := by decide
    have hdec : sharedBaObj.withRc (decNonExclRc sharedBaObj.rc) = sharedBaObjAfter := by
      simp [sharedBaObj, sharedBaObjAfter, mkBaObj, LcnfObj.withRc, decNonExclRc]
    rw [ite_eq_right hne, hdec] at hm'
    exact ⟨rfl, st', hm'⟩
  have hrun := arrayDemoArm64Cert.run_ret1_sep arrayDemoArm64Init
    arrayDemoArm64_baCowSetGet_fnSpec.2 arrayCowBytes
    (arrayRtBase, sharedBaAddr, 42#8, ()) 62#8 P
    (by rw [arrayCowBytes_ok.1]; decide) (by decide) hspec (fun _ _ h => h) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hrets, hmem⟩ =>
      ⟨hpc, arm_retsIn_i8 hrets, hmem⟩) hrun

end LeanQbe.T.Arm64
