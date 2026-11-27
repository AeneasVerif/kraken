module

public import LeanQbe.T.Amd64.LcnfC0FullCertX64
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemoProof
public import LeanQbe.T.MainCertFlat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemo

/-!
# SysV x86-64 `LinkedCert` & Execution Witnesses for `ArrayDemo` (`LcnfC0ArrayDemoCertX64`)

Acyclically compiles `arrayDemoProgMod` (`ArrayDemo.{arrayPushSetGet, baPushSetGet, baCowSetGet}`,
`3` fns) via `compile_linked_chunks!`, appends onto `rtC0CoreCert` (`80` pure-C0 runtime fns,
`0` externs, `0` C runtime) via `LcnfC0LinkKit.linkRtC0Cert` (`83` fns total, `maxBound = 2048`),
bridges `arrayDemoLinkedMod_moduleOk` to `x64Target.Defined` + `x64Target.FnSpec`, and proves
closed concrete SysV x86-64 `Eventually` execution witnesses (`0` `import all`):

1. `arrayDemoX64_arrayPushSetGet_run`: `(10, 20, 42) → boxNat 62 = 125#64` in `%rax` (`0` leaks).
2. `arrayDemoX64_baPushSetGet_run`: `(4, 10, 20, 42) → 62#8` in `%al` (`0` leaks).
3. `arrayDemoX64_baCowSetGet_shared_run`: shared `rc = 2` `ByteArray` `[10, 20]` updated with
   `42#8` → returns `62#8` in `%al` **and** preserves the original `[10, 20]` object with `rc = 1`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

/-! ## 1. `compile_linked_chunks!` & Compositional `linkRtC0Cert` -/

compile_linked_chunks! arrayDemoX64ProgCert x64Target x64Layout x64LegalTarget x64LabelClean
  arrayDemoProgMod 3 (ext := rtC0CoreAllExt) (exits := rtExitSyms) (nX := 64) (maxDirs := 600)
  (flat := true)

/-- Full `83`-function SysV x86-64 `LinkedCert` combining `rtC0CoreCert` (`80` fns) and
`arrayDemoX64ProgCert` (`3` R2 container client fns, `maxBound = 2048`, `0` externs). -/
@[expose] noncomputable def arrayDemoX64Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      arrayDemoLinkedMod [] rtExitSyms 64 (Nat.max 2048 2048) :=
  linkRtC0Cert rtC0CoreCert arrayDemoX64ProgCert (by t_kernel_rfl)

theorem arrayDemoX64Cert_bounds_len : arrayDemoX64Cert.bounds.length = 83 :=
  arrayDemoX64Cert.bounds_length.trans (by decide)

theorem arrayDemoX64Cert_bounds_le :
    arrayDemoX64Cert.bounds.all (fun p => Nat.ble p.2 2048) = true := by
  t_kernel_rfl

private theorem arrayDemoLinkedMod_x64_legalSig :
    LegalSigAll x64LegalTarget arrayDemoLinkedMod.fns :=
  linkLcnfWithRtC0_legalSigAll x64LegalTarget arrayDemoTfs (by t_kernel_rfl) (by decide)

/-! ## 2. Machine-Level `x64Target.Defined` + `x64Target.FnSpec` Bridges -/

private theorem arrayDemo_mem_tf0 :
    arrayDemoTfs.tf_0.toFn ∈ (lcnfProgMod arrayDemoTfs).fns := by
  rw [arrayDemoProgMod_fns_eq]; exact List.mem_cons_self

private theorem arrayDemo_mem_tf1 :
    arrayDemoTfs.tf_1.toFn ∈ (lcnfProgMod arrayDemoTfs).fns := by
  rw [arrayDemoProgMod_fns_eq]; simp

private theorem arrayDemo_mem_tf2 :
    arrayDemoTfs.tf_2.toFn ∈ (lcnfProgMod arrayDemoTfs).fns := by
  rw [arrayDemoProgMod_fns_eq]; simp

theorem arrayDemoX64_arrayPushSetGet_fnSpec :
    x64Target.Defined arrayDemoX64Cert.host arrayDemoArrName ∧
      x64Target.FnSpec arrayDemoX64Cert.host arrayDemoArrName arrayPushSetGetSpec
        (arrayDemoX64Cert.bound arrayDemoArrName) 64 :=
  linkRtC0Cert_fnSpec_of_spec arrayDemoX64Cert arrayDemoEnv
    arrayDemoLinkedMod_checkAcyclic arrayDemoLinkedMod_x64_legalSig arrayDemoProgMod_wp
    arrayDemo_mem_tf0 (fun _ _ _ _ _ h => arrayDemoEnv_arrayPushSetGet_noex h)
    (fun _ _ _ _ h => arrayDemoEnv_arrayPushSetGet h)

theorem arrayDemoX64_baPushSetGet_fnSpec :
    x64Target.Defined arrayDemoX64Cert.host arrayDemoBaName ∧
      x64Target.FnSpec arrayDemoX64Cert.host arrayDemoBaName baPushSetGetSpec
        (arrayDemoX64Cert.bound arrayDemoBaName) 64 :=
  linkRtC0Cert_fnSpec_of_spec arrayDemoX64Cert arrayDemoEnv
    arrayDemoLinkedMod_checkAcyclic arrayDemoLinkedMod_x64_legalSig arrayDemoProgMod_wp
    arrayDemo_mem_tf1 (fun _ _ _ _ _ h => arrayDemoEnv_baPushSetGet_noex h)
    (fun _ _ _ _ h => arrayDemoEnv_baPushSetGet h)

theorem arrayDemoX64_baCowSetGet_fnSpec :
    x64Target.Defined arrayDemoX64Cert.host arrayDemoBaCowName ∧
      x64Target.FnSpec arrayDemoX64Cert.host arrayDemoBaCowName baCowSetGetSpec
        (arrayDemoX64Cert.bound arrayDemoBaCowName) 64 :=
  linkRtC0Cert_fnSpec_of_spec arrayDemoX64Cert arrayDemoEnv
    arrayDemoLinkedMod_checkAcyclic arrayDemoLinkedMod_x64_legalSig arrayDemoProgMod_wp
    arrayDemo_mem_tf2 (fun _ _ _ _ _ h => arrayDemoEnv_baCowSetGet_noex h)
    (fun _ _ _ _ h => arrayDemoEnv_baCowSetGet h)

/-! ## 3. `TargetInit` for `64KiB` Payload Slabs (`0` `import all`) & Concrete `Eventually` Runs -/

theorem x64InitMem_entry_64k (n : Nat) (ra : Int64) (bs : List UInt8)
    (hn : n ≤ 2048) (hbs : bs.length ≤ 65536) :
    (Eq (bs.At 0x1000#64) ⋆ x64Target.Entry 0x0ff8#64 ra n ⋆ Std.ExtHashMap.emp)
      (x64InitMem n ra bs) := by
  let raBytes : List UInt8 := Int.toBytes 8 ra.toBitVec.toInt
  have hra : raBytes.length = 8 := Int.toBytes_length 8 _
  have hzs : (stackZeros n).length = n := stackZeros_length n
  have hsp : (0x0ff8#64 - BitVec.ofNat 64 n) + BitVec.ofNat 64 n = 0x0ff8#64 :=
    BitVec.sub_add_cancel _ _
  have h1000 : (0x0ff8#64 : BitVec 64) + BitVec.ofNat 64 8 = 0x1000#64 := by decide
  have hlen1 : (stackZeros n).length + (raBytes ++ bs).length ≤ 2 ^ 64 := by
    rw [hzs, List.length_append, hra]
    exact Nat.le_trans (Nat.add_le_add hn (Nat.add_le_add_left hbs 8)) (by decide)
  have hlen2 : raBytes.length + bs.length ≤ 2 ^ 64 := by
    rw [hra]; exact Nat.le_trans (Nat.add_le_add_left hbs 8) (by decide)
  have h1 : Eq ((stackZeros n ++ (raBytes ++ bs)).At (0x0ff8#64 - BitVec.ofNat 64 n)) =
      (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆
        Eq ((raBytes ++ bs).At 0x0ff8#64)) := by
    have e := Mem.At_append_sep (stackZeros n) (raBytes ++ bs) (0x0ff8#64 - BitVec.ofNat 64 n) hlen1
    rwa [hzs, hsp] at e
  have h2 : Eq ((raBytes ++ bs).At 0x0ff8#64) =
      (Eq (raBytes.At 0x0ff8#64) ⋆ Eq (bs.At 0x1000#64)) := by
    have e := Mem.At_append_sep raBytes bs 0x0ff8#64 hlen2
    rwa [hra, h1000] at e
  have hmem : (Eq (bs.At 0x1000#64) ⋆
      (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆ Eq (raBytes.At 0x0ff8#64)) ⋆
      Std.ExtHashMap.emp) (x64InitMem n ra bs) := by
    rw [Std.ExtHashMap.sep_emp]
    refine sep_cast (show Eq (x64InitMem n ra bs) (x64InitMem n ra bs) from rfl) ?_
    change Eq ((stackZeros n ++ raBytes ++ bs).At (0x0ff8#64 - BitVec.ofNat 64 n)) = _
    rw [List.append_assoc, h1, h2]; ac_rfl
  exact sep_mono_mid (fun _ hm => sep_mono (fun _ hm' => ⟨stackZeros n, hzs, hm'.symm⟩) hm) hmem

/-- `TargetInit` extending `x64Init` to `64KiB` payload slabs (`arrayRtBytes` / `arrayCowBytes`).
-/
@[expose] def arrayDemoX64Init : TargetInit x64Target 2048 65536 where
  sp0 := x64Init.sp0
  ra0 := x64Init.ra0
  ret0 := x64Init.ret0
  arg0 := x64Init.arg0
  initState := x64Init.initState
  get_sp := x64Init.get_sp
  argsIn := x64Init.argsIn
  raReg := x64Init.raReg
  spEntry := x64Init.spEntry
  mem_entry n bs {_} _ hn hbs := x64InitMem_entry_64k n 0x1234 bs hn hbs
  retsIn_singleton := x64Init.retsIn_singleton
  argsIn_singleton := x64Init.argsIn_singleton

private theorem x64_retsIn_i8 {v : BitVec 8} {s : MachineData}
    (h : x64Target.RetsIn (bs := [i8]) (v, ()) s) :
    (s.regs.get64 .rax).setWidth 8 = v := by
  obtain ⟨locs, hlocs, hrel⟩ := h
  change some (AbiReg.gpr .rax, ()) = some locs at hlocs
  injection hlocs with hlocs; subst hlocs
  cases hrel with
  | cons h1 _ =>
    have h64 : s.regs.get64 .rax = v.setWidth 64 := h1.2
    rw [h64]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide)), Nat.mod_eq_of_lt v.isLt]

/-- Closed x86-64 machine execution of `ArrayDemo.arrayPushSetGet (10, 20, 42)` on `arrayRtBytes`
(`0x1000#64`), returning `boxNat 62 = 125#64` in `%rax` and preserving `rtC0Inv` (`0` leaks). -/
theorem arrayDemoX64_arrayPushSetGet_run :
    letI : Host := arrayDemoX64Cert.host
    Eventually (step1 arrayDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 62 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ st' : RtC0State, rtC0Inv arrayRtBase st' m') ⋆
          x64Target.Exit 0x0ff8#64 (arrayDemoX64Cert.bound arrayDemoArrName) ⋆ emp))
      ⟨x64InitState (as := [i64, i64, i64, i64])
          (arrayDemoX64Cert.bound arrayDemoArrName) arrayRtBytes
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
  exact arrayDemoX64Cert.run_ret1_sep_i64 arrayDemoX64Init
    arrayDemoX64_arrayPushSetGet_fnSpec.2 arrayRtBytes
    (arrayRtBase, boxNat 10, boxNat 20, boxNat 42, ()) (boxNat 62) P
    (by rw [arrayRtBytes_ok.1]; decide) (by decide) hspec (fun _ _ h => h) (by decide)

/-- Closed x86-64 machine execution of `ArrayDemo.baPushSetGet (4, 10, 20, 42)` on `arrayRtBytes`
(`0x1000#64`), returning `62#8` in `%al` and preserving `rtC0Inv` (`0` leaks). -/
theorem arrayDemoX64_baPushSetGet_run :
    letI : Host := arrayDemoX64Cert.host
    Eventually (step1 arrayDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.get64 .rax).setWidth 8 = 62#8 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ st' : RtC0State, rtC0Inv arrayRtBase st' m') ⋆
          x64Target.Exit 0x0ff8#64 (arrayDemoX64Cert.bound arrayDemoBaName) ⋆ emp))
      ⟨x64InitState (as := [i64, i64, i8, i8, i8])
          (arrayDemoX64Cert.bound arrayDemoBaName) arrayRtBytes
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
  have hrun := arrayDemoX64Cert.run_ret1_sep arrayDemoX64Init
    arrayDemoX64_baPushSetGet_fnSpec.2 arrayRtBytes
    (arrayRtBase, boxNat 4, 10#8, 20#8, 42#8, ()) 62#8 P
    (by rw [arrayRtBytes_ok.1]; decide) (by decide) hspec (fun _ _ h => h) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hrets, hmem⟩ =>
      ⟨hpc, x64_retsIn_i8 hrets, hmem⟩) hrun

/-- Closed x86-64 machine execution of `ArrayDemo.baCowSetGet` on a **shared (`rc = 2`)**
`ByteArray` `[10, 20]` with `v = 42#8` (`arrayCowBytes` @ `0x1000#64`): returns `62#8` in `%al`
**and** preserves the untouched original `[10, 20]` object (`sharedBaObjAfter`, `rc = 1`). -/
theorem arrayDemoX64_baCowSetGet_shared_run :
    letI : Host := arrayDemoX64Cert.host
    Eventually (step1 arrayDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.get64 .rax).setWidth 8 = 62#8 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ st' : RtC0State,
            (rtC0Inv arrayRtBase st' ⋆ lcnfObjMem sharedBaObjAfter) m') ⋆
          x64Target.Exit 0x0ff8#64 (arrayDemoX64Cert.bound arrayDemoBaCowName) ⋆ emp))
      ⟨x64InitState (as := [i64, i64, i8])
          (arrayDemoX64Cert.bound arrayDemoBaCowName) arrayCowBytes
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
  have hrun := arrayDemoX64Cert.run_ret1_sep arrayDemoX64Init
    arrayDemoX64_baCowSetGet_fnSpec.2 arrayCowBytes
    (arrayRtBase, sharedBaAddr, 42#8, ()) 62#8 P
    (by rw [arrayCowBytes_ok.1]; decide) (by decide) hspec (fun _ _ h => h) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hrets, hmem⟩ =>
      ⟨hpc, x64_retsIn_i8 hrets, hmem⟩) hrun

end LeanQbe.T.Amd64
