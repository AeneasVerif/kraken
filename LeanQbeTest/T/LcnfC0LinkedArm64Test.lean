module

public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0DemoProof
public import LeanQbe.T.Logic.MemLemmas
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0Demo

/-!
# End-to-End AAPCS64 AArch64 Linked Certificate & Execution Suite (`demoNatStrLinkedMod`)

Links `demoNatStrProgMod` (`DemoNatStr.{addNat, addToStr, fmtSumTagged}`, `3` fns) onto the
pre-verified `86`-function `rtC0CoreArm64Cert` (`LcnfC0FullCertArm64`) via `LcnfC0LinkKit`, checks
architecture isolation (`0` X64/Amd64 imports), bridges `demoNatStrLinkedMod_moduleOk` to
`armTarget.Defined` + `armTarget.FnSpec`, and proves closed concrete AArch64 `Eventually`
(`step1 demoNatStrArm64Cert.host.exe`, `XPost := False`) execution witnesses for all three
functions:

1. `addNat` on `nvBnMem` (`[2^64-1, 1] + [5, 2]` MPZs → `[4, 4]` MPZ via `lcnf_nat_slow` → R0).
2. `addToStr` on `nvDagMem` (`(boxNat 17, boxNat 25) → "42"` via `addNat` + `lcnf_nat_to_str`).
3. `fmtSumTagged` on `demoTagMem` (`("sum=", 17, 25) → "sum=42"` via `addToStr` +
   in-place `lcnf_string_append` + header RC load + `lcnf_dec_ref_cold`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0LinkedArm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64 Kraken

/-! ## 1. Architecture Isolation & Program Compilation + Linking -/

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let x64 := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64.isEmpty then
    throwError "LcnfC0LinkedArm64Test leaked X64/Amd64 imports: {x64.toList}"

#guard demoNatStrLinkedMod.fns.length == 89
#guard demoNatStrLinkedMod.externs.isEmpty
#guard demoNatStrLinkedMod.exits == ["lcnf_panic"]
#guard demoNatStrLinkedMod.checkAcyclic
#guard checkLegalSigAll armLegalTarget demoNatStrLinkedMod.fns

compile_linked_chunks! demoNatStrArm64ProgCert armTarget armLayout armLegalTarget armLabelClean
  demoNatStrProgMod 2 (ext := rtC0CoreArm64AllExt) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 600)

/-- Full `89`-function AAPCS64 AArch64 linked certificate combining `rtC0CoreArm64Cert` (`86` fns)
and `demoNatStrArm64ProgCert` (`3` fns) via `LcnfC0LinkKit.linkRtC0Cert`. -/
@[expose] noncomputable def demoNatStrArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      demoNatStrLinkedMod [] rtExitSyms 64 (Nat.max 2048 2048) :=
  linkRtC0Cert rtC0CoreArm64Cert demoNatStrArm64ProgCert (by t_kernel_rfl)

theorem demoNatStrArm64Cert_bounds_len : demoNatStrArm64Cert.bounds.length = 89 := by
  exact demoNatStrArm64Cert.bounds_length.trans (by decide)

theorem demoNatStrArm64Cert_bounds_le :
    demoNatStrArm64Cert.bounds.all (fun p => Nat.ble p.2 2048) = true := by
  t_kernel_rfl

private theorem demoNatStrLinkedMod_arm_legalSig :
    LegalSigAll armLegalTarget demoNatStrLinkedMod.fns :=
  linkLcnfWithRtC0_legalSigAll armLegalTarget demoNatStrTfs (by t_kernel_rfl) (by decide)

/-! ## 2. Machine-Level `armTarget.Defined` + `armTarget.FnSpec` Bridges -/

private theorem mem_tf0 : demoNatStrTfs.tf_0.toFn ∈ (lcnfProgMod demoNatStrTfs).fns := by
  rw [demoNatStrProgMod_fns_eq]
  exact List.mem_cons_self

private theorem mem_tf1 : demoNatStrTfs.tf_1.toFn ∈ (lcnfProgMod demoNatStrTfs).fns := by
  rw [demoNatStrProgMod_fns_eq]
  simp

private theorem mem_tf2 : demoNatStrTfs.tf_2.toFn ∈ (lcnfProgMod demoNatStrTfs).fns := by
  rw [demoNatStrProgMod_fns_eq]
  simp

theorem demoNatStrArm64_addNat_fnSpec :
    armTarget.Defined demoNatStrArm64Cert.host "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat" ∧
    armTarget.FnSpec demoNatStrArm64Cert.host "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat"
      addNatSpec (demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat") 64 :=
  linkRtC0Cert_fnSpec_of_spec demoNatStrArm64Cert demoNatStrEnv
    demoNatStrLinkedMod_checkAcyclic demoNatStrLinkedMod_arm_legalSig demoNatStrProgMod_wp
    mem_tf0 (fun _ _ _ _ _ h => demoNatStrEnv_addNat_noex h)
    (fun _ _ _ _ h => demoNatStrEnv_addNat h)

theorem demoNatStrArm64_addToStr_fnSpec :
    armTarget.Defined demoNatStrArm64Cert.host "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr" ∧
    armTarget.FnSpec demoNatStrArm64Cert.host "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr"
      addToStrSpec (demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr") 64 :=
  linkRtC0Cert_fnSpec_of_spec demoNatStrArm64Cert demoNatStrEnv
    demoNatStrLinkedMod_checkAcyclic demoNatStrLinkedMod_arm_legalSig demoNatStrProgMod_wp
    mem_tf1 (fun _ _ _ _ _ h => demoNatStrEnv_addToStr_noex h)
    (fun _ _ _ _ h => demoNatStrEnv_addToStr h)

theorem demoNatStrArm64_fmtSumTagged_fnSpec :
    armTarget.Defined demoNatStrArm64Cert.host "l_LeanQbe_T_LeanLCNF_DemoNatStr_fmtSumTagged" ∧
    armTarget.FnSpec demoNatStrArm64Cert.host "l_LeanQbe_T_LeanLCNF_DemoNatStr_fmtSumTagged"
      fmtSumTaggedSpec
      (demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_fmtSumTagged") 64 :=
  linkRtC0Cert_fnSpec_of_spec demoNatStrArm64Cert demoNatStrEnv
    demoNatStrLinkedMod_checkAcyclic demoNatStrLinkedMod_arm_legalSig demoNatStrProgMod_wp
    mem_tf2 (fun _ _ _ _ _ h => demoNatStrEnv_fmtSumTagged_noex h)
    (fun _ _ _ _ h => demoNatStrEnv_fmtSumTagged h)

/-! ## 3. Closed Concrete AArch64 `Eventually` Execution Witnesses -/

private theorem mem_At_disjoint_armInitMem {base : BitVec 64} {bs : List UInt8}
    {n b : Nat} (hbase : 0x1000 ≤ base.toNat) (hfit : base.toNat + n < 2 ^ 64)
    (hlen : bs.length = n) (hb : b ≤ 2048) :
    (bs.At base).inter (armInitMem b []) = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  intro k
  rw [inter_eq, mem_inter_iff]
  rintro ⟨h1, h2⟩
  rw [mem_At_iff] at h1
  rw [armInitMem, mem_At_iff] at h2
  rcases h1 with ⟨i, hi, rfl⟩
  rcases h2 with ⟨j, hj, heq⟩
  rw [hlen] at hi
  simp only [List.length_append, List.length_nil, Nat.add_zero, stackZeros_length] at hj
  have hL : (base + BitVec.ofNat 64 i).toNat ≥ 0x1000 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hR : ((0x1000#64 - BitVec.ofNat 64 b) + BitVec.ofNat 64 j).toNat < 0x1000 := by
    have hsp : (0x1000#64 : BitVec 64).toNat = 0x1000 := by decide
    have hsub : (0x1000#64 - BitVec.ofNat 64 b).toNat = 0x1000 - b := by
      rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
      rw [hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [heq] at hL
  omega

private theorem armInitMem_empty_entry {b : Nat} (hb : b ≤ 2048) :
    region (0x1000#64 - BitVec.ofNat 64 b) b (armInitMem b []) := by
  have hm := armInitMem_entry b [] hb (by decide)
  have hnil : ([].At 0x1000#64 : Mem 64) = ∅ := by
    rw [eq_empty_iff_forall_not_mem]
    intro k hk
    rw [mem_At_iff] at hk
    rcases hk with ⟨_, hi, _⟩
    simp at hi
  rw [hnil, eq_empty_eq_emp, emp_sep, sep_emp] at hm
  simp only [Target.Entry, armTarget, armFrameTarget, armFramePreds, region_zero,
    sep_emp] at hm
  exact hm

private theorem slab_machine_dmem_entry {as : List Ty} {mem : Mem 64} (b : Nat)
    (hb : b ≤ 2048) (hdisj : mem.inter (armInitMem b []) = ∅) (args : Tup Val as) :
    ((mem.union (armInitState b [] args).dmem) =⋆
      Eq mem ⋆
      region ((armInitState b [] args).regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆
      emp) := by
  have hsp : (armInitState (as := as) b [] args).regs.SP.toBitVec = 0x1000#64 :=
    armInit.get_sp b [] args
  have hdmem : (armInitState (as := as) b [] args).dmem = armInitMem b [] := by
    dsimp only [armInitState]
  rw [hsp, hdmem, sep_emp]
  exact ⟨mem, armInitMem b [], rfl, hdisj, rfl, armInitMem_empty_entry hb⟩

private theorem slab_machine_argsIn {as : List Ty} (mem : Mem 64) (b : Nat) (args : Tup Val as)
    (hassign : (armTarget.toIsa.assignArgs as).isSome = true) :
    armTarget.ArgsIn args { armInitState b [] args with
      dmem := mem.union (armInitState b [] args).dmem } :=
  armInit.argsIn b [] args hassign

private theorem slab_machine_x30_ok {as : List Ty} (mem : Mem 64) (b : Nat) (args : Tup Val as) :
    { armInitState b [] args with
      dmem := mem.union (armInitState b [] args).dmem }.regs.X30 = (0x1234 : Int64).toUInt64 :=
  UInt64.toBitVec_inj.mp (armInit.raReg b [] args)

private theorem slab_machine_sp_ok {as : List Ty} (mem : Mem 64) (b : Nat) (args : Tup Val as) :
    { armInitState b [] args with
      dmem := mem.union (armInitState b [] args).dmem }.regs.SP.toNat % 16 = 0 := by
  have hsp : (armInitState (as := as) b [] args).regs.SP.toBitVec = 0x1000#64 :=
    armInit.get_sp b [] args
  change (armInitState (as := as) b [] args).regs.SP.toBitVec.toNat % 16 = 0
  rw [hsp]
  decide

private theorem nvBnMem_disjoint_armInitMem {b : Nat} (hb : b ≤ 2048) :
    nvBnMem.inter (armInitMem b []) = ∅ := by
  have hlen : (nvBnRtBytes ++ nvBnHeapBytes).length = 34392 := by
    simp only [List.length_append, nvBnRtBytes, nvBnHeapBytes, nvBnObjBytes, bytes64_length,
      List.length_cons, List.length_nil, List.length_replicate, nvBnHdrWords, nvBnRtState,
      nvBnWorkCap, nvBnRem, nvBnScrCap, nvBnScrLimbs, rtExtraSlots, rtGlobalSlots,
      nvBnNatA, nvBnNatB, nvBnIntNegA, nvBnIntPosB]
    decide
  exact mem_At_disjoint_armInitMem (by decide) (by decide) hlen hb

private theorem nvDagMem_disjoint_armInitMem {b : Nat} (hb : b ≤ 2048) :
    nvDagMem.inter (armInitMem b []) = ∅ := by
  have hlen : (nvRtBytes ++ nvDagBytes).length = 33912 := by
    simp only [List.length_append, nvRtBytes, nvDagBytes, nvObjABytes, nvObjBBytes, nvObjCBytes,
      nvObjPBytes, nvObjUBytes, bytes64_length, List.length_cons, List.length_nil,
      List.length_replicate, nvHdrWords, nvRtState, initRtC0State, nvWorkCap, nvRem,
      rtExtraSlots, rtGlobalSlots, rtNumClasses, nvObjA, nvObjB, nvObjC, nvObjP, nvObjU]
  exact mem_At_disjoint_armInitMem (by decide) (by decide) hlen hb

private theorem demoTagMem_disjoint_armInitMem {b : Nat} (hb : b ≤ 2048) :
    demoTagMem.inter (armInitMem b []) = ∅ := by
  have hlen : ((nvRtBytes ++ nvDagBytes) ++ demoTagBytes).length = 33960 := by
    have h1 : (nvRtBytes ++ nvDagBytes).length = 33912 := by
      simp only [List.length_append, nvRtBytes, nvDagBytes, nvObjABytes, nvObjBBytes,
        nvObjCBytes, nvObjPBytes, nvObjUBytes, bytes64_length, List.length_cons, List.length_nil,
        List.length_replicate, nvHdrWords, nvRtState, initRtC0State, nvWorkCap, nvRem,
        rtExtraSlots, rtGlobalSlots, rtNumClasses, nvObjA, nvObjB, nvObjC, nvObjP, nvObjU]
    have h2 : demoTagBytes.length = 48 := by decide
    rw [List.length_append, h1, h2]
  exact mem_At_disjoint_armInitMem (by decide) (by decide) hlen hb

private theorem nvBnRtWf_ok :
    BigNumRtWf nvBnRtBase nvBnRtState nvBnScr nvBnScrLimbs := by
  have hlen : nvBnScrLimbs.length = 32 := List.length_replicate
  refine ⟨?_, by decide, by decide, by decide, ?_, ?_⟩
  · unfold BigNumRt.RtC0State.Bounded48
    decide
  · rw [hlen]
    decide
  · rw [hlen]
    decide

private theorem nvBnNatA_rep_ok : natRep nvBnAddrNatA nvValNatA nvBnObjs := by
  have hge : ¬(nvValNatA < 2 ^ 63) := by decide
  simp only [natRep, hge, ↓reduceIte]
  refine ⟨by decide, nvBnNatA, by simp [nvBnObjs], rfl, ?_, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, by decide⟩
  · unfold BigNumRt.LcnfObj.Wf BigNumRt.LcnfObj.totalBytes
    decide
  · simp [nvBnNatA, limbsVal, nvValNatA]

private theorem nvBnNatB_rep_ok : natRep nvBnAddrNatB nvValNatB nvBnObjs := by
  have hge : ¬(nvValNatB < 2 ^ 63) := by decide
  simp only [natRep, hge, ↓reduceIte]
  refine ⟨by decide, nvBnNatB, by simp [nvBnObjs], rfl, ?_, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, by decide⟩
  · unfold BigNumRt.LcnfObj.Wf BigNumRt.LcnfObj.totalBytes
    decide
  · simp [nvBnNatB, limbsVal, nvValNatB]

private theorem natToDecimalBytes_42 : natToDecimalBytes 42 = [52, 50] := by
  rw [natToDecimalBytes, ite_eq_right (by decide),
    natDigitsRev.eq_def, dite_eq_right (by decide),
    natDigitsRev.eq_def, dite_eq_right (by decide),
    natDigitsRev.eq_def, dite_eq_left (by decide)]
  decide

/-- Closed concrete AArch64 machine execution (`Eventually (step1 demoNatStrArm64Cert.host.exe)`)
of Lean `LCNF` `DemoNatStr.addNat` adding 2-limb MPZs `[2^64-1, 1] + [5, 2]` on `nvBnMem`,
returning heap MPZ `natRep p (nvValNatA + nvValNatB) objs'` (`XPost := False`). -/
theorem demoNatStrArm64_addNat_bignum_run :
    let b := demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat"
    let args : Tup Val [i64, i64, i64] := (nvBnRtBase, nvBnAddrNatA, nvBnAddrNatB, ())
    let s0 : MachineData :=
      { armInitState b [] args with dmem := nvBnMem.union (armInitState b [] args).dmem }
    letI : Host := demoNatStrArm64Cert.host
    Eventually (step1 demoNatStrArm64Cert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        ∃ (p : BitVec 64) (st' : BigNumRt.RtC0State) (scrLimbs' : List (BitVec 64))
          (objs' : List BigNumRt.LcnfObj) (obj : BigNumRt.LcnfObj) (m' : Mem 64),
          st.data.regs.X0.toBitVec = p ∧
          (p &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = p ∧
          obj.tag = BigNumRt.mpzTag ∧ obj.other = 0 ∧
          natRep p (nvValNatA + nvValNatB) objs' ∧
          (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆
            BigNumRt.lcnfHeap objs') m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (0x1000#64 - BitVec.ofNat 64 b) b ⋆ emp))
      ⟨s0, Labels.label "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat"⟩ := by
  letI : Host := demoNatStrArm64Cert.host
  let b := demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat"
  let args : Tup Val [i64, i64, i64] := (nvBnRtBase, nvBnAddrNatA, nvBnAddrNatB, ())
  let s0 : MachineData :=
    { armInitState b [] args with dmem := nvBnMem.union (armInitState b [] args).dmem }
  let Q : Post [i64] := fun (r, ()) m' =>
    ∃ (st' : BigNumRt.RtC0State) (scrLimbs' : List (BitVec 64))
      (objs' : List BigNumRt.LcnfObj) (obj : BigNumRt.LcnfObj),
      (r &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = r ∧
      obj.tag = BigNumRt.mpzTag ∧ obj.other = 0 ∧
      natRep r (nvValNatA + nvValNatB) objs' ∧
      (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ BigNumRt.lcnfHeap objs') m'
  have hb : b ≤ 2048 :=
    Nat.le_trans (demoNatStrArm64Cert.bound_le_max "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat")
      (by decide)
  have hspec : addNatSpec args nvBnMem Q (fun _ _ _ _ => False) := by
    dsimp only [addNatSpec]
    rw [ite_eq_right (by decide)]
    refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, emp, nvBnRtWf_ok,
      by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
    have hmem : (1#64 : BitVec 64).toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] := by decide
    simp only [hmem, ↓reduceIte]
    refine ⟨nvValNatA, nvValNatB, nvBnNatA_rep_ok, Or.inr nvBnNatB_rep_ok, ?_, ?_⟩
    · dsimp only [natArithOk, natArithRes]
      have hcap : nvBnScrLimbs.length = 32 := List.length_replicate
      rw [hcap]
      refine ⟨by decide, by decide, fun _ => Or.inr (by decide)⟩
    · intro res st' scrLimbs' objs' m' _ _ _ hpost hm'
      rw [sep_emp] at hm'
      have hrep : natRep res (nvValNatA + nvValNatB) objs' := by
        simpa [natArithPost, natArithRes] using hpost.1
      have hbig : ¬(nvValNatA + nvValNatB < 2 ^ 63) := by decide
      have hrep' := hrep
      simp only [natRep, hbig, ↓reduceIte] at hrep'
      rcases hrep' with ⟨halign, obj, hobjMem, hobjAddr, _, htag, hoth, _⟩
      exact ⟨st', scrLimbs', objs', obj, halign, hobjMem, hobjAddr, htag, hoth, hrep, hm'⟩
  have hrun := arm64_of_returns demoNatStrArm64_addNat_fnSpec.2 hspec s0 (0x1234 : Int64) emp
    (slab_machine_argsIn nvBnMem b args rfl) (slab_machine_x30_ok nvBnMem b args)
    (slab_machine_sp_ok nvBnMem b args)
    (slab_machine_dmem_entry b hb (nvBnMem_disjoint_armInitMem hb) args)
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨p, ⟨⟩⟩, m', ⟨st', scrLimbs', objs', obj, h1, h2, h3, h4, h5, h6, hinv⟩,
    hrets, hm'⟩
  have hsp : s0.regs.SP.toBitVec = 0x1000#64 := armInit.get_sp b [] args
  have hx0 : st.data.regs.X0.toBitVec = p :=
    armInit.retsIn_singleton p st.data hrets
  rw [hsp] at hm'
  exact ⟨hpc, p, st', scrLimbs', objs', obj, m', hx0, h1, h2, h3, h4, h5, h6, hinv, hm'⟩

/-- Closed concrete AArch64 machine execution (`Eventually (step1 demoNatStrArm64Cert.host.exe)`)
of Lean `LCNF` `DemoNatStr.addToStr` (`boxNat 17`, `boxNat 25`) on `nvDagMem`, calling `addNat` +
`lcnf_nat_to_str` → `lcnf_alloc` and returning `"42"` (`[52, 50]`, `XPost := False`). -/
theorem demoNatStrArm64_addToStr_42_run :
    let b := demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr"
    let args : Tup Val [i64, i64, i64] := (nvRtBase, boxNat 17, boxNat 25, ())
    let s0 : MachineData :=
      { armInitState b [] args with dmem := nvDagMem.union (armInitState b [] args).dmem }
    letI : Host := demoNatStrArm64Cert.host
    Eventually (step1 demoNatStrArm64Cert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        ∃ (s : BitVec 64) (st' : RtC0State) (m' : Mem 64),
          st.data.regs.X0.toBitVec = s ∧
          s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
          (rtC0Inv nvRtBase st' ⋆
            lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2) ⋆
            lcnfHeap nvDagObjs) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (0x1000#64 - BitVec.ofNat 64 b) b ⋆ emp))
      ⟨s0, Labels.label "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr"⟩ := by
  letI : Host := demoNatStrArm64Cert.host
  let b := demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr"
  let args : Tup Val [i64, i64, i64] := (nvRtBase, boxNat 17, boxNat 25, ())
  let s0 : MachineData :=
    { armInitState b [] args with dmem := nvDagMem.union (armInitState b [] args).dmem }
  let Q : Post [i64] := fun (s, ()) m' =>
    s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
    ∃ st' : RtC0State,
      (rtC0Inv nvRtBase st' ⋆
        lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2) ⋆
        lcnfHeap nvDagObjs) m'
  have hb : b ≤ 2048 :=
    Nat.le_trans (demoNatStrArm64Cert.bound_le_max "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr")
      (by decide)
  have hspec : addToStrSpec args nvDagMem Q (fun _ _ _ _ => False) := by
    have hm : (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap nvDagObjs ⋆ emp) nvDagMem := by
      rw [sep_emp]
      exact nvDagMem_ok
    refine ⟨17, 25, rfl, rfl, by decide, nvRtState, nvDagObjs, emp,
      (fun o ho => demoTagObjs_heapRcInv.1 o (List.mem_cons_of_mem _ ho)), hm, ?_⟩
    rw [show (17 + 25 : Nat) = 42 by rfl, natToDecimalBytes_42]
    have hrem : strAllocBytes ([52, 50].length + 1) ≤ nvRtState.rem := by
      unfold RtC0State.rem
      simp only [nvRtState, initRtC0State, nvRtBase, nvWorkCap, nvRem]
      decide
    refine ⟨Or.inr hrem, fun s st' m' hs0 hs8 _ _ _ hm' => ?_⟩
    rw [sep_emp] at hm'
    exact ⟨hs0, hs8, st', hm'⟩
  have hrun := arm64_of_returns demoNatStrArm64_addToStr_fnSpec.2 hspec s0 (0x1234 : Int64) emp
    (slab_machine_argsIn nvDagMem b args rfl) (slab_machine_x30_ok nvDagMem b args)
    (slab_machine_sp_ok nvDagMem b args)
    (slab_machine_dmem_entry b hb (nvDagMem_disjoint_armInitMem hb) args)
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨s, ⟨⟩⟩, m', ⟨hs0, hs8, st', hinv⟩, hrets, hm'⟩
  have hsp : s0.regs.SP.toBitVec = 0x1000#64 := armInit.get_sp b [] args
  have hx0 : st.data.regs.X0.toBitVec = s :=
    armInit.retsIn_singleton s st.data hrets
  rw [hsp] at hm'
  exact ⟨hpc, s, st', m', hx0, hs0, hs8, hinv, hm'⟩

/-- Closed concrete AArch64 machine execution (`Eventually (step1 demoNatStrArm64Cert.host.exe)`)
of Lean `LCNF` `DemoNatStr.fmtSumTagged` (`"sum="`, `boxNat 17`, `boxNat 25`) on `demoTagMem`,
returning `demoTagAddr` holding `"sum=42"` (`XPost := False`). -/
theorem demoNatStrArm64_fmtSumTagged_run :
    let b := demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_fmtSumTagged"
    let args : Tup Val [i64, i64, i64, i64] :=
      (nvRtBase, demoTagAddr, boxNat 17, boxNat 25, ())
    let s0 : MachineData :=
      { armInitState b [] args with dmem := demoTagMem.union (armInitState b [] args).dmem }
    letI : Host := demoNatStrArm64Cert.host
    Eventually (step1 demoNatStrArm64Cert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        st.data.regs.X0.toBitVec = demoTagAddr ∧
        ∃ (st' : RtC0State) (objs' : List LcnfObj) (m' : Mem 64),
          mkStrObj demoTagAddr 1#32 16 [115, 117, 109, 61, 52, 50] 6 ∈ objs' ∧
          (rtC0Inv nvRtBase st' ⋆ lcnfHeap objs') m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (0x1000#64 - BitVec.ofNat 64 b) b ⋆ emp))
      ⟨s0, Labels.label "l_LeanQbe_T_LeanLCNF_DemoNatStr_fmtSumTagged"⟩ := by
  letI : Host := demoNatStrArm64Cert.host
  let b := demoNatStrArm64Cert.bound "l_LeanQbe_T_LeanLCNF_DemoNatStr_fmtSumTagged"
  let args : Tup Val [i64, i64, i64, i64] :=
    (nvRtBase, demoTagAddr, boxNat 17, boxNat 25, ())
  let s0 : MachineData :=
    { armInitState b [] args with dmem := demoTagMem.union (armInitState b [] args).dmem }
  let Q : Post [i64] := fun (ret, ()) m' =>
    ret = demoTagAddr ∧
    ∃ (st' : RtC0State) (objs' : List LcnfObj),
      mkStrObj demoTagAddr 1#32 16 [115, 117, 109, 61, 52, 50] 6 ∈ objs' ∧
      (rtC0Inv nvRtBase st' ⋆ lcnfHeap objs') m'
  have hb : b ≤ 2048 :=
    Nat.le_trans (demoNatStrArm64Cert.bound_le_max "l_LeanQbe_T_LeanLCNF_DemoNatStr_fmtSumTagged")
      (by decide)
  have hspec : fmtSumTaggedSpec args demoTagMem Q (fun _ _ _ _ => False) := by
    have hm : (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap demoTagObjs ⋆ emp) demoTagMem := by
      rw [sep_emp]
      exact demoTagMem_ok
    have hrem : strAllocBytes ((natToDecimalBytes (17 + 25)).length + 1) ≤ nvRtState.rem := by
      rw [show (17 + 25 : Nat) = 42 by rfl, natToDecimalBytes_42]
      unfold RtC0State.rem
      simp only [nvRtState, initRtC0State, nvRtBase, nvWorkCap, nvRem]
      decide
    have hcap : (strPayload demoTagObj ++ natToDecimalBytes (17 + 25)).length + 1 ≤
        demoTagObj.cap := by
      rw [show (17 + 25 : Nat) = 42 by rfl, natToDecimalBytes_42]
      decide
    have hwc : demoTagObjs.length + 1 ≤ nvRtState.workCap := by decide
    refine ⟨17, 25, demoTagObj, nvRtState, demoTagObjs, emp, rfl, rfl, by decide,
      List.mem_cons_self, rfl, demoTagObj_canon, rfl, hcap, demoTagObjs_heapRcInv, hwc,
      Or.inr hrem, hm, ?_⟩
    intro st' objs' m' _ _ rObj _ hrIn hm'
    rw [sep_emp] at hm'
    refine ⟨rfl, st', objs', ?_, hm'⟩
    have hPay : strPayload demoTagObj ++ natToDecimalBytes (17 + 25) =
        [115, 117, 109, 61, 52, 50] := by
      rw [show (17 + 25 : Nat) = 42 by rfl, natToDecimalBytes_42]
      decide
    have hLen : (demoTagObj.strLen + (natToDecimalBytes (17 + 25)).length) % 2 ^ 64 = 6 := by
      rw [show (17 + 25 : Nat) = 42 by rfl, natToDecimalBytes_42]
      decide
    have hrDef : rObj = mkStrObj demoTagAddr 1#32 16 [115, 117, 109, 61, 52, 50] 6 := by
      change mkStrObj demoTagAddr 1#32 demoTagObj.cap
          (strPayload demoTagObj ++ natToDecimalBytes (17 + 25))
          ((demoTagObj.strLen + (natToDecimalBytes (17 + 25)).length) % 2 ^ 64) =
        mkStrObj demoTagAddr 1#32 16 [115, 117, 109, 61, 52, 50] 6
      rw [hPay, hLen]
      rfl
    exact hrDef ▸ hrIn
  have hrun := arm64_of_returns demoNatStrArm64_fmtSumTagged_fnSpec.2 hspec s0 (0x1234 : Int64) emp
    (slab_machine_argsIn demoTagMem b args rfl) (slab_machine_x30_ok demoTagMem b args)
    (slab_machine_sp_ok demoTagMem b args)
    (slab_machine_dmem_entry b hb (demoTagMem_disjoint_armInitMem hb) args)
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨ret, ⟨⟩⟩, m', ⟨hret, st', objs', hrIn, hinv⟩, hrets, hm'⟩
  have hsp : s0.regs.SP.toBitVec = 0x1000#64 := armInit.get_sp b [] args
  have hx0 : st.data.regs.X0.toBitVec = demoTagAddr := by
    have hbit := armInit.retsIn_singleton ret st.data hrets
    rw [hret] at hbit
    exact hbit
  rw [hsp] at hm'
  exact ⟨hpc, hx0, st', objs', m', hrIn, hinv, hm'⟩

/-! ## 4. Standard-Axiom Audit (`≤ std3`) -/

#print axioms demoNatStrLinkedMod_moduleOk
#print axioms demoNatStrArm64Cert
#print axioms demoNatStrArm64Cert_bounds_len
#print axioms demoNatStrArm64Cert_bounds_le
#print axioms demoNatStrArm64_addNat_fnSpec
#print axioms demoNatStrArm64_addToStr_fnSpec
#print axioms demoNatStrArm64_fmtSumTagged_fnSpec
#print axioms demoNatStrArm64_addNat_bignum_run
#print axioms demoNatStrArm64_addToStr_42_run
#print axioms demoNatStrArm64_fmtSumTagged_run

end LeanQbeTest.T.LcnfC0LinkedArm64Test
