module

public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainCertFlat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public meta import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
public meta import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof
public meta import LeanQbe.T.LeanLCNF.LcnfC0LinkKit
public meta import Kraken.AArch64.Syntax

/-!
# AAPCS64 AArch64 Closed Linked Certificate for `FactLoop` (`LcnfC0LoopDemoCertArm64`)

Links `factLoopProgMod` (`FactLoop.factAcc`, `FactLoop.factStr`) onto the verified 86-function
pure-C0 runtime certificate `rtC0CoreArm64Cert`, producing closed `factLoopArm64Cert`,
`Defined`/`FnSpec` bridges for `factLoopEnv`, and a closed `Eventually` machine-execution witness
computing `25!` and formatting `"15511210043330985984000000"`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

compile_linked_chunks! factLoopArm64ProgCert armTarget armLayout armLegalTarget armLabelClean
  (lcnfProgMod factLoopTfs) 1 (ext := rtC0CoreArm64AllExt) (exits := rtExitSyms) (nX := 64)
  (maxBound := 2048) (maxDirs := 600) (flat := true)

/-- Closed 88-function AAPCS64 AArch64 linked certificate (`rtC0CoreMod ++ factLoopProgMod`). -/
noncomputable def factLoopArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      factLoopLinkedMod [] rtExitSyms 64 2048 :=
  linkRtC0Cert rtC0CoreArm64Cert factLoopArm64ProgCert (by t_kernel_rfl)

theorem factLoopArm64Cert_maxBound :
    factLoopArm64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" ≤ 2048 :=
  factLoopArm64Cert.bound_le_max _

theorem factLoopArm64Cert_factAcc_bound :
    factLoopArm64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factAcc" ≤ 2048 :=
  factLoopArm64Cert.bound_le_max _

theorem factLoopLinkedMod_arm64_legalSig :
    LegalSigAll armLegalTarget factLoopLinkedMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

private theorem factLoop_factStr_prog_mem :
    factLoopTfs.tf_1.toFn ∈ (lcnfProgMod factLoopTfs).fns := by
  simp [lcnfProgMod, factLoopTfs, Frontend.C0.tflatFnsToFns]

private theorem factLoop_factStr_linked_mem :
    factLoopTfs.tf_1.toFn ∈ factLoopLinkedMod.fns := by
  change factLoopTfs.tf_1.toFn ∈ (linkLcnfWithRtC0 factLoopTfs false).fns
  rw [linkLcnfWithRtC0_fns_eq]
  exact List.mem_append_right _ factLoop_factStr_prog_mem

theorem factLoopArm64_factStr_fnSpec :
    armTarget.Defined factLoopArm64Cert.host "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" ∧
      armTarget.FnSpec factLoopArm64Cert.host "l_LeanQbe_T_LeanLCNF_FactLoop_factStr"
        (factLoopEnv "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" [i64, i64] [i64])
        (factLoopArm64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr") 64 :=
  factLoopArm64Cert.fnSpec_host_of_legalSigAll factLoopEnv factLoopLinkedMod_acyclic
    factLoopLinkedMod_fns_wf factLoopLinkedMod_arm64_legalSig
    (fun fn hfn _ _ _ _ hp => factLoopLinkedMod_wp fn hfn hp)
    factLoop_factStr_linked_mem
    (factLoopEnv_noex _ factLoop_factStr_prog_mem)

/-- Zero-padding byte gap `[0x1000, 0x100000)` separating initial stack from `loopRtMem`. -/
@[expose] def loopArm64PadLen : Nat := 1044480

/-- Initial AArch64 memory containing the stack frame, padding gap, and `loopRtMem`. -/
@[expose] def loopArm64Dmem (b : Nat) : Mem 64 :=
  (stackZeros b ++ (List.replicate loopArm64PadLen 0 ++ loopRtBytes)).At
    (0x1000#64 - BitVec.ofNat 64 b)

private theorem loopRtBytes_len : loopRtBytes.length = 36056 := by
  simp only [loopRtBytes, List.length_append, bytes64_length, List.length_replicate,
    loopRtState.extraLen, loopRtState.globalsLen, loopRtState.freeListLen, loopRtState.workLen,
    rtExtraSlots, rtGlobalSlots, BigNumRt.rtNumClasses, loopRem,
    loopScrLimbs, loopScrCap]
  dsimp [nvBnHdrWords]
  decide

private theorem loopArm64Dmem_entry (b : Nat) (hb : b ≤ 2048) :
    loopArm64Dmem b =⋆ Eq loopRtMem ⋆ region (0x1000#64 - BitVec.ofNat 64 b) b ⋆
      Eq ((List.replicate loopArm64PadLen 0).At 0x1000#64) := by
  let padBytes : List UInt8 := List.replicate loopArm64PadLen 0
  let base0 : BitVec 64 := 0x1000#64 - BitVec.ofNat 64 b
  have hzs : (stackZeros b).length = b := stackZeros_length b
  have hpad : padBytes.length = 1044480 := List.length_replicate
  have hrt : loopRtBytes.length = 36056 := loopRtBytes_len
  have hlen2 : padBytes.length + loopRtBytes.length ≤ 2 ^ 64 := by
    rw [hpad, hrt]; decide
  have hlen1 : (stackZeros b).length + (padBytes ++ loopRtBytes).length ≤ 2 ^ 64 := by
    rw [List.length_append, hzs, hpad, hrt]; omega
  have h1 := Mem.At_append_sep (stackZeros b) (padBytes ++ loopRtBytes) base0 hlen1
  have hsp : base0 + BitVec.ofNat 64 (stackZeros b).length = 0x1000#64 := by
    rw [hzs]; exact BitVec.sub_add_cancel 0x1000#64 (BitVec.ofNat 64 b)
  rw [hsp] at h1
  have h2 := Mem.At_append_sep padBytes loopRtBytes 0x1000#64 hlen2
  have hbase : (0x1000#64 : BitVec 64) + BitVec.ofNat 64 padBytes.length = loopRtBase := by
    rw [hpad]; rfl
  rw [hbase] at h2
  have hmem :
      (Eq ((stackZeros b).At base0) ⋆
        (Eq (padBytes.At 0x1000#64) ⋆ Eq (loopRtBytes.At loopRtBase)))
        (loopArm64Dmem b) := by
    have he0 : Eq ((stackZeros b ++ (padBytes ++ loopRtBytes)).At base0) (loopArm64Dmem b) := rfl
    rw [h1, h2] at he0
    exact he0
  have hreg :
      (region base0 b ⋆ (Eq (padBytes.At 0x1000#64) ⋆ Eq loopRtMem)) (loopArm64Dmem b) :=
    sep_mono (fun _ hm => ⟨stackZeros b, hzs, hm.symm⟩) hmem
  exact sep_cast hreg (by ac_rfl)

/-- Closed AAPCS64 AArch64 concrete execution of `FactLoop.factStr (boxNat 25)` returning the
`"25!"` string `"15511210043330985984000000"` (`fact25Bytes`). -/
theorem factLoopArm64_fact25_run :
    let b := factLoopArm64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr"
    let args : Tup Val [i64, i64] := (loopRtBase, boxNat 25, ())
    let s0 : MachineData := { armInitState b [] args with dmem := loopArm64Dmem b }
    letI : Host := factLoopArm64Cert.host
    Eventually (step1 factLoopArm64Cert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        ∃ (s : BitVec 64) (st' : RtC0State) (objs' : List LcnfObj)
          (scrLimbs' : List (BitVec 64)) (m' : Mem 64),
          st.data.regs.X0.toBitVec = s ∧
          s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
          st'.PreservesMeta (b2rState loopRtState) ∧ st'.rem ≤ loopRtState.rem ∧
          StrCanon (mkStrObj s 1#32 27 fact25Bytes 26) ∧
          (rtC0Inv loopRtBase st' ⋆
            lcnfObjMem (mkStrObj s 1#32 27 fact25Bytes 26) ⋆
            lcnfHeap objs' ⋆
            cell64 (loopRtBase + 33672#64) loopScr ⋆
            cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 loopScr scrLimbs') m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (0x1000#64 - BitVec.ofNat 64 b) b ⋆
            region 0x1000#64 loopArm64PadLen))
      ⟨s0, Labels.label "l_LeanQbe_T_LeanLCNF_FactLoop_factStr"⟩ := by
  letI : Host := factLoopArm64Cert.host
  let b := factLoopArm64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr"
  let args : Tup Val [i64, i64] := (loopRtBase, boxNat 25, ())
  let s0 : MachineData := { armInitState b [] args with dmem := loopArm64Dmem b }
  let padR : Mem 64 → Prop := Eq ((List.replicate loopArm64PadLen 0).At 0x1000#64)
  let Q : Post [i64] := fun (s, ()) m' =>
    s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
    ∃ (st' : RtC0State) (objs' : List LcnfObj) (scrLimbs' : List (BitVec 64)),
      st'.PreservesMeta (b2rState loopRtState) ∧ st'.rem ≤ loopRtState.rem ∧
      StrCanon (mkStrObj s 1#32 27 fact25Bytes 26) ∧
      (rtC0Inv loopRtBase st' ⋆
        lcnfObjMem (mkStrObj s 1#32 27 fact25Bytes 26) ⋆
        lcnfHeap objs' ⋆
        cell64 (loopRtBase + 33672#64) loopScr ⋆
        cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
        array64 loopScr scrLimbs') m'
  have hb : b ≤ 2048 := factLoopArm64Cert_maxBound
  have hsp : s0.regs.SP.toBitVec = 0x1000#64 := armInit.get_sp b [] args
  have hargs : armTarget.ArgsIn args s0 := armInit.argsIn b [] args rfl
  have hra : s0.regs.X30 = (0x1234 : Int64).toUInt64 :=
    UInt64.toBitVec_inj.mp (armInit.raReg b [] args)
  have hspAl : s0.regs.SP.toNat % 16 = 0 := by
    have ht : s0.regs.SP.toBitVec.toNat = 0x1000 := by rw [hsp]; rfl
    change s0.regs.SP.toBitVec.toNat % 16 = 0
    exact ht ▸ (by decide : 0x1000 % 16 = 0)
  have hmem :
      s0.dmem =⋆ Eq loopRtMem ⋆ region (s0.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ padR := by
    rw [hsp]; exact loopArm64Dmem_entry b hb
  have hspec :
      factLoopEnv "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" [i64, i64] [i64]
        args loopRtMem Q (fun _ _ _ _ => False) :=
    fact25_str_spec Q (fun _ _ _ _ => False) fun s st' objs' scrLimbs' m' hs0 hs8 hpr hrem hcan
        hm' =>
      ⟨hs0, hs8, st', objs', scrLimbs', hpr, hrem, hcan, hm'⟩
  have hrun :=
    arm64_of_returns factLoopArm64_factStr_fnSpec.2 hspec s0 (0x1234 : Int64) padR
      hargs hra hspAl hmem
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨s, ⟨⟩⟩, m', ⟨hs0, hs8, st', objs', scrLimbs', hpr, hrem, hcan, hm'⟩,
    hrets, hdmem⟩
  rw [hsp] at hdmem
  have hdmem' :
      (st.data.dmem =⋆ Eq m' ⋆ region (0x1000#64 - BitVec.ofNat 64 b) b ⋆
        region 0x1000#64 loopArm64PadLen) :=
    sep_mono_r (fun _ h => ⟨List.replicate loopArm64PadLen 0, List.length_replicate, h.symm⟩) hdmem
  exact ⟨hpc, s, st', objs', scrLimbs', m', armInit.retsIn_singleton s st.data hrets,
    hs0, hs8, hpr, hrem, hcan, hm', hdmem'⟩

end LeanQbe.T.Arm64
