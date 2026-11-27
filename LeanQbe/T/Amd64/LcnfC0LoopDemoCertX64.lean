module

public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof
public import LeanQbe.T.Amd64.LcnfC0FullCertX64
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainCertFlat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Amd64.LcnfC0FullCertX64
public meta import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
public meta import LeanQbe.T.LeanLCNF.LcnfC0LinkKit
public meta import Kraken.X64.Syntax

/-!
# SysV x86-64 Closed Linked Certificate for `FactLoop` (`LcnfC0LoopDemoCertX64`)

Links `factLoopProgMod` (`FactLoop.factAcc`, `FactLoop.factStr`) onto the verified 86-function
pure-C0 runtime certificate `rtC0CoreCert`, producing closed `factLoopX64Cert`, `Defined`/`FnSpec`
bridges for `factLoopEnv`, and a closed `Eventually` machine-execution witness computing `25!`
and formatting `"15511210043330985984000000"`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

compile_linked_chunks! factLoopX64ProgCert x64Target x64Layout x64LegalTarget x64LabelClean
  (lcnfProgMod factLoopTfs) 1 (ext := rtC0CoreAllExt) (exits := rtExitSyms) (nX := 64)
  (maxBound := 2048) (maxDirs := 600) (flat := true)

/-- Closed 88-function SysV x86-64 linked certificate (`rtC0CoreMod ++ factLoopProgMod`). -/
noncomputable def factLoopX64Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      factLoopLinkedMod [] rtExitSyms 64 2048 :=
  linkRtC0Cert rtC0CoreCert factLoopX64ProgCert (by t_kernel_rfl)

theorem factLoopX64Cert_maxBound :
    factLoopX64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" ≤ 2048 :=
  factLoopX64Cert.bound_le_max _

theorem factLoopX64Cert_factAcc_bound :
    factLoopX64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factAcc" ≤ 2048 :=
  factLoopX64Cert.bound_le_max _

theorem factLoopLinkedMod_x64_legalSig :
    LegalSigAll x64LegalTarget factLoopLinkedMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

private theorem factLoop_factStr_prog_mem :
    factLoopTfs.tf_1.toFn ∈ (lcnfProgMod factLoopTfs).fns := by
  simp [lcnfProgMod, factLoopTfs, Frontend.C0.tflatFnsToFns]

private theorem factLoop_factStr_linked_mem :
    factLoopTfs.tf_1.toFn ∈ factLoopLinkedMod.fns := by
  change factLoopTfs.tf_1.toFn ∈ (linkLcnfWithRtC0 factLoopTfs false).fns
  rw [linkLcnfWithRtC0_fns_eq]
  exact List.mem_append_right _ factLoop_factStr_prog_mem

theorem factLoopX64_factStr_fnSpec :
    x64Target.Defined factLoopX64Cert.host "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" ∧
      x64Target.FnSpec factLoopX64Cert.host "l_LeanQbe_T_LeanLCNF_FactLoop_factStr"
        (factLoopEnv "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" [i64, i64] [i64])
        (factLoopX64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr") 64 :=
  factLoopX64Cert.fnSpec_host_of_legalSigAll factLoopEnv factLoopLinkedMod_acyclic
    factLoopLinkedMod_fns_wf factLoopLinkedMod_x64_legalSig
    (fun fn hfn _ _ _ _ hp => factLoopLinkedMod_wp fn hfn hp)
    factLoop_factStr_linked_mem
    (factLoopEnv_noex _ factLoop_factStr_prog_mem)

/-- Zero-padding byte gap `[0x1000, 0x100000)` separating initial stack from `loopRtMem`. -/
@[expose] def loopX64PadLen : Nat := 1044480

/-- Initial x86-64 memory containing the stack frame, padding gap, and `loopRtMem`. -/
@[expose] def loopX64Dmem (b : Nat) : Mem 64 :=
  ((stackZeros b ++ Int.toBytes 8 (0x1234 : Int64).toBitVec.toInt) ++
    (List.replicate loopX64PadLen 0 ++ loopRtBytes)).At (0x0ff8#64 - BitVec.ofNat 64 b)

private theorem loopRtBytes_len : loopRtBytes.length = 36056 := by
  simp only [loopRtBytes, List.length_append, bytes64_length, List.length_replicate,
    loopRtState.extraLen, loopRtState.globalsLen, loopRtState.freeListLen, loopRtState.workLen,
    rtExtraSlots, rtGlobalSlots, BigNumRt.rtNumClasses, loopRem,
    loopScrLimbs, loopScrCap]
  dsimp [nvBnHdrWords]
  decide

private theorem loopX64Dmem_entry (b : Nat) (hb : b ≤ 2048) :
    loopX64Dmem b =⋆ Eq loopRtMem ⋆
      (region (0x0ff8#64 - BitVec.ofNat 64 b) b ⋆
        cell64 0x0ff8#64 (0x1234 : Int64).toBitVec) ⋆
      Eq ((List.replicate loopX64PadLen 0).At 0x1000#64) := by
  let raBytes : List UInt8 := Int.toBytes 8 (0x1234 : Int64).toBitVec.toInt
  let padBytes : List UInt8 := List.replicate loopX64PadLen 0
  let base0 : BitVec 64 := 0x0ff8#64 - BitVec.ofNat 64 b
  have hra : raBytes.length = 8 := Int.toBytes_length 8 _
  have hzs : (stackZeros b).length = b := stackZeros_length b
  have hpad : padBytes.length = 1044480 := List.length_replicate
  have hrt : loopRtBytes.length = 36056 := loopRtBytes_len
  have hlen3 : padBytes.length + loopRtBytes.length ≤ 2 ^ 64 := by
    rw [hpad, hrt]; decide
  have hlen2 : raBytes.length + (padBytes ++ loopRtBytes).length ≤ 2 ^ 64 := by
    rw [List.length_append, hra, hpad, hrt]; decide
  have hlen1 :
      (stackZeros b).length + (raBytes ++ (padBytes ++ loopRtBytes)).length ≤ 2 ^ 64 := by
    rw [List.length_append, List.length_append, hzs, hra, hpad, hrt]; omega
  have h1 := Mem.At_append_sep (stackZeros b) (raBytes ++ (padBytes ++ loopRtBytes))
    base0 hlen1
  have hsp : base0 + BitVec.ofNat 64 (stackZeros b).length = 0x0ff8#64 := by
    rw [hzs]; exact BitVec.sub_add_cancel 0x0ff8#64 (BitVec.ofNat 64 b)
  rw [hsp] at h1
  have h2 := Mem.At_append_sep raBytes (padBytes ++ loopRtBytes) 0x0ff8#64 hlen2
  have h1000 : (0x0ff8#64 : BitVec 64) + BitVec.ofNat 64 raBytes.length = 0x1000#64 := by
    rw [hra]; decide
  rw [h1000] at h2
  have h3 := Mem.At_append_sep padBytes loopRtBytes 0x1000#64 hlen3
  have hbase : (0x1000#64 : BitVec 64) + BitVec.ofNat 64 padBytes.length = loopRtBase := by
    rw [hpad]; rfl
  rw [hbase] at h3
  have hmem :
      (Eq ((stackZeros b).At base0) ⋆
        (Eq (raBytes.At 0x0ff8#64) ⋆
          (Eq (padBytes.At 0x1000#64) ⋆ Eq (loopRtBytes.At loopRtBase))))
        (loopX64Dmem b) := by
    have he0 : Eq ((stackZeros b ++ (raBytes ++ (padBytes ++ loopRtBytes))).At base0)
        (loopX64Dmem b) := by
      dsimp only [loopX64Dmem, raBytes, padBytes, base0]
      rw [← List.append_assoc]
    rw [h1, h2, h3] at he0
    exact he0
  have hreg :
      (region base0 b ⋆
        (cell64 0x0ff8#64 (0x1234 : Int64).toBitVec ⋆
          (Eq (padBytes.At 0x1000#64) ⋆ Eq loopRtMem)))
        (loopX64Dmem b) :=
    sep_mono (fun _ hm => ⟨stackZeros b, hzs, hm.symm⟩) hmem
  exact sep_cast hreg (by ac_rfl)

/-- Closed SysV x86-64 concrete execution of `FactLoop.factStr (boxNat 25)` returning the `"25!"`
string `"15511210043330985984000000"` (`fact25Bytes`). -/
theorem factLoopX64_fact25_run :
    let b := factLoopX64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr"
    let args : Tup Val [i64, i64] := (loopRtBase, boxNat 25, ())
    let s0 : MachineData := { x64InitState b [] args with dmem := loopX64Dmem b }
    letI : Host := factLoopX64Cert.host
    Eventually (step1 factLoopX64Cert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        ∃ (s : BitVec 64) (st' : RtC0State) (objs' : List LcnfObj)
          (scrLimbs' : List (BitVec 64)) (m' : Mem 64),
          st.data.regs.get64 .rax = s ∧
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
            region (0x0ff8#64 - BitVec.ofNat 64 b) (b + 8) ⋆
            region 0x1000#64 loopX64PadLen))
      ⟨s0, Labels.label "l_LeanQbe_T_LeanLCNF_FactLoop_factStr"⟩ := by
  letI : Host := factLoopX64Cert.host
  let b := factLoopX64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr"
  let args : Tup Val [i64, i64] := (loopRtBase, boxNat 25, ())
  let s0 : MachineData := { x64InitState b [] args with dmem := loopX64Dmem b }
  let padR : Mem 64 → Prop := Eq ((List.replicate loopX64PadLen 0).At 0x1000#64)
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
  have hb : b ≤ 2048 := factLoopX64Cert_maxBound
  have hsp : s0.regs.get64 .rsp = 0x0ff8#64 := x64Init.get_sp b [] args
  have hargs : x64Target.ArgsIn args s0 := x64Init.argsIn b [] args rfl
  have hspAl : (s0.regs.get64 .rsp + 8#64).toNat % 16 = 0 := by rw [hsp]; decide
  have hmem :
      s0.dmem =⋆ Eq loopRtMem ⋆
        (region (s0.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
          cell64 (s0.regs.get64 .rsp) (0x1234 : Int64).toBitVec) ⋆ padR := by
    rw [hsp]; exact loopX64Dmem_entry b hb
  have hspec :
      factLoopEnv "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" [i64, i64] [i64]
        args loopRtMem Q (fun _ _ _ _ => False) :=
    fact25_str_spec Q (fun _ _ _ _ => False) fun s st' objs' scrLimbs' m' hs0 hs8 hpr hrem hcan
        hm' =>
      ⟨hs0, hs8, st', objs', scrLimbs', hpr, hrem, hcan, hm'⟩
  have hrun :=
    x64_of_returns factLoopX64_factStr_fnSpec.2 hspec s0 (0x1234 : Int64) padR hargs hspAl hmem
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨s, ⟨⟩⟩, m', ⟨hs0, hs8, st', objs', scrLimbs', hpr, hrem, hcan, hm'⟩,
    hrets, hdmem⟩
  rw [hsp] at hdmem
  have hdmem' :
      (st.data.dmem =⋆ Eq m' ⋆ region (0x0ff8#64 - BitVec.ofNat 64 b) (b + 8) ⋆
        region 0x1000#64 loopX64PadLen) :=
    sep_mono_r (fun _ h => ⟨List.replicate loopX64PadLen 0, List.length_replicate, h.symm⟩) hdmem
  exact ⟨hpc, s, st', objs', scrLimbs', m', x64Init.retsIn_singleton s st.data hrets,
    hs0, hs8, hpr, hrem, hcan, hm', hdmem'⟩

end LeanQbe.T.Amd64
