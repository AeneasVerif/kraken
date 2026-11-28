module

import LeanQbe.T.Amd64.LcnfC0FullCertX64
import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Bedrock2.Phoas
meta import Lean
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64

/-!
# Verification Suite for SysV x64 `rtC0CoreMod` Linked Certificate (`LcnfC0FullCertX64`)

1. Architecture-isolation `#eval` audit (zero `Kraken.AArch64` / `LeanQbe.T.Arm64` imports).
2. Kernel `#guard` and structural certificate checks across all `80` pure-C0 runtime functions
   (`exits = ["lcnf_panic"]`, `nX = 64`, max stack bound `≤ 272`).
3. Closed concrete x86-64 machine execution (`Eventually (step1 rtC0CoreCert.host.exe)`) witnesses
   (`XPost := False`):
   - `lcnf_nat_slow` (`add` of 2-limb MPZs → 2-limb MPZ `[4#64, 4#64]`, calling R0 `lcnf_alloc`)
     on `nvBnMem`;
   - `lcnf_nat_to_str` (`boxNat 42` → `"42"` string object `[52, 50]`, calling R0 `lcnf_alloc`)
     on `nvDagMem`.
4. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LcnfC0FullCertTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64 Kraken

/-! ## 1. Architecture Isolation & Metadata Guards -/

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let arm := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.AArch64" || s.startsWith "LeanQbe.T.Arm64"
  if !arm.isEmpty then
    throwError "LcnfC0FullCertTest leaked Arm64 imports: {arm.toList}"

#guard rtC0CoreMod.fns.length == 80
#guard rtC0CoreMod.externs.isEmpty
#guard rtC0CoreMod.exits == ["lcnf_panic"]
#guard rtC0CoreMod.checkAcyclic
#guard checkLegalSigAll x64LegalTarget rtC0CoreMod.fns
#guard rtC0CoreAllExt.length == 80

/-! ## 2. Closed Concrete x86-64 Machine Execution Witnesses -/

private theorem mem_At_disjoint_x64InitMem {base : BitVec 64} {bs : List UInt8}
    {n b : Nat} (hbase : 0x1000 ≤ base.toNat) (hfit : base.toNat + n < 2 ^ 64)
    (hlen : bs.length = n) (hb : b ≤ 2048) :
    (bs.At base).inter (x64InitMem b 0x1234 []) = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  intro k
  rw [inter_eq, mem_inter_iff]
  rintro ⟨h1, h2⟩
  rw [mem_At_iff] at h1
  rw [x64InitMem, mem_At_iff] at h2
  rcases h1 with ⟨i, hi, rfl⟩
  rcases h2 with ⟨j, hj, heq⟩
  rw [hlen] at hi
  simp only [List.length_append, List.length_nil, Nat.add_zero, stackZeros_length,
    Int.toBytes_length] at hj
  have hL : (base + BitVec.ofNat 64 i).toNat ≥ 0x1000 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hR : ((0x0ff8#64 - BitVec.ofNat 64 b) + BitVec.ofNat 64 j).toNat < 0x1000 := by
    have hsp : (0x0ff8#64 : BitVec 64).toNat = 0x0ff8 := by decide
    have hsub : (0x0ff8#64 - BitVec.ofNat 64 b).toNat = 0x0ff8 - b := by
      rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
      rw [hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [heq] at hL
  omega

private theorem x64InitMem_empty_entry {b : Nat} (hb : b ≤ 2048) :
    (region (0x0ff8#64 - BitVec.ofNat 64 b) b ⋆ cell64 0x0ff8#64 0x1234#64)
      (x64InitMem b 0x1234 []) := by
  have hm := x64InitMem_entry b 0x1234 [] hb (by decide)
  have hnil : ([].At 0x1000#64 : Mem 64) = ∅ := by
    rw [eq_empty_iff_forall_not_mem]
    intro k hk
    rw [mem_At_iff] at hk
    rcases hk with ⟨_, hi, _⟩
    simp at hi
  rw [hnil, eq_empty_eq_emp, emp_sep, sep_emp] at hm
  exact hm

private theorem slab_machine_dmem_entry {as : List Ty} {mem : Mem 64} (b : Nat)
    (hb : b ≤ 2048) (hdisj : mem.inter (x64InitMem b 0x1234 []) = ∅) (args : Tup Val as) :
    ((mem.union (x64InitState b [] args).dmem) =⋆
      Eq mem ⋆
      (region ((x64InitState b [] args).regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 ((x64InitState b [] args).regs.get64 .rsp) (0x1234#64)) ⋆
      emp) := by
  have hsp : (x64InitState (as := as) b [] args).regs.get64 .rsp = 0x0ff8#64 :=
    x64Init.get_sp b [] args
  have hdmem : (x64InitState (as := as) b [] args).dmem = x64InitMem b 0x1234 [] := by
    dsimp only [x64InitState]
  rw [hsp, hdmem, sep_emp]
  exact LeanQbe.T.Bedrock2.split_sep ⟨rfl, hdisj⟩ rfl (x64InitMem_empty_entry hb)

private theorem slab_machine_argsIn {as : List Ty} (mem : Mem 64) (b : Nat) (args : Tup Val as)
    (hassign : (x64Target.toIsa.assignArgs as).isSome = true) :
    x64Target.ArgsIn args { x64InitState b [] args with
      dmem := mem.union (x64InitState b [] args).dmem } :=
  x64Init.argsIn b [] args hassign

private theorem slab_machine_rsp_ok {as : List Ty} (mem : Mem 64) (b : Nat) (args : Tup Val as) :
    (({ x64InitState b [] args with
        dmem := mem.union (x64InitState b [] args).dmem }.regs.get64 .rsp + 8#64).toNat %
      16 = 0) := by
  have hsp : (x64InitState (as := as) b [] args).regs.get64 .rsp = 0x0ff8#64 :=
    x64Init.get_sp b [] args
  change ((x64InitState (as := as) b [] args).regs.get64 .rsp + 8#64).toNat % 16 = 0
  rw [hsp]
  decide

private theorem nvBnMem_disjoint_x64InitMem {b : Nat} (hb : b ≤ 2048) :
    nvBnMem.inter (x64InitMem b 0x1234 []) = ∅ := by
  have hlen : (nvBnRtBytes ++ nvBnHeapBytes).length = 34392 := by
    simp only [List.length_append, nvBnRtBytes, nvBnHeapBytes, nvBnObjBytes, bytes64_length,
      List.length_cons, List.length_nil, List.length_replicate, nvBnHdrWords, nvBnRtState,
      nvBnWorkCap, nvBnRem, nvBnScrCap, nvBnScrLimbs, rtExtraSlots, rtGlobalSlots,
      nvBnNatA, nvBnNatB, nvBnIntNegA, nvBnIntPosB]
    decide
  exact mem_At_disjoint_x64InitMem (by decide) (by decide) hlen hb

private theorem nvDagMem_disjoint_x64InitMem {b : Nat} (hb : b ≤ 2048) :
    nvDagMem.inter (x64InitMem b 0x1234 []) = ∅ := by
  have hlen : (nvRtBytes ++ nvDagBytes).length = 33912 := by
    simp only [List.length_append, nvRtBytes, nvDagBytes, nvObjABytes, nvObjBBytes, nvObjCBytes,
      nvObjPBytes, nvObjUBytes, bytes64_length, List.length_cons, List.length_nil,
      List.length_replicate, nvHdrWords, nvRtState, initRtC0State, nvWorkCap, nvRem,
      rtExtraSlots, rtGlobalSlots, rtNumClasses, nvObjA, nvObjB, nvObjC, nvObjP, nvObjU]
  exact mem_At_disjoint_x64InitMem (by decide) (by decide) hlen hb

private theorem nvBnRtWf_ok :
    BigNumRtWf nvBnRtBase nvBnRtState nvBnScr nvBnScrLimbs := by
  have hlen : nvBnScrLimbs.length = 32 := List.length_replicate
  refine ⟨?_, by decide, by decide, by decide, ?_, ?_⟩
  · unfold RtC0State.Bounded48
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
  · unfold LcnfObj.Wf LcnfObj.totalBytes
    decide
  · simp [nvBnNatA, limbsVal, nvValNatA]

private theorem nvBnNatB_rep_ok : natRep nvBnAddrNatB nvValNatB nvBnObjs := by
  have hge : ¬(nvValNatB < 2 ^ 63) := by decide
  simp only [natRep, hge, ↓reduceIte]
  refine ⟨by decide, nvBnNatB, by simp [nvBnObjs], rfl, ?_, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, by decide⟩
  · unfold LcnfObj.Wf LcnfObj.totalBytes
    decide
  · simp [nvBnNatB, limbsVal, nvValNatB]

/-- Concrete x86-64 machine execution (`Eventually (step1 rtC0CoreCert.host.exe)`) of
`lcnf_nat_slow` (`add` of 2-limb MPZs `[2^64-1, 1] + [5, 2]`) on `nvBnMem` (`XPost := False`),
exercising cross-module R1 → R0 (`lcnf_alloc`) in verified native machine code. -/
theorem rtC0Core_nat_slow_add_x64_run :
    let b := rtC0CoreCert.bound "lcnf_nat_slow"
    let args : Tup Val [i64, i64, i64, i64] :=
      (nvBnRtBase, 1#64, nvBnAddrNatA, nvBnAddrNatB, ())
    let s0 : MachineData :=
      { x64InitState b [] args with dmem := nvBnMem.union (x64InitState b [] args).dmem }
    letI : Host := rtC0CoreCert.host
    Eventually (step1 rtC0CoreCert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        ∃ (p : BitVec 64) (st' : RtC0State) (scrLimbs' : List (BitVec 64))
          (objs' : List LcnfObj) (obj : LcnfObj) (m' : Mem 64),
          st.data.regs.get64 .rax = p ∧
          (p &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = p ∧
          obj.tag = mpzTag ∧ obj.other = 0 ∧
          natRep p (nvValNatA + nvValNatB) objs' ∧
          (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆
            lcnfHeap objs') m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (0x0ff8#64 - BitVec.ofNat 64 b) (b + 8) ⋆ emp))
      ⟨s0, Labels.label "lcnf_nat_slow"⟩ := by
  letI : Host := rtC0CoreCert.host
  let b := rtC0CoreCert.bound "lcnf_nat_slow"
  let args : Tup Val [i64, i64, i64, i64] :=
    (nvBnRtBase, 1#64, nvBnAddrNatA, nvBnAddrNatB, ())
  let s0 : MachineData :=
    { x64InitState b [] args with dmem := nvBnMem.union (x64InitState b [] args).dmem }
  let Q : Post [i64] := fun (r, ()) m' =>
    ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64))
      (objs' : List LcnfObj) (obj : LcnfObj),
      (r &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = r ∧
      obj.tag = mpzTag ∧ obj.other = 0 ∧
      natRep r (nvValNatA + nvValNatB) objs' ∧
      (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ lcnfHeap objs') m'
  have hb : b ≤ 2048 := rtC0CoreCert.bound_le_max "lcnf_nat_slow"
  have hspec : lcnfNatSlowSpec args nvBnMem Q (fun _ _ _ _ => False) := by
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
  have hrun := x64_of_returns rtC0Core_nat_slow_fnSpec.2 hspec s0 (0x1234 : Int64) emp
    (slab_machine_argsIn nvBnMem b args rfl) (slab_machine_rsp_ok nvBnMem b args)
    (slab_machine_dmem_entry b hb (nvBnMem_disjoint_x64InitMem hb) args)
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨p, ⟨⟩⟩, m', ⟨st', scrLimbs', objs', obj, h1, h2, h3, h4, h5, h6, hinv⟩,
    hrets, hm'⟩
  have hsp : s0.regs.get64 .rsp = 0x0ff8#64 := x64Init.get_sp b [] args
  rw [hsp] at hm'
  exact ⟨hpc, p, st', scrLimbs', objs', obj, m', x64Init.retsIn_singleton p st.data hrets,
    h1, h2, h3, h4, h5, h6, hinv, hm'⟩

/-- Concrete x86-64 machine execution (`Eventually (step1 rtC0CoreCert.host.exe)`) of
`lcnf_nat_to_str` (`boxNat 42` → `"42"` string object `[52, 50]`) on `nvDagMem` (`XPost := False`),
exercising R2b → R0 (`lcnf_alloc`) in verified native machine code. -/
theorem rtC0Core_nat_to_str_42_x64_run :
    let b := rtC0CoreCert.bound "lcnf_nat_to_str"
    let args : Tup Val [i64, i64] := (nvRtBase, boxNat 42, ())
    let s0 : MachineData :=
      { x64InitState b [] args with dmem := nvDagMem.union (x64InitState b [] args).dmem }
    letI : Host := rtC0CoreCert.host
    Eventually (step1 rtC0CoreCert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        ∃ (s : BitVec 64) (st' : RtC0State) (m' : Mem 64),
          st.data.regs.get64 .rax = s ∧
          s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
          (rtC0Inv nvRtBase st' ⋆
            lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2) ⋆
            lcnfHeap nvDagObjs) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (0x0ff8#64 - BitVec.ofNat 64 b) (b + 8) ⋆ emp))
      ⟨s0, Labels.label "lcnf_nat_to_str"⟩ := by
  letI : Host := rtC0CoreCert.host
  let b := rtC0CoreCert.bound "lcnf_nat_to_str"
  let args : Tup Val [i64, i64] := (nvRtBase, boxNat 42, ())
  let s0 : MachineData :=
    { x64InitState b [] args with dmem := nvDagMem.union (x64InitState b [] args).dmem }
  let Q : Post [i64] := fun (s, ()) m' =>
    s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
    ∃ st' : RtC0State,
      (rtC0Inv nvRtBase st' ⋆
        lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2) ⋆
        lcnfHeap nvDagObjs) m'
  have hb : b ≤ 2048 := rtC0CoreCert.bound_le_max "lcnf_nat_to_str"
  have hspec : lcnfNatToStrSpec args nvDagMem Q (fun _ _ _ _ => False) := by
    have hm : (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap [] ⋆ lcnfHeap nvDagObjs) nvDagMem := by
      simp only [lcnfHeap]
      rw [sep_emp]
      exact nvDagMem_ok
    refine ⟨nvRtState, 42, [], lcnfHeap nvDagObjs,
      by simp [NatInHeap]; decide, (fun _ h => nomatch h), hm, ?_⟩
    rw [ite_eq_left (by decide)]
    have hdec : natToDecimalBytes 42 = [52, 50] := by
      rw [natToDecimalBytes, ite_eq_right (by decide),
        natDigitsRev.eq_def, dite_eq_right (by decide),
        natDigitsRev.eq_def, dite_eq_right (by decide),
        natDigitsRev.eq_def, dite_eq_left (by decide)]
      decide
    rw [hdec]
    have hrem : strAllocBytes ([52, 50].length + 1) ≤ nvRtState.rem := by
      unfold RtC0State.rem
      simp only [nvRtState, initRtC0State, nvRtBase, nvWorkCap, nvRem]
      decide
    refine ⟨Or.inr hrem, fun s st' m' hs0 hs8 _ _ _ hm' => ?_⟩
    refine ⟨hs0, hs8, st', ?_⟩
    simp only [lcnfHeap, List.length_cons, List.length_nil] at hm'
    rw [sep_emp] at hm'
    exact hm'
  have hrun := x64_of_returns rtC0Core_nat_to_str_fnSpec.2 hspec s0 (0x1234 : Int64) emp
    (slab_machine_argsIn nvDagMem b args rfl) (slab_machine_rsp_ok nvDagMem b args)
    (slab_machine_dmem_entry b hb (nvDagMem_disjoint_x64InitMem hb) args)
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨s, ⟨⟩⟩, m', ⟨hs0, hs8, st', hinv⟩, hrets, hm'⟩
  have hsp : s0.regs.get64 .rsp = 0x0ff8#64 := x64Init.get_sp b [] args
  rw [hsp] at hm'
  exact ⟨hpc, s, st', m', x64Init.retsIn_singleton s st.data hrets, hs0, hs8, hinv, hm'⟩

/-! ## 3. Standard-Axiom Audit -/

#print axioms rtC0CoreCert
#print axioms rtC0CoreMod_legalSig
#print axioms rtC0CoreCert_bounds_len
#print axioms rtC0CoreCert_bounds_le
#print axioms rtC0Core_all_fnSpec
#print axioms rtC0Core_all_fnSpec_src
#print axioms rtC0Core_fnSpec_src_at_idx
#print axioms rtC0Core_alloc_fnSpec
#print axioms rtC0Core_extra_fnSpecs
#print axioms rtC0Core_nat_slow_fnSpec
#print axioms rtC0Core_nat_to_str_fnSpec
#print axioms rtC0Core_nat_slow_add_x64_run
#print axioms rtC0Core_nat_to_str_42_x64_run

end LeanQbeTest.T.LcnfC0FullCertTest
