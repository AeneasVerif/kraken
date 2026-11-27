module

public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Logic.MemLemmas
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64

/-!
# Verification Suite for AAPCS64 Arm64 `rtC0CoreMod` Linked Certificate (`LcnfC0FullCertArm64`)

1. Architecture-isolation `#eval` audit (zero `Kraken.X64` / `LeanQbe.T.Amd64` imports).
2. Kernel `#guard` and structural certificate checks across all `80` pure-C0 runtime functions
   (`exits = ["lcnf_panic"]`, `nX = 64`, max stack bound `≤ 272`).
3. Closed concrete AArch64 machine execution (`Eventually (step1 rtC0CoreArm64Cert.host.exe)`)
   witnesses (`XPost := False`):
   - `lcnf_nat_slow` (`add` of 2-limb MPZs → 2-limb MPZ `[4#64, 4#64]`, calling R0 `lcnf_alloc`)
     on `nvBnMem`;
   - `lcnf_nat_to_str` (`boxNat 42` → `"42"` string object `[52, 50]`, calling R0 `lcnf_alloc`)
     on `nvDagMem`.
4. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0FullCertArm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64 Kraken

/-! ## 1. Architecture Isolation & Metadata Guards -/

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let x64 := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64.isEmpty then
    throwError "LcnfC0FullCertArm64Test leaked X64 imports: {x64.toList}"

#guard rtC0CoreMod.fns.length == 80
#guard rtC0CoreMod.externs.isEmpty
#guard rtC0CoreMod.exits == ["lcnf_panic"]
#guard rtC0CoreMod.checkAcyclic
#guard checkLegalSigAll armLegalTarget rtC0CoreMod.fns
#guard rtC0CoreArm64AllExt.length == 80

/-! ## 2. Closed Concrete AArch64 Machine Execution Witnesses -/

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
  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds] at hm
  simp only [region_zero, sep_emp] at hm
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

/-- Concrete AArch64 machine execution (`Eventually (step1 rtC0CoreArm64Cert.host.exe)`) of
`lcnf_nat_slow` (`add` of 2-limb MPZs `[2^64-1, 1] + [5, 2]`) on `nvBnMem` (`XPost := False`),
exercising cross-module R1 → R0 (`lcnf_alloc`) in verified native machine code. -/
theorem rtC0CoreArm64_nat_slow_add_arm64_run :
    let b := rtC0CoreArm64Cert.bound "lcnf_nat_slow"
    let args : Tup Val [i64, i64, i64, i64] :=
      (nvBnRtBase, 1#64, nvBnAddrNatA, nvBnAddrNatB, ())
    let s0 : MachineData :=
      { armInitState b [] args with dmem := nvBnMem.union (armInitState b [] args).dmem }
    letI : Host := rtC0CoreArm64Cert.host
    Eventually (step1 rtC0CoreArm64Cert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        ∃ (p : BitVec 64) (st' : RtC0State) (scrLimbs' : List (BitVec 64))
          (objs' : List LcnfObj) (obj : LcnfObj) (m' : Mem 64),
          (st.data.regs.getXReg .X0).toBitVec = p ∧
          (p &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = p ∧
          obj.tag = mpzTag ∧ obj.other = 0 ∧
          natRep p (nvValNatA + nvValNatB) objs' ∧
          (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆
            lcnfHeap objs') m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (0x1000#64 - BitVec.ofNat 64 b) b ⋆ emp))
      ⟨s0, Labels.label "lcnf_nat_slow"⟩ := by
  letI : Host := rtC0CoreArm64Cert.host
  let b := rtC0CoreArm64Cert.bound "lcnf_nat_slow"
  let args : Tup Val [i64, i64, i64, i64] :=
    (nvBnRtBase, 1#64, nvBnAddrNatA, nvBnAddrNatB, ())
  let s0 : MachineData :=
    { armInitState b [] args with dmem := nvBnMem.union (armInitState b [] args).dmem }
  let Q : Post [i64] := fun (r, ()) m' =>
    ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64))
      (objs' : List LcnfObj) (obj : LcnfObj),
      (r &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = r ∧
      obj.tag = mpzTag ∧ obj.other = 0 ∧
      natRep r (nvValNatA + nvValNatB) objs' ∧
      (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ lcnfHeap objs') m'
  have hb : b ≤ 2048 := rtC0CoreArm64Cert.bound_le_max "lcnf_nat_slow"
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
  have hrun := arm64_of_returns rtC0CoreArm64_nat_slow_fnSpec.2 hspec s0 (0x1234 : Int64) emp
    (slab_machine_argsIn nvBnMem b args rfl) (slab_machine_x30_ok nvBnMem b args)
    (slab_machine_sp_ok nvBnMem b args)
    (slab_machine_dmem_entry b hb (nvBnMem_disjoint_armInitMem hb) args)
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨p, ⟨⟩⟩, m', ⟨st', scrLimbs', objs', obj, h1, h2, h3, h4, h5, h6, hinv⟩,
    hrets, hm'⟩
  have hsp : s0.regs.SP.toBitVec = 0x1000#64 := armInit.get_sp b [] args
  change _ at hm'
  rw [hsp] at hm'
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = p := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton p st.data hrets
  exact ⟨hpc, p, st', scrLimbs', objs', obj, m', hx0, h1, h2, h3, h4, h5, h6, hinv, hm'⟩

/-- Concrete AArch64 machine execution (`Eventually (step1 rtC0CoreArm64Cert.host.exe)`) of
`lcnf_nat_to_str` (`boxNat 42` → `"42"` string object `[52, 50]`) on `nvDagMem` (`XPost := False`),
exercising R2b → R0 (`lcnf_alloc`) in verified native machine code. -/
theorem rtC0CoreArm64_nat_to_str_42_arm64_run :
    let b := rtC0CoreArm64Cert.bound "lcnf_nat_to_str"
    let args : Tup Val [i64, i64] := (nvRtBase, boxNat 42, ())
    let s0 : MachineData :=
      { armInitState b [] args with dmem := nvDagMem.union (armInitState b [] args).dmem }
    letI : Host := rtC0CoreArm64Cert.host
    Eventually (step1 rtC0CoreArm64Cert.host.exe)
      (fun st =>
        st.pc = (0x1234 : Int64) ∧
        ∃ (s : BitVec 64) (st' : RtC0State) (m' : Mem 64),
          (st.data.regs.getXReg .X0).toBitVec = s ∧
          s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
          (rtC0Inv nvRtBase st' ⋆
            lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2) ⋆
            lcnfHeap nvDagObjs) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (0x1000#64 - BitVec.ofNat 64 b) b ⋆ emp))
      ⟨s0, Labels.label "lcnf_nat_to_str"⟩ := by
  letI : Host := rtC0CoreArm64Cert.host
  let b := rtC0CoreArm64Cert.bound "lcnf_nat_to_str"
  let args : Tup Val [i64, i64] := (nvRtBase, boxNat 42, ())
  let s0 : MachineData :=
    { armInitState b [] args with dmem := nvDagMem.union (armInitState b [] args).dmem }
  let Q : Post [i64] := fun (s, ()) m' =>
    s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
    ∃ st' : RtC0State,
      (rtC0Inv nvRtBase st' ⋆
        lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2) ⋆
        lcnfHeap nvDagObjs) m'
  have hb : b ≤ 2048 := rtC0CoreArm64Cert.bound_le_max "lcnf_nat_to_str"
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
  have hrun := arm64_of_returns rtC0CoreArm64_nat_to_str_fnSpec.2 hspec s0 (0x1234 : Int64) emp
    (slab_machine_argsIn nvDagMem b args rfl) (slab_machine_x30_ok nvDagMem b args)
    (slab_machine_sp_ok nvDagMem b args)
    (slab_machine_dmem_entry b hb (nvDagMem_disjoint_armInitMem hb) args)
  refine eventually_weaken _ _ _ _ ?_ hrun
  rintro st ⟨hpc, _, _, ⟨s, ⟨⟩⟩, m', ⟨hs0, hs8, st', hinv⟩, hrets, hm'⟩
  have hsp : s0.regs.SP.toBitVec = 0x1000#64 := armInit.get_sp b [] args
  change _ at hm'
  rw [hsp] at hm'
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = s := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton s st.data hrets
  exact ⟨hpc, s, st', m', hx0, hs0, hs8, hinv, hm'⟩

/-! ## 3. Standard-Axiom Audit -/

#print axioms rtC0CoreArm64Cert
#print axioms rtC0CoreMod_arm64_legalSig
#print axioms rtC0CoreArm64Cert_bounds_len
#print axioms rtC0CoreArm64Cert_bounds_le
#print axioms rtC0CoreArm64_all_fnSpec
#print axioms rtC0CoreArm64_all_fnSpec_src
#print axioms rtC0CoreArm64_fnSpec_src_at_idx
#print axioms rtC0CoreArm64_alloc_fnSpec
#print axioms rtC0CoreArm64_extra_fnSpecs
#print axioms rtC0CoreArm64_nat_slow_fnSpec
#print axioms rtC0CoreArm64_nat_to_str_fnSpec
#print axioms rtC0CoreArm64_nat_slow_add_arm64_run
#print axioms rtC0CoreArm64_nat_to_str_42_arm64_run

end LeanQbeTest.T.LcnfC0FullCertArm64Test
