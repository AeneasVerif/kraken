module

public import LeanQbe.T.LeanLCNF.LcnfC0RtProofM0b
import LeanQbe.T.Logic.MemLemmas
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Rt`, Part Nv (Concrete 5-Node DAG Non-Vacuity)

Constructs a concrete 64-bit memory image `nvDagMem` packing the `LcnfC0Rt` state slab and a
5-node cyclic-free ctor/closure DAG, and proves `nvDagMem_ok`, `nv_dec_ref_cold_dag`, and
`nv_mark_persistent_dag` with `XPost := False`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open Std.ExtHashMap
open LeanQbe.T.LeanLCNF.RtProof

@[expose] public section

/-! ## Concrete `Mem 64` Non-Vacuity (`XPost := False`, Multi-Node Ctor/Closure DAG) -/

def nvRtBase : BitVec 64 := 0x10000#64
def nvWorkCap : Nat := 8
def nvRem : Nat := 64

def nvRtState : RtC0State :=
  initRtC0State nvRtBase nvWorkCap nvRem (by decide) (by decide)

def nvDagBase : BitVec 64 := nvRtBase + 33800#64
def nvAddrA : BitVec 64 := nvDagBase
def nvAddrB : BitVec 64 := nvDagBase + 24#64
def nvAddrC : BitVec 64 := nvDagBase + 56#64
def nvAddrP : BitVec 64 := nvDagBase + 80#64
def nvAddrU : BitVec 64 := nvDagBase + 96#64

/-- Root ctor `A` (`rc=1`) referencing exclusive closure `B` and shared ctor `C`. -/
def nvObjA : LcnfObj :=
  { addr := nvAddrA, rc := 1#32, csSz := 24, other := 2, tag := 0, fields := [nvAddrB, nvAddrC] }

/-- Exclusive closure `B` (`rc=1`, `arity=2`) capturing shared ctor `C`. -/
def nvObjB : LcnfObj :=
  { addr := nvAddrB, rc := 1#32, csSz := 32, other := 0, tag := closureTag,
    funId := 0x400#64, arity := 2, fields := [nvAddrC] }

/-- Shared ctor `C` (`rc=3`) referencing scalar `7#64` and persistent leaf `P`. -/
def nvObjC : LcnfObj :=
  { addr := nvAddrC, rc := 3#32, csSz := 24, other := 2, tag := 1, fields := [7#64, nvAddrP] }

/-- Persistent leaf ctor `P` (`rc=0`) holding scalar `11#64`. -/
def nvObjP : LcnfObj :=
  { addr := nvAddrP, rc := 0#32, csSz := 16, other := 1, tag := 2, fields := [11#64] }

/-- Unreachable ctor `U` (`rc=2`) holding scalar `13#64`. -/
def nvObjU : LcnfObj :=
  { addr := nvAddrU, rc := 2#32, csSz := 16, other := 1, tag := 3, fields := [13#64] }

def nvDagObjs : List LcnfObj := [nvObjA, nvObjB, nvObjC, nvObjP, nvObjU]

def nvHdrWords (h : LcnfC0Rt) : List (BitVec 64) :=
  [ h.s_large_free, h.s_ba_empty, h.s_cur, h.s_end, h.s_work, h.s_work_cap, h.s_chunks, h.s_nchunks,
    h.s_chunks_cap, h.s_st_allocs, h.s_st_frees, h.s_st_live, h.s_st_peak_live, h.s_st_persistent,
    h.s_st_reused, h.s_st_cold_decs, h.s_st_bytes ]

def nvRtBytes : List UInt8 :=
  bytes64 nvRtState.extraArgs ++ bytes64 nvRtState.globals ++ bytes64 nvRtState.freeList ++
  bytes64 (nvHdrWords nvRtState.hdr) ++ bytes64 nvRtState.workBuf ++ List.replicate nvRem 0

def nvObjABytes : List UInt8 := bytes64 [nvObjA.header, nvAddrB, nvAddrC]
def nvObjBBytes : List UInt8 := bytes64 [nvObjB.header, nvObjB.funId, nvObjB.cloMeta, nvAddrC]
def nvObjCBytes : List UInt8 := bytes64 [nvObjC.header, 7#64, nvAddrP]
def nvObjPBytes : List UInt8 := bytes64 [nvObjP.header, 11#64]
def nvObjUBytes : List UInt8 := bytes64 [nvObjU.header, 13#64]
def nvDagBytes : List UInt8 :=
  nvObjABytes ++ nvObjBBytes ++ nvObjCBytes ++ nvObjPBytes ++ nvObjUBytes

/-- Concrete `Mem 64` image packing the `LcnfC0Rt` slab (`33800B`) + 5-node DAG (`112B`). -/
def nvDagMem : Mem 64 := (nvRtBytes ++ nvDagBytes).At nvRtBase
end

public section

private theorem nv_sep_append {P Q : Mem 64 → Prop} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hs := congrFun (Mem.At_append_sep bs1 bs2 a (by omega)) ((bs1 ++ bs2).At a)
  obtain ⟨_, _, hu, hd, rfl, rfl⟩ := hs.mp rfl; exact ⟨_, _, hu, hd, hp, h1 ▸ hq⟩

private theorem nv_sep_join {P Q : Mem 64 → Prop} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by simp [h1, h2], nv_sep_append h1 h2 hfit hp hq⟩

private theorem array64_hdrWords_to_At (rt : BitVec 64) (h : LcnfC0Rt) {m : Mem 64}
    (hm : array64 (rt + 33536#64) (nvHdrWords h) m) : LcnfC0Rt.At rt h m := by
  unfold nvHdrWords at hm; simp only [array64, cell64_eq_cell, sep_emp, BitVec.add_assoc] at hm
  unfold LcnfC0Rt.At; exact sep_cast hm (by ac_rfl)

private theorem nvRtBytes_ok :
    nvRtBytes.length = 33800 ∧ rtC0Inv nvRtBase nvRtState (nvRtBytes.At nvRtBase) := by
  let b0 := bytes64 nvRtState.extraArgs; let b1 := bytes64 nvRtState.globals
  let b2 := bytes64 nvRtState.freeList; let b3 := bytes64 (nvHdrWords nvRtState.hdr)
  let b4 := bytes64 nvRtState.workBuf; let b5 := List.replicate nvRem (0 : UInt8)
  have hl0 : b0.length = 256 := by simp [b0, bytes64_length, nvRtState.extraLen, rtExtraSlots]
  have hl1 : b1.length = 32768 := by simp [b1, bytes64_length, nvRtState.globalsLen, rtGlobalSlots]
  have hl2 : b2.length = 512 := by simp [b2, bytes64_length, nvRtState.freeListLen, rtNumClasses]
  have hl3 : b3.length = 136 := by simp [b3, bytes64_length, nvHdrWords]
  have hwl : nvRtState.workBuf.length = 8 := by simp [nvRtState, initRtC0State, nvWorkCap]
  have hl4 : b4.length = 64 := by simp [b4, bytes64_length, hwl]
  have hl5 : b5.length = 64 := by simp [b5, nvRem]
  have s1 := nv_sep_join (a := nvRtBase) hl0 hl1 (by decide)
    (array64_bytes nvRtBase _ (by rw [nvRtState.extraLen]; decide))
    (array64_bytes _ _ (by rw [nvRtState.globalsLen]; decide))
  have s2 := nv_sep_join (a := nvRtBase) s1.1 hl2 (by decide) s1.2
    (array64_bytes _ _ (by rw [nvRtState.freeListLen]; decide))
  have s3 := nv_sep_join (a := nvRtBase) s2.1 hl3 (by decide) s2.2
    (array64_hdrWords_to_At nvRtBase _ (array64_bytes _ _ (by decide)))
  have s4 := nv_sep_join (a := nvRtBase) s3.1 hl4 (by decide) s3.2
    (array64_bytes _ _ (by rw [hwl]; decide))
  have s5 := nv_sep_join (a := nvRtBase) (Q := region (nvRtBase + 33736#64) nvRem)
    s4.1 hl5 (by decide) s4.2 ⟨b5, hl5, rfl⟩
  exact ⟨s5.1, rtC0Inv_init_satisfiable nvRtBase nvWorkCap nvRem (by decide) (by decide) s5.2⟩

private theorem array64_ctor_to_objMem {o : LcnfObj} (ht : o.tag ≠ closureTag ∧
    o.tag ≠ arrayTag ∧ o.tag ≠ sarrayTag ∧ o.tag ≠ stringTag ∧ o.tag ≠ mpzTag)
    (hdat : o.scalarData = []) (hcs : o.csSz = 8 + 8 * o.fields.length) {m : Mem 64}
    (hm : array64 o.addr (o.header :: o.fields) m) : lcnfObjMem o m := by
  have hbnil : ∀ a : BitVec 64, bytes a [] = emp := fun a => (eq_nil_At a).symm; unfold lcnfObjMem
  simpa [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2, hdat, hcs, hbnil, region_zero,
    sep_emp] using hm

private theorem array64_clo_to_objMem {o : LcnfObj} (ht : o.tag = closureTag)
    (hcs : o.csSz = 24 + 8 * o.fields.length) {m : Mem 64}
    (hm : array64 o.addr (o.header :: o.funId :: o.cloMeta :: o.fields) m) : lcnfObjMem o m := by
  unfold lcnfObjMem; simp only [ht, ↓reduceIte, hcs, Nat.sub_self, region_zero, sep_emp]
  simp only [array64, BitVec.add_assoc] at hm; exact sep_cast hm (by ac_rfl)

private theorem nvDagBytes_ok :
    nvDagBytes.length = 112 ∧ lcnfHeap nvDagObjs (nvDagBytes.At nvDagBase) := by
  have s1 := nv_sep_join (by simp [nvObjABytes, bytes64_length] : nvObjABytes.length = 24)
    (by simp [nvObjBBytes, bytes64_length] : nvObjBBytes.length = 32) (by decide)
    (array64_ctor_to_objMem (o := nvObjA) (by decide) rfl rfl
      (array64_bytes nvAddrA [nvObjA.header, nvAddrB, nvAddrC] (by decide)))
    (array64_clo_to_objMem (o := nvObjB) rfl rfl
      (array64_bytes nvAddrB [nvObjB.header, nvObjB.funId, nvObjB.cloMeta, nvAddrC]
        (by decide)))
  have s2 := nv_sep_join s1.1 (by simp [nvObjCBytes, bytes64_length] : nvObjCBytes.length = 24)
    (by decide) s1.2 (array64_ctor_to_objMem (o := nvObjC) (by decide) rfl rfl
      (array64_bytes nvAddrC [nvObjC.header, 7#64, nvAddrP] (by decide)))
  have s3 := nv_sep_join s2.1 (by simp [nvObjPBytes, bytes64_length] : nvObjPBytes.length = 16)
    (by decide) s2.2 (array64_ctor_to_objMem (o := nvObjP) (by decide) rfl rfl
      (array64_bytes nvAddrP [nvObjP.header, 11#64] (by decide)))
  have s4 := nv_sep_join s3.1 (by simp [nvObjUBytes, bytes64_length] : nvObjUBytes.length = 16)
    (by decide) s3.2 (array64_ctor_to_objMem (o := nvObjU) (by decide) rfl rfl
      (array64_bytes nvAddrU [nvObjU.header, 13#64] (by decide)))
  exact ⟨s4.1, by simp only [nvDagObjs, lcnfHeap, sep_emp]; exact sep_cast s4.2 (by ac_rfl)⟩

theorem nvDagMem_ok : (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap nvDagObjs) nvDagMem := by
  have ⟨hlRt, hRt⟩ := nvRtBytes_ok; have ⟨hlDag, hDag⟩ := nvDagBytes_ok
  exact nv_sep_append hlRt hlDag (by decide) hRt hDag

private theorem nvDagObjs_wf : ∀ o ∈ nvDagObjs, o.Wf := fun o ho => by
  simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> (unfold LcnfObj.Wf LcnfObj.totalBytes; decide)

private theorem nvDagObjs_closed : lcnfHeapClosed nvDagObjs := fun o ho f hf hf0 => by
  simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;>
    simp [LcnfObj.childFields, nvObjA, nvObjB, nvObjC, nvObjP, nvObjU, closureTag] at hf
  · exact hf.elim (fun h => h ▸ ⟨nvObjB, by simp [nvDagObjs], rfl⟩)
      (fun h => h ▸ ⟨nvObjC, by simp [nvDagObjs], rfl⟩)
  · exact ⟨nvObjC, by simp [nvDagObjs], hf.symm⟩
  · exact hf.elim (fun h => absurd (h ▸ hf0) (by decide))
      (fun h => h ▸ ⟨nvObjP, by simp [nvDagObjs], rfl⟩)
  · exact absurd (hf ▸ hf0) (by decide)
  · exact absurd (hf ▸ hf0) (by decide)

private theorem nvDagObjs_rcSound : RcSound nvAddrA nvDagObjs := by
  refine ⟨fun p hp hp0 f hf hf0 => ?_, fun y hy hyPos => ?_⟩
  · simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd hp0 (by decide) | (
      change f ∈ [11#64] at hf; simp only [List.mem_singleton] at hf; subst hf
      exact absurd hf0 (by decide))
  · simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd hyPos (by decide)

private theorem nvDag_not_reach_U : ¬ NonPersistReach nvDagObjs nvAddrA nvAddrU := fun hr => by
  cases hr with
  | step _ hch =>
    obtain ⟨ou, hou, _, hv⟩ := hch
    simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hou
    rcases hou with rfl | rfl | rfl | rfl | rfl <;> (
      simp [LcnfObj.childFields, nvObjA, nvObjB, nvObjC, nvObjP, nvObjU, closureTag] at hv
      first | exact absurd hv (by decide) |
        exact hv.elim (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))

private theorem nonPersistRefs_filter_le (xs : List LcnfObj) (p : LcnfObj → Bool)
    (a : BitVec 64) : nonPersistRefs (xs.filter p) a ≤ nonPersistRefs xs a := by
  induction xs with
  | nil => simp [nonPersistRefs]
  | cons z zs ih =>
    rw [List.filter_cons, nonPersistRefs_cons]
    cases hpz : p z <;> simp [nonPersistRefs_cons] <;> omega

private theorem nv_not_in_objs_freed {o : LcnfObj} {objs' : List LcnfObj} (ho : o ∈ nvDagObjs)
    (hNot : ∀ o' ∈ objs', o'.addr ≠ o.addr) : o ∈ freedObjs nvDagObjs objs' := by
  simp only [freedObjs, List.mem_filter, Bool.not_eq_true']; refine ⟨ho, ?_⟩
  cases hc : (objs'.map LcnfObj.addr).contains o.addr
  · rfl
  · obtain ⟨o', ho', heq⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
    exact absurd heq (hNot o' ho')

private theorem nv_surv_of_not_freed {o : LcnfObj} {objs' : List LcnfObj} (ho : o ∈ nvDagObjs)
    (hnf : o ∉ freedObjs nvDagObjs objs') :
    (objs'.map LcnfObj.addr).contains o.addr = true ∧ ∃ q ∈ objs', q.addr = o.addr := by
  have hc : (objs'.map LcnfObj.addr).contains o.addr = true := by
    cases h : (objs'.map LcnfObj.addr).contains o.addr
    · exact absurd (by simp only [freedObjs, List.mem_filter, ho, h, Bool.not_false, and_self]) hnf
    · rfl
  exact ⟨hc, List.mem_map.mp (List.contains_iff_mem.mp hc)⟩

private theorem nv_surv_rc {objs' : List LcnfObj} {orig o : LcnfObj} (ho' : o ∈ objs')
    (hoA : o.addr = orig.addr) (hFree : freedObjs nvDagObjs objs' = [nvObjA, nvObjB])
    (hEq : o.rc.toNat + ((if orig.addr = nvAddrA then 1 else 0) +
      nonPersistRefs (freedObjs nvDagObjs objs') orig.addr) = orig.rc.toNat)
    {k : Nat} (hk : orig.rc.toNat - ((if orig.addr = nvAddrA then 1 else 0) +
      nonPersistRefs [nvObjA, nvObjB] orig.addr) = k) :
    ∃ q ∈ objs', q.addr = orig.addr ∧ q.rc = BitVec.ofNat 32 k := by
  rw [hFree] at hEq; exact ⟨o, ho', hoA, BitVec.eq_of_toNat_eq (by
    have : k < 2 ^ 32 := hk ▸ Nat.lt_of_le_of_lt (Nat.sub_le _ _) orig.rc.isLt
    simp [Nat.mod_eq_of_lt this]; omega)⟩

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `lcnf_dec_ref_cold`:
dropping root ctor `A` (`rc=1`) cascadingly frees exclusive closure `B` (`rc=1`), decrements
shared ctor `C` from `rc=3` to `rc=1`, and preserves persistent leaf `P` (`rc=0`) and
unreachable ctor `U` (`rc=2`). -/
theorem nv_dec_ref_cold_dag :
    Func.wp rtC0Env lcnf_dec_ref_cold.body (nvRtBase, nvAddrA, ()) nvDagMem
    (fun () m' => ∃ st' objs', st'.PreservesMeta nvRtState ∧ st'.rem = nvRtState.rem ∧
      (rtC0Inv nvRtBase st' ⋆ lcnfHeap objs') m' ∧
      (∀ o' ∈ objs', o'.addr ≠ nvAddrA ∧ o'.addr ≠ nvAddrB) ∧
      (∃ oC ∈ objs', oC.addr = nvAddrC ∧ oC.rc = 1#32) ∧
      (∃ oP ∈ objs', oP.addr = nvAddrP ∧ oP.rc = 0#32) ∧
      (∃ oU ∈ objs', oU.addr = nvAddrU ∧ oU.rc = 2#32)) (fun _ _ _ _ => False) := by
  have hm : (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap nvDagObjs ⋆ emp) nvDagMem := by
    rw [sep_emp]; exact nvDagMem_ok
  refine rtC0Env_dec_ref_cold_wp (nvRtBase, nvAddrA, ()) nvDagMem _ _
    ⟨by decide, nvRtState, nvDagObjs, emp, by decide, hm, ⟨nvObjA, by simp [nvDagObjs], rfl, rfl⟩,
      nvDagObjs_wf, nvDagObjs_closed, nvDagObjs_rcSound, ?_⟩
  intro st' objs' m' hMeta hRem hRel hm'; rw [sep_emp] at hm'
  rcases hRel with ⟨_, _, _, _, hSurv, _, _, hPersSurv, hExact⟩
  have hNotA : ∀ o' ∈ objs', o'.addr ≠ nvAddrA := fun o' ho' => (hSurv o' ho').2.1
  have hAfree := nv_not_in_objs_freed (o := nvObjA) (by simp [nvDagObjs]) hNotA
  have hNotB : ∀ o' ∈ objs', o'.addr ≠ nvAddrB := fun o' ho' heq => by
    have hEqB := (hExact nvObjB (by simp [nvDagObjs]) (by decide)).1 o' ho' heq
    have hSurvB := hSurv o' ho'
    have hPosOrig : ∀ orig ∈ nvDagObjs, orig.addr = nvAddrB → orig.rc ≠ 0#32 := by decide
    have hPosB : 0 < o'.rc.toNat := by
      rcases hSurvB.2.2 with ⟨orig, horig, had, _, _, _, _, _, _, _, _, _, _, _, hrc⟩
      rcases hrc with ⟨h0, _⟩ | ⟨_, hpos, _⟩
      · exact absurd h0 (hPosOrig orig horig (had.trans heq))
      · have := objWf_rc_lt hSurvB.1; rw [BitVec.toInt_eq_toNat_cond] at hpos
        split at hpos <;> omega
    have hRefB : 1 ≤ nonPersistRefs (freedObjs nvDagObjs objs') nvAddrB := by
      rw [List.mem_iff_getElem] at hAfree; obtain ⟨i, hi, hAi⟩ := hAfree
      have hsp := nonPersistRefs_focus (freedObjs nvDagObjs objs') hi nvAddrB; rw [hAi] at hsp
      simp only [show nvObjA.rc ≠ 0#32 by decide, ↓reduceIte,
        show nvObjA.childFields.count nvAddrB = 1 by decide] at hsp; omega
    have h1B : nvObjB.rc.toNat = 1 := rfl; have hba : nvObjB.addr = nvAddrB := rfl
    have hneBA : (if nvAddrB = nvAddrA then 1 else 0) = 0 := by decide
    rw [h1B, hba, hneBA] at hEqB; omega
  have hBfree := nv_not_in_objs_freed (o := nvObjB) (by simp [nvDagObjs]) hNotB
  have hPSurv := hPersSurv nvObjP (by simp [nvDagObjs]) rfl
  have hPnotFree : nvObjP ∉ freedObjs nvDagObjs objs' := fun hmem => by
    obtain ⟨oP, hoP, hoPa, _⟩ := hPSurv
    have hcon : (objs'.map LcnfObj.addr).contains nvObjP.addr = true :=
      List.contains_iff_mem.mpr (hoPa ▸ List.mem_map_of_mem (f := LcnfObj.addr) hoP)
    simp only [freedObjs, List.mem_filter, hcon, Bool.not_true, Bool.false_eq_true,
      and_false] at hmem
  have hUnotFree : nvObjU ∉ freedObjs nvDagObjs objs' := fun hmem =>
    nvDag_not_reach_U ((hExact nvObjU (by simp [nvDagObjs]) (by decide)).2 hmem).2
  have hCnotFree : nvObjC ∉ freedObjs nvDagObjs objs' := fun hmem => by
    have hEqC := ((hExact nvObjC (by simp [nvDagObjs]) (by decide)).2 hmem).1
    have hle := nonPersistRefs_filter_le nvDagObjs
      (fun o => !(objs'.map LcnfObj.addr).contains o.addr) nvAddrC
    have h2 : nonPersistRefs nvDagObjs nvAddrC = 2 := by decide
    have h3 : nvObjC.rc.toNat = 3 := rfl
    change _ = _ + nonPersistRefs (nvDagObjs.filter _) _ at hEqC
    rw [h3, show (if nvObjC.addr = nvAddrA then 1 else 0) = 0 by decide,
      show nvObjC.addr = nvAddrC from rfl] at hEqC; omega
  obtain ⟨hfC, oC, hoC, hoCa⟩ := nv_surv_of_not_freed (by simp [nvDagObjs]) hCnotFree
  obtain ⟨hfP, _⟩ := nv_surv_of_not_freed (by simp [nvDagObjs]) hPnotFree
  obtain ⟨hfU, oU, hoU, hoUa⟩ := nv_surv_of_not_freed (by simp [nvDagObjs]) hUnotFree
  have hFreeEq : freedObjs nvDagObjs objs' = [nvObjA, nvObjB] := by
    simp only [freedObjs, List.mem_filter, Bool.not_eq_true'] at hAfree hBfree
    simp only [freedObjs, nvDagObjs, List.filter_cons, List.filter_nil, hAfree.2, hBfree.2, hfC,
      hfP, hfU, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨st', objs', hMeta, hRem, hm', fun o' ho' => ⟨hNotA o' ho', hNotB o' ho'⟩,
    nv_surv_rc hoC hoCa hFreeEq ((hExact nvObjC (by simp [nvDagObjs]) (by decide)).1 oC hoC hoCa)
      (k := 1) (by decide), hPSurv,
    nv_surv_rc hoU hoUa hFreeEq ((hExact nvObjU (by simp [nvDagObjs]) (by decide)).1 oU hoU hoUa)
      (k := 2) (by decide)⟩

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `lcnf_mark_persistent`:
marking root ctor `A` recursively marks closure `B` and shared ctor `C` persistent (`rc=0`),
keeps persistent leaf `P` (`rc=0`), and leaves unreachable ctor `U` untouched (`rc=2`). -/
theorem nv_mark_persistent_dag :
    Func.wp rtC0Env lcnf_mark_persistent.body (nvRtBase, nvAddrA, ()) nvDagMem
    (fun () m' => ∃ st' objs', st'.PreservesMeta nvRtState ∧ st'.rem = nvRtState.rem ∧
      (rtC0Inv nvRtBase st' ⋆ lcnfHeap objs') m' ∧ objs'.length = 5 ∧
      (∀ h0 : 0 < objs'.length, objs'[0].addr = nvAddrA ∧ objs'[0].rc = 0#32) ∧
      (∀ h1 : 1 < objs'.length, objs'[1].addr = nvAddrB ∧ objs'[1].rc = 0#32) ∧
      (∀ h2 : 2 < objs'.length, objs'[2].addr = nvAddrC ∧ objs'[2].rc = 0#32) ∧
      (∀ h3 : 3 < objs'.length, objs'[3].addr = nvAddrP ∧ objs'[3].rc = 0#32) ∧
      (∀ h4 : 4 < objs'.length, objs'[4].addr = nvAddrU ∧ objs'[4].rc = 2#32))
    (fun _ _ _ _ => False) := by
  refine rtC0Env_mark_persistent_wp (nvRtBase, nvAddrA, ()) nvDagMem _ _ ?_
  dsimp [lcnfMarkPersistentSpec]
  simp only [show (nvAddrA &&& 1#64 ≠ 0#64) = False from by decide, ↓reduceIte]
  refine ⟨nvRtState, nvDagObjs, emp, by decide, by rw [sep_emp]; exact nvDagMem_ok,
    ⟨nvObjA, by simp [nvDagObjs], rfl⟩, nvDagObjs_wf, nvDagObjs_closed, ?_⟩
  intro st' objs' m' hMeta hRem ⟨hlen, _, _, _, hZip⟩ hm'; rw [sep_emp] at hm'
  have hlen5 : objs'.length = 5 := by simpa [nvDagObjs] using hlen
  have hAt : ∀ k (hk : k < 5), (nvDagObjs[k], objs'[k]'(by omega)) ∈ nvDagObjs.zip objs' :=
    fun k hk => List.mem_iff_getElem.mpr
      ⟨k, by rw [List.length_zip, hlen5]; simp [nvDagObjs]; omega, by rw [List.getElem_zip]; rfl⟩
  have hRA : NonPersistReach nvDagObjs nvAddrA nvAddrA :=
    NonPersistReach.refl ⟨nvObjA, by simp [nvDagObjs], rfl, by decide⟩
  have hRB : NonPersistReach nvDagObjs nvAddrA nvAddrB := NonPersistReach.step hRA
    ⟨nvObjA, by simp [nvDagObjs], rfl, by decide⟩ (by decide)
    ⟨nvObjB, by simp [nvDagObjs], rfl, by decide⟩
  have hRC : NonPersistReach nvDagObjs nvAddrA nvAddrC := NonPersistReach.step hRB
    ⟨nvObjB, by simp [nvDagObjs], rfl, by decide⟩ (by decide)
    ⟨nvObjC, by simp [nvDagObjs], rfl, by decide⟩
  rcases hZip _ (hAt 0 (by decide)) with ⟨_, h0a, _, _, _, _, _, _, _, _, _, _, _, h0r, _, _⟩
  rcases hZip _ (hAt 1 (by decide)) with ⟨_, h1a, _, _, _, _, _, _, _, _, _, _, _, _, _, h1i⟩
  rcases hZip _ (hAt 2 (by decide)) with ⟨_, h2a, _, _, _, _, _, _, _, _, _, _, _, _, _, h2i⟩
  rcases hZip _ (hAt 3 (by decide)) with ⟨_, h3a, _, _, _, _, _, _, _, _, _, _, _, _, h3o, _⟩
  rcases hZip _ (hAt 4 (by decide)) with ⟨_, h4a, _, _, _, _, _, _, _, _, _, _, _, _, h4o, h4i⟩
  refine ⟨st', objs', hMeta, hRem, hm', hlen5, (fun _ => ⟨h0a, h0r rfl⟩),
    (fun _ => ⟨h1a, (h1i (by dsimp only; decide)).mpr hRB⟩),
    (fun _ => ⟨h2a, (h2i (by dsimp only; decide)).mpr hRC⟩),
    (fun _ => ⟨h3a, h3o.elim id id⟩), (fun _ => ⟨h4a, h4o.elim id fun h =>
      absurd ((h4i (by dsimp only; decide)).mp h) nvDag_not_reach_U⟩)⟩

end

end LeanQbe.T.LeanLCNF
