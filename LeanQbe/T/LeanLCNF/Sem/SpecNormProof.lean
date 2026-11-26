module

public import LeanQbe.T.LeanLCNF.Sem.SpecNorm

/-!
# Runtime Spec Normalization Proofs (`G-R1` & `G-R2`) for `LeanLCNF` Tier-H Semantics

Proves the public `BigNumRt ↔ R0` bijections, separation-footprint equalities, normalized R1→R0
`Spec` refinement bridges into `rtR1Env` and `rtC0CoreEnv`, and `G-R2` coercions between
canonical `natRepR0` and R2b's `NatInHeap`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open Std.ExtHashMap

/-! ## 1. State, Object, Heap, & RC Equivalences (`BigNumRt ↔ R0`) -/

theorem bnStateToRtR0_preservesMeta {st st' : BigNumRt.RtC0State} :
    (bnStateToRtR0 st').PreservesMeta (bnStateToRtR0 st) ↔ st'.PreservesMeta st :=
  Iff.rfl

theorem rtStateToBnR0_preservesMeta {st st' : RtC0State} :
    (rtStateToBnR0 st').PreservesMeta (rtStateToBnR0 st) ↔ st'.PreservesMeta st :=
  Iff.rfl

theorem bnStateToRtR0_bounded48 {st : BigNumRt.RtC0State} :
    (bnStateToRtR0 st).Bounded48 ↔ st.Bounded48 :=
  Iff.rfl

theorem rtStateToBnR0_bounded48 {st : RtC0State} :
    (rtStateToBnR0 st).Bounded48 ↔ st.Bounded48 :=
  Iff.rfl

theorem bnStateToRtR0_hasFree_iff {st : BigNumRt.RtC0State} {bytes : Nat} :
    (bnStateToRtR0 st).hasFree bytes ↔ st.hasFree bytes :=
  Iff.rfl

theorem rtStateToBnR0_hasFree_iff {st : RtC0State} {bytes : Nat} :
    (rtStateToBnR0 st).hasFree bytes ↔ st.hasFree bytes :=
  Iff.rfl

private theorem bnSmallFreeList_eq (bytes : Nat) :
    ∀ (hd : BitVec 64) (xs : List (BitVec 64)),
      BigNumRt.smallFreeList bytes hd xs = smallFreeList bytes hd xs
  | _, [] => rfl
  | _, _ :: rest => by
    funext m
    simp only [BigNumRt.smallFreeList, smallFreeList, BigNumRt.smallFreeNode, smallFreeNode,
      bnSmallFreeList_eq bytes _ rest]
    rfl

private theorem bnSmallPoolsAt_eq (fl : List (BitVec 64)) (pools : Nat → List (BitVec 64)) :
    ∀ n, BigNumRt.smallPoolsAt fl pools n = smallPoolsAt fl pools n
  | 0 => rfl
  | n + 1 => by
    simp only [BigNumRt.smallPoolsAt, smallPoolsAt, BigNumRt.smallPoolSlot, smallPoolSlot,
      bnSmallPoolsAt_eq fl pools n, bnSmallFreeList_eq]

private theorem bnLargeSeg_eq :
    ∀ (hd endPtr : BitVec 64) (xs : List (BitVec 64 × Nat)),
      BigNumRt.largeSeg hd endPtr xs = largeSeg hd endPtr xs
  | _, _, [] => rfl
  | _, endPtr, _ :: rest => by
    funext m
    simp only [BigNumRt.largeSeg, largeSeg, BigNumRt.largeFreeNode, largeFreeNode,
      BigNumRt.rtMaxObjBytes, rtMaxObjBytes, bnLargeSeg_eq _ endPtr rest]
    rfl

theorem bnRtC0Inv_eq (rt : BitVec 64) (st : BigNumRt.RtC0State) :
    BigNumRt.rtC0Inv rt st = rtC0Inv rt (bnStateToRtR0 st) := by
  unfold BigNumRt.rtC0Inv rtC0Inv bnStateToRtR0
  have hAt : LcnfC0BaseRt.At rt st.hdr = LcnfC0Rt.At rt (bnHdrToRtR0 st.hdr) := rfl
  have hSm : BigNumRt.smallPoolsAt st.freeList st.smallPools BigNumRt.rtNumClasses =
      smallPoolsAt st.freeList st.smallPools rtNumClasses :=
    bnSmallPoolsAt_eq st.freeList st.smallPools BigNumRt.rtNumClasses
  have hLg : BigNumRt.largeFreeList st.hdr.s_large_free st.largeNodes =
      largeFreeList st.hdr.s_large_free st.largeNodes :=
    bnLargeSeg_eq st.hdr.s_large_free 0#64 st.largeNodes
  change
    (array64 rt st.extraArgs ⋆
     array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
     array64 (rt + 33024#64) st.freeList ⋆
     LcnfC0BaseRt.At rt st.hdr ⋆
     array64 st.hdr.s_work st.workBuf ⋆
     BigNumRt.smallPoolsAt st.freeList st.smallPools BigNumRt.rtNumClasses ⋆
     BigNumRt.largeFreeList st.hdr.s_large_free st.largeNodes ⋆
     region st.hdr.s_cur st.rem) =
    (array64 rt st.extraArgs ⋆
     array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
     array64 (rt + 33024#64) st.freeList ⋆
     LcnfC0Rt.At rt (bnHdrToRtR0 st.hdr) ⋆
     array64 (bnHdrToRtR0 st.hdr).s_work st.workBuf ⋆
     smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
     largeFreeList (bnHdrToRtR0 st.hdr).s_large_free st.largeNodes ⋆
     region (bnHdrToRtR0 st.hdr).s_cur st.rem)
  rw [hAt, hSm, hLg]
  rfl

theorem rtC0Inv_eq_bn (rt : BitVec 64) (st : RtC0State) :
    rtC0Inv rt st = BigNumRt.rtC0Inv rt (rtStateToBnR0 st) := by
  rw [bnRtC0Inv_eq, bnStateToRtR0_rtStateToBnR0]

theorem fullRtInv_eq_bigNumRtInv (rt : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) :
    fullRtInv rt st scr scrLimbs = bigNumRtInv rt (rtStateToBnR0 st) scr scrLimbs := by
  unfold fullRtInv bigNumRtInv
  rw [rtC0Inv_eq_bn]

theorem bigNumRtInv_eq_fullRtInv (rt : BitVec 64) (st : BigNumRt.RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) :
    bigNumRtInv rt st scr scrLimbs = fullRtInv rt (bnStateToRtR0 st) scr scrLimbs := by
  rw [fullRtInv_eq_bigNumRtInv, rtStateToBnR0_bnStateToRtR0]

theorem bnObjMem_eq (o : BigNumRt.LcnfObj) :
    BigNumRt.lcnfObjMem o = lcnfObjMem (bnObjToRtR0 o) :=
  rfl

theorem rtObjMem_eq_bn (o : LcnfObj) :
    lcnfObjMem o = BigNumRt.lcnfObjMem (rtObjToBnR0 o) :=
  rfl

theorem bnHeap_eq : ∀ (objs : List BigNumRt.LcnfObj),
    BigNumRt.lcnfHeap objs = lcnfHeap (objs.map bnObjToRtR0)
  | [] => rfl
  | o :: os => by
    simp only [BigNumRt.lcnfHeap, List.map_cons, lcnfHeap, bnHeap_eq os, bnObjMem_eq]

theorem rtHeap_eq_bn (objs : List LcnfObj) :
    lcnfHeap objs = BigNumRt.lcnfHeap (objs.map rtObjToBnR0) := by
  rw [bnHeap_eq, List.map_map]
  have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  rw [hcomp, List.map_id]

theorem bnObjWf_iff (o : BigNumRt.LcnfObj) : o.Wf ↔ (bnObjToRtR0 o).Wf :=
  Iff.rfl

theorem rtObjWf_iff (o : LcnfObj) : o.Wf ↔ (rtObjToBnR0 o).Wf :=
  Iff.rfl

theorem bnHeapClosed_iff (objs : List BigNumRt.LcnfObj) :
    BigNumRt.lcnfHeapClosed objs ↔ lcnfHeapClosed (objs.map bnObjToRtR0) := by
  constructor
  · intro h o ho f hf h0
    obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
    obtain ⟨bo', hbo', haddr⟩ := h bo hbo f hf h0
    exact ⟨bnObjToRtR0 bo', List.mem_map_of_mem hbo', haddr⟩
  · intro h bo hbo f hf h0
    obtain ⟨o', ho', haddr⟩ := h (bnObjToRtR0 bo) (List.mem_map_of_mem hbo) f hf h0
    obtain ⟨bo', hbo', rfl⟩ := List.mem_map.mp ho'
    exact ⟨bo', hbo', haddr⟩

theorem rtHeapClosed_iff (objs : List LcnfObj) :
    lcnfHeapClosed objs ↔ BigNumRt.lcnfHeapClosed (objs.map rtObjToBnR0) := by
  have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  rw [bnHeapClosed_iff, List.map_map, hcomp, List.map_id]

private theorem bnNonPersistRefs_aux (addr : BitVec 64) :
    ∀ (objs : List BigNumRt.LcnfObj) (acc : Nat),
      objs.foldl (fun a p => if p.rc = 0#32 then a else a + p.childFields.count addr) acc =
      (objs.map bnObjToRtR0).foldl
        (fun a p => if p.rc = 0#32 then a else a + p.childFields.count addr) acc
  | [], _ => rfl
  | _ :: os, _ => bnNonPersistRefs_aux addr os _

theorem bnNonPersistRefs_eq (objs : List BigNumRt.LcnfObj) (addr : BitVec 64) :
    BigNumRt.nonPersistRefs objs addr = nonPersistRefs (objs.map bnObjToRtR0) addr :=
  bnNonPersistRefs_aux addr objs 0

theorem rtNonPersistRefs_eq (objs : List LcnfObj) (addr : BitVec 64) :
    nonPersistRefs objs addr = BigNumRt.nonPersistRefs (objs.map rtObjToBnR0) addr := by
  have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  rw [bnNonPersistRefs_eq, List.map_map, hcomp, List.map_id]

theorem bnRcSound_iff (root : BitVec 64) (objs : List BigNumRt.LcnfObj) :
    BigNumRt.RcSound root objs ↔ RcSound root (objs.map bnObjToRtR0) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro p hp hrc f hf h0
      obtain ⟨bp, hbp, rfl⟩ := List.mem_map.mp hp
      obtain ⟨bq, hbq, haddr, hqrc⟩ := h1 bp hbp hrc f hf h0
      exact ⟨bnObjToRtR0 bq, List.mem_map_of_mem hbq, haddr, hqrc⟩
    · intro y hy hpos
      obtain ⟨by0, hby, rfl⟩ := List.mem_map.mp hy
      rw [← bnNonPersistRefs_eq]
      exact h2 by0 hby hpos
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro bp hbp hrc f hf h0
      obtain ⟨q, hq, haddr, hqrc⟩ := h1 (bnObjToRtR0 bp) (List.mem_map_of_mem hbp) hrc f hf h0
      obtain ⟨bq, hbq, rfl⟩ := List.mem_map.mp hq
      exact ⟨bq, hbq, haddr, hqrc⟩
    · intro by0 hby hpos
      rw [bnNonPersistRefs_eq]
      exact h2 (bnObjToRtR0 by0) (List.mem_map_of_mem hby) hpos

theorem rtRcSound_iff (root : BitVec 64) (objs : List LcnfObj) :
    RcSound root objs ↔ BigNumRt.RcSound root (objs.map rtObjToBnR0) := by
  have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  rw [bnRcSound_iff, List.map_map, hcomp, List.map_id]

private theorem bnNonPersistReach_of_rt {objs : List BigNumRt.LcnfObj} {root x : BitVec 64}
    (h : NonPersistReach (objs.map bnObjToRtR0) root x) :
    BigNumRt.NonPersistReach objs root x := by
  induction h with
  | refl hex =>
    obtain ⟨o, ho, haddr, hrc⟩ := hex
    obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
    exact BigNumRt.NonPersistReach.refl ⟨bo, hbo, haddr, hrc⟩
  | step _ hch h0 hex ih =>
    obtain ⟨o, ho, haddr, hmem⟩ := hch
    obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
    obtain ⟨o', ho', haddr', hrc'⟩ := hex
    obtain ⟨bo', hbo', rfl⟩ := List.mem_map.mp ho'
    exact BigNumRt.NonPersistReach.step ih ⟨bo, hbo, haddr, hmem⟩ h0 ⟨bo', hbo', haddr', hrc'⟩

private theorem rtNonPersistReach_of_bn {objs : List BigNumRt.LcnfObj} {root x : BitVec 64}
    (h : BigNumRt.NonPersistReach objs root x) :
    NonPersistReach (objs.map bnObjToRtR0) root x := by
  induction h with
  | refl hex =>
    obtain ⟨bo, hbo, haddr, hrc⟩ := hex
    exact NonPersistReach.refl ⟨bnObjToRtR0 bo, List.mem_map_of_mem hbo, haddr, hrc⟩
  | step _ hch h0 hex ih =>
    obtain ⟨bo, hbo, haddr, hmem⟩ := hch
    obtain ⟨bo', hbo', haddr', hrc'⟩ := hex
    exact NonPersistReach.step ih
      ⟨bnObjToRtR0 bo, List.mem_map_of_mem hbo, haddr, hmem⟩ h0
      ⟨bnObjToRtR0 bo', List.mem_map_of_mem hbo', haddr', hrc'⟩

theorem bnNonPersistReach_iff (objs : List BigNumRt.LcnfObj) (root x : BitVec 64) :
    BigNumRt.NonPersistReach objs root x ↔ NonPersistReach (objs.map bnObjToRtR0) root x :=
  ⟨rtNonPersistReach_of_bn, bnNonPersistReach_of_rt⟩

private theorem bnFreedObjs_map (objs : List BigNumRt.LcnfObj) (objs' : List LcnfObj) :
    (BigNumRt.freedObjs objs (objs'.map rtObjToBnR0)).map bnObjToRtR0 =
      freedObjs (objs.map bnObjToRtR0) objs' := by
  have haddrs : (objs'.map rtObjToBnR0).map BigNumRt.LcnfObj.addr = objs'.map LcnfObj.addr := by
    rw [List.map_map]; rfl
  unfold BigNumRt.freedObjs freedObjs
  rw [haddrs, List.filter_map]
  rfl

private theorem bnDecColdRel_of_rt {root : BitVec 64} {objs : List BigNumRt.LcnfObj}
    {objs' : List LcnfObj} (h : DecColdRel root (objs.map bnObjToRtR0) objs') :
    BigNumRt.DecColdRel root objs (objs'.map rtObjToBnR0) := by
  have hback : (objs'.map rtObjToBnR0).map bnObjToRtR0 = objs' := by
    rw [List.map_map]
    have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
    rw [hcomp, List.map_id]
  rcases h with ⟨hroot, hwf, hcl, hcl', hall', hpers', hrefs', hpersKeep, hdrop⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨o, ho, haddr, hrc⟩ := hroot
    obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
    exact ⟨bo, hbo, haddr, hrc⟩
  · intro bo hbo; exact hwf (bnObjToRtR0 bo) (List.mem_map_of_mem hbo)
  · exact (bnHeapClosed_iff objs).mpr hcl
  · exact (bnHeapClosed_iff (objs'.map rtObjToBnR0)).mpr (by rwa [hback])
  · intro bo' hbo'
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hbo'
    obtain ⟨hwf', hne, o, ho, hrest⟩ := hall' o' ho'
    obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
    exact ⟨hwf', hne, bo, hbo, hrest⟩
  · intro bp hbp hrc f hf h0
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hbp
    obtain ⟨q, hq, haddr, hqrc⟩ := hpers' p hp hrc f hf h0
    exact ⟨rtObjToBnR0 q, List.mem_map_of_mem hq, haddr, hqrc⟩
  · intro by0 hby hpos
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hby
    rw [bnNonPersistRefs_eq, hback]
    exact hrefs' y hy hpos
  · intro bo hbo hrc
    obtain ⟨o', ho', haddr, hrc'⟩ := hpersKeep (bnObjToRtR0 bo) (List.mem_map_of_mem hbo) hrc
    exact ⟨rtObjToBnR0 o', List.mem_map_of_mem ho', haddr, hrc'⟩
  · intro bo hbo hpos
    have hd := hdrop (bnObjToRtR0 bo) (List.mem_map_of_mem hbo) hpos
    have hnr : BigNumRt.nonPersistRefs (BigNumRt.freedObjs objs (objs'.map rtObjToBnR0)) bo.addr =
        nonPersistRefs (freedObjs (objs.map bnObjToRtR0) objs') bo.addr := by
      rw [bnNonPersistRefs_eq, bnFreedObjs_map]
    dsimp only at hd ⊢
    rw [hnr]
    refine ⟨?_, ?_⟩
    · intro bo' hbo' haddr
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hbo'
      exact hd.1 o' ho' haddr
    · intro hmem
      have hmem' : bnObjToRtR0 bo ∈ freedObjs (objs.map bnObjToRtR0) objs' := by
        rw [← bnFreedObjs_map]; exact List.mem_map_of_mem hmem
      obtain ⟨hrc, hreach⟩ := hd.2 hmem'
      exact ⟨hrc, bnNonPersistReach_of_rt hreach⟩

theorem bnDecColdRel_iff {root : BitVec 64} {objs : List BigNumRt.LcnfObj}
    {objs' : List LcnfObj} :
    BigNumRt.DecColdRel root objs (objs'.map rtObjToBnR0) ↔
      DecColdRel root (objs.map bnObjToRtR0) objs' := by
  constructor
  · intro h
    have hback : (objs'.map rtObjToBnR0).map bnObjToRtR0 = objs' := by
      rw [List.map_map]
      have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
      rw [hcomp, List.map_id]
    rcases h with ⟨hroot, hwf, hcl, hcl', hall', hpers', hrefs', hpersKeep, hdrop⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨bo, hbo, haddr, hrc⟩ := hroot
      exact ⟨bnObjToRtR0 bo, List.mem_map_of_mem hbo, haddr, hrc⟩
    · intro o ho
      obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
      exact hwf bo hbo
    · exact (bnHeapClosed_iff objs).mp hcl
    · rwa [← hback, ← bnHeapClosed_iff]
    · intro o' ho'
      obtain ⟨hwf', hne, bo, hbo, hrest⟩ := hall' (rtObjToBnR0 o') (List.mem_map_of_mem ho')
      exact ⟨hwf', hne, bnObjToRtR0 bo, List.mem_map_of_mem hbo, hrest⟩
    · intro p hp hrc f hf h0
      obtain ⟨bq, hbq, haddr, hqrc⟩ := hpers' (rtObjToBnR0 p) (List.mem_map_of_mem hp) hrc f hf h0
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hbq
      exact ⟨q, hq, haddr, hqrc⟩
    · intro y hy hpos
      rw [rtNonPersistRefs_eq]
      exact hrefs' (rtObjToBnR0 y) (List.mem_map_of_mem hy) hpos
    · intro o ho hrc
      obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
      obtain ⟨bo', hbo', haddr, hrc'⟩ := hpersKeep bo hbo hrc
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hbo'
      exact ⟨o', ho', haddr, hrc'⟩
    · intro o ho hpos
      obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
      have hd := hdrop bo hbo hpos
      have hnr : BigNumRt.nonPersistRefs (BigNumRt.freedObjs objs (objs'.map rtObjToBnR0)) bo.addr =
          nonPersistRefs (freedObjs (objs.map bnObjToRtR0) objs') bo.addr := by
        rw [bnNonPersistRefs_eq, bnFreedObjs_map]
      dsimp only at hd ⊢
      rw [show (bnObjToRtR0 bo).addr = bo.addr from rfl, ← hnr]
      refine ⟨?_, ?_⟩
      · intro o' ho' haddr
        exact hd.1 (rtObjToBnR0 o') (List.mem_map_of_mem ho') haddr
      · intro hmem
        have hmem' : bo ∈ BigNumRt.freedObjs objs (objs'.map rtObjToBnR0) := by
          unfold BigNumRt.freedObjs
          have haddrs : (objs'.map rtObjToBnR0).map BigNumRt.LcnfObj.addr =
              objs'.map LcnfObj.addr := by rw [List.map_map]; rfl
          rw [haddrs]
          unfold freedObjs at hmem
          rcases List.mem_filter.mp hmem with ⟨_, hnot⟩
          exact List.mem_filter.mpr ⟨hbo, hnot⟩
        obtain ⟨hrc, hreach⟩ := hd.2 hmem'
        exact ⟨hrc, rtNonPersistReach_of_bn hreach⟩
  · exact bnDecColdRel_of_rt

theorem mpzNatCanonR0_iff (obj : BigNumRt.LcnfObj) (n : Nat) :
    mpzNatCanonR0 (bnObjToRtR0 obj) n ↔ mpzNatCanon obj n :=
  Iff.rfl

theorem mpzNatCanonR0_rt_iff (obj : LcnfObj) (n : Nat) :
    mpzNatCanonR0 obj n ↔ mpzNatCanon (rtObjToBnR0 obj) n :=
  Iff.rfl

theorem natRepR0_iff (w : BitVec 64) (n : Nat) (objs : List BigNumRt.LcnfObj) :
    natRepR0 w n (objs.map bnObjToRtR0) ↔ natRep w n objs := by
  unfold natRepR0 natRep
  split
  · exact Iff.rfl
  · constructor
    · rintro ⟨hw, o, ho, had, hc⟩
      obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
      exact ⟨hw, bo, hbo, had, hc⟩
    · rintro ⟨hw, bo, hbo, had, hc⟩
      exact ⟨hw, bnObjToRtR0 bo, List.mem_map_of_mem hbo, had, hc⟩

theorem natRepR0_rt_iff (w : BitVec 64) (n : Nat) (objs : List LcnfObj) :
    natRepR0 w n objs ↔ natRep w n (objs.map rtObjToBnR0) := by
  have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  rw [← natRepR0_iff w n (objs.map rtObjToBnR0), List.map_map, hcomp, List.map_id]

theorem mpzIntCanonR0_iff (obj : BigNumRt.LcnfObj) (z : Int) :
    mpzIntCanonR0 (bnObjToRtR0 obj) z ↔ mpzIntCanon obj z :=
  Iff.rfl

theorem intRepR0_iff (w : BitVec 64) (z : Int) (objs : List BigNumRt.LcnfObj) :
    intRepR0 w z (objs.map bnObjToRtR0) ↔ intRep w z objs := by
  unfold intRepR0 intRep
  split
  · exact Iff.rfl
  · constructor
    · rintro ⟨hw, o, ho, had, hc⟩
      obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp ho
      exact ⟨hw, bo, hbo, had, hc⟩
    · rintro ⟨hw, bo, hbo, had, hc⟩
      exact ⟨hw, bnObjToRtR0 bo, List.mem_map_of_mem hbo, had, hc⟩

theorem intRepR0_rt_iff (w : BitVec 64) (z : Int) (objs : List LcnfObj) :
    intRepR0 w z objs ↔ intRep w z (objs.map rtObjToBnR0) := by
  have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  rw [← intRepR0_iff w z (objs.map rtObjToBnR0), List.map_map, hcomp, List.map_id]

theorem canAllocBytesR0_iff (st : RtC0State) (bytes : Nat) :
    canAllocBytesR0 st bytes ↔ canAllocBytes (rtStateToBnR0 st) bytes :=
  Iff.rfl

theorem natPowOkR0_iff (aVal bVal scrCap : Nat) (st : RtC0State) :
    natPowOkR0 aVal bVal scrCap st ↔ natPowOk aVal bVal scrCap (rtStateToBnR0 st) :=
  Iff.rfl

theorem natGcdOkR0_iff (aVal bVal scrCap : Nat) (st : RtC0State) :
    natGcdOkR0 aVal bVal scrCap st ↔ natGcdOk aVal bVal scrCap (rtStateToBnR0 st) :=
  Iff.rfl

theorem natArithOkR0_iff (op aVal bVal scrCap : Nat) (st : RtC0State) :
    natArithOkR0 op aVal bVal scrCap st ↔ natArithOk op aVal bVal scrCap (rtStateToBnR0 st) :=
  Iff.rfl

theorem natArithPostR0_iff (op aVal bVal : Nat) (res : BitVec 64)
    (objs : List LcnfObj) (objs' : List BigNumRt.LcnfObj) :
    natArithPost op aVal bVal res (objs.map rtObjToBnR0) objs' ↔
      natArithPostR0 op aVal bVal res objs (objs'.map bnObjToRtR0) := by
  unfold natArithPost natArithPostR0
  have hcompR : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  have hcompB : rtObjToBnR0 ∘ bnObjToRtR0 = id := funext rtObjToBnR0_bnObjToRtR0
  split
  · constructor
    · rintro ⟨hr, he⟩; refine ⟨hr, ?_⟩
      have h1 := congrArg (List.map bnObjToRtR0) he
      simpa [List.map_map, hcompR] using h1
    · rintro ⟨hr, he⟩; refine ⟨hr, ?_⟩
      have h1 := congrArg (List.map rtObjToBnR0) he
      simpa [List.map_map, hcompB] using h1
  · split
    · constructor
      · rintro ⟨hr, he⟩; refine ⟨hr, ?_⟩
        have h1 := congrArg (List.map bnObjToRtR0) he
        simpa [List.map_map, hcompR] using h1
      · rintro ⟨hr, he⟩; refine ⟨hr, ?_⟩
        have h1 := congrArg (List.map rtObjToBnR0) he
        simpa [List.map_map, hcompB] using h1
    · split
      · constructor
        · rintro ⟨hr, he⟩; refine ⟨hr, ?_⟩
          have h1 := congrArg (List.map bnObjToRtR0) he
          simpa [List.map_map, hcompR] using h1
        · rintro ⟨hr, he⟩; refine ⟨hr, ?_⟩
          have h1 := congrArg (List.map rtObjToBnR0) he
          simpa [List.map_map, hcompB] using h1
      · constructor
        · rintro ⟨hrep, hsub⟩
          refine ⟨(natRepR0_iff res _ objs').mpr hrep, fun o ho => ?_⟩
          exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hsub _ (List.mem_map_of_mem ho))
        · rintro ⟨hrep, hsub⟩
          refine ⟨(natRepR0_iff res _ objs').mp hrep, fun bo hbo => ?_⟩
          obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hbo
          obtain ⟨bo', hbo', hba⟩ := List.mem_map.mp (hsub o ho)
          simpa [rtObjToBnR0_bnObjToRtR0] using hba ▸ hbo'

theorem natBitsOkR0_iff (op : Nat) (aVal : Nat) (bRaw : BitVec 64) (objs : List LcnfObj)
    (scrCap : Nat) (st : RtC0State) :
    natBitsOkR0 op aVal bRaw objs scrCap st ↔
      natBitsOk op aVal bRaw (objs.map rtObjToBnR0) scrCap (rtStateToBnR0 st) := by
  unfold natBitsOkR0 natBitsOk
  split
  · exact Iff.rfl
  · split
    · exact Iff.rfl
    · split
      · exact Iff.rfl
      · constructor
        · rintro ⟨bVal, hb, hrest⟩
          exact ⟨bVal, (natRepR0_rt_iff bRaw bVal objs).mp hb, hrest⟩
        · rintro ⟨bVal, hb, hrest⟩
          exact ⟨bVal, (natRepR0_rt_iff bRaw bVal objs).mpr hb, hrest⟩

theorem natBitsPostR0_iff (op : Nat) (aVal : Nat) (bRaw res : BitVec 64)
    (objs : List LcnfObj) (objs' : List BigNumRt.LcnfObj) :
    natBitsPost op aVal bRaw res (objs.map rtObjToBnR0) objs' ↔
      natBitsPostR0 op aVal bRaw res objs (objs'.map bnObjToRtR0) := by
  unfold natBitsPost natBitsPostR0
  have hcompR : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  have hcompB : rtObjToBnR0 ∘ bnObjToRtR0 = id := funext rtObjToBnR0_bnObjToRtR0
  split
  · constructor
    · rintro ⟨he, hr⟩
      exact ⟨by have h1 := congrArg (List.map bnObjToRtR0) he
                simpa [List.map_map, hcompR] using h1, hr⟩
    · rintro ⟨he, hr⟩
      exact ⟨by have h1 := congrArg (List.map rtObjToBnR0) he
                simpa [List.map_map, hcompB] using h1, hr⟩
  · split
    · constructor
      · rintro ⟨hrep, hsub⟩
        refine ⟨(natRepR0_iff res _ objs').mpr hrep, fun o ho => ?_⟩
        exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hsub _ (List.mem_map_of_mem ho))
      · rintro ⟨hrep, hsub⟩
        refine ⟨(natRepR0_iff res _ objs').mp hrep, fun bo hbo => ?_⟩
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hbo
        obtain ⟨bo', hbo', hba⟩ := List.mem_map.mp (hsub o ho)
        simpa [rtObjToBnR0_bnObjToRtR0] using hba ▸ hbo'
    · split
      · constructor
        · rintro ⟨hrep, he⟩
          exact ⟨(natRepR0_iff res _ objs').mpr hrep,
            by have h1 := congrArg (List.map bnObjToRtR0) he
               simpa [List.map_map, hcompR] using h1⟩
        · rintro ⟨hrep, he⟩
          exact ⟨(natRepR0_iff res _ objs').mp hrep,
            by have h1 := congrArg (List.map rtObjToBnR0) he
               simpa [List.map_map, hcompB] using h1⟩
      · constructor
        · rintro ⟨bVal, hb, hsub, hres⟩
          refine ⟨bVal, (natRepR0_rt_iff bRaw bVal objs).mpr hb, fun o ho => ?_, ?_⟩
          · exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hsub _ (List.mem_map_of_mem ho))
          · repeat first
              | (split at hres <;> rename_i hc <;> simp only [hc, ↓reduceIte]
                 first
                   | exact (natRepR0_iff _ _ objs').mpr hres
                   | exact False.elim hres)
              | exact False.elim hres
        · rintro ⟨bVal, hb, hsub, hres⟩
          refine ⟨bVal, (natRepR0_rt_iff bRaw bVal objs).mp hb, fun bo hbo => ?_, ?_⟩
          · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hbo
            obtain ⟨bo', hbo', hba⟩ := List.mem_map.mp (hsub o ho)
            simpa [rtObjToBnR0_bnObjToRtR0] using hba ▸ hbo'
          · repeat first
              | (split at hres <;> rename_i hc <;> simp only [hc, ↓reduceIte]
                 first
                   | exact (natRepR0_iff _ _ objs').mp hres
                   | exact False.elim hres)
              | exact False.elim hres

/-! ## 2. Normalized R1 `Spec` Bridges (`SpecNorm → rtR1Env / rtC0CoreEnv`, `G-R1`) -/

theorem lcnfNatAllocSpecR0_to_bn {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatAllocSpecR0 xs m Q X) : lcnfNatAllocSpec xs m Q X := by
  rcases xs with ⟨rt, nlimbs, ⟨⟩⟩
  rcases h with ⟨st, R, hmax, hbd, hfr, hm, hk⟩
  rw [rtC0Inv_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, R, hmax, hbd, hfr, hm, fun p st' m' hwf hp0 hpr hle hbd' hm' => ?_⟩
  rw [bnRtC0Inv_eq, bnObjMem_eq] at hm'
  exact hk p (bnStateToRtR0 st') m' hwf hp0 hpr hle hbd' hm'

theorem lcnfNatAllocSpecR0_le_rtR1Env {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatAllocSpecR0 xs m Q X) :
    rtR1Env "lcnf_nat_alloc" [i64, i64] [i64] xs m Q X :=
  rtR1Env_lcnf_nat_alloc (lcnfNatAllocSpecR0_to_bn h)

theorem lcnfNatAllocSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatAllocSpecR0 xs m Q X) :
    rtC0CoreEnv "lcnf_nat_alloc" [i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (lcnfNatAllocSpecR0_le_rtR1Env h)

private theorem decNatRelR0_of_bn {a : BitVec 64} {st st' : BigNumRt.RtC0State}
    {objs objs' : List BigNumRt.LcnfObj} (h : DecNatRel a st st' objs objs') :
    DecNatRelR0 a (bnStateToRtR0 st) (bnStateToRtR0 st')
      (objs.map bnObjToRtR0) (objs'.map bnObjToRtR0) := by
  rcases h with ⟨hodd, rfl, rfl⟩ | ⟨hev, obj, hmem, ha, hrc, rfl, rfl⟩ |
      ⟨hev, i, hi, ha, hgt, rfl, rfl⟩ | ⟨hev, hpm, hrem, hrel⟩
  · exact Or.inl ⟨hodd, rfl, rfl⟩
  · exact Or.inr <| Or.inl ⟨hev, bnObjToRtR0 obj, List.mem_map_of_mem hmem, ha, hrc, rfl, rfl⟩
  · refine Or.inr <| Or.inr <| Or.inl ⟨hev, i, by simpa using hi, ?_, ?_, rfl, ?_⟩
    · simp only [List.getElem_map]; exact ha
    · simp only [List.getElem_map]; exact hgt
    · rw [List.map_set]; simp only [List.getElem_map]; rfl
  · have hback : objs' = (objs'.map bnObjToRtR0).map rtObjToBnR0 := by
      rw [List.map_map]
      have hcomp : rtObjToBnR0 ∘ bnObjToRtR0 = id := funext rtObjToBnR0_bnObjToRtR0
      rw [hcomp, List.map_id]
    rw [hback] at hrel
    exact Or.inr <| Or.inr <| Or.inr ⟨hev, hpm, hrem, (bnDecColdRel_iff).mp hrel⟩

theorem bnDecNatSpecR0_to_bn {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : bnDecNatSpecR0 xs m Q X) : bnDecNatSpec xs m Q X := by
  rcases xs with ⟨rt, a, ⟨⟩⟩
  dsimp only [bnDecNatSpecR0, bnDecNatSpec] at h ⊢
  by_cases ha : (a &&& 1#64) ≠ 0#64
  · rw [ite_eq_left ha] at h ⊢; exact h
  · rw [ite_eq_right ha] at h ⊢
    rcases h with ⟨st, objs, R, hcap, hm, hmem, hwf, hcl, hrc, hk⟩
    rw [rtC0Inv_eq_bn, rtHeap_eq_bn] at hm
    refine ⟨rtStateToBnR0 st, objs.map rtObjToBnR0, R,
      (rtStateToBnR0_workCap st).symm ▸ (by simpa using hcap), hm, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hmem with ⟨obj, ho, had⟩
      exact ⟨rtObjToBnR0 obj, List.mem_map_of_mem ho, had⟩
    · intro bo hbo
      rcases List.mem_map.mp hbo with ⟨o, ho, rfl⟩
      exact hwf o ho
    · exact (rtHeapClosed_iff objs).mp hcl
    · intro bo hbo had hrc1
      rcases List.mem_map.mp hbo with ⟨o, ho, rfl⟩
      exact (rtRcSound_iff a objs).mp (hrc o ho had hrc1)
    · intro st' objs' m' hrel hm'
      rw [bnRtC0Inv_eq, bnHeap_eq] at hm'
      have hrel' := decNatRelR0_of_bn hrel
      rw [bnStateToRtR0_rtStateToBnR0, List.map_map] at hrel'
      have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
      rw [hcomp, List.map_id] at hrel'
      exact hk (bnStateToRtR0 st') (objs'.map bnObjToRtR0) m' hrel' hm'

theorem bnDecNatSpecR0_le_rtR1Env {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : bnDecNatSpecR0 xs m Q X) :
    rtR1Env "bn_dec_nat" [i64, i64] [] xs m Q X :=
  rtR1Env_bn_dec_nat (bnDecNatSpecR0_to_bn h)

theorem bnDecNatSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : bnDecNatSpecR0 xs m Q X) :
    rtC0CoreEnv "bn_dec_nat" [i64, i64] [] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (bnDecNatSpecR0_le_rtR1Env h)

theorem bnNatPowSpecR0_to_bn {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatPowSpecR0 xs m Q X) : bnNatPowSpec xs m Q X := by
  rcases xs with ⟨rt, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hok, hm, hk⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, aVal, bVal, R,
    hwf, (natRepR0_rt_iff a aVal objs).mp ha, (natRepR0_rt_iff b bVal objs).mp hb,
    hok, hm, fun res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep1 hkeep2 hm' => ?_⟩
  rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
  refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
    ((natRepR0_iff res _ objs').mpr hres) ?_ ?_ hm'
  · intro o ho haddr
    exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep1 _ (List.mem_map_of_mem ho) haddr)
  · intro o ho hne
    exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep2 _ (List.mem_map_of_mem ho) hne)

theorem bnNatPowSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatPowSpecR0 xs m Q X) :
    rtR1Env "bn_nat_pow" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_bn_nat_pow (bnNatPowSpecR0_to_bn h)

theorem bnNatPowSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatPowSpecR0 xs m Q X) :
    rtC0CoreEnv "bn_nat_pow" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (bnNatPowSpecR0_le_rtR1Env h)

theorem bnNatGcdSpecR0_to_bn {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatGcdSpecR0 xs m Q X) : bnNatGcdSpec xs m Q X := by
  rcases xs with ⟨rt, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hok, hm, hk⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, aVal, bVal, R,
    hwf, (natRepR0_rt_iff a aVal objs).mp ha, (natRepR0_rt_iff b bVal objs).mp hb,
    hok, hm, fun res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm' => ?_⟩
  rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
  refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
    ((natRepR0_iff res _ objs').mpr hres) ?_ hm'
  intro o ho
  exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep _ (List.mem_map_of_mem ho))

theorem bnNatGcdSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatGcdSpecR0 xs m Q X) :
    rtR1Env "bn_nat_gcd" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_bn_nat_gcd (bnNatGcdSpecR0_to_bn h)

theorem bnNatGcdSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatGcdSpecR0 xs m Q X) :
    rtC0CoreEnv "bn_nat_gcd" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (bnNatGcdSpecR0_le_rtR1Env h)

theorem lcnfNatArithSpecR0_to_bn {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatArithSpecR0 xs m Q X) : lcnfNatArithSpec xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hok, hm, hk⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, aVal, bVal, R, hwf,
    (natRepR0_rt_iff a aVal objs).mp ha,
    hb.imp id fun hb' => (natRepR0_rt_iff b bVal objs).mp hb',
    hok, hm, fun res st' scrLimbs' objs' m' hpr hrem hwf' hpost hm' => ?_⟩
  rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
  exact hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
    ((natArithPostR0_iff op.toNat aVal bVal res objs objs').mp hpost) hm'

theorem lcnfNatArithSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfNatArithSpecR0 xs m Q X) :
    rtR1Env "lcnf_nat_arith" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_lcnf_nat_arith (lcnfNatArithSpecR0_to_bn h)

theorem lcnfNatArithSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfNatArithSpecR0 xs m Q X) :
    rtC0CoreEnv "lcnf_nat_arith" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (lcnfNatArithSpecR0_le_rtR1Env h)

theorem lcnfNatBitsSpecR0_to_bn {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatBitsSpecR0 xs m Q X) : lcnfNatBitsSpec xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, aVal, R, hwf, ha, hok, hm, hk⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, aVal, R, hwf, ?_,
    (natBitsOkR0_iff op.toNat aVal b objs scrLimbs.length st).mp hok, hm,
    fun res st' scrLimbs' objs' m' hpr hrem hwf' hpost hm' => ?_⟩
  · split at ha <;> rename_i hc <;> simp only [hc, ↓reduceIte]
    · exact ha
    · exact (natRepR0_rt_iff a aVal objs).mp ha
  · rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
    exact hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
      ((natBitsPostR0_iff op.toNat aVal b res objs objs').mp hpost) hm'

theorem lcnfNatBitsSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfNatBitsSpecR0 xs m Q X) :
    rtR1Env "lcnf_nat_bits" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_lcnf_nat_bits (lcnfNatBitsSpecR0_to_bn h)

theorem lcnfNatBitsSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfNatBitsSpecR0 xs m Q X) :
    rtC0CoreEnv "lcnf_nat_bits" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (lcnfNatBitsSpecR0_le_rtR1Env h)

theorem lcnfNatSlowSpecR0_to_bn {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatSlowSpecR0 xs m Q X) : lcnfNatSlowSpec xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, R, hwf, hm, hbody⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, R, hwf, hm, ?_⟩
  by_cases h1 : op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17]
  · rw [ite_eq_left h1] at hbody ⊢
    rcases hbody with ⟨aVal, bVal, ha, hb, hok, hk⟩
    refine ⟨aVal, bVal, (natRepR0_rt_iff a aVal objs).mp ha,
      hb.imp id fun hb' => (natRepR0_rt_iff b bVal objs).mp hb', hok,
      fun res st' scrLimbs' objs' m' hpr hrem hwf' hpost hm' => ?_⟩
    rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
    exact hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
      ((natArithPostR0_iff op.toNat aVal bVal res objs objs').mp hpost) hm'
  · rw [ite_eq_right h1] at hbody ⊢
    by_cases h2 : op.toNat ∈ [9, 10, 11, 12, 13, 14, 15, 19]
    · rw [ite_eq_left h2] at hbody ⊢
      rcases hbody with ⟨aVal, ha, hok, hk⟩
      refine ⟨aVal, ?_, (natBitsOkR0_iff op.toNat aVal b objs scrLimbs.length st).mp hok,
        fun res st' scrLimbs' objs' m' hpr hrem hwf' hpost hm' => ?_⟩
      · split at ha <;> rename_i hc <;> simp only [hc, ↓reduceIte]
        · exact ha
        · exact (natRepR0_rt_iff a aVal objs).mp ha
      · rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
        exact hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
          ((natBitsPostR0_iff op.toNat aVal b res objs objs').mp hpost) hm'
    · rw [ite_eq_right h2] at hbody ⊢
      by_cases h3 : op.toNat = 16
      · rw [ite_eq_left h3] at hbody ⊢
        rcases hbody with ⟨aVal, bVal, ha, hb, hok, hk⟩
        refine ⟨aVal, bVal, (natRepR0_rt_iff a aVal objs).mp ha,
          (natRepR0_rt_iff b bVal objs).mp hb, hok,
          fun res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm' => ?_⟩
        rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
        refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
          ((natRepR0_iff res _ objs').mpr hres) ?_ hm'
        intro o ho _
        exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep _ (List.mem_map_of_mem ho) ‹_›)
      · rw [ite_eq_right h3] at hbody ⊢
        by_cases h4 : op.toNat = 18
        · rw [ite_eq_left h4] at hbody ⊢
          rcases hbody with ⟨aVal, bVal, ha, hb, hok, hk⟩
          refine ⟨aVal, bVal, (natRepR0_rt_iff a aVal objs).mp ha,
            (natRepR0_rt_iff b bVal objs).mp hb, hok,
            fun res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm' => ?_⟩
          rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
          refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
            ((natRepR0_iff res _ objs').mpr hres) ?_ hm'
          intro o ho
          exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep _ (List.mem_map_of_mem ho))
        · rw [ite_eq_right h4] at hbody
          exact False.elim hbody

theorem lcnfNatSlowSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfNatSlowSpecR0 xs m Q X) :
    rtR1Env "lcnf_nat_slow" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_lcnf_nat_slow (lcnfNatSlowSpecR0_to_bn h)

theorem lcnfNatSlowSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfNatSlowSpecR0 xs m Q X) :
    rtC0CoreEnv "lcnf_nat_slow" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (lcnfNatSlowSpecR0_le_rtR1Env h)

private theorem intConv1_body_aux {rt : BitVec 64} {st : RtC0State} {scr : BitVec 64}
    {objs : List LcnfObj} {R : Mem 64 → Prop} {Q : Post [i64]}
    (z : Int)
    (hk : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
      intRepR0 res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta (rtStateToBnR0 st) → st'.rem ≤ (rtStateToBnR0 st).rem →
      BigNumRtWf rt st' scr scrLimbs' →
      intRep res z objs' → (∀ o ∈ objs.map rtObjToBnR0, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ BigNumRt.lcnfHeap objs' ⋆ R) m' → Q (res, ()) m' := by
  intro res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm'
  rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
  exact hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
    ((intRepR0_iff res z objs').mpr hres)
    (fun o ho => bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep _ (List.mem_map_of_mem ho)))
    hm'

private theorem intConv2_body_aux {rt a : BitVec 64} {st : RtC0State} {scr : BitVec 64}
    {objs : List LcnfObj} {R : Mem 64 → Prop} {Q : Post [i64]}
    (z : Int)
    (hk : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
      intRepR0 res z objs' →
      (∀ o ∈ objs, o.addr ≠ a → ∃ o' ∈ objs', o'.addr = o.addr ∧ o'.tag = o.tag ∧
        o'.other = o.other ∧ o'.arrSize = o.arrSize ∧ o'.cap = o.cap ∧
        o'.limbs = o.limbs ∧ (o.Wf → o'.Wf)) →
      (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta (rtStateToBnR0 st) → st'.rem ≤ (rtStateToBnR0 st).rem →
      BigNumRtWf rt st' scr scrLimbs' →
      intRep res z objs' →
      (∀ o ∈ objs.map rtObjToBnR0, o.addr ≠ a →
        ∃ o' ∈ objs', o'.addr = o.addr ∧ o'.tag = o.tag ∧
          o'.other = o.other ∧ o'.arrSize = o.arrSize ∧ o'.cap = o.cap ∧
          o'.limbs = o.limbs ∧ (o.Wf → o'.Wf)) →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ BigNumRt.lcnfHeap objs' ⋆ R) m' → Q (res, ()) m' := by
  intro res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm'
  rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
  refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
    ((intRepR0_iff res z objs').mpr hres) ?_ hm'
  intro o ho hne
  obtain ⟨bo', hbo', hfields⟩ := hkeep _ (List.mem_map_of_mem ho) hne
  exact ⟨bnObjToRtR0 bo', List.mem_map_of_mem hbo', hfields⟩

theorem lcnfIntConvSpecR0_to_bn {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfIntConvSpecR0 xs m Q X) : lcnfIntConvSpec xs m Q X := by
  rcases xs with ⟨rt, op, a, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, R, hwf, hm, hbody⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, R, hwf, hm, ?_⟩
  by_cases h1 : op.toNat = 1
  · rw [ite_eq_left h1] at hbody ⊢
    rcases hbody with ⟨aVal, ha, hall, hk⟩
    exact ⟨aVal, (natRepR0_rt_iff a aVal objs).mp ha, hall, intConv1_body_aux (aVal : Int) hk⟩
  · rw [ite_eq_right h1] at hbody ⊢
    by_cases h13 : op.toNat = 13
    · rw [ite_eq_left h13] at hbody ⊢
      rcases hbody with ⟨hall, hk⟩
      refine ⟨hall, fun res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm' => ?_⟩
      rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
      have hres' : intRepR0 res a.toInt (objs'.map bnObjToRtR0) :=
        (intRepR0_iff res a.toInt objs').mpr hres
      exact hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf' hres'
        (fun o ho =>
          bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep _ (List.mem_map_of_mem ho)))
        hm'
    · rw [ite_eq_right h13] at hbody ⊢
      by_cases h16 : op.toNat = 16
      · rw [ite_eq_left h16] at hbody ⊢
        rcases hbody with ⟨z, hz, hk⟩
        refine ⟨z, (intRepR0_rt_iff a z objs).mp hz, fun m' hm' => ?_⟩
        rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq, bnStateToRtR0_rtStateToBnR0] at hm'
        have hcomp : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
        rw [List.map_map, hcomp, List.map_id] at hm'
        exact hk m' hm'
      · rw [ite_eq_right h16] at hbody ⊢
        by_cases h2 : op.toNat = 2
        · rw [ite_eq_left h2] at hbody ⊢
          rcases hbody with ⟨aVal, ha, hmax, hbig, hsm, hk⟩
          refine ⟨aVal, (natRepR0_rt_iff a aVal objs).mp ha, hmax, fun ha2 => ?_, hsm,
            intConv2_body_aux (Int.negSucc aVal) hk⟩
          obtain ⟨hs, hcap, hwfO, hclO, hrcO, hrem⟩ := hbig ha2
          refine ⟨hs, (rtStateToBnR0_workCap st).symm ▸ (by simpa using hcap),
            ?_, (rtHeapClosed_iff objs).mp hclO, ?_, hrem⟩
          · intro bo hbo
            obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hbo
            exact hwfO o ho
          · intro bo hbo had hrc1
            obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hbo
            exact (rtRcSound_iff a objs).mp (hrcO o ho had hrc1)
        · rw [ite_eq_right h2] at hbody ⊢
          by_cases h3 : op.toNat = 3
          · rw [ite_eq_left h3] at hbody ⊢
            rcases hbody with ⟨z, hz, hnz, hk⟩
            refine ⟨z, (intRepR0_rt_iff a z objs).mp hz, hnz,
              fun res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm' => ?_⟩
            rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
            refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
              ((intRepR0_iff res _ objs').mpr hres) ?_ hm'
            intro o ho
            exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep _ (List.mem_map_of_mem ho))
          · rw [ite_eq_right h3] at hbody ⊢
            by_cases h9 : op.toNat = 9
            · rw [ite_eq_left h9] at hbody ⊢
              rcases hbody with ⟨z, hz, hnz, hk⟩
              refine ⟨z, (intRepR0_rt_iff a z objs).mp hz, hnz,
                fun res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm' => ?_⟩
              rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
              refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem
                hwf' ((natRepR0_iff res _ objs').mpr hres) ?_ hm'
              intro o ho
              exact bnObjToRtR0_rtObjToBnR0 o ▸
                List.mem_map_of_mem (hkeep _ (List.mem_map_of_mem ho))
            · rw [ite_eq_right h9] at hbody
              exact False.elim hbody

theorem lcnfIntConvSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfIntConvSpecR0 xs m Q X) :
    rtR1Env "lcnf_int_conv" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_lcnf_int_conv (lcnfIntConvSpecR0_to_bn h)

theorem lcnfIntConvSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntConvSpecR0 xs m Q X) :
    rtC0CoreEnv "lcnf_int_conv" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (lcnfIntConvSpecR0_le_rtR1Env h)

theorem lcnfIntAddSubCmpSpecR0_to_bn {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntAddSubCmpSpecR0 xs m Q X) :
    lcnfIntAddSubCmpSpec xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hscr, hop, harith, hm, hk⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  have hcompR : bnObjToRtR0 ∘ rtObjToBnR0 = id := funext bnObjToRtR0_rtObjToBnR0
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, aVal, bVal, R, hwf,
    (intRepR0_rt_iff a aVal objs).mp ha, (intRepR0_rt_iff b bVal objs).mp hb,
    hscr, hop, harith, hm, fun res st' scrLimbs' objs' m' hpr hrem hwf' hpost hm' => ?_⟩
  rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
  refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf' ?_ hm'
  by_cases h4 : op.toNat = 4
  · rw [ite_eq_left h4] at hpost ⊢
    refine ⟨(intRepR0_iff res _ objs').mpr hpost.1, fun o ho => ?_⟩
    exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hpost.2 _ (List.mem_map_of_mem ho))
  · rw [ite_eq_right h4] at hpost ⊢
    by_cases h5 : op.toNat = 5
    · rw [ite_eq_left h5] at hpost ⊢
      refine ⟨(intRepR0_iff res _ objs').mpr hpost.1, fun o ho => ?_⟩
      exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hpost.2 _ (List.mem_map_of_mem ho))
    · rw [ite_eq_right h5] at hpost ⊢
      by_cases h10 : op.toNat = 10
      · rw [ite_eq_left h10] at hpost ⊢
        exact ⟨hpost.1, by have h1 := congrArg (List.map bnObjToRtR0) hpost.2
                           simpa [List.map_map, hcompR] using h1⟩
      · rw [ite_eq_right h10] at hpost ⊢
        by_cases h11 : op.toNat = 11
        · rw [ite_eq_left h11] at hpost ⊢
          exact ⟨hpost.1, by have h1 := congrArg (List.map bnObjToRtR0) hpost.2
                             simpa [List.map_map, hcompR] using h1⟩
        · rw [ite_eq_right h11] at hpost ⊢
          exact ⟨hpost.1, by have h1 := congrArg (List.map bnObjToRtR0) hpost.2
                             simpa [List.map_map, hcompR] using h1⟩

theorem lcnfIntAddSubCmpSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntAddSubCmpSpecR0 xs m Q X) :
    rtR1Env "lcnf_int_addsub_cmp" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_lcnf_int_addsub_cmp (lcnfIntAddSubCmpSpecR0_to_bn h)

theorem lcnfIntAddSubCmpSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntAddSubCmpSpecR0 xs m Q X) :
    rtC0CoreEnv "lcnf_int_addsub_cmp" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (lcnfIntAddSubCmpSpecR0_le_rtR1Env h)

theorem lcnfIntMulDivSpecR0_to_bn {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntMulDivSpecR0 xs m Q X) :
    lcnfIntMulDivSpec xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hop, hscr, hmax, hall,
    hm, hk⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, aVal, bVal, R, hwf,
    (intRepR0_rt_iff a aVal objs).mp ha, (intRepR0_rt_iff b bVal objs).mp hb,
    hop, hscr, hmax, hall, hm, fun res st' scrLimbs' objs' m' hpr hrem hwf' hres hkeep hm' => ?_⟩
  rw [bigNumRtInv_eq_fullRtInv, bnHeap_eq] at hm'
  refine hk res (bnStateToRtR0 st') scrLimbs' (objs'.map bnObjToRtR0) m' hpr hrem hwf'
    ((intRepR0_iff res _ objs').mpr hres) ?_ hm'
  intro o ho
  exact bnObjToRtR0_rtObjToBnR0 o ▸ List.mem_map_of_mem (hkeep _ (List.mem_map_of_mem ho))

theorem lcnfIntMulDivSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntMulDivSpecR0 xs m Q X) :
    rtR1Env "lcnf_int_muldiv" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_lcnf_int_muldiv (lcnfIntMulDivSpecR0_to_bn h)

theorem lcnfIntMulDivSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntMulDivSpecR0 xs m Q X) :
    rtC0CoreEnv "lcnf_int_muldiv" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (lcnfIntMulDivSpecR0_le_rtR1Env h)

theorem lcnfIntOpSpecR0_to_bn {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntOpSpecR0 xs m Q X) : lcnfIntOpSpec xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, R, hwf, hm, hbody⟩
  rw [fullRtInv_eq_bigNumRtInv, rtHeap_eq_bn] at hm
  refine ⟨rtStateToBnR0 st, scr, scrLimbs, objs.map rtObjToBnR0, R, hwf, hm, ?_⟩
  by_cases h1 : op.toNat ∈ [1, 2, 3, 9, 13, 16]
  · rw [ite_eq_left h1] at hbody ⊢
    exact lcnfIntConvSpecR0_to_bn hbody
  · rw [ite_eq_right h1] at hbody ⊢
    by_cases h2 : op.toNat ∈ [4, 5, 10, 11, 12]
    · rw [ite_eq_left h2] at hbody ⊢
      exact lcnfIntAddSubCmpSpecR0_to_bn hbody
    · rw [ite_eq_right h2] at hbody ⊢
      by_cases h3 : op.toNat ∈ [6, 7, 8, 14, 15]
      · rw [ite_eq_left h3] at hbody ⊢
        exact lcnfIntMulDivSpecR0_to_bn hbody
      · rw [ite_eq_right h3] at hbody
        exact False.elim hbody

theorem lcnfIntOpSpecR0_le_rtR1Env {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntOpSpecR0 xs m Q X) :
    rtR1Env "lcnf_int_op" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_lcnf_int_op (lcnfIntOpSpecR0_to_bn h)

theorem lcnfIntOpSpecR0_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntOpSpecR0 xs m Q X) :
    rtC0CoreEnv "lcnf_int_op" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (lcnfIntOpSpecR0_le_rtR1Env h)

/-! ## 3. Unified `Nat` Coercions (`natRepR0 ↔ NatInHeap`, `G-R2`) -/

private theorem ofNat64_box_and1_ne {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n + 1) &&& 1#64) ≠ 0#64 := by
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  have hand : (BitVec.ofNat 64 (2 * n + 1) &&& 1#64) = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, BitVec.toNat_ofNat, hmod]
    omega
  rw [hand]; decide

private theorem ofNat64_box_shr1 {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n + 1) >>> 1).toNat = n := by
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hmod, Nat.shiftRight_eq_div_pow,
    show (2 ^ 1 : Nat) = 2 by decide]
  omega

theorem natRepR0_to_natInHeap_small {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hs : n < 2 ^ 63) (hrep : natRepR0 w n objs) : NatInHeap w n objs := by
  have hw : w = BitVec.ofNat 64 (2 * n + 1) := by
    simpa [natRepR0, hs] using hrep
  subst hw
  rw [NatInHeap, ite_eq_left (ofNat64_box_and1_ne hs), ofNat64_box_shr1 hs]

theorem mpzNatCanonR0_to_mpzCanon {obj : LcnfObj} {n : Nat}
    (hc : mpzNatCanonR0 obj n) (hcs0 : obj.csSz = 0) :
    MpzCanon obj ∧ mpzLimbsVal (obj.limbs.take obj.arrSize) = n := by
  rcases hc with ⟨hwf, htag, hoth, harr, _, _, _, hval, _⟩
  rcases hwf with ⟨h0, h8, hrc, _, _, _, _, _, _, hkind⟩
  simp only [htag, show mpzTag = 250 from rfl, closureTag, arrayTag, sarrayTag, stringTag] at hkind
  rcases hkind with ⟨hlcap, hcap, _⟩
  have harrcap : obj.arrSize ≤ obj.cap := by omega
  refine ⟨⟨h0, h8, hrc, hcs0, hoth, htag, hlcap, harrcap, hcap⟩, ?_⟩
  rw [harr, List.take_length, mpzLimbsVal_eq_limbsVal, hval]

theorem natRepR0_to_natInHeap {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hrep : natRepR0 w n objs) (hcs0 : ∀ o ∈ objs, o.addr = w → o.csSz = 0) :
    NatInHeap w n objs := by
  by_cases hs : n < 2 ^ 63
  · exact natRepR0_to_natInHeap_small hs hrep
  · simp only [natRepR0, hs, ↓reduceIte] at hrep
    rcases hrep with ⟨hw0, obj, hmem, had, hc⟩
    have hnot : ¬ ((w &&& 1#64) ≠ 0#64) := fun h => h hw0
    rw [NatInHeap, ite_eq_right hnot]
    obtain ⟨hmc, hval⟩ := mpzNatCanonR0_to_mpzCanon hc (hcs0 obj hmem had)
    exact ⟨obj, hmem, had, hmc, hval.symm⟩

theorem natInHeap_to_natRepR0_small {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hodd : (w &&& 1#64) ≠ 0#64) (hnih : NatInHeap w n objs) : natRepR0 w n objs := by
  rw [NatInHeap, ite_eq_left hodd] at hnih
  have hsh : n = w.toNat / 2 := by
    rw [hnih, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (2 ^ 1 : Nat) = 2 by decide]
  have hlt : n < 2 ^ 63 := by
    have := w.isLt
    omega
  have hmod : w.toNat % 2 = 1 := by
    by_cases hm : w.toNat % 2 = 1
    · exact hm
    · exfalso
      apply hodd
      apply BitVec.eq_of_getElem_eq
      intro i hi
      cases i with
      | zero =>
        simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_and, BitVec.toNat_ofNat,
          Nat.testBit_zero]
        have hm0 : w.toNat % 2 = 0 := by omega
        simp [hm0]
      | succ k =>
        simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_and, BitVec.toNat_ofNat]
        rw [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
        have h1bit : (1 : Nat).testBit (k + 1) = false := by simp [Nat.testBit_succ]
        have h0bit : (0 : Nat).testBit (k + 1) = false := by simp
        simp [h1bit, h0bit]
  simp only [natRepR0, hlt, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem natInHeap_to_natRepR0 {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hnih : NatInHeap w n objs)
    (hcanon : (w &&& 1#64) = 0#64 →
      ∃ obj ∈ objs, obj.addr = w ∧ MpzCanon obj ∧
        obj.arrSize = obj.limbs.length ∧ 1 ≤ obj.limbs.length ∧
        obj.limbs.getLast! ≠ 0#64 ∧ mpzLimbsVal obj.limbs = n ∧ 2 ^ 63 ≤ n) :
    natRepR0 w n objs := by
  by_cases hodd : (w &&& 1#64) ≠ 0#64
  · exact natInHeap_to_natRepR0_small hodd hnih
  · have hw0 : (w &&& 1#64) = 0#64 := Decidable.not_not.mp hodd
    obtain ⟨obj, hmem, had, hmc, harr, hlen, hlast, hval, hge⟩ := hcanon hw0
    have hnot : ¬(n < 2 ^ 63) := Nat.not_lt.mpr hge
    simp only [natRepR0, hnot, ↓reduceIte]
    have hcapMax : obj.limbs.length ≤ mpzMaxLimbs := by
      have := hmc.2.2.2.2.2.2.1
      have := hmc.2.2.2.2.2.2.2.2
      unfold mpzMaxLimbs
      omega
    refine ⟨hw0, obj, hmem, had, hmc.wf, hmc.2.2.2.2.2.1, hmc.2.2.2.2.1,
      harr, hlen, hcapMax, hlast, ?_, hge⟩
    rw [← mpzLimbsVal_eq_limbsVal, hval]

end LeanQbe.T.LeanLCNF.Sem
