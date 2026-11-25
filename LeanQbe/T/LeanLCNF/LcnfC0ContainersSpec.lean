module

public import LeanQbe.T.LeanLCNF.LcnfC0Containers
public import LeanQbe.T.LeanLCNF.LcnfC0RtSpec

/-!
# Functional & Separation-Logic Specifications for `LcnfC0Containers` (R2 Part 1)

Defines canonical heap object constructors (`mkBaObj`, `mkArrObj`), validity predicates
(`BaCanon`, `ArrCanon`), multi-handle Perceus RC soundness (`HandlesRcSound`), pure byte-slice
comparison (`cmpByteSlices`, `baCmpOpSpec`), `Func.wp` specification contracts for all 22 C0
functions in `rtR2Mod` plus the 4 R0 externs, `Spec.Mono` proofs, and the closed `rtR2Env` table.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

/-! ## 1. Container Constants, Canonical Models, and RC Arithmetic -/

/-- Maximum `ByteArray` byte capacity fitting R0 `lcnf_alloc` (`align8 (24 + cap) ≤ 268435440`). -/
def baMaxCap : Nat := 268435416

/-- Maximum `Array` slot capacity fitting R0 `lcnf_alloc` (`24 + 8 * cap ≤ 268435448`). -/
def arrMaxCap : Nat := 33554428

/-- Exit panic code for capacity overflow / size errors (`lcnf_alloc` convention). -/
def panicCapCode : BitVec 64 := 2#64

/-- Exit panic code for unchecked/unboxed out-of-bounds access. -/
def panicOobCode : BitVec 64 := 7#64

/-- Total byte allocation size for a `ByteArray` (`tag 248`) of capacity `cap`. -/
def baAllocBytes (cap : Nat) : Nat := align8 (24 + cap)

/-- Total byte allocation size for an `Array` (`tag 246`) of capacity `cap`. -/
def arrAllocBytes (cap : Nat) : Nat := 24 + 8 * cap

/-- New capacity chosen by `r2_ensure_excl_ba(rt, ba, expand)`. -/
def baEnsureCap (sz cap : Nat) (expand : BitVec 64) : Nat :=
  if expand = 0#64 then cap
  else if sz < cap then cap
  else if cap = 0 then 8
  else min baMaxCap (cap * 2)

/-- New capacity chosen by `r2_ensure_excl_array(rt, a, expand)`. -/
def arrEnsureCap (sz cap : Nat) (expand : BitVec 64) : Nat :=
  if expand = 0#64 then cap
  else if sz < cap then cap
  else if cap = 0 then 4
  else min arrMaxCap (cap * 2)

/-- Packed 64-bit object header for fresh `ByteArray` (`rc=1, csSz=0, other=1, tag=248`). -/
def baHeaderWord : BitVec 64 := 0xf801000000000001#64

/-- Packed 64-bit object header for fresh `Array` (`rc=1, csSz=0, other=0, tag=246`). -/
def arrHeaderWord : BitVec 64 := 0xf600000000000001#64

/-- Construct a canonical `ByteArray` (`tag 248`, `m_other = 1`) `LcnfObj`. -/
def mkBaObj (addr : BitVec 64) (rc : BitVec 32) (cap : Nat) (data : List UInt8) : LcnfObj :=
  { addr := addr
    rc := rc
    csSz := 0
    other := 1
    tag := sarrayTag
    cap := cap
    arrSize := data.length
    scalarData := data }

/-- Construct a canonical `Array` (`tag 246`) `LcnfObj`. -/
def mkArrObj (addr : BitVec 64) (rc : BitVec 32) (cap : Nat) (elems : List (BitVec 64)) :
    LcnfObj :=
  { addr := addr
    rc := rc
    csSz := 0
    other := 0
    tag := arrayTag
    cap := cap
    fields := elems }

/-- Canonical `ByteArray` object invariant (`tag 248`, `other = 1`, length ≤ cap ≤ `baMaxCap`). -/
def BaCanon (o : LcnfObj) : Prop :=
  o.addr ≠ 0#64 ∧ o.addr.toNat % 8 = 0 ∧ 0 ≤ o.rc.toInt ∧
  o.csSz = 0 ∧ o.other = 1 ∧ o.tag = sarrayTag ∧
  o.arrSize = o.scalarData.length ∧ o.arrSize ≤ o.cap ∧ o.cap ≤ baMaxCap

/-- Canonical `Array` object invariant (`tag 246`, `fields.length ≤ cap ≤ arrMaxCap`). -/
def ArrCanon (o : LcnfObj) : Prop :=
  o.addr ≠ 0#64 ∧ o.addr.toNat % 8 = 0 ∧ 0 ≤ o.rc.toInt ∧
  o.csSz = 0 ∧ o.other = 0 ∧ o.tag = arrayTag ∧
  o.fields.length ≤ o.cap ∧ o.cap ≤ arrMaxCap

theorem BaCanon.wf {o : LcnfObj} (h : BaCanon o) : o.Wf := by
  rcases h with ⟨h0, h8, hrc, hcs, ho, ht, hlen, hsc, hcap⟩
  have hb : o.cap ≤ 268435416 := by unfold baMaxCap at hcap; exact hcap
  have htb : o.totalBytes = align8 (24 + o.cap) := by
    simp [LcnfObj.totalBytes, ht, ho, sarrayTag, arrayTag]
  refine ⟨h0, h8, hrc, by omega, by omega, by simp [ht, sarrayTag], ?_, ?_, ?_, ?_⟩
  · rw [htb]; unfold align8 rtMinObjBytes; omega
  · rw [htb]; unfold align8 rtMaxObjBytes; omega
  · rw [htb]; unfold align8; omega
  · simp [ht, sarrayTag, arrayTag, closureTag]
    have hars : o.arrSize < 18446744073709551616 := by omega
    rw [hlen] at hsc
    exact ⟨by omega, hars, by simp [ho, hsc]⟩

theorem ArrCanon.wf {o : LcnfObj} (h : ArrCanon o) : o.Wf := by
  rcases h with ⟨h0, h8, hrc, hcs, ho, ht, hfc, hcap⟩
  have ha : o.cap ≤ 33554428 := by unfold arrMaxCap at hcap; exact hcap
  have htb : o.totalBytes = 24 + 8 * o.cap := by
    simp [LcnfObj.totalBytes, ht, arrayTag]
  refine ⟨h0, h8, hrc, by omega, by omega, by simp [ht, arrayTag], ?_, ?_, ?_, ?_⟩
  · rw [htb]; unfold rtMinObjBytes; omega
  · rw [htb]; unfold rtMaxObjBytes; omega
  · rw [htb]; omega
  · simp [ht, arrayTag, closureTag]
    exact ⟨hfc, ha⟩

theorem mkBaObj_canon {p : BitVec 64} {rc : BitVec 32} {cap : Nat} {data : List UInt8}
    (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0) (hrc : 0 ≤ rc.toInt)
    (hlen : data.length ≤ cap) (hcap : cap ≤ baMaxCap) :
    BaCanon (mkBaObj p rc cap data) :=
  ⟨hp0, hp8, hrc, rfl, rfl, rfl, rfl, hlen, hcap⟩

theorem mkArrObj_canon {p : BitVec 64} {rc : BitVec 32} {cap : Nat} {elems : List (BitVec 64)}
    (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0) (hrc : 0 ≤ rc.toInt)
    (hlen : elems.length ≤ cap) (hcap : cap ≤ arrMaxCap) :
    ArrCanon (mkArrObj p rc cap elems) :=
  ⟨hp0, hp8, hrc, rfl, rfl, rfl, hlen, hcap⟩

/-- Header word of `mkBaObj p 1#32 cap data` equals `baHeaderWord`. -/
theorem mkBaObj_header (p : BitVec 64) (cap : Nat) (data : List UInt8) :
    (mkBaObj p 1#32 cap data).header = baHeaderWord := by
  apply BitVec.eq_of_getLsbD_eq
  simp only [LcnfObj.header, mkBaObj, sarrayTag, baHeaderWord,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  decide

/-- Header word of `mkArrObj p 1#32 cap elems` equals `arrHeaderWord`. -/
theorem mkArrObj_header (p : BitVec 64) (cap : Nat) (elems : List (BitVec 64)) :
    (mkArrObj p 1#32 cap elems).header = arrHeaderWord := by
  apply BitVec.eq_of_getLsbD_eq
  simp only [LcnfObj.header, mkArrObj, arrayTag, arrHeaderWord,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  decide

/-- Reference-count increment performed by `r2_inc_obj` (`0` and `≥ 2^31 - 1` stay unchanged). -/
def incRcVal (rc : BitVec 32) : BitVec 32 :=
  if 0 < rc.toInt ∧ rc.toInt < 2147483647 then rc + 1#32 else rc

/-- Reference-count decrement performed on non-exclusive objects (`1 < rc.toInt`). -/
def decNonExclRc (rc : BitVec 32) : BitVec 32 :=
  if 1 < rc.toInt then rc - 1#32 else rc

/-- Pure lexicographical comparison of two byte lists: `0#64` = lt, `1#64` = eq, `2#64` = gt. -/
def cmpByteSlices : List UInt8 → List UInt8 → BitVec 64
  | [], [] => 1#64
  | [], _ :: _ => 0#64
  | _ :: _, [] => 2#64
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then 0#64
    else if a.toNat > b.toNat then 2#64
    else cmpByteSlices as bs

/-- Pure mathematical result of `lcnf_ba_cmp_op(rt, op, a, b)`. -/
def baCmpOpVal (op a b : BitVec 64) (bsA bsB : List UInt8) : BitVec 64 :=
  if a = b then
    if op = 0#64 then 1#64 else if op = 1#64 then 0#64 else 1#64
  else if op = 0#64 then
    if bsA.length = bsB.length ∧ cmpByteSlices bsA bsB = 1#64 then 1#64 else 0#64
  else if op = 1#64 then
    if cmpByteSlices bsA bsB = 0#64 then 1#64 else 0#64
  else
    cmpByteSlices bsA bsB

/-- Pure mathematical result of `lcnf_ba_get(rt, ba, idx, unboxed)`. -/
def baGetVal (data : List UInt8) (idx unboxed : BitVec 64) : BitVec 64 :=
  let i :=
    if unboxed ≠ 0#64 then idx.toNat
    else if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
    else data.length
  if h : i < data.length then BitVec.ofNat 64 data[i].toNat else 0#64

/-- Static/caller-owned metadata preserved when `lcnf_ba_empty` lazily sets `s_ba_empty`. -/
def RtC0State.PreservesMetaExceptBaEmpty (st st' : RtC0State) : Prop :=
  st'.extraArgs = st.extraArgs ∧
  st'.globals = st.globals ∧
  st'.hdr.s_end = st.hdr.s_end ∧
  st'.hdr.s_work = st.hdr.s_work ∧
  st'.hdr.s_work_cap = st.hdr.s_work_cap ∧
  st'.hdr.s_chunks = st.hdr.s_chunks ∧
  st'.hdr.s_nchunks = st.hdr.s_nchunks ∧
  st'.hdr.s_chunks_cap = st.hdr.s_chunks_cap

theorem RtC0State.PreservesMeta.toExceptBaEmpty {st st' : RtC0State}
    (h : st'.PreservesMeta st) : st'.PreservesMetaExceptBaEmpty st :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem RtC0State.PreservesMeta.trans {st1 st2 st3 : RtC0State}
    (h12 : st2.PreservesMeta st1) (h23 : st3.PreservesMeta st2) :
    st3.PreservesMeta st1 := by
  rcases h12 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  rcases h23 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8, a9.trans b9⟩

theorem RtC0State.PreservesMeta.refl (st : RtC0State) : st.PreservesMeta st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Multi-Handle Perceus Soundness & Heap Transition Relations -/

/-- Multi-handle Perceus RC soundness for a heap object list `objs` and live caller handles:
1. Persistent objects (`m_rc = 0`) point only to persistent objects (`m_rc = 0`).
2. Every RC-managed object (`0 < y.rc.toInt`) has
   `nonPersistRefs objs y.addr + handles.count y.addr ≤ y.rc.toNat`. -/
def HandlesRcSound (handles : List (BitVec 64)) (objs : List LcnfObj) : Prop :=
  (∀ p ∈ objs, p.rc = 0#32 → ∀ f ∈ p.childFields, (f &&& 1#64) = 0#64 →
    ∃ q ∈ objs, q.addr = f ∧ q.rc = 0#32) ∧
  (∀ y ∈ objs, 0 < y.rc.toInt →
    nonPersistRefs objs y.addr + handles.count y.addr ≤ y.rc.toNat)

theorem handlesRcSound_singleton_iff (root : BitVec 64) (objs : List LcnfObj) :
    HandlesRcSound [root] objs ↔ RcSound root objs := by
  simp only [HandlesRcSound, RcSound]
  have hcnt : ∀ a : BitVec 64, [root].count a = if a = root then 1 else 0 := by
    intro a
    rw [List.count_cons, List.count_nil]
    by_cases h : root = a
    · have hb : (root == a) = true := beq_iff_eq.mpr h
      rw [ite_eq_left_of_eq_true _ _ (eq_true hb), ite_eq_left_of_eq_true _ _ (eq_true h.symm)]
    · have hb : (root == a) = false := beq_false_of_ne h
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [hb])),
        ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h))]
  simp only [hcnt]

/-- Relational post-state for `r2_dec_obj(rt, o)`. -/
def DecObjRel (o : BitVec 64) (objs objs' : List LcnfObj) : Prop :=
  if o = 0#64 ∨ (o &&& 1#64) ≠ 0#64 then
    objs' = objs
  else
    ∃ obj ∈ objs, obj.addr = o ∧
      if obj.rc = 1#32 then DecColdRel o objs objs'
      else objs' = objs.map fun y => if y.addr = o then y.withRc (decNonExclRc y.rc) else y

/-- Heap transform when copying elements of a shared/persistent `Array` (`rc ≠ 1#32`) into a new
exclusive copy: increments `rc` of each non-persistent child by its multiplicity in `fields`. -/
def incChildrenObjs (fields : List (BitVec 64)) (objs : List LcnfObj) : List LcnfObj :=
  objs.map fun y =>
    if 0 < y.rc.toInt then y.withRc (BitVec.ofNat 32 (y.rc.toNat + fields.count y.addr)) else y

/-- Heap transition performed by `r2_ensure_excl_array` on `(arrObj, childObjs)` where `arrObj`
is separated from `childObjs`. -/
def EnsureExclArrayOutcome (arrObj : LcnfObj) (expand : BitVec 64) (r : BitVec 64)
    (childObjs childObjs' : List LcnfObj) (rObj : LcnfObj) (oldKeep : Mem 64 → Prop) : Prop :=
  let newCap := arrEnsureCap arrObj.fields.length arrObj.cap expand
  rObj = mkArrObj r 1#32 newCap arrObj.fields ∧
  ArrCanon rObj ∧
  (expand ≠ 0#64 → arrObj.fields.length < newCap) ∧
  (arrObj.rc = 1#32 → (expand = 0#64 ∨ arrObj.fields.length < arrObj.cap) → r = arrObj.addr) ∧
  (arrObj.rc = 1#32 → childObjs' = childObjs ∧ oldKeep = emp) ∧
  (arrObj.rc ≠ 1#32 →
    childObjs' = incChildrenObjs arrObj.fields childObjs ∧
    oldKeep = lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc)))

/-- Heap transition after `lcnf_array_set` when in bounds (`i < sz`), replacing `arrObj` in `objs`
with `rObj` (element `i` set to `v`) and calling `r2_dec_obj` on `old = arrObj.fields[i]`. -/
def ArraySetInBoundsRel (arr i v : BitVec 64) (objs objs' : List LcnfObj) : Prop :=
  ∃ (arrObj : LcnfObj) (k : Nat) (_hk : k < objs.length) (r : BitVec 64) (rObj : LcnfObj)
      (mid1 mid2 : List LcnfObj) (hi : i.toNat < arrObj.fields.length),
    objs[k] = arrObj ∧ arrObj.addr = arr ∧ ArrCanon arrObj ∧
    r ≠ 0#64 ∧ r.toNat % 8 = 0 ∧
    rObj = mkArrObj r 1#32 arrObj.cap (arrObj.fields.set i.toNat v) ∧
    (arrObj.rc = 1#32 → r = arr ∧ mid1 = objs.eraseIdx k) ∧
    (arrObj.rc ≠ 1#32 →
      mid1 = (incChildrenObjs arrObj.fields (objs.eraseIdx k)).insertIdx k
        (arrObj.withRc (decNonExclRc arrObj.rc))) ∧
    mid2 = rObj :: mid1 ∧
    DecObjRel (arrObj.fields[i.toNat]'hi) mid2 objs'

/-- Heap transition after `lcnf_array_pop`, ensuring exclusive `r` and (when `sz > 0`) shrinking
`fields` via `dropLast` before calling `r2_dec_obj` on the popped last element. -/
def ArrayPopRel (arr : BitVec 64) (objs objs' : List LcnfObj) : Prop :=
  ∃ (arrObj : LcnfObj) (k : Nat) (hk : k < objs.length) (r : BitVec 64) (rObj : LcnfObj)
      (mid1 mid2 : List LcnfObj),
    objs[k] = arrObj ∧ arrObj.addr = arr ∧ ArrCanon arrObj ∧
    r ≠ 0#64 ∧ r.toNat % 8 = 0 ∧
    rObj = mkArrObj r 1#32 arrObj.cap arrObj.fields.dropLast ∧
    (arrObj.rc = 1#32 → r = arr ∧ mid1 = objs.eraseIdx k) ∧
    (arrObj.rc ≠ 1#32 →
      mid1 = (incChildrenObjs arrObj.fields (objs.eraseIdx k)).insertIdx k
        (arrObj.withRc (decNonExclRc arrObj.rc))) ∧
    mid2 = rObj :: mid1 ∧
    (if h : 0 < arrObj.fields.length then
      DecObjRel (arrObj.fields[arrObj.fields.length - 1]'(by omega)) mid2 objs'
    else objs' = mid2)

/-! ## 3. Function `Spec` Contracts (`rtR2SpecEntries`) -/

/-- `r2_inc_obj(o) -> ()`: increments non-zero, unsaturated `m_rc`; no-op on 0 or scalar. -/
def r2IncObjSpec : Spec [i64] [] := fun (o, ()) m Q _ =>
  if o = 0#64 ∨ (o &&& 1#64) ≠ 0#64 then
    Q () m
  else
    ∃ (obj : LcnfObj) (R : Mem 64 → Prop),
      obj.addr = o ∧ obj.Wf ∧ (lcnfObjMem obj ⋆ R) m ∧
      ∀ m', (lcnfObjMem (obj.withRc (incRcVal obj.rc)) ⋆ R) m' → Q () m'

/-- `r2_dec_obj(rt, o) -> ()`: decrements or cascades cold free on `o` (no-op on 0 or scalar). -/
def r2DecObjSpec : Spec [i64, i64] [] := fun (rt, o, ()) m Q _ =>
  if o = 0#64 ∨ (o &&& 1#64) ≠ 0#64 then
    Q () m
  else
    ∃ (st : RtC0State) (objs : List LcnfObj) (R : Mem 64 → Prop),
      (∃ obj ∈ objs, obj.addr = o ∧
        (obj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound o objs)) ∧
      (∀ obj ∈ objs, obj.Wf) ∧
      (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
      ∀ st' objs' m',
        st'.PreservesMeta st → st'.rem = st.rem →
        DecObjRel o objs objs' →
        (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q () m'

/-- `r2_mem_copy_bytes(dst, src, len) -> ()`: copies `len` bytes from `src` into uninit `dst`. -/
def r2MemCopyBytesSpec : Spec [i64, i64, i64] [] := fun (dst, src, len, ()) m Q _ =>
  ∃ (srcData : List UInt8) (remCap : Nat) (R : Mem 64 → Prop),
    srcData.length = len.toNat ∧ len.toNat ≤ remCap ∧ remCap ≤ 2 ^ 64 ∧
    (bytes src srcData ⋆ region dst remCap ⋆ R) m ∧
    ∀ m',
      (bytes src srcData ⋆ bytes dst srcData ⋆
        region (dst + len) (remCap - len.toNat) ⋆ R) m' →
      Q () m'

/-- `r2_cmp_byte_slices(ap, la, bp, lb) -> ord`: lexicographical compare (`0=lt, 1=eq, 2=gt`). -/
def r2CmpByteSlicesSpec : Spec [i64, i64, i64, i64] [i64] := fun (ap, la, bp, lb, ()) m Q _ =>
  ∃ (bsA bsB : List UInt8) (RA RB : Mem 64 → Prop),
    bsA.length = la.toNat ∧ bsB.length = lb.toNat ∧
    (bytes ap bsA ⋆ RA) m ∧ (bytes bp bsB ⋆ RB) m ∧
    Q (cmpByteSlices bsA bsB, ()) m

/-- `lcnf_oob(rt, dv) -> dv`: increments default value `dv` and returns it. -/
def lcnfOobSpec : Spec [i64, i64] [i64] := fun (_rt, dv, ()) m Q _ =>
  if dv = 0#64 ∨ (dv &&& 1#64) ≠ 0#64 then
    Q (dv, ()) m
  else
    ∃ (obj : LcnfObj) (R : Mem 64 → Prop),
      obj.addr = dv ∧ obj.Wf ∧ (lcnfObjMem obj ⋆ R) m ∧
      ∀ m', (lcnfObjMem (obj.withRc (incRcVal obj.rc)) ⋆ R) m' → Q (dv, ()) m'

/-- `r2_alloc_sarray(rt, size, cap) -> p`: allocates `ByteArray` header + uninit payload region,
or exits cleanly via `lcnf_panic(rt, 2)` when `size > cap ∨ cap > baMaxCap`. -/
def r2AllocSarraySpec : Spec [i64, i64, i64] [i64] := fun (rt, size, cap, ()) m Q X =>
  if size.toNat ≤ cap.toNat ∧ cap.toNat ≤ baMaxCap then
    ∃ (st : RtC0State) (R : Mem 64 → Prop),
      let bytes := baAllocBytes cap.toNat
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ R) m ∧
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (rtC0Inv rt st' ⋆ cell64 p baHeaderWord ⋆
          cell64 (p + 8#64) size ⋆ cell64 (p + 16#64) cap ⋆
          region (p + 24#64) (bytes - 24) ⋆ R) m' →
        Q (p, ()) m'
  else
    X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m

/-- `r2_ensure_excl_ba(rt, ba, expand) -> r`: COW exclusivity for `ByteArray` (`m_rc == 1` in-place
fast path vs fresh copy + free/dec old), with clean `lcnf_panic(rt, 2)` on max-cap overflow. -/
def r2EnsureExclBaSpec : Spec [i64, i64, i64] [i64] := fun (rt, ba, expand, ()) m Q X =>
  ∃ (st : RtC0State) (baObj : LcnfObj) (R : Mem 64 → Prop),
    baObj.addr = ba ∧ BaCanon baObj ∧
    (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m ∧
    if expand ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let newCap := baEnsureCap baObj.arrSize baObj.cap expand
      let needAlloc := baObj.rc ≠ 1#32 ∨ (expand ≠ 0#64 ∧ baObj.arrSize ≥ baObj.cap)
      let reqBytes := baAllocBytes newCap
      (needAlloc → st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
      ∀ r st' m',
        r ≠ 0#64 → r.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (baObj.rc = 1#32 → (expand = 0#64 ∨ baObj.arrSize < baObj.cap) → r = ba ∧ st' = st) →
        (expand ≠ 0#64 → baObj.arrSize < newCap) →
        newCap ≤ baMaxCap →
        let rObj := mkBaObj r 1#32 newCap baObj.scalarData
        let oldKeep :=
          if baObj.rc = 1#32 then emp
          else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))
        (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ R) m' →
        Q (r, ()) m'

/-- `lcnf_ba_empty(rt) -> p`: returns cached persistent empty `ByteArray` (`s.ba_empty`),
lazily allocating and marking persistent on first call. -/
def lcnfBaEmptySpec : Spec [i64] [i64] := fun (rt, ()) m Q _ =>
  ∃ (st : RtC0State) (R : Mem 64 → Prop),
    (rtC0Inv rt st ⋆ R) m ∧
    if st.hdr.s_ba_empty ≠ 0#64 then
      Q (st.hdr.s_ba_empty, ()) m
    else
      1 ≤ st.workCap ∧ (st.hasFree 24 ∨ 24 ≤ st.rem) ∧
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        st'.PreservesMetaExceptBaEmpty st → st'.rem ≤ st.rem →
        st'.hdr.s_ba_empty = p →
        let emptyObj := mkBaObj p 0#32 0 []
        (rtC0Inv rt st' ⋆ lcnfObjMem emptyObj ⋆ R) m' →
        Q (p, ()) m'

/-- `lcnf_ba_mk_empty(rt, cap) -> p`: allocates empty `ByteArray` with unboxed capacity `cap`. -/
def lcnfBaMkEmptySpec : Spec [i64, i64] [i64] := fun (rt, cap, ()) m Q X =>
  let c := if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0
  if c ≤ baMaxCap then
    ∃ (st : RtC0State) (R : Mem 64 → Prop),
      (st.hasFree (baAllocBytes c) ∨ baAllocBytes c ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ R) m ∧
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        let baObj := mkBaObj p 1#32 c []
        BaCanon baObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m' →
        Q (p, ()) m'
  else
    X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m

/-- `lcnf_ba_mk(rt, arr) -> ba`: converts owned `Array UInt8` into `ByteArray` and decs `arr`. -/
def lcnfBaMkSpec : Spec [i64, i64] [i64] := fun (rt, arr, ()) m Q _ =>
  ∃ (st : RtC0State) (arrObj : LcnfObj) (objs : List LcnfObj) (R : Mem 64 → Prop),
    arrObj ∈ objs ∧ arrObj.addr = arr ∧ ArrCanon arrObj ∧
    (∀ f ∈ arrObj.fields, (f &&& 1#64) = 1#64) ∧
    (∀ o ∈ objs, o.Wf) ∧
    (arrObj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound arr objs) ∧
    (st.hasFree (baAllocBytes arrObj.fields.length) ∨
      baAllocBytes arrObj.fields.length ≤ st.rem) ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ ba st' objs' m',
      ba ≠ 0#64 → ba.toNat % 8 = 0 →
      st'.PreservesMeta st → st'.rem ≤ st.rem →
      let data := arrObj.fields.map fun elem => UInt8.ofNat (elem >>> 1#64).toNat
      let baObj := mkBaObj ba 1#32 arrObj.fields.length data
      BaCanon baObj → DecObjRel arr objs objs' →
      (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (ba, ()) m'

/-- `lcnf_ba_get(rt, ba, idx, unboxed) -> b`: bounds-checked byte load (`0` if OOB). -/
def lcnfBaGetSpec : Spec [i64, i64, i64, i64] [i64] := fun (_rt, ba, idx, unboxed, ()) m Q _ =>
  ∃ (baObj : LcnfObj) (R : Mem 64 → Prop),
    baObj.addr = ba ∧ BaCanon baObj ∧
    (lcnfObjMem baObj ⋆ R) m ∧
    Q (baGetVal baObj.scalarData idx unboxed, ()) m

/-- `lcnf_ba_set(rt, ba, idx, b, unboxed) -> r`: COW byte update (in-place when `rc = 1`). -/
def lcnfBaSetSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (rt, ba, idx, b, unboxed, ()) m Q _ =>
    ∃ (st : RtC0State) (baObj : LcnfObj) (R : Mem 64 → Prop),
      baObj.addr = ba ∧ BaCanon baObj ∧
      (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m ∧
      let iNat :=
        if unboxed ≠ 0#64 then idx.toNat
        else if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
        else baObj.arrSize
      if iNat ≥ baObj.arrSize then
        Q (ba, ()) m
      else
        (baObj.rc ≠ 1#32 →
          st.hasFree (baAllocBytes baObj.cap) ∨ baAllocBytes baObj.cap ≤ st.rem) ∧
        ∀ r st' m',
          r ≠ 0#64 → r.toNat % 8 = 0 →
          st'.PreservesMeta st → st'.rem ≤ st.rem →
          (baObj.rc = 1#32 → r = ba ∧ st' = st) →
          let rObj := mkBaObj r 1#32 baObj.cap (baObj.scalarData.set iNat (UInt8.ofNat b.toNat))
          let oldKeep :=
            if baObj.rc = 1#32 then emp
            else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))
          BaCanon rObj →
          (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ R) m' →
          Q (r, ()) m'

/-- `lcnf_ba_push(rt, ba, b) -> r`: COW append byte (grows cap cleanly, panics on overflow). -/
def lcnfBaPushSpec : Spec [i64, i64, i64] [i64] := fun (rt, ba, b, ()) m Q X =>
  ∃ (st : RtC0State) (baObj : LcnfObj) (R : Mem 64 → Prop),
    baObj.addr = ba ∧ BaCanon baObj ∧
    (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m ∧
    if baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let newCap := baEnsureCap baObj.arrSize baObj.cap 1#64
      let needAlloc := baObj.rc ≠ 1#32 ∨ baObj.arrSize ≥ baObj.cap
      let reqBytes := baAllocBytes newCap
      (needAlloc → st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
      ∀ r st' m',
        r ≠ 0#64 → r.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (baObj.rc = 1#32 → baObj.arrSize < baObj.cap → r = ba ∧ st' = st) →
        let rObj := mkBaObj r 1#32 newCap (baObj.scalarData ++ [UInt8.ofNat b.toNat])
        let oldKeep :=
          if baObj.rc = 1#32 then emp
          else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))
        BaCanon rObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ R) m' →
        Q (r, ()) m'

/-- `lcnf_ba_cmp_op(rt, op, a, b) -> res`: byte-array equality / `<` / `Ordering` compare. -/
def lcnfBaCmpOpSpec : Spec [i64, i64, i64, i64] [i64] := fun (_rt, op, a, b, ()) m Q _ =>
  ∃ (aObj bObj : LcnfObj) (RA RB : Mem 64 → Prop),
    aObj.addr = a ∧ bObj.addr = b ∧ BaCanon aObj ∧ BaCanon bObj ∧
    (lcnfObjMem aObj ⋆ RA) m ∧ (lcnfObjMem bObj ⋆ RB) m ∧
    Q (baCmpOpVal op a b aObj.scalarData bObj.scalarData, ()) m

/-- `r2_alloc_array(rt, size, cap) -> p`: allocates `Array` header + uninit `8 * cap` payload,
or exits cleanly via `lcnf_panic(rt, 2)` when `size > cap ∨ cap > arrMaxCap`. -/
def r2AllocArraySpec : Spec [i64, i64, i64] [i64] := fun (rt, size, cap, ()) m Q X =>
  if size.toNat ≤ cap.toNat ∧ cap.toNat ≤ arrMaxCap then
    ∃ (st : RtC0State) (R : Mem 64 → Prop),
      let bytes := arrAllocBytes cap.toNat
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ R) m ∧
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (rtC0Inv rt st' ⋆ cell64 p arrHeaderWord ⋆
          cell64 (p + 8#64) size ⋆ cell64 (p + 16#64) cap ⋆
          region (p + 24#64) (8 * cap.toNat) ⋆ R) m' →
        Q (p, ()) m'
  else
    X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m

/-- `r2_ensure_excl_array(rt, a, expand) -> r`: COW exclusivity for `Array` (`m_rc == 1` in-place
fast path, `m_rc == 1` expand + shallow `lcnf_free_obj`, shared/persistent copy + `r2_inc_obj`). -/
def r2EnsureExclArraySpec : Spec [i64, i64, i64] [i64] := fun (rt, a, expand, ()) m Q X =>
  ∃ (st : RtC0State) (arrObj : LcnfObj) (childObjs : List LcnfObj) (R : Mem 64 → Prop),
    arrObj.addr = a ∧ ArrCanon arrObj ∧ (∀ y ∈ childObjs, y.Wf) ∧
    (rtC0Inv rt st ⋆ lcnfObjMem arrObj ⋆ lcnfHeap childObjs ⋆ R) m ∧
    (arrObj.rc ≠ 1#32 →
      (∀ f ∈ arrObj.fields, (f &&& 1#64) = 0#64 → ∃ y ∈ childObjs, y.addr = f) ∧
      (∀ y ∈ childObjs, 0 < y.rc.toInt →
        y.rc.toInt + (arrObj.fields.count y.addr : Int) < 2147483648)) ∧
    if expand ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let newCap := arrEnsureCap arrObj.fields.length arrObj.cap expand
      let needAlloc := arrObj.rc ≠ 1#32 ∨ (expand ≠ 0#64 ∧ arrObj.fields.length ≥ arrObj.cap)
      let reqBytes := arrAllocBytes newCap
      (needAlloc → st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
      ∀ r st' childObjs' m',
        r ≠ 0#64 → r.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (arrObj.rc = 1#32 → (expand = 0#64 ∨ arrObj.fields.length < arrObj.cap) → st' = st) →
        let rObj := mkArrObj r 1#32 newCap arrObj.fields
        let oldKeep :=
          if arrObj.rc = 1#32 then emp
          else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))
        EnsureExclArrayOutcome arrObj expand r childObjs childObjs' rObj oldKeep →
        (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R) m' →
        Q (r, ()) m'

/-- `lcnf_array_mk_empty(rt, cap) -> p`: allocates empty `Array` with capacity `cap`. -/
def lcnfArrayMkEmptySpec : Spec [i64, i64] [i64] := fun (rt, cap, ()) m Q X =>
  let c := if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0
  if c ≤ arrMaxCap then
    ∃ (st : RtC0State) (R : Mem 64 → Prop),
      (st.hasFree (arrAllocBytes c) ∨ arrAllocBytes c ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ R) m ∧
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        let arrObj := mkArrObj p 1#32 c []
        ArrCanon arrObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem arrObj ⋆ R) m' →
        Q (p, ()) m'
  else
    X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m

/-- `lcnf_array_get(rt, dv, arr, idx, flags) -> v`: reads element (or `dv` on boxed OOB), with
optional `r2_inc_obj` (`borrowed` = bit 0) and clean `lcnf_panic(rt, 7)` on unboxed OOB. -/
def lcnfArrayGetSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (rt, dv, arr, idx, flags, ()) m Q X =>
    let borrowed := (flags &&& 1#64) ≠ 0#64
    let unboxed := (flags &&& 2#64) ≠ 0#64
    ∃ (arrObj : LcnfObj) (objs : List LcnfObj) (R : Mem 64 → Prop),
      arrObj ∈ objs ∧ arrObj.addr = arr ∧ ArrCanon arrObj ∧ (∀ o ∈ objs, o.Wf) ∧
      (lcnfHeap objs ⋆ R) m ∧
      if unboxed ∧ arrObj.fields.length ≤ idx.toNat then
        X "lcnf_panic" [i64, i64] (rt, panicOobCode, ()) m
      else
        let ret :=
          if unboxed then
            if h : idx.toNat < arrObj.fields.length then arrObj.fields[idx.toNat] else dv
          else if (idx &&& 1#64) ≠ 0#64 then
            if h : (idx >>> 1).toNat < arrObj.fields.length then
              arrObj.fields[(idx >>> 1).toNat]
            else dv
          else dv
        ((¬borrowed ∧ ret ≠ 0#64 ∧ (ret &&& 1#64) = 0#64) → ∃ o ∈ objs, o.addr = ret) ∧
        ∀ m',
          let objs' :=
            if borrowed ∨ ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64 then objs
            else objs.map fun o => if o.addr = ret then o.withRc (incRcVal o.rc) else o
          (borrowed → m' = m) →
          (lcnfHeap objs' ⋆ R) m' →
          Q (ret, ()) m'

/-- `lcnf_array_set(rt, arr, idx, v, unboxed) -> r`: COW element replace; on OOB decs `v` and
returns `arr` unchanged; in bounds writes `v` before dec'ing old element. -/
def lcnfArraySetSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (rt, arr, idx, v, unboxed, ()) m Q _ =>
    ∃ (st : RtC0State) (objs : List LcnfObj) (k : Nat) (hk : k < objs.length) (R : Mem 64 → Prop),
      let arrObj := objs[k]'hk
      arrObj.addr = arr ∧ ArrCanon arrObj ∧ arrObj.addr ∉ arrObj.fields ∧
      (∀ o ∈ objs, o.Wf) ∧ lcnfHeapClosed objs ∧
      (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
      let iNat :=
        if unboxed ≠ 0#64 then idx.toNat
        else if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
        else arrObj.fields.length
      if hlt : iNat < arrObj.fields.length then
        let old := arrObj.fields[iNat]'hlt
        (arrObj.rc ≠ 1#32 →
          (st.hasFree (arrAllocBytes arrObj.cap) ∨ arrAllocBytes arrObj.cap ≤ st.rem) ∧
          (∀ y ∈ objs.eraseIdx k, 0 < y.rc.toInt →
            y.rc.toInt + (arrObj.fields.count y.addr : Int) < 2147483648)) ∧
        (arrObj.rc = 1#32 → old ≠ 0#64 → (old &&& 1#64) = 0#64 →
          let mid2 :=
            mkArrObj arr 1#32 arrObj.cap (arrObj.fields.set iNat v) :: objs.eraseIdx k
          ∀ o2 ∈ mid2, o2.addr = old → o2.rc = 1#32 →
            mid2.length ≤ st.workCap ∧ lcnfHeapClosed mid2 ∧ RcSound old mid2) ∧
        (old ≠ 0#64 → (old &&& 1#64) = 0#64 → (v &&& 1#64) = 0#64 → ∃ vo ∈ objs, vo.addr = v) ∧
        ∀ r st' objs' m',
          r ≠ 0#64 → r.toNat % 8 = 0 →
          st'.PreservesMeta st → st'.rem ≤ st.rem →
          (arrObj.rc = 1#32 → r = arr) →
          ∀ (rObj : LcnfObj) (mid1 mid2 : List LcnfObj),
            rObj = mkArrObj r 1#32 arrObj.cap (arrObj.fields.set iNat v) →
            (arrObj.rc = 1#32 → mid1 = objs.eraseIdx k) →
            (arrObj.rc ≠ 1#32 →
              mid1 = (incChildrenObjs arrObj.fields (objs.eraseIdx k)).insertIdx k
                (arrObj.withRc (decNonExclRc arrObj.rc))) →
            mid2 = rObj :: mid1 →
            DecObjRel old mid2 objs' →
            (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' →
            Q (r, ()) m'
      else
        ((v ≠ 0#64 ∧ (v &&& 1#64) = 0#64) →
          ∃ vo ∈ objs, vo.addr = v ∧ (vo.rc = 1#32 → objs.length ≤ st.workCap ∧ RcSound v objs)) ∧
        ∀ st' objs' m',
          st'.PreservesMeta st → st'.rem = st.rem →
          DecObjRel v objs objs' →
          (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' →
          Q (arr, ()) m'

/-- `lcnf_array_push(rt, arr, v) -> r`: COW element append with doubling capacity growth. -/
def lcnfArrayPushSpec : Spec [i64, i64, i64] [i64] := fun (rt, arr, v, ()) m Q X =>
  ∃ (st : RtC0State) (arrObj : LcnfObj) (childObjs : List LcnfObj) (R : Mem 64 → Prop),
    arrObj.addr = arr ∧ ArrCanon arrObj ∧ (∀ y ∈ childObjs, y.Wf) ∧
    (rtC0Inv rt st ⋆ lcnfObjMem arrObj ⋆ lcnfHeap childObjs ⋆ R) m ∧
    (arrObj.rc ≠ 1#32 →
      (∀ f ∈ arrObj.fields, (f &&& 1#64) = 0#64 → ∃ y ∈ childObjs, y.addr = f) ∧
      (∀ y ∈ childObjs, 0 < y.rc.toInt →
        y.rc.toInt + (arrObj.fields.count y.addr : Int) < 2147483648)) ∧
    if arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap then
      X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
    else
      let newCap := arrEnsureCap arrObj.fields.length arrObj.cap 1#64
      let needAlloc := arrObj.rc ≠ 1#32 ∨ arrObj.fields.length ≥ arrObj.cap
      let reqBytes := arrAllocBytes newCap
      (needAlloc → st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
      ∀ r st' childObjs' m',
        r ≠ 0#64 → r.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (arrObj.rc = 1#32 → arrObj.fields.length < arrObj.cap → r = arr ∧ st' = st) →
        let rObj := mkArrObj r 1#32 newCap (arrObj.fields ++ [v])
        let oldKeep :=
          if arrObj.rc = 1#32 then emp
          else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))
        ArrCanon rObj →
        (arrObj.rc = 1#32 → childObjs' = childObjs) →
        (arrObj.rc ≠ 1#32 → childObjs' = incChildrenObjs arrObj.fields childObjs) →
        (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R) m' →
        Q (r, ()) m'

/-- `lcnf_array_pop(rt, arr) -> r`: COW pop of last element (dec'ing removed element if non-empty).
-/
def lcnfArrayPopSpec : Spec [i64, i64] [i64] := fun (rt, arr, ()) m Q _ =>
  ∃ (st : RtC0State) (objs : List LcnfObj) (k : Nat) (hk : k < objs.length) (R : Mem 64 → Prop),
    let arrObj := objs[k]'hk
    arrObj.addr = arr ∧ ArrCanon arrObj ∧ arrObj.addr ∉ arrObj.fields ∧
    (∀ o ∈ objs, o.Wf) ∧ lcnfHeapClosed objs ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    (arrObj.rc ≠ 1#32 →
      (st.hasFree (arrAllocBytes arrObj.cap) ∨ arrAllocBytes arrObj.cap ≤ st.rem) ∧
      (∀ y ∈ objs.eraseIdx k, 0 < y.rc.toInt →
        y.rc.toInt + (arrObj.fields.count y.addr : Int) < 2147483648)) ∧
    (∀ hpos : 0 < arrObj.fields.length,
      let old := arrObj.fields[arrObj.fields.length - 1]
      arrObj.rc = 1#32 → old ≠ 0#64 → (old &&& 1#64) = 0#64 →
        let mid2 := mkArrObj arr 1#32 arrObj.cap arrObj.fields.dropLast :: objs.eraseIdx k
        ∀ o2 ∈ mid2, o2.addr = old → o2.rc = 1#32 →
          mid2.length ≤ st.workCap ∧ lcnfHeapClosed mid2 ∧ RcSound old mid2) ∧
    ∀ r st' objs' m',
      r ≠ 0#64 → r.toNat % 8 = 0 →
      st'.PreservesMeta st → st'.rem ≤ st.rem →
      (arrObj.rc = 1#32 → r = arr) →
      ∀ (rObj : LcnfObj) (mid1 mid2 : List LcnfObj),
        rObj = mkArrObj r 1#32 arrObj.cap arrObj.fields.dropLast →
        (arrObj.rc = 1#32 → mid1 = objs.eraseIdx k) →
        (arrObj.rc ≠ 1#32 →
          mid1 = (incChildrenObjs arrObj.fields (objs.eraseIdx k)).insertIdx k
            (arrObj.withRc (decNonExclRc arrObj.rc))) →
        mid2 = rObj :: mid1 →
        (if h : 0 < arrObj.fields.length then
          DecObjRel (arrObj.fields[arrObj.fields.length - 1]) mid2 objs'
        else objs' = mid2) →
        (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' →
        Q (r, ()) m'

/-- `lcnf_array_swap(rt, arr, i, j, check_bounds) -> r`: COW slot swap; returns `arr` unchanged on
checked OOB, or exits cleanly via `lcnf_panic(rt, 7)` on unchecked OOB / non-scalar index. -/
def lcnfArraySwapSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (rt, arr, i, j, check_bounds, ()) m Q X =>
    ∃ (st : RtC0State) (arrObj : LcnfObj) (childObjs : List LcnfObj) (R : Mem 64 → Prop),
      arrObj.addr = arr ∧ ArrCanon arrObj ∧ (∀ y ∈ childObjs, y.Wf) ∧
      (rtC0Inv rt st ⋆ lcnfObjMem arrObj ⋆ lcnfHeap childObjs ⋆ R) m ∧
      let ui := (i >>> 1).toNat
      let uj := (j >>> 1).toNat
      if hi : (i &&& 1#64) ≠ 0#64 ∧ (j &&& 1#64) ≠ 0#64 ∧
          ui < arrObj.fields.length ∧ uj < arrObj.fields.length then
        (arrObj.rc ≠ 1#32 →
          (st.hasFree (arrAllocBytes arrObj.cap) ∨ arrAllocBytes arrObj.cap ≤ st.rem) ∧
          (∀ f ∈ arrObj.fields, (f &&& 1#64) = 0#64 → ∃ y ∈ childObjs, y.addr = f) ∧
          (∀ y ∈ childObjs, 0 < y.rc.toInt →
            y.rc.toInt + (arrObj.fields.count y.addr : Int) < 2147483648)) ∧
        ∀ r st' childObjs' m',
          r ≠ 0#64 → r.toNat % 8 = 0 →
          st'.PreservesMeta st → st'.rem ≤ st.rem →
          (arrObj.rc = 1#32 → r = arr ∧ st' = st) →
          let vi := arrObj.fields[ui]'hi.2.2.1
          let vj := arrObj.fields[uj]'hi.2.2.2
          let swapped := (arrObj.fields.set ui vj).set uj vi
          let rObj := mkArrObj r 1#32 arrObj.cap swapped
          let oldKeep :=
            if arrObj.rc = 1#32 then emp
            else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))
          ArrCanon rObj →
          (arrObj.rc = 1#32 → childObjs' = childObjs) →
          (arrObj.rc ≠ 1#32 → childObjs' = incChildrenObjs arrObj.fields childObjs) →
          (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R) m' →
          Q (r, ()) m'
      else if check_bounds ≠ 0#64 then
        Q (arr, ()) m
      else
        X "lcnf_panic" [i64, i64] (rt, panicOobCode, ()) m

/-! ## 4. Monotonicity (`Spec.Mono`) & Closed Environment Table (`rtR2Env`) -/

theorem r2IncObjSpec_mono : r2IncObjSpec.Mono := by
  rintro ⟨o, ⟨⟩⟩ m Q Q' X X' hQ _ h
  dsimp only [r2IncObjSpec] at h ⊢
  split at h <;> split
  · exact hQ _ m h
  · contradiction
  · contradiction
  · rcases h with ⟨obj, R, h0, hwf, hm, hk⟩
    exact ⟨obj, R, h0, hwf, hm, fun m' hm' => hQ _ m' (hk m' hm')⟩

theorem r2DecObjSpec_mono : r2DecObjSpec.Mono := by
  rintro ⟨rt, o, ⟨⟩⟩ m Q Q' X X' hQ _ h
  dsimp only [r2DecObjSpec] at h ⊢
  split at h <;> split
  · exact hQ _ m h
  · contradiction
  · contradiction
  · rcases h with ⟨st, objs, R, ho, hwf, hm, hk⟩
    exact ⟨st, objs, R, ho, hwf, hm, fun st' objs' m' hp hr hd hm' =>
      hQ _ m' (hk st' objs' m' hp hr hd hm')⟩

theorem r2MemCopyBytesSpec_mono : r2MemCopyBytesSpec.Mono := by
  rintro ⟨dst, src, len, ⟨⟩⟩ m Q Q' X X' hQ _ ⟨sd, rc, R, h1, h2, h3, hm, hk⟩
  exact ⟨sd, rc, R, h1, h2, h3, hm, fun m' hm' => hQ _ m' (hk m' hm')⟩

theorem r2CmpByteSlicesSpec_mono : r2CmpByteSlicesSpec.Mono := by
  rintro ⟨ap, la, bp, lb, ⟨⟩⟩ m Q Q' X X' hQ _ ⟨bsA, bsB, RA, RB, h1, h2, hm1, hm2, hq⟩
  exact ⟨bsA, bsB, RA, RB, h1, h2, hm1, hm2, hQ _ m hq⟩

theorem lcnfOobSpec_mono : lcnfOobSpec.Mono := by
  rintro ⟨rt, dv, ⟨⟩⟩ m Q Q' X X' hQ _ h
  dsimp only [lcnfOobSpec] at h ⊢
  split at h <;> split
  · exact hQ _ m h
  · contradiction
  · contradiction
  · rcases h with ⟨obj, R, h0, hwf, hm, hk⟩
    exact ⟨obj, R, h0, hwf, hm, fun m' hm' => hQ _ m' (hk m' hm')⟩

theorem r2AllocSarraySpec_mono : r2AllocSarraySpec.Mono := by
  rintro ⟨rt, sz, cap, ⟨⟩⟩ m Q Q' X X' hQ hX h
  dsimp only [r2AllocSarraySpec] at h ⊢
  by_cases hc : sz.toNat ≤ cap.toNat ∧ cap.toNat ≤ baMaxCap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h ⊢
    rcases h with ⟨st, R, hfr, hm, hk⟩
    exact ⟨st, R, hfr, hm, fun p st' m' hp1 hp2 hpr hr hm' =>
      hQ _ m' (hk p st' m' hp1 hp2 hpr hr hm')⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h ⊢
    exact hX _ _ _ m h

theorem r2EnsureExclBaSpec_mono : r2EnsureExclBaSpec.Mono := by
  rintro ⟨rt, ba, exp, ⟨⟩⟩ m Q Q' X X' hQ hX ⟨st, baObj, R, ha, hc, hm, h⟩
  refine ⟨st, baObj, R, ha, hc, hm, ?_⟩
  dsimp only at h ⊢
  by_cases hp : exp ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h ⊢
    exact hX _ _ _ m h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h ⊢
    rcases h with ⟨hfr, hk⟩
    exact ⟨hfr, fun r st' m' hr1 hr2 hpr hrem hfp hlt hcap hm' =>
      hQ _ m' (hk r st' m' hr1 hr2 hpr hrem hfp hlt hcap hm')⟩

theorem lcnfBaEmptySpec_mono : lcnfBaEmptySpec.Mono := by
  rintro ⟨rt, ⟨⟩⟩ m Q Q' X X' hQ _ ⟨st, R, hm, h⟩
  refine ⟨st, R, hm, ?_⟩
  dsimp only at h ⊢
  by_cases he : st.hdr.s_ba_empty ≠ 0#64
  · rw [ite_eq_left_of_eq_true _ _ (eq_true he)] at h ⊢
    exact hQ _ m h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false he)] at h ⊢
    rcases h with ⟨hw, hfr, hk⟩
    exact ⟨hw, hfr, fun p st' m' hp1 hp2 hpr hrem hba hm' =>
      hQ _ m' (hk p st' m' hp1 hp2 hpr hrem hba hm')⟩

theorem lcnfBaMkEmptySpec_mono : lcnfBaMkEmptySpec.Mono := by
  rintro ⟨rt, cap, ⟨⟩⟩ m Q Q' X X' hQ hX h
  dsimp only [lcnfBaMkEmptySpec] at h ⊢
  by_cases hc : (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) ≤ baMaxCap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h ⊢
    rcases h with ⟨st, R, hfr, hm, hk⟩
    exact ⟨st, R, hfr, hm, fun p st' m' hp1 hp2 hpr hr hcan hm' =>
      hQ _ m' (hk p st' m' hp1 hp2 hpr hr hcan hm')⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h ⊢
    exact hX _ _ _ m h

theorem lcnfBaMkSpec_mono : lcnfBaMkSpec.Mono := by
  rintro ⟨rt, arr, ⟨⟩⟩ m Q Q' X X' hQ _
    ⟨st, arrObj, objs, R, hmem, ha, hc, hsc, hwf, hrc, hfr, hm, hk⟩
  exact ⟨st, arrObj, objs, R, hmem, ha, hc, hsc, hwf, hrc, hfr, hm,
    fun ba st' objs' m' h1 h2 hpr hr hbc hdec hm' =>
      hQ _ m' (hk ba st' objs' m' h1 h2 hpr hr hbc hdec hm')⟩

theorem lcnfBaGetSpec_mono : lcnfBaGetSpec.Mono := by
  rintro ⟨rt, ba, idx, unb, ⟨⟩⟩ m Q Q' X X' hQ _ ⟨baObj, R, ha, hc, hm, hq⟩
  exact ⟨baObj, R, ha, hc, hm, hQ _ m hq⟩

theorem lcnfBaSetSpec_mono : lcnfBaSetSpec.Mono := by
  rintro ⟨rt, ba, idx, b, unb, ⟨⟩⟩ m Q Q' X X' hQ _ ⟨st, baObj, R, ha, hc, hm, h⟩
  refine ⟨st, baObj, R, ha, hc, hm, ?_⟩
  dsimp only at h ⊢
  by_cases hi :
      (if unb ≠ 0#64 then idx.toNat
        else if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat else baObj.arrSize) ≥ baObj.arrSize
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hi)] at h ⊢
    exact hQ _ m h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hi)] at h ⊢
    rcases h with ⟨hfr, hk⟩
    exact ⟨hfr, fun r st' m' h1 h2 hpr hr hfp hcan hm' =>
      hQ _ m' (hk r st' m' h1 h2 hpr hr hfp hcan hm')⟩

theorem lcnfBaPushSpec_mono : lcnfBaPushSpec.Mono := by
  rintro ⟨rt, ba, b, ⟨⟩⟩ m Q Q' X X' hQ hX ⟨st, baObj, R, ha, hc, hm, h⟩
  refine ⟨st, baObj, R, ha, hc, hm, ?_⟩
  dsimp only at h ⊢
  by_cases hp : baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h ⊢
    exact hX _ _ _ m h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h ⊢
    rcases h with ⟨hfr, hk⟩
    exact ⟨hfr, fun r st' m' h1 h2 hpr hr hfp hcan hm' =>
      hQ _ m' (hk r st' m' h1 h2 hpr hr hfp hcan hm')⟩

theorem lcnfBaCmpOpSpec_mono : lcnfBaCmpOpSpec.Mono := by
  rintro ⟨rt, op, a, b, ⟨⟩⟩ m Q Q' X X' hQ _ ⟨aO, bO, RA, RB, ha, hb, hca, hcb, hma, hmb, hq⟩
  exact ⟨aO, bO, RA, RB, ha, hb, hca, hcb, hma, hmb, hQ _ m hq⟩

theorem r2AllocArraySpec_mono : r2AllocArraySpec.Mono := by
  rintro ⟨rt, sz, cap, ⟨⟩⟩ m Q Q' X X' hQ hX h
  dsimp only [r2AllocArraySpec] at h ⊢
  by_cases hc : sz.toNat ≤ cap.toNat ∧ cap.toNat ≤ arrMaxCap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h ⊢
    rcases h with ⟨st, R, hfr, hm, hk⟩
    exact ⟨st, R, hfr, hm, fun p st' m' hp1 hp2 hpr hr hm' =>
      hQ _ m' (hk p st' m' hp1 hp2 hpr hr hm')⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h ⊢
    exact hX _ _ _ m h

theorem r2EnsureExclArraySpec_mono : r2EnsureExclArraySpec.Mono := by
  rintro ⟨rt, a, exp, ⟨⟩⟩ m Q Q' X X' hQ hX ⟨st, arrObj, ch, R, ha, hc, hwf, hm, hch, h⟩
  refine ⟨st, arrObj, ch, R, ha, hc, hwf, hm, hch, ?_⟩
  dsimp only at h ⊢
  by_cases hp : exp ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h ⊢
    exact hX _ _ _ m h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h ⊢
    rcases h with ⟨hfr, hk⟩
    exact ⟨hfr, fun r st' ch' m' h1 h2 hpr hr hfp hout hm' =>
      hQ _ m' (hk r st' ch' m' h1 h2 hpr hr hfp hout hm')⟩

theorem lcnfArrayMkEmptySpec_mono : lcnfArrayMkEmptySpec.Mono := by
  rintro ⟨rt, cap, ⟨⟩⟩ m Q Q' X X' hQ hX h
  dsimp only [lcnfArrayMkEmptySpec] at h ⊢
  by_cases hc : (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) ≤ arrMaxCap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h ⊢
    rcases h with ⟨st, R, hfr, hm, hk⟩
    exact ⟨st, R, hfr, hm, fun p st' m' hp1 hp2 hpr hr hcan hm' =>
      hQ _ m' (hk p st' m' hp1 hp2 hpr hr hcan hm')⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h ⊢
    exact hX _ _ _ m h

theorem lcnfArrayGetSpec_mono : lcnfArrayGetSpec.Mono := by
  rintro ⟨rt, dv, arr, idx, fl, ⟨⟩⟩ m Q Q' X X' hQ hX ⟨arrObj, objs, R, hmem, ha, hc, hwf, hm, h⟩
  refine ⟨arrObj, objs, R, hmem, ha, hc, hwf, hm, ?_⟩
  dsimp only at h ⊢
  by_cases hp : (fl &&& 2#64) ≠ 0#64 ∧ arrObj.fields.length ≤ idx.toNat
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h ⊢
    exact hX _ _ _ m h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h ⊢
    rcases h with ⟨hret, hk⟩
    exact ⟨hret, fun m' heq hm' => hQ _ m' (hk m' heq hm')⟩

theorem lcnfArraySetSpec_mono : lcnfArraySetSpec.Mono := by
  rintro ⟨rt, arr, idx, v, unb, ⟨⟩⟩ m Q Q' X X' hQ _
    ⟨st, objs, k, hklen, R, ha, hc, hns, hwf, hcl, hm, h⟩
  refine ⟨st, objs, k, hklen, R, ha, hc, hns, hwf, hcl, hm, ?_⟩
  dsimp only at h ⊢
  by_cases hi :
      (if unb ≠ 0#64 then idx.toNat
        else if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
        else (objs[k]'hklen).fields.length) < (objs[k]'hklen).fields.length
  · rw [dite_eq_left_of_eq_true (eq_true hi)] at h ⊢
    rcases h with ⟨hrcn, hrc1, hvo, hk⟩
    exact ⟨hrcn, hrc1, hvo, fun r st' objs' m' h1 h2 hpr hr hfp rO m1 m2 hrO hm1a hm1b hm2 hd hm' =>
      hQ _ m' (hk r st' objs' m' h1 h2 hpr hr hfp rO m1 m2 hrO hm1a hm1b hm2 hd hm')⟩
  · rw [dite_eq_right_of_eq_false (eq_false hi)] at h ⊢
    rcases h with ⟨hv, hk⟩
    exact ⟨hv, fun st' objs' m' hpr hr hd hm' => hQ _ m' (hk st' objs' m' hpr hr hd hm')⟩

theorem lcnfArrayPushSpec_mono : lcnfArrayPushSpec.Mono := by
  rintro ⟨rt, arr, v, ⟨⟩⟩ m Q Q' X X' hQ hX ⟨st, arrObj, ch, R, ha, hc, hwf, hm, hch, h⟩
  refine ⟨st, arrObj, ch, R, ha, hc, hwf, hm, hch, ?_⟩
  dsimp only at h ⊢
  by_cases hp : arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h ⊢
    exact hX _ _ _ m h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h ⊢
    rcases h with ⟨hfr, hk⟩
    exact ⟨hfr, fun r st' ch' m' h1 h2 hpr hr hfp hcan hc1 hc2 hm' =>
      hQ _ m' (hk r st' ch' m' h1 h2 hpr hr hfp hcan hc1 hc2 hm')⟩

theorem lcnfArrayPopSpec_mono : lcnfArrayPopSpec.Mono := by
  rintro ⟨rt, arr, ⟨⟩⟩ m Q Q' X X' hQ _
    ⟨st, objs, k, hklen, R, ha, hc, hns, hwf, hcl, hm, hrcn, hrc1, hk⟩
  exact ⟨st, objs, k, hklen, R, ha, hc, hns, hwf, hcl, hm, hrcn, hrc1,
    fun r st' objs' m' h1 h2 hpr hr hfp rO m1 m2 hrO hm1a hm1b hm2 hd hm' =>
      hQ _ m' (hk r st' objs' m' h1 h2 hpr hr hfp rO m1 m2 hrO hm1a hm1b hm2 hd hm')⟩

theorem lcnfArraySwapSpec_mono : lcnfArraySwapSpec.Mono := by
  rintro ⟨rt, arr, i, j, chk, ⟨⟩⟩ m Q Q' X X' hQ hX ⟨st, arrObj, ch, R, ha, hc, hwf, hm, h⟩
  refine ⟨st, arrObj, ch, R, ha, hc, hwf, hm, ?_⟩
  dsimp only at h ⊢
  by_cases hi : (i &&& 1#64) ≠ 0#64 ∧ (j &&& 1#64) ≠ 0#64 ∧
      (i >>> 1).toNat < arrObj.fields.length ∧ (j >>> 1).toNat < arrObj.fields.length
  · rw [dite_eq_left_of_eq_true (eq_true hi)] at h ⊢
    rcases h with ⟨hrcn, hk⟩
    exact ⟨hrcn, fun r st' ch' m' h1 h2 hpr hr hfp hcan hc1 hc2 hm' =>
      hQ _ m' (hk r st' ch' m' h1 h2 hpr hr hfp hcan hc1 hc2 hm')⟩
  · rw [dite_eq_right_of_eq_false (eq_false hi)] at h ⊢
    by_cases hc : chk ≠ 0#64
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h ⊢
      exact hQ _ m h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h ⊢
      exact hX _ _ _ m h

/-- Combined specification table for `rtR2Mod` (22 defined functions + 4 R0 externs). -/
def rtR2SpecEntries : List SpecEntry :=
  [ ⟨"r2_inc_obj", [i64], [], r2IncObjSpec, false⟩
  , ⟨"r2_dec_obj", [i64, i64], [], r2DecObjSpec, false⟩
  , ⟨"r2_mem_copy_bytes", [i64, i64, i64], [], r2MemCopyBytesSpec, false⟩
  , ⟨"r2_cmp_byte_slices", [i64, i64, i64, i64], [i64], r2CmpByteSlicesSpec, false⟩
  , ⟨"lcnf_oob", [i64, i64], [i64], lcnfOobSpec, false⟩
  , ⟨"r2_alloc_sarray", [i64, i64, i64], [i64], r2AllocSarraySpec, false⟩
  , ⟨"r2_ensure_excl_ba", [i64, i64, i64], [i64], r2EnsureExclBaSpec, false⟩
  , ⟨"lcnf_ba_empty", [i64], [i64], lcnfBaEmptySpec, false⟩
  , ⟨"lcnf_ba_mk_empty", [i64, i64], [i64], lcnfBaMkEmptySpec, false⟩
  , ⟨"lcnf_ba_mk", [i64, i64], [i64], lcnfBaMkSpec, false⟩
  , ⟨"lcnf_ba_get", [i64, i64, i64, i64], [i64], lcnfBaGetSpec, false⟩
  , ⟨"lcnf_ba_set", [i64, i64, i64, i64, i64], [i64], lcnfBaSetSpec, false⟩
  , ⟨"lcnf_ba_push", [i64, i64, i64], [i64], lcnfBaPushSpec, false⟩
  , ⟨"lcnf_ba_cmp_op", [i64, i64, i64, i64], [i64], lcnfBaCmpOpSpec, false⟩
  , ⟨"r2_alloc_array", [i64, i64, i64], [i64], r2AllocArraySpec, false⟩
  , ⟨"r2_ensure_excl_array", [i64, i64, i64], [i64], r2EnsureExclArraySpec, false⟩
  , ⟨"lcnf_array_mk_empty", [i64, i64], [i64], lcnfArrayMkEmptySpec, false⟩
  , ⟨"lcnf_array_get", [i64, i64, i64, i64, i64], [i64], lcnfArrayGetSpec, false⟩
  , ⟨"lcnf_array_set", [i64, i64, i64, i64, i64], [i64], lcnfArraySetSpec, false⟩
  , ⟨"lcnf_array_push", [i64, i64, i64], [i64], lcnfArrayPushSpec, false⟩
  , ⟨"lcnf_array_pop", [i64, i64], [i64], lcnfArrayPopSpec, false⟩
  , ⟨"lcnf_array_swap", [i64, i64, i64, i64, i64], [i64], lcnfArraySwapSpec, false⟩
  , ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocSpec, false⟩
  , ⟨"lcnf_free_obj", [i64, i64], [], lcnfFreeObjSpec, false⟩
  , ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩
  , ⟨"lcnf_mark_persistent", [i64, i64], [], lcnfMarkPersistentSpec, false⟩ ]

theorem rtR2SpecEntries_names_nodup : (rtR2SpecEntries.map SpecEntry.name).Nodup := by
  simp only [rtR2SpecEntries, List.map]
  decide

/-- Closed specification environment for `rtR2Mod`. -/
def rtR2Env : Env := Env.ofTable rtR2SpecEntries

private theorem env_lookup_at (i : Nat) (hi : i < rtR2SpecEntries.length)
    (hno : rtR2SpecEntries[i].noExit = false)
    {xs : Tup Val rtR2SpecEntries[i].as} {m : Mem 64}
    {Q : Post rtR2SpecEntries[i].rs} {X : XPost}
    (h : rtR2SpecEntries[i].spec xs m Q X) :
    rtR2Env rtR2SpecEntries[i].name rtR2SpecEntries[i].as rtR2SpecEntries[i].rs xs m Q X := by
  refine Env.ofTable_of_mem (List.getElem_mem hi) rtR2SpecEntries_names_nodup ?_
  simpa [SpecEntry.eff, hno] using h

theorem rtR2Env_r2_inc_obj {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : r2IncObjSpec xs m Q X) : rtR2Env "r2_inc_obj" [i64] [] xs m Q X :=
  env_lookup_at 0 (by decide) rfl h

theorem rtR2Env_r2_dec_obj {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : r2DecObjSpec xs m Q X) : rtR2Env "r2_dec_obj" [i64, i64] [] xs m Q X :=
  env_lookup_at 1 (by decide) rfl h

theorem rtR2Env_r2_mem_copy_bytes {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : r2MemCopyBytesSpec xs m Q X) :
    rtR2Env "r2_mem_copy_bytes" [i64, i64, i64] [] xs m Q X :=
  env_lookup_at 2 (by decide) rfl h

theorem rtR2Env_r2_cmp_byte_slices {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : r2CmpByteSlicesSpec xs m Q X) :
    rtR2Env "r2_cmp_byte_slices" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 3 (by decide) rfl h

theorem rtR2Env_lcnf_oob {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lcnfOobSpec xs m Q X) : rtR2Env "lcnf_oob" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 4 (by decide) rfl h

theorem rtR2Env_r2_alloc_sarray {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : r2AllocSarraySpec xs m Q X) :
    rtR2Env "r2_alloc_sarray" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 5 (by decide) rfl h

theorem rtR2Env_r2_ensure_excl_ba {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : r2EnsureExclBaSpec xs m Q X) :
    rtR2Env "r2_ensure_excl_ba" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 6 (by decide) rfl h

theorem rtR2Env_lcnf_ba_empty {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lcnfBaEmptySpec xs m Q X) : rtR2Env "lcnf_ba_empty" [i64] [i64] xs m Q X :=
  env_lookup_at 7 (by decide) rfl h

theorem rtR2Env_lcnf_ba_mk_empty {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfBaMkEmptySpec xs m Q X) :
    rtR2Env "lcnf_ba_mk_empty" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 8 (by decide) rfl h

theorem rtR2Env_lcnf_ba_mk {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lcnfBaMkSpec xs m Q X) : rtR2Env "lcnf_ba_mk" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 9 (by decide) rfl h

theorem rtR2Env_lcnf_ba_get {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfBaGetSpec xs m Q X) :
    rtR2Env "lcnf_ba_get" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 10 (by decide) rfl h

theorem rtR2Env_lcnf_ba_set {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfBaSetSpec xs m Q X) :
    rtR2Env "lcnf_ba_set" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 11 (by decide) rfl h

theorem rtR2Env_lcnf_ba_push {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfBaPushSpec xs m Q X) :
    rtR2Env "lcnf_ba_push" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 12 (by decide) rfl h

theorem rtR2Env_lcnf_ba_cmp_op {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfBaCmpOpSpec xs m Q X) :
    rtR2Env "lcnf_ba_cmp_op" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 13 (by decide) rfl h

theorem rtR2Env_r2_alloc_array {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : r2AllocArraySpec xs m Q X) :
    rtR2Env "r2_alloc_array" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 14 (by decide) rfl h

theorem rtR2Env_r2_ensure_excl_array {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : r2EnsureExclArraySpec xs m Q X) :
    rtR2Env "r2_ensure_excl_array" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 15 (by decide) rfl h

theorem rtR2Env_lcnf_array_mk_empty {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfArrayMkEmptySpec xs m Q X) :
    rtR2Env "lcnf_array_mk_empty" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 16 (by decide) rfl h

theorem rtR2Env_lcnf_array_get {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfArrayGetSpec xs m Q X) :
    rtR2Env "lcnf_array_get" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 17 (by decide) rfl h

theorem rtR2Env_lcnf_array_set {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfArraySetSpec xs m Q X) :
    rtR2Env "lcnf_array_set" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 18 (by decide) rfl h

theorem rtR2Env_lcnf_array_push {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfArrayPushSpec xs m Q X) :
    rtR2Env "lcnf_array_push" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 19 (by decide) rfl h

theorem rtR2Env_lcnf_array_pop {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfArrayPopSpec xs m Q X) :
    rtR2Env "lcnf_array_pop" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 20 (by decide) rfl h

theorem rtR2Env_lcnf_array_swap {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfArraySwapSpec xs m Q X) :
    rtR2Env "lcnf_array_swap" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 21 (by decide) rfl h

theorem rtR2Env_lcnf_alloc {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lcnfAllocSpec xs m Q X) : rtR2Env "lcnf_alloc" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 22 (by decide) rfl h

theorem rtR2Env_lcnf_free_obj {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : lcnfFreeObjSpec xs m Q X) : rtR2Env "lcnf_free_obj" [i64, i64] [] xs m Q X :=
  env_lookup_at 23 (by decide) rfl h

theorem rtR2Env_lcnf_dec_ref_cold {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : lcnfDecRefColdSpec xs m Q X) :
    rtR2Env "lcnf_dec_ref_cold" [i64, i64] [] xs m Q X :=
  env_lookup_at 24 (by decide) rfl h

theorem rtR2Env_lcnf_mark_persistent {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : lcnfMarkPersistentSpec xs m Q X) :
    rtR2Env "lcnf_mark_persistent" [i64, i64] [] xs m Q X :=
  env_lookup_at 25 (by decide) rfl h

end LeanQbe.T.LeanLCNF
