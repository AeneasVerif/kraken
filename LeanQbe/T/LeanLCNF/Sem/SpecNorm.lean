module

public import LeanQbe.T.LeanLCNF.LcnfC0FullProof
public import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumSpec
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.Logic.MemLemmas

/-!
# Runtime Spec Normalization (`G-R1` & `G-R2`) for `LeanLCNF` Tier-H Semantics

Bridges the two runtime object/state universes (`BigNumRt` from R1 vs `LeanLCNF` from R0/R2/R2b)
and unifies the two `Nat` heap predicates (`natRep` vs `NatInHeap`) so Tier-H semantics (`Sem/H`)
works over a single `LeanLCNF.RtC0State` / `LeanLCNF.LcnfObj` universe:

1. **Public `@[expose]`d bijections (`G-R1`)**:
   `bnHdrToRtR0`/`rtHdrToBnR0`, `bnStateToRtR0`/`rtStateToBnR0`, `bnObjToRtR0`/`rtObjToBnR0`,
   together with the unified runtime slab invariant `fullRtInv` and well-formedness `BigNumRtWfR0`.
2. **Unified `Nat` & `Int` predicates (`G-R2`)**:
   `mpzNatCanonR0`, `natRepR0`, `mpzIntCanonR0`, `intRepR0`, `DecNatRelR0`, `canAllocBytesR0`,
   `natPowOkR0`, `natGcdOkR0`, `natArithOkR0`, `natArithPostR0`, `natBitsOkR0`, `natBitsPostR0`
   over `LeanLCNF.LcnfObj` and `LeanLCNF.RtC0State`.
3. **Normalized R1 `Spec`s over R0 universe (`G-R1`)**:
   `lcnfNatAllocSpecR0`, `bnDecNatSpecR0`, `bnNatPowSpecR0`, `bnNatGcdSpecR0`,
   `lcnfNatArithSpecR0`, `lcnfNatBitsSpecR0`, `lcnfNatSlowSpecR0`, `lcnfIntConvSpecR0`,
   `lcnfIntAddSubCmpSpecR0`, `lcnfIntMulDivSpecR0`, `lcnfIntOpSpecR0`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open Std.ExtHashMap

/-! ## 1. Public `BigNumRt ↔ R0` Bijections & Unified Runtime Invariant (`G-R1`) -/

/-- Convert R1's `LcnfC0BaseRt` header to R0's `LcnfC0Rt` header (`33536..33671`). -/
@[expose] def bnHdrToRtR0 (h : LcnfC0BaseRt) : LcnfC0Rt :=
  { s_large_free := h.s_large_free
    s_ba_empty := h.s_ba_empty
    s_cur := h.s_cur
    s_end := h.s_end
    s_work := h.s_work
    s_work_cap := h.s_work_cap
    s_chunks := h.s_chunks
    s_nchunks := h.s_nchunks
    s_chunks_cap := h.s_chunks_cap
    s_st_allocs := h.s_st_allocs
    s_st_frees := h.s_st_frees
    s_st_live := h.s_st_live
    s_st_peak_live := h.s_st_peak_live
    s_st_persistent := h.s_st_persistent
    s_st_reused := h.s_st_reused
    s_st_cold_decs := h.s_st_cold_decs
    s_st_bytes := h.s_st_bytes }

/-- Convert R0's `LcnfC0Rt` header to R1's `LcnfC0BaseRt` header. -/
@[expose] def rtHdrToBnR0 (h : LcnfC0Rt) : LcnfC0BaseRt :=
  { s_large_free := h.s_large_free
    s_ba_empty := h.s_ba_empty
    s_cur := h.s_cur
    s_end := h.s_end
    s_work := h.s_work
    s_work_cap := h.s_work_cap
    s_chunks := h.s_chunks
    s_nchunks := h.s_nchunks
    s_chunks_cap := h.s_chunks_cap
    s_st_allocs := h.s_st_allocs
    s_st_frees := h.s_st_frees
    s_st_live := h.s_st_live
    s_st_peak_live := h.s_st_peak_live
    s_st_persistent := h.s_st_persistent
    s_st_reused := h.s_st_reused
    s_st_cold_decs := h.s_st_cold_decs
    s_st_bytes := h.s_st_bytes }

/-- Convert `BigNumRt.RtC0State` to R0's `RtC0State`. -/
@[expose] def bnStateToRtR0 (st : BigNumRt.RtC0State) : RtC0State :=
  { extraArgs := st.extraArgs
    globals := st.globals
    freeList := st.freeList
    hdr := bnHdrToRtR0 st.hdr
    workBuf := st.workBuf
    smallPools := st.smallPools
    largeNodes := st.largeNodes
    extraLen := st.extraLen
    globalsLen := st.globalsLen
    freeListLen := st.freeListLen
    workLen := st.workLen
    curLeEnd := st.curLeEnd
    arenaAlign := st.arenaAlign
    curNz := st.curNz }

/-- Convert R0's `RtC0State` to `BigNumRt.RtC0State`. -/
@[expose] def rtStateToBnR0 (st : RtC0State) : BigNumRt.RtC0State :=
  { extraArgs := st.extraArgs
    globals := st.globals
    freeList := st.freeList
    hdr := rtHdrToBnR0 st.hdr
    workBuf := st.workBuf
    smallPools := st.smallPools
    largeNodes := st.largeNodes
    extraLen := st.extraLen
    globalsLen := st.globalsLen
    freeListLen := st.freeListLen
    workLen := st.workLen
    curLeEnd := st.curLeEnd
    arenaAlign := st.arenaAlign
    curNz := st.curNz }

/-- Convert `BigNumRt.LcnfObj` to R0's `LcnfObj`. -/
@[expose] def bnObjToRtR0 (o : BigNumRt.LcnfObj) : LcnfObj :=
  { addr := o.addr
    rc := o.rc
    csSz := o.csSz
    other := o.other
    tag := o.tag
    funId := o.funId
    arity := o.arity
    cap := o.cap
    arrSize := o.arrSize
    strLen := o.strLen
    fields := o.fields
    scalarData := o.scalarData
    limbs := o.limbs }

/-- Convert R0's `LcnfObj` to `BigNumRt.LcnfObj`. -/
@[expose] def rtObjToBnR0 (o : LcnfObj) : BigNumRt.LcnfObj :=
  { addr := o.addr
    rc := o.rc
    csSz := o.csSz
    other := o.other
    tag := o.tag
    funId := o.funId
    arity := o.arity
    cap := o.cap
    arrSize := o.arrSize
    strLen := o.strLen
    fields := o.fields
    scalarData := o.scalarData
    limbs := o.limbs }

theorem bnHdrToRtR0_rtHdrToBnR0 (h : LcnfC0Rt) : bnHdrToRtR0 (rtHdrToBnR0 h) = h := by
  cases h; rfl

theorem rtHdrToBnR0_bnHdrToRtR0 (h : LcnfC0BaseRt) : rtHdrToBnR0 (bnHdrToRtR0 h) = h := by
  cases h; rfl

theorem bnStateToRtR0_rtStateToBnR0 (st : RtC0State) : bnStateToRtR0 (rtStateToBnR0 st) = st := by
  cases st; rfl

theorem rtStateToBnR0_bnStateToRtR0 (st : BigNumRt.RtC0State) :
    rtStateToBnR0 (bnStateToRtR0 st) = st := by
  cases st; rfl

theorem bnObjToRtR0_rtObjToBnR0 (o : LcnfObj) : bnObjToRtR0 (rtObjToBnR0 o) = o := by
  cases o; rfl

theorem rtObjToBnR0_bnObjToRtR0 (o : BigNumRt.LcnfObj) : rtObjToBnR0 (bnObjToRtR0 o) = o := by
  cases o; rfl

theorem bnStateToRtR0_rem (st : BigNumRt.RtC0State) : (bnStateToRtR0 st).rem = st.rem := rfl

theorem rtStateToBnR0_rem (st : RtC0State) : (rtStateToBnR0 st).rem = st.rem := rfl

theorem bnStateToRtR0_workCap (st : BigNumRt.RtC0State) :
    (bnStateToRtR0 st).workCap = st.workCap := rfl

theorem rtStateToBnR0_workCap (st : RtC0State) :
    (rtStateToBnR0 st).workCap = st.workCap := rfl

/-- Exposed unified `Mem 64` runtime slab invariant: R0 slab (`0..33671`) plus R1 trailing
`scratch` / `scratch_cap` fields (`33672..33687`) and scratch limb array. -/
@[expose] def fullRtInv (rt : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) : Mem 64 → Prop :=
  rtC0Inv rt st ⋆
  cell64 (rt + 33672#64) scr ⋆
  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
  array64 scr scrLimbs

/-- Well-formedness of the unified `LcnfC0FullRt` slab and scratch buffer over R0's `RtC0State`. -/
@[expose] def BigNumRtWfR0 (rt : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) : Prop :=
  st.Bounded48 ∧
  rt.toNat + LcnfC0BigNumRt.sizeof < 2 ^ 64 ∧
  scr ≠ 0#64 ∧
  scr.toNat % 8 = 0 ∧
  scrLimbs.length < 2 ^ 64 ∧
  scr.toNat + 8 * scrLimbs.length < 2 ^ 64

theorem bigNumRtWfR0_iff (rt : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) :
    BigNumRtWfR0 rt st scr scrLimbs ↔ BigNumRtWf rt (rtStateToBnR0 st) scr scrLimbs :=
  Iff.rfl

/-! ## 2. Unified `Nat` / `Int` Representation over `LeanLCNF.LcnfObj` (`G-R2`) -/

/-- Canonical boxed MPZ `Nat` invariant over R0's `LcnfObj`. -/
@[expose] def mpzNatCanonR0 (obj : LcnfObj) (n : Nat) : Prop :=
  obj.Wf ∧
  obj.tag = mpzTag ∧
  obj.other = 0 ∧
  obj.arrSize = obj.limbs.length ∧
  1 ≤ obj.limbs.length ∧
  obj.limbs.length ≤ mpzMaxLimbs ∧
  obj.limbs.getLast! ≠ 0#64 ∧
  limbsVal obj.limbs = n ∧
  2 ^ 63 ≤ n

/-- Unified representation predicate for Lean runtime `Nat` values (`(2*n + 1)` scalar or boxed
canonical MPZ in R0 `LcnfObj` heap). -/
@[expose] def natRepR0 (w : BitVec 64) (n : Nat) (objs : List LcnfObj) : Prop :=
  if n < 2 ^ 63 then w = BitVec.ofNat 64 (2 * n + 1)
  else (w &&& 1#64) = 0#64 ∧ ∃ obj ∈ objs, obj.addr = w ∧ mpzNatCanonR0 obj n

/-- Canonical boxed MPZ `Int` invariant over R0's `LcnfObj`. -/
@[expose] def mpzIntCanonR0 (obj : LcnfObj) (z : Int) : Prop :=
  obj.Wf ∧
  obj.tag = mpzTag ∧
  (obj.other = 0 ∨ obj.other = 1) ∧
  obj.arrSize = obj.limbs.length ∧
  1 ≤ obj.limbs.length ∧
  obj.limbs.length ≤ mpzMaxLimbs ∧
  obj.limbs.getLast! ≠ 0#64 ∧
  limbsVal obj.limbs = z.natAbs ∧
  (obj.other = 1 ↔ z < 0) ∧
  (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z)

/-- Unified representation predicate for Lean runtime `Int` values (`[-2^62, 2^62)` scalar or boxed
canonical MPZ in R0 `LcnfObj` heap). -/
@[expose] def intRepR0 (w : BitVec 64) (z : Int) (objs : List LcnfObj) : Prop :=
  if -(2 ^ 62 : Int) ≤ z ∧ z < (2 ^ 62 : Int) then w = BitVec.ofInt 64 (2 * z + 1)
  else (w &&& 1#64) = 0#64 ∧ ∃ obj ∈ objs, obj.addr = w ∧ mpzIntCanonR0 obj z

theorem mpzLimbsVal_eq_limbsVal : ∀ xs : List (BitVec 64), mpzLimbsVal xs = limbsVal xs
  | [] => rfl
  | x :: xs => by
    unfold mpzLimbsVal
    simp only [List.foldr_cons, limbsVal_cons]
    congr 2
    exact mpzLimbsVal_eq_limbsVal xs

theorem natRepR0_preserving {w : BitVec 64} {n : Nat} {objs objs' : List LcnfObj}
    (h : natRepR0 w n objs) (hsub : ∀ o ∈ objs, o.addr = w → o ∈ objs') :
    natRepR0 w n objs' := by
  dsimp only [natRepR0] at h ⊢
  split at h <;> rename_i hs
  · simp only [hs]; exact h
  · simp only [hs]
    rcases h with ⟨hw, obj, hmem, had, hc⟩
    exact ⟨hw, obj, hsub obj hmem had, had, hc⟩

theorem intRepR0_preserving {w : BitVec 64} {z : Int} {objs objs' : List LcnfObj}
    (h : intRepR0 w z objs) (hsub : ∀ o ∈ objs, o.addr = w → o ∈ objs') :
    intRepR0 w z objs' := by
  dsimp only [intRepR0] at h ⊢
  split at h <;> rename_i hs
  · simp only [hs]; exact h
  · simp only [hs]
    rcases h with ⟨hw, obj, hmem, had, hc⟩
    exact ⟨hw, obj, hsub obj hmem had, had, hc⟩

/-- Outcome of `bn_dec_nat(rt, a)` stated over R0's `RtC0State` and `LcnfObj`. -/
@[expose] def DecNatRelR0 (a : BitVec 64) (st st' : RtC0State)
    (objs objs' : List LcnfObj) : Prop :=
  ((a &&& 1#64) ≠ 0#64 ∧ st' = st ∧ objs' = objs) ∨
  ((a &&& 1#64) = 0#64 ∧ ∃ obj ∈ objs, obj.addr = a ∧ obj.rc = 0#32 ∧ st' = st ∧ objs' = objs) ∨
  ((a &&& 1#64) = 0#64 ∧ ∃ (i : Nat) (hi : i < objs.length),
    objs[i].addr = a ∧ 1 < objs[i].rc.toInt ∧ st' = st ∧
    objs' = objs.set i (objs[i].withRc (objs[i].rc - 1#32))) ∨
  ((a &&& 1#64) = 0#64 ∧ st'.PreservesMeta st ∧ st'.rem = st.rem ∧ DecColdRel a objs objs')

/-- Allocation capacity predicate over R0's `RtC0State`. -/
@[expose] def canAllocBytesR0 (st : RtC0State) (bytes : Nat) : Prop :=
  st.hasFree bytes ∨ bytes ≤ st.rem

@[expose] def natPowOkR0 (aVal bVal scrCap : Nat) (st : RtC0State) : Prop :=
  bVal = 0 ∨ aVal = 0 ∨ aVal = 1 ∨
  (bVal < 2 ^ 63 ∧
   let tn := limbLenNat (aVal ^ bVal)
   tn ≤ mpzMaxLimbs ∧ 4 * (tn + 1) ≤ scrCap ∧
   (2 ^ 63 ≤ aVal ^ bVal → canAllocBytesR0 st (16 + 8 * tn)))

@[expose] def natGcdOkR0 (aVal bVal scrCap : Nat) (st : RtC0State) : Prop :=
  let na := limbLenNat aVal
  let nb := limbLenNat bVal
  let maxn := max na nb
  let g := Nat.gcd aVal bVal
  let tg := limbLenNat g
  (aVal = 0 ∧ bVal = 0) ∨
  (aVal = 0 ∧ bVal ≠ 0 ∧ nb ≤ scrCap ∧ (2 ^ 63 ≤ bVal → canAllocBytesR0 st (16 + 8 * nb))) ∨
  (aVal ≠ 0 ∧ bVal = 0 ∧ na ≤ scrCap ∧ (2 ^ 63 ≤ aVal → canAllocBytesR0 st (16 + 8 * na))) ∨
  (aVal ≠ 0 ∧ bVal ≠ 0 ∧ 4 * maxn ≤ scrCap ∧
    (2 ^ 63 ≤ g → canAllocBytesR0 st (16 + 8 * tg)))

@[expose] def natArithOkR0 (op aVal bVal scrCap : Nat) (st : RtC0State) : Prop :=
  let na := limbLenNat aVal
  let nb := limbLenNat bVal
  if op = 17 then
    aVal < 2 ^ 63 ∨
    (2 * na ≤ scrCap ∧
      (2 ^ 63 ≤ aVal - 1 → canAllocBytesR0 st (16 + 8 * limbLenNat (aVal - 1))))
  else if op ∈ [1, 2, 3, 4, 5] then
    let res := natArithRes op aVal bVal
    2 * (na + nb) + 2 ≤ scrCap ∧
    limbLenNat res ≤ mpzMaxLimbs ∧
    (2 ^ 63 ≤ res → canAllocBytesR0 st (16 + 8 * limbLenNat res))
  else if op ∈ [6, 7, 8] then
    2 * (na + nb) + 2 ≤ scrCap
  else False

@[expose] def natArithPostR0 (op aVal bVal : Nat) (res : BitVec 64)
    (objs objs' : List LcnfObj) : Prop :=
  if op = 6 then res = (if aVal = bVal then 1#64 else 0#64) ∧ objs' = objs
  else if op = 7 then res = (if aVal < bVal then 1#64 else 0#64) ∧ objs' = objs
  else if op = 8 then res = (if aVal ≤ bVal then 1#64 else 0#64) ∧ objs' = objs
  else natRepR0 res (natArithRes op aVal bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')

@[expose] def natBitsOkR0 (op : Nat) (aVal : Nat) (bRaw : BitVec 64) (objs : List LcnfObj)
    (scrCap : Nat) (st : RtC0State) : Prop :=
  let na := limbLenNat aVal
  if op = 13 then True
  else if op = 14 then
    2 ^ 63 ≤ aVal → canAllocBytesR0 st 24
  else if op = 19 then True
  else ∃ bVal : Nat, natRepR0 bRaw bVal objs ∧
    if op = 9 then
      let res := aVal >>> bVal
      (aVal < 2 ^ 63 ∨ 2 ^ 63 ≤ bVal ∨ na ≤ bVal / 64) ∨
      (2 * na - bVal / 64 ≤ scrCap ∧
        (2 ^ 63 ≤ res → canAllocBytesR0 st (16 + 8 * limbLenNat res)))
    else if op = 15 then
      aVal = 0 ∨
      (bVal < 2 ^ 63 ∧
       na + bVal / 64 + 1 ≤ mpzMaxLimbs ∧
       2 * na + bVal / 64 + 1 ≤ scrCap ∧
       (2 ^ 63 ≤ aVal <<< bVal → canAllocBytesR0 st (16 + 8 * limbLenNat (aVal <<< bVal))))
    else if op ∈ [10, 11, 12] then
      let nb := limbLenNat bVal
      let res := if op = 10 then Nat.land aVal bVal else if op = 11 then Nat.lor aVal bVal
        else Nat.xor aVal bVal
      na + nb + max na nb + 1 ≤ scrCap ∧
      (2 ^ 63 ≤ res → canAllocBytesR0 st (16 + 8 * limbLenNat res))
    else False

@[expose] def natBitsPostR0 (op : Nat) (aVal : Nat) (bRaw : BitVec 64) (res : BitVec 64)
    (objs objs' : List LcnfObj) : Prop :=
  if op = 13 then
    objs' = objs ∧
    res =
      (if bRaw.toNat = 0 then 0#64
       else if 64 ≤ bRaw.toNat then BitVec.ofNat 64 aVal
       else BitVec.ofNat 64 (aVal % 2 ^ bRaw.toNat))
  else if op = 14 then
    natRepR0 res aVal objs' ∧ (∀ o ∈ objs, o ∈ objs')
  else if op = 19 then
    natRepR0 res aVal.log2 objs' ∧ objs' = objs
  else ∃ bVal : Nat, natRepR0 bRaw bVal objs ∧ (∀ o ∈ objs, o ∈ objs') ∧
    if op = 9 then natRepR0 res (aVal >>> bVal) objs'
    else if op = 15 then natRepR0 res (aVal <<< bVal) objs'
    else if op = 10 then natRepR0 res (Nat.land aVal bVal) objs'
    else if op = 11 then natRepR0 res (Nat.lor aVal bVal) objs'
    else if op = 12 then natRepR0 res (Nat.xor aVal bVal) objs'
    else False

/-! ## 3. R1 Runtime `Spec`s Restated over `LeanLCNF.LcnfObj` / `RtC0State` (`G-R1`) -/

@[expose] def lcnfNatAllocSpecR0 : Spec [i64, i64] [i64] := fun (rt, nlimbs, ()) m Q _ =>
  let n' := max 1 nlimbs.toNat
  let bytes := 16 + 8 * n'
  ∃ (st : RtC0State) (R : Mem 64 → Prop),
    nlimbs.toNat ≤ mpzMaxLimbs ∧ st.Bounded48 ∧
    (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
    (rtC0Inv rt st ⋆ R) m ∧
    ∀ p st' m',
      let obj : LcnfObj :=
        { addr := p
          rc := 1#32
          csSz := if bytes < 65536 then bytes else 0
          other := 0
          tag := mpzTag
          cap := n'
          arrSize := n'
          limbs := List.replicate n' 0#64 }
      obj.Wf → (p &&& 1#64) = 0#64 →
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      (rtC0Inv rt st' ⋆ lcnfObjMem obj ⋆ R) m' → Q (p, ()) m'

@[expose] def bnDecNatSpecR0 : Spec [i64, i64] [] := fun (rt, a, ()) m Q _ =>
  if (a &&& 1#64) ≠ 0#64 then
    Q () m
  else
    ∃ (st : RtC0State) (objs : List LcnfObj) (R : Mem 64 → Prop),
      objs.length ≤ st.workCap ∧
      (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
      (∃ obj ∈ objs, obj.addr = a) ∧
      (∀ obj ∈ objs, obj.Wf) ∧ lcnfHeapClosed objs ∧
      (∀ obj ∈ objs, obj.addr = a → obj.rc = 1#32 → RcSound a objs) ∧
      ∀ st' objs' m',
        DecNatRelR0 a st st' objs objs' →
        (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q () m'

@[expose] def bnNatPowSpecR0 : Spec [i64, i64, i64] [i64] := fun (rt, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Nat) (R : Mem 64 → Prop),
    BigNumRtWfR0 rt st scr scrLimbs ∧
    natRepR0 a aVal objs ∧ natRepR0 b bVal objs ∧
    natPowOkR0 aVal bVal scrLimbs.length st ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
      natRepR0 res (aVal ^ bVal) objs' →
      (∀ o ∈ objs, o.addr = a ∨ o.addr = b → o ∈ objs') →
      (∀ o ∈ objs, o.addr ≠ res → o ∈ objs') →
      (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

@[expose] def bnNatGcdSpecR0 : Spec [i64, i64, i64] [i64] := fun (rt, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Nat) (R : Mem 64 → Prop),
    BigNumRtWfR0 rt st scr scrLimbs ∧
    natRepR0 a aVal objs ∧ natRepR0 b bVal objs ∧
    natGcdOkR0 aVal bVal scrLimbs.length st ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
      natRepR0 res (Nat.gcd aVal bVal) objs' →
      (∀ o ∈ objs, o ∈ objs') →
      (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

@[expose] def lcnfNatArithSpecR0 : Spec [i64, i64, i64, i64] [i64] :=
    fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Nat) (R : Mem 64 → Prop),
    BigNumRtWfR0 rt st scr scrLimbs ∧
    natRepR0 a aVal objs ∧
    (op.toNat = 17 ∨ natRepR0 b bVal objs) ∧
    natArithOkR0 op.toNat aVal bVal scrLimbs.length st ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
      natArithPostR0 op.toNat aVal bVal res objs objs' →
      (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

@[expose] def lcnfNatBitsSpecR0 : Spec [i64, i64, i64, i64] [i64] :=
    fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal : Nat) (R : Mem 64 → Prop),
    BigNumRtWfR0 rt st scr scrLimbs ∧
    (if op.toNat = 14 then aVal = a.toNat else natRepR0 a aVal objs) ∧
    natBitsOkR0 op.toNat aVal b objs scrLimbs.length st ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
      natBitsPostR0 op.toNat aVal b res objs objs' →
      (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

@[expose] def lcnfNatSlowSpecR0 : Spec [i64, i64, i64, i64] [i64] :=
    fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop),
    BigNumRtWfR0 rt st scr scrLimbs ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    (if op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] then
      ∃ aVal bVal, natRepR0 a aVal objs ∧ (op.toNat = 17 ∨ natRepR0 b bVal objs) ∧
        natArithOkR0 op.toNat aVal bVal scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
          natArithPostR0 op.toNat aVal bVal res objs objs' →
          (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat ∈ [9, 10, 11, 12, 13, 14, 15, 19] then
      ∃ aVal, (if op.toNat = 14 then aVal = a.toNat else natRepR0 a aVal objs) ∧
        natBitsOkR0 op.toNat aVal b objs scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
          natBitsPostR0 op.toNat aVal b res objs objs' →
          (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 16 then
      ∃ aVal bVal, natRepR0 a aVal objs ∧ natRepR0 b bVal objs ∧
        natPowOkR0 aVal bVal scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
          natRepR0 res (aVal ^ bVal) objs' →
          (∀ o ∈ objs, o.addr ≠ res → o ∈ objs') →
          (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 18 then
      ∃ aVal bVal, natRepR0 a aVal objs ∧ natRepR0 b bVal objs ∧
        natGcdOkR0 aVal bVal scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
          natRepR0 res (Nat.gcd aVal bVal) objs' →
          (∀ o ∈ objs, o ∈ objs') →
          (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else False)

@[expose] def lcnfIntConvSpecR0 : Spec [i64, i64, i64] [i64] := fun (rt, op, a, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop),
    BigNumRtWfR0 rt st scr scrLimbs ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    (if op.toNat = 1 then
      ∃ aVal : Nat, natRepR0 a aVal objs ∧
        ((2 ^ 62 ≤ aVal ∧ aVal < 2 ^ 63) → canAllocBytesR0 st 24) ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
          intRepR0 res (aVal : Int) objs' →
          (∀ o ∈ objs, o ∈ objs') →
          (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 13 then
      let z : Int := a.toInt
      ((z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytesR0 st 24) ∧
      ∀ res st' scrLimbs' objs' m',
        st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
        intRepR0 res z objs' →
        (∀ o ∈ objs, o ∈ objs') →
        (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 16 then
      ∃ z : Int, intRepR0 a z objs ∧
        ∀ m', (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m' →
          Q (if (0 : Int) ≤ z then 1#64 else 0#64, ()) m'
    else if op.toNat = 2 then
      ∃ aVal : Nat, natRepR0 a aVal objs ∧
        let z := Int.negSucc aVal
        let tn := limbLenNat (aVal + 1)
        tn ≤ mpzMaxLimbs ∧
        (2 ^ 63 ≤ aVal →
          limbLenNat aVal + 1 ≤ scrLimbs.length ∧
          objs.length ≤ st.workCap ∧ (∀ o ∈ objs, o.Wf) ∧ lcnfHeapClosed objs ∧
          (∀ o ∈ objs, o.addr = a → o.rc = 1#32 → RcSound a objs) ∧
          16 + 8 * tn ≤ st.rem) ∧
        ((aVal < 2 ^ 63 ∧ z < -(2 ^ 62 : Int)) → canAllocBytesR0 st 24) ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
          intRepR0 res z objs' →
          (∀ o ∈ objs, o.addr ≠ a → ∃ o' ∈ objs', o'.addr = o.addr ∧ o'.tag = o.tag ∧
            o'.other = o.other ∧ o'.arrSize = o.arrSize ∧ o'.cap = o.cap ∧
            o'.limbs = o.limbs ∧ (o.Wf → o'.Wf)) →
          (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 3 then
      ∃ z : Int, intRepR0 a z objs ∧
        (z ≠ 0 → limbLenNat z.natAbs ≤ scrLimbs.length ∧
          ((-z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ -z) →
            canAllocBytesR0 st (16 + 8 * limbLenNat z.natAbs))) ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
          intRepR0 res (-z) objs' →
          (∀ o ∈ objs, o ∈ objs') →
          (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 9 then
      ∃ z : Int, intRepR0 a z objs ∧
        (z ≠ 0 → limbLenNat z.natAbs ≤ scrLimbs.length ∧
          (2 ^ 63 ≤ z.natAbs → canAllocBytesR0 st (16 + 8 * limbLenNat z.natAbs))) ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
          natRepR0 res z.natAbs objs' →
          (∀ o ∈ objs, o ∈ objs') →
          (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else False)

@[expose] def lcnfIntAddSubCmpSpecR0 : Spec [i64, i64, i64, i64] [i64] :=
    fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Int) (R : Mem 64 → Prop),
    let na := limbLenNat aVal.natAbs
    let nb := limbLenNat bVal.natAbs
    BigNumRtWfR0 rt st scr scrLimbs ∧
    intRepR0 a aVal objs ∧ intRepR0 b bVal objs ∧
    na + nb + max na nb + 1 ≤ scrLimbs.length ∧
    op.toNat ∈ [4, 5, 10, 11, 12] ∧
    (op.toNat ∈ [4, 5] →
      let z := if op.toNat = 4 then aVal + bVal else aVal - bVal
      let tn := limbLenNat z.natAbs
      tn ≤ mpzMaxLimbs ∧
      ((z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytesR0 st (16 + 8 * tn))) ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
      (if op.toNat = 4 then intRepR0 res (aVal + bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')
       else if op.toNat = 5 then intRepR0 res (aVal - bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')
       else if op.toNat = 10 then res = (if aVal = bVal then 1#64 else 0#64) ∧ objs' = objs
       else if op.toNat = 11 then res = (if aVal < bVal then 1#64 else 0#64) ∧ objs' = objs
       else res = (if aVal ≤ bVal then 1#64 else 0#64) ∧ objs' = objs) →
      (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

@[expose] def lcnfIntMulDivSpecR0 : Spec [i64, i64, i64, i64] [i64] :=
    fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Int) (R : Mem 64 → Prop),
    let na := limbLenNat aVal.natAbs
    let nb := limbLenNat bVal.natAbs
    let z := intMulDivRes op.toNat aVal bVal
    let tn := limbLenNat z.natAbs
    BigNumRtWfR0 rt st scr scrLimbs ∧
    intRepR0 a aVal objs ∧ intRepR0 b bVal objs ∧
    op.toNat ∈ [6, 7, 8, 14, 15] ∧
    2 * (na + nb) + max na nb + 2 ≤ scrLimbs.length ∧
    tn ≤ mpzMaxLimbs ∧
    ((z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytesR0 st (16 + 8 * tn)) ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWfR0 rt st' scr scrLimbs' →
      intRepR0 res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (fullRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

@[expose] def lcnfIntOpSpecR0 : Spec [i64, i64, i64, i64] [i64] :=
    fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop),
    BigNumRtWfR0 rt st scr scrLimbs ∧
    (fullRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    (if op.toNat ∈ [1, 2, 3, 9, 13, 16] then
      lcnfIntConvSpecR0 (rt, op, a, ()) m Q (fun _ _ _ _ => False)
    else if op.toNat ∈ [4, 5, 10, 11, 12] then
      lcnfIntAddSubCmpSpecR0 (rt, op, a, b, ()) m Q (fun _ _ _ _ => False)
    else if op.toNat ∈ [6, 7, 8, 14, 15] then
      lcnfIntMulDivSpecR0 (rt, op, a, b, ()) m Q (fun _ _ _ _ => False)
    else False)

end LeanQbe.T.LeanLCNF.Sem
