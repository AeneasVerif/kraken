module

public import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.ControlComb
import Kraken.Separation

/-!
# Shared Proof Infrastructure for `LcnfC0Rt`

Provides shared `c0_load`/`c0_store` bridge lemmas, BitVec/alignment/tag arithmetic helpers,
`RtC0State` & `rtC0Inv` focus/update helpers, and shared `LcnfObj`/`lcnfHeap`/worklist/DFS
invariants used by `LcnfC0RtProofM0a`, `LcnfC0RtProofM0b`, and `LcnfC0RtProofNv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.C0Step
open Std.ExtHashMap

/-! ## 1. Baseline `c0_load` / `c0_store` Theorems in `LeanQbe.T.LeanLCNF` -/

@[local c0_load] theorem c0_load_cell64_add8_imm {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem
    64} (h : (cell64 (a + 8#64) v ⋆ R) m) : loadVal m i64 (a + 8) = some v := loadVal_cell64 h

@[local c0_store] theorem c0_store_cell64_add8_imm {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64
    → Prop} {m : Mem 64} (h : (cell64 (a + 8#64) v0 ⋆ R) m) : storeOk m i64 (a + 8) ∧ (cell64 (a +
    8#64) v ⋆ R) (storeMem m i64 (a + 8) v) := store_cell64 v h

@[local c0_load] theorem c0_load_cell64_add16_imm {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem
    64} (h : (cell64 (a + 16#64) v ⋆ R) m) : loadVal m i64 (a + 16) = some v := loadVal_cell64 h

@[local c0_store] theorem c0_store_cell64_add16_imm {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64
    → Prop} {m : Mem 64} (h : (cell64 (a + 16#64) v0 ⋆ R) m) : storeOk m i64 (a + 16) ∧ (cell64 (a
    + 16#64) v ⋆ R) (storeMem m i64 (a + 16) v) := store_cell64 v h

@[local c0_load] theorem c0_load_array64_fl {rt i : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64
    → Prop} {m : Mem 64} (h : (array64 (rt + 33024#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (rt + 33024 + i * 8) = some (xs[i.toNat]'hi) := c0_load_array64 h hi

@[local c0_store] theorem c0_store_array64_fl {rt i : BitVec 64} {xs : List (BitVec 64)} (v :
    BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (rt + 33024#64) xs ⋆ R) m) (hi :
    i.toNat < xs.length) : storeOk m i64 (rt + 33024 + i * 8) ∧ (array64 (rt + 33024#64) (xs.set
    i.toNat v) ⋆ R) (storeMem m i64 (rt + 33024 + i * 8) v) := c0_store_array64 v h hi

private theorem shl3_eq_mul8_priv (i : BitVec 64) : i <<< 3#64 = i * 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mul_comm]

@[local c0_load] theorem c0_load_array64_shl3 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + (i <<< 3#64)) = some (xs[i.toNat]'hi) := by
  rw [shl3_eq_mul8_priv]; exact c0_load_array64 h hi

@[local c0_store] theorem c0_store_array64_shl3 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) : storeOk m i64 (a + (i <<< 3#64)) ∧
    (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + (i <<< 3#64)) v) := by
  rw [shl3_eq_mul8_priv]; exact c0_store_array64 v h hi

@[local c0_load] theorem c0_load_array64_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 8#64 * i) = some (xs[i.toNat]'hi) := by
  rw [BitVec.mul_comm 8#64 i]; exact c0_load_array64 h hi

@[local c0_store] theorem c0_store_array64_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) : storeOk m i64 (a + 8#64 * i) ∧
    (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + 8#64 * i) v) := by
  rw [BitVec.mul_comm 8#64 i]; exact c0_store_array64 v h hi

/-! ## 2. Shared Helpers in `LeanQbe.T.LeanLCNF.RtProof` -/

namespace RtProof

@[expose] def RtC0State.withWorkBuf (st : RtC0State) (wb : List (BitVec 64))
    (hlen : wb.length = st.hdr.s_work_cap.toNat) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := st.hdr
  workBuf := wb
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := hlen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

@[expose] def RtC0State.withColdDecs (st : RtC0State) (v : BitVec 64) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := { st.hdr with s_st_cold_decs := v }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

@[expose] def RtC0State.withColdDecsInc (st : RtC0State) : RtC0State :=
  RtC0State.withColdDecs st (st.hdr.s_st_cold_decs + 1#64)

@[expose] def RtC0State.withPersist (st : RtC0State) (v : BitVec 64) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := { st.hdr with s_st_persistent := v }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

@[expose] def RtC0State.withPersistInc (st : RtC0State) : RtC0State :=
  RtC0State.withPersist st (st.hdr.s_st_persistent + 1#64)

@[expose] def lcnfObjBody (o : LcnfObj) : Mem 64 → Prop :=
  if o.tag = closureTag then
    cell64 (o.addr + 8#64) o.funId ⋆ cell64 (o.addr + 16#64) o.cloMeta ⋆
      array64 (o.addr + 24#64) o.fields ⋆
      region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
        (o.csSz - (24 + 8 * o.fields.length))
  else if o.tag = arrayTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆ array64 (o.addr + 24#64) o.fields ⋆
      region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
        (8 * (o.cap - o.fields.length))
  else if o.tag = sarrayTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      bytes (o.addr + 24#64) o.scalarData ⋆
      region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
        (o.totalBytes - (24 + o.scalarData.length))
  else if o.tag = stringTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
      bytes (o.addr + 32#64) o.scalarData ⋆
      region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length))
        (o.totalBytes - (32 + o.scalarData.length))
  else if o.tag = mpzTag then
    cell64 (o.addr + 8#64) o.mpzMeta ⋆ array64 (o.addr + 16#64) o.limbs
  else
    let soff := 8 + 8 * o.fields.length
    array64 (o.addr + 8#64) o.fields ⋆
      bytes (o.addr + BitVec.ofNat 64 soff) o.scalarData ⋆
      region (o.addr + BitVec.ofNat 64 (soff + o.scalarData.length))
        (o.csSz - (soff + o.scalarData.length))

@[expose] def SameNonRc (a b : LcnfObj) : Prop :=
  b.addr = a.addr ∧ b.csSz = a.csSz ∧ b.other = a.other ∧ b.tag = a.tag ∧
  b.funId = a.funId ∧ b.arity = a.arity ∧ b.cap = a.cap ∧ b.arrSize = a.arrSize ∧
  b.strLen = a.strLen ∧ b.fields = a.fields ∧ b.scalarData = a.scalarData ∧ b.limbs = a.limbs

@[expose] def objFieldsOff (o : LcnfObj) : BitVec 64 :=
  if o.tag = closureTag ∨ o.tag = arrayTag then 24#64 else 8#64

@[expose] def unmarkedCount (objs : List LcnfObj) : Nat :=
  (objs.filter (fun o => o.rc != 0#32)).length

/-! ### Scoped `c0_load` / `c0_store` Lemmas -/

@[scoped c0_load] theorem load_cell64_var {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} (h :
    (cell64 a v ⋆ R) m) : loadVal m i64 a = some v := loadVal_cell64 h
@[scoped c0_store] theorem store_cell64_var {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64 → Prop}
    {m : Mem 64} (h : (cell64 a v0 ⋆ R) m) : storeOk m i64 a ∧ (cell64 a v ⋆ R) (storeMem m i64 a
    v) := store_cell64 v h
@[scoped c0_load] theorem load_cell64_add8_imm {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 8#64) v ⋆ R) m) : loadVal m i64 (a + 8) = some v := loadVal_cell64 h
@[scoped c0_load] theorem load_cell64_add8_imm64 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem
    64} (h : (cell64 (a + 8#64) v ⋆ R) m) : loadVal m i64 (a + 8#64) = some v := loadVal_cell64 h
@[scoped c0_store] theorem store_cell64_add8_imm {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64 →
    Prop} {m : Mem 64} (h : (cell64 (a + 8#64) v0 ⋆ R) m) : storeOk m i64 (a + 8) ∧ (cell64 (a +
    8#64) v ⋆ R) (storeMem m i64 (a + 8) v) := store_cell64 v h
@[scoped c0_store] theorem store_cell64_add8_imm64 {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64
    → Prop} {m : Mem 64} (h : (cell64 (a + 8#64) v0 ⋆ R) m) : storeOk m i64 (a + 8#64) ∧ (cell64
    (a + 8#64) v ⋆ R) (storeMem m i64 (a + 8#64) v) := store_cell64 v h
@[scoped c0_load] theorem load_cell64_add16_imm {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 16#64) v ⋆ R) m) : loadVal m i64 (a + 16) = some v := loadVal_cell64 h
@[scoped c0_load] theorem load_cell64_add16_imm64 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem
    64} (h : (cell64 (a + 16#64) v ⋆ R) m) : loadVal m i64 (a + 16#64) = some v := loadVal_cell64
    h
@[scoped c0_store] theorem store_cell64_add16_imm {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64 →
    Prop} {m : Mem 64} (h : (cell64 (a + 16#64) v0 ⋆ R) m) : storeOk m i64 (a + 16) ∧ (cell64 (a +
    16#64) v ⋆ R) (storeMem m i64 (a + 16) v) := store_cell64 v h
@[scoped c0_store] theorem store_cell64_add16_imm64 {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64
    → Prop} {m : Mem 64} (h : (cell64 (a + 16#64) v0 ⋆ R) m) : storeOk m i64 (a + 16#64) ∧ (cell64
    (a + 16#64) v ⋆ R) (storeMem m i64 (a + 16#64) v) := store_cell64 v h
@[scoped c0_load] theorem load_array64_fl {rt i : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64 →
    Prop} {m : Mem 64} (h : (array64 (rt + 33024#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (rt + 33024 + i * 8) = some (xs[i.toNat]'hi) := c0_load_array64 h hi
@[scoped c0_load] theorem load_array64_fl64 {rt i : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64
    → Prop} {m : Mem 64} (h : (array64 (rt + 33024#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (rt + 33024#64 + i * 8#64) = some (xs[i.toNat]'hi) := c0_load_array64 h hi
@[scoped c0_store] theorem store_array64_fl {rt i : BitVec 64} {xs : List (BitVec 64)} (v : BitVec
    64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (rt + 33024#64) xs ⋆ R) m) (hi : i.toNat <
    xs.length) : storeOk m i64 (rt + 33024 + i * 8) ∧ (array64 (rt + 33024#64) (xs.set i.toNat v)
    ⋆ R) (storeMem m i64 (rt + 33024 + i * 8) v) := c0_store_array64 v h hi
@[scoped c0_store] theorem store_array64_fl64 {rt i : BitVec 64} {xs : List (BitVec 64)} (v :
    BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (rt + 33024#64) xs ⋆ R) m) (hi :
    i.toNat < xs.length) : storeOk m i64 (rt + 33024#64 + i * 8#64) ∧ (array64 (rt + 33024#64)
    (xs.set i.toNat v) ⋆ R) (storeMem m i64 (rt + 33024#64 + i * 8#64) v) := c0_store_array64 v h
    hi
@[scoped c0_load] theorem load_array64_shl3 {a i : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64
    → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) : loadVal m i64 (a
    + (i <<< 3#64)) = some (xs[i.toNat]'hi) := c0_load_array64_shl3 h hi
@[scoped c0_store] theorem store_array64_shl3 {a i : BitVec 64} {xs : List (BitVec 64)} (v :
    BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat <
    xs.length) : storeOk m i64 (a + (i <<< 3#64)) ∧ (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m
    i64 (a + (i <<< 3#64)) v) := c0_store_array64_shl3 v h hi
@[scoped c0_load] theorem load_array64_mul8 {a i : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64
    → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) : loadVal m i64 (a
    + 8#64 * i) = some (xs[i.toNat]'hi) := c0_load_array64_mul8 h hi
@[scoped c0_store] theorem store_array64_mul8 {a i : BitVec 64} {xs : List (BitVec 64)} (v :
    BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat <
    xs.length) : storeOk m i64 (a + 8#64 * i) ∧ (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64
    (a + 8#64 * i) v) := c0_store_array64_mul8 v h hi
@[scoped c0_load] theorem load_array64_8mul {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 8 * i) = some (xs[i.toNat]'hi) := by
  rw [BitVec.mul_comm 8 i]; exact c0_load_array64 h hi
@[scoped c0_store] theorem store_array64_8mul {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) : storeOk m i64 (a + 8 * i) ∧
    (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + 8 * i) v) := by
  rw [BitVec.mul_comm 8 i]; exact c0_store_array64 v h hi
@[scoped c0_load] theorem load_array64_24_8mul {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (a + 24#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 24 + 8 * i) = some (xs[i.toNat]'hi) := by
  rw [show (a + 24 + 8 * i : BitVec 64) = (a + 24#64) + i * 8 by rw [BitVec.mul_comm 8 i]; rfl]
  exact c0_load_array64 h hi
@[scoped c0_store] theorem store_array64_24_8mul {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (a + 24#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + 24 + 8 * i) ∧ (array64 (a + 24#64) (xs.set i.toNat v) ⋆ R)
    (storeMem m i64 (a + 24 + 8 * i) v) := by
  rw [show (a + 24 + 8 * i : BitVec 64) = (a + 24#64) + i * 8 by rw [BitVec.mul_comm 8 i]; rfl]
  exact c0_store_array64 v h hi
@[scoped c0_load] theorem load_array64_24_8mul64 {a i : BitVec 64} {xs : List (BitVec 64)} {R :
    Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 24#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 24#64 + 8#64 * i) = some (xs[i.toNat]'hi) := load_array64_24_8mul h hi
@[scoped c0_store] theorem store_array64_24_8mul64 {a i : BitVec 64} {xs : List (BitVec 64)} (v :
    BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 24#64) xs ⋆ R) m) (hi : i.toNat
    < xs.length) : storeOk m i64 (a + 24#64 + 8#64 * i) ∧ (array64 (a + 24#64) (xs.set i.toNat v)
    ⋆ R) (storeMem m i64 (a + 24#64 + 8#64 * i) v) := store_array64_24_8mul v h hi
@[scoped c0_load] theorem load_array64_mul8_l64 {a i : BitVec 64} {xs : List (BitVec 64)} {R : Mem
    64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) : loadVal m i64
    (a + i * 8#64) = some (xs[i.toNat]'hi) := c0_load_array64 h hi
@[scoped c0_store] theorem store_array64_mul8_l64 {a i : BitVec 64} {xs : List (BitVec 64)} (v :
    BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat <
    xs.length) : storeOk m i64 (a + i * 8#64) ∧ (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64
    (a + i * 8#64) v) := c0_store_array64 v h hi
@[scoped c0_load] theorem load_rtAt_large_free64 {p : BitVec 64} {s : LcnfC0Rt} {R : Mem 64 →
    Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : loadVal m i64 (p + 33536#64) = some
    s.s_large_free := LcnfC0Rt.load_s_large_free h
@[scoped c0_store] theorem store_rtAt_large_free64 {p : BitVec 64} {s : LcnfC0Rt} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : storeOk m i64 (p + 33536#64)
    ∧ (LcnfC0Rt.At p { s with s_large_free := v } ⋆ R) (storeMem m i64 (p + 33536#64) v) :=
    LcnfC0Rt.store_s_large_free v h
@[scoped c0_load] theorem load_rtAt_cur64 {p : BitVec 64} {s : LcnfC0Rt} {R : Mem 64 → Prop} {m :
    Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : loadVal m i64 (p + 33552#64) = some s.s_cur :=
    LcnfC0Rt.load_s_cur h
@[scoped c0_store] theorem store_rtAt_cur64 {p : BitVec 64} {s : LcnfC0Rt} (v : BitVec 64) {R :
    Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : storeOk m i64 (p + 33552#64) ∧
    (LcnfC0Rt.At p { s with s_cur := v } ⋆ R) (storeMem m i64 (p + 33552#64) v) :=
    LcnfC0Rt.store_s_cur v h
@[scoped c0_load] theorem load_rtAt_end64 {p : BitVec 64} {s : LcnfC0Rt} {R : Mem 64 → Prop} {m :
    Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : loadVal m i64 (p + 33560#64) = some s.s_end :=
    LcnfC0Rt.load_s_end h
@[scoped c0_load] theorem load_rtAt_work64 {p : BitVec 64} {s : LcnfC0Rt} {R : Mem 64 → Prop} {m :
    Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : loadVal m i64 (p + 33568#64) = some s.s_work :=
    LcnfC0Rt.load_s_work h
@[scoped c0_load] theorem load_rtAt_work_cap64 {p : BitVec 64} {s : LcnfC0Rt} {R : Mem 64 → Prop}
    {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : loadVal m i64 (p + 33576#64) = some s.s_work_cap
    := LcnfC0Rt.load_s_work_cap h
@[scoped c0_load] theorem load_rtAt_persistent64 {p : BitVec 64} {s : LcnfC0Rt} {R : Mem 64 →
    Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : loadVal m i64 (p + 33640#64) = some
    s.s_st_persistent := LcnfC0Rt.load_s_st_persistent h
@[scoped c0_store] theorem store_rtAt_persistent64 {p : BitVec 64} {s : LcnfC0Rt} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : storeOk m i64 (p + 33640#64)
    ∧ (LcnfC0Rt.At p { s with s_st_persistent := v } ⋆ R) (storeMem m i64 (p + 33640#64) v) :=
    LcnfC0Rt.store_s_st_persistent v h
@[scoped c0_load] theorem load_rtAt_reused64 {p : BitVec 64} {s : LcnfC0Rt} {R : Mem 64 → Prop} {m
    : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : loadVal m i64 (p + 33648#64) = some s.s_st_reused :=
    LcnfC0Rt.load_s_st_reused h
@[scoped c0_store] theorem store_rtAt_reused64 {p : BitVec 64} {s : LcnfC0Rt} (v : BitVec 64) {R :
    Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : storeOk m i64 (p + 33648#64) ∧
    (LcnfC0Rt.At p { s with s_st_reused := v } ⋆ R) (storeMem m i64 (p + 33648#64) v) :=
    LcnfC0Rt.store_s_st_reused v h
@[scoped c0_load] theorem load_rtAt_cold_decs64 {p : BitVec 64} {s : LcnfC0Rt} {R : Mem 64 → Prop}
    {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : loadVal m i64 (p + 33656#64) = some
    s.s_st_cold_decs := LcnfC0Rt.load_s_st_cold_decs h
@[scoped c0_store] theorem store_rtAt_cold_decs64 {p : BitVec 64} {s : LcnfC0Rt} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) : storeOk m i64 (p + 33656#64)
    ∧ (LcnfC0Rt.At p { s with s_st_cold_decs := v } ⋆ R) (storeMem m i64 (p + 33656#64) v) :=
    LcnfC0Rt.store_s_st_cold_decs v h
theorem rtC0Inv_hdr_focus {rt : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : (LcnfC0Rt.At rt st.hdr ⋆
    (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
    array64 (rt + 33024#64) st.freeList ⋆ array64 st.hdr.s_work st.workBuf ⋆
    smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
    largeFreeList st.hdr.s_large_free st.largeNodes ⋆ region st.hdr.s_cur st.rem ⋆ R)) m := by
  unfold rtC0Inv at hm; exact sep_cast hm (by ac_rfl)

theorem rtC0Inv_work_focus {rt : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : (array64 st.hdr.s_work st.workBuf ⋆
    (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
    array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
    smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
    largeFreeList st.hdr.s_large_free st.largeNodes ⋆ region st.hdr.s_cur st.rem ⋆ R)) m := by
  unfold rtC0Inv at hm; exact sep_cast hm (by ac_rfl)

@[scoped c0_load] theorem load_rtC0Inv_s_work {rt : BitVec 64} {st : RtC0State} {R : Mem 64 →
    Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : loadVal m i64 (rt + 33568) = some
    st.hdr.s_work := LcnfC0Rt.load_s_work (rtC0Inv_hdr_focus hm)

@[scoped c0_load] theorem load_rtC0Inv_s_work64 {rt : BitVec 64} {st : RtC0State} {R : Mem 64 →
    Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : loadVal m i64 (rt + 33568#64) = some
    st.hdr.s_work := LcnfC0Rt.load_s_work (rtC0Inv_hdr_focus hm)

@[scoped c0_load] theorem load_rtC0Inv_s_work_cap {rt : BitVec 64} {st : RtC0State} {R : Mem 64 →
    Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : loadVal m i64 (rt + 33576) = some
    st.hdr.s_work_cap := LcnfC0Rt.load_s_work_cap (rtC0Inv_hdr_focus hm)

@[scoped c0_load] theorem load_rtC0Inv_s_work_cap64 {rt : BitVec 64} {st : RtC0State} {R : Mem 64
    → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : loadVal m i64 (rt + 33576#64) = some
    st.hdr.s_work_cap := LcnfC0Rt.load_s_work_cap (rtC0Inv_hdr_focus hm)

@[scoped c0_load] theorem load_rtC0Inv_s_st_cold_decs {rt : BitVec 64} {st : RtC0State} {R : Mem
    64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : loadVal m i64 (rt + 33656) = some
    st.hdr.s_st_cold_decs := LcnfC0Rt.load_s_st_cold_decs (rtC0Inv_hdr_focus hm)

@[scoped c0_load] theorem load_rtC0Inv_s_st_cold_decs64 {rt : BitVec 64} {st : RtC0State} {R : Mem
    64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : loadVal m i64 (rt + 33656#64) = some
    st.hdr.s_st_cold_decs := LcnfC0Rt.load_s_st_cold_decs (rtC0Inv_hdr_focus hm)

@[scoped c0_store] theorem store_rtC0Inv_s_st_cold_decs {rt : BitVec 64} {st : RtC0State}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    storeOk m i64 (rt + 33656) ∧
    (rtC0Inv rt (RtC0State.withColdDecs st v) ⋆ R) (storeMem m i64 (rt + 33656) v) := by
  have h1 := LcnfC0Rt.store_s_st_cold_decs v (rtC0Inv_hdr_focus hm)
  refine ⟨h1.1, ?_⟩
  unfold rtC0Inv RtC0State.withColdDecs; exact sep_cast h1.2 (by ac_rfl)

@[scoped c0_store] theorem store_rtC0Inv_s_st_cold_decs64 {rt : BitVec 64} {st : RtC0State}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    storeOk m i64 (rt + 33656#64) ∧
    (rtC0Inv rt (RtC0State.withColdDecs st v) ⋆ R) (storeMem m i64 (rt + 33656#64) v) :=
  store_rtC0Inv_s_st_cold_decs v hm

@[scoped c0_load] theorem load_rtC0Inv_s_st_persistent {rt : BitVec 64} {st : RtC0State} {R : Mem
    64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : loadVal m i64 (rt + 33640) = some
    st.hdr.s_st_persistent := LcnfC0Rt.load_s_st_persistent (rtC0Inv_hdr_focus hm)

@[scoped c0_load] theorem load_rtC0Inv_s_st_persistent64 {rt : BitVec 64} {st : RtC0State} {R :
    Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) : loadVal m i64 (rt + 33640#64) =
    some st.hdr.s_st_persistent := LcnfC0Rt.load_s_st_persistent (rtC0Inv_hdr_focus hm)

@[scoped c0_store] theorem store_rtC0Inv_s_st_persistent {rt : BitVec 64} {st : RtC0State}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    storeOk m i64 (rt + 33640) ∧
    (rtC0Inv rt (RtC0State.withPersist st v) ⋆ R) (storeMem m i64 (rt + 33640) v) := by
  have h1 := LcnfC0Rt.store_s_st_persistent v (rtC0Inv_hdr_focus hm)
  refine ⟨h1.1, ?_⟩
  unfold rtC0Inv RtC0State.withPersist; exact sep_cast h1.2 (by ac_rfl)

@[scoped c0_store] theorem store_rtC0Inv_s_st_persistent64 {rt : BitVec 64} {st : RtC0State}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    storeOk m i64 (rt + 33640#64) ∧
    (rtC0Inv rt (RtC0State.withPersist st v) ⋆ R) (storeMem m i64 (rt + 33640#64) v) :=
  store_rtC0Inv_s_st_persistent v hm

theorem rtC0Inv_load_work {rt : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (hi : i < st.workBuf.length) (hm : (rtC0Inv rt st ⋆ R) m) :
    loadVal m i64 (st.hdr.s_work + BitVec.ofNat 64 (8 * i)) = some (st.workBuf[i]'hi) :=
  loadVal_array64 hi (rtC0Inv_work_focus hm)

theorem rtC0Inv_store_work {rt : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (hi : i < st.workBuf.length) (v : BitVec 64)
    (hm : (rtC0Inv rt st ⋆ R) m) : storeOk m i64 (st.hdr.s_work + BitVec.ofNat 64 (8 * i)) ∧
    (rtC0Inv rt (RtC0State.withWorkBuf st (st.workBuf.set i v)
    (by rw [List.length_set]; exact st.workLen))
    ⋆ R) (storeMem m i64 (st.hdr.s_work + BitVec.ofNat 64 (8 * i)) v) := by
  have h1 := store_array64 v hi (rtC0Inv_work_focus hm)
  refine ⟨h1.1, ?_⟩
  unfold rtC0Inv RtC0State.withWorkBuf; exact sep_cast h1.2 (by ac_rfl)

/-! ### BitVec, Alignment, Tag, and List Helpers -/

theorem ptr_add_nat_p (a : BitVec 64) (m n : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem shl3_eq_mul8 (i : BitVec 64) : i <<< 3#64 = i * 8 := shl3_eq_mul8_priv i

theorem bv64_and_mask8 (x : BitVec 64) :
    x &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 ((x.toNat / 8) * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by decide : 0xfffffffffffffff8 < 2 ^ 64),
    Nat.mod_eq_of_lt (by have := x.isLt; omega : (x.toNat / 8) * 8 < 2 ^ 64)]
  apply Nat.eq_of_testBit_eq
  intro i; have h1 : (0xfffffffffffffff8 : Nat) = (2 ^ 61 - 1) <<< 3 := by decide
  have h2 : (x.toNat / 8) * 8 = (x.toNat >>> 3) <<< 3 := by
    simp [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.testBit_and, h1, h2, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · by_cases h3 : 3 ≤ i
    · have hsr : (x.toNat >>> 3).testBit (i - 3) = x.toNat.testBit i := by
        rw [Nat.testBit_shiftRight, show 3 + (i - 3) = i by omega]
      simp [h3, show i - 3 < 61 by omega, hsr]
    · simp [h3]
  · have hlt : x.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
    by_cases h3 : 3 ≤ i <;> simp [h3, show ¬(i - 3 < 61) by omega, hlt]

theorem align8_bv_eq (sz : BitVec 64) (hsz : sz.toNat ≤ 268435448) :
    (sz + 7) &&& 18446744073709551608 = BitVec.ofNat 64 (align8 sz.toNat) := by
  change (sz + 7#64) &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 (align8 sz.toNat)
  rw [bv64_and_mask8]; unfold align8; congr 1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 7 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : sz.toNat + 7 < 2 ^ 64)]

theorem align8_div8_eq (sz : BitVec 64) (hsz : sz.toNat ≤ 268435448) :
    ((sz + 7) &&& 18446744073709551608) >>> 3 = BitVec.ofNat 64 (align8 sz.toNat / 8) := by
  rw [align8_bv_eq sz hsz]; apply BitVec.eq_of_toNat_eq; unfold align8
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp [Nat.shiftRight_eq_div_pow]

theorem align8_div8_mul8 {n : Nat} (h : n % 8 = 0) : 8 * (n / 8) = n := by omega

theorem bv_and7_eq_zero_of_mod8 {x : BitVec 64} (h : x.toNat % 8 = 0) : x &&& 7#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_zero,
    Nat.mod_eq_of_lt (by decide : 7 < 2 ^ 64),
    show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, show 2 ^ 3 = 8 from rfl]
  exact h

theorem bv_ofNat_div8 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  simp [Nat.shiftRight_eq_div_pow]

theorem bump_cur_nz {cur endp : BitVec 64} {bytes : Nat}
    (hcur : cur ≠ 0#64) (hle : cur.toNat ≤ endp.toNat) (hbytes : bytes ≤ endp.toNat - cur.toNat) :
    cur + BitVec.ofNat 64 bytes ≠ 0#64 := by
  have := endp.isLt; c0_bv_omega

theorem bump_cur_align {cur endp : BitVec 64} {bytes : Nat}
    (hal : cur.toNat % 8 = 0) (hle : cur.toNat ≤ endp.toNat)
    (hbytes : bytes ≤ endp.toNat - cur.toNat) (hmod : bytes % 8 = 0) :
    (cur + BitVec.ofNat 64 bytes).toNat % 8 = 0 := by
  have hlt : cur.toNat + bytes < 2 ^ 64 := by have := endp.isLt; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bytes < 2 ^ 64),
    Nat.mod_eq_of_lt hlt]
  omega

theorem bump_curLeEnd {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ sEnd.toNat - cur.toNat) :
    (cur + BitVec.ofNat 64 bytes).toNat ≤ sEnd.toNat := by
  unfold rtMaxObjBytes at hmax; have := sEnd.isLt; c0_bv_omega

theorem bump_rem_eq {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ sEnd.toNat - cur.toNat) :
    sEnd.toNat - (cur + BitVec.ofNat 64 bytes).toNat = sEnd.toNat - cur.toNat - bytes := by
  unfold rtMaxObjBytes at hmax; have := sEnd.isLt; c0_bv_omega

theorem rem_of_not_gt {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hnot : ¬ BitVec.toNat (sEnd - cur) < (BitVec.ofNat 64 bytes).toNat) :
    bytes ≤ sEnd.toNat - cur.toNat := by
  unfold rtMaxObjBytes at hmax; c0_bv_omega

theorem bv64_align8_eq {n : Nat} (hn : n + 7 < 2 ^ 64) :
    (BitVec.ofNat 64 n + 7#64) &&& 18446744073709551608#64 = BitVec.ofNat 64 (align8 n) := by
  rw [show (BitVec.ofNat 64 n + 7#64) = (BitVec.ofNat 64 n + 7) from rfl,
    show (18446744073709551608#64 : BitVec 64) = 0xfffffffffffffff8#64 from by decide,
    bv64_and_mask8]
  unfold align8; congr 1; have := BitVec.toNat_add (BitVec.ofNat 64 n) 7; c0_bv_omega

theorem bv64_tag_eq (hdr : BitVec 64) {t : Nat} (_ht : t < 256) (h : (hdr >>> 56).toNat = t) :
    (hdr >>> BitVec.signExtend 64 56#32 == BitVec.ofNat 64 t) = true := by
  rw [show BitVec.signExtend 64 56#32 = 56#64 from by decide, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt (by omega : t < 2 ^ 64)] using h

theorem bv64_tag_ne (hdr : BitVec 64) {t : Nat} (ht : t < 256) (h : (hdr >>> 56).toNat ≠ t) :
    (hdr >>> BitVec.signExtend 64 56#32 == BitVec.ofNat 64 t) = false := by
  rw [show BitVec.signExtend 64 56#32 = 56#64 from by decide, beq_eq_false_iff_ne]; intro heq
  apply h
  have := congrArg BitVec.toNat heq
  simpa [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt (by omega : t < 2 ^ 64)] using this

theorem bv64_shr3_toNat (bytes : Nat) (hb : bytes < 2 ^ 64) :
    (BitVec.ofNat 64 bytes >>> 3#64).toNat = bytes / 8 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_natTag_eq (hdr : BitVec 64) {t : Nat} (ht : t < 256) (h : (hdr >>> 56).toNat = t) :
    decide (hdr >>> 56 = BitVec.ofNat 64 t) = true := by
  rw [decide_eq_true_iff]; apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem bv64_natTag_ne (hdr : BitVec 64) {t : Nat} (ht : t < 256) (h : (hdr >>> 56).toNat ≠ t) :
    decide (hdr >>> 56 = BitVec.ofNat 64 t) = false := by
  rw [decide_eq_false_iff_not]; intro heq; apply h
  have := congrArg BitVec.toNat heq; simpa [Nat.mod_eq_of_lt (by omega : t < 2 ^ 64)] using this

theorem bv64_mul8_comm (n : Nat) : BitVec.ofNat 64 n * 8#64 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]

theorem bv64_8_mul (n : Nat) : 8#64 * BitVec.ofNat 64 n = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem list_getD_set_self {α : Type} (xs : List α) {i : Nat} (v d : α)
    (hi : i < xs.length) : (xs.set i v).getD i d = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]

theorem list_getD_set_ne {α : Type} (xs : List α) {i j : Nat} (v d : α)
    (hne : j ≠ i) : (xs.set i v).getD j d = xs.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]

theorem list_take_set_append {α : Type _} (wb : List α) {len : Nat}
    (hlen : len < wb.length) (v : α) : (wb.set len v).take (len + 1) = wb.take len ++ [v] := by
  apply List.ext_getElem
  · simp; omega
  · intro j hj1 hj2
    have hlt : j < len + 1 := by
      have : j < min (len + 1) (wb.set len v).length := by simpa [List.length_take] using hj1
      omega
    by_cases hjl : j = len
    · subst hjl; rw [List.getElem_take, List.getElem_set_self]
      have hlenT : (wb.take j).length = j := List.length_take_of_le (by omega)
      rw [List.getElem_append_right (by omega)]; simp [hlenT]
    · have hjlt : j < len := by omega
      have hlenT : (wb.take len).length = len := List.length_take_of_le (by omega)
      rw [List.getElem_take, List.getElem_set_ne (Ne.symm hjl)]
      rw [List.getElem_append_left (by omega), List.getElem_take]

theorem cloMetaWord_nfix (a n : Nat) (ha : a < 65536) (hn : n < 65536) :
    ((cloMetaWord a n >>> 16) &&& 65535#64) = BitVec.ofNat 64 n := by
  unfold cloMetaWord; apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq
  intro i; have haM : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have hnM : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have h65 : (65535#64).toNat = 2 ^ 16 - 1 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, h65, haM, hnM, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < 16
  · have hlt64 : 16 + i < 64 := by omega
    have ha0 : a.testBit (16 + i) = false := Nat.testBit_lt_two_pow (by
      calc a < 2 ^ 16 := ha
        _ ≤ 2 ^ (16 + i) := Nat.pow_le_pow_right (by omega) (by omega))
    have hge : 16 ≤ 16 + i := by omega
    have hsub : 16 + i - 16 = i := by omega
    simp [hi, hlt64, ha0, Nat.testBit_shiftLeft, hge, hsub]
  · have hn0 : n.testBit i = false := Nat.testBit_lt_two_pow (by
      calc n < 2 ^ 16 := hn
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))
    simp [hi, hn0]

theorem preservesMeta_trans {a b c : RtC0State}
    (h1 : b.PreservesMeta a) (h2 : c.PreservesMeta b) : c.PreservesMeta a := by
  rcases h1 with ⟨h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  rcases h2 with ⟨h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

/-! ### `LcnfObj`, `lcnfHeap`, `SameNonRc`, Worklist, and DFS Helpers -/

theorem cell64_conflict (a v1 v2 : BitVec 64) (R1 R2 : Mem 64 → Prop) (m : Mem 64)
    (h : ((cell64 a v1 ⋆ R1) ⋆ (cell64 a v2 ⋆ R2)) m) : False := by
  have h1 : (cell64 a v1 ⋆ (R1 ⋆ (cell64 a v2 ⋆ R2))) m := sep_cast h (by ac_rfl)
  have h2 : (cell64 a v2 ⋆ (R2 ⋆ (cell64 a v1 ⋆ R1))) m := sep_cast h (by ac_rfl)
  have h12 : v1 = v2 := Option.some.inj ((loadVal_cell64 h1).symm.trans (loadVal_cell64 h2))
  have hst := (store_cell64 (v1 + 1#64) h1).2
  have hst2 : (cell64 a v2 ⋆ (R2 ⋆ (cell64 a (v1 + 1#64) ⋆ R1)))
      (storeMem m i64 a (v1 + 1#64)) := sep_cast hst (by ac_rfl)
  have hne : v1 + 1#64 = v2 :=
    Option.some.inj ((loadVal_cell64 hst).symm.trans (loadVal_cell64 hst2))
  subst h12; simp at hne

theorem lcnfObjMem_eq_header_body (o : LcnfObj) :
    lcnfObjMem o = (cell64 o.addr o.header ⋆ lcnfObjBody o) := by
  unfold lcnfObjMem lcnfObjBody
  split
  · ac_rfl
  · split
    · ac_rfl
    · split
      · ac_rfl
      · split
        · ac_rfl
        · split
          · ac_rfl
          · dsimp only; ac_rfl

theorem lcnfObjBody_withRc (o : LcnfObj) (rc' : BitVec 32) :
    lcnfObjBody (o.withRc rc') = lcnfObjBody o := by
  unfold lcnfObjBody LcnfObj.withRc LcnfObj.cloMeta LcnfObj.mpzMeta LcnfObj.totalBytes; rfl

theorem lcnfObjWf_withRc {o : LcnfObj} {rc' : BitVec 32}
    (h : o.Wf) (hrc : 0 ≤ rc'.toInt) : (o.withRc rc').Wf := by
  unfold LcnfObj.Wf LcnfObj.totalBytes at h ⊢; dsimp [LcnfObj.withRc] at *
  rcases h with ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, hrest⟩
  exact ⟨h1, h2, hrc, h4, h5, h6, h7, h8, h9, hrest⟩

theorem bv32_ofNat_and_hi_zero (rc : Nat) (hrc : rc < 2 ^ 32) (hi : BitVec 64)
    (hlo : (hi &&& 4294967295#64) = 0#64) : BitVec.ofNat 64 rc &&& hi = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi64; rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  by_cases hi32 : i < 32
  · have hget := congrArg (fun bv : BitVec 64 => bv.getLsbD i) hlo
    rw [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hget
    have hmask : (4294967295#64).getLsbD i = true := by
      rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 by decide,
        Nat.testBit_two_pow_sub_one]
      simp [hi64, hi32]
    rw [hmask, Bool.and_true] at hget; rw [hget, Bool.and_false]
  · have : (BitVec.ofNat 64 rc).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]; simp [hi64]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hrc (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [this, Bool.false_and]

theorem obj_hi_lo_zero (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256) :
    ((o.withRc 0#32).header &&& 4294967295#64) = 0#64 := by
  have hc : (o.withRc 0#32).header &&& 18446744069414584320#64 = (o.withRc 0#32).header := by
    simpa [LcnfObj.withRc] using LcnfObj.header_clear_rc (o.withRc 0#32) hcs hoth ht
  rw [← hc, BitVec.and_assoc]
  have hz : (18446744069414584320#64 &&& 4294967295#64) = 0#64 := by decide
  rw [hz, BitVec.and_zero]

theorem obj_header_eq_add (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256) :
    o.header = BitVec.ofNat 64 o.rc.toNat + (o.withRc 0#32).header := by
  have hlo := obj_hi_lo_zero o hcs hoth ht
  have hzero : BitVec.ofNat 64 o.rc.toNat &&& (o.withRc 0#32).header = 0#64 :=
    bv32_ofNat_and_hi_zero o.rc.toNat o.rc.isLt _ hlo
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hzero]; unfold LcnfObj.header LcnfObj.withRc
  dsimp; simp [BitVec.zero_or, BitVec.or_assoc]

theorem lcnfObjHeader_add1 (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256)
    (h0 : 0 ≤ o.rc.toInt) (hlt : o.rc.toInt < 2147483647) :
    o.header + 1#64 = (o.withRc (o.rc + 1#32)).header := by
  have hrc : o.rc.toNat < 2147483647 := by
    rw [BitVec.toInt_eq_toNat_cond] at h0 hlt; split at hlt <;> omega
  have hw1 : (o.withRc (o.rc + 1#32)).header =
      BitVec.ofNat 64 (o.rc + 1#32).toNat + (o.withRc 0#32).header := by
    simpa [LcnfObj.withRc] using obj_header_eq_add (o.withRc (o.rc + 1#32)) hcs hoth ht
  have hrc1 : BitVec.ofNat 64 (o.rc + 1#32).toNat = BitVec.ofNat 64 o.rc.toNat + 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [obj_header_eq_add o hcs hoth ht, hw1, hrc1]; ac_rfl

theorem lcnfObjHeader_sub1 (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256)
    (h0 : 0 ≤ o.rc.toInt) (hgt : 1 < o.rc.toNat) :
    o.header - 1#64 = (o.withRc (o.rc - 1#32)).header := by
  have hrc : o.rc.toNat < 2147483648 := by
    rw [BitVec.toInt_eq_toNat_cond] at h0; split at h0 <;> omega
  have hw1 : (o.withRc (o.rc - 1#32)).header =
      BitVec.ofNat 64 (o.rc - 1#32).toNat + (o.withRc 0#32).header := by
    dsimp only [LcnfObj.withRc]
    exact obj_header_eq_add (o.withRc (o.rc - 1#32)) hcs hoth ht
  have hrc1 : BitVec.ofNat 64 (o.rc - 1#32).toNat = BitVec.ofNat 64 o.rc.toNat - 1#64 := by
    c0_bv_omega
  rw [obj_header_eq_add o hcs hoth ht, hw1, hrc1]; bv_omega

theorem lcnfObjHeader_sub1_wf (o : LcnfObj) (hw : o.Wf) (hgt : 1 < o.rc.toNat) :
    o.header - 1#64 = (o.withRc (o.rc - 1#32)).header :=
  lcnfObjHeader_sub1 o hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2.1 hw.2.2.1 hgt

theorem lcnfHeap_addr_lt {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfHeap objs ⋆ R) m) {i j : Nat} (hij : i < j) (hj : j < objs.length) :
    objs[i].addr ≠ objs[j].addr := by
  intro heq; have hi : i < objs.length := Nat.lt_trans hij hj; rw [lcnfHeap_focus objs hi] at h
  have hj' : j - (i + 1) < (objs.drop (i + 1)).length := by rw [List.length_drop]; omega
  rw [lcnfHeap_focus (objs.drop (i + 1)) hj'] at h
  have hget : (objs.drop (i + 1))[j - (i + 1)] = objs[j] := by
    rw [List.getElem_drop]; congr 1; omega
  rw [hget, lcnfObjMem_eq_header_body objs[i], lcnfObjMem_eq_header_body objs[j]] at h
  have hcon :
      ((cell64 objs[i].addr objs[i].header ⋆ lcnfObjBody objs[i]) ⋆
        (cell64 objs[j].addr objs[j].header ⋆
          (lcnfObjBody objs[j] ⋆
            (lcnfHeap (objs.take i) ⋆
              (lcnfHeap ((objs.drop (i + 1)).take (j - (i + 1))) ⋆
                lcnfHeap ((objs.drop (i + 1)).drop (j - (i + 1) + 1))) ⋆ R)))) m :=
    sep_cast h (by ac_rfl)
  rw [heq] at hcon; exact cell64_conflict _ _ _ _ _ m hcon

theorem lcnfHeap_addr_ne {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfHeap objs ⋆ R) m) {i j : Nat} (hi : i < objs.length) (hj : j < objs.length)
    (hne : i ≠ j) : objs[i].addr ≠ objs[j].addr := by
  by_cases hij : i < j
  · exact lcnfHeap_addr_lt h hij hj
  · exact Ne.symm (lcnfHeap_addr_lt h (by omega) hi)

theorem lcnfHeapClosed_set_withRc {objs : List LcnfObj} (hCl : lcnfHeapClosed objs)
    {idx : Nat} (hidx : idx < objs.length) (rc' : BitVec 32) :
    lcnfHeapClosed (objs.set idx (objs[idx].withRc rc')) := by
  intro o ho f hf hf0; rw [List.mem_iff_getElem] at ho
  obtain ⟨k, hk, rfl⟩ := ho; have hk0 : k < objs.length := by rw [List.length_set] at hk; exact hk
  have hchild : (objs.set idx (objs[idx].withRc rc'))[k].childFields = objs[k].childFields := by
    by_cases hki : k = idx
    · subst hki; rw [List.getElem_set_self]; rfl
    · rw [List.getElem_set_ne (Ne.symm hki) (by simp [hk0])]
  rw [hchild] at hf; obtain ⟨o', ho', had'⟩ := hCl objs[k] (List.getElem_mem hk0) f hf hf0
  rw [List.mem_iff_getElem] at ho'; obtain ⟨k', hk', hk'eq⟩ := ho'
  have hk's : k' < (objs.set idx (objs[idx].withRc rc')).length := by
    rw [List.length_set]; exact hk'
  have had_k' : (objs.set idx (objs[idx].withRc rc'))[k'].addr = f := by
    by_cases hki : k' = idx
    · subst hki; rw [List.getElem_set_self]; simp [LcnfObj.withRc, hk'eq, had']
    · rw [List.getElem_set_ne (Ne.symm hki) (by simp [hk']), hk'eq, had']
  exact ⟨(objs.set idx (objs[idx].withRc rc'))[k'], List.getElem_mem hk's, had_k'⟩

theorem SameNonRc.refl (a : LcnfObj) : SameNonRc a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameNonRc.trans {a b c : LcnfObj} (h1 : SameNonRc a b) (h2 : SameNonRc b c) :
    SameNonRc a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2.2.2⟩

theorem SameNonRc.withRc_r {a b : LcnfObj} (h : SameNonRc a b) (_rc' : BitVec 32) :
    SameNonRc a (b.withRc _rc') := h

theorem SameNonRc.childFields_eq {a b : LcnfObj} (h : SameNonRc a b) :
    b.childFields = a.childFields := by
  unfold LcnfObj.childFields; rw [h.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1]

theorem objWf_childFields_lt {o : LcnfObj} (hwf : o.Wf) : o.childFields.length < 2 ^ 64 := by
  unfold LcnfObj.childFields; rcases hwf with ⟨_, _, _, _, _, _, _, _, _, hsp⟩
  by_cases hc : o.tag = closureTag
  · simp only [hc, true_or, or_true, ↓reduceIte] at hsp ⊢; have := hsp.2.1; omega
  · by_cases ha : o.tag = arrayTag
    · simp only [ha, show arrayTag ≠ closureTag by decide, or_true, ↓reduceIte] at hsp ⊢
      have := hsp.1; have := hsp.2; omega
    · by_cases hsa : o.tag = sarrayTag
      · simp [hsa, closureTag, arrayTag, sarrayTag]
      · by_cases hstr : o.tag = stringTag
        · simp [hstr, closureTag, arrayTag, stringTag]
        · by_cases hmpz : o.tag = mpzTag
          · simp [hmpz, closureTag, arrayTag, mpzTag]
          · simp only [hc, ha, hsa, hstr, hmpz, ↓reduceIte] at hsp
            have h1 := hsp.1; have h2 := hsp.2.1; simp only [h1, true_or, ↓reduceIte]; omega

theorem objWf_addr_even {o : LcnfObj} (hwf : o.Wf) : (o.addr &&& 1#64) = 0#64 := by
  have hal := hwf.2.1; c0_bv_omega

theorem objWf_rc_pos {o : LcnfObj} (hwf : o.Wf) (hnz : o.rc ≠ 0#32) : 0 < o.rc.toInt := by
  have hnn := hwf.2.2.1; rw [BitVec.toInt_eq_toNat_cond] at hnn ⊢
  have hne0 : o.rc.toNat ≠ 0 := fun hz => hnz (BitVec.eq_of_toNat_eq hz)
  split at hnn <;> simp_all <;> omega

theorem objWf_rc_lt {o : LcnfObj} (hwf : o.Wf) : o.rc.toNat < 2147483648 := by
  have hnn := hwf.2.2.1; rw [BitVec.toInt_eq_toNat_cond] at hnn
  split at hnn <;> omega

theorem objWf_withRc_zero {o : LcnfObj} (hwf : o.Wf) : (o.withRc 0#32).Wf :=
  lcnfObjWf_withRc hwf (by decide)

theorem objWf_rc_sub1_toInt {o : LcnfObj} (hwf : o.Wf) (hgt : 1 < o.rc.toNat) :
    (o.rc - 1#32).toInt = o.rc.toInt - 1 := by
  have hlt := objWf_rc_lt hwf; rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have hsub : (o.rc - 1#32).toNat = o.rc.toNat - 1 := by bv_omega
  rw [hsub]
  split <;> split <;> omega

theorem objRc_sub1_toNat {o : LcnfObj} (hgt : 1 < o.rc.toNat) :
    (o.rc - 1#32).toNat = o.rc.toNat - 1 := by
  bv_omega

theorem lcnfObjMem_load_header {o : LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ F) m) : loadVal m i64 o.addr = some o.header := by
  rw [lcnfObjMem_eq_header_body] at hm
  exact loadVal_cell64 (show (cell64 o.addr o.header ⋆ (lcnfObjBody o ⋆ F)) m from
    sep_cast hm (by ac_rfl))

theorem lcnfObjMem_load_cloMeta {o : LcnfObj} (ht : o.tag = closureTag)
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + 16#64) = some o.cloMeta := by
  unfold lcnfObjMem at hm; rw [ite_eq_left ht] at hm
  exact loadVal_cell64 (show (cell64 (o.addr + 16#64) o.cloMeta ⋆ _) m by c0_frame)

theorem lcnfObjMem_load_arrSize {o : LcnfObj} (ht : o.tag = arrayTag)
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.fields.length) := by
  unfold lcnfObjMem at hm; rw [ite_eq_right (by rw [ht]; decide), ite_eq_left ht] at hm
  exact loadVal_cell64 (show (cell64 (o.addr + 8#64) _ ⋆ _) m by c0_frame)

theorem lcnfObjMem_load_child {o : LcnfObj} (_hwf : o.Wf) {F : Mem 64 → Prop}
    {m : Mem 64} (hm : (lcnfObjMem o ⋆ F) m) {i : Nat} (hi : i < o.childFields.length) :
    loadVal m i64 ((o.addr + objFieldsOff o) + BitVec.ofNat 64 (8 * i)) =
    some (o.childFields[i]'hi) := by
  unfold lcnfObjMem at hm; unfold objFieldsOff; unfold LcnfObj.childFields at hi ⊢
  by_cases hc : o.tag = closureTag
  · simp only [hc, ↓reduceIte, true_or, or_true] at hm hi ⊢
    exact loadVal_array64 hi (show (array64 (o.addr + 24#64) o.fields ⋆ _) m by c0_frame)
  · by_cases ha : o.tag = arrayTag
    · simp only [ha, show arrayTag ≠ closureTag by decide, ↓reduceIte, or_true] at hm hi ⊢
      exact loadVal_array64 hi (show (array64 (o.addr + 24#64) o.fields ⋆ _) m by c0_frame)
    · by_cases hle : o.tag ≤ 244
      · have hsa : o.tag ≠ sarrayTag := by unfold sarrayTag; omega
        have hstr : o.tag ≠ stringTag := by unfold stringTag; omega
        have hmpz : o.tag ≠ mpzTag := by unfold mpzTag; omega
        simp only [hc, ha, hsa, hstr, hmpz, hle, true_or, or_self, ↓reduceIte] at hm hi ⊢
        exact loadVal_array64 hi (show (array64 (o.addr + 8#64) o.fields ⋆ _) m by c0_frame)
      · simp only [hc, ha, hle, or_self, ↓reduceIte] at hi; simp at hi

theorem lcnfObjMem_store_rc {o : LcnfObj} (rc' : BitVec 32) {F : Mem 64 → Prop}
    {m : Mem 64} (hm : (lcnfObjMem o ⋆ F) m) : storeOk m i64 o.addr ∧
    (lcnfObjMem (o.withRc rc') ⋆ F) (storeMem m i64 o.addr (o.withRc rc').header) := by
  rw [lcnfObjMem_eq_header_body] at hm
  have h1 := store_cell64 (o.withRc rc').header
    (show (cell64 o.addr o.header ⋆ (lcnfObjBody o ⋆ F)) m from sep_cast hm (by ac_rfl))
  refine ⟨h1.1, ?_⟩
  rw [lcnfObjMem_eq_header_body, lcnfObjBody_withRc]; exact sep_cast h1.2 (by ac_rfl)

theorem lcnfHeap_load_header {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfHeap objs ⋆ F) m) :
    loadVal m i64 objs[idx].addr = some objs[idx].header := by
  rw [lcnfHeap_focus objs hidx] at hm
  exact lcnfObjMem_load_header (show (lcnfObjMem objs[idx] ⋆ _) m by c0_frame)

theorem lcnfHeap_load_cloMeta {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    (ht : objs[idx].tag = closureTag) {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfHeap objs ⋆ F) m) :
    loadVal m i64 (objs[idx].addr + 16#64) = some objs[idx].cloMeta := by
  rw [lcnfHeap_focus objs hidx] at hm
  exact lcnfObjMem_load_cloMeta ht (show (lcnfObjMem objs[idx] ⋆ _) m by c0_frame)

theorem lcnfHeap_load_arrSize {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    (ht : objs[idx].tag = arrayTag) {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfHeap objs ⋆ F) m) :
    loadVal m i64 (objs[idx].addr + 8#64) = some (BitVec.ofNat 64 objs[idx].fields.length) := by
  rw [lcnfHeap_focus objs hidx] at hm
  exact lcnfObjMem_load_arrSize ht (show (lcnfObjMem objs[idx] ⋆ _) m by c0_frame)

theorem lcnfHeap_load_child {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    (hwf : objs[idx].Wf) {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfHeap objs ⋆ F) m)
    {i : Nat} (hi : i < objs[idx].childFields.length) :
    loadVal m i64 ((objs[idx].addr + objFieldsOff objs[idx]) + BitVec.ofNat 64 (8 * i)) =
    some (objs[idx].childFields[i]'hi) := by
  rw [lcnfHeap_focus objs hidx] at hm
  exact lcnfObjMem_load_child hwf (show (lcnfObjMem objs[idx] ⋆ _) m by c0_frame) hi

theorem lcnfHeap_store_rc {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    (rc' : BitVec 32) {F : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfHeap objs ⋆ F) m) :
    storeOk m i64 objs[idx].addr ∧ (lcnfHeap (objs.set idx (objs[idx].withRc rc')) ⋆ F)
    (storeMem m i64 objs[idx].addr (objs[idx].withRc rc').header) := by
  rw [lcnfHeap_focus objs hidx] at hm
  have h1 := lcnfObjMem_store_rc rc' (show
    (lcnfObjMem objs[idx] ⋆ ((lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆ F)) m
    from sep_cast hm (by ac_rfl))
  refine ⟨h1.1, ?_⟩
  rw [lcnfHeap_set objs hidx]; exact sep_cast h1.2 (by ac_rfl)

theorem nodup_getElem_inj {α : Type _} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (heq : xs[i] = xs[j]) : i = j := by
  have hp := List.pairwise_iff_getElem.mp hnd
  by_cases hlt : i < j
  · exact absurd heq (hp i j hi hj hlt)
  · by_cases hgt : j < i
    · exact absurd heq.symm (hp j i hj hi hgt)
    · omega

theorem lcnfHeap_nodup_addrs {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfHeap objs ⋆ R) m) : (objs.map LcnfObj.addr).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]; intro i j hi hj hij
  simp only [List.length_map] at hi hj; simp only [List.getElem_map]
  exact lcnfHeap_addr_lt h hij hj

theorem nodup_addr_eq_of_mem {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {a b : LcnfObj} (ha : a ∈ objs) (hb : b ∈ objs) (heq : a.addr = b.addr) : a = b := by
  rw [List.mem_iff_getElem] at ha hb; obtain ⟨i, hi, rfl⟩ := ha; obtain ⟨j, hj, rfl⟩ := hb
  have hij : i = j :=
    nodup_getElem_inj hnd (by simpa using hi) (by simpa using hj) (by simpa using heq)
  subst hij; rfl

theorem nodup_addr_idx_eq {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {i j : Nat} (hi : i < objs.length) (hj : j < objs.length)
    (heq : objs[i].addr = objs[j].addr) : i = j :=
  nodup_getElem_inj hnd (by simpa using hi) (by simpa using hj) (by simpa using heq)

theorem nodup_length_le_of_subset {α : Type _} [DecidableEq α] :
    ∀ (xs ys : List α), xs.Nodup → (∀ a ∈ xs, a ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    rw [List.nodup_cons] at hnd; have hxMem : x ∈ ys := hsub x List.mem_cons_self
    rw [List.mem_iff_getElem] at hxMem; obtain ⟨idx, hidx, hxEq⟩ := hxMem
    have hsub' : ∀ a ∈ xs, a ∈ ys.eraseIdx idx := by
      intro a ha; have hne : a ≠ x := fun h => hnd.1 (h ▸ ha)
      have haMem : a ∈ ys := hsub a (List.mem_cons_of_mem _ ha)
      rw [List.mem_iff_getElem] at haMem; obtain ⟨j, hj, rfl⟩ := haMem
      have hji : j ≠ idx := fun h => hne (by subst h; exact hxEq)
      rw [List.eraseIdx_eq_take_drop_succ, List.mem_append]
      by_cases hlt : j < idx
      · left; rw [List.mem_iff_getElem]
        exact ⟨j, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
      · right; rw [List.mem_iff_getElem]
        exact ⟨j - (idx + 1), by rw [List.length_drop]; omega,
          by rw [List.getElem_drop]; congr 1; omega⟩
    have ih := nodup_length_le_of_subset xs (ys.eraseIdx idx) hnd.2 hsub'
    rw [List.length_eraseIdx_of_lt hidx] at ih; simp only [List.length_cons]; omega

theorem nodup_addr_length_le {xs : List (BitVec 64)} {objs : List LcnfObj}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, ∃ o ∈ objs, o.addr = a) : xs.length ≤ objs.length := by
  have h1 := nodup_length_le_of_subset xs (objs.map LcnfObj.addr) hnd fun a ha => by
    obtain ⟨o, ho, rfl⟩ := hsub a ha; exact List.mem_map_of_mem ho
  simpa using h1

theorem work_push_lt_cap {wl : List (BitVec 64)} {xAddr c : BitVec 64}
    {curObjs : List LcnfObj} {cap : Nat}
    (hnd : wl.Nodup) (hxNot : xAddr ∉ wl) (hcNot : c ∉ wl) (hne : c ≠ xAddr)
    (hxMem : ∃ o ∈ curObjs, o.addr = xAddr) (hcMem : ∃ o ∈ curObjs, o.addr = c)
    (hwlMem : ∀ a ∈ wl, ∃ o ∈ curObjs, o.addr = a) (hcap : curObjs.length ≤ cap) :
    wl.length < cap := by
  have hnd2 : (c :: xAddr :: wl).Nodup := by
    rw [List.nodup_cons, List.nodup_cons]
    exact ⟨fun h => by rcases List.mem_cons.mp h with rfl | h' <;> contradiction, hxNot, hnd⟩
  have hsub : ∀ a ∈ c :: xAddr :: wl, ∃ o ∈ curObjs, o.addr = a := by
    intro a ha; rcases List.mem_cons.mp ha with rfl | ha'
    · exact hcMem
    · rcases List.mem_cons.mp ha' with rfl | ha''
      · exact hxMem
      · exact hwlMem a ha''
  have hle := nodup_addr_length_le hnd2 hsub; simp only [List.length_cons] at hle; omega

theorem unmarkedCount_set_zero : ∀ (objs : List LcnfObj) {idx : Nat} (hidx : idx < objs.length),
    objs[idx].rc ≠ 0#32 →
    unmarkedCount (objs.set idx (objs[idx].withRc 0#32)) + 1 = unmarkedCount objs
  | [], _, hi, _ => by simp at hi
  | o :: os, 0, _, hnz => by
    simp only [List.set_cons_zero, List.getElem_cons_zero] at hnz ⊢; unfold unmarkedCount
    have h1 : (o.rc != 0#32) = true := bne_iff_ne.mpr hnz
    have h2 : ((o.withRc 0#32).rc != 0#32) = false := by simp [LcnfObj.withRc]
    simp [h1, h2]
  | o :: os, idx + 1, hi, hnz => by
    simp only [List.set_cons_succ, List.getElem_cons_succ] at hnz ⊢
    have ih := unmarkedCount_set_zero os (by simp at hi; omega) hnz; unfold unmarkedCount at ih ⊢
    by_cases h : (o.rc != 0#32) = true
    · simp only [List.filter_cons, h, ↓reduceIte, List.length_cons]; omega
    · have hf : (o.rc != 0#32) = false := Bool.eq_false_iff.mpr h
      simp only [List.filter_cons, hf, Bool.false_eq_true, ↓reduceIte]; exact ih

theorem nonPersistRefs_foldl_shift (objs : List LcnfObj) (a : BitVec 64) (init : Nat) :
    objs.foldl (fun acc p => if p.rc = 0#32 then acc else acc + p.childFields.count a) init =
    init + nonPersistRefs objs a := by
  unfold nonPersistRefs
  induction objs generalizing init with
  | nil => simp
  | cons o os ih =>
    simp only [List.foldl_cons]
    by_cases h0 : o.rc = 0#32
    · simp only [h0, ↓reduceIte]; exact ih init
    · simp only [h0, ↓reduceIte]
      rw [ih (init + o.childFields.count a), ih (0 + o.childFields.count a)]; omega

theorem nonPersistRefs_cons (o : LcnfObj) (os : List LcnfObj) (a : BitVec 64) :
    nonPersistRefs (o :: os) a =
    (if o.rc = 0#32 then 0 else o.childFields.count a) + nonPersistRefs os a := by
  unfold nonPersistRefs; simp only [List.foldl_cons]
  split
  · simp
  · rw [nonPersistRefs_foldl_shift]
    change 0 + o.childFields.count a + nonPersistRefs os a = _ + nonPersistRefs os a; omega

theorem nonPersistRefs_append (xs ys : List LcnfObj) (a : BitVec 64) :
    nonPersistRefs (xs ++ ys) a = nonPersistRefs xs a + nonPersistRefs ys a := by
  induction xs with
  | nil => simp [nonPersistRefs]
  | cons x xs ih => simp only [List.cons_append, nonPersistRefs_cons, ih]; omega

theorem nonPersistRefs_focus (objs : List LcnfObj) {idx : Nat} (hidx : idx < objs.length)
    (a : BitVec 64) : nonPersistRefs objs a =
    (if objs[idx].rc = 0#32 then 0 else objs[idx].childFields.count a) +
    nonPersistRefs (objs.eraseIdx idx) a := by
  have hsp : objs = objs.take idx ++ objs[idx] :: objs.drop (idx + 1) := by
    have h1 := List.take_append_drop idx objs
    have h2 : objs.drop idx = objs[idx] :: objs.drop (idx + 1) := List.drop_eq_getElem_cons hidx
    rw [h2] at h1; exact h1.symm
  conv => lhs; rw [hsp]
  rw [nonPersistRefs_append, nonPersistRefs_cons, List.eraseIdx_eq_take_drop_succ,
    nonPersistRefs_append]
  omega

theorem nonPersistRefs_set_same_nz (objs : List LcnfObj) {idx : Nat}
    (hidx : idx < objs.length) {rc' : BitVec 32} (h1 : objs[idx].rc ≠ 0#32) (h2 : rc' ≠ 0#32)
    (a : BitVec 64) :
    nonPersistRefs (objs.set idx (objs[idx].withRc rc')) a = nonPersistRefs objs a := by
  have hsp1 := nonPersistRefs_focus objs hidx a
  have hidx' : idx < (objs.set idx (objs[idx].withRc rc')).length := by simp [hidx]
  have hsp2 := nonPersistRefs_focus (objs.set idx (objs[idx].withRc rc')) hidx' a
  have her : (objs.set idx (objs[idx].withRc rc')).eraseIdx idx = objs.eraseIdx idx := by
    rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ]; congr 1
    · apply List.ext_getElem
      · simp
      · intro j hj1 _
        have hlt : j < idx := by
          have : j < min idx (objs.set idx (objs[idx].withRc rc')).length := by
            simpa [List.length_take] using hj1
          omega
        simp [List.getElem_take, List.getElem_set_ne (by omega : idx ≠ j)]
    · apply List.ext_getElem
      · simp
      · intro j _ _
        simp only [List.getElem_drop, List.getElem_set_ne (by omega : idx ≠ idx + 1 + j)]
  rw [hsp1, hsp2, her, List.getElem_set_self]
  simp only [LcnfObj.withRc, LcnfObj.childFields, h1, h2, ↓reduceIte]; rfl

theorem nonPersistRefs_eq_zero_imp (objs : List LcnfObj) (a : BitVec 64)
    (h0 : nonPersistRefs objs a = 0) : ∀ p ∈ objs, p.rc ≠ 0#32 → a ∉ p.childFields := by
  induction objs with
  | nil => intro p hp; nomatch hp
  | cons x xs ih =>
    rw [nonPersistRefs_cons] at h0; intro p hp hnz; rcases List.mem_cons.mp hp with rfl | hmem
    · simp only [hnz, ↓reduceIte] at h0
      intro hmemC; have hpos : 0 < List.count a p.childFields := List.count_pos_iff.mpr hmemC
      omega
    · exact ih (by omega) p hmem hnz

theorem nonPersistRefs_filter_step :
    ∀ (xs : List LcnfObj) (p q : BitVec 64 → Bool) (xAddr : BitVec 64)
    (xFields : List (BitVec 64)), (xs.map LcnfObj.addr).Nodup → (∀ a, a ≠ xAddr → p a = q a) →
    p xAddr = false → q xAddr = true →
    (∃ ox ∈ xs, ox.addr = xAddr ∧ ox.rc ≠ 0#32 ∧ ox.childFields = xFields) →
    ∀ y, nonPersistRefs (xs.filter (fun o => q o.addr)) y =
    nonPersistRefs (xs.filter (fun o => p o.addr)) y + xFields.count y
  | [], _, _, _, _, _, _, _, _, ⟨_, h, _⟩, _ => nomatch h
  | o :: os, p, q, xAddr, xFields, hnd, hagree, hp0, hq1, hex, y => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases ho : o.addr = xAddr
    · obtain ⟨ox, hoxMem, hoxAddr, hoxNz, hoxF⟩ := hex
      have hoxEq : ox = o := by
        rcases List.mem_cons.mp hoxMem with rfl | htl
        · rfl
        · exfalso; exact hnd.1 (ho ▸ hoxAddr ▸ List.mem_map_of_mem htl)
      subst hoxEq
      have htlEq : os.filter (fun z => q z.addr) = os.filter (fun z => p z.addr) := by
        refine List.filter_congr fun z hz => ?_
        have hne : z.addr ≠ xAddr := fun h => hnd.1 (ho ▸ h ▸ List.mem_map_of_mem hz)
        exact (hagree z.addr hne).symm
      simp only [List.filter_cons, ho, hp0, hq1, Bool.false_eq_true, ↓reduceIte, htlEq,
        nonPersistRefs_cons, hoxNz, hoxF]
      omega
    · obtain ⟨ox, hoxMem, hoxAddr, hoxNz, hoxF⟩ := hex
      have hoxTl : ox ∈ os := by
        rcases List.mem_cons.mp hoxMem with rfl | htl
        · exact absurd hoxAddr ho
        · exact htl
      have ih := nonPersistRefs_filter_step os p q xAddr xFields hnd.2 hagree hp0 hq1
        ⟨ox, hoxTl, hoxAddr, hoxNz, hoxF⟩ y
      have hpq : q o.addr = p o.addr := (hagree o.addr ho).symm; simp only [List.filter_cons, hpq]
      cases p o.addr
      · simpa using ih
      · simp only [↓reduceIte, nonPersistRefs_cons, ih]; omega

theorem freedObjs_self (objs : List LcnfObj) : freedObjs objs objs = [] := by
  unfold freedObjs; rw [List.filter_eq_nil_iff]; intro o ho; simp [List.mem_map_of_mem ho]

theorem freedObjs_set_rc (objs curObjs : List LcnfObj) {idx : Nat}
    (hidx : idx < curObjs.length) (rc' : BitVec 32) :
    freedObjs objs (curObjs.set idx (curObjs[idx].withRc rc')) = freedObjs objs curObjs := by
  unfold freedObjs
  have hmap : (curObjs.set idx (curObjs[idx].withRc rc')).map LcnfObj.addr =
      curObjs.map LcnfObj.addr := by
    apply List.ext_getElem
    · simp
    · intro j _ _; simp only [List.getElem_map]
      by_cases hji : j = idx
      · subst hji; simp [LcnfObj.withRc]
      · simp [List.getElem_set_ne (Ne.symm hji)]
  rw [hmap]

theorem map_addr_eraseIdx_mem {curObjs : List LcnfObj}
    (hnd : (curObjs.map LcnfObj.addr).Nodup) {idx : Nat} (hidx : idx < curObjs.length)
    (a : BitVec 64) : (a ∈ (curObjs.eraseIdx idx).map LcnfObj.addr) ↔
    (a ∈ curObjs.map LcnfObj.addr ∧ a ≠ curObjs[idx].addr) := by
  constructor
  · intro hm; rw [List.mem_map] at hm; obtain ⟨o, ho, rfl⟩ := hm
    have ho' : o ∈ curObjs := List.mem_of_mem_eraseIdx ho
    refine ⟨List.mem_map_of_mem ho', ?_⟩
    intro heq; have hsp := List.eraseIdx_eq_take_drop_succ (l := curObjs) (i := idx)
    rw [hsp, List.mem_append] at ho; rcases ho with ht | hd
    · rw [List.mem_iff_getElem] at ht; obtain ⟨j, hj, rfl⟩ := ht
      have hlt : j < idx := by
        have : j < min idx curObjs.length := by simpa [List.length_take] using hj
        omega
      rw [List.getElem_take] at heq; have : j = idx := nodup_addr_idx_eq hnd (by omega) hidx heq
      omega
    · rw [List.mem_iff_getElem] at hd; obtain ⟨j, hj, rfl⟩ := hd; rw [List.getElem_drop] at heq
      have hj' : idx + 1 + j < curObjs.length := by simp [List.length_drop] at hj; omega
      have : idx + 1 + j = idx := nodup_addr_idx_eq hnd hj' hidx heq; omega
  · intro ⟨hm, hne⟩; rw [List.mem_map] at hm; obtain ⟨o, ho, rfl⟩ := hm
    rw [List.mem_iff_getElem] at ho; obtain ⟨j, hj, rfl⟩ := ho
    have hji : j ≠ idx := fun h => hne (by subst h; rfl); rw [List.mem_map]
    refine ⟨curObjs[j], ?_, rfl⟩
    rw [List.eraseIdx_eq_take_drop_succ, List.mem_append]
    by_cases hlt : j < idx
    · left; rw [List.mem_iff_getElem]
      exact ⟨j, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
    · right; rw [List.mem_iff_getElem]
      exact ⟨j - (idx + 1), by rw [List.length_drop]; omega,
        by rw [List.getElem_drop]; congr 1; omega⟩

theorem nonPersistRefs_freedObjs_eraseIdx {objs curObjs : List LcnfObj}
    (hndO : (objs.map LcnfObj.addr).Nodup) (hndC : (curObjs.map LcnfObj.addr).Nodup)
    {idx : Nat} (hidx : idx < curObjs.length)
    (horig : ∃ ox ∈ objs, ox.addr = curObjs[idx].addr ∧ ox.rc ≠ 0#32 ∧
    ox.childFields = curObjs[idx].childFields) (y : BitVec 64) :
    nonPersistRefs (freedObjs objs (curObjs.eraseIdx idx)) y =
    nonPersistRefs (freedObjs objs curObjs) y + curObjs[idx].childFields.count y := by
  unfold freedObjs
  refine nonPersistRefs_filter_step objs
    (fun a => !(curObjs.map LcnfObj.addr).contains a)
    (fun a => !((curObjs.eraseIdx idx).map LcnfObj.addr).contains a)
    curObjs[idx].addr curObjs[idx].childFields hndO ?_ ?_ ?_ horig y
  · intro a hne; have hiff := map_addr_eraseIdx_mem hndC hidx a
    by_cases hm : a ∈ curObjs.map LcnfObj.addr
    · have hm' : a ∈ (curObjs.eraseIdx idx).map LcnfObj.addr := hiff.mpr ⟨hm, hne⟩; simp [hm, hm']
    · have hm' : a ∉ (curObjs.eraseIdx idx).map LcnfObj.addr := fun h => hm (hiff.mp h).1
      simp [hm, hm']
  · have hm : curObjs[idx].addr ∈ curObjs.map LcnfObj.addr :=
      List.mem_map_of_mem (List.getElem_mem hidx)
    simp [hm]
  · have hm' : curObjs[idx].addr ∉ (curObjs.eraseIdx idx).map LcnfObj.addr := by
      intro h; exact (map_addr_eraseIdx_mem hndC hidx _).mp h |>.2 rfl
    simp [hm']

theorem nonPersistReach_root_nz {objs : List LcnfObj} {root a : BitVec 64}
    (h : NonPersistReach objs root a) : ∃ o' ∈ objs, o'.addr = root ∧ o'.rc ≠ 0#32 := by
  induction h with
  | refl h0 => exact h0
  | step _ _ _ _ ih => exact ih

theorem nonPersistReach_mark_complete {objs curObjs : List LcnfObj} {root : BitVec 64}
    (hlen : curObjs.length = objs.length) (hnd : (objs.map LcnfObj.addr).Nodup)
    (hroot : ∀ k (hk : k < objs.length) (hk' : k < curObjs.length),
    objs[k].addr = root → curObjs[k].rc = 0#32)
    (haddr : ∀ k (hk : k < objs.length) (hk' : k < curObjs.length), SameNonRc objs[k] curObjs[k])
    (hstep : ∀ k (hk : k < objs.length) (hk' : k < curObjs.length),
    objs[k].rc ≠ 0#32 → curObjs[k].rc = 0#32 → ∀ f ∈ curObjs[k].childFields, (f &&& 1#64) = 0#64 →
    ∃ q ∈ curObjs, q.addr = f ∧ q.rc = 0#32)
    {a : BitVec 64} (hreach : NonPersistReach objs root a) :
    ∃ k, ∃ _hk : k < curObjs.length, curObjs[k].addr = a ∧ curObjs[k].rc = 0#32 := by
  induction hreach with
  | refl h =>
    obtain ⟨obj, hmem, rfl, _⟩ := h; rw [List.mem_iff_getElem] at hmem
    obtain ⟨k, hk, rfl⟩ := hmem; have hk' : k < curObjs.length := by omega
    exact ⟨k, hk', (haddr k hk hk').1, hroot k hk hk' rfl⟩
  | @step u v _ hchild hv0 _ ih =>
    obtain ⟨ku, hku', hkuAddr, hkuRc⟩ := ih; have hku : ku < objs.length := by omega
    obtain ⟨ou, houMem, houAddr, hvIn⟩ := hchild
    have houEq' : ou = objs[ku] := by
      refine nodup_addr_eq_of_mem hnd houMem (List.getElem_mem hku) ?_
      rw [houAddr, ← hkuAddr, (haddr ku hku hku').1]
    subst houEq'
    have hkuOrigNz : objs[ku].rc ≠ 0#32 := by
      obtain ⟨o0, ho0, ho0Addr, hnz0⟩ : ∃ o ∈ objs, o.addr = u ∧ o.rc ≠ 0#32 := by
        cases ‹NonPersistReach objs root u› with
        | refl h => exact h
        | step _ _ _ h' => exact h'
      have := nodup_addr_eq_of_mem hnd ho0 (List.getElem_mem hku)
        (by rw [ho0Addr, ← hkuAddr, (haddr ku hku hku').1])
      rwa [← this]
    have hvInCur : v ∈ curObjs[ku].childFields := by
      rw [(haddr ku hku hku').childFields_eq]; exact hvIn
    obtain ⟨q, hqMem, hqAddr, hqRc⟩ := hstep ku hku hku' hkuOrigNz hkuRc v hvInCur hv0
    rw [List.mem_iff_getElem] at hqMem; obtain ⟨kv, hkv', rfl⟩ := hqMem
    exact ⟨kv, hkv', hqAddr, hqRc⟩

end RtProof

end LeanQbe.T.LeanLCNF
