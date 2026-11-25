module

public import LeanQbe.T.LeanLCNF.LcnfC0ContainersSpec
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Containers`, Part 1: Memory Lemmas, RC Ownership & Core Helpers

Provides:
1. `@[c0_load]` / `@[c0_store]` lemmas for `cell64`, `array64`, `bytes`, and `LcnfC0Rt.At`
   (`s_ba_empty`), plus `bytes_append`, `region_pop_store_byte`, and `LcnfObj` focus/update lemmas.
2. `lcnfHeap_nodup_addrs`, `nonPersistRefs` algebra, `incChildrenObjs` lemmas, and
   `HandlesRcSound` COW exclusivity & update preservation theorems.
3. `Func.wp` proofs against `rtR2Env` for `r2_inc_obj`, `r2_dec_obj`, `r2_mem_copy_bytes`,
   `r2_cmp_byte_slices`, and `lcnf_oob`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

scoped macro "r2_steps" : tactic =>
  `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_steps))

scoped macro "r2_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_))

/-! ## 1. BitVec, Pointer, and C0 Load/Store Helpers -/

theorem ptr_add_nat_r2 (a : BitVec 64) (m n : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bv64_and1_zero_of_mod8 {p : BitVec 64} (h : p.toNat % 8 = 0) :
    (p &&& 1#64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (p.toNat &&& (2 ^ 1 - 1)) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.pow_one]
  omega

theorem r2_bv64_mul8_eq_ofNat (i : BitVec 64) : i * 8#64 = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem bv64_8mul_eq_ofNat (i : BitVec 64) : 8#64 * i = BitVec.ofNat 64 (8 * i.toNat) := by
  rw [BitVec.mul_comm, r2_bv64_mul8_eq_ofNat]

theorem bv64_setWidth8_ofNat (n : Nat) :
    ((BitVec.ofNat 64 n).setWidth 8).toNat = n % 256 := by
  simp

theorem uint8_ofNat_setWidth8 (v : BitVec 64) :
    UInt8.ofNat (v.setWidth 8).toNat = UInt8.ofNat v.toNat := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

@[c0_load] theorem r2_c0_load_cell64 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 a v ⋆ R) m) : loadVal m i64 a = some v :=
  loadVal_cell64 h

@[c0_store] theorem r2_c0_store_cell64 {a v0 : BitVec 64} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (cell64 a v0 ⋆ R) m) :
    storeOk m i64 a ∧ (cell64 a v ⋆ R) (storeMem m i64 a v) :=
  store_cell64 v h

@[c0_load] theorem r2_c0_load_cell64_add8 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 8#64) v ⋆ R) m) : loadVal m i64 (a + 8#64) = some v :=
  loadVal_cell64 h

@[c0_store] theorem r2_c0_store_cell64_add8 {a v0 : BitVec 64} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (cell64 (a + 8#64) v0 ⋆ R) m) :
    storeOk m i64 (a + 8#64) ∧ (cell64 (a + 8#64) v ⋆ R) (storeMem m i64 (a + 8#64) v) :=
  store_cell64 v h

@[c0_load] theorem r2_c0_load_cell64_add16 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 16#64) v ⋆ R) m) : loadVal m i64 (a + 16#64) = some v :=
  loadVal_cell64 h

@[c0_store] theorem r2_c0_store_cell64_add16 {a v0 : BitVec 64} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (cell64 (a + 16#64) v0 ⋆ R) m) :
    storeOk m i64 (a + 16#64) ∧ (cell64 (a + 16#64) v ⋆ R) (storeMem m i64 (a + 16#64) v) :=
  store_cell64 v h

@[c0_load] theorem r2_c0_load_array64_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 8#64 * i) = some (xs[i.toNat]'hi) := by
  rw [BitVec.mul_comm 8#64 i]
  exact c0_load_array64 h hi

@[c0_store] theorem r2_c0_store_array64_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + 8#64 * i) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + 8#64 * i) v) := by
  rw [BitVec.mul_comm 8#64 i]
  exact c0_store_array64 v h hi

@[c0_load] theorem r2_c0_load_array64_add24_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 24#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 24#64 + 8#64 * i) = some (xs[i.toNat]'hi) :=
  r2_c0_load_array64_mul8 h hi

@[c0_store] theorem r2_c0_store_array64_add24_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (a + 24#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + 24#64 + 8#64 * i) ∧
      (array64 (a + 24#64) (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + 24#64 + 8#64 * i) v) :=
  r2_c0_store_array64_mul8 v h hi

/-! ## 2. `bytes` & `region` Byte-Granularity Helpers -/

theorem bytes_nil_eq (a : BitVec 64) : bytes a [] = emp :=
  (eq_nil_At a).symm

private theorem intToBytes_1_bv8 (v : BitVec 8) :
    Int.toBytes 1 (BitVec.setWidth (8 * i8.bytes) (toBits i8 v)).toInt =
      [UInt8.ofNat v.toNat] := by
  have hbits : (BitVec.setWidth (8 * i8.bytes) (toBits i8 v)).toInt = v.toInt := rfl
  have h1 : v.toInt.take (8 * 1) = ((UInt8.ofNat v.toNat).toNat : Int).take (8 * 1) := by
    have hlt : v.toNat < 256 := v.isLt
    have hu : (UInt8.ofNat v.toNat).toNat = v.toNat := by simp
    simp only [Int.take, hu]
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  rw [hbits, ← Int.toBytes_emod, h1, Int.toBytes_emod]
  exact toBytes_u8 (UInt8.ofNat v.toNat)

theorem bytes_singleton_eq_cell8 (a : BitVec 64) (b : UInt8) :
    bytes a [b] = cell (t := i8) a (BitVec.ofNat 8 b.toNat) := by
  have hb := intToBytes_1_bv8 (BitVec.ofNat 8 b.toNat)
  have hb' : UInt8.ofNat (BitVec.ofNat 8 b.toNat).toNat = b := by
    apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    simp
  rw [hb'] at hb
  change Eq ([b].At a) = Eq ((Int.toBytes i8.bytes
    (BitVec.setWidth (8 * i8.bytes) (toBits i8 (BitVec.ofNat 8 b.toNat))).toInt).At a)
  have hbytes : i8.bytes = 1 := rfl
  rw [hbytes] at hb ⊢
  rw [hb]

theorem bytes_append (a : BitVec 64) (xs ys : List UInt8) (hfit : xs.length + ys.length ≤ 2 ^ 64) :
    bytes a (xs ++ ys) = (bytes a xs ⋆ bytes (a + BitVec.ofNat 64 xs.length) ys) := by
  simp only [bytes]
  exact eq_append_At a xs ys hfit

theorem bytes_split2 (a : BitVec 64) (xs : List UInt8) (k : Nat) (hk : k ≤ xs.length)
    (hfit : xs.length ≤ 2 ^ 64) :
    bytes a xs = (bytes a (xs.take k) ⋆ bytes (a + BitVec.ofNat 64 k) (xs.drop k)) := by
  conv => lhs; rw [← List.take_append_drop k xs]
  rw [bytes_append a (xs.take k) (xs.drop k) (by simp; omega), List.length_take_of_le hk]

@[c0_load] theorem r2_c0_load_bytes_bv {a i : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (bytes a bs ⋆ R) m)
    (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    loadVal m i8 (a + i) = some (BitVec.ofNat 8 (bs[i.toNat]'hi).toNat) := by
  simpa using load_bytes_at (base := a) (i := i.toNat) hi hlen h

@[c0_load] theorem r2_c0_load_bytes_add24 {a i : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (bytes (a + 24#64) bs ⋆ R) m)
    (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    loadVal m i8 (a + 24#64 + i) = some (BitVec.ofNat 8 (bs[i.toNat]'hi).toNat) :=
  r2_c0_load_bytes_bv h hi hlen

theorem store_bytes_at_bv {a i : BitVec 64} {bs : List UInt8} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes a bs ⋆ R) m) :
    storeOk m i8 (a + i) ∧
      (bytes a (bs.set i.toNat (UInt8.ofNat v.toNat)) ⋆ R) (storeMem m i8 (a + i) v) := by
  let bOld := bs[i.toNat]'hi
  have hsp : bytes a bs =
      (bytes a (bs.take i.toNat) ⋆
        (bytes (a + i) [bOld] ⋆ bytes (a + i + 1#64) (bs.drop (i.toNat + 1)))) := by
    rw [bytes_split2 a bs i.toNat (Nat.le_of_lt hi) hlen]
    have hdrop : bs.drop i.toNat = [bOld] ++ bs.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons hi]; rfl
    rw [hdrop, bytes_append _ [bOld] _ (by simp; omega)]
    rw [show BitVec.ofNat 64 i.toNat = i from by simp]
    simp only [List.length_singleton, BitVec.add_assoc]
  rw [hsp, bytes_singleton_eq_cell8] at hm
  have hm' : (cell (t := i8) (a + i) (BitVec.ofNat 8 bOld.toNat) ⋆
      (bytes a (bs.take i.toNat) ⋆ bytes (a + i + 1#64) (bs.drop (i.toNat + 1)) ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  obtain ⟨hok, hst⟩ := store_cell (t := i8) v (by decide) hm'
  refine ⟨hok, ?_⟩
  have hvEq : v = BitVec.ofNat 8 (UInt8.ofNat v.toNat).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp
  have hst' : (bytes (a + i) [UInt8.ofNat v.toNat] ⋆
      (bytes a (bs.take i.toNat) ⋆ bytes (a + i + 1#64) (bs.drop (i.toNat + 1)) ⋆ R))
      (storeMem m i8 (a + i) v) := by
    rw [bytes_singleton_eq_cell8, ← hvEq]
    exact hst
  have hjoin : bytes a (bs.set i.toNat (UInt8.ofNat v.toNat)) =
      (bytes a (bs.take i.toNat) ⋆
        (bytes (a + i) [UInt8.ofNat v.toNat] ⋆ bytes (a + i + 1#64) (bs.drop (i.toNat + 1)))) := by
    have hlen' : (bs.set i.toNat (UInt8.ofNat v.toNat)).length ≤ 2 ^ 64 := by simpa using hlen
    rw [bytes_split2 a _ i.toNat (by simp; omega) hlen']
    rw [List.take_set_of_le (Nat.le_refl _)]
    have hdrop' : (bs.set i.toNat (UInt8.ofNat v.toNat)).drop i.toNat =
        [UInt8.ofNat v.toNat] ++ bs.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [hi]), List.getElem_set_self]
      congr 1
      exact List.drop_set_of_lt (Nat.lt_succ_self i.toNat)
    rw [hdrop', bytes_append _ [UInt8.ofNat v.toNat] _ (by simp; omega),
      show BitVec.ofNat 64 i.toNat = i from by simp]
    simp only [List.length_singleton, BitVec.add_assoc]
  rw [hjoin]
  exact sep_cast hst' (by ac_rfl)

@[c0_store] theorem r2_c0_store_bytes_bv {a i : BitVec 64} {bs : List UInt8} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bytes a bs ⋆ R) m)
    (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    storeOk m i8 (a + i) ∧
      (bytes a (bs.set i.toNat (UInt8.ofNat v.toNat)) ⋆ R) (storeMem m i8 (a + i) v) :=
  store_bytes_at_bv v hi hlen hm

@[c0_store] theorem r2_c0_store_bytes_add24 {a i : BitVec 64} {bs : List UInt8} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bytes (a + 24#64) bs ⋆ R) m)
    (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    storeOk m i8 (a + 24#64 + i) ∧
      (bytes (a + 24#64) (bs.set i.toNat (UInt8.ofNat v.toNat)) ⋆ R)
        (storeMem m i8 (a + 24#64 + i) v) :=
  store_bytes_at_bv v hi hlen hm

theorem region_pop_byte {a : BitVec 64} {rem : Nat} (hrem : 0 < rem) (hfit : rem ≤ 2 ^ 64)
    {m : Mem 64} (hm : region a rem m) :
    ∃ v0 : BitVec 8, (cell (t := i8) a v0 ⋆ region (a + 1#64) (rem - 1)) m := by
  have heq : rem = 1 + (rem - 1) := by omega
  rw [heq, region_split (by omega)] at hm
  obtain ⟨f1, f2, hu, hd, hf1, hf2⟩ := hm
  rcases hf1 with ⟨bs, hbsLen, hmem⟩
  rcases bs with _ | ⟨b0, _ | _⟩ <;> simp at hbsLen
  have hcell : cell (t := i8) a (BitVec.ofNat 8 b0.toNat) f1 := by
    rw [← bytes_singleton_eq_cell8]
    exact hmem.symm
  refine ⟨BitVec.ofNat 8 b0.toNat, f1, f2, hu, hd, hcell, ?_⟩
  simpa using hf2

theorem region_pop_store_byte {a : BitVec 64} {rem : Nat} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hrem : 0 < rem) (hfit : rem ≤ 2 ^ 64)
    (hm : (region a rem ⋆ R) m) :
    storeOk m i8 a ∧
      (bytes a [UInt8.ofNat v.toNat] ⋆ region (a + 1#64) (rem - 1) ⋆ R) (storeMem m i8 a v) := by
  obtain ⟨f1, f2, hu, hd, hf1, hf2⟩ := hm
  obtain ⟨v0, hv0⟩ := region_pop_byte hrem hfit hf1
  have hm1 : (cell (t := i8) a v0 ⋆ (region (a + 1#64) (rem - 1) ⋆ R)) m := by
    rw [← sep_assoc]
    exact ⟨f1, f2, hu, hd, hv0, hf2⟩
  obtain ⟨hok, hst⟩ := store_cell (t := i8) v (by decide) hm1
  refine ⟨hok, ?_⟩
  have hvEq : v = BitVec.ofNat 8 (UInt8.ofNat v.toNat).toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  have hst' : (bytes a [UInt8.ofNat v.toNat] ⋆ (region (a + 1#64) (rem - 1) ⋆ R))
      (storeMem m i8 a v) := by
    rw [bytes_singleton_eq_cell8, ← hvEq]
    exact hst
  exact sep_cast hst' (by ac_rfl)

theorem byte_to_region {a : BitVec 64} {b : UInt8} {m : Mem 64}
    (h : bytes a [b] m) : region a 1 m := by
  simpa using bytes_to_region h

/-! ## 3. `LcnfC0Rt` & `LcnfObj` Focus, Update, and Header RC Lemmas -/

theorem rtC0Inv_hdr_focus {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    (LcnfC0Rt.At rt st.hdr ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ array64 st.hdr.s_work st.workBuf ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        largeFreeList st.hdr.s_large_free st.largeNodes ⋆
        region st.hdr.s_cur st.rem ⋆ H ⋆ R)) m := by
  unfold rtC0Inv at hm
  exact sep_cast hm (by ac_rfl)

theorem rtC0Inv_load_s_ba_empty {rt : BitVec 64} {st : RtC0State} {H R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    loadVal m i64 (rt + 33544#64) = some st.hdr.s_ba_empty :=
  LcnfC0Rt.load_s_ba_empty (rtC0Inv_hdr_focus hm)

theorem rtC0Inv_store_s_ba_empty {rt : BitVec 64} {st : RtC0State} (p : BitVec 64)
    {H R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ H ⋆ R) m) :
    storeOk m i64 (rt + 33544#64) ∧
      ((rtC0Inv rt { st with hdr := { st.hdr with s_ba_empty := p } } ⋆ H) ⋆ R)
        (storeMem m i64 (rt + 33544#64) p) := by
  have h1 := LcnfC0Rt.store_s_ba_empty p (rtC0Inv_hdr_focus hm)
  refine ⟨h1.1, ?_⟩
  unfold rtC0Inv
  exact sep_cast h1.2 (by ac_rfl)

private def lcnfObjMemTail (o : LcnfObj) : Mem 64 → Prop :=
  if o.tag = closureTag then
    cell64 (o.addr + 8#64) o.funId ⋆
    cell64 (o.addr + 16#64) o.cloMeta ⋆
    array64 (o.addr + 24#64) o.fields ⋆
    region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
      (o.csSz - (24 + 8 * o.fields.length))
  else if o.tag = arrayTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    array64 (o.addr + 24#64) o.fields ⋆
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
    cell64 (o.addr + 8#64) o.mpzMeta ⋆
    array64 (o.addr + 16#64) o.limbs
  else
    let soff := 8 + 8 * o.fields.length
    array64 (o.addr + 8#64) o.fields ⋆
    bytes (o.addr + BitVec.ofNat 64 soff) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (soff + o.scalarData.length))
      (o.csSz - (soff + o.scalarData.length))

private theorem lcnfObjMem_eq_header_tail (o : LcnfObj) :
    lcnfObjMem o = (cell64 o.addr o.header ⋆ lcnfObjMemTail o) := by
  unfold lcnfObjMem lcnfObjMemTail closureTag arrayTag sarrayTag stringTag mpzTag
  by_cases h1 : o.tag = 245; · simp [h1, sep_assoc]
  by_cases h2 : o.tag = 246; · simp [h2, sep_assoc]
  by_cases h3 : o.tag = 248; · simp [h3, sep_assoc]
  by_cases h4 : o.tag = 249; · simp [h4, sep_assoc]
  by_cases h5 : o.tag = 250; · simp [h5, sep_assoc]
  simp [h1, h2, h3, h4, h5, sep_assoc]

theorem lcnfObjMem_header_body (o : LcnfObj) :
    ∃ (body : Mem 64 → Prop),
      lcnfObjMem o = (cell64 o.addr o.header ⋆ body) ∧
      (∀ rc' : BitVec 32, lcnfObjMem { o with rc := rc' } =
        (cell64 o.addr { o with rc := rc' }.header ⋆ body)) :=
  ⟨lcnfObjMemTail o, lcnfObjMem_eq_header_tail o,
    fun rc' => by rw [lcnfObjMem_eq_header_tail]; rfl⟩

theorem r2_lcnfObjMem_load_header {o : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) : loadVal m i64 o.addr = some o.header := by
  obtain ⟨body, h, _⟩ := lcnfObjMem_header_body o
  rw [h, sep_assoc] at hm
  exact loadVal_cell64 hm

theorem lcnfObjMem_store_rc {o : LcnfObj} (rc' : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    storeOk m i64 o.addr ∧
      (lcnfObjMem (o.withRc rc') ⋆ R) (storeMem m i64 o.addr (o.withRc rc').header) := by
  obtain ⟨body, h, hw⟩ := lcnfObjMem_header_body o
  rw [h, sep_assoc] at hm
  obtain ⟨hok, hm'⟩ := store_cell64 (o.withRc rc').header hm
  refine ⟨hok, ?_⟩
  have heq : lcnfObjMem (o.withRc rc') = (cell64 o.addr (o.withRc rc').header ⋆ body) :=
    hw rc'
  rw [heq, sep_assoc]
  exact hm'

private theorem bv32_ofNat_and_hi_zero (rc : Nat) (hrc : rc < 2 ^ 32) (w : BitVec 64)
    (hlo : (w &&& 4294967295#64) = 0#64) :
    BitVec.ofNat 64 rc &&& w = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi64
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  by_cases hi32 : i < 32
  · have hget := congrArg (fun bv : BitVec 64 => bv.getLsbD i) hlo
    rw [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hget
    have hmask : (4294967295#64 : BitVec 64).getLsbD i = true := by
      rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 by decide,
        Nat.testBit_two_pow_sub_one]
      simp [hi64, hi32]
    rw [hmask, Bool.and_true] at hget
    simp [hget]
  · have : (BitVec.ofNat 64 rc).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]
      simp [hi64]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hrc (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

private theorem obj_hi_lo_zero (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256) :
    ((o.withRc 0#32).header &&& 4294967295#64) = 0#64 := by
  have hc : (o.withRc 0#32).header &&& 18446744069414584320#64 = (o.withRc 0#32).header := by
    simpa [LcnfObj.withRc] using LcnfObj.header_clear_rc (o.withRc 0#32) hcs hoth ht
  rw [← hc, BitVec.and_assoc]
  have hz : (18446744069414584320#64 &&& 4294967295#64) = 0#64 := by decide
  rw [hz, BitVec.and_zero]

private theorem obj_header_eq_add (o : LcnfObj)
    (hcs : o.csSz < 65536) (hoth : o.other < 256) (ht : o.tag < 256) :
    o.header = BitVec.ofNat 64 o.rc.toNat + (o.withRc 0#32).header := by
  have hlo := obj_hi_lo_zero o hcs hoth ht
  have hzero : BitVec.ofNat 64 o.rc.toNat &&& (o.withRc 0#32).header = 0#64 :=
    bv32_ofNat_and_hi_zero o.rc.toNat o.rc.isLt _ hlo
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hzero]
  unfold LcnfObj.header LcnfObj.withRc
  dsimp
  simp [BitVec.zero_or, BitVec.or_assoc]

theorem lcnfObjHeader_add1 (o : LcnfObj) (hwf : o.Wf) (hlt : o.rc.toInt < 2147483647) :
    o.header + 1#64 = (o.withRc (o.rc + 1#32)).header := by
  rcases hwf with ⟨_, _, h0, hcs, hoth, ht, _⟩
  have hrc : o.rc.toNat < 2147483647 := by
    rw [BitVec.toInt_eq_toNat_cond] at h0 hlt
    split at hlt <;> omega
  have hw := obj_header_eq_add (o.withRc (o.rc + 1#32)) hcs hoth ht
  have hw1 : (o.withRc (o.rc + 1#32)).header =
      BitVec.ofNat 64 (o.rc + 1#32).toNat + (o.withRc 0#32).header := by
    simpa [LcnfObj.withRc] using hw
  have hrc1 : BitVec.ofNat 64 (o.rc + 1#32).toNat = BitVec.ofNat 64 o.rc.toNat + 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  rw [obj_header_eq_add o hcs hoth ht, hw1, hrc1]; ac_rfl

theorem lcnfObjHeader_sub1 (o : LcnfObj) (hwf : o.Wf) (hgt : 1 < o.rc.toNat) :
    o.header - 1#64 = (o.withRc (o.rc - 1#32)).header := by
  rcases hwf with ⟨_, _, _, hcs, hoth, ht, _⟩
  have hw := obj_header_eq_add (o.withRc (o.rc - 1#32)) hcs hoth ht
  have hw1 : (o.withRc (o.rc - 1#32)).header =
      BitVec.ofNat 64 (o.rc - 1#32).toNat + (o.withRc 0#32).header := by
    simpa [LcnfObj.withRc] using hw
  have hadd : BitVec.ofNat 64 o.rc.toNat = BitVec.ofNat 64 (o.rc - 1#32).toNat + 1#64 := by
    apply BitVec.eq_of_toNat_eq
    have h1le32 : (1#32 : BitVec 32) ≤ o.rc := by
      rw [BitVec.le_def]; exact Nat.le_of_lt hgt
    have hlt64 : o.rc.toNat < 2 ^ 64 := Nat.lt_trans o.rc.isLt (by decide)
    simp [BitVec.toNat_add, BitVec.toNat_sub_of_le h1le32,
      Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt (by omega : o.rc.toNat - 1 < 2 ^ 64)]
    omega
  rw [obj_header_eq_add o hcs hoth ht, hw1, hadd]
  have hcanc : ∀ x : BitVec 64, x + 1#64 - 1#64 = x := fun x => by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc,
      show (1#64 : BitVec 64) + (-1#64) = 0#64 from by decide, BitVec.add_zero]
  rw [BitVec.add_comm (BitVec.ofNat 64 (o.rc - 1#32).toNat + 1#64), ← BitVec.add_assoc,
    hcanc, BitVec.add_comm]

theorem lcnfObjMem_sarray_eq {o : LcnfObj} (h : o.tag = sarrayTag) :
    lcnfObjMem o =
      (cell64 o.addr o.header ⋆
        cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        bytes (o.addr + 24#64) o.scalarData ⋆
        region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
          (o.totalBytes - (24 + o.scalarData.length))) := by
  simp [lcnfObjMem, h, show sarrayTag ≠ closureTag by decide,
    show sarrayTag ≠ arrayTag by decide]

theorem lcnfObjMem_array_eq {o : LcnfObj} (h : o.tag = arrayTag) :
    lcnfObjMem o =
      (cell64 o.addr o.header ⋆
        cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        array64 (o.addr + 24#64) o.fields ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length))) := by
  simp [lcnfObjMem, h, show arrayTag ≠ closureTag by decide]

/-! ## 4. Heap Nodup, `nonPersistRefs`, and `HandlesRcSound` COW Lemmas -/

theorem cell64_sep_ne {a1 a2 v1 v2 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 a1 v1 ⋆ cell64 a2 v2 ⋆ R) m) : a1 ≠ a2 := by
  intro heq
  subst heq
  have hm1 : (cell64 a1 v1 ⋆ (cell64 a1 v2 ⋆ R)) m := sep_cast h (by ac_rfl)
  have hl1 : loadVal m i64 a1 = some v1 := loadVal_cell64 hm1
  let vnew : BitVec 64 := if v1 = v2 + 1#64 then v2 + 2#64 else v2 + 1#64
  have hm2 : (cell64 a1 v2 ⋆ (cell64 a1 v1 ⋆ R)) m := sep_cast h (by ac_rfl)
  obtain ⟨_, hst⟩ := store_cell64 vnew hm2
  have hst' : (cell64 a1 v1 ⋆ (cell64 a1 vnew ⋆ R)) (storeMem m i64 a1 vnew) :=
    sep_cast hst (by ac_rfl)
  have hl2 : loadVal (storeMem m i64 a1 vnew) i64 a1 = some v1 := loadVal_cell64 hst'
  have hl3 : loadVal (storeMem m i64 a1 vnew) i64 a1 = some vnew := loadVal_cell64 hst
  rw [hl2] at hl3
  injection hl3 with hvv
  dsimp [vnew] at hvv
  split at hvv
  · exact absurd hvv (by bv_omega)
  · exact absurd hvv (by assumption)

theorem lcnfHeap_addr_ne {objs : List LcnfObj} {i j : Nat} (hij : i < j) (hj : j < objs.length)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfHeap objs ⋆ R) m) :
    objs[i].addr ≠ objs[j].addr := by
  have hi : i < objs.length := Nat.lt_trans hij hj
  rw [lcnfHeap_focus objs hi] at hm
  have hj' : j - (i + 1) < (objs.drop (i + 1)).length := by simp; omega
  have heq : (objs.drop (i + 1))[j - (i + 1)] = objs[j] := by simp; congr 1; omega
  rw [lcnfHeap_focus (objs.drop (i + 1)) hj', heq] at hm
  obtain ⟨bi, hbi, _⟩ := lcnfObjMem_header_body objs[i]
  obtain ⟨bj, hbj, _⟩ := lcnfObjMem_header_body objs[j]
  rw [hbi, hbj] at hm
  have h2 : (cell64 objs[i].addr objs[i].header ⋆ cell64 objs[j].addr objs[j].header ⋆
      (bi ⋆ bj ⋆ lcnfHeap (objs.take i) ⋆ lcnfHeap ((objs.drop (i + 1)).take (j - (i + 1))) ⋆
        lcnfHeap ((objs.drop (i + 1)).drop (j - (i + 1) + 1)) ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  exact cell64_sep_ne h2

theorem lcnfHeap_nodup_addrs {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfHeap objs ⋆ R) m) : (objs.map LcnfObj.addr).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map]
  exact lcnfHeap_addr_ne hij hj hm

theorem nodup_addr_eq_of_mem {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {a b : LcnfObj} (ha : a ∈ objs) (hb : b ∈ objs) (heq : a.addr = b.addr) : a = b := by
  rw [List.mem_iff_getElem] at ha hb
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  have hij : i = j := by
    have hp := List.pairwise_iff_getElem.mp hnd
    by_cases hlt : i < j
    · have hne := hp i j (by simpa using hi) (by simpa using hj) hlt
      simp only [List.getElem_map] at hne
      exact absurd heq hne
    · by_cases hgt : j < i
      · have hne := hp j i (by simpa using hj) (by simpa using hi) hgt
        simp only [List.getElem_map] at hne
        exact absurd heq.symm hne
      · omega
  subst hij; rfl

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
      rw [ih (init + o.childFields.count a), ih (0 + o.childFields.count a)]
      omega

theorem nonPersistRefs_cons (o : LcnfObj) (os : List LcnfObj) (a : BitVec 64) :
    nonPersistRefs (o :: os) a =
      (if o.rc = 0#32 then 0 else o.childFields.count a) + nonPersistRefs os a := by
  unfold nonPersistRefs
  simp only [List.foldl_cons]
  split
  · simp
  · rw [nonPersistRefs_foldl_shift]
    change 0 + o.childFields.count a + nonPersistRefs os a = _ + nonPersistRefs os a
    omega

theorem nonPersistRefs_append (xs ys : List LcnfObj) (a : BitVec 64) :
    nonPersistRefs (xs ++ ys) a = nonPersistRefs xs a + nonPersistRefs ys a := by
  induction xs with
  | nil => simp [nonPersistRefs]
  | cons x xs ih => simp only [List.cons_append, nonPersistRefs_cons, ih]; omega

theorem nonPersistRefs_focus (objs : List LcnfObj) {idx : Nat} (hidx : idx < objs.length)
    (a : BitVec 64) :
    nonPersistRefs objs a =
      (if objs[idx].rc = 0#32 then 0 else objs[idx].childFields.count a) +
      nonPersistRefs (objs.eraseIdx idx) a := by
  have hsp : objs = objs.take idx ++ objs[idx] :: objs.drop (idx + 1) := by
    have h1 := List.take_append_drop idx objs
    rw [List.drop_eq_getElem_cons hidx] at h1
    exact h1.symm
  conv => lhs; rw [hsp]
  rw [nonPersistRefs_append, nonPersistRefs_cons, List.eraseIdx_eq_take_drop_succ,
    nonPersistRefs_append]
  omega

/-- Key COW uniqueness property: if `aObj ∈ objs` has `m_rc = 1#32` under `HandlesRcSound`,
and caller holds a handle `a = aObj.addr` in `a :: extraHandles`, then `aObj` has zero aliases
in `extraHandles` and zero incoming edges from any object in `objs` (including itself). -/
theorem handlesRcSound_exclusive_no_aliases {a : BitVec 64} {extraHandles : List (BitVec 64)}
    {objs : List LcnfObj} (hrc : HandlesRcSound (a :: extraHandles) objs)
    {aObj : LcnfObj} (hmem : aObj ∈ objs) (ha : aObj.addr = a) (h1 : aObj.rc = 1#32) :
    nonPersistRefs objs a = 0 ∧ extraHandles.count a = 0 ∧ a ∉ aObj.childFields := by
  have hpos : 0 < aObj.rc.toInt := by rw [h1]; decide
  have hle := hrc.2 aObj hmem hpos
  rw [ha, h1] at hle
  have hcnt : (a :: extraHandles).count a = 1 + extraHandles.count a := by
    rw [List.count_cons]; simp; omega
  rw [hcnt, show (1#32 : BitVec 32).toNat = 1 from rfl] at hle
  have hnp : nonPersistRefs objs a = 0 := by omega
  have hex : extraHandles.count a = 0 := by omega
  refine ⟨hnp, hex, fun hchild => ?_⟩
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨idx, hidx, rfl⟩ := hmem
  have hsp := nonPersistRefs_focus objs hidx a
  have hcntChild : 0 < objs[idx].childFields.count a := List.count_pos_iff.mpr hchild
  rw [hnp, h1] at hsp
  simp at hsp
  omega

theorem lcnfObjMem_array_incChildren_map (fields : List (BitVec 64)) (y : LcnfObj) :
    (fun o : LcnfObj =>
      if 0 < o.rc.toInt then o.withRc (BitVec.ofNat 32 (o.rc.toNat + fields.count o.addr))
      else o) y =
      if 0 < y.rc.toInt then y.withRc (BitVec.ofNat 32 (y.rc.toNat + fields.count y.addr))
      else y := rfl

theorem incChildrenObjs_length (fields : List (BitVec 64)) (objs : List LcnfObj) :
    (incChildrenObjs fields objs).length = objs.length := by
  simp [incChildrenObjs]

theorem lcnfObjMem_incChildren_step (fields : List (BitVec 64))
    (objs : List LcnfObj) :
    incChildrenObjs (fields.take 0) objs = objs := by
  simp [incChildrenObjs, LcnfObj.withRc]

/-! ## 5. WP Proofs for Core Helpers (`r2_inc_obj`, `r2_dec_obj`, Copy, Compare, `lcnf_oob`) -/

private theorem bv64_and1_ne_zero_iff (x : BitVec 64) :
    (x &&& 1#64) ≠ 0#64 ↔ (x &&& 1#64) = 1#64 := by
  have hlt : (x &&& 1#64).toNat < 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change x.toNat &&& (2 ^ 1 - 1) < 2
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.pow_one]
    exact Nat.mod_lt _ (by decide)
  have h1n : (1#64 : BitVec 64).toNat = 1 := rfl
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have hne0 : (x &&& 1#64).toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq h0)
    rw [h1n]; omega
  · intro h; rw [h]; decide

theorem r2_inc_obj_wp :
    ∀ xs m Q X, r2IncObjSpec xs m Q X → Func.wp rtR2Env r2_inc_obj_body xs m Q X := by
  intro ⟨o, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2_inc_obj_body, r2IncObjSpec] at hPre ⊢
  change LeanQbe.T.wp _ _ _ _ _
  by_cases hnull : o = 0#64 ∨ (o &&& 1#64) ≠ 0#64
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hnull)] at hPre
    c0_steps <;> first
      | exact hPre
      | (exfalso; rcases hnull with h0 | h1 <;> contradiction)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hnull)] at hPre
    rcases hPre with ⟨obj, R, rfl, hwf, hm, hk⟩
    r2_steps
    apply wp_load_of
    · exact r2_lcnfObjMem_load_header hm
    · have hrcEq := LcnfObj.header_rc obj hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
      r2_steps
      · -- rc ≠ 0#64 ∧ rc < 2147483647#64
        have hrcNe0 : obj.rc ≠ 0#32 := by
          have hne : (obj.header &&& 0xffffffff#64) ≠ 0#64 := by assumption
          intro h0; rw [h0] at hrcEq; simp at hrcEq; contradiction
        have hltNat : obj.rc.toNat < 2147483647 := by
          have hlt : (obj.header &&& 0xffffffff#64).toNat < 2147483647 := by assumption
          rw [hrcEq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_trans obj.rc.isLt (by decide))] at hlt
          exact hlt
        have hpos : 0 < obj.rc.toInt := by
          have h0 := hwf.2.2.1
          have hne0N : obj.rc.toNat ≠ 0 := fun h => hrcNe0 (BitVec.eq_of_toNat_eq h)
          rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
        have hltInt : obj.rc.toInt < 2147483647 := by
          rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
        have hinc : incRcVal obj.rc = obj.rc + 1#32 := by simp [incRcVal, hpos, hltInt]
        obtain ⟨hok, hm'⟩ := lcnfObjMem_store_rc (obj.rc + 1#32) hm
        rw [← lcnfObjHeader_add1 obj hwf hltInt] at hm'
        apply wp_store_sep
        · exact ⟨hok, hm'⟩
        · intro m' hm''
          r2_steps
          exact hk m' (hinc ▸ hm'')
      · -- rc ≥ 2147483647#64
        have hgeNat : 2147483647 ≤ obj.rc.toNat := by
          have hge : ¬ (obj.header &&& 0xffffffff#64).toNat < 2147483647 := by assumption
          rw [hrcEq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_trans obj.rc.isLt (by decide))] at hge
          omega
        have hgeInt : ¬ obj.rc.toInt < 2147483647 := by
          have h0 := hwf.2.2.1
          rw [BitVec.toInt_eq_toNat_cond] at h0 ⊢; split at h0 <;> omega
        have hinc : incRcVal obj.rc = obj.rc := by simp [incRcVal, hgeInt]
        have hself : obj.withRc obj.rc = obj := by cases obj; rfl
        have hm' : (lcnfObjMem (obj.withRc (incRcVal obj.rc)) ⋆ R) m := by
          rw [hinc, hself]; exact hm
        exact hk m hm'
      · -- rc = 0#64
        have hrc0 : obj.rc = 0#32 := by
          have h0 : (obj.header &&& 0xffffffff#64) = 0#64 := by assumption
          rw [hrcEq] at h0
          have htoNat : (BitVec.ofNat 64 obj.rc.toNat).toNat = 0 := by rw [h0]; rfl
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans obj.rc.isLt (by decide))] at htoNat
          exact BitVec.eq_of_toNat_eq htoNat
        have hinc : incRcVal obj.rc = obj.rc := by simp [incRcVal, hrc0]
        have hself : obj.withRc obj.rc = obj := by cases obj; rfl
        have hm' : (lcnfObjMem (obj.withRc (incRcVal obj.rc)) ⋆ R) m := by
          rw [hinc, hself]; exact hm
        exact hk m hm'

theorem r2_dec_obj_wp :
    ∀ xs m Q X, r2DecObjSpec xs m Q X → Func.wp rtR2Env r2_dec_obj_body xs m Q X := by
  intro ⟨rt, o, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2_dec_obj_body, r2DecObjSpec] at hPre ⊢
  change LeanQbe.T.wp _ _ _ _ _
  by_cases hnull : o = 0#64 ∨ (o &&& 1#64) ≠ 0#64
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hnull)] at hPre
    c0_steps <;> first
      | exact hPre
      | (exfalso; rcases hnull with h0 | h1 <;> contradiction)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hnull)] at hPre
    rcases hPre with ⟨st, objs, R, ⟨obj, hmem, ha, h1pre⟩, hwf, hm, hk⟩
    have hnd := lcnfHeap_nodup_addrs
      (sep_cast hm (by ac_rfl) : (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ R)) m)
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨idx, hidx, rfl⟩ := hmem
    have hobjWf : objs[idx].Wf := hwf _ (List.getElem_mem hidx)
    have hmHdr : (lcnfObjMem objs[idx] ⋆
        (rtC0Inv rt st ⋆ lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1)) ⋆ R)) m := by
      rw [lcnfHeap_focus objs hidx] at hm
      exact sep_cast hm (by ac_rfl)
    r2_steps
    apply wp_load_of
    · exact ha ▸ r2_lcnfObjMem_load_header hmHdr
    · have hrcEq := LcnfObj.header_rc objs[idx] hobjWf.2.2.2.1 hobjWf.2.2.2.2.1 hobjWf.2.2.2.2.2.1
      r2_steps
      · -- rc = 1#64 -> call lcnf_dec_ref_cold(rt, o)
        have hrc1 : objs[idx].rc = 1#32 := by
          have hc1 : (objs[idx].header &&& 0xffffffff#64) = 1#64 := by assumption
          rw [hrcEq] at hc1
          have htoNat : (BitVec.ofNat 64 objs[idx].rc.toNat).toNat = 1 := by rw [hc1]; rfl
          rw [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_trans objs[idx].rc.isLt (by decide))] at htoNat
          exact BitVec.eq_of_toNat_eq htoNat
        obtain ⟨hwc, hcl, hrcS⟩ := h1pre hrc1
        have hand0 : (o &&& 1#64) = 0#64 := Classical.not_not.mp fun h => hnull (Or.inr h)
        r2_call rtR2Env_lcnf_dec_ref_cold
        refine ⟨hand0, st, objs, R, hwc, hm, ⟨objs[idx], List.getElem_mem hidx, ha, hrc1⟩,
          hwf, hcl, hrcS, ?_⟩
        intro st' objs' m' hpr hrem hcold hm'
        dsimp only [Arg.val] at hcold hm'
        r2_steps
        have hrel : DecObjRel o objs objs' := by
          simp only [DecObjRel, ite_eq_right_of_eq_false _ _ (eq_false hnull)]
          exact ⟨objs[idx], List.getElem_mem hidx, ha, by simp [hrc1, hcold]⟩
        exact hk st' objs' m' hpr hrem hrel hm'
      · -- 1 < rc ∧ rc < 2147483648
        have hrcNe1 : objs[idx].rc ≠ 1#32 := by
          have hne : (objs[idx].header &&& 0xffffffff#64) ≠ 1#64 := by assumption
          intro h1; rw [h1] at hrcEq; simp at hrcEq; contradiction
        have hgt1 : 1 < objs[idx].rc.toNat := by
          have hc1 : 1 < (objs[idx].header &&& 0xffffffff#64).toNat := by assumption
          rw [hrcEq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_trans objs[idx].rc.isLt (by decide))] at hc1
          exact hc1
        have hlt231 : objs[idx].rc.toNat < 2147483648 := by
          have hc2 : (objs[idx].header &&& 0xffffffff#64).toNat < 2147483648 := by assumption
          rw [hrcEq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_trans objs[idx].rc.isLt (by decide))] at hc2
          exact hc2
        have hgtInt : 1 < objs[idx].rc.toInt := by
          have h0 := hobjWf.2.2.1
          rw [BitVec.toInt_eq_toNat_cond] at h0 ⊢; split at h0 <;> omega
        obtain ⟨hok, hm'⟩ := lcnfObjMem_store_rc (objs[idx].rc - 1#32) hmHdr
        rw [← lcnfObjHeader_sub1 objs[idx] hobjWf hgt1] at hm'
        rw [ha] at hok hm'
        apply wp_store_sep
        · exact ⟨hok, hm'⟩
        · intro m' hm''
          r2_steps
          have hmObj' :
              (rtC0Inv rt st ⋆
                lcnfHeap (objs.set idx (objs[idx].withRc (objs[idx].rc - 1#32))) ⋆ R) m' := by
            rw [lcnfHeap_set objs hidx]
            exact sep_cast hm'' (by ac_rfl)
          have hmap : objs.set idx (objs[idx].withRc (objs[idx].rc - 1#32)) =
              objs.map fun y => if y.addr = o then y.withRc (decNonExclRc y.rc) else y := by
            apply List.ext_getElem
            · simp
            · intro j hj1 hj2
              have hjLen : j < objs.length := by simpa using hj2
              by_cases hji : j = idx
              · subst hji
                simp only [List.getElem_set_self, List.getElem_map, ha, ↓reduceIte,
                  decNonExclRc, hgtInt]
              · have hneA : objs[j].addr ≠ o := by
                  intro heq
                  have hlt : j < idx ∨ idx < j := Nat.lt_or_gt_of_ne hji
                  rcases hlt with h1 | h2
                  · exact lcnfHeap_addr_ne h1 hidx
                      (sep_cast hm (by ac_rfl) : (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ R)) m)
                      (heq.trans ha.symm)
                  · exact lcnfHeap_addr_ne h2 hjLen
                      (sep_cast hm (by ac_rfl) : (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ R)) m)
                      (ha.trans heq.symm)
                simp only [List.getElem_set_ne (Ne.symm hji), List.getElem_map,
                  ite_eq_right_of_eq_false _ _ (eq_false hneA)]
          rw [hmap] at hmObj'
          have hrel : DecObjRel o objs
              (objs.map fun y => if y.addr = o then y.withRc (decNonExclRc y.rc) else y) := by
            simp only [DecObjRel, ite_eq_right_of_eq_false _ _ (eq_false hnull)]
            exact ⟨objs[idx], List.getElem_mem hidx, ha, by simp [hrcNe1]⟩
          exact hk st _ m' (RtC0State.PreservesMeta.refl st) rfl hrel hmObj'
      · -- 1 < rc ∧ ¬ rc < 2147483648: impossible since o.rc.toInt ≥ 0
        exfalso
        have hnot : ¬ (objs[idx].header &&& 0xffffffff#64).toNat < 2147483648 := by assumption
        have h0 := hobjWf.2.2.1
        rw [hrcEq, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_trans objs[idx].rc.isLt (by decide))] at hnot
        rw [BitVec.toInt_eq_toNat_cond] at h0; split at h0 <;> omega
      · -- rc = 0
        have hrcNe1 : objs[idx].rc ≠ 1#32 := by
          have hne : (objs[idx].header &&& 0xffffffff#64) ≠ 1#64 := by assumption
          intro h1; rw [h1] at hrcEq; simp at hrcEq; contradiction
        have hnot : ¬ 1 < (objs[idx].header &&& 0xffffffff#64).toNat := by assumption
        have h0 := hobjWf.2.2.1
        have hlt231 : objs[idx].rc.toNat < 2147483648 := by
          rw [BitVec.toInt_eq_toNat_cond] at h0; split at h0 <;> omega
        have hrc0Nat : objs[idx].rc.toNat = 0 := by
          rw [hrcEq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_trans objs[idx].rc.isLt (by decide))] at hnot
          have hne1Nat : objs[idx].rc.toNat ≠ 1 := fun h => hrcNe1 (BitVec.eq_of_toNat_eq h)
          omega
        have hrc0 : objs[idx].rc = 0#32 := BitVec.eq_of_toNat_eq hrc0Nat
        have hmapEq : (objs.map fun y =>
            if y.addr = o then y.withRc (decNonExclRc y.rc) else y) = objs := by
          apply List.ext_getElem
          · simp
          · intro j hj1 hj2
            simp only [List.getElem_map]
            split
            · rename_i heq
              have hy := nodup_addr_eq_of_mem hnd (List.getElem_mem (by simpa using hj2))
                (List.getElem_mem hidx) (heq.trans ha.symm)
              rw [hy, hrc0]
              simp only [decNonExclRc, show ¬ 1 < (0#32 : BitVec 32).toInt by decide, ↓reduceIte]
              rw [← hrc0]; cases objs[idx]; rfl
            · rfl
        have hrel : DecObjRel o objs objs := by
          simp only [DecObjRel, ite_eq_right_of_eq_false _ _ (eq_false hnull)]
          exact ⟨objs[idx], List.getElem_mem hidx, ha, by simp [hrcNe1, hmapEq]⟩
        exact hk st objs m (RtC0State.PreservesMeta.refl st) rfl hrel hm

theorem r2_mem_copy_bytes_wp :
    ∀ xs m Q X, r2MemCopyBytesSpec xs m Q X → Func.wp rtR2Env r2_mem_copy_bytes_body xs m Q X := by
  intro ⟨dst, src, len, ⟨⟩⟩ m Q X ⟨srcData, remCap, R, hslen, hle, hremFit, hm, hk⟩
  dsimp only [Func.wp, r2_mem_copy_bytes_body]
  change LeanQbe.T.wp _ _ _ _ _
  have hfitLen : len.toNat ≤ 2 ^ 64 := Nat.le_of_lt len.isLt
  refine wp_loop_inv
    (fun (xs : Tup Val [i64]) mL =>
      ∃ (iNat : Nat), iNat ≤ len.toNat ∧ xs.1 = BitVec.ofNat 64 iNat ∧
        (bytes src srcData ⋆ bytes dst (srcData.take iNat) ⋆
          region (dst + BitVec.ofNat 64 iNat) (remCap - iNat) ⋆ R) mL)
    (fun (xs : Tup Val [i64]) _ => len.toNat - xs.1.toNat) ?_ ?_
  · intro Js hJs
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    refine hJs (0#64, ()) m ⟨0, Nat.zero_le _, rfl, ?_⟩
    rw [List.take_zero, bytes_nil_eq, show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl,
      BitVec.add_zero, Nat.sub_zero]
    exact sep_cast hm (by ac_rfl)
  · intro Js ⟨i, ⟨⟩⟩ mL ⟨iNat, hiLe, hiEq, hmL⟩ hRec
    dsimp only at hiEq
    subst hiEq
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · -- i < len
      have hlt : iNat < len.toNat := by
        have hc : (BitVec.ofNat 64 iNat).toNat < len.toNat := by assumption
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
      have hiSrc : (BitVec.ofNat 64 iNat).toNat < srcData.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hslen]; exact hlt
      have hregFocus : (region (dst + BitVec.ofNat 64 iNat) (remCap - iNat) ⋆
          (bytes src srcData ⋆ bytes dst (srcData.take iNat) ⋆ R)) mL :=
        sep_cast hmL (by ac_rfl)
      let bVal := BitVec.ofNat 8 (srcData[(BitVec.ofNat 64 iNat).toNat]'hiSrc).toNat
      obtain ⟨hok, hmStore⟩ := region_pop_store_byte bVal (by omega) (by omega) hregFocus
      apply wp_store_sep
      · exact ⟨hok, hmStore⟩
      · intro mL' hmL'
        have hbEq : UInt8.ofNat bVal.toNat = srcData[iNat]'(by omega) := by
          have hidxNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
            simp [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
          dsimp [bVal]
          apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
          simp [hidxNat]
        have hlenTake : (srcData.take iNat).length = iNat := List.length_take_of_le (by omega)
        have htakeSucc :
            srcData.take iNat ++ [srcData[iNat]'(by omega)] = srcData.take (iNat + 1) := by
          rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
        have hjoin : (bytes dst (srcData.take iNat) ⋆
            bytes (dst + BitVec.ofNat 64 iNat) [UInt8.ofNat bVal.toNat]) =
            bytes dst (srcData.take (iNat + 1)) := by
          rw [hbEq, ← htakeSucc, bytes_append dst (srcData.take iNat) _ (by simp [hlenTake]; omega),
            hlenTake]
        have hmNext : (bytes src srcData ⋆ bytes dst (srcData.take (iNat + 1)) ⋆
            region (dst + BitVec.ofNat 64 (iNat + 1)) (remCap - (iNat + 1)) ⋆ R) mL' := by
          have h1 : ((bytes dst (srcData.take iNat) ⋆
              bytes (dst + BitVec.ofNat 64 iNat) [UInt8.ofNat bVal.toNat]) ⋆
              (bytes src srcData ⋆
                region (dst + BitVec.ofNat 64 iNat + 1#64) (remCap - iNat - 1) ⋆ R)) mL' :=
            sep_cast hmL' (by ac_rfl)
          rw [hjoin, ptr_add_nat_r2, show remCap - iNat - 1 = remCap - (iNat + 1) by omega] at h1
          exact sep_cast h1 (by ac_rfl)
        r2_steps
        have hi1 : BitVec.ofNat 64 iNat + 1 = BitVec.ofNat 64 (iNat + 1) := by
          apply BitVec.eq_of_toNat_eq; simp
        rw [hi1]
        refine hRec (BitVec.ofNat 64 (iNat + 1), ()) mL' ?_ ⟨iNat + 1, by omega, rfl, hmNext⟩
        change len.toNat - (BitVec.ofNat 64 (iNat + 1)).toNat <
          len.toNat - (BitVec.ofNat 64 iNat).toNat
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    · -- ¬ i < len -> iNat = len.toNat
      have heq : iNat = len.toNat := by
        have hc : ¬ (BitVec.ofNat 64 iNat).toNat < len.toNat := by assumption
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
        omega
      subst heq
      rw [List.take_of_length_le (by omega),
        show BitVec.ofNat 64 len.toNat = len from by simp] at hmL
      exact hk mL hmL

private theorem cmpByteSlices_cons (a b : UInt8) (as bs : List UInt8) :
    cmpByteSlices (a :: as) (b :: bs) =
      if a.toNat < b.toNat then 0#64
      else if a.toNat > b.toNat then 2#64
      else cmpByteSlices as bs := rfl

private theorem u8_mod_lt (b : UInt8) : b.toNat % 2 ^ 8 % 2 ^ 64 = b.toNat := by
  rw [Nat.mod_eq_of_lt (UInt8.toNat_lt b),
    Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt b) (by decide))]

theorem r2_cmp_byte_slices_wp :
    ∀ xs m Q X, r2CmpByteSlicesSpec xs m Q X →
      Func.wp rtR2Env r2_cmp_byte_slices_body xs m Q X := by
  intro ⟨ap, la, bp, lb, ⟨⟩⟩ m Q X ⟨bsA, bsB, RA, RB, hla, hlb, hma, hmb, hq⟩
  dsimp only [Func.wp, r2_cmp_byte_slices_body]
  change LeanQbe.T.wp _ _ _ _ _
  let minLen := min bsA.length bsB.length
  refine wp_join_group
    (fun (xs : Tup Val [i64]) m' => xs.1 = BitVec.ofNat 64 minLen ∧ m' = m) ?_ ?_
  · intro J_m ⟨mVal, ⟨⟩⟩ m' ⟨hmVal, hmEq⟩
    dsimp only at hmVal; subst hmVal; subst m'
    refine wp_loop_inv
      (fun (xs : Tup Val [i64]) mL =>
        ∃ (iNat : Nat), iNat ≤ minLen ∧ xs.1 = BitVec.ofNat 64 iNat ∧ mL = m ∧
          cmpByteSlices bsA bsB = cmpByteSlices (bsA.drop iNat) (bsB.drop iNat))
      (fun (xs : Tup Val [i64]) _ => minLen - xs.1.toNat) ?_ ?_
    · intro Js hJs
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      exact hJs (0, ()) m ⟨0, Nat.zero_le _, rfl, rfl, rfl⟩
    · intro Js ⟨i, ⟨⟩⟩ mL ⟨iNat, hiLe, hiEq, hmL, hcmp⟩ hRec
      dsimp only at hiEq; subst hiEq; subst mL
      have hminLt : minLen < 2 ^ 64 := by dsimp [minLen]; omega
      r2_steps
      · -- i < m ∧ ba < bb -> return 0
        have hlt : iNat < minLen := by
          have hc : (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 minLen).toNat := by assumption
          rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hminLt] at hc
        have hdropA :=
          List.drop_eq_getElem_cons (show iNat < bsA.length by dsimp [minLen] at hlt; omega)
        have hdropB :=
          List.drop_eq_getElem_cons (show iNat < bsB.length by dsimp [minLen] at hlt; omega)
        rw [hdropA, hdropB, cmpByteSlices_cons] at hcmp
        have hltByte : (bsA[iNat]'(by dsimp [minLen] at hlt; omega)).toNat <
            (bsB[iNat]'(by dsimp [minLen] at hlt; omega)).toNat := by
          have hc :
              (bsA[iNat % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
                dsimp [minLen] at hlt; omega)).toNat % 2 ^ 8 % 2 ^ 64 <
              (bsB[iNat % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
                dsimp [minLen] at hlt; omega)).toNat % 2 ^ 8 % 2 ^ 64 := by
            assumption
          simp only [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64), u8_mod_lt] at hc
          exact hc
        simp only [hltByte, ↓reduceIte] at hcmp
        rw [hcmp] at hq; exact hq
      · -- i < m ∧ ¬ ba < bb ∧ ba > bb -> return 2
        have hlt : iNat < minLen := by
          have hc : (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 minLen).toNat := by assumption
          rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hminLt] at hc
        have hdropA :=
          List.drop_eq_getElem_cons (show iNat < bsA.length by dsimp [minLen] at hlt; omega)
        have hdropB :=
          List.drop_eq_getElem_cons (show iNat < bsB.length by dsimp [minLen] at hlt; omega)
        rw [hdropA, hdropB, cmpByteSlices_cons] at hcmp
        have hgtByte : (bsB[iNat]'(by dsimp [minLen] at hlt; omega)).toNat <
            (bsA[iNat]'(by dsimp [minLen] at hlt; omega)).toNat := by
          have hc :
              (bsB[iNat % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
                dsimp [minLen] at hlt; omega)).toNat % 2 ^ 8 % 2 ^ 64 <
              (bsA[iNat % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
                dsimp [minLen] at hlt; omega)).toNat % 2 ^ 8 % 2 ^ 64 := by
            assumption
          simp only [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64), u8_mod_lt] at hc
          exact hc
        have hnotLt : ¬ (bsA[iNat]'(by dsimp [minLen] at hlt; omega)).toNat <
            (bsB[iNat]'(by dsimp [minLen] at hlt; omega)).toNat := by omega
        simp only [hnotLt, ↓reduceIte, gt_iff_lt, hgtByte] at hcmp
        rw [hcmp] at hq; exact hq
      · -- i < m ∧ ba = bb -> continue loop
        have hlt : iNat < minLen := by
          have hc : (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 minLen).toNat := by assumption
          rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hminLt] at hc
        have hdropA :=
          List.drop_eq_getElem_cons (show iNat < bsA.length by dsimp [minLen] at hlt; omega)
        have hdropB :=
          List.drop_eq_getElem_cons (show iNat < bsB.length by dsimp [minLen] at hlt; omega)
        rw [hdropA, hdropB, cmpByteSlices_cons] at hcmp
        have hnotLt : ¬ (bsA[iNat]'(by dsimp [minLen] at hlt; omega)).toNat <
            (bsB[iNat]'(by dsimp [minLen] at hlt; omega)).toNat := by
          have hc :
              ¬ (bsA[iNat % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
                dsimp [minLen] at hlt; omega)).toNat % 2 ^ 8 % 2 ^ 64 <
              (bsB[iNat % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
                dsimp [minLen] at hlt; omega)).toNat % 2 ^ 8 % 2 ^ 64 := by
            assumption
          simp only [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64), u8_mod_lt] at hc
          exact hc
        have hnotGt : ¬ (bsA[iNat]'(by dsimp [minLen] at hlt; omega)).toNat >
            (bsB[iNat]'(by dsimp [minLen] at hlt; omega)).toNat := by
          have hc :
              ¬ (bsB[iNat % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
                dsimp [minLen] at hlt; omega)).toNat % 2 ^ 8 % 2 ^ 64 <
              (bsA[iNat % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64)]
                dsimp [minLen] at hlt; omega)).toNat % 2 ^ 8 % 2 ^ 64 := by
            assumption
          simp only [Nat.mod_eq_of_lt (by omega : iNat < 2 ^ 64), u8_mod_lt] at hc
          simpa [gt_iff_lt] using hc
        simp only [hnotLt, ↓reduceIte, gt_iff_lt, hnotGt] at hcmp
        have hi1 : BitVec.ofNat 64 iNat + 1 = BitVec.ofNat 64 (iNat + 1) := by
          apply BitVec.eq_of_toNat_eq; simp
        rw [hi1]
        refine hRec (BitVec.ofNat 64 (iNat + 1), ()) m ?_
          ⟨iNat + 1, by omega, rfl, rfl, hcmp⟩
        change minLen - (BitVec.ofNat 64 (iNat + 1)).toNat <
          minLen - (BitVec.ofNat 64 iNat).toNat
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · -- ¬ i < m ∧ la < lb -> return 0
        have heq : iNat = minLen := by
          have hc : ¬ (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 minLen).toNat := by assumption
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hminLt] at hc
          omega
        subst heq
        have hltAB : bsA.length < bsB.length := by
          have hc : la.toNat < lb.toNat := by assumption
          omega
        have hdA : bsA.drop minLen = [] := List.drop_of_length_le (by dsimp [minLen]; omega)
        have hdB := List.drop_eq_getElem_cons (show minLen < bsB.length by dsimp [minLen]; omega)
        rw [hdA, hdB] at hcmp
        simp only [cmpByteSlices] at hcmp
        rw [hcmp] at hq; exact hq
      · -- ¬ i < m ∧ la > lb -> return 2
        have heq : iNat = minLen := by
          have hc : ¬ (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 minLen).toNat := by assumption
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hminLt] at hc
          omega
        subst heq
        have hgtAB : bsB.length < bsA.length := by
          have hc : lb.toNat < la.toNat := by assumption
          omega
        have hdB : bsB.drop minLen = [] := List.drop_of_length_le (by dsimp [minLen]; omega)
        have hdA := List.drop_eq_getElem_cons (show minLen < bsA.length by dsimp [minLen]; omega)
        rw [hdA, hdB] at hcmp
        simp only [cmpByteSlices] at hcmp
        rw [hcmp] at hq; exact hq
      · -- ¬ i < m ∧ la = lb -> return 1
        have heq : iNat = minLen := by
          have hc : ¬ (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 minLen).toNat := by assumption
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hminLt] at hc
          omega
        subst heq
        have hnotLt : ¬ la.toNat < lb.toNat := by assumption
        have hnotGt : ¬ lb.toNat < la.toNat := by assumption
        have heqAB : bsA.length = bsB.length := by omega
        have hdA : bsA.drop minLen = [] := List.drop_of_length_le (by dsimp [minLen]; omega)
        have hdB : bsB.drop minLen = [] := List.drop_of_length_le (by dsimp [minLen]; omega)
        rw [hdA, hdB] at hcmp
        simp only [cmpByteSlices] at hcmp
        rw [hcmp] at hq; exact hq
  · intro J_m hJm
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · -- lb < la -> m = lb
      have hlt : bsB.length < bsA.length := by
        have hc : lb.toNat < la.toNat := by assumption
        omega
      have heq : lb = BitVec.ofNat 64 minLen := by
        apply BitVec.eq_of_toNat_eq
        simp [minLen, Nat.min_eq_right (Nat.le_of_lt hlt), hlb]
      rw [heq]; exact hJm (BitVec.ofNat 64 minLen, ()) m ⟨rfl, rfl⟩
    · -- ¬ lb < la -> m = la
      have hge : bsA.length ≤ bsB.length := by
        have hc : ¬ lb.toNat < la.toNat := by assumption
        omega
      have heq : la = BitVec.ofNat 64 minLen := by
        apply BitVec.eq_of_toNat_eq
        simp [minLen, Nat.min_eq_left hge, hla]
      rw [heq]; exact hJm (BitVec.ofNat 64 minLen, ()) m ⟨rfl, rfl⟩

theorem lcnf_oob_wp :
    ∀ xs m Q X, lcnfOobSpec xs m Q X → Func.wp rtR2Env lcnf_oob_body xs m Q X := by
  intro ⟨rt, dv, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, lcnf_oob_body, lcnfOobSpec] at hPre ⊢
  change LeanQbe.T.wp _ _ _ _ _
  r2_call rtR2Env_r2_inc_obj
  by_cases hnull : dv = 0#64 ∨ (dv &&& 1#64) ≠ 0#64
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hnull)] at hPre
    dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hnull)]
    r2_steps
    exact hPre
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hnull)] at hPre
    rcases hPre with ⟨obj, R, rfl, hwf, hm, hk⟩
    dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnull)]
    refine ⟨obj, R, rfl, hwf, hm, fun m' hm' => ?_⟩
    r2_steps
    exact hk m' hm'

end LeanQbe.T.LeanLCNF
