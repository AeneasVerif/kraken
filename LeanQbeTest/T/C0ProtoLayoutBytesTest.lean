module

public import LeanQbe.T.Logic.BytesUnaligned
public import LeanQbe.T.Logic.SlabLayoutElab
public meta import LeanQbe.T.Logic.SlabLayoutElab

/-!
# Unit Tests for Unaligned `BytesUnaligned` Loads/Stores and `c0_slab_layout!` DSL

Verifies:
1. `c0_slab_layout!` generation for single-field, static multi-segment (with `pad`, `bytes`,
   and `array`), and parametric (`(nVars : Nat)`) slabs (`to_region`, `of_region_frame`,
   `load_*`, `store_*`, `lens_*`).
2. Unaligned little-endian `u16`, `u32`, and `u64` loads and stores over `bytes p bs` with
   `hlen : bs.length ≤ 2 ^ 64` and `off + k ≤ bs.length`, plus `loadVal_bytes_bool_ne`.
3. Standard axiom footprint (`≤ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.C0ProtoLayoutBytesTest

open LeanQbe.T
open Std Std.ExtHashMap

c0_slab_layout! SingleSlab where
  x : cell u32

c0_slab_layout! StaticSlab where
  tag : cell32
  _p0 : pad 4
  val : cell64
  buf : bytes[6]
  arr : array i16[3]

c0_slab_layout! ParamSlab (nVars : Nat) where
  hdr : array ptr[4]
  clauses : array_align8 i32[nVars]
  flags : bytes[8]
  scratch : region nVars

#check SingleSlab.to_region
#check SingleSlab.of_region_frame
#check StaticSlab.to_region
#check StaticSlab.of_region_frame
#check StaticSlab.load_buf_bv
#check StaticSlab.load_arr_bv_ok
#check StaticSlab.store_arr_u32_ok
#check ParamSlab.to_region
#check ParamSlab.of_region_frame
#check ParamSlab.load_clauses_u32_ok
#check ParamSlab.store_clauses_u32_ok
#check ParamSlab.lens_clauses

theorem proto_unaligned_bytes_u16
    {p : BitVec 64} {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : bs.length = 2) (v : BitVec 16) (hm : (bytes p bs ⋆ R) m) :
    loadVal m i16 p =
      some (BitVec.ofNat 16 (bs[0]'(by omega)).toNat |||
        (BitVec.ofNat 16 (bs[1]'(by omega)).toNat <<< 8)) ∧
      storeOk m i16 p ∧
      (bytes p ([UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8)] ++
        bs.drop 2) ⋆ R) (storeMem m i16 p v) := by
  have h1 := loadVal_bytes_u16_zero (by omega) (by omega) hm
  have h2 := store_bytes_u16_zero v (by omega) (by omega) hm
  exact ⟨h1, h2.1, h2.2⟩

theorem proto_unaligned_bytes_u32
    {p : BitVec 64} {bs : List UInt8} {off : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + 4 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64) (v : BitVec 32)
    (hm : (bytes p bs ⋆ R) m) :
    loadVal m i32 (p + BitVec.ofNat 64 off) =
      some (BitVec.ofNat 32 (bs[off]'(by omega)).toNat |||
        (BitVec.ofNat 32 (bs[off + 1]'(by omega)).toNat <<< 8) |||
        (BitVec.ofNat 32 (bs[off + 2]'(by omega)).toNat <<< 16) |||
        (BitVec.ofNat 32 (bs[off + 3]'(by omega)).toNat <<< 24)) ∧
      storeOk m i32 (p + BitVec.ofNat 64 off) ∧
      (bytes p (bs.take off ++
        [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
         UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8)] ++
        bs.drop (off + 4)) ⋆ R) (storeMem m i32 (p + BitVec.ofNat 64 off) v) := by
  have h1 := loadVal_bytes_u32 hoff hlen hm
  have h2 := store_bytes_u32 v hoff hlen hm
  exact ⟨h1, h2.1, h2.2⟩

theorem proto_unaligned_bytes_u64
    {p off : BitVec 64} {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off.toNat + 8 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64) (v : BitVec 64)
    (hm : (bytes p bs ⋆ R) m) :
    loadVal m i64 (p + off) =
      some (BitVec.ofNat 64 (bs[off.toNat]'(by omega)).toNat |||
        (BitVec.ofNat 64 (bs[off.toNat + 1]'(by omega)).toNat <<< 8) |||
        (BitVec.ofNat 64 (bs[off.toNat + 2]'(by omega)).toNat <<< 16) |||
        (BitVec.ofNat 64 (bs[off.toNat + 3]'(by omega)).toNat <<< 24) |||
        (BitVec.ofNat 64 (bs[off.toNat + 4]'(by omega)).toNat <<< 32) |||
        (BitVec.ofNat 64 (bs[off.toNat + 5]'(by omega)).toNat <<< 40) |||
        (BitVec.ofNat 64 (bs[off.toNat + 6]'(by omega)).toNat <<< 48) |||
        (BitVec.ofNat 64 (bs[off.toNat + 7]'(by omega)).toNat <<< 56)) ∧
      storeOk m i64 (p + off) ∧
      (bytes p (bs.take off.toNat ++
        [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
         UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8),
         UInt8.ofBitVec ((v >>> 32).setWidth 8), UInt8.ofBitVec ((v >>> 40).setWidth 8),
         UInt8.ofBitVec ((v >>> 48).setWidth 8), UInt8.ofBitVec ((v >>> 56).setWidth 8)] ++
        bs.drop (off.toNat + 8)) ⋆ R) (storeMem m i64 (p + off) v) := by
  have h1 := loadVal_bytes_u64_bv hoff hlen hm
  have h2 := store_bytes_u64_bv v hoff hlen hm
  exact ⟨h1, h2.1, h2.2⟩

theorem proto_bytes_bool_ne {a : BitVec 64} {m : Mem 64} (hm : bytes a [2] m) :
    loadVal m .bool a = none :=
  loadVal_bytes_bool_ne hm

#print axioms SingleSlab.to_region
#print axioms StaticSlab.of_region_frame
#print axioms ParamSlab.to_region
#print axioms ParamSlab.of_region_frame
#print axioms proto_unaligned_bytes_u16
#print axioms proto_unaligned_bytes_u32
#print axioms proto_unaligned_bytes_u64
#print axioms proto_bytes_bool_ne

end LeanQbeTest.T.C0ProtoLayoutBytesTest

end
