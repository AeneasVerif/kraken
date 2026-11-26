module

public import LeanQbe.T.Logic.U32
public import LeanQbe.T.Logic.MemAlgebra
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ProofKit

set_option autoImplicit false

/-!
Unit and smoke tests for `LeanQbe.T.Logic.U32` and `LeanQbe.T.Logic.MemAlgebra`, verifying
`u32_omega`, scoped `U32.c0_bv32_omega`, `storeBytes_*`, `array64_split3`, `pack64`/`repr64`,
`@[c0_load]` / `@[c0_store]` dispatch (`c0_hsteps`) over `word8Array` and `byte1Array`,
`boxNat_*`, `nodup_lt_length_le`, `list_swap_perm`, and `<= std3` axioms under
`-DwarningAsError=true`.
-/

public section

namespace LeanQbeTest.T.LogicU32MemTest

open LeanQbe.T
open LeanQbe.T.C0HeadStep
open Std.ExtHashMap
open Kraken.Bedrock2.Test

/-! ## `U32` arithmetic, wraparound, bitwise, and `u32_omega` smoke tests -/

theorem test_u32_wrap (a : UInt32) (h : a.toNat + 1 < 4294967296) :
    (a + 1).toNat = a.toNat + 1 :=
  u32_add1_toNat h

theorem test_u32_omega_basic (a b : UInt32) (h1 : a < b) (h2 : b.toNat ≤ 100) :
    a.toNat + 1 ≤ 100 := by
  u32_omega

theorem test_u32_omega_star (a : UInt8) (b : UInt32) (h : a.toNat < b.toNat) :
    b.toNat > 0 := by
  u32_omega [*]

theorem test_u32_omega_hint (x : BitVec 32) (h : x.toNat < 50) :
    (BitVec.setWidth 64 x).toNat < 100 := by
  u32_omega [h]

theorem test_bv32_omega_scoped (x : BitVec 32) (h : x < 10#32) :
    (BitVec.setWidth 64 x).toNat < 10 := by
  open scoped LeanQbe.T.U32 in
  c0_bv32_omega

theorem test_bv64_add1 (x : BitVec 64) (h : x.toNat < 1000) :
    (x + 1).toNat = x.toNat + 1 :=
  bv64_add1_toNat (by omega)

theorem test_u32_pack (b0 b1 b2 b3 : UInt8) :
    ((b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
      (b3.toUInt32 <<< 24)) >>> 16).toUInt8 = b2 :=
  (u32_pack_unpack_bytes b0 b1 b2 b3).2.2.1

theorem test_bv32_xor_self (x : BitVec 32) : (x ^^^ 1) ^^^ 1 = x :=
  bv32_xor1_self x

theorem test_bv32_tag (x : BitVec 32) (h : x.toNat < 100) :
    ((x ||| 2147483648#32) &&& 2147483647#32 = x) ∧
      ((x ||| 2147483648#32) ≠ 4294967295#32) :=
  ⟨bv32_tag_bin_mask x (by omega), bv32_tag_bin_ne_sent x (by omega)⟩

/-! ## `MemAlgebra` separation, `array64_split3`, `boxNat`, `Nodup`/`Perm` tests -/

theorem test_storeBytes_nil (m : Mem 64) (a : BitVec 64) :
    m.storeBytes a [] = m :=
  storeBytes_nil m a

theorem test_loadBytes_zero (m : Mem 64) (a : BitVec 64) :
    m.loadBytes a 0 = some [] :=
  loadBytes_zero m a

theorem test_storeBytes_region {m : Mem 64} {a : BitVec 64} {R : Mem 64 → Prop}
    (h : (region a 4 ⋆ R) m) :
    (bytes a [1, 2, 3, 4] ⋆ R) (m.storeBytes a [1, 2, 3, 4]) :=
  storeBytes_region_sep rfl h

theorem test_storeInt_region {m : Mem 64} {a : BitVec 64} {R : Mem 64 → Prop}
    (v : Int) (h : (region a 4 ⋆ R) m) :
    (bytes a (Int.toBytes 4 v) ⋆ R) (m.storeInt a 4 v) :=
  storeInt_region_sep v h

theorem test_array64_split3 (a : BitVec 64) (xs1 xs2 xs3 : List (BitVec 64)) :
    array64 a (xs1 ++ xs2 ++ xs3) =
      (array64 a xs1 ⋆ array64 (a + BitVec.ofNat 64 (8 * xs1.length)) xs2 ⋆
        array64 (a + BitVec.ofNat 64 (8 * (xs1 ++ xs2).length)) xs3) :=
  array64_split3 a xs1 xs2 xs3

theorem test_region_to_array64 {a : BitVec 64} {m : Mem 64} (hm : region a 16 m) :
    ∃ xs : List (BitVec 64), xs.length = 2 ∧ array64 a xs m :=
  region_to_array64 2 (by omega) hm

theorem test_pack64_roundtrip (lo hi : BitVec 32) :
    BitVec.truncate 32 (pack64 lo hi) = lo ∧
      BitVec.truncate 32 (pack64 lo hi >>> 32) = hi :=
  ⟨pack64_lo lo hi, pack64_hi lo hi⟩

theorem test_repr64_roundtrip (xs : List (BitVec 64)) {i j : Nat}
    (hij : i ≠ j) (hi : i / 2 < xs.length) (v : BitVec 32) :
    repr64Get (repr64Set xs i v) i = v ∧
      repr64Get (repr64Set xs i v) j = repr64Get xs j :=
  ⟨repr64Get_set_same xs hi v, repr64Get_set_ne xs hij hi v⟩

theorem test_boxNat (a b : Nat) (ha : 2 * a + 1 < 18446744073709551616)
    (hb : 2 * b + 1 < 18446744073709551616)
    (h : 2 * (a + b) + 1 < 18446744073709551616)
    (hmul : 2 * (a * b) + 1 < 18446744073709551616) :
    MemAlgebra.boxNat a + MemAlgebra.boxNat b - 1 = MemAlgebra.boxNat (a + b) ∧
      (((MemAlgebra.boxNat a >>> (1 : BitVec 64)) *
        (MemAlgebra.boxNat b >>> (1 : BitVec 64))) <<< (1 : BitVec 64)) ||| 1 =
        MemAlgebra.boxNat (a * b) :=
  ⟨boxNat_add_fast a b h, boxNat_umul_eq a b ha hb hmul⟩

theorem test_nodup_lt (l : List Nat) (n : Nat) (hnd : l.Nodup) (hb : ∀ x ∈ l, x < n) :
    l.length ≤ n :=
  nodup_lt_length_le hnd hb

theorem test_swap_perm {α : Type} (l : List α) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) :
    ((l.set i l[j]).set j l[i]).Perm l :=
  list_swap_perm l hi hj

/-! ## `@[c0_load]` / `@[c0_store]` lemma and `c0_hsteps` dispatch checks -/

theorem test_c0_word8Array_load_zero {m : Mem 64} {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} (hpos : 0 < xs.length) (h : (word8Array a xs ⋆ R) m) :
    loadVal m i64 a = some xs[0] :=
  c0_load_word8Array_zero h hpos

theorem test_c0_word8Array_load_shl3 {m : Mem 64} {a idx : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} (hi : idx.toNat < xs.length) (h : (word8Array a xs ⋆ R) m) :
    loadVal m i64 (a + (idx <<< (3 : BitVec 64))) = some xs[idx.toNat] :=
  c0_load_word8Array_shl3 h hi

theorem test_c0_byte1Array_store_zero {m : Mem 64} {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} (v : BitVec 8) (hpos : 0 < xs.length)
    (h : (byte1Array a xs ⋆ R) m) :
    storeOk m i8 a ∧
      (byte1Array a (xs.set 0 (BitVec.setWidth 64 v)) ⋆ R) (storeMem m i8 a v) :=
  c0_store_byte1Array_zero v h hpos

theorem test_c0_hsteps_word8Array_wp {Γ : Env} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hi : idx.toNat < xs.length) (h : (word8Array a xs ⋆ R) m) :
    wp (rs := [i64]) Γ (fun r m' => r = (xs[idx.toNat], ()) ∧ (word8Array a xs ⋆ R) m')
      (fun _ _ _ _ => False)
      (Expr.load i64 (Arg.var (a + (idx <<< (3 : BitVec 64)))) fun v =>
        Expr.ret (rs := [i64]) (Arg.var v, ())) m := by
  c0_hsteps
  exact ⟨rfl, h⟩

theorem test_c0_hsteps_byte1Array_store_wp {Γ : Env} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} (v : BitVec 8)
    (hpos : 0 < xs.length) (h : (byte1Array a xs ⋆ R) m) :
    wp (rs := []) Γ
      (fun r m' => r = () ∧ (byte1Array a (xs.set 0 (BitVec.setWidth 64 v)) ⋆ R) m')
      (fun _ _ _ _ => False)
      (Expr.store (t := i8) (Arg.var (t := i8) v) (Arg.var a) (Expr.ret (rs := []) ())) m := by
  c0_hsteps
  exact ⟨rfl, by assumption⟩

theorem test_c0_hsteps_int4Array_load_wp {Γ : Env} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hi : idx.toNat < xs.length) (h : (int4Array a xs ⋆ R) m) :
    wp (rs := [i32]) Γ
      (fun r m' => r = (BitVec.setWidth 32 xs[idx.toNat], ()) ∧ (int4Array a xs ⋆ R) m')
      (fun _ _ _ _ => False)
      (Expr.load i32 (Arg.var (a + (idx <<< (2 : BitVec 64)))) fun v =>
        Expr.ret (rs := [i32]) (Arg.var v, ())) m := by
  c0_hsteps
  exact ⟨rfl, h⟩

#print axioms test_u32_omega_basic
#print axioms test_bv32_omega_scoped
#print axioms test_u32_pack
#print axioms test_storeBytes_nil
#print axioms test_storeBytes_region
#print axioms test_array64_split3
#print axioms test_region_to_array64
#print axioms test_pack64_roundtrip
#print axioms test_repr64_roundtrip
#print axioms test_boxNat
#print axioms test_nodup_lt
#print axioms test_swap_perm
#print axioms test_c0_hsteps_word8Array_wp
#print axioms test_c0_hsteps_byte1Array_store_wp
#print axioms test_c0_hsteps_int4Array_load_wp

end LeanQbeTest.T.LogicU32MemTest
