module

public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.C0StepAttr
import all Kraken.Mem
import all Kraken.Separation

/-!
# Unaligned `u16` / `u32` / `u64` Loads and Stores over `bytes`

Extension leaf over `LeanQbe.T.Logic.Bytes` providing little-endian bitvector decoding
(`bv16_ofInt_ofBytes`, `bv32_ofInt_ofBytes`, `bv64_ofInt_ofBytes`), `@[c0_load]` and
`@[c0_store]` rules for unaligned `u16`/`u32`/`u64` accesses on `bytes base bs` at `Nat`
and `BitVec 64` offsets, and the `loadVal_bytes_bool_ne` guard.
-/

set_option autoImplicit false
/-! ## Unaligned `u16` / `u32` / `u64` loads and stores over `bytes` -/

public section

namespace LeanQbe.T

open Std Std.ExtHashMap

private theorem nat_testBit_add_shl {a n s i : Nat} (ha : a < 2 ^ s) :
    (a + n * 2 ^ s).testBit i = (a ||| (n <<< s)).testBit i := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases his : i < s
  · have hns : ¬ s ≤ i := Nat.not_le_of_lt his
    simp only [hns, decide_false, Bool.false_and, Bool.or_false]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt his
    have hs : s = i + (k + 1) := by omega
    have hpow : 2 ^ s = 2 ^ i * 2 ^ (k + 1) := by rw [hs, Nat.pow_add]
    have hpow2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmul : n * 2 ^ s = (n * 2 ^ k * 2) * 2 ^ i := by rw [hpow, hpow2]; ac_rfl
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [hmul, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
      Nat.and_comm 1 _, Nat.and_two_pow_sub_one_eq_mod _ 1,
      Nat.and_comm 1 _, Nat.and_two_pow_sub_one_eq_mod _ 1,
      Nat.pow_one, Nat.add_mul_mod_self_right]
  · have hsi : s ≤ i := Nat.le_of_not_lt his
    have hai : a < 2 ^ i := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hsi)
    have ha0 : a.testBit i = false := Nat.testBit_lt_two_pow hai
    simp only [hsi, decide_true, Bool.true_and, ha0, Bool.false_or]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hsi
    have hpow : 2 ^ i = 2 ^ s * 2 ^ d := by rw [hd, Nat.pow_add]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [hpow, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
      Nat.div_eq_of_lt ha, Nat.zero_add, hd, Nat.add_sub_cancel_left]

private theorem bv_ofNat_cons_shl8 {w : Nat} (n : Nat) (b : UInt8) :
    BitVec.ofNat w (n * 256 + b.toNat) =
      BitVec.ofNat w b.toNat ||| (BitVec.ofNat w n <<< 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi,
    decide_true, Bool.true_and]
  rw [Nat.add_comm (n * 256) b.toNat, show (256 : Nat) = 2 ^ 8 from rfl,
    nat_testBit_add_shl b.toNat_lt, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi8 : i < 8
  · have hge : ¬ 8 ≤ i := by omega
    simp [hi8, hge]
  · have hge : 8 ≤ i := by omega
    have hlt : i - 8 < w := by omega
    simp [hi8, hge, hlt]

private theorem bv_ofInt_ofBytes_cons {w : Nat} (b : UInt8) (bs : List UInt8) :
    BitVec.ofInt w (Int.ofBytes (b :: bs)) =
      BitVec.ofNat w b.toNat ||| (BitVec.ofInt w (Int.ofBytes bs) <<< 8) := by
  have hge : 0 ≤ Int.ofBytes bs := Int.ofBytes_ge_zero bs
  have hge' : 0 ≤ Int.ofBytes (b :: bs) := Int.ofBytes_ge_zero (b :: bs)
  have hb1 : BitVec.ofInt w (Int.ofBytes bs) = BitVec.ofNat w (Int.ofBytes bs).toNat := by
    rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg hge]
  have hb2 : BitVec.ofInt w (Int.ofBytes (b :: bs)) =
      BitVec.ofNat w (Int.ofBytes (b :: bs)).toNat := by
    rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg hge']
  rw [hb1, hb2, Int.ofBytes_cons,
    show (Int.ofBytes bs * 256 + (b.toNat : Int)).toNat = (Int.ofBytes bs).toNat * 256 + b.toNat by
      omega]
  exact bv_ofNat_cons_shl8 (Int.ofBytes bs).toNat b

private theorem bv_shl_or {w k : Nat} (x y : BitVec w) :
    (x ||| y) <<< k = (x <<< k) ||| (y <<< k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or, hi, decide_true, Bool.true_and]
  by_cases hik : i < k
  · simp [hik]
  · have hlt : i - k < w := by omega
    simp [hik, hlt, Bool.and_or_distrib_left]

private theorem bv_shl_shl {w a b : Nat} (x : BitVec w) :
    (x <<< a) <<< b = x <<< (a + b) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases h1 : i < b
  · have h3 : i < a + b := by omega
    simp [h1, h3]
  · have h1' : i - b < w := by omega
    by_cases h2 : i - b < a
    · have h3 : i < a + b := by omega
      simp [h1, h1', h2, h3]
    · have h3 : ¬ i < a + b := by omega
      simp [h1, h1', h2, h3, show i - b - a = i - (a + b) by omega]

private theorem bv_ofInt_ofBytes_nil (w : Nat) :
    BitVec.ofInt w (Int.ofBytes []) = 0#w := rfl

private theorem bv_zero_shl {w k : Nat} : (0#w <<< k) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp

private theorem bv_or_zero_right {w : Nat} (x : BitVec w) : (x ||| 0#w) = x := BitVec.or_zero

theorem bv16_ofInt_ofBytes (b0 b1 : UInt8) :
    BitVec.ofInt 16 (Int.ofBytes [b0, b1]) =
      BitVec.ofNat 16 b0.toNat ||| (BitVec.ofNat 16 b1.toNat <<< 8) := by
  rw [bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_nil, bv_zero_shl,
    bv_or_zero_right]

theorem bv32_ofInt_ofBytes (b0 b1 b2 b3 : UInt8) :
    BitVec.ofInt 32 (Int.ofBytes [b0, b1, b2, b3]) =
      BitVec.ofNat 32 b0.toNat ||| (BitVec.ofNat 32 b1.toNat <<< 8) |||
        (BitVec.ofNat 32 b2.toNat <<< 16) ||| (BitVec.ofNat 32 b3.toNat <<< 24) := by
  rw [bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_cons,
    bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_nil, bv_zero_shl, bv_or_zero_right]
  simp only [bv_shl_or, bv_shl_shl, BitVec.or_assoc]

theorem bv64_ofInt_ofBytes (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    BitVec.ofInt 64 (Int.ofBytes [b0, b1, b2, b3, b4, b5, b6, b7]) =
      BitVec.ofNat 64 b0.toNat ||| (BitVec.ofNat 64 b1.toNat <<< 8) |||
        (BitVec.ofNat 64 b2.toNat <<< 16) ||| (BitVec.ofNat 64 b3.toNat <<< 24) |||
        (BitVec.ofNat 64 b4.toNat <<< 32) ||| (BitVec.ofNat 64 b5.toNat <<< 40) |||
        (BitVec.ofNat 64 b6.toNat <<< 48) ||| (BitVec.ofNat 64 b7.toNat <<< 56) := by
  rw [bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_cons,
    bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_cons,
    bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_cons, bv_ofInt_ofBytes_nil,
    bv_zero_shl, bv_or_zero_right]
  simp only [bv_shl_or, bv_shl_shl, BitVec.or_assoc]

private theorem toBytes_succ_bv {w : Nat} (k : Nat) (v : BitVec w) :
    Int.toBytes (k + 1) (v.toNat : Int) =
      UInt8.ofBitVec (v.setWidth 8) :: Int.toBytes k ((v >>> 8).toNat : Int) := by
  simp only [Int.toBytes, Int.take]
  have hmod : ((v.toNat : Int) % (2 : Int) ^ 8).toNat = v.toNat % 256 := by omega
  have hdiv : (v.toNat : Int) / (256 : Int) = ((v >>> 8).toNat : Int) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  rw [hdiv]
  congr 1
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  rw [hmod]
  simp [BitVec.toNat_setWidth]

private theorem bv_ushr_ushr {w a b : Nat} (x : BitVec w) : (x >>> a) >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]

private theorem toBytes_u16_eq (v : BitVec 16) :
    Int.toBytes 2 (v.toNat : Int) =
      [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8)] := by
  rw [toBytes_succ_bv, toBytes_succ_bv]; rfl

private theorem toBytes_u32_eq (v : BitVec 32) :
    Int.toBytes 4 (v.toNat : Int) =
      [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
       UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8)] := by
  rw [toBytes_succ_bv, toBytes_succ_bv, toBytes_succ_bv, toBytes_succ_bv]
  simp only [bv_ushr_ushr]; rfl

private theorem toBytes_u64_eq (v : BitVec 64) :
    Int.toBytes 8 (v.toNat : Int) =
      [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
       UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8),
       UInt8.ofBitVec ((v >>> 32).setWidth 8), UInt8.ofBitVec ((v >>> 40).setWidth 8),
       UInt8.ofBitVec ((v >>> 48).setWidth 8), UInt8.ofBitVec ((v >>> 56).setWidth 8)] := by
  rw [toBytes_succ_bv, toBytes_succ_bv, toBytes_succ_bv, toBytes_succ_bv,
    toBytes_succ_bv, toBytes_succ_bv, toBytes_succ_bv, toBytes_succ_bv]
  simp only [bv_ushr_ushr]; rfl

private theorem drop_take_2 {bs : List UInt8} {off : Nat} (h : off + 2 ≤ bs.length) :
    (bs.drop off).take 2 = [bs[off]'(by omega), bs[off + 1]'(by omega)] := by
  rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons, List.take_zero]

private theorem drop_take_4 {bs : List UInt8} {off : Nat} (h : off + 4 ≤ bs.length) :
    (bs.drop off).take 4 =
      [bs[off]'(by omega), bs[off + 1]'(by omega),
       bs[off + 2]'(by omega), bs[off + 3]'(by omega)] := by
  rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons, List.take_zero]

private theorem drop_take_8 {bs : List UInt8} {off : Nat} (h : off + 8 ≤ bs.length) :
    (bs.drop off).take 8 =
      [bs[off]'(by omega), bs[off + 1]'(by omega),
       bs[off + 2]'(by omega), bs[off + 3]'(by omega),
       bs[off + 4]'(by omega), bs[off + 5]'(by omega),
       bs[off + 6]'(by omega), bs[off + 7]'(by omega)] := by
  rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons,
    List.drop_eq_getElem_cons (by omega), List.take_succ_cons, List.take_zero]

private theorem bytes_split3 {base : BitVec 64} {bs : List UInt8} {off len : Nat}
    (hoff : off + len ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    bytes base bs =
      (Eq (((bs.drop off).take len).At (base + BitVec.ofNat 64 off)) ⋆
        (Eq ((bs.take off).At base) ⋆
          Eq ((bs.drop (off + len)).At (base + BitVec.ofNat 64 (off + len))))) := by
  have hsplit : bs = bs.take off ++ ((bs.drop off).take len ++ bs.drop (off + len)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hl1 : (bs.take off).length = off := List.length_take_of_le (by omega)
  have hl2 : ((bs.drop off).take len).length = len :=
    List.length_take_of_le (by simp only [List.length_drop]; omega)
  have hl3 : (bs.drop (off + len)).length = bs.length - (off + len) := List.length_drop
  change Eq (bs.At base) = _
  conv => lhs; rw [hsplit]
  rw [eq_append_At base (bs.take off) _ (by simp only [List.length_append, hl1, hl2, hl3]; omega),
    hl1, eq_append_At (base + BitVec.ofNat 64 off) _ _ (by simp only [hl2, hl3]; omega),
    hl2, BitVec.add_assoc, ← BitVec.ofNat_add]
  ac_rfl

private theorem bytes_replace3 {base : BitVec 64} {bs ys : List UInt8} {off len : Nat}
    (hoff : off + len ≤ bs.length) (hy : ys.length = len) (hlen : bs.length ≤ 2 ^ 64) :
    bytes base (bs.take off ++ ys ++ bs.drop (off + len)) =
      (Eq (ys.At (base + BitVec.ofNat 64 off)) ⋆
        (Eq ((bs.take off).At base) ⋆
          Eq ((bs.drop (off + len)).At (base + BitVec.ofNat 64 (off + len))))) := by
  have hl1 : (bs.take off).length = off := List.length_take_of_le (by omega)
  have hl3 : (bs.drop (off + len)).length = bs.length - (off + len) := List.length_drop
  change Eq ((bs.take off ++ ys ++ bs.drop (off + len)).At base) = _
  rw [List.append_assoc,
    eq_append_At base (bs.take off) _ (by simp only [List.length_append, hl1, hy, hl3]; omega),
    hl1, eq_append_At (base + BitVec.ofNat 64 off) _ _ (by simp only [hy, hl3]; omega),
    hy, BitVec.add_assoc, ← BitVec.ofNat_add]
  ac_rfl

private theorem loadVal_bytes_bits_aux {n : Nat} {base : BitVec 64} {bs : List UInt8}
    {off : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + (Ty.bits n).bytes ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m (.bits n) (base + BitVec.ofNat 64 off) =
      some (BitVec.ofInt n (Int.ofBytes ((bs.drop off).take (Ty.bits n).bytes))) := by
  have hl2 : ((bs.drop off).take (Ty.bits n).bytes).length = (Ty.bits n).bytes :=
    List.length_take_of_le (by simp only [List.length_drop]; omega)
  have hm' : (Eq (((bs.drop off).take (Ty.bits n).bytes).At (base + BitVec.ofNat 64 off)) ⋆
      ((Eq ((bs.take off).At base) ⋆
        Eq ((bs.drop (off + (Ty.bits n).bytes)).At
          (base + BitVec.ofNat 64 (off + (Ty.bits n).bytes)))) ⋆ R)) m := by
    rw [bytes_split3 hoff hlen] at hm; exact sep_cast hm (by ac_rfl)
  have hload := Mem.loadInt_sep _ (base + BitVec.ofNat 64 off) (Ty.bits n).bytes _ m hm'
    hl2 (by omega)
  simp only [loadVal, hload, Option.bind_some, ofBits]

private theorem store_bytes_bits_aux {n : Nat} {base : BitVec 64} {bs : List UInt8}
    {off : Nat} (v : BitVec n) {R : Mem 64 → Prop} {m : Mem 64}
    (hn : n = 8 * (Ty.bits n).bytes)
    (hoff : off + (Ty.bits n).bytes ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m (.bits n) (base + BitVec.ofNat 64 off) ∧
      (bytes base (bs.take off ++ Int.toBytes (Ty.bits n).bytes (v.toNat : Int) ++
        bs.drop (off + (Ty.bits n).bytes)) ⋆ R)
        (storeMem m (.bits n) (base + BitVec.ofNat 64 off) v) := by
  have hl2 : ((bs.drop off).take (Ty.bits n).bytes).length = (Ty.bits n).bytes :=
    List.length_take_of_le (by simp only [List.length_drop]; omega)
  have hrt : (bs.drop off).take (Ty.bits n).bytes =
      Int.toBytes (Ty.bits n).bytes (Int.ofBytes ((bs.drop off).take (Ty.bits n).bytes)) := by
    conv => rhs; arg 1; rw [← hl2]
    rw [Int.toBytes_ofBytes_all]
  have hm' : (Eq ((Int.toBytes (Ty.bits n).bytes
        (Int.ofBytes ((bs.drop off).take (Ty.bits n).bytes))).At (base + BitVec.ofNat 64 off)) ⋆
      ((Eq ((bs.take off).At base) ⋆
        Eq ((bs.drop (off + (Ty.bits n).bytes)).At
          (base + BitVec.ofNat 64 (off + (Ty.bits n).bytes)))) ⋆ R)) m := by
    rw [bytes_split3 hoff hlen, hrt] at hm
    exact sep_cast hm (by ac_rfl)
  obtain ⟨hok, hst⟩ := store_toBytes_bits (n := n) v hn (by omega) hm'
  refine ⟨hok, ?_⟩
  rw [bytes_replace3 hoff (Int.toBytes_length _ _) hlen]
  exact sep_cast hst (by ac_rfl)

/-- Unaligned little-endian `u16` load from `bytes base bs` at `base + BitVec.ofNat 64 off`. -/
@[c0_load] theorem loadVal_bytes_u16 {base : BitVec 64} {bs : List UInt8} {off : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + 2 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i16 (base + BitVec.ofNat 64 off) =
      some (BitVec.ofNat 16 (bs[off]'(by omega)).toNat |||
        (BitVec.ofNat 16 (bs[off + 1]'(by omega)).toNat <<< 8)) := by
  have h := loadVal_bytes_bits_aux (n := 16) (base := base) (bs := bs) (off := off)
    (by simpa [Ty.bytes, Ty.size] using hoff) hlen hm
  simpa only [Ty.bytes, Ty.size, i16, drop_take_2 hoff, bv16_ofInt_ofBytes] using h

/-- Unaligned little-endian `u16` load at offset `0` (`base`). -/
@[c0_load] theorem loadVal_bytes_u16_zero {base : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : 2 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i16 base =
      some (BitVec.ofNat 16 (bs[0]'(by omega)).toNat |||
        (BitVec.ofNat 16 (bs[1]'(by omega)).toNat <<< 8)) := by
  simpa using loadVal_bytes_u16 (off := 0) hoff hlen hm

/-- Unaligned little-endian `u16` load at `BitVec 64` offset `base + off`. -/
@[c0_load] theorem loadVal_bytes_u16_bv {base off : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off.toNat + 2 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i16 (base + off) =
      some (BitVec.ofNat 16 (bs[off.toNat]'(by omega)).toNat |||
        (BitVec.ofNat 16 (bs[off.toNat + 1]'(by omega)).toNat <<< 8)) := by
  have h := loadVal_bytes_u16 (off := off.toNat) hoff hlen hm
  simpa [BitVec.ofNat_toNat] using h

/-- Unaligned little-endian `u32` load from `bytes base bs` at `base + BitVec.ofNat 64 off`. -/
@[c0_load] theorem loadVal_bytes_u32 {base : BitVec 64} {bs : List UInt8} {off : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + 4 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i32 (base + BitVec.ofNat 64 off) =
      some (BitVec.ofNat 32 (bs[off]'(by omega)).toNat |||
        (BitVec.ofNat 32 (bs[off + 1]'(by omega)).toNat <<< 8) |||
        (BitVec.ofNat 32 (bs[off + 2]'(by omega)).toNat <<< 16) |||
        (BitVec.ofNat 32 (bs[off + 3]'(by omega)).toNat <<< 24)) := by
  have h := loadVal_bytes_bits_aux (n := 32) (base := base) (bs := bs) (off := off)
    (by simpa [Ty.bytes, Ty.size] using hoff) hlen hm
  simpa only [Ty.bytes, Ty.size, i32, drop_take_4 hoff, bv32_ofInt_ofBytes] using h

/-- Unaligned little-endian `u32` load at offset `0` (`base`). -/
@[c0_load] theorem loadVal_bytes_u32_zero {base : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : 4 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i32 base =
      some (BitVec.ofNat 32 (bs[0]'(by omega)).toNat |||
        (BitVec.ofNat 32 (bs[1]'(by omega)).toNat <<< 8) |||
        (BitVec.ofNat 32 (bs[2]'(by omega)).toNat <<< 16) |||
        (BitVec.ofNat 32 (bs[3]'(by omega)).toNat <<< 24)) := by
  simpa using loadVal_bytes_u32 (off := 0) hoff hlen hm

/-- Unaligned little-endian `u32` load at `BitVec 64` offset `base + off`. -/
@[c0_load] theorem loadVal_bytes_u32_bv {base off : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off.toNat + 4 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i32 (base + off) =
      some (BitVec.ofNat 32 (bs[off.toNat]'(by omega)).toNat |||
        (BitVec.ofNat 32 (bs[off.toNat + 1]'(by omega)).toNat <<< 8) |||
        (BitVec.ofNat 32 (bs[off.toNat + 2]'(by omega)).toNat <<< 16) |||
        (BitVec.ofNat 32 (bs[off.toNat + 3]'(by omega)).toNat <<< 24)) := by
  have h := loadVal_bytes_u32 (off := off.toNat) hoff hlen hm
  simpa [BitVec.ofNat_toNat] using h

/-- Unaligned little-endian `u64` load from `bytes base bs` at `base + BitVec.ofNat 64 off`. -/
@[c0_load] theorem loadVal_bytes_u64 {base : BitVec 64} {bs : List UInt8} {off : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + 8 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i64 (base + BitVec.ofNat 64 off) =
      some (BitVec.ofNat 64 (bs[off]'(by omega)).toNat |||
        (BitVec.ofNat 64 (bs[off + 1]'(by omega)).toNat <<< 8) |||
        (BitVec.ofNat 64 (bs[off + 2]'(by omega)).toNat <<< 16) |||
        (BitVec.ofNat 64 (bs[off + 3]'(by omega)).toNat <<< 24) |||
        (BitVec.ofNat 64 (bs[off + 4]'(by omega)).toNat <<< 32) |||
        (BitVec.ofNat 64 (bs[off + 5]'(by omega)).toNat <<< 40) |||
        (BitVec.ofNat 64 (bs[off + 6]'(by omega)).toNat <<< 48) |||
        (BitVec.ofNat 64 (bs[off + 7]'(by omega)).toNat <<< 56)) := by
  have h := loadVal_bytes_bits_aux (n := 64) (base := base) (bs := bs) (off := off)
    (by simpa [Ty.bytes, Ty.size] using hoff) hlen hm
  simpa only [Ty.bytes, Ty.size, i64, drop_take_8 hoff, bv64_ofInt_ofBytes] using h

/-- Unaligned little-endian `u64` load at offset `0` (`base`). -/
@[c0_load] theorem loadVal_bytes_u64_zero {base : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : 8 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i64 base =
      some (BitVec.ofNat 64 (bs[0]'(by omega)).toNat |||
        (BitVec.ofNat 64 (bs[1]'(by omega)).toNat <<< 8) |||
        (BitVec.ofNat 64 (bs[2]'(by omega)).toNat <<< 16) |||
        (BitVec.ofNat 64 (bs[3]'(by omega)).toNat <<< 24) |||
        (BitVec.ofNat 64 (bs[4]'(by omega)).toNat <<< 32) |||
        (BitVec.ofNat 64 (bs[5]'(by omega)).toNat <<< 40) |||
        (BitVec.ofNat 64 (bs[6]'(by omega)).toNat <<< 48) |||
        (BitVec.ofNat 64 (bs[7]'(by omega)).toNat <<< 56)) := by
  simpa using loadVal_bytes_u64 (off := 0) hoff hlen hm

/-- Unaligned little-endian `u64` load at `BitVec 64` offset `base + off`. -/
@[c0_load] theorem loadVal_bytes_u64_bv {base off : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off.toNat + 8 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i64 (base + off) =
      some (BitVec.ofNat 64 (bs[off.toNat]'(by omega)).toNat |||
        (BitVec.ofNat 64 (bs[off.toNat + 1]'(by omega)).toNat <<< 8) |||
        (BitVec.ofNat 64 (bs[off.toNat + 2]'(by omega)).toNat <<< 16) |||
        (BitVec.ofNat 64 (bs[off.toNat + 3]'(by omega)).toNat <<< 24) |||
        (BitVec.ofNat 64 (bs[off.toNat + 4]'(by omega)).toNat <<< 32) |||
        (BitVec.ofNat 64 (bs[off.toNat + 5]'(by omega)).toNat <<< 40) |||
        (BitVec.ofNat 64 (bs[off.toNat + 6]'(by omega)).toNat <<< 48) |||
        (BitVec.ofNat 64 (bs[off.toNat + 7]'(by omega)).toNat <<< 56)) := by
  have h := loadVal_bytes_u64 (off := off.toNat) hoff hlen hm
  simpa [BitVec.ofNat_toNat] using h

/-- Unaligned little-endian `u16` store into `bytes base bs` at `base + BitVec.ofNat 64 off`. -/
@[c0_store] theorem store_bytes_u16 {base : BitVec 64} {bs : List UInt8} {off : Nat}
    (v : BitVec 16) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + 2 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i16 (base + BitVec.ofNat 64 off) ∧
      (bytes base (bs.take off ++
        [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8)] ++
        bs.drop (off + 2)) ⋆ R)
        (storeMem m i16 (base + BitVec.ofNat 64 off) v) := by
  have h := store_bytes_bits_aux (n := 16) (base := base) (bs := bs) (off := off) v
    (by decide) (by simpa [Ty.bytes, Ty.size] using hoff) hlen hm
  change storeOk m i16 (base + BitVec.ofNat 64 off) ∧
    (bytes base (bs.take off ++ Int.toBytes 2 (v.toNat : Int) ++ bs.drop (off + 2)) ⋆ R)
      (storeMem m i16 (base + BitVec.ofNat 64 off) v) at h
  rw [toBytes_u16_eq] at h
  exact h

/-- Unaligned little-endian `u16` store at offset `0` (`base`). -/
@[c0_store] theorem store_bytes_u16_zero {base : BitVec 64} {bs : List UInt8}
    (v : BitVec 16) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : 2 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i16 base ∧
      (bytes base ([UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8)] ++
        bs.drop 2) ⋆ R)
        (storeMem m i16 base v) := by
  simpa using store_bytes_u16 (off := 0) v hoff hlen hm

/-- Unaligned little-endian `u16` store at `BitVec 64` offset `base + off`. -/
@[c0_store] theorem store_bytes_u16_bv {base off : BitVec 64} {bs : List UInt8}
    (v : BitVec 16) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off.toNat + 2 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i16 (base + off) ∧
      (bytes base (bs.take off.toNat ++
        [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8)] ++
        bs.drop (off.toNat + 2)) ⋆ R)
        (storeMem m i16 (base + off) v) := by
  have h := store_bytes_u16 (off := off.toNat) v hoff hlen hm
  simpa [BitVec.ofNat_toNat] using h

/-- Unaligned little-endian `u32` store into `bytes base bs` at `base + BitVec.ofNat 64 off`. -/
@[c0_store] theorem store_bytes_u32 {base : BitVec 64} {bs : List UInt8} {off : Nat}
    (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + 4 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i32 (base + BitVec.ofNat 64 off) ∧
      (bytes base (bs.take off ++
        [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
         UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8)] ++
        bs.drop (off + 4)) ⋆ R)
        (storeMem m i32 (base + BitVec.ofNat 64 off) v) := by
  have h := store_bytes_bits_aux (n := 32) (base := base) (bs := bs) (off := off) v
    (by decide) (by simpa [Ty.bytes, Ty.size] using hoff) hlen hm
  change storeOk m i32 (base + BitVec.ofNat 64 off) ∧
    (bytes base (bs.take off ++ Int.toBytes 4 (v.toNat : Int) ++ bs.drop (off + 4)) ⋆ R)
      (storeMem m i32 (base + BitVec.ofNat 64 off) v) at h
  rw [toBytes_u32_eq] at h
  exact h

/-- Unaligned little-endian `u32` store at offset `0` (`base`). -/
@[c0_store] theorem store_bytes_u32_zero {base : BitVec 64} {bs : List UInt8}
    (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : 4 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i32 base ∧
      (bytes base ([UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
         UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8)] ++
        bs.drop 4) ⋆ R)
        (storeMem m i32 base v) := by
  simpa using store_bytes_u32 (off := 0) v hoff hlen hm

/-- Unaligned little-endian `u32` store at `BitVec 64` offset `base + off`. -/
@[c0_store] theorem store_bytes_u32_bv {base off : BitVec 64} {bs : List UInt8}
    (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off.toNat + 4 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i32 (base + off) ∧
      (bytes base (bs.take off.toNat ++
        [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
         UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8)] ++
        bs.drop (off.toNat + 4)) ⋆ R)
        (storeMem m i32 (base + off) v) := by
  have h := store_bytes_u32 (off := off.toNat) v hoff hlen hm
  simpa [BitVec.ofNat_toNat] using h

/-- Unaligned little-endian `u64` store into `bytes base bs` at `base + BitVec.ofNat 64 off`. -/
@[c0_store] theorem store_bytes_u64 {base : BitVec 64} {bs : List UInt8} {off : Nat}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off + 8 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i64 (base + BitVec.ofNat 64 off) ∧
      (bytes base (bs.take off ++
        [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
         UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8),
         UInt8.ofBitVec ((v >>> 32).setWidth 8), UInt8.ofBitVec ((v >>> 40).setWidth 8),
         UInt8.ofBitVec ((v >>> 48).setWidth 8), UInt8.ofBitVec ((v >>> 56).setWidth 8)] ++
        bs.drop (off + 8)) ⋆ R)
        (storeMem m i64 (base + BitVec.ofNat 64 off) v) := by
  have h := store_bytes_bits_aux (n := 64) (base := base) (bs := bs) (off := off) v
    (by decide) (by simpa [Ty.bytes, Ty.size] using hoff) hlen hm
  change storeOk m i64 (base + BitVec.ofNat 64 off) ∧
    (bytes base (bs.take off ++ Int.toBytes 8 (v.toNat : Int) ++ bs.drop (off + 8)) ⋆ R)
      (storeMem m i64 (base + BitVec.ofNat 64 off) v) at h
  rw [toBytes_u64_eq] at h
  exact h

/-- Unaligned little-endian `u64` store at offset `0` (`base`). -/
@[c0_store] theorem store_bytes_u64_zero {base : BitVec 64} {bs : List UInt8}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : 8 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i64 base ∧
      (bytes base ([UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
         UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8),
         UInt8.ofBitVec ((v >>> 32).setWidth 8), UInt8.ofBitVec ((v >>> 40).setWidth 8),
         UInt8.ofBitVec ((v >>> 48).setWidth 8), UInt8.ofBitVec ((v >>> 56).setWidth 8)] ++
        bs.drop 8) ⋆ R)
        (storeMem m i64 base v) := by
  simpa using store_bytes_u64 (off := 0) v hoff hlen hm

/-- Unaligned little-endian `u64` store at `BitVec 64` offset `base + off`. -/
@[c0_store] theorem store_bytes_u64_bv {base off : BitVec 64} {bs : List UInt8}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hoff : off.toNat + 8 ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i64 (base + off) ∧
      (bytes base (bs.take off.toNat ++
        [UInt8.ofBitVec (v.setWidth 8), UInt8.ofBitVec ((v >>> 8).setWidth 8),
         UInt8.ofBitVec ((v >>> 16).setWidth 8), UInt8.ofBitVec ((v >>> 24).setWidth 8),
         UInt8.ofBitVec ((v >>> 32).setWidth 8), UInt8.ofBitVec ((v >>> 40).setWidth 8),
         UInt8.ofBitVec ((v >>> 48).setWidth 8), UInt8.ofBitVec ((v >>> 56).setWidth 8)] ++
        bs.drop (off.toNat + 8)) ⋆ R)
        (storeMem m i64 (base + off) v) := by
  have h := store_bytes_u64 (off := off.toNat) v hoff hlen hm
  simpa [BitVec.ofNat_toNat] using h

/-- Guard showing `bytes` cannot validly supply `.bool` when a byte is outside `{0, 1}`. -/
theorem loadVal_bytes_bool_ne {a : BitVec 64} {m : Mem 64} (hm : bytes a [2] m) :
    loadVal m .bool a = none := by
  have hsep : (Eq (([2] : List UInt8).At a) ⋆ emp) m := by rwa [sep_emp]
  have hld := loadBytes_sep_At (a := a) (bs := [2]) (by decide) hsep
  rw [List.length_singleton] at hld
  simp [loadVal, Mem.loadInt, hld, Int.ofBytes]

end LeanQbe.T

end
