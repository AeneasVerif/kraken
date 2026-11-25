module

public import LeanQbe.T.Logic.ByteArrayDecimal
public meta import Lean.Elab.Tactic

/-!
# `Codec0Kit`: Arch-Free `UInt32`/`UInt64`/`UInt8` & Binary Codec Round-Trip Toolkit

AVX-free, architecture-free helper module (`0` `Kraken.X64`, `IselVec`, `Targ`, `Amd64`,
`Arm64`, or `Kraken.AArch64` imports; strictly `std3` axioms) providing:

1. **`U32Kit`:** `UInt8`/`UInt32`/`UInt64` extensionality, subtraction/wrap-around helpers,
   little-endian byte/word bit-packing proofs, `nat_cases_le` linear case-splitting, and the
   kernel-sound `c0_bv32_omega` tactic.
2. **`CodecRoundTripKit`:** `baSlice` / `List.drop` slice algebra, generic length-prefixed
   counted list codec combinators, tail-recursive worklist encoder/decoder loop combinators,
   and `decode_enum_tag!` / `c0_decide_ite` / `decode_ite_chain` / `emit_dir_equiv!` tactics.
-/

set_option autoImplicit false

namespace LeanQbe.T.Bootstrap0.Codec0Kit

open LeanQbe.T.ByteArrayDecimal

/-! ## 1. `U32Kit`: `UInt8` / `UInt32` / `UInt64` Algebra & Bit-Packing -/

public section

theorem u8_ext {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem u32_ext {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem u8_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 8) : (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem u32_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem u64_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem u32_ofNat_eq {n : Nat} {c : UInt32} (h : n = c.toNat) : UInt32.ofNat n = c :=
  u32_ext <| by rw [u32_ofNat_toNat_lt (by rw [h]; exact c.toNat_lt), h]

theorem u32_eq_zero_of_toNat_eq_zero {x : UInt32} (h : x.toNat = 0) : x = 0 :=
  u32_ext (by simpa using h)

theorem u32_ne_zero_of_toNat_pos {x : UInt32} (h : 0 < x.toNat) : x ≠ 0 :=
  fun hz => by subst hz; simp at h

theorem u32_toNat_pos_of_ne_zero {x : UInt32} (h : x ≠ 0) : 1 ≤ x.toNat := by
  cases Nat.eq_zero_or_pos x.toNat with
  | inl hz => exact absurd (u32_eq_zero_of_toNat_eq_zero hz) h
  | inr hp => exact hp

theorem u32_ofNat_succ_sub_one {k : Nat} (hk : k + 1 < 2 ^ 32) :
    UInt32.ofNat (k + 1) ≠ 0 ∧ UInt32.ofNat (k + 1) - 1 = UInt32.ofNat k := by
  refine ⟨u32_ne_zero_of_toNat_pos (by rw [u32_ofNat_toNat_lt hk]; omega), ?_⟩
  apply u32_ext
  have h1 : (1 : UInt32) ≤ UInt32.ofNat (k + 1) := by
    rw [UInt32.le_iff_toNat_le, u32_ofNat_toNat_lt hk]; change 1 ≤ k + 1; omega
  rw [UInt32.toNat_sub_of_le _ _ h1, u32_ofNat_toNat_lt hk, u32_ofNat_toNat_lt (by omega)]
  change k + 1 - 1 = k; omega

theorem u32_sub1_toNat {rem : UInt32} {n : Nat} (h : rem.toNat = n + 1) :
    rem ≠ 0 ∧ (rem - 1).toNat = n := by
  refine ⟨u32_ne_zero_of_toNat_pos (by omega), ?_⟩
  have h1 : (1 : UInt32) ≤ rem := by rw [UInt32.le_iff_toNat_le]; change 1 ≤ rem.toNat; omega
  rw [UInt32.toNat_sub_of_le rem 1 h1, h]; rfl

theorem u32_sub_ofNat {a b : Nat} (ha : a ≤ 0xffffffff) (hba : b ≤ a) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  apply u32_ext
  have ha' := u32_ofNat_toNat_lt (by omega : a < 2 ^ 32)
  have hb' := u32_ofNat_toNat_lt (by omega : b < 2 ^ 32)
  have hle : UInt32.ofNat b ≤ UInt32.ofNat a := by
    rw [UInt32.le_iff_toNat_le, ha', hb']; exact hba
  rw [UInt32.toNat_sub_of_le _ _ hle, ha', hb', u32_ofNat_toNat_lt (by omega)]

theorem u32_sub_ofNat_toNat {fuel : UInt32} {n : Nat} (h : n ≤ fuel.toNat) :
    (fuel - UInt32.ofNat n).toNat = fuel.toNat - n := by
  have hlt := fuel.toNat_lt
  have hle : UInt32.ofNat n ≤ fuel := by
    rw [UInt32.le_iff_toNat_le, u32_ofNat_toNat_lt (by omega)]; exact h
  rw [UInt32.toNat_sub_of_le fuel (UInt32.ofNat n) hle, u32_ofNat_toNat_lt (by omega)]

theorem u32_sub1_ge {fuel : UInt32} {n : Nat} (h : 1 + n ≤ fuel.toNat) :
    n ≤ (fuel - 1).toNat := by
  rw [show (1 : UInt32) = UInt32.ofNat 1 from rfl, u32_sub_ofNat_toNat (by omega)]; omega

theorem u32_sub_sub_ofNat {fuel : UInt32} {a b : Nat} (h : a + b ≤ fuel.toNat) :
    fuel - UInt32.ofNat a - UInt32.ofNat b = fuel - UInt32.ofNat (a + b) := by
  have hlt := fuel.toNat_lt
  conv => lhs; rw [show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm]
  conv => rhs; rw [show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm]
  rw [u32_sub_ofNat (by omega) (by omega), u32_sub_ofNat (by omega) (by omega),
    u32_sub_ofNat (by omega) (by omega)]
  congr 1; omega

theorem u32_sub1_sub {fuel : UInt32} {n : Nat} (h : 1 + n ≤ fuel.toNat) :
    fuel - 1 - UInt32.ofNat n = fuel - UInt32.ofNat (1 + n) :=
  u32_sub_sub_ofNat (a := 1) (b := n) h

theorem u32_cnt_sub1_add {done : Nat} {rem : UInt32} (hrem : rem ≠ 0) :
    UInt32.ofNat done + 1 + (rem - 1) = UInt32.ofNat done + rem := by
  rw [UInt32.add_assoc]
  congr 1
  apply u32_ext
  have hpos := u32_toNat_pos_of_ne_zero hrem
  have hle : (1 : UInt32) ≤ rem := UInt32.le_iff_toNat_le.mpr hpos
  have hlt := rem.toNat_lt
  rw [UInt32.toNat_add, UInt32.toNat_sub_of_le rem 1 hle,
    show (1 : UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

theorem u32_cnt_sub1_lt {done : Nat} {rem : UInt32} (hrem : rem ≠ 0)
    (hlt : done + 1 + rem.toNat < 2 ^ 32) :
    done + 1 + 1 + (rem - 1).toNat < 2 ^ 32 := by
  have hpos := u32_toNat_pos_of_ne_zero hrem
  have hle : (1 : UInt32) ≤ rem := UInt32.le_iff_toNat_le.mpr hpos
  rw [UInt32.toNat_sub_of_le rem 1 hle, show (1 : UInt32).toNat = 1 from rfl]
  omega

theorem u8_eq_ofNat_of_le_ne {b : UInt8} {k : Nat} (hk : k < 2 ^ 8) (hle : b.toNat ≤ k)
    (hne : ∀ i, i < k → b ≠ UInt8.ofNat i) : b = UInt8.ofNat k := by
  apply u8_ext
  rw [u8_ofNat_toNat_lt hk]
  cases Nat.lt_or_eq_of_le hle with
  | inl h => exact absurd UInt8.ofNat_toNat.symm (hne b.toNat h)
  | inr h => exact h

theorem nat_cases_le_step {P : Nat → Prop} {n k : Nat} (hle : n ≤ k + 1)
    (hk : P (k + 1)) (hrest : n ≤ k → P n) : P n :=
  if heq : n = k + 1 then heq ▸ hk else hrest (by omega)

theorem nat_cases_le_zero {P : Nat → Prop} {n : Nat} (hle : n ≤ 0) (h0 : P 0) : P n :=
  (Nat.le_zero.mp hle) ▸ h0

theorem u8_cases_le {P : UInt8 → Prop} (b : UInt8) (k : Nat) (hk : b.toNat ≤ k)
    (h : ∀ n, n ≤ k → P (UInt8.ofNat n)) : P b := by
  rw [← UInt8.ofNat_toNat (x := b)]
  exact h b.toNat hk

private theorem testBit_u32_shl (x k : UInt32) (hk : k.toNat < 32) (i : Nat) :
    (x <<< k).toNat.testBit i =
      (decide (i < 32) && decide (k.toNat ≤ i) && x.toNat.testBit (i - k.toNat)) := by
  rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hk]
  change ((x.toNat <<< k.toNat) % 2 ^ 32).testBit i = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases hi : i < 32 <;> by_cases hki : k.toNat ≤ i <;> simp [hi, hki]

private theorem testBit_u32_shr (x k : UInt32) (hk : k.toNat < 32) (i : Nat) :
    (x >>> k).toNat.testBit i = x.toNat.testBit (k.toNat + i) := by
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.testBit_shiftRight]

private theorem testBit_u32_toUInt8 (x : UInt32) (i : Nat) :
    x.toUInt8.toNat.testBit i = (decide (i < 8) && x.toNat.testBit i) := by
  rw [UInt32.toNat_toUInt8]; exact Nat.testBit_mod_two_pow x.toNat 8 i

private theorem testBit_u64_shl (x k : UInt64) (hk : k.toNat < 64) (i : Nat) :
    (x <<< k).toNat.testBit i =
      (decide (i < 64) && decide (k.toNat ≤ i) && x.toNat.testBit (i - k.toNat)) := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk]
  change ((x.toNat <<< k.toNat) % 2 ^ 64).testBit i = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases hi : i < 64 <;> by_cases hki : k.toNat ≤ i <;> simp [hi, hki]

private theorem testBit_u64_shr (x k : UInt64) (hk : k.toNat < 64) (i : Nat) :
    (x >>> k).toNat.testBit i = x.toNat.testBit (k.toNat + i) := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.testBit_shiftRight]

private theorem testBit_u64_toUInt32 (x : UInt64) (i : Nat) :
    x.toUInt32.toNat.testBit i = (decide (i < 32) && x.toNat.testBit i) := by
  rw [UInt64.toNat_toUInt32]; exact Nat.testBit_mod_two_pow x.toNat 32 i

private theorem testBit_u8_ge8 (b : UInt8) {i : Nat} (hi : 8 ≤ i) :
    b.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by omega) hi))

private theorem testBit_u32_ge32 (x : UInt32) {i : Nat} (hi : 32 ≤ i) :
    x.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by omega) hi))

private theorem testBit_u64_ge64 (x : UInt64) {i : Nat} (hi : 64 ≤ i) :
    x.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by omega) hi))

private theorem testBit_u32_pack4 (b0 b1 b2 b3 : UInt8) (i : Nat) :
    ((b0.toUInt32 ||| (b1.toUInt32 <<< 8)) |||
      ((b2.toUInt32 ||| (b3.toUInt32 <<< 8)) <<< 16)).toNat.testBit i =
    if i < 8 then b0.toNat.testBit i
    else if i < 16 then b1.toNat.testBit (i - 8)
    else if i < 24 then b2.toNat.testBit (i - 16)
    else if i < 32 then b3.toNat.testBit (i - 24)
    else false := by
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have h16 : (16 : UInt32).toNat = 16 := rfl
  simp only [UInt32.toNat_or, Nat.testBit_or, testBit_u32_shl _ 16 (by decide),
    testBit_u32_shl _ 8 (by decide), UInt8.toNat_toUInt32, h8, h16]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
      32 ≤ i by omega) with h0 | ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | h4
  · simp [h0, show ¬ (8 ≤ i) by omega, show ¬ (16 ≤ i) by omega]
  · simp [show ¬ (i < 8) by omega, h1a, h1b, show i < 32 by omega, show ¬ (16 ≤ i) by omega,
      testBit_u8_ge8 b0 (i := i) h1a]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, h2a, h2b, show i < 32 by omega,
      show i - 16 < 32 by omega, show ¬ (8 ≤ i - 16) by omega,
      testBit_u8_ge8 b0 (i := i) (by omega), testBit_u8_ge8 b1 (i := i - 8) (by omega)]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, show ¬ (i < 24) by omega, h3b,
      show i - 16 < 32 by omega, show 8 ≤ i - 16 by omega, show 16 ≤ i by omega,
      show i - 16 - 8 = i - 24 by omega, testBit_u8_ge8 b0 (i := i) (by omega),
      testBit_u8_ge8 b1 (i := i - 8) (by omega), testBit_u8_ge8 b2 (i := i - 16) (by omega)]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, show ¬ (i < 24) by omega,
      show ¬ (i < 32) by omega, testBit_u8_ge8 b0 (i := i) (by omega),
      testBit_u8_ge8 b1 (i := i - 8) (by omega)]

theorem u32_pack_unpack_bytes (b0 b1 b2 b3 : UInt8) :
    let lo := b0.toUInt32 ||| (b1.toUInt32 <<< 8)
    let hi := b2.toUInt32 ||| (b3.toUInt32 <<< 8)
    let v := lo ||| (hi <<< 16)
    v.toUInt8 = b0 ∧ (v >>> 8).toUInt8 = b1 ∧
      (v >>> 16).toUInt8 = b2 ∧ (v >>> 24).toUInt8 = b3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (
    apply u8_ext; apply Nat.eq_of_testBit_eq; intro i
    simp only [testBit_u32_toUInt8, testBit_u32_shr _ 8 (by decide),
      testBit_u32_shr _ 16 (by decide), testBit_u32_shr _ 24 (by decide), testBit_u32_pack4]
    have h8 : (8 : UInt32).toNat = 8 := rfl
    have h16 : (16 : UInt32).toNat = 16 := rfl
    have h24 : (24 : UInt32).toNat = 24 := rfl
    by_cases hi : i < 8
    · simp [hi, h8, h16, h24, show ¬ (8 + i < 8) by omega, show 8 + i < 16 by omega,
        show ¬ (16 + i < 8) by omega, show ¬ (16 + i < 16) by omega, show 16 + i < 24 by omega,
        show ¬ (24 + i < 8) by omega, show ¬ (24 + i < 16) by omega,
        show ¬ (24 + i < 24) by omega, show 24 + i < 32 by omega]
    · simp [hi, testBit_u8_ge8 _ (i := i) (Nat.le_of_not_lt hi)])

theorem u32_of_u8_pack (v : UInt32) :
    (v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8)) |||
      (((v >>> 16).toUInt8.toUInt32 ||| ((v >>> 24).toUInt8.toUInt32 <<< 8)) <<< 16) = v := by
  apply u32_ext; apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_u32_pack4]
  simp only [testBit_u32_toUInt8, testBit_u32_shr _ 8 (by decide),
    testBit_u32_shr _ 16 (by decide), testBit_u32_shr _ 24 (by decide)]
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have h16 : (16 : UInt32).toNat = 16 := rfl
  have h24 : (24 : UInt32).toNat = 24 := rfl
  rw [h8, h16, h24]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
      32 ≤ i by omega) with h0 | ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | h4
  · simp [h0]
  · simp [show ¬ (i < 8) by omega, h1b, show i - 8 < 8 by omega, Nat.add_sub_cancel' h1a]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, h2b, show i - 16 < 8 by omega,
      Nat.add_sub_cancel' h2a]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, show ¬ (i < 24) by omega, h3b,
      show i - 24 < 8 by omega, Nat.add_sub_cancel' h3a]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, show ¬ (i < 24) by omega,
      show ¬ (i < 32) by omega, testBit_u32_ge32 v (i := i) h4]

theorem u64_pack_unpack_u32 (lo hi : UInt32) :
    let v := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
    v.toUInt32 = lo ∧ (v >>> 32).toUInt32 = hi := by
  refine ⟨?_, ?_⟩ <;> (
    apply u32_ext; apply Nat.eq_of_testBit_eq; intro i
    simp only [testBit_u64_toUInt32, testBit_u64_shr _ 32 (by decide), UInt64.toNat_or,
      Nat.testBit_or, testBit_u64_shl _ 32 (by decide), UInt32.toNat_toUInt64]
    have h32 : (32 : UInt64).toNat = 32 := rfl; rw [h32]
    by_cases hi32 : i < 32
    · simp [hi32, show ¬ (32 ≤ i) by omega, show 32 + i < 64 by omega,
        testBit_u32_ge32 lo (i := 32 + i) (by omega)]
    · simp [hi32, testBit_u32_ge32 _ (i := i) (Nat.le_of_not_lt hi32)])

theorem u64_of_u32_pack (v : UInt64) :
    v.toUInt32.toUInt64 ||| ((v >>> 32).toUInt32.toUInt64 <<< 32) = v := by
  apply u64_ext; apply Nat.eq_of_testBit_eq; intro i
  simp only [UInt64.toNat_or, Nat.testBit_or, testBit_u64_shl _ 32 (by decide),
    UInt32.toNat_toUInt64, testBit_u64_toUInt32, testBit_u64_shr _ 32 (by decide)]
  have h32 : (32 : UInt64).toNat = 32 := rfl; rw [h32]
  rcases (show i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ 64 ≤ i by omega) with h0 | ⟨h1a, h1b⟩ | h2
  · simp [h0, show ¬ (32 ≤ i) by omega]
  · simp [show ¬ (i < 32) by omega, h1a, h1b, show i - 32 < 32 by omega, Nat.add_sub_cancel' h1a]
  · simp [show ¬ (i < 32) by omega, show ¬ (i < 64) by omega, testBit_u64_ge64 v (i := i) h2]

end

/-! ## 2. `CodecRoundTripKit`: Byte-Slice, List & Worklist Loop Combinators -/

public section

@[expose] def baSlice (ba : ByteArray) (p0 p1 : Nat) : List UInt8 :=
  (ba.data.toList.drop p0).take (p1 - p0)

theorem ba_data_toList_length (ba : ByteArray) : ba.data.toList.length = ba.size := by
  cases ba; dsimp only [ByteArray.size]; exact Array.length_toList

theorem ba_emptyWithCapacity_data_toList (c : Nat) :
    (ByteArray.emptyWithCapacity c).data.toList = [] := rfl

theorem drop_pos_add (l : List UInt8) (a b : Nat) :
    l.drop (a + b) = (l.drop a).drop b := by rw [List.drop_drop, Nat.add_comm]

theorem drop_cons_step {ba : ByteArray} {pos : Nat} {b : UInt8} {rest : List UInt8}
    (h : ba.data.toList.drop pos = b :: rest) :
    ba.data.toList.drop (pos + 1) = rest := by
  rw [drop_pos_add, h]; rfl

theorem drop_append_step {ba : ByteArray} {pos : Nat} {xs rest : List UInt8}
    (h : ba.data.toList.drop pos = xs ++ rest) :
    ba.data.toList.drop (pos + xs.length) = rest := by
  rw [drop_pos_add, h, List.drop_left]

theorem drop_eq_cons_iff (ba : ByteArray) (pos : Nat) (b : UInt8) (rest : List UInt8) :
    (∃ (h : pos < ba.size), ba[pos]'h = b ∧ ba.data.toList.drop (pos + 1) = rest) ↔
      ba.data.toList.drop pos = b :: rest := by
  constructor
  · rintro ⟨h, hb, hdrop⟩
    have hlen : pos < ba.data.toList.length := by rw [ba_data_toList_length]; exact h
    have hget : ba[pos]'h = ba.data.toList[pos]'hlen := rfl
    rw [List.drop_eq_getElem_cons hlen, hdrop, ← hget, hb]
  · intro hdrop
    have hlen : pos < ba.data.toList.length := by
      cases Nat.lt_or_ge pos ba.data.toList.length with
      | inl h => exact h | inr h => rw [List.drop_eq_nil_of_le h] at hdrop; cases hdrop
    have h : pos < ba.size := by rw [← ba_data_toList_length]; exact hlen
    refine ⟨h, ?_, drop_cons_step hdrop⟩
    have hcons := List.drop_eq_getElem_cons hlen; rw [hdrop] at hcons
    injection hcons with hhead _; exact hhead.symm

theorem baSlice_zero_self (ba : ByteArray) : baSlice ba 0 ba.size = ba.data.toList := by
  dsimp only [baSlice]; rw [List.drop_zero, Nat.sub_zero, ← ba_data_toList_length, List.take_length]

theorem baSlice_self (ba : ByteArray) (p : Nat) : baSlice ba p p = [] := by
  dsimp only [baSlice]; rw [Nat.sub_self, List.take_zero]

theorem baSlice_trans {ba : ByteArray} {p0 p1 p2 : Nat}
    (h01 : p0 ≤ p1) (h12 : p1 ≤ p2) :
    baSlice ba p0 p2 = baSlice ba p0 p1 ++ baSlice ba p1 p2 := by
  dsimp only [baSlice]
  have hdrop : ba.data.toList.drop p1 = (ba.data.toList.drop p0).drop (p1 - p0) := by
    rw [← drop_pos_add, Nat.add_sub_cancel' h01]
  rw [hdrop, (by omega : p2 - p0 = (p1 - p0) + (p2 - p1)), List.take_add]

theorem baSlice_cat {ba : ByteArray} {p0 p1 p2 : Nat} {xs ys : List UInt8}
    (h01 : p0 ≤ p1) (h12 : p1 ≤ p2)
    (hs1 : baSlice ba p0 p1 = xs) (hs2 : baSlice ba p1 p2 = ys) :
    baSlice ba p0 p2 = xs ++ ys := by
  rw [baSlice_trans h01 h12, hs1, hs2]

theorem baSlice_of_drop_prefix {ba : ByteArray} {pos : Nat} {xs rest : List UInt8}
    (hdrop : ba.data.toList.drop pos = xs ++ rest) :
    baSlice ba pos (pos + xs.length) = xs ∧ ba.data.toList.drop (pos + xs.length) = rest :=
  ⟨by dsimp only [baSlice]; rw [hdrop, Nat.add_sub_cancel_left, List.take_left],
    drop_append_step hdrop⟩

theorem dite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a : p → α} {b : ¬ p → α}
    (h : p) : (if h' : p then a h' else b h') = a h := by
  cases ‹Decidable p› with | isTrue _ => rfl | isFalse hn => exact absurd h hn

theorem dite_false_eq {p : Prop} [Decidable p] {α : Sort _} {a : p → α} {b : ¬ p → α}
    (h : ¬ p) : (if h' : p then a h' else b h') = b h := by
  cases ‹Decidable p› with | isTrue hp => exact absurd hp h | isFalse _ => rfl

theorem ite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : p) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with | isTrue _ => rfl | isFalse hn => exact absurd h hn

theorem ite_false_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with | isTrue hp => exact absurd hp h | isFalse _ => rfl

theorem ite_false_beq {α : Type _} [BEq α] [LawfulBEq α] {x y : α} {β : Sort _} {a b : β}
    (hne : x ≠ y) : (if (x == y) = true then a else b) = b :=
  ite_false_eq fun hb => hne (beq_iff_eq.mp hb)

/-! ### Generic Length, Reverse, Counted List & Worklist Loop Combinators -/

theorem lenU32_eq_of_steps {α : Type} (lenFn : List α → UInt32 → UInt32)
    (hNil : ∀ acc, lenFn [] acc = acc)
    (hCons : ∀ x xs acc, lenFn (x :: xs) acc = lenFn xs (acc + 1)) :
    ∀ (xs : List α) (acc : UInt32), lenFn xs acc = acc + UInt32.ofNat xs.length
  | [], acc => by rw [hNil, List.length_nil]; exact (UInt32.add_zero acc).symm
  | x :: xs, acc => by
    rw [hCons, lenU32_eq_of_steps lenFn hNil hCons xs (acc + 1),
      List.length_cons, Nat.add_comm, UInt32.ofNat_add, UInt32.add_assoc]; rfl

theorem revList_eq_of_steps {α : Type} (revFn : List α → List α → List α)
    (hNil : ∀ acc, revFn [] acc = acc)
    (hCons : ∀ x xs acc, revFn (x :: xs) acc = revFn xs (x :: acc)) :
    ∀ (xs acc : List α), revFn xs acc = xs.reverse ++ acc
  | [], acc => hNil acc
  | x :: xs, acc => by
    rw [hCons, revList_eq_of_steps revFn hNil hCons xs (x :: acc),
      List.reverse_cons, List.append_assoc]; rfl

theorem encodeListLoop_bytes_of_steps {α : Type}
    (encLoop : ByteArray → List α → ByteArray) (encElem : ByteArray → α → ByteArray)
    (elemBytes : α → List UInt8) (seqBytes : List α → List UInt8)
    (hNil : ∀ ba, encLoop ba [] = ba)
    (hCons : ∀ ba x xs, encLoop ba (x :: xs) = encLoop (encElem ba x) xs)
    (hElem : ∀ ba x, (encElem ba x).data.toList = ba.data.toList ++ elemBytes x)
    (hSeqNil : seqBytes [] = [])
    (hSeqCons : ∀ x xs, seqBytes (x :: xs) = elemBytes x ++ seqBytes xs) :
    ∀ (xs : List α) (ba : ByteArray),
      (encLoop ba xs).data.toList = ba.data.toList ++ seqBytes xs
  | [], ba => by rw [hNil, hSeqNil, List.append_nil]
  | x :: xs, ba => by
    rw [hCons, encodeListLoop_bytes_of_steps encLoop encElem elemBytes seqBytes
      hNil hCons hElem hSeqNil hSeqCons xs (encElem ba x), hElem, hSeqCons, List.append_assoc]

theorem decodeListLoop_of_bytes_of_steps {α Res : Type}
    (mkOk : List α → Nat → Res)
    (decLoop : ByteArray → Nat → UInt32 → List α → Res)
    (decElem : ByteArray → Nat → α → Nat → Prop)
    (revFn : List α → List α → List α)
    (elemBytes : α → List UInt8) (seqBytes : List α → List UInt8)
    (elemOk : α → Prop)
    (hDone : ∀ ba pos acc, decLoop ba pos 0 acc = mkOk (revFn acc []) pos)
    (hStep : ∀ ba pos rem acc x pos1, rem ≠ 0 → decElem ba pos x pos1 →
      decLoop ba pos rem acc = decLoop ba pos1 (rem - 1) (x :: acc))
    (hRev : ∀ xs acc, revFn xs acc = xs.reverse ++ acc)
    (hSeqNil : seqBytes [] = [])
    (hSeqCons : ∀ x xs, seqBytes (x :: xs) = elemBytes x ++ seqBytes xs)
    (hDec : ∀ ba pos x rest, elemOk x →
      ba.data.toList.drop pos = elemBytes x ++ rest →
      decElem ba pos x (pos + (elemBytes x).length))
    (ba : ByteArray) :
    ∀ (xs acc : List α) (pos : Nat) (rem : UInt32) (rest : List UInt8),
      rem.toNat = xs.length → (∀ x ∈ xs, elemOk x) →
      ba.data.toList.drop pos = seqBytes xs ++ rest →
      decLoop ba pos rem acc = mkOk (acc.reverse ++ xs) (pos + (seqBytes xs).length)
  | [], acc, pos, rem, _, hlen, _, _ => by
    have hz : rem = 0 := u32_ext (by simpa using hlen)
    subst hz; rw [hDone, hRev, List.append_nil, hSeqNil, List.length_nil, Nat.add_zero]
  | x :: xs, acc, pos, rem, rest, hlen, hbx, hdrop => by
    obtain ⟨hne, hrem1⟩ := u32_sub1_toNat (by simpa using hlen)
    rw [hSeqCons] at hdrop
    have hd1 : ba.data.toList.drop (pos + (elemBytes x).length) = seqBytes xs ++ rest := by
      rw [drop_pos_add, hdrop, List.append_assoc, List.drop_left]
    have hde := hDec ba pos x (seqBytes xs ++ rest) (hbx x (List.mem_cons_self ..))
      (by simpa [List.append_assoc] using hdrop)
    rw [hStep ba pos rem acc x (pos + (elemBytes x).length) hne hde,
      decodeListLoop_of_bytes_of_steps mkOk decLoop decElem revFn elemBytes seqBytes
        elemOk hDone hStep hRev hSeqNil hSeqCons hDec ba xs (x :: acc)
        (pos + (elemBytes x).length) (rem - 1) rest hrem1
        (fun y hy => hbx y (List.mem_cons_of_mem x hy)) hd1]
    rw [hSeqCons, List.length_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, Nat.add_assoc]

theorem decodeListLoop_ok_bytes_of_steps {α Res : Type}
    (mkOk : List α → Nat → Res)
    (decLoop : ByteArray → Nat → UInt32 → List α → Res)
    (revFn : List α → List α → List α)
    (elemBytes : α → List UInt8) (seqBytes : List α → List UInt8)
    (elemOk : α → Prop)
    (hZero : ∀ ba pos acc res pos',
      decLoop ba pos 0 acc = mkOk res pos' → res = revFn acc [] ∧ pos' = pos)
    (hSucc : ∀ ba pos rem acc res pos', rem ≠ 0 →
      decLoop ba pos rem acc = mkOk res pos' →
      ∃ x p1, pos ≤ p1 ∧ (pos ≤ ba.size → p1 ≤ ba.size) ∧ elemOk x ∧
        baSlice ba pos p1 = elemBytes x ∧ decLoop ba p1 (rem - 1) (x :: acc) = mkOk res pos')
    (hRev : ∀ xs acc, revFn xs acc = xs.reverse ++ acc)
    (hSeqNil : seqBytes [] = [])
    (hSeqCons : ∀ x xs, seqBytes (x :: xs) = elemBytes x ++ seqBytes xs)
    (ba : ByteArray) :
    ∀ (n pos : Nat) (rem : UInt32) (acc res : List α) (pos' : Nat),
      rem.toNat = n → decLoop ba pos rem acc = mkOk res pos' →
      pos ≤ pos' ∧ (pos ≤ ba.size → pos' ≤ ba.size) ∧
        ∃ tail : List α, tail.length = n ∧ res = acc.reverse ++ tail ∧
          (∀ x ∈ tail, elemOk x) ∧ baSlice ba pos pos' = seqBytes tail
  | 0, pos, rem, acc, res, pos', hn, h => by
    have hz : rem = 0 := u32_ext (by simpa using hn)
    subst hz
    obtain ⟨rfl, rfl⟩ := hZero ba pos acc res pos' h
    rw [hRev, List.append_nil]
    exact ⟨Nat.le_refl _, fun hp => hp, [], rfl, (List.append_nil _).symm,
      (fun _ hc => by cases hc), by rw [baSlice_self, hSeqNil]⟩
  | n + 1, pos, rem, acc, res, pos', hn, h => by
    obtain ⟨hne, hrem1⟩ := u32_sub1_toNat hn
    obtain ⟨x, p1, h01, h1s, hbx, hs1, hnext⟩ := hSucc ba pos rem acc res pos' hne h
    obtain ⟨h12, h2s, tail, hlen, hres, hbt, hs2⟩ :=
      decodeListLoop_ok_bytes_of_steps mkOk decLoop revFn elemBytes seqBytes elemOk
        hZero hSucc hRev hSeqNil hSeqCons ba n p1 (rem - 1) (x :: acc) res pos' hrem1 hnext
    refine ⟨Nat.le_trans h01 h12, fun hp => h2s (h1s hp), x :: tail, by simp [hlen], ?_, ?_, ?_⟩
    · rw [hres, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro y hy; cases hy with | head => exact hbx | tail _ hy' => exact hbt y hy'
    · rw [baSlice_cat h01 h12 hs1 hs2, hSeqCons]

theorem encodeList_bytes_of_steps {α : Type}
    (encList : ByteArray → List α → ByteArray) (encLoop : ByteArray → List α → ByteArray)
    (encU32 : ByteArray → UInt32 → ByteArray) (lenFn : List α → UInt32 → UInt32)
    (u32B : UInt32 → List UInt8) (seqB : List α → List UInt8) (listB : List α → List UInt8)
    (hDef : ∀ ba xs, encList ba xs = encLoop (encU32 ba (lenFn xs 0)) xs)
    (hLoop : ∀ xs ba, (encLoop ba xs).data.toList = ba.data.toList ++ seqB xs)
    (hU32 : ∀ ba v, (encU32 ba v).data.toList = ba.data.toList ++ u32B v)
    (hLen : ∀ xs acc, lenFn xs acc = acc + UInt32.ofNat xs.length)
    (hList : ∀ xs, listB xs = u32B (UInt32.ofNat xs.length) ++ seqB xs)
    (ba : ByteArray) (xs : List α) :
    (encList ba xs).data.toList = ba.data.toList ++ listB xs := by
  rw [hDef, hLoop, hU32, hLen, UInt32.zero_add, hList, List.append_assoc]

theorem decodeList_of_bytes_of_steps {α Res : Type}
    (mkOk : List α → Nat → Res)
    (decList : ByteArray → Nat → Res)
    (decLoop : ByteArray → Nat → UInt32 → List α → Res)
    (decU32 : ByteArray → Nat → UInt32 → Nat → Prop)
    (u32B : UInt32 → List UInt8) (seqB : List α → List UInt8) (listB : List α → List UInt8)
    (elemOk : α → Prop)
    (hDef : ∀ ba pos v, decU32 ba pos v (pos + 4) →
      decList ba pos = decLoop ba (pos + 4) v [])
    (hU32 : ∀ ba pos v rest, ba.data.toList.drop pos = u32B v ++ rest →
      decU32 ba pos v (pos + 4))
    (hLoop : ∀ ba xs acc pos rem rest,
      rem.toNat = xs.length → (∀ x ∈ xs, elemOk x) →
      ba.data.toList.drop pos = seqB xs ++ rest →
      decLoop ba pos rem acc = mkOk (acc.reverse ++ xs) (pos + (seqB xs).length))
    (hU32Len : ∀ v, (u32B v).length = 4)
    (hList : ∀ xs, listB xs = u32B (UInt32.ofNat xs.length) ++ seqB xs)
    (ba : ByteArray) (pos : Nat) (xs : List α) (rest : List UInt8)
    (hb : xs.length < 2 ^ 32) (hbx : ∀ x ∈ xs, elemOk x)
    (h : ba.data.toList.drop pos = listB xs ++ rest) :
    decList ba pos = mkOk xs (pos + (listB xs).length) := by
  rw [hList, List.append_assoc] at h
  have hd1 : ba.data.toList.drop (pos + 4) = seqB xs ++ rest := by
    have h4 : (u32B (UInt32.ofNat xs.length)).length = 4 := hU32Len _
    rw [← h4, drop_append_step h]
  have hu := hU32 ba pos (UInt32.ofNat xs.length) (seqB xs ++ rest) h
  rw [hDef ba pos (UInt32.ofNat xs.length) hu,
    hLoop ba xs [] (pos + 4) (UInt32.ofNat xs.length) rest (u32_ofNat_toNat_lt hb) hbx hd1]
  rw [List.reverse_nil, List.nil_append, hList, List.length_append, hU32Len, Nat.add_assoc]

theorem decodeList_ok_bytes_of_steps {α Res : Type}
    (mkOk : List α → Nat → Res)
    (decList : ByteArray → Nat → Res)
    (decLoop : ByteArray → Nat → UInt32 → List α → Res)
    (decU32Ok : ByteArray → Nat → UInt32 → Nat → Prop)
    (u32B : UInt32 → List UInt8) (seqB : List α → List UInt8) (listB : List α → List UInt8)
    (elemOk : α → Prop)
    (hMatch : ∀ ba pos res pos', decList ba pos = mkOk res pos' →
      ∃ cnt p1, decU32Ok ba pos cnt p1 ∧ decLoop ba p1 cnt [] = mkOk res pos')
    (hU32 : ∀ ba pos cnt p1, decU32Ok ba pos cnt p1 →
      pos ≤ p1 ∧ p1 ≤ ba.size ∧ p1 = pos + 4 ∧ baSlice ba pos p1 = u32B cnt)
    (hLoop : ∀ ba n pos rem acc res pos',
      rem.toNat = n → decLoop ba pos rem acc = mkOk res pos' →
      pos ≤ pos' ∧ (pos ≤ ba.size → pos' ≤ ba.size) ∧
        ∃ tail : List α, tail.length = n ∧ res = acc.reverse ++ tail ∧
          (∀ x ∈ tail, elemOk x) ∧ baSlice ba pos pos' = seqB tail)
    (hList : ∀ xs, listB xs = u32B (UInt32.ofNat xs.length) ++ seqB xs)
    (ba : ByteArray) (pos : Nat) (xs : List α) (pos' : Nat)
    (h : decList ba pos = mkOk xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧
      (∀ x ∈ xs, elemOk x) ∧ baSlice ba pos pos' = listB xs := by
  obtain ⟨cnt, p1, h32, hlp⟩ := hMatch ba pos xs pos' h
  obtain ⟨h01, h1s, hp1, hs1⟩ := hU32 ba pos cnt p1 h32
  subst hp1
  obtain ⟨h12, h2s, tail, hlen, hres, hbt, hs2⟩ :=
    hLoop ba cnt.toNat (pos + 4) cnt [] xs pos' rfl hlp
  rw [List.reverse_nil, List.nil_append] at hres
  subst xs
  refine ⟨by omega, h2s h1s, by rw [hlen]; exact cnt.toNat_lt, hbt, ?_⟩
  rw [baSlice_cat (by omega) h12 hs1 hs2, hList, u32_ofNat_eq hlen]

theorem worklist_enc_bytes_of_steps {Item : Type}
    (workFn : ByteArray → List Item → ByteArray)
    (stepFn : ByteArray → Item → List Item → ByteArray × List Item)
    (weight : List Item → Nat) (encBytes : List Item → List UInt8)
    (hNil : ∀ ba, workFn ba [] = ba)
    (hCons : ∀ ba item rest, workFn ba (item :: rest) =
      let s := stepFn ba item rest; workFn s.1 s.2)
    (hEncNil : encBytes [] = [])
    (hLt : ∀ ba item rest, weight (stepFn ba item rest).2 < weight (item :: rest))
    (hStep : ∀ ba item rest,
      (stepFn ba item rest).1.data.toList ++ encBytes (stepFn ba item rest).2 =
        ba.data.toList ++ encBytes (item :: rest)) :
    ∀ (w : Nat) (work : List Item) (ba : ByteArray),
      weight work = w → (workFn ba work).data.toList = ba.data.toList ++ encBytes work
  | _, [], ba, _ => by rw [hNil, hEncNil, List.append_nil]
  | w, item :: rest, ba, hw => by
    have hlt : weight (stepFn ba item rest).2 < w := by rw [← hw]; exact hLt ba item rest
    have ih := worklist_enc_bytes_of_steps workFn stepFn weight encBytes hNil hCons hEncNil hLt
      hStep (weight (stepFn ba item rest).2) (stepFn ba item rest).2
      (stepFn ba item rest).1 rfl
    rw [hCons, ih, hStep]
termination_by w => w

theorem workloop_lin_push_of_steps {α φ ρ : Type}
    (loop : UInt32 → ByteArray → Nat → List φ → ρ)
    (applyResult : ByteArray → Nat → α → List φ → UInt32 → ρ)
    (nodes : α → Nat) (bytes : α → List UInt8)
    {ba : ByteArray} {pos pos1 : Nat} {f : φ} {t k : α}
    {frames : List φ} {fuel : UInt32}
    (hf : 1 + nodes k ≤ fuel.toNat)
    (hnodes : nodes t = 1 + nodes k)
    (hstep : loop fuel ba pos frames = loop (fuel - 1) ba pos1 (f :: frames))
    (hih : loop (fuel - 1) ba pos1 (f :: frames) =
      applyResult ba (pos1 + (bytes k).length) k (f :: frames) (fuel - 1))
    (happly : applyResult ba (pos1 + (bytes k).length) k (f :: frames) (fuel - 1) =
      applyResult ba (pos + (bytes t).length) t frames fuel) :
    loop fuel ba pos frames = applyResult ba (pos + (bytes t).length) t frames fuel := by
  have _ := hf; have _ := hnodes
  rw [hstep, hih, happly]

theorem workloop_leaf_of_steps {α φ ρ : Type}
    (loop : UInt32 → ByteArray → Nat → List φ → ρ)
    (applyResult : ByteArray → Nat → α → List φ → UInt32 → ρ)
    {ba : ByteArray} {pos pos1 : Nat} {t : α} {frames : List φ} {fuel : UInt32}
    (bytes : α → List UInt8)
    (hstep : loop fuel ba pos frames = applyResult ba pos1 t frames fuel)
    (hlen : pos1 = pos + (bytes t).length) :
    loop fuel ba pos frames = applyResult ba (pos + (bytes t).length) t frames fuel := by
  rw [hstep, hlen]

end

/-! ## 3. Meta Infrastructure: `c0_bv32_omega`, Tag/Slice Tactics, & `emit_dir_equiv!` -/

public section

open Lean Meta Elab Tactic Command

private meta def evalNatExpr? (e : Lean.Expr) : MetaM (Option Nat) :=
  Meta.getNatValue? e

private meta def propFactsFromLCtx : MetaM (List Lean.Expr) := do
  let mut facts : List Lean.Expr := []
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if ← isProp decl.type then
        facts := decl.toExpr :: facts
  return facts

private meta def tryProveWithOmega? (goalTy : Lean.Expr) : MetaM (Option Lean.Expr) := do
  withoutModifyingState do
    try
      let facts ← propFactsFromLCtx
      let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
      Lean.Elab.Tactic.Omega.omega facts mvar.mvarId!
      let prf ← instantiateMVars mvar
      if prf.hasExprMVar then return none
      return some prf
    catch _ =>
      return none

/-- Reduce `a % b` to `a` whenever `omega` proves `a < b`. -/
simproc ↓ c0ModLt32Simproc ((_ : Nat) % _) := fun e => do
  unless e.isAppOfArity ``HMod.hMod 6 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat && args[2]!.isConstOf ``Nat do
    return .continue
  let aE := args[4]!
  let bE := args[5]!
  let condTy ← mkAppM ``LT.lt #[aE, bE]
  let some hlt ← tryProveWithOmega? condTy | return .continue
  let prf := mkApp3 (mkConst ``Nat.mod_eq_of_lt) aE bE hlt
  return .visit { expr := aE, proof? := some prf }

/-- Reduce `2 ^ k` for concrete `Nat` exponents `k ≤ 64`. -/
simproc c0Pow32Simproc ((2 : Nat) ^ _) := fun e => do
  unless e.isAppOfArity ``HPow.hPow 6 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat && args[2]!.isConstOf ``Nat do
    return .continue
  let some b ← evalNatExpr? args[4]! | return .continue
  let some k ← evalNatExpr? args[5]! | return .continue
  if b == 2 && k ≤ 64 then
    let valE := mkNatLit (2 ^ k)
    return .done { expr := valE, proof? := none }
  return .continue

private meta def mkUintLitSimproc (toNatNm : Name) (bound : Nat) (e : Lean.Expr) :
    SimpM Simp.Step := do
  unless e.isAppOfArity toNatNm 1 do return .continue
  let inner := e.appArg!
  let some nE :=
    if inner.isAppOfArity ``OfNat.ofNat 3 then some (inner.getArg! 1)
    else if inner.isAppOfArity ``UInt8.ofNat 1 || inner.isAppOfArity ``UInt32.ofNat 1 ||
        inner.isAppOfArity ``UInt64.ofNat 1 then some inner.appArg!
    else none | return .continue
  let some n ← evalNatExpr? nE | return .continue
  if n < bound then
    return .done { expr := mkNatLit n, proof? := none }
  return .continue

simproc c0U8OfNatSimproc (UInt8.toNat _) := mkUintLitSimproc ``UInt8.toNat (2 ^ 8)
simproc c0U32OfNatSimproc (UInt32.toNat _) := mkUintLitSimproc ``UInt32.toNat (2 ^ 32)
simproc c0U64OfNatSimproc (UInt64.toNat _) := mkUintLitSimproc ``UInt64.toNat (2 ^ 64)

theorem u8_toNat_sub_of_le_toNat (x y : UInt8) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  UInt8.toNat_sub_of_le x y (UInt8.le_iff_toNat_le.mpr h)

theorem u32_toNat_sub_of_le_toNat (x y : UInt32) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le x y (UInt32.le_iff_toNat_le.mpr h)

theorem u64_toNat_sub_of_le_toNat (x y : UInt64) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  UInt64.toNat_sub_of_le x y (UInt64.le_iff_toNat_le.mpr h)

private meta def mkUintSubSimproc (toNatNm subThmNm : Name) (e : Lean.Expr) :
    SimpM Simp.Step := do
  unless e.isAppOfArity toNatNm 1 do return .continue
  let inner := e.appArg!
  unless inner.isAppOfArity ``HSub.hSub 6 do return .continue
  let args := inner.getAppArgs
  let xE := args[4]!
  let yE := args[5]!
  let xToNat := mkApp (mkConst toNatNm) xE
  let yToNat := mkApp (mkConst toNatNm) yE
  let condTy ← mkAppM ``LE.le #[yToNat, xToNat]
  let some hle ← tryProveWithOmega? condTy | return .continue
  let prf := mkApp3 (mkConst subThmNm) xE yE hle
  let rhs ← mkAppM ``HSub.hSub #[xToNat, yToNat]
  return .visit { expr := rhs, proof? := some prf }

simproc ↓ c0SubU8Simproc (UInt8.toNat (_ - _)) :=
  mkUintSubSimproc ``UInt8.toNat ``u8_toNat_sub_of_le_toNat

simproc ↓ c0SubU32Simproc (UInt32.toNat (_ - _)) :=
  mkUintSubSimproc ``UInt32.toNat ``u32_toNat_sub_of_le_toNat

simproc ↓ c0SubU64Simproc (UInt64.toNat (_ - _)) :=
  mkUintSubSimproc ``UInt64.toNat ``u64_toNat_sub_of_le_toNat

theorem u8_lt_two_pow (x : UInt8) : x.toNat < 2 ^ 8 := x.toNat_lt
theorem u32_lt_two_pow (x : UInt32) : x.toNat < 2 ^ 32 := x.toNat_lt
theorem u64_lt_two_pow (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt_size

private meta def collectUintTerms (e : Lean.Expr) (seen : Std.HashSet (Name × Lean.Expr)) :
    MetaM (Std.HashSet (Name × Lean.Expr)) := do
  let ref ← IO.mkRef seen
  e.forEach fun sub => do
    if sub.hasLooseBVars then return
    if sub.isAppOfArity ``UInt8.toNat 1 then
      ref.modify (·.insert (``UInt8, sub.appArg!))
    else if sub.isAppOfArity ``UInt32.toNat 1 then
      ref.modify (·.insert (``UInt32, sub.appArg!))
    else if sub.isAppOfArity ``UInt64.toNat 1 then
      ref.modify (·.insert (``UInt64, sub.appArg!))
  ref.get

private meta def injectUintBounds (mvar : MVarId) : MetaM MVarId :=
  mvar.withContext do
    let mut items : Std.HashSet (Name × Lean.Expr) := {}
    items ← collectUintTerms (← mvar.getType) items
    for decl in ← getLCtx do
      if !decl.isImplementationDetail then
        if ← isProp decl.type then
          items ← collectUintTerms decl.type items
        else
          let ty ← whnf decl.type
          if let some tyNm :=
              if ty.isConstOf ``UInt8 then some ``UInt8
              else if ty.isConstOf ``UInt32 then some ``UInt32
              else if ty.isConstOf ``UInt64 then some ``UInt64
              else none then
            if !decl.toExpr.hasLooseBVars then
              items := items.insert (tyNm, decl.toExpr)
    let mut cur := mvar
    let mut idx : Nat := 0
    for (tyNm, xE) in items do
      let (toNatNm, ltThmNm, w) :=
        if tyNm == ``UInt8 then (``UInt8.toNat, ``u8_lt_two_pow, 8)
        else if tyNm == ``UInt32 then (``UInt32.toNat, ``u32_lt_two_pow, 32)
        else (``UInt64.toNat, ``u64_lt_two_pow, 64)
      let term := mkApp (mkConst toNatNm) xE
      let boundTy ← mkAppM ``LT.lt #[term, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit w]]
      let already ← cur.withContext do
        (← getLCtx).anyM fun d => do
          if d.isImplementationDetail then return false
          withoutModifyingState (isDefEq d.type boundTy)
      if !already then
        let prf := mkApp (mkConst ltThmNm) xE
        cur ← cur.assert (Lean.Name.mkSimple s!"_u_lt_{idx}") boundTy prf
        let (_, cur') ← cur.intro1P
        cur := cur'
        idx := idx + 1
    return cur

theorem u8_eq_iff (a b : UInt8) : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt8.toNat, u8_ext⟩

theorem u32_eq_iff (a b : UInt32) : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt32.toNat, u32_ext⟩

theorem u64_eq_iff (a b : UInt64) : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg UInt64.toNat, u64_ext⟩

theorem u8_ne_iff (a b : UInt8) : a ≠ b ↔ a.toNat ≠ b.toNat := by
  simp [u8_eq_iff]

theorem u32_ne_iff (a b : UInt32) : a ≠ b ↔ a.toNat ≠ b.toNat := by
  simp [u32_eq_iff]

theorem u64_ne_iff (a b : UInt64) : a ≠ b ↔ a.toNat ≠ b.toNat := by
  simp [u64_eq_iff]

theorem u8_toNat_ofNat_lit {n : Nat} : (UInt8.ofNat n).toNat = n % 2 ^ 8 :=
  UInt8.toNat_ofNat'

theorem u32_toNat_ofNat_lit {n : Nat} : (UInt32.ofNat n).toNat = n % 2 ^ 32 :=
  UInt32.toNat_ofNat'

theorem u64_toNat_ofNat_lit {n : Nat} : (UInt64.ofNat n).toNat = n % 2 ^ 64 :=
  UInt64.toNat_ofNat'

theorem u8_toNat_ofNat_nat {n : Nat} : (OfNat.ofNat n : UInt8).toNat = n % 2 ^ 8 :=
  UInt8.toNat_ofNat'

theorem u32_toNat_ofNat_nat {n : Nat} : (OfNat.ofNat n : UInt32).toNat = n % 2 ^ 32 :=
  UInt32.toNat_ofNat'

theorem u64_toNat_ofNat_nat {n : Nat} : (OfNat.ofNat n : UInt64).toNat = n % 2 ^ 64 :=
  UInt64.toNat_ofNat'

private meta def runBv32OmegaSimpPass (includeSub : Bool) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let (g, tail) := match ← getGoals with | g :: gs => (g, gs) | [] => unreachable!
  let resGoal? ← g.withContext do
    let mut thms : SimpTheorems := {}
    for c in [
      ``u8_eq_iff, ``u32_eq_iff, ``u64_eq_iff,
      ``u8_ne_iff, ``u32_ne_iff, ``u64_ne_iff,
      ``UInt8.le_iff_toNat_le, ``UInt32.le_iff_toNat_le, ``UInt64.le_iff_toNat_le,
      ``UInt8.lt_iff_toNat_lt, ``UInt32.lt_iff_toNat_lt, ``UInt64.lt_iff_toNat_lt,
      ``u8_toNat_ofNat_lit, ``u32_toNat_ofNat_lit, ``u64_toNat_ofNat_lit,
      ``u8_toNat_ofNat_nat, ``u32_toNat_ofNat_nat, ``u64_toNat_ofNat_nat,
      ``UInt8.toNat_zero, ``UInt32.toNat_zero, ``UInt64.toNat_zero,
      ``UInt8.toNat_add, ``UInt32.toNat_add, ``UInt64.toNat_add,
      ``UInt8.toNat_mul, ``UInt32.toNat_mul, ``UInt64.toNat_mul,
      ``UInt8.toNat_toUInt32, ``UInt8.toNat_toUInt64,
      ``UInt32.toNat_toUInt64, ``UInt64.toNat_toUInt32,
      ``Nat.mul_one, ``Nat.one_mul, ``Nat.add_zero, ``Nat.zero_add, ``Nat.mod_mod] do
      thms ← thms.addConst c
    let mut simprocs : Simp.Simprocs := {}
    for post in [false, true] do
      simprocs ← simprocs.add ``c0Pow32Simproc post
      simprocs ← simprocs.add ``c0U8OfNatSimproc post
      simprocs ← simprocs.add ``c0U32OfNatSimproc post
      simprocs ← simprocs.add ``c0U64OfNatSimproc post
    simprocs ← simprocs.add ``c0SubU8Simproc includeSub
    simprocs ← simprocs.add ``c0SubU32Simproc includeSub
    simprocs ← simprocs.add ``c0SubU64Simproc includeSub
    simprocs ← simprocs.add ``c0ModLt32Simproc true
    let ctx ← Simp.mkContext
      (config := { failIfUnchanged := false, maxSteps := 100000 })
      (simpTheorems := #[thms])
    let propIds := (← getLCtx).foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail then acc.push d.fvarId else acc
    let (res?, _) ← simpGoal g ctx #[simprocs] (simplifyTarget := true) (fvarIdsToSimp := propIds)
    return res?
  match resGoal? with
  | none => setGoals tail
  | some (_, g') => setGoals (g' :: tail)

/-- Normalize `UInt8` / `UInt32` / `UInt64` equalities, inequalities, additions, multiplications,
widening casts, and subtractions to `Nat` bounds and close via `omega` (`std3` axioms only). -/
elab "c0_bv32_omega" : tactic => do
  evalTactic (← `(tactic| try (first | rfl | assumption)))
  if (← getGoals).isEmpty then return
  let (g, tail) := match ← getGoals with | g :: gs => (g, gs) | [] => unreachable!
  let g ← injectUintBounds g
  setGoals (g :: tail)
  runBv32OmegaSimpPass (includeSub := false)
  if (← getGoals).isEmpty then return
  runBv32OmegaSimpPass (includeSub := true)
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| first | rfl | assumption | omega))

/-- Automatically decide and rewrite any ground `if c then a else b` in the goal. -/
elab "c0_decide_ite" : tactic => do
  for _ in [:32] do
    if (← getGoals).isEmpty then break
    let ok ←
      (do evalTactic (← `(tactic| rw [Codec0Kit.ite_true_eq (by decide)])); pure true)
      <|> (do evalTactic (← `(tactic| rw [Codec0Kit.ite_false_eq (by decide)])); pure true)
      <|> pure false
    if !ok then break

/-- Automatically decide and rewrite any ground `if c then a else b` at hypothesis `h`. -/
syntax "c0_decide_ite_at " ident : tactic
elab_rules : tactic
  | `(tactic| c0_decide_ite_at $h:ident) => do
      for _ in [:32] do
        if (← getGoals).isEmpty then break
        let ok ←
          (do evalTactic (← `(tactic|
                rw [Codec0Kit.ite_true_eq (by decide)] at $h:ident)); pure true)
          <|> (do evalTactic (← `(tactic|
                rw [Codec0Kit.ite_false_eq (by decide)] at $h:ident)); pure true)
          <|> pure false
        if !ok then break

/-- Inversion helpers for guarded `if` / `Option` decoder branches. -/
public theorem ite_none_eq_some {α} {c : Prop} [Decidable c] {a : Option α} {r : α}
    (h : (if c then a else none) = some r) : c ∧ a = some r := by
  by_cases hc : c <;> simp_all

public theorem dite_none_eq_some {α} {c : Prop} [Decidable c] {a : c → Option α} {r : α}
    (h : (if hc : c then a hc else none) = some r) : ∃ hc : c, a hc = some r := by
  by_cases hc : c
  · exact ⟨hc, by simpa [hc] using h⟩
  · simp [hc] at h

/-- Split `cases hv : e` inside `h : (match e with | none => none | ok ... => ...) = ...`. -/
syntax "codec_match " ident " , " ident " , " ident " ← " term " at " ident : tactic
syntax "codec_match " ident " , " ident " , " ident " , " ident " ← " term " at " ident : tactic
syntax "codec_match " ident " , " ident " , " ident " , " ident " , " ident
  " ← " term " at " ident : tactic
syntax "codec_opt " ident " , " ident " ← " term " at " ident : tactic
syntax "codec_step " ident " , " ident " , " ident " ← " term " at " ident : tactic
private meta def runCodecMatch (e : Term) (hv h : Ident) (vars : Array Ident)
    (isStep : Bool := false) : TacticM Unit := do
  let hvBind ← `(Lean.binderIdent| $hv:ident)
  let hvRw ← `(Lean.Parser.Tactic.rwRule| $hv:ident)
  evalTactic (← `(tactic| cases $hvBind : $e))
  let gNone :: gOk :: gs ← getGoals |
    throwError "codec_match: expected 2 constructor branches"
  setGoals [gNone]
  evalTactic (← `(tactic| rw [$hvRw] at $h:ident))
  if isStep then
    evalTactic (← `(tactic| subst $h:ident))
    evalTactic (← `(tactic| trivial))
  else
    evalTactic (← `(tactic| cases $h:ident))
  let remNone ← getGoals
  setGoals [gOk]
  let bs ← vars.mapM fun v => `(Lean.binderIdent| $v:ident)
  evalTactic (← `(tactic| rename_i $[$bs]*))
  evalTactic (← `(tactic| rw [$hvRw] at $h:ident))
  evalTactic (← `(tactic| try dsimp only at $h:ident))
  setGoals (remNone ++ (← getGoals) ++ gs)

elab_rules : tactic
  | `(tactic| codec_match $a:ident , $b:ident , $hv:ident ← $e:term at $h:ident) =>
      runCodecMatch e hv h #[a, b]
  | `(tactic| codec_match $a:ident , $b:ident , $c:ident , $hv:ident ← $e:term at $h:ident) =>
      runCodecMatch e hv h #[a, b, c]
  | `(tactic| codec_match $a:ident , $b:ident , $c:ident , $d:ident , $hv:ident
      ← $e:term at $h:ident) =>
      runCodecMatch e hv h #[a, b, c, d]
  | `(tactic| codec_opt $v:ident , $hv:ident ← $e:term at $h:ident) =>
      runCodecMatch e hv h #[v]
  | `(tactic| codec_step $a:ident , $b:ident , $hv:ident ← $e:term at $h:ident) =>
      runCodecMatch e hv h #[a, b] (isStep := true)

/-- Linearly split `b : UInt8` given `hb : b.toNat ≤ k` into concrete numerals `0 .. k`
and run `tac` on each branch. -/
syntax "u8_split_le " term " with " tactic : tactic

private meta partial def runU8CasesLoop (predNat : Term) (nId hnId : Ident)
    (tac : TSyntax `tactic) : Nat → TacticM Unit
  | 0 => do
    evalTactic (← `(tactic|
      refine Codec0Kit.nat_cases_le_zero (P := $predNat) (n := $nId:ident) $hnId:ident ?_))
    evalTactic (← `(tactic| try dsimp only))
    evalTactic tac
  | k + 1 => do
    let hnNext := mkIdent (← withMainContext <| mkFreshUserName `_hle)
    evalTactic (← `(tactic|
      refine Codec0Kit.nat_cases_le_step (P := $predNat) (n := $nId:ident)
        (k := $(quote k)) $hnId:ident ?_ (fun $hnNext:ident => ?_)))
    let g1 :: gRest :: gs ← getGoals | return
    setGoals [g1]
    evalTactic (← `(tactic| try dsimp only))
    evalTactic tac
    let rem ← getGoals
    setGoals [gRest]
    runU8CasesLoop predNat nId hnNext tac k
    setGoals ((← getGoals) ++ rem ++ gs)

elab_rules : tactic
  | `(tactic| u8_split_le $hk with $tac) => do
    let (pStx, bStx, k) ← withMainContext do
      let hkE ← elabTerm hk none
      let hkTy ← whnf (← inferType hkE)
      let some (lhsE, rhsE) := hkTy.app2? ``Nat.le |
        throwError "u8_split_le: expected `b.toNat ≤ k`, got {hkTy}"
      let some k ← Meta.getNatValue? (← whnf rhsE) |
        throwError "u8_split_le: upper bound must be a numeral, got {rhsE}"
      let some bE :=
        (if lhsE.isAppOfArity ``UInt8.toNat 1 then some lhsE.appArg! else none) |
        throwError "u8_split_le: expected `b.toNat ≤ k`, got {hkTy}"
      let tgt ← instantiateMVars (← getMainTarget)
      let body ← Meta.kabstract tgt bE
      let pred := mkLambda `_b .default (mkConst ``UInt8) body
      return (← Term.exprToSyntax pred, ← Term.exprToSyntax bE, k)
    let nId := mkIdent (← withMainContext <| mkFreshUserName `_n)
    let hnId := mkIdent (← withMainContext <| mkFreshUserName `_hn)
    let predNat ← `(term| fun _m : Nat => $pStx (UInt8.ofNat _m))
    evalTactic (← `(tactic|
      refine Codec0Kit.u8_cases_le (P := $pStx) $bStx $(quote k) $hk ?_))
    evalTactic (← `(tactic| intro $nId:ident $hnId:ident))
    runU8CasesLoop predNat nId hnId tac k

/-- Recursively split cascading `if (tag == c) = true then ... else ...` in hypothesis `h`,
trying `leafTac` on each true branch and `elseTac` at the bottom. -/
syntax "decode_ite_chain " ident " with " tactic " else " tactic : tactic

private meta partial def runDecodeIteChain (hId : Ident) (leafTac elseTac : TSyntax `tactic)
    (fuel : Nat) : TacticM Unit := do
  if fuel == 0 || (← getGoals).isEmpty then return
  let eqStx? ← withMainContext do
    let some decl := (← getLCtx).findFromUserName? hId.getId | return none
    let ty ← instantiateMVars decl.type
    let some (_, lhs, _) := ty.eq? | return none
    if lhs.isAppOfArity ``ite 5 then
      let cond := lhs.getArg! 1
      if cond.isAppOfArity ``Eq 3 && (cond.getArg! 1).isAppOfArity ``BEq.beq 4 then
        let lhsB := (cond.getArg! 1).getArg! 2
        let rhsB := (cond.getArg! 1).getArg! 3
        let eqProp ← mkEq lhsB rhsB
        return some (← Term.exprToSyntax eqProp)
    return none
  let some eqStx := eqStx? | do evalTactic elseTac; return
  let hTagId := mkIdent (← withMainContext <| mkFreshUserName `hTag)
  evalTactic (← `(tactic| by_cases $hTagId:ident : $eqStx))
  let gTrue :: gFalse :: gs ← getGoals | return
  setGoals [gTrue]
  evalTactic (← `(tactic| subst $hTagId:ident))
  evalTactic (← `(tactic| rw [Codec0Kit.ite_true_eq (by decide)] at $hId:ident))
  evalTactic leafTac
  let rem1 ← getGoals
  setGoals [gFalse]
  evalTactic (← `(tactic| rw [Codec0Kit.ite_false_beq $hTagId:ident] at $hId:ident))
  runDecodeIteChain hId leafTac elseTac (fuel - 1)
  let rem2 ← getGoals
  setGoals (rem1 ++ rem2 ++ gs)

elab_rules : tactic
  | `(tactic| decode_ite_chain $hId with $leafTac else $elseTac) => do
    runDecodeIteChain hId leafTac elseTac 32

/-- Kernel-checked `UInt8`-enum decoder soundness proof (`decodeTy0`, `decodeWidth0`, etc.)
yielding `pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 1 ∧ baSlice ba pos pos' = [tagFn v]`
using strictly `std3` axioms. -/
elab "decode_enum_tag! " decId:ident _tagId:ident hId:ident : tactic => do
  let decU8Nm ← resolveGlobalConstNoOverload (mkIdent `LeanQbe.T.Bootstrap0.Codec0.decodeU8)
  let decU8OkNm ←
    resolveGlobalConstNoOverload (mkIdent `LeanQbe.T.Bootstrap0.Codec0Spec.decodeU8_ok_bytes)
  let (baStx, posStx) ← withMainContext do
    let some decl := (← getLCtx).findFromUserName? hId.getId |
      throwError "decode_enum_tag!: unknown hypothesis `{hId}`"
    let ty ← instantiateMVars decl.type
    let some (_, lhs, _) := ty.eq? | throwError "decode_enum_tag!: expected equality in `{hId}`"
    let args := lhs.getAppArgs
    if args.size < 2 then throwError "decode_enum_tag!: expected `dec ba pos` in `{hId}`"
    return (← Term.exprToSyntax args[args.size - 2]!, ← Term.exprToSyntax args[args.size - 1]!)
  let decU8Id := mkIdent decU8Nm
  let decU8OkId := mkIdent decU8OkNm
  evalTactic (← `(tactic| dsimp only [$decId:ident] at $hId:ident))
  evalTactic (← `(tactic|
    cases hu : $decU8Id $baStx $posStx with
    | none => rw [hu] at $hId:ident; cases $hId:ident
    | ok b p1 =>
      rw [hu] at $hId:ident
      try dsimp only at $hId:ident
      obtain ⟨h01, h1s, hp1, hsl⟩ := $decU8OkId $baStx $posStx b p1 hu
      decode_ite_chain $hId:ident
        with (cases $hId:ident; subst hp1; exact ⟨h01, h1s, rfl, hsl⟩)
        else (cases $hId:ident)))

/-- Join a chain of `baSlice` facts `[hs1, hs2, ...]` via `baSlice_trans`. -/
elab "ba_slice_join" "[" hs:term,* "]" : tactic => do
  let hArr := hs.getElems
  if hArr.isEmpty then return
  let fnId? ← withMainContext do
    let hE ← elabTerm hArr[0]! none
    let hTy ← whnf (← inferType hE)
    let some (_, lhs, _) := hTy.eq? | return none
    match lhs.getAppFn.constName? with
    | some fnNm =>
      if fnNm == ``Codec0Kit.baSlice then return none else return some (mkIdent fnNm)
    | none => return none
  if let some fnId := fnId? then
    evalTactic (← `(tactic| try dsimp only [$fnId:ident] at *))
  let n := hArr.size
  for i in [:n - 1] do
    let hStx := hArr[i]!
    let pMidStx ← withMainContext do
      let hE ← elabTerm hStx none
      let hTy ← whnf (← inferType hE)
      let some (_, lhs, _) := hTy.eq? | throwError "ba_slice_join: expected `baSlice ... = ...`"
      let args := lhs.getAppArgs
      if args.size < 3 then throwError "ba_slice_join: expected `baSlice ba p0 p1`"
      Term.exprToSyntax args[2]!
    let hRw ← `(Lean.Parser.Tactic.rwRule| $hStx:term)
    evalTactic (← `(tactic|
      rw [Codec0Kit.baSlice_trans (p1 := $pMidStx) (by omega) (by omega), $hRw]))
  let hLast := hArr[n - 1]!
  let hLastRw ← `(Lean.Parser.Tactic.rwRule| $hLast:term)
  evalTactic (← `(tactic| rw [$hLastRw]))
  evalTactic (← `(tactic| try simp only [List.append_assoc, List.cons_append, List.nil_append]))
  evalTactic (← `(tactic| try rfl))

/-- Persistent configuration for `emit_dir_equiv!` registered by `PrintDir0Lemmas`. -/
meta structure EmitDirEquivCfg where
  defs : Array Name := #[]
  rws : Array Name := #[]
  deriving Inhabited

meta initialize emitDirEquivExt :
    SimpleScopedEnvExtension (Array Name × Array Name) EmitDirEquivCfg ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun cfg (ds, rs) => { defs := cfg.defs ++ ds, rws := cfg.rws ++ rs }
  }

/-- Register `dsimp only` definitions and rewrite lemmas for `emit_dir_equiv!`. -/
elab "register_emit_dir_equiv! " "[" defs:ident,* "]" "[" rws:ident,* "]" : command => do
  let ds ← defs.getElems.mapM (liftCoreM <| realizeGlobalConstNoOverload ·)
  let rs ← rws.getElems.mapM (liftCoreM <| realizeGlobalConstNoOverload ·)
  liftCoreM <| modifyEnv fun env => emitDirEquivExt.addEntry env (ds, rs)

/-- Unfold `PrintDir0` / `Bridge0` / `PrintAsm0` definitions, normalize `if-then-else` and
helper byte-emitter equations, and close via `rfl` when complete. -/
elab "emit_dir_equiv!" : tactic => do
  let cfg := emitDirEquivExt.getState (← getEnv)
  if !cfg.defs.isEmpty then
    let defIds : Array Ident := cfg.defs.map mkIdent
    evalTactic (← `(tactic| try dsimp only [$[$defIds:ident],*]))
  let mut rwTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| rw [ite_eq_left.mpr (fun _ => rfl)]),
    ← `(tactic| rw [ite_eq_right.mpr Bool.false_ne_true])
  ]
  for r in cfg.rws do
    let rId := mkIdent r
    rwTacs := rwTacs.push (← `(tactic| rw [$rId:ident]))
  evalTactic (← `(tactic| repeat (first $[| $rwTacs:tactic]*)))
  evalTactic (← `(tactic| try rfl))

end

end LeanQbe.T.Bootstrap0.Codec0Kit
