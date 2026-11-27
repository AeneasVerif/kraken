module

public import LeanQbe.T.Logic.ByteArrayDecimal
public import LeanQbe.T.Logic.ProofKit
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.ProofKit

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
open LeanQbe.T.ProofKit

/-! ## 1. `U32Kit`: `UInt8` / `UInt32` / `UInt64` Algebra & Bit-Packing -/

public section

theorem u32_ext {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  (U32Kit.u32_eq_iff a b).mpr h

theorem u32_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n := by
  c0_bv32_omega

theorem u32_ofNat_eq {n : Nat} {c : UInt32} (h : n = c.toNat) : UInt32.ofNat n = c := by
  c0_bv32_omega

theorem u32_eq_zero_of_toNat_eq_zero {x : UInt32} (h : x.toNat = 0) : x = 0 := by
  c0_bv32_omega

theorem u32_ne_zero_of_toNat_pos {x : UInt32} (h : 0 < x.toNat) : x ≠ 0 := by
  c0_bv32_omega

theorem u32_toNat_pos_of_ne_zero {x : UInt32} (h : x ≠ 0) : 1 ≤ x.toNat := by
  c0_bv32_omega

theorem u32_ofNat_succ_sub_one {k : Nat} (hk : k + 1 < 2 ^ 32) :
    UInt32.ofNat (k + 1) ≠ 0 ∧ UInt32.ofNat (k + 1) - 1 = UInt32.ofNat k :=
  ⟨by c0_bv32_omega, by c0_bv32_omega⟩

theorem u32_sub1_toNat {rem : UInt32} {n : Nat} (h : rem.toNat = n + 1) :
    rem ≠ 0 ∧ (rem - 1).toNat = n :=
  ⟨by c0_bv32_omega, by c0_bv32_omega⟩

theorem u32_sub_ofNat {a b : Nat} (ha : a ≤ 0xffffffff) (hba : b ≤ a) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  c0_bv32_omega

theorem u32_sub_ofNat_toNat {fuel : UInt32} {n : Nat} (h : n ≤ fuel.toNat) :
    (fuel - UInt32.ofNat n).toNat = fuel.toNat - n := by
  c0_bv32_omega

theorem u32_sub1_ge {fuel : UInt32} {n : Nat} (h : 1 + n ≤ fuel.toNat) :
    n ≤ (fuel - 1).toNat := by
  c0_bv32_omega

theorem u32_sub_sub_ofNat {fuel : UInt32} {a b : Nat} (h : a + b ≤ fuel.toNat) :
    fuel - UInt32.ofNat a - UInt32.ofNat b = fuel - UInt32.ofNat (a + b) := by
  c0_bv32_omega

theorem u32_sub1_sub {fuel : UInt32} {n : Nat} (h : 1 + n ≤ fuel.toNat) :
    fuel - 1 - UInt32.ofNat n = fuel - UInt32.ofNat (1 + n) :=
  u32_sub_sub_ofNat (a := 1) (b := n) h

theorem u32_cnt_sub1_add {done : Nat} {rem : UInt32} (hrem : rem ≠ 0) :
    UInt32.ofNat done + 1 + (rem - 1) = UInt32.ofNat done + rem := by
  rw [UInt32.add_assoc]; congr 1; c0_bv32_omega

theorem u32_cnt_sub1_lt {done : Nat} {rem : UInt32} (hrem : rem ≠ 0)
    (hlt : done + 1 + rem.toNat < 2 ^ 32) :
    done + 1 + 1 + (rem - 1).toNat < 2 ^ 32 := by
  c0_bv32_omega

theorem u32_toNat_sub_of_le_toNat (x y : UInt32) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  U32Kit.u32_toNat_sub_of_eq x y rfl rfl h

theorem u64_toNat_sub_of_le_toNat (x y : UInt64) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  U32Kit.u64_toNat_sub_of_eq x y rfl rfl h

theorem nat_cases_le_step {P : Nat → Prop} {n k : Nat} (hle : n ≤ k + 1)
    (hk : P (k + 1)) (hrest : n ≤ k → P n) : P n :=
  if heq : n = k + 1 then heq ▸ hk else hrest (by omega)

theorem nat_cases_le_zero {P : Nat → Prop} {n : Nat} (hle : n ≤ 0) (h0 : P 0) : P n :=
  (Nat.le_zero.mp hle) ▸ h0

theorem u8_cases_le {P : UInt8 → Prop} (b : UInt8) (k : Nat) (hk : b.toNat ≤ k)
    (h : ∀ n, n ≤ k → P (UInt8.ofNat n)) : P b := by
  rw [← UInt8.ofNat_toNat (x := b)]
  exact h b.toNat hk

private theorem bv8_getLsbD_ge (b : UInt8) {k : Nat} (hk : 8 ≤ k) : b.toBitVec.getLsbD k = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toBitVec.isLt (Nat.pow_le_pow_right (by omega) hk))

theorem u32_pack_unpack_bytes (b0 b1 b2 b3 : UInt8) :
    let lo := b0.toUInt32 ||| (b1.toUInt32 <<< 8)
    let hi := b2.toUInt32 ||| (b3.toUInt32 <<< 8)
    let v := lo ||| (hi <<< 16)
    v.toUInt8 = b0 ∧ (v >>> 8).toUInt8 = b1 ∧
      (v >>> 16).toUInt8 = b2 ∧ (v >>> 24).toUInt8 = b3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (
    apply UInt8.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
      UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32, BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', hi, show i < 32 by omega, show 8 + i < 32 by omega,
      show 16 + i < 32 by omega, show 24 + i < 32 by omega, show ¬ (8 + i < 8) by omega,
      show ¬ (16 + i < 8) by omega, show ¬ (24 + i < 8) by omega, show ¬ (8 + i ≥ 16) by omega,
      show ¬ (16 + i < 16) by omega, show ¬ (24 + i < 16) by omega,
      show ¬ (24 + i - 16 < 8) by omega, show 24 + i - 16 - 8 = i by omega,
      bv8_getLsbD_ge _ (by omega : 8 ≤ 16 + i),
      bv8_getLsbD_ge _ (by omega : 8 ≤ 16 + i - 8),
      bv8_getLsbD_ge _ (by omega : 8 ≤ 24 + i),
      bv8_getLsbD_ge _ (by omega : 8 ≤ 24 + i - 8),
      bv8_getLsbD_ge _ (by omega : 8 ≤ 24 + i - 16)])

theorem u32_of_u8_pack (v : UInt32) :
    (v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8)) |||
      (((v >>> 16).toUInt8.toUInt32 ||| ((v >>> 24).toUInt8.toUInt32 <<< 8)) <<< 16) = v := by
  apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega) with
    h0 | ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
  · simp [hi, h0, show ¬ (16 ≤ i) by omega]
  · simp [hi, show ¬ (i < 8) by omega, show ¬ (16 ≤ i) by omega,
      show i - 8 < 8 by omega, show i - 8 < 32 by omega, Nat.add_sub_cancel' h1a]
  · simp [hi, h2a, show ¬ (i < 8) by omega, show ¬ (i - 8 < 8) by omega,
      show i - 16 < 8 by omega, show i - 16 < 32 by omega, Nat.add_sub_cancel' h2a]
  · simp [hi, show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, show ¬ (i - 8 < 8) by omega,
      show ¬ (i - 16 < 8) by omega, show i - 16 < 32 by omega, show 16 ≤ i by omega,
      show i - 16 - 8 = i - 24 by omega, show i - 24 < 8 by omega,
      show i - 24 < 32 by omega, Nat.add_sub_cancel' h3a]

theorem u64_pack_unpack_u32 (lo hi : UInt32) :
    let v := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
    v.toUInt32 = lo ∧ (v >>> 32).toUInt32 = hi := by
  refine ⟨?_, ?_⟩ <;> (
    apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hlt
    simp [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      UInt64.toBitVec_toUInt32, UInt32.toBitVec_toUInt64, BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', hlt, show i < 64 by omega,
      show 32 + i < 64 by omega, show ¬ (32 + i < 32) by omega])

theorem u64_of_u32_pack (v : UInt64) :
    v.toUInt32.toUInt64 ||| ((v >>> 32).toUInt32.toUInt64 <<< 32) = v := by
  apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_toUInt32, UInt32.toBitVec_toUInt64, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  rcases (show i < 32 ∨ (32 ≤ i ∧ i < 64) by omega) with h0 | ⟨h1a, h1b⟩
  · simp [hi, h0]
  · simp [hi, show ¬ (i < 32) by omega, show i - 32 < 32 by omega, show i - 32 < 64 by omega,
      Nat.add_sub_cancel' h1a]

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

/-! ## 3. Meta Infrastructure: Tag/Slice Tactics & `emit_dir_equiv!` -/

public section

open Lean Meta Elab Tactic Command

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
