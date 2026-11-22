module

public import LeanQbe.T.Bootstrap0.Codec0

/-!
# `Codec0` Boundedness Specification & Scalar/List Byte Lemmas (`Codec0Lemmas1`)

Provides `Mod0Bounded` (`checkMod0Bounded` / `mod0Bounded_of_check`), `ByteArray`/slice
algebra, and scalar/enum/`Arg0`/`OpCode0`/list byte-codec proofs backing `Codec0Lemmas`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Bootstrap0

public section

/-! ## 1. 32-Bit Boundedness Specification (`Mod0Bounded`) -/

mutual
/-- Structural 32-bit list-length bound on `TFlat0` (matching `UInt32` wire counts). -/
@[expose] def TFlat0ListBounded : TFlat0 → Prop
  | .let1 _ args k => args.length < 2 ^ 32 ∧ TFlat0ListBounded k
  | .let2Umulw64 _ _ k => TFlat0ListBounded k
  | .load _ _ k => TFlat0ListBounded k
  | .store _ _ _ k => TFlat0ListBounded k
  | .call _ as bs args k =>
    as.length < 2 ^ 32 ∧ bs.length < 2 ^ 32 ∧ args.length < 2 ^ 32 ∧ TFlat0ListBounded k
  | .tailCall _ as args => as.length < 2 ^ 32 ∧ args.length < 2 ^ 32
  | .jnz _ t e => TFlat0ListBounded t ∧ TFlat0ListBounded e
  | .jump _ args => args.length < 2 ^ 32
  | .ret vs => vs.length < 2 ^ 32
  | .exit _ as args => as.length < 2 ^ 32 ∧ args.length < 2 ^ 32
  | .hlt => True
  | .group bodies k =>
    bodies.length < 2 ^ 32 ∧ Blocks0ListBounded bodies ∧ TFlat0ListBounded k

/-- Structural 32-bit list-length bound over `.group` blocks. -/
@[expose] def Blocks0ListBounded : List (List Ty0 × TFlat0) → Prop
  | [] => True
  | (ts, b) :: rest => ts.length < 2 ^ 32 ∧ TFlat0ListBounded b ∧ Blocks0ListBounded rest
end

mutual
/-- Exact number of `TFlat0` AST nodes (1 unit of `decodeTFlatLoop0` fuel per node). -/
@[expose] def tflatNodes : TFlat0 → Nat
  | .let1 _ _ k => 1 + tflatNodes k
  | .let2Umulw64 _ _ k => 1 + tflatNodes k
  | .load _ _ k => 1 + tflatNodes k
  | .store _ _ _ k => 1 + tflatNodes k
  | .call _ _ _ _ k => 1 + tflatNodes k
  | .tailCall _ _ _ => 1
  | .jnz _ t e => 1 + tflatNodes t + tflatNodes e
  | .jump _ _ => 1
  | .ret _ => 1
  | .exit _ _ _ => 1
  | .hlt => 1
  | .group bodies k => 1 + blocksNodes bodies + tflatNodes k

/-- Node count over a `.group` block list. -/
@[expose] def blocksNodes : List (List Ty0 × TFlat0) → Nat
  | [] => 0
  | (_, b) :: rest => tflatNodes b + blocksNodes rest
end

/-- Complete 32-bit size bound on `TFlat0` (`TFlat0ListBounded` and `≤ 0xffffffff` nodes). -/
@[expose] def TFlat0Bounded (t : TFlat0) : Prop :=
  TFlat0ListBounded t ∧ tflatNodes t ≤ 0xffffffff

/-- 32-bit boundedness for a `TFlatFn0`. -/
@[expose] def Fn0Bounded (fn : TFlatFn0) : Prop :=
  fn.as.length < 2 ^ 32 ∧ fn.rs.length < 2 ^ 32 ∧ TFlat0Bounded fn.body

/-- 32-bit boundedness for an `ExtSig0`. -/
@[expose] def ExtSig0Bounded (ex : ExtSig0) : Prop :=
  ex.as.length < 2 ^ 32 ∧ ex.rs.length < 2 ^ 32

/-- 32-bit boundedness for a `TFlatModule0` (satisfied by all practical IR modules `< 4 GiB`). -/
@[expose] def Mod0Bounded (m : TFlatModule0) : Prop :=
  m.fns.length < 2 ^ 32 ∧
  m.externs.length < 2 ^ 32 ∧
  m.exits.length < 2 ^ 32 ∧
  (∀ fn ∈ m.fns, Fn0Bounded fn) ∧
  (∀ ex ∈ m.externs, ExtSig0Bounded ex)

mutual
/-- Computable boolean checker for `TFlat0ListBounded`. -/
@[expose] def checkTFlat0ListBounded : TFlat0 → Bool
  | .let1 _ args k => decide (args.length < 2 ^ 32) && checkTFlat0ListBounded k
  | .let2Umulw64 _ _ k => checkTFlat0ListBounded k
  | .load _ _ k => checkTFlat0ListBounded k
  | .store _ _ _ k => checkTFlat0ListBounded k
  | .call _ as bs args k =>
    decide (as.length < 2 ^ 32) && decide (bs.length < 2 ^ 32) &&
      decide (args.length < 2 ^ 32) && checkTFlat0ListBounded k
  | .tailCall _ as args => decide (as.length < 2 ^ 32) && decide (args.length < 2 ^ 32)
  | .jnz _ t e => checkTFlat0ListBounded t && checkTFlat0ListBounded e
  | .jump _ args => decide (args.length < 2 ^ 32)
  | .ret vs => decide (vs.length < 2 ^ 32)
  | .exit _ as args => decide (as.length < 2 ^ 32) && decide (args.length < 2 ^ 32)
  | .hlt => true
  | .group bodies k =>
    decide (bodies.length < 2 ^ 32) && checkBlocks0ListBounded bodies && checkTFlat0ListBounded k

/-- Computable boolean checker for `Blocks0ListBounded`. -/
@[expose] def checkBlocks0ListBounded : List (List Ty0 × TFlat0) → Bool
  | [] => true
  | (ts, b) :: rest =>
    decide (ts.length < 2 ^ 32) && checkTFlat0ListBounded b && checkBlocks0ListBounded rest
end

/-- Computable boolean checker for `Mod0Bounded`. -/
@[expose] def checkMod0Bounded (m : TFlatModule0) : Bool :=
  decide (m.fns.length < 2 ^ 32) &&
  decide (m.externs.length < 2 ^ 32) &&
  decide (m.exits.length < 2 ^ 32) &&
  m.fns.all (fun fn =>
    decide (fn.as.length < 2 ^ 32) && decide (fn.rs.length < 2 ^ 32) &&
      checkTFlat0ListBounded fn.body && decide (tflatNodes fn.body ≤ 0xffffffff)) &&
  m.externs.all (fun ex => decide (ex.as.length < 2 ^ 32) && decide (ex.rs.length < 2 ^ 32))

end

mutual
private theorem checkTFlat0ListBounded_sound :
    ∀ t, checkTFlat0ListBounded t = true → TFlat0ListBounded t
  | .let1 _ args k, h => by
    dsimp only [checkTFlat0ListBounded, TFlat0ListBounded] at h ⊢
    rw [Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨h.1, checkTFlat0ListBounded_sound k h.2⟩
  | .let2Umulw64 _ _ k, h | .load _ _ k, h | .store _ _ _ k, h => checkTFlat0ListBounded_sound k h
  | .call _ as bs args k, h => by
    dsimp only [checkTFlat0ListBounded, TFlat0ListBounded] at h ⊢
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨of_decide_eq_true h.1.1.1, of_decide_eq_true h.1.1.2,
      of_decide_eq_true h.1.2, checkTFlat0ListBounded_sound k h.2⟩
  | .tailCall _ as args, h | .exit _ as args, h => by
    dsimp only [checkTFlat0ListBounded, TFlat0ListBounded] at h ⊢
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h; exact h
  | .jnz _ t e, h => by
    dsimp only [checkTFlat0ListBounded, TFlat0ListBounded] at h ⊢
    rw [Bool.and_eq_true] at h
    exact ⟨checkTFlat0ListBounded_sound t h.1, checkTFlat0ListBounded_sound e h.2⟩
  | .jump _ args, h | .ret args, h => by
    dsimp only [checkTFlat0ListBounded, TFlat0ListBounded] at h ⊢; exact of_decide_eq_true h
  | .hlt, _ => trivial
  | .group bodies k, h => by
    dsimp only [checkTFlat0ListBounded, TFlat0ListBounded] at h ⊢
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨of_decide_eq_true h.1.1, checkBlocks0ListBounded_sound bodies h.1.2,
      checkTFlat0ListBounded_sound k h.2⟩

private theorem checkBlocks0ListBounded_sound :
    ∀ bs, checkBlocks0ListBounded bs = true → Blocks0ListBounded bs
  | [], _ => trivial
  | (ts, b) :: rest, h => by
    dsimp only [checkBlocks0ListBounded, Blocks0ListBounded] at h ⊢
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨of_decide_eq_true h.1.1, checkTFlat0ListBounded_sound b h.1.2,
      checkBlocks0ListBounded_sound rest h.2⟩
end

/-- Soundness of `checkMod0Bounded` for proving `Mod0Bounded`. -/
public theorem mod0Bounded_of_check (m : TFlatModule0) (h : checkMod0Bounded m = true) :
    Mod0Bounded m := by
  dsimp only [checkMod0Bounded, Mod0Bounded] at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1.1.1.1, of_decide_eq_true h.1.1.1.2,
    of_decide_eq_true h.1.1.2, ?_, ?_⟩
  · intro fn hfn
    have h1 := List.all_eq_true.mp h.1.2 fn hfn
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
    exact ⟨of_decide_eq_true h1.1.1.1, of_decide_eq_true h1.1.1.2,
      checkTFlat0ListBounded_sound fn.body h1.1.2, of_decide_eq_true h1.2⟩
  · intro ex hex
    have h2 := List.all_eq_true.mp h.2 ex hex; rw [Bool.and_eq_true] at h2
    exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩


namespace Codec0Spec

/-! ## 2. `ByteArray` and Slice Algebra Helpers -/

@[expose] public def baSlice (ba : ByteArray) (p0 p1 : Nat) : List UInt8 :=
  (ba.data.toList.drop p0).take (p1 - p0)

public theorem ba_eq_of_data_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := by
  cases a; cases b; congr 1; exact Array.ext' h

public theorem ba_data_toList_length (ba : ByteArray) : ba.data.toList.length = ba.size := by
  cases ba; dsimp only [ByteArray.size]; exact Array.length_toList

public theorem ba_push_data_toList (ba : ByteArray) (b : UInt8) :
    (ba.push b).data.toList = ba.data.toList ++ [b] := by
  cases ba; dsimp only [ByteArray.push]; exact Array.toList_push

public theorem ba_emptyWithCapacity_data_toList (c : Nat) :
    (ByteArray.emptyWithCapacity c).data.toList = [] := rfl

public theorem ba_e2_data_toList (ba : ByteArray) (a b : UInt8) :
    (Codec0.e2 ba a b).data.toList = ba.data.toList ++ [a, b] := by
  dsimp only [Codec0.e2]; rw [ba_push_data_toList, ba_push_data_toList, List.append_assoc]; rfl

public theorem ba_e4_data_toList (ba : ByteArray) (a b c d : UInt8) :
    (Codec0.e4 ba a b c d).data.toList = ba.data.toList ++ [a, b, c, d] := by
  dsimp only [Codec0.e4]
  rw [ba_push_data_toList, ba_push_data_toList, ba_push_data_toList, ba_push_data_toList,
    List.append_assoc, List.append_assoc, List.append_assoc]; rfl

public theorem drop_pos_add (l : List UInt8) (a b : Nat) :
    l.drop (a + b) = (l.drop a).drop b := by rw [List.drop_drop, Nat.add_comm]

private theorem drop_eq_cons_iff (ba : ByteArray) (pos : Nat) (b : UInt8) (rest : List UInt8) :
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
    refine ⟨h, ?_, by rw [drop_pos_add, hdrop]; rfl⟩
    have hcons := List.drop_eq_getElem_cons hlen; rw [hdrop] at hcons
    injection hcons with hhead _; exact hhead.symm

public theorem baSlice_zero_self (ba : ByteArray) : baSlice ba 0 ba.size = ba.data.toList := by
  dsimp only [baSlice]; rw [List.drop_zero, Nat.sub_zero, ← ba_data_toList_length, List.take_length]

public theorem baSlice_self (ba : ByteArray) (p : Nat) : baSlice ba p p = [] := by
  dsimp only [baSlice]; rw [Nat.sub_self, List.take_zero]

public theorem baSlice_trans {ba : ByteArray} {p0 p1 p2 : Nat}
    (h01 : p0 ≤ p1) (h12 : p1 ≤ p2) :
    baSlice ba p0 p2 = baSlice ba p0 p1 ++ baSlice ba p1 p2 := by
  dsimp only [baSlice]
  have hdrop : ba.data.toList.drop p1 = (ba.data.toList.drop p0).drop (p1 - p0) := by
    rw [← drop_pos_add, Nat.add_sub_cancel' h01]
  rw [hdrop, (by omega : p2 - p0 = (p1 - p0) + (p2 - p1)), List.take_add]

private theorem baSlice_of_drop_prefix {ba : ByteArray} {pos : Nat} {xs rest : List UInt8}
    (hdrop : ba.data.toList.drop pos = xs ++ rest) :
    baSlice ba pos (pos + xs.length) = xs ∧ ba.data.toList.drop (pos + xs.length) = rest :=
  ⟨by dsimp only [baSlice]; rw [hdrop, Nat.add_sub_cancel_left, List.take_left],
    by rw [drop_pos_add, hdrop, List.drop_left]⟩

public theorem dite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a : p → α} {b : ¬ p → α}
    (h : p) : (if h' : p then a h' else b h') = a h := by
  cases ‹Decidable p› with | isTrue _ => rfl | isFalse hn => exact absurd h hn

public theorem dite_false_eq {p : Prop} [Decidable p] {α : Sort _} {a : p → α} {b : ¬ p → α}
    (h : ¬ p) : (if h' : p then a h' else b h') = b h := by
  cases ‹Decidable p› with | isTrue hp => exact absurd hp h | isFalse _ => rfl

public theorem ite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : p) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with | isTrue _ => rfl | isFalse hn => exact absurd h hn

public theorem ite_false_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with | isTrue hp => exact absurd hp h | isFalse _ => rfl

/-! ## 3. Scalar, Enum, `Arg0`, `OpCode0`, and List Codec Proofs -/

@[expose] public def u32Bytes (v : UInt32) : List UInt8 :=
  [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

@[expose] public def u64Bytes (v : UInt64) : List UInt8 :=
  u32Bytes v.toUInt32 ++ u32Bytes (v >>> 32).toUInt32

@[expose] public def headerBytes : List UInt8 :=
  [0x4c, 0x51, 0x42, 0x30, 0x01]

public theorem encodeHeader_bytes (ba : ByteArray) :
    (Codec0.encodeHeader ba).data.toList = ba.data.toList ++ headerBytes := by
  dsimp only [Codec0.encodeHeader, headerBytes]
  rw [ba_push_data_toList, ba_e4_data_toList, List.append_assoc]
  rfl

public theorem encodeU32_bytes (ba : ByteArray) (v : UInt32) :
    (Codec0.encodeU32 ba v).data.toList = ba.data.toList ++ u32Bytes v := by
  dsimp only [Codec0.encodeU32, u32Bytes]
  exact ba_e4_data_toList ba _ _ _ _

private theorem encodeU64_bytes (ba : ByteArray) (v : UInt64) :
    (Codec0.encodeU64 ba v).data.toList = ba.data.toList ++ u64Bytes v := by
  dsimp only [Codec0.encodeU64, u64Bytes]
  rw [encodeU32_bytes, encodeU32_bytes, List.append_assoc]

public theorem decodeU8_of_bytes (ba : ByteArray) (pos : Nat) (b : UInt8) (rest : List UInt8)
    (h : ba.data.toList.drop pos = b :: rest) :
    Codec0.decodeU8 ba pos = .ok b (pos + 1) := by
  have h1 := (drop_eq_cons_iff ba pos b rest).mpr h
  rcases h1 with ⟨hlt, hb, _⟩
  dsimp only [Codec0.decodeU8]
  rw [dite_true_eq hlt, hb]

public theorem decodeU8_ok_bytes (ba : ByteArray) (pos : Nat) (b : UInt8) (pos' : Nat)
    (h : Codec0.decodeU8 ba pos = .ok b pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 1 ∧ baSlice ba pos pos' = [b] := by
  dsimp only [Codec0.decodeU8] at h
  by_cases hlt : pos < ba.size
  · rw [dite_true_eq hlt] at h
    cases h
    have hdrop : ba.data.toList.drop pos = (ba[pos]'hlt) :: ba.data.toList.drop (pos + 1) :=
      (drop_eq_cons_iff ba pos (ba[pos]'hlt) _).mp ⟨hlt, rfl, rfl⟩
    have hsl := (baSlice_of_drop_prefix (xs := [ba[pos]'hlt])
      (rest := ba.data.toList.drop (pos + 1)) (by simpa using hdrop)).1
    exact ⟨Nat.le_succ pos, hlt, rfl, hsl⟩
  · rw [dite_false_eq hlt] at h
    cases h

private theorem testBit_u32_shl (x : UInt32) (k : UInt32) (hk : k.toNat < 32) (i : Nat) :
    (x <<< k).toNat.testBit i =
      (decide (i < 32) && decide (k.toNat ≤ i) && x.toNat.testBit (i - k.toNat)) := by
  rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hk]
  change ((x.toNat <<< k.toNat) % 2 ^ 32).testBit i = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases hi : i < 32 <;> by_cases hki : k.toNat ≤ i <;> simp [hi, hki]

private theorem testBit_u32_shr (x : UInt32) (k : UInt32) (hk : k.toNat < 32) (i : Nat) :
    (x >>> k).toNat.testBit i = x.toNat.testBit (k.toNat + i) := by
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.testBit_shiftRight]

private theorem testBit_u32_toUInt8 (x : UInt32) (i : Nat) :
    x.toUInt8.toNat.testBit i = (decide (i < 8) && x.toNat.testBit i) := by
  rw [UInt32.toNat_toUInt8]
  change (x.toNat % 2 ^ 8).testBit i = _
  exact Nat.testBit_mod_two_pow x.toNat 8 i

private theorem testBit_u64_shl (x : UInt64) (k : UInt64) (hk : k.toNat < 64) (i : Nat) :
    (x <<< k).toNat.testBit i =
      (decide (i < 64) && decide (k.toNat ≤ i) && x.toNat.testBit (i - k.toNat)) := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk]
  change ((x.toNat <<< k.toNat) % 2 ^ 64).testBit i = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases hi : i < 64 <;> by_cases hki : k.toNat ≤ i <;> simp [hi, hki]

private theorem testBit_u64_shr (x : UInt64) (k : UInt64) (hk : k.toNat < 64) (i : Nat) :
    (x >>> k).toNat.testBit i = x.toNat.testBit (k.toNat + i) := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.testBit_shiftRight]

private theorem testBit_u64_toUInt32 (x : UInt64) (i : Nat) :
    x.toUInt32.toNat.testBit i = (decide (i < 32) && x.toNat.testBit i) := by
  rw [UInt64.toNat_toUInt32]
  change (x.toNat % 2 ^ 32).testBit i = _
  exact Nat.testBit_mod_two_pow x.toNat 32 i

private theorem testBit_u8_ge8 (b : UInt8) {i : Nat} (hi : 8 ≤ i) : b.toNat.testBit i = false :=
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
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ 32 ≤ i by
    omega) with h0 | ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | h4
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

private theorem u32_pack_unpack_bytes (b0 b1 b2 b3 : UInt8) :
    let lo := b0.toUInt32 ||| (b1.toUInt32 <<< 8)
    let hi := b2.toUInt32 ||| (b3.toUInt32 <<< 8)
    let v := lo ||| (hi <<< 16)
    v.toUInt8 = b0 ∧ (v >>> 8).toUInt8 = b1 ∧
      (v >>> 16).toUInt8 = b2 ∧ (v >>> 24).toUInt8 = b3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (
    apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq
    intro i; change (UInt8.toNat _).testBit i = _
    simp only [testBit_u32_toUInt8, testBit_u32_shr _ 8 (by decide),
      testBit_u32_shr _ 16 (by decide), testBit_u32_shr _ 24 (by decide), testBit_u32_pack4]
    by_cases hi : i < 8
    · have h8 : (8 : UInt32).toNat = 8 := rfl
      have h16 : (16 : UInt32).toNat = 16 := rfl
      have h24 : (24 : UInt32).toNat = 24 := rfl
      simp [hi, h8, h16, h24, show ¬ (8 + i < 8) by omega, show 8 + i < 16 by omega,
        show ¬ (16 + i < 8) by omega, show ¬ (16 + i < 16) by omega, show 16 + i < 24 by omega,
        show ¬ (24 + i < 8) by omega, show ¬ (24 + i < 16) by omega, show ¬ (24 + i < 24) by omega,
        show 24 + i < 32 by omega]
    · simp [hi, testBit_u8_ge8 _ (i := i) (Nat.le_of_not_lt hi)])

private theorem u32_of_u8_pack (v : UInt32) :
    (v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8)) |||
      (((v >>> 16).toUInt8.toUInt32 ||| ((v >>> 24).toUInt8.toUInt32 <<< 8)) <<< 16) = v := by
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq
  intro i; change (UInt32.toNat _).testBit i = v.toNat.testBit i
  rw [testBit_u32_pack4]
  simp only [testBit_u32_toUInt8, testBit_u32_shr _ 8 (by decide),
    testBit_u32_shr _ 16 (by decide), testBit_u32_shr _ 24 (by decide)]
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have h16 : (16 : UInt32).toNat = 16 := rfl
  have h24 : (24 : UInt32).toNat = 24 := rfl
  rw [h8, h16, h24]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ 32 ≤ i by
    omega) with h0 | ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | h4
  · simp [h0]
  · simp [show ¬ (i < 8) by omega, h1b, show i - 8 < 8 by omega, Nat.add_sub_cancel' h1a]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, h2b, show i - 16 < 8 by omega,
      Nat.add_sub_cancel' h2a]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, show ¬ (i < 24) by omega, h3b,
      show i - 24 < 8 by omega, Nat.add_sub_cancel' h3a]
  · simp [show ¬ (i < 8) by omega, show ¬ (i < 16) by omega, show ¬ (i < 24) by omega,
      show ¬ (i < 32) by omega, testBit_u32_ge32 v (i := i) h4]

private theorem u64_pack_unpack_u32 (lo hi : UInt32) :
    let v := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
    v.toUInt32 = lo ∧ (v >>> 32).toUInt32 = hi := by
  refine ⟨?_, ?_⟩ <;> (
    apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq
    intro i; change (UInt32.toNat _).testBit i = _
    simp only [testBit_u64_toUInt32, testBit_u64_shr _ 32 (by decide), UInt64.toNat_or,
      Nat.testBit_or, testBit_u64_shl _ 32 (by decide), UInt32.toNat_toUInt64]
    have h32 : (32 : UInt64).toNat = 32 := rfl
    rw [h32]
    by_cases hi32 : i < 32
    · simp [hi32, show ¬ (32 ≤ i) by omega, show 32 + i < 64 by omega,
        testBit_u32_ge32 lo (i := 32 + i) (by omega)]
    · simp [hi32, testBit_u32_ge32 _ (i := i) (Nat.le_of_not_lt hi32)])

private theorem u64_of_u32_pack (v : UInt64) :
    v.toUInt32.toUInt64 ||| ((v >>> 32).toUInt32.toUInt64 <<< 32) = v := by
  apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq
  intro i; change (UInt64.toNat _).testBit i = v.toNat.testBit i
  simp only [UInt64.toNat_or, Nat.testBit_or, testBit_u64_shl _ 32 (by decide),
    UInt32.toNat_toUInt64, testBit_u64_toUInt32, testBit_u64_shr _ 32 (by decide)]
  have h32 : (32 : UInt64).toNat = 32 := rfl
  rw [h32]
  rcases (show i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ 64 ≤ i by omega) with h0 | ⟨h1a, h1b⟩ | h2
  · simp [h0, show ¬ (32 ≤ i) by omega]
  · simp [show ¬ (i < 32) by omega, h1a, h1b, show i - 32 < 32 by omega, Nat.add_sub_cancel' h1a]
  · simp [show ¬ (i < 32) by omega, show ¬ (i < 64) by omega, testBit_u64_ge64 v h2]

public theorem decodeU32_of_bytes (ba : ByteArray) (pos : Nat) (v : UInt32) (rest : List UInt8)
    (h : ba.data.toList.drop pos = u32Bytes v ++ rest) :
    Codec0.decodeU32 ba pos = .ok v (pos + 4) := by
  dsimp only [u32Bytes] at h
  have hd0 : ba.data.toList.drop pos =
      v.toUInt8 :: ((v >>> 8).toUInt8 :: (v >>> 16).toUInt8 :: (v >>> 24).toUInt8 :: rest) := h
  have hd1 : ba.data.toList.drop (pos + 1) =
      (v >>> 8).toUInt8 :: (v >>> 16).toUInt8 :: (v >>> 24).toUInt8 :: rest := by
    rw [drop_pos_add, hd0]; rfl
  have hd2 : ba.data.toList.drop (pos + 2) = (v >>> 16).toUInt8 :: (v >>> 24).toUInt8 :: rest := by
    rw [drop_pos_add, hd0]; rfl
  have hd3 : ba.data.toList.drop (pos + 3) = (v >>> 24).toUInt8 :: rest := by
    rw [drop_pos_add, hd0]; rfl
  dsimp only [Codec0.decodeU32, Codec0.decodeU16]
  rw [decodeU8_of_bytes ba pos _ _ hd0]; dsimp only
  rw [decodeU8_of_bytes ba (pos + 1) _ _ hd1]; dsimp only
  rw [show pos + 1 + 1 = pos + 2 by omega, decodeU8_of_bytes ba (pos + 2) _ _ hd2]; dsimp only
  rw [decodeU8_of_bytes ba (pos + 3) _ _ hd3]; dsimp only
  rw [show pos + 2 + 1 + 1 = pos + 4 by omega, u32_of_u8_pack v]

public theorem decodeU32_ok_bytes (ba : ByteArray) (pos : Nat) (v : UInt32) (pos' : Nat)
    (h : Codec0.decodeU32 ba pos = .ok v pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 4 ∧ baSlice ba pos pos' = u32Bytes v := by
  dsimp only [Codec0.decodeU32] at h
  cases hlo : Codec0.decodeU16 ba pos with
  | none => rw [hlo] at h; cases h
  | ok lo p1 =>
    rw [hlo] at h; dsimp only at h
    cases hhi : Codec0.decodeU16 ba p1 with
    | none => rw [hhi] at h; cases h
    | ok hi p2 =>
      rw [hhi] at h; dsimp only [Codec0.decodeU16] at hlo hhi
      cases hb0 : Codec0.decodeU8 ba pos with
      | none => rw [hb0] at hlo; cases hlo
      | ok b0 q0 =>
        rw [hb0] at hlo; dsimp only at hlo
        obtain ⟨_, _, hq0, hs0⟩ := decodeU8_ok_bytes ba pos b0 q0 hb0; subst hq0
        cases hb1 : Codec0.decodeU8 ba (pos + 1) with
        | none => rw [hb1] at hlo; cases hlo
        | ok b1 q1 =>
          rw [hb1] at hlo
          obtain ⟨_, _, hq1, hs1⟩ := decodeU8_ok_bytes ba (pos + 1) b1 q1 hb1; subst hq1; cases hlo
          cases hb2 : Codec0.decodeU8 ba (pos + 1 + 1) with
          | none => rw [hb2] at hhi; cases hhi
          | ok b2 q2 =>
            rw [hb2] at hhi; dsimp only at hhi
            obtain ⟨_, _, hq2, hs2⟩ := decodeU8_ok_bytes ba (pos + 1 + 1) b2 q2 hb2; subst hq2
            cases hb3 : Codec0.decodeU8 ba (pos + 1 + 1 + 1) with
            | none => rw [hb3] at hhi; cases hhi
            | ok b3 q3 =>
              rw [hb3] at hhi
              obtain ⟨_, hlt, hq3, hs3⟩ :=
                decodeU8_ok_bytes ba (pos + 1 + 1 + 1) b3 q3 hb3; subst hq3
              cases hhi; cases h
              refine ⟨by omega, by omega, by omega, ?_⟩
              rw [baSlice_trans (by omega) (by omega : pos + 1 ≤ pos + 4), hs0,
                baSlice_trans (by omega) (by omega : pos + 1 + 1 ≤ pos + 4), hs1,
                baSlice_trans (by omega) (by omega : pos + 1 + 1 + 1 ≤ pos + 4), hs2, hs3]
              have hp_unpack := u32_pack_unpack_bytes b0 b1 b2 b3
              dsimp only [u32Bytes]
              rw [hp_unpack.1, hp_unpack.2.1, hp_unpack.2.2.1, hp_unpack.2.2.2]; rfl

private theorem decodeU64_of_bytes (ba : ByteArray) (pos : Nat) (v : UInt64) (rest : List UInt8)
    (h : ba.data.toList.drop pos = u64Bytes v ++ rest) :
    Codec0.decodeU64 ba pos = .ok v (pos + 8) := by
  dsimp only [u64Bytes] at h; rw [List.append_assoc] at h
  have h1 : ba.data.toList.drop (pos + 4) = u32Bytes (v >>> 32).toUInt32 ++ rest := by
    rw [drop_pos_add, h]; change (u32Bytes v.toUInt32 ++ _).drop 4 = _; exact List.drop_left' rfl
  dsimp only [Codec0.decodeU64]
  rw [decodeU32_of_bytes ba pos v.toUInt32 _ h]; dsimp only
  rw [decodeU32_of_bytes ba (pos + 4) (v >>> 32).toUInt32 rest h1]; dsimp only
  rw [u64_of_u32_pack v, show pos + 4 + 4 = pos + 8 by omega]

private theorem decodeU64_ok_bytes (ba : ByteArray) (pos : Nat) (v : UInt64) (pos' : Nat)
    (h : Codec0.decodeU64 ba pos = .ok v pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 8 ∧ baSlice ba pos pos' = u64Bytes v := by
  dsimp only [Codec0.decodeU64] at h
  cases hlo : Codec0.decodeU32 ba pos with
  | none => rw [hlo] at h; cases h
  | ok lo p1 =>
    rw [hlo] at h; dsimp only at h
    obtain ⟨_, _, hp1, hs1⟩ := decodeU32_ok_bytes ba pos lo p1 hlo; subst hp1
    cases hhi : Codec0.decodeU32 ba (pos + 4) with
    | none => rw [hhi] at h; cases h
    | ok hi p2 =>
      rw [hhi] at h
      obtain ⟨_, h2s, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 4) hi p2 hhi; subst hp2; cases h
      have hp_unpack := u64_pack_unpack_u32 lo hi
      refine ⟨by omega, h2s, by omega, ?_⟩
      rw [baSlice_trans (by omega) (by omega), hs1, hs2]
      dsimp only [u64Bytes]; rw [hp_unpack.1, hp_unpack.2]

public theorem checkHeader_of_bytes (ba : ByteArray) (rest : List UInt8)
    (h : ba.data.toList = headerBytes ++ rest) : Codec0.checkHeader ba = true := by
  have hdrop0 : ba.data.toList.drop 0 = u32Bytes 0x3042514c ++ (0x01 :: rest) := by
    rw [List.drop_zero, h]; rfl
  have hdrop4 : ba.data.toList.drop 4 = 0x01 :: rest := by rw [h]; rfl
  dsimp only [Codec0.checkHeader]
  rw [decodeU32_of_bytes ba 0 0x3042514c (0x01 :: rest) hdrop0]; dsimp only
  rw [ite_true_eq (by decide : ((0x3042514c : UInt32) == 0x3042514c) = true),
    decodeU8_of_bytes ba 4 0x01 rest hdrop4]; rfl

public theorem checkHeader_ok_bytes (ba : ByteArray) (h : Codec0.checkHeader ba = true) :
    5 ≤ ba.size ∧ baSlice ba 0 5 = headerBytes := by
  dsimp only [Codec0.checkHeader] at h
  cases h1 : Codec0.decodeU32 ba 0 with
  | none => rw [h1] at h; cases h
  | ok magic p1 =>
    rw [h1] at h; dsimp only at h
    by_cases hm : magic = 0x3042514c
    · subst hm; rw [ite_true_eq (by decide : ((0x3042514c : UInt32) == 0x3042514c) = true)] at h
      obtain ⟨_, _, hp1, hs1⟩ := decodeU32_ok_bytes ba 0 0x3042514c p1 h1; subst hp1
      cases h2 : Codec0.decodeU8 ba 4 with
      | none => rw [h2] at h; cases h
      | ok ver p2 =>
        rw [h2] at h
        by_cases hv : ver = 1
        · subst hv
          obtain ⟨_, h2s, hp2, hs2⟩ := decodeU8_ok_bytes ba 4 1 p2 h2; subst hp2
          refine ⟨h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
        · rcases ver with ⟨⟨⟨n, _⟩⟩⟩
          match n with
          | 0 => cases h
          | 1 => exact absurd rfl hv
          | _ + 2 => cases h
    · rw [ite_false_eq (by intro hb; exact hm (beq_iff_eq.mp hb))] at h; cases h

/-! ### Enum, `Arg0`, and `OpCode0` Bytes & Round-Trip -/

@[expose] public def argBytes : Arg0 → List UInt8
  | .var idx => 0 :: u32Bytes idx | .immBool false => [1] | .immBool true => [2]
  | .immBits w val => 3 :: Codec0.widthTag w :: u64Bytes val

@[expose] public def opBytes : OpCode0 → List UInt8
  | .un op t => [0, Codec0.unOp0Tag op, Codec0.ty0Tag t]
  | .bin op t => [1, Codec0.binOp0Tag op, Codec0.ty0Tag t]
  | .cmp co t => [2, Codec0.cmpOpTag co, Codec0.ty0Tag t]
  | .select t => [3, Codec0.ty0Tag t]
  | .conv op wSrc wDst => [4, Codec0.convOp0Tag op, Codec0.widthTag wSrc, Codec0.widthTag wDst]
  | .div op w => [5, Codec0.divOp0Tag op, Codec0.widthTag w]
  | .umulw64 => [6]

public theorem encodeTy0_bytes (ba : ByteArray) (t : Ty0) :
    (Codec0.encodeTy0 ba t).data.toList = ba.data.toList ++ [Codec0.ty0Tag t] :=
  ba_push_data_toList ba (Codec0.ty0Tag t)

private theorem encodeWidth0_bytes (ba : ByteArray) (w : Width) :
    (Codec0.encodeWidth0 ba w).data.toList = ba.data.toList ++ [Codec0.widthTag w] :=
  ba_push_data_toList ba (Codec0.widthTag w)

public theorem encodeArg0_bytes (ba : ByteArray) (a : Arg0) :
    (Codec0.encodeArg0 ba a).data.toList = ba.data.toList ++ argBytes a := by
  cases a with
  | var idx =>
    dsimp only [Codec0.encodeArg0, argBytes]
    rw [encodeU32_bytes, ba_push_data_toList, List.append_assoc]; rfl
  | immBool b => cases b <;> exact ba_push_data_toList ba _
  | immBits w val =>
    dsimp only [Codec0.encodeArg0, argBytes]
    rw [encodeU64_bytes, encodeWidth0_bytes, ba_push_data_toList,
      List.append_assoc, List.append_assoc]; rfl

public theorem encodeOpCode0_bytes (ba : ByteArray) (op : OpCode0) :
    (Codec0.encodeOpCode0 ba op).data.toList = ba.data.toList ++ opBytes op := by
  cases op with
  | un o t | bin o t | cmp o t =>
    dsimp only [Codec0.encodeOpCode0, Codec0.encodeOpCodeLow0, opBytes]
    rw [ba_e2_data_toList, ba_push_data_toList, List.append_assoc]; rfl
  | select t => exact ba_e2_data_toList ba _ _
  | conv c ws wd => exact ba_e4_data_toList ba _ _ _ _
  | div d w =>
    dsimp only [Codec0.encodeOpCode0, opBytes]
    rw [ba_e2_data_toList, ba_push_data_toList, List.append_assoc]; rfl
  | umulw64 => exact ba_push_data_toList ba 6

public theorem decodeTy0_of_bytes (ba : ByteArray) (pos : Nat) (t : Ty0) (rest : List UInt8)
    (h : ba.data.toList.drop pos = Codec0.ty0Tag t :: rest) :
    Codec0.decodeTy0 ba pos = .ok t (pos + 1) := by
  dsimp only [Codec0.decodeTy0]; rw [decodeU8_of_bytes ba pos _ rest h]; cases t <;> rfl

public theorem decodeTy0_ok_bytes (ba : ByteArray) (pos : Nat) (t : Ty0) (pos' : Nat)
    (h : Codec0.decodeTy0 ba pos = .ok t pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 1 ∧ baSlice ba pos pos' = [Codec0.ty0Tag t] := by
  dsimp only [Codec0.decodeTy0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok b p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨h01, h1s, hp1, hsl⟩ := decodeU8_ok_bytes ba pos b p1 hu
    have hb : b = Codec0.ty0Tag t ∧ pos' = p1 := by
      by_cases h0 : b = 0
      · subst h0; rw [ite_true_eq (by decide : ((0 : UInt8) == 0) = true)] at h
        cases h; exact ⟨rfl, rfl⟩
      · rw [ite_false_eq (fun hb => h0 (beq_iff_eq.mp hb))] at h
        by_cases h1 : b = 1
        · subst h1; rw [ite_true_eq (by decide : ((1 : UInt8) == 1) = true)] at h
          cases h; exact ⟨rfl, rfl⟩
        · rw [ite_false_eq (fun hb => h1 (beq_iff_eq.mp hb))] at h
          by_cases h2 : b = 2
          · subst h2; rw [ite_true_eq (by decide : ((2 : UInt8) == 2) = true)] at h
            cases h; exact ⟨rfl, rfl⟩
          · rw [ite_false_eq (fun hb => h2 (beq_iff_eq.mp hb))] at h
            by_cases h3 : b = 3
            · subst h3; rw [ite_true_eq (by decide : ((3 : UInt8) == 3) = true)] at h
              cases h; exact ⟨rfl, rfl⟩
            · rw [ite_false_eq (fun hb => h3 (beq_iff_eq.mp hb))] at h
              by_cases h4 : b = 4
              · subst h4; rw [ite_true_eq (by decide : ((4 : UInt8) == 4) = true)] at h
                cases h; exact ⟨rfl, rfl⟩
              · rw [ite_false_eq (fun hb => h4 (beq_iff_eq.mp hb))] at h; cases h
    rcases hb with ⟨rfl, rfl⟩; subst hp1; exact ⟨h01, h1s, rfl, hsl⟩

private theorem decodeWidth0_of_bytes (ba : ByteArray) (pos : Nat) (w : Width)
    (rest : List UInt8) (h : ba.data.toList.drop pos = Codec0.widthTag w :: rest) :
    Codec0.decodeWidth0 ba pos = .ok w (pos + 1) := by
  dsimp only [Codec0.decodeWidth0]; rw [decodeU8_of_bytes ba pos _ rest h]; cases w <;> rfl

private theorem decodeWidth0_ok_bytes (ba : ByteArray) (pos : Nat) (w : Width) (pos' : Nat)
    (h : Codec0.decodeWidth0 ba pos = .ok w pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 1 ∧
      baSlice ba pos pos' = [Codec0.widthTag w] := by
  dsimp only [Codec0.decodeWidth0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok b p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨h01, h1s, hp1, hsl⟩ := decodeU8_ok_bytes ba pos b p1 hu
    have hb : b = Codec0.widthTag w ∧ pos' = p1 := by
      by_cases h0 : b = 0
      · subst h0; rw [ite_true_eq (by decide : ((0 : UInt8) == 0) = true)] at h
        cases h; exact ⟨rfl, rfl⟩
      · rw [ite_false_eq (fun hb => h0 (beq_iff_eq.mp hb))] at h
        by_cases h1 : b = 1
        · subst h1; rw [ite_true_eq (by decide : ((1 : UInt8) == 1) = true)] at h
          cases h; exact ⟨rfl, rfl⟩
        · rw [ite_false_eq (fun hb => h1 (beq_iff_eq.mp hb))] at h
          by_cases h2 : b = 2
          · subst h2; rw [ite_true_eq (by decide : ((2 : UInt8) == 2) = true)] at h
            cases h; exact ⟨rfl, rfl⟩
          · rw [ite_false_eq (fun hb => h2 (beq_iff_eq.mp hb))] at h
            by_cases h3 : b = 3
            · subst h3; rw [ite_true_eq (by decide : ((3 : UInt8) == 3) = true)] at h
              cases h; exact ⟨rfl, rfl⟩
            · rw [ite_false_eq (fun hb => h3 (beq_iff_eq.mp hb))] at h; cases h
    rcases hb with ⟨rfl, rfl⟩; subst hp1; exact ⟨h01, h1s, rfl, hsl⟩

public theorem decodeArg0_of_bytes (ba : ByteArray) (pos : Nat) (a : Arg0) (rest : List UInt8)
    (h : ba.data.toList.drop pos = argBytes a ++ rest) :
    Codec0.decodeArg0 ba pos = .ok a (pos + (argBytes a).length) := by
  cases a with
  | var idx =>
    dsimp only [argBytes] at h ⊢
    have hd1 : ba.data.toList.drop (pos + 1) = u32Bytes idx ++ rest := by
      rw [drop_pos_add, h]; rfl
    dsimp only [Codec0.decodeArg0, Codec0.decodeArgVar0]
    rw [decodeU8_of_bytes ba pos 0 _ h]; dsimp only
    rw [ite_true_eq (by decide : ((0 : UInt8) == 0) = true),
      decodeU32_of_bytes ba (pos + 1) idx rest hd1]; rfl
  | immBool b =>
    cases b <;> (
      dsimp only [argBytes, Codec0.decodeArg0] at h ⊢
      rw [decodeU8_of_bytes ba pos _ rest h]; rfl)
  | immBits w val =>
    dsimp only [argBytes] at h ⊢
    have hd1 : ba.data.toList.drop (pos + 1) = Codec0.widthTag w :: (u64Bytes val ++ rest) := by
      rw [drop_pos_add, h]; rfl
    have hd2 : ba.data.toList.drop (pos + 2) = u64Bytes val ++ rest := by rw [drop_pos_add, h]; rfl
    dsimp only [Codec0.decodeArg0, Codec0.decodeArgBits0]
    rw [decodeU8_of_bytes ba pos 3 _ h]; dsimp only
    rw [ite_false_eq (by decide : ¬ ((3 : UInt8) == 0) = true),
      ite_false_eq (by decide : ¬ ((3 : UInt8) == 1) = true),
      ite_false_eq (by decide : ¬ ((3 : UInt8) == 2) = true),
      ite_true_eq (by decide : ((3 : UInt8) == 3) = true),
      decodeWidth0_of_bytes ba (pos + 1) w _ hd1]; dsimp only
    rw [show pos + 1 + 1 = pos + 2 by omega, decodeU64_of_bytes ba (pos + 2) val rest hd2]
    dsimp only [u64Bytes, u32Bytes]; rw [show pos + 2 + 8 = pos + 10 by omega]; rfl

public theorem decodeArg0_ok_bytes (ba : ByteArray) (pos : Nat) (a : Arg0) (pos' : Nat)
    (h : Codec0.decodeArg0 ba pos = .ok a pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ baSlice ba pos pos' = argBytes a := by
  dsimp only [Codec0.decodeArg0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok tag p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU8_ok_bytes ba pos tag p1 hu; subst hp1
    by_cases ht0 : tag = 0
    · subst ht0; rw [ite_true_eq (by decide : ((0 : UInt8) == 0) = true)] at h
      dsimp only [Codec0.decodeArgVar0] at h
      cases hx : Codec0.decodeU32 ba (pos + 1) with
      | none => rw [hx] at h; cases h
      | ok idx p2 =>
        rw [hx] at h
        obtain ⟨_, h2s, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 1) idx p2 hx; subst hp2; cases h
        refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
    · rw [ite_false_eq (fun hb => ht0 (beq_iff_eq.mp hb))] at h
      by_cases ht1 : tag = 1
      · subst ht1; cases h; exact ⟨by omega, h1s, hs1⟩
      · rw [ite_false_eq (fun hb => ht1 (beq_iff_eq.mp hb))] at h
        by_cases ht2 : tag = 2
        · subst ht2; cases h; exact ⟨by omega, h1s, hs1⟩
        · rw [ite_false_eq (fun hb => ht2 (beq_iff_eq.mp hb))] at h
          by_cases ht3 : tag = 3
          · subst ht3; rw [ite_true_eq (by decide : ((3 : UInt8) == 3) = true)] at h
            dsimp only [Codec0.decodeArgBits0] at h
            cases hw : Codec0.decodeWidth0 ba (pos + 1) with
            | none => rw [hw] at h; cases h
            | ok w p2 =>
              rw [hw] at h; dsimp only at h
              obtain ⟨_, _, hp2, hs2⟩ := decodeWidth0_ok_bytes ba (pos + 1) w p2 hw; subst hp2
              cases hv : Codec0.decodeU64 ba (pos + 1 + 1) with
              | none => rw [hv] at h; cases h
              | ok val p3 =>
                rw [hv] at h
                obtain ⟨_, h3s, hp3, hs3⟩ :=
                  decodeU64_ok_bytes ba (pos + 1 + 1) val p3 hv; subst hp3
                cases h; refine ⟨by omega, h3s, ?_⟩
                rw [baSlice_trans (by omega) (by omega : pos + 1 ≤ pos + 1 + 1 + 8), hs1,
                  baSlice_trans (by omega) (by omega : pos + 1 + 1 ≤ pos + 1 + 1 + 8), hs2, hs3]
                rfl
          · rw [ite_false_eq (fun hb => ht3 (beq_iff_eq.mp hb))] at h; cases h

public theorem decodeOpCode0_of_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0)
    (rest : List UInt8) (h : ba.data.toList.drop pos = opBytes op ++ rest) :
    Codec0.decodeOpCode0 ba pos = .ok op (pos + (opBytes op).length) := by
  cases op with
  | un o t =>
    dsimp only [opBytes] at h ⊢
    have hd1 : ba.data.toList.drop (pos + 1) =
        Codec0.unOp0Tag o :: Codec0.ty0Tag t :: rest := by rw [drop_pos_add, h]; rfl
    have hd2 : ba.data.toList.drop (pos + 2) = Codec0.ty0Tag t :: rest := by
      rw [drop_pos_add, h]; rfl
    dsimp only [Codec0.decodeOpCode0, Codec0.decodeOpCodeLow0, Codec0.decodeOpUn0]
    rw [decodeU8_of_bytes ba pos 0 _ h]; dsimp only
    rw [ite_true_eq (by decide : ((0 : UInt8) ≤ 2)),
      ite_true_eq (by decide : ((0 : UInt8) == 0) = true),
      decodeU8_of_bytes ba (pos + 1) (Codec0.unOp0Tag o) _ hd1]; dsimp only
    rw [ite_false_eq (by cases o <;> decide : ¬ (2 < Codec0.unOp0Tag o)),
      show pos + 1 + 1 = pos + 2 by omega, decodeTy0_of_bytes ba (pos + 2) t rest hd2]
    cases o <;> rfl
  | bin o t =>
    dsimp only [opBytes] at h ⊢
    have hd1 : ba.data.toList.drop (pos + 1) =
        Codec0.binOp0Tag o :: Codec0.ty0Tag t :: rest := by rw [drop_pos_add, h]; rfl
    have hd2 : ba.data.toList.drop (pos + 2) = Codec0.ty0Tag t :: rest := by
      rw [drop_pos_add, h]; rfl
    dsimp only [Codec0.decodeOpCode0, Codec0.decodeOpCodeLow0, Codec0.decodeOpBin0,
      Codec0.decodeOpBinLow0, Codec0.decodeOpBinHi0]
    rw [decodeU8_of_bytes ba pos 1 _ h]; dsimp only
    rw [ite_true_eq (by decide : ((1 : UInt8) ≤ 2)),
      ite_false_eq (by decide : ¬ ((1 : UInt8) == 0) = true),
      ite_true_eq (by decide : ((1 : UInt8) == 1) = true),
      decodeU8_of_bytes ba (pos + 1) (Codec0.binOp0Tag o) _ hd1]; dsimp only
    rw [ite_false_eq (by cases o <;> decide : ¬ (10 < Codec0.binOp0Tag o)),
      show pos + 1 + 1 = pos + 2 by omega, decodeTy0_of_bytes ba (pos + 2) t rest hd2]
    cases o <;> rfl
  | cmp co t =>
    dsimp only [opBytes] at h ⊢
    have hd1 : ba.data.toList.drop (pos + 1) =
        Codec0.cmpOpTag co :: Codec0.ty0Tag t :: rest := by rw [drop_pos_add, h]; rfl
    have hd2 : ba.data.toList.drop (pos + 2) = Codec0.ty0Tag t :: rest := by
      rw [drop_pos_add, h]; rfl
    dsimp only [Codec0.decodeOpCode0, Codec0.decodeOpCodeLow0, Codec0.decodeOpCmp0,
      Codec0.decodeOpCmpLow0, Codec0.decodeOpCmpHi0]
    rw [decodeU8_of_bytes ba pos 2 _ h]; dsimp only
    rw [ite_true_eq (by decide : ((2 : UInt8) ≤ 2)),
      ite_false_eq (by decide : ¬ ((2 : UInt8) == 0) = true),
      ite_false_eq (by decide : ¬ ((2 : UInt8) == 1) = true),
      decodeU8_of_bytes ba (pos + 1) (Codec0.cmpOpTag co) _ hd1]; dsimp only
    rw [ite_false_eq (by cases co <;> decide : ¬ (9 < Codec0.cmpOpTag co)),
      show pos + 1 + 1 = pos + 2 by omega, decodeTy0_of_bytes ba (pos + 2) t rest hd2]
    cases co <;> rfl
  | select t =>
    dsimp only [opBytes] at h ⊢
    have hd1 : ba.data.toList.drop (pos + 1) = Codec0.ty0Tag t :: rest := by
      rw [drop_pos_add, h]; rfl
    dsimp only [Codec0.decodeOpCode0, Codec0.decodeOpCodeHi0]
    rw [decodeU8_of_bytes ba pos 3 _ h]; dsimp only
    rw [ite_false_eq (by decide : ¬ ((3 : UInt8) ≤ 2)),
      ite_true_eq (by decide : ((3 : UInt8) == 3) = true),
      decodeTy0_of_bytes ba (pos + 1) t rest hd1]; rfl
  | conv c ws wd =>
    dsimp only [opBytes] at h ⊢
    have hd1 : ba.data.toList.drop (pos + 1) =
        Codec0.convOp0Tag c :: Codec0.widthTag ws :: Codec0.widthTag wd :: rest := by
      rw [drop_pos_add, h]; rfl
    have hd2 : ba.data.toList.drop (pos + 2) =
        Codec0.widthTag ws :: Codec0.widthTag wd :: rest := by rw [drop_pos_add, h]; rfl
    have hd3 : ba.data.toList.drop (pos + 3) = Codec0.widthTag wd :: rest := by
      rw [drop_pos_add, h]; rfl
    dsimp only [Codec0.decodeOpCode0, Codec0.decodeOpCodeHi0, Codec0.decodeOpConv0,
      Codec0.mkConvOp0]
    rw [decodeU8_of_bytes ba pos 4 _ h]; dsimp only
    rw [ite_false_eq (by decide : ¬ ((4 : UInt8) ≤ 2)),
      ite_false_eq (by decide : ¬ ((4 : UInt8) == 3) = true),
      ite_true_eq (by decide : ((4 : UInt8) == 4) = true),
      decodeU8_of_bytes ba (pos + 1) (Codec0.convOp0Tag c) _ hd1]; dsimp only
    rw [ite_false_eq (by cases c <;> decide : ¬ (3 < Codec0.convOp0Tag c)),
      show pos + 1 + 1 = pos + 2 by omega, decodeWidth0_of_bytes ba (pos + 2) ws _ hd2]
    dsimp only
    rw [show pos + 2 + 1 = pos + 3 by omega, decodeWidth0_of_bytes ba (pos + 3) wd rest hd3]
    cases c <;> rfl
  | div d w =>
    dsimp only [opBytes] at h ⊢
    have hd1 : ba.data.toList.drop (pos + 1) =
        Codec0.divOp0Tag d :: Codec0.widthTag w :: rest := by rw [drop_pos_add, h]; rfl
    have hd2 : ba.data.toList.drop (pos + 2) = Codec0.widthTag w :: rest := by
      rw [drop_pos_add, h]; rfl
    dsimp only [Codec0.decodeOpCode0, Codec0.decodeOpCodeHi0, Codec0.decodeOpDiv0, Codec0.mkDivOp0]
    rw [decodeU8_of_bytes ba pos 5 _ h]; dsimp only
    rw [ite_false_eq (by decide : ¬ ((5 : UInt8) ≤ 2)),
      ite_false_eq (by decide : ¬ ((5 : UInt8) == 3) = true),
      ite_false_eq (by decide : ¬ ((5 : UInt8) == 4) = true),
      ite_true_eq (by decide : ((5 : UInt8) == 5) = true),
      decodeU8_of_bytes ba (pos + 1) (Codec0.divOp0Tag d) _ hd1]; dsimp only
    rw [ite_false_eq (by cases d <;> decide : ¬ (3 < Codec0.divOp0Tag d)),
      show pos + 1 + 1 = pos + 2 by omega, decodeWidth0_of_bytes ba (pos + 2) w rest hd2]
    cases d <;> rfl
  | umulw64 =>
    dsimp only [opBytes, Codec0.decodeOpCode0, Codec0.decodeOpCodeHi0] at h ⊢
    rw [decodeU8_of_bytes ba pos 6 rest h]; rfl

private theorem decodeOpUn0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpUn0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ (match op with
      | .un u t => baSlice ba pos pos' = [Codec0.unOp0Tag u, Codec0.ty0Tag t] | _ => False) := by
  dsimp only [Codec0.decodeOpUn0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok b p1 =>
    rw [hu] at h; dsimp only at h
    by_cases hgt : 2 < b
    · rw [ite_true_eq hgt] at h; cases h
    · rw [ite_false_eq hgt] at h
      cases ht : Codec0.decodeTy0 ba p1 with
      | none => rw [ht] at h; cases h
      | ok t p2 =>
        rw [ht] at h; dsimp only at h
        obtain ⟨_, _, hp1, hs1⟩ := decodeU8_ok_bytes ba pos b p1 hu
        obtain ⟨_, h2s, hp2, hs2⟩ := decodeTy0_ok_bytes ba p1 t p2 ht
        have hbn : b.toNat ≤ 2 := by change ¬ (2 < b.toNat) at hgt; omega
        have decB : ∃ u, op = .un u t ∧ b = Codec0.unOp0Tag u ∧ pos' = p2 := by
          rw [(UInt8.ofNat_toNat (x := b)).symm] at h ⊢; revert h; generalize b.toNat = n at hbn ⊢
          match n, hbn with
          | 0, _ => intro h; cases h; exact ⟨.copy, rfl, rfl, rfl⟩
          | 1, _ => intro h; cases h; exact ⟨.neg, rfl, rfl, rfl⟩
          | 2, _ => intro h; cases h; exact ⟨.not, rfl, rfl, rfl⟩
          | _ + 3, h => omega
        rcases decB with ⟨u, rfl, rfl, rfl⟩; subst hp1; subst hp2
        refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl

private theorem decodeOpBin0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpBin0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ (match op with
      | .bin o t => baSlice ba pos pos' = [Codec0.binOp0Tag o, Codec0.ty0Tag t] | _ => False) := by
  dsimp only [Codec0.decodeOpBin0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok b p1 =>
    rw [hu] at h; dsimp only at h
    by_cases hgt : 10 < b
    · rw [ite_true_eq hgt] at h; cases h
    · rw [ite_false_eq hgt] at h
      cases ht : Codec0.decodeTy0 ba p1 with
      | none => rw [ht] at h; cases h
      | ok t p2 =>
        rw [ht] at h; dsimp only at h
        obtain ⟨_, _, hp1, hs1⟩ := decodeU8_ok_bytes ba pos b p1 hu
        obtain ⟨_, h2s, hp2, hs2⟩ := decodeTy0_ok_bytes ba p1 t p2 ht
        have hbn : b.toNat ≤ 10 := by change ¬ (10 < b.toNat) at hgt; omega
        have decB : ∃ o, op = .bin o t ∧ b = Codec0.binOp0Tag o ∧ pos' = p2 := by
          dsimp only [Codec0.decodeOpBinLow0, Codec0.decodeOpBinHi0] at h
          rw [(UInt8.ofNat_toNat (x := b)).symm] at h ⊢; revert h; generalize b.toNat = n at hbn ⊢
          match n, hbn with
          | 0, _ => intro h; cases h; exact ⟨.add, rfl, rfl, rfl⟩
          | 1, _ => intro h; cases h; exact ⟨.sub, rfl, rfl, rfl⟩
          | 2, _ => intro h; cases h; exact ⟨.mul, rfl, rfl, rfl⟩
          | 3, _ => intro h; cases h; exact ⟨.and, rfl, rfl, rfl⟩
          | 4, _ => intro h; cases h; exact ⟨.or, rfl, rfl, rfl⟩
          | 5, _ => intro h; cases h; exact ⟨.xor, rfl, rfl, rfl⟩
          | 6, _ => intro h; cases h; exact ⟨.shl, rfl, rfl, rfl⟩
          | 7, _ => intro h; cases h; exact ⟨.lshr, rfl, rfl, rfl⟩
          | 8, _ => intro h; cases h; exact ⟨.ashr, rfl, rfl, rfl⟩
          | 9, _ => intro h; cases h; exact ⟨.rotl, rfl, rfl, rfl⟩
          | 10, _ => intro h; cases h; exact ⟨.rotr, rfl, rfl, rfl⟩
          | _ + 11, h => omega
        rcases decB with ⟨o, rfl, rfl, rfl⟩; subst hp1; subst hp2
        refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl

private theorem decodeOpCmp0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpCmp0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ (match op with
      | .cmp co t => baSlice ba pos pos' = [Codec0.cmpOpTag co, Codec0.ty0Tag t] | _ => False) := by
  dsimp only [Codec0.decodeOpCmp0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok b p1 =>
    rw [hu] at h; dsimp only at h
    by_cases hgt : 9 < b
    · rw [ite_true_eq hgt] at h; cases h
    · rw [ite_false_eq hgt] at h
      cases ht : Codec0.decodeTy0 ba p1 with
      | none => rw [ht] at h; cases h
      | ok t p2 =>
        rw [ht] at h; dsimp only at h
        obtain ⟨_, _, hp1, hs1⟩ := decodeU8_ok_bytes ba pos b p1 hu
        obtain ⟨_, h2s, hp2, hs2⟩ := decodeTy0_ok_bytes ba p1 t p2 ht
        have hbn : b.toNat ≤ 9 := by change ¬ (9 < b.toNat) at hgt; omega
        have decB : ∃ co, op = .cmp co t ∧ b = Codec0.cmpOpTag co ∧ pos' = p2 := by
          dsimp only [Codec0.decodeOpCmpLow0, Codec0.decodeOpCmpHi0] at h
          rw [(UInt8.ofNat_toNat (x := b)).symm] at h ⊢; revert h; generalize b.toNat = n at hbn ⊢
          match n, hbn with
          | 0, _ => intro h; cases h; exact ⟨.eq, rfl, rfl, rfl⟩
          | 1, _ => intro h; cases h; exact ⟨.ne, rfl, rfl, rfl⟩
          | 2, _ => intro h; cases h; exact ⟨.ult, rfl, rfl, rfl⟩
          | 3, _ => intro h; cases h; exact ⟨.ule, rfl, rfl, rfl⟩
          | 4, _ => intro h; cases h; exact ⟨.ugt, rfl, rfl, rfl⟩
          | 5, _ => intro h; cases h; exact ⟨.uge, rfl, rfl, rfl⟩
          | 6, _ => intro h; cases h; exact ⟨.slt, rfl, rfl, rfl⟩
          | 7, _ => intro h; cases h; exact ⟨.sle, rfl, rfl, rfl⟩
          | 8, _ => intro h; cases h; exact ⟨.sgt, rfl, rfl, rfl⟩
          | 9, _ => intro h; cases h; exact ⟨.sge, rfl, rfl, rfl⟩
          | _ + 10, h => omega
        rcases decB with ⟨co, rfl, rfl, rfl⟩; subst hp1; subst hp2
        refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl

private theorem decodeOpConv0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpConv0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ (match op with
      | .conv c ws wd =>
        baSlice ba pos pos' = [Codec0.convOp0Tag c, Codec0.widthTag ws, Codec0.widthTag wd]
      | _ => False) := by
  dsimp only [Codec0.decodeOpConv0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok b p1 =>
    rw [hu] at h; dsimp only at h
    by_cases hgt : 3 < b
    · rw [ite_true_eq hgt] at h; cases h
    · rw [ite_false_eq hgt] at h
      cases hws : Codec0.decodeWidth0 ba p1 with
      | none => rw [hws] at h; cases h
      | ok ws p2 =>
        rw [hws] at h; dsimp only at h
        cases hwd : Codec0.decodeWidth0 ba p2 with
        | none => rw [hwd] at h; cases h
        | ok wd p3 =>
          rw [hwd] at h; dsimp only [Codec0.mkConvOp0] at h
          obtain ⟨_, _, hp1, hs1⟩ := decodeU8_ok_bytes ba pos b p1 hu
          obtain ⟨_, _, hp2, hs2⟩ := decodeWidth0_ok_bytes ba p1 ws p2 hws
          obtain ⟨_, h3s, hp3, hs3⟩ := decodeWidth0_ok_bytes ba p2 wd p3 hwd
          have hbn : b.toNat ≤ 3 := by change ¬ (3 < b.toNat) at hgt; omega
          have decB : ∃ c, op = .conv c ws wd ∧ b = Codec0.convOp0Tag c ∧ pos' = p3 := by
            rw [(UInt8.ofNat_toNat (x := b)).symm] at h ⊢; revert h; generalize b.toNat = n at hbn ⊢
            match n, hbn with
            | 0, _ => intro h; cases h; exact ⟨.ofBool, rfl, rfl, rfl⟩
            | 1, _ => intro h; cases h; exact ⟨.zext, rfl, rfl, rfl⟩
            | 2, _ => intro h; cases h; exact ⟨.sext, rfl, rfl, rfl⟩
            | 3, _ => intro h; cases h; exact ⟨.trunc, rfl, rfl, rfl⟩
            | _ + 4, h => omega
          rcases decB with ⟨c, rfl, rfl, rfl⟩; subst hp1; subst hp2; subst hp3
          refine ⟨by omega, h3s, ?_⟩
          rw [baSlice_trans (by omega) (by omega : pos + 1 ≤ pos + 1 + 1 + 1), hs1,
            baSlice_trans (by omega) (by omega : pos + 1 + 1 ≤ pos + 1 + 1 + 1), hs2, hs3]; rfl

private theorem decodeOpDiv0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpDiv0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ (match op with
      | .div d w =>
        baSlice ba pos pos' = [Codec0.divOp0Tag d, Codec0.widthTag w] | _ => False) := by
  dsimp only [Codec0.decodeOpDiv0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok b p1 =>
    rw [hu] at h; dsimp only at h
    by_cases hgt : 3 < b
    · rw [ite_true_eq hgt] at h; cases h
    · rw [ite_false_eq hgt] at h
      cases hw : Codec0.decodeWidth0 ba p1 with
      | none => rw [hw] at h; cases h
      | ok w p2 =>
        rw [hw] at h; dsimp only [Codec0.mkDivOp0] at h
        obtain ⟨_, _, hp1, hs1⟩ := decodeU8_ok_bytes ba pos b p1 hu
        obtain ⟨_, h2s, hp2, hs2⟩ := decodeWidth0_ok_bytes ba p1 w p2 hw
        have hbn : b.toNat ≤ 3 := by change ¬ (3 < b.toNat) at hgt; omega
        have decB : ∃ d, op = .div d w ∧ b = Codec0.divOp0Tag d ∧ pos' = p2 := by
          rw [(UInt8.ofNat_toNat (x := b)).symm] at h ⊢; revert h; generalize b.toNat = n at hbn ⊢
          match n, hbn with
          | 0, _ => intro h; cases h; exact ⟨.udiv, rfl, rfl, rfl⟩
          | 1, _ => intro h; cases h; exact ⟨.urem, rfl, rfl, rfl⟩
          | 2, _ => intro h; cases h; exact ⟨.sdiv, rfl, rfl, rfl⟩
          | 3, _ => intro h; cases h; exact ⟨.srem, rfl, rfl, rfl⟩
          | _ + 4, h => omega
        rcases decB with ⟨d, rfl, rfl, rfl⟩; subst hp1; subst hp2
        refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl

public theorem decodeOpCode0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpCode0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ baSlice ba pos pos' = opBytes op := by
  dsimp only [Codec0.decodeOpCode0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; cases h
  | ok tag p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU8_ok_bytes ba pos tag p1 hu; subst hp1
    by_cases hle2 : tag ≤ 2
    · rw [ite_true_eq hle2] at h; dsimp only [Codec0.decodeOpCodeLow0] at h
      by_cases ht0 : tag = 0
      · subst ht0; rw [ite_true_eq (by decide : ((0 : UInt8) == 0) = true)] at h
        obtain ⟨_, h2s, hs2⟩ := decodeOpUn0_ok_bytes ba (pos + 1) op pos' h
        cases op with
        | un u t =>
          refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
        | _ => exact False.elim hs2
      · rw [ite_false_eq (fun hb => ht0 (beq_iff_eq.mp hb))] at h
        by_cases ht1 : tag = 1
        · subst ht1; rw [ite_true_eq (by decide : ((1 : UInt8) == 1) = true)] at h
          obtain ⟨_, h2s, hs2⟩ := decodeOpBin0_ok_bytes ba (pos + 1) op pos' h
          cases op with
          | bin o t =>
            refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
          | _ => exact False.elim hs2
        · rw [ite_false_eq (fun hb => ht1 (beq_iff_eq.mp hb))] at h
          have ht2 : tag = 2 := by
            have htb := UInt8.ofNat_toNat (x := tag); have : tag.toNat ≤ 2 := hle2
            have hn0 : tag.toNat ≠ 0 := fun hz => ht0 (by rw [← htb, hz]; rfl)
            have hn1 : tag.toNat ≠ 1 := fun hz => ht1 (by rw [← htb, hz]; rfl)
            rw [← htb, (by omega : tag.toNat = 2)]; rfl
          subst ht2
          obtain ⟨_, h2s, hs2⟩ := decodeOpCmp0_ok_bytes ba (pos + 1) op pos' h
          cases op with
          | cmp co t =>
            refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
          | _ => exact False.elim hs2
    · rw [ite_false_eq hle2] at h; dsimp only [Codec0.decodeOpCodeHi0] at h
      by_cases ht3 : tag = 3
      · subst ht3; rw [ite_true_eq (by decide : ((3 : UInt8) == 3) = true)] at h
        cases ht : Codec0.decodeTy0 ba (pos + 1) with
        | none => rw [ht] at h; cases h
        | ok t p2 =>
          rw [ht] at h; obtain ⟨_, h2s, hp2, hs2⟩ := decodeTy0_ok_bytes ba (pos + 1) t p2 ht
          subst hp2; cases h; refine ⟨by omega, h2s, ?_⟩
          rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
      · rw [ite_false_eq (fun hb => ht3 (beq_iff_eq.mp hb))] at h
        by_cases ht4 : tag = 4
        · subst ht4; rw [ite_true_eq (by decide : ((4 : UInt8) == 4) = true)] at h
          obtain ⟨_, h2s, hs2⟩ := decodeOpConv0_ok_bytes ba (pos + 1) op pos' h
          cases op with
          | conv c ws wd =>
            refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
          | _ => exact False.elim hs2
        · rw [ite_false_eq (fun hb => ht4 (beq_iff_eq.mp hb))] at h
          by_cases ht5 : tag = 5
          · subst ht5; rw [ite_true_eq (by decide : ((5 : UInt8) == 5) = true)] at h
            obtain ⟨_, h2s, hs2⟩ := decodeOpDiv0_ok_bytes ba (pos + 1) op pos' h
            cases op with
            | div d w =>
              refine ⟨by omega, h2s, ?_⟩; rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
            | _ => exact False.elim hs2
          · rw [ite_false_eq (fun hb => ht5 (beq_iff_eq.mp hb))] at h
            by_cases ht6 : tag = 6
            · subst ht6; cases h; exact ⟨by omega, h1s, hs1⟩
            · rw [ite_false_eq (fun hb => ht6 (beq_iff_eq.mp hb))] at h; cases h

/-! ### List Codecs (`Ty0`, `Arg0`, `Sym0`) -/

@[expose] public def tySeqBytes : List Ty0 → List UInt8
  | [] => []
  | t :: rest => Codec0.ty0Tag t :: tySeqBytes rest

@[expose] public def tyListBytes (xs : List Ty0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ tySeqBytes xs

@[expose] public def argSeqBytes : List Arg0 → List UInt8
  | [] => []
  | a :: rest => argBytes a ++ argSeqBytes rest

@[expose] public def argListBytes (xs : List Arg0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ argSeqBytes xs

@[expose] public def symSeqBytes : List Sym0 → List UInt8
  | [] => []
  | s :: rest => u32Bytes s ++ symSeqBytes rest

@[expose] public def symListBytes (xs : List Sym0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ symSeqBytes xs

public theorem u32Bytes_length (v : UInt32) : (u32Bytes v).length = 4 := rfl

private theorem lenTysU32_eq (xs : List Ty0) (acc : UInt32) :
    Codec0.lenTysU32 xs acc = acc + UInt32.ofNat xs.length := by
  induction xs generalizing acc with
  | nil => exact (UInt32.add_zero acc).symm
  | cons _ _ ih =>
    dsimp only [Codec0.lenTysU32]
    rw [ih (acc + 1), List.length_cons, Nat.add_comm, UInt32.ofNat_add, UInt32.add_assoc]; rfl

private theorem lenArgsU32_eq (xs : List Arg0) (acc : UInt32) :
    Codec0.lenArgsU32 xs acc = acc + UInt32.ofNat xs.length := by
  induction xs generalizing acc with
  | nil => exact (UInt32.add_zero acc).symm
  | cons _ _ ih =>
    dsimp only [Codec0.lenArgsU32]
    rw [ih (acc + 1), List.length_cons, Nat.add_comm, UInt32.ofNat_add, UInt32.add_assoc]; rfl

private theorem lenSymsU32_eq (xs : List Sym0) (acc : UInt32) :
    Codec0.lenSymsU32 xs acc = acc + UInt32.ofNat xs.length := by
  induction xs generalizing acc with
  | nil => exact (UInt32.add_zero acc).symm
  | cons _ _ ih =>
    dsimp only [Codec0.lenSymsU32]
    rw [ih (acc + 1), List.length_cons, Nat.add_comm, UInt32.ofNat_add, UInt32.add_assoc]; rfl

private theorem encodeTyListLoop0_bytes (ba : ByteArray) (xs : List Ty0) :
    (Codec0.encodeTyListLoop0 ba xs).data.toList = ba.data.toList ++ tySeqBytes xs := by
  induction xs generalizing ba with
  | nil => dsimp only [Codec0.encodeTyListLoop0, tySeqBytes]; rw [List.append_nil]
  | cons t _ ih =>
    dsimp only [Codec0.encodeTyListLoop0, tySeqBytes]
    rw [ih, encodeTy0_bytes, List.append_assoc]; rfl

public theorem encodeTyList0_bytes (ba : ByteArray) (xs : List Ty0) :
    (Codec0.encodeTyList0 ba xs).data.toList = ba.data.toList ++ tyListBytes xs := by
  dsimp only [Codec0.encodeTyList0, tyListBytes]
  rw [encodeTyListLoop0_bytes, encodeU32_bytes, lenTysU32_eq, UInt32.zero_add, List.append_assoc]

private theorem encodeArgListLoop0_bytes (ba : ByteArray) (xs : List Arg0) :
    (Codec0.encodeArgListLoop0 ba xs).data.toList = ba.data.toList ++ argSeqBytes xs := by
  induction xs generalizing ba with
  | nil => dsimp only [Codec0.encodeArgListLoop0, argSeqBytes]; rw [List.append_nil]
  | cons a _ ih =>
    dsimp only [Codec0.encodeArgListLoop0, argSeqBytes]
    rw [ih, encodeArg0_bytes, List.append_assoc]

public theorem encodeArgList0_bytes (ba : ByteArray) (xs : List Arg0) :
    (Codec0.encodeArgList0 ba xs).data.toList = ba.data.toList ++ argListBytes xs := by
  dsimp only [Codec0.encodeArgList0, argListBytes]
  rw [encodeArgListLoop0_bytes, encodeU32_bytes, lenArgsU32_eq, UInt32.zero_add, List.append_assoc]

private theorem encodeSymListLoop0_bytes (ba : ByteArray) (xs : List Sym0) :
    (Codec0.encodeSymListLoop0 ba xs).data.toList = ba.data.toList ++ symSeqBytes xs := by
  induction xs generalizing ba with
  | nil => dsimp only [Codec0.encodeSymListLoop0, symSeqBytes]; rw [List.append_nil]
  | cons s _ ih =>
    dsimp only [Codec0.encodeSymListLoop0, symSeqBytes]; rw [ih, encodeU32_bytes, List.append_assoc]

public theorem encodeSymList0_bytes (ba : ByteArray) (xs : List Sym0) :
    (Codec0.encodeSymList0 ba xs).data.toList = ba.data.toList ++ symListBytes xs := by
  dsimp only [Codec0.encodeSymList0, symListBytes]
  rw [encodeSymListLoop0_bytes, encodeU32_bytes, lenSymsU32_eq, UInt32.zero_add, List.append_assoc]

private theorem revTys0_eq (xs acc : List Ty0) : Codec0.revTys0 xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x _ ih => dsimp only [Codec0.revTys0]; rw [ih, List.reverse_cons, List.append_assoc]; rfl

private theorem revArgs0_eq (xs acc : List Arg0) : Codec0.revArgs0 xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x _ ih => dsimp only [Codec0.revArgs0]; rw [ih, List.reverse_cons, List.append_assoc]; rfl

private theorem revSyms0_eq (xs acc : List Sym0) : Codec0.revSyms0 xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x _ ih => dsimp only [Codec0.revSyms0]; rw [ih, List.reverse_cons, List.append_assoc]; rfl

public theorem u32_sub1_toNat {rem : UInt32} {n : Nat} (h : rem.toNat = n + 1) :
    rem ≠ 0 ∧ (rem - 1).toNat = n := by
  have hne : rem ≠ 0 := fun hz => by subst hz; simp at h
  have h1 : (1 : UInt32) ≤ rem := by change 1 ≤ rem.toNat; rw [h]; omega
  refine ⟨hne, ?_⟩; rw [UInt32.toNat_sub_of_le rem 1 h1, h]; rfl

public theorem u32_ofNat_eq {n : Nat} {c : UInt32} (h : n = c.toNat) : UInt32.ofNat n = c := by
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  change (UInt32.ofNat n).toNat = c.toNat
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by rw [h]; exact c.toNat_lt), h]

private theorem decodeTyListLoop0_of_bytes (ba : ByteArray) :
    ∀ (xs acc : List Ty0) (pos : Nat) (rem : UInt32) (rest : List UInt8),
      rem.toNat = xs.length → ba.data.toList.drop pos = tySeqBytes xs ++ rest →
      Codec0.decodeTyListLoop0 ba pos rem acc =
        .ok (acc.reverse ++ xs) (pos + (tySeqBytes xs).length)
  | [], acc, pos, rem, _, hlen, _ => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hlen)
    unfold Codec0.decodeTyListLoop0; rw [dite_true_eq hz, revTys0_eq, List.append_nil]; rfl
  | t :: xs, acc, pos, rem, rest, hlen, hdrop => by
    obtain ⟨hpos, hrem1⟩ := u32_sub1_toNat (by simpa using hlen)
    have hd1 : ba.data.toList.drop (pos + 1) = tySeqBytes xs ++ rest := by
      rw [drop_pos_add, hdrop]; rfl
    unfold Codec0.decodeTyListLoop0
    rw [dite_false_eq hpos, decodeTy0_of_bytes ba pos t _ hdrop]; dsimp only
    rw [decodeTyListLoop0_of_bytes ba xs (t :: acc) (pos + 1) (rem - 1) rest hrem1 hd1]
    dsimp only [tySeqBytes]; simp only [List.length_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, show pos + 1 + (tySeqBytes xs).length =
        pos + ((tySeqBytes xs).length + 1) by omega]

public theorem decodeTyList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List Ty0)
    (rest : List UInt8) (hb : xs.length < 2 ^ 32)
    (h : ba.data.toList.drop pos = tyListBytes xs ++ rest) :
    Codec0.decodeTyList0 ba pos = .ok xs (pos + (tyListBytes xs).length) := by
  dsimp only [tyListBytes] at h ⊢; rw [List.append_assoc] at h
  have hd1 : ba.data.toList.drop (pos + 4) = tySeqBytes xs ++ rest := by
    rw [drop_pos_add, h]; exact List.drop_left' rfl
  have hlen : (UInt32.ofNat xs.length).toNat = xs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hb]
  dsimp only [Codec0.decodeTyList0]
  rw [decodeU32_of_bytes ba pos (UInt32.ofNat xs.length) _ h]; dsimp only
  rw [decodeTyListLoop0_of_bytes ba xs [] (pos + 4) (UInt32.ofNat xs.length) rest hlen hd1]
  simp only [List.reverse_nil, List.nil_append, List.length_append, u32Bytes_length, Nat.add_assoc]

private theorem decodeTyListLoop0_ok_bytes (ba : ByteArray) :
    ∀ (n pos : Nat) (rem : UInt32) (acc res : List Ty0) (pos' : Nat),
      rem.toNat = n → Codec0.decodeTyListLoop0 ba pos rem acc = .ok res pos' →
      pos ≤ pos' ∧ (pos ≤ ba.size → pos' ≤ ba.size) ∧
        ∃ tail : List Ty0, tail.length = n ∧ res = acc.reverse ++ tail ∧
          baSlice ba pos pos' = tySeqBytes tail
  | 0, pos, rem, acc, res, pos', hn, h => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hn)
    unfold Codec0.decodeTyListLoop0 at h; rw [dite_true_eq hz, revTys0_eq] at h; cases h
    exact ⟨Nat.le_refl _, fun hp => hp, [], rfl, rfl, baSlice_self ba pos⟩
  | n + 1, pos, rem, acc, res, pos', hn, h => by
    obtain ⟨hne, hrem1⟩ := u32_sub1_toNat hn
    unfold Codec0.decodeTyListLoop0 at h; rw [dite_false_eq hne] at h
    cases ht : Codec0.decodeTy0 ba pos with
    | none => rw [ht] at h; cases h | ok t p1 =>
      rw [ht] at h; dsimp only at h
      obtain ⟨_, h1s, hp1, hs1⟩ := decodeTy0_ok_bytes ba pos t p1 ht; subst hp1
      obtain ⟨h12, h2s, tail, hlen, hres, hs2⟩ :=
        decodeTyListLoop0_ok_bytes ba n (pos + 1) (rem - 1) (t :: acc) res pos' hrem1 h
      refine ⟨by omega, fun _ => h2s h1s, t :: tail, by simp [hlen], ?_, ?_⟩
      · rw [hres]; simp [List.reverse_cons, List.append_assoc]
      · rw [baSlice_trans (by omega) h12, hs1, hs2]; rfl

public theorem decodeTyList0_ok_bytes (ba : ByteArray) (pos : Nat) (xs : List Ty0) (pos' : Nat)
    (h : Codec0.decodeTyList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧ baSlice ba pos pos' = tyListBytes xs := by
  dsimp only [Codec0.decodeTyList0] at h
  cases hu : Codec0.decodeU32 ba pos with
  | none => rw [hu] at h; cases h | ok cnt p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU32_ok_bytes ba pos cnt p1 hu; subst hp1
    obtain ⟨h12, h2s, tail, hlen, hres, hs2⟩ :=
      decodeTyListLoop0_ok_bytes ba cnt.toNat (pos + 4) cnt [] xs pos' rfl h
    rw [List.reverse_nil, List.nil_append] at hres; subst xs
    refine ⟨by omega, h2s h1s, by rw [hlen]; exact cnt.toNat_lt, ?_⟩
    rw [baSlice_trans (by omega) h12, hs1, hs2]; dsimp only [tyListBytes]; rw [u32_ofNat_eq hlen]

private theorem decodeArgListLoop0_of_bytes (ba : ByteArray) :
    ∀ (xs acc : List Arg0) (pos : Nat) (rem : UInt32) (rest : List UInt8),
      rem.toNat = xs.length → ba.data.toList.drop pos = argSeqBytes xs ++ rest →
      Codec0.decodeArgListLoop0 ba pos rem acc =
        .ok (acc.reverse ++ xs) (pos + (argSeqBytes xs).length)
  | [], acc, pos, rem, _, hlen, _ => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hlen)
    unfold Codec0.decodeArgListLoop0; rw [dite_true_eq hz, revArgs0_eq, List.append_nil]; rfl
  | a :: xs, acc, pos, rem, rest, hlen, hdrop => by
    obtain ⟨hpos, hrem1⟩ := u32_sub1_toNat (by simpa using hlen)
    dsimp only [argSeqBytes] at hdrop ⊢; rw [List.append_assoc] at hdrop
    have hd1 : ba.data.toList.drop (pos + (argBytes a).length) = argSeqBytes xs ++ rest := by
      rw [drop_pos_add, hdrop, List.drop_left]
    unfold Codec0.decodeArgListLoop0
    rw [dite_false_eq hpos, decodeArg0_of_bytes ba pos a _ hdrop]; dsimp only
    rw [decodeArgListLoop0_of_bytes ba xs (a :: acc) (pos + (argBytes a).length) (rem - 1) rest
      hrem1 hd1]
    simp only [List.length_append, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, Nat.add_assoc]

public theorem decodeArgList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List Arg0)
    (rest : List UInt8) (hb : xs.length < 2 ^ 32)
    (h : ba.data.toList.drop pos = argListBytes xs ++ rest) :
    Codec0.decodeArgList0 ba pos = .ok xs (pos + (argListBytes xs).length) := by
  dsimp only [argListBytes] at h ⊢; rw [List.append_assoc] at h
  have hd1 : ba.data.toList.drop (pos + 4) = argSeqBytes xs ++ rest := by
    rw [drop_pos_add, h]; exact List.drop_left' rfl
  have hlen : (UInt32.ofNat xs.length).toNat = xs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hb]
  dsimp only [Codec0.decodeArgList0]
  rw [decodeU32_of_bytes ba pos (UInt32.ofNat xs.length) _ h]; dsimp only
  rw [decodeArgListLoop0_of_bytes ba xs [] (pos + 4) (UInt32.ofNat xs.length) rest hlen hd1]
  simp only [List.reverse_nil, List.nil_append, List.length_append, u32Bytes_length, Nat.add_assoc]

private theorem decodeArgListLoop0_ok_bytes (ba : ByteArray) :
    ∀ (n pos : Nat) (rem : UInt32) (acc res : List Arg0) (pos' : Nat),
      rem.toNat = n → Codec0.decodeArgListLoop0 ba pos rem acc = .ok res pos' →
      pos ≤ pos' ∧ (pos ≤ ba.size → pos' ≤ ba.size) ∧
        ∃ tail : List Arg0, tail.length = n ∧ res = acc.reverse ++ tail ∧
          baSlice ba pos pos' = argSeqBytes tail
  | 0, pos, rem, acc, res, pos', hn, h => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hn)
    unfold Codec0.decodeArgListLoop0 at h; rw [dite_true_eq hz, revArgs0_eq] at h; cases h
    exact ⟨Nat.le_refl _, fun hp => hp, [], rfl, rfl, baSlice_self ba pos⟩
  | n + 1, pos, rem, acc, res, pos', hn, h => by
    obtain ⟨hne, hrem1⟩ := u32_sub1_toNat hn
    unfold Codec0.decodeArgListLoop0 at h; rw [dite_false_eq hne] at h
    cases ha : Codec0.decodeArg0 ba pos with
    | none => rw [ha] at h; cases h | ok a p1 =>
      rw [ha] at h; dsimp only at h
      obtain ⟨h01, h1s, hs1⟩ := decodeArg0_ok_bytes ba pos a p1 ha
      obtain ⟨h12, h2s, tail, hlen, hres, hs2⟩ :=
        decodeArgListLoop0_ok_bytes ba n p1 (rem - 1) (a :: acc) res pos' hrem1 h
      refine ⟨by omega, fun _ => h2s h1s, a :: tail, by simp [hlen], ?_, ?_⟩
      · rw [hres]; simp [List.reverse_cons, List.append_assoc]
      · rw [baSlice_trans h01 h12, hs1, hs2]; rfl

public theorem decodeArgList0_ok_bytes (ba : ByteArray) (pos : Nat) (xs : List Arg0) (pos' : Nat)
    (h : Codec0.decodeArgList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧ baSlice ba pos pos' = argListBytes xs := by
  dsimp only [Codec0.decodeArgList0] at h
  cases hu : Codec0.decodeU32 ba pos with
  | none => rw [hu] at h; cases h | ok cnt p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU32_ok_bytes ba pos cnt p1 hu; subst hp1
    obtain ⟨h12, h2s, tail, hlen, hres, hs2⟩ :=
      decodeArgListLoop0_ok_bytes ba cnt.toNat (pos + 4) cnt [] xs pos' rfl h
    rw [List.reverse_nil, List.nil_append] at hres; subst xs
    refine ⟨by omega, h2s h1s, by rw [hlen]; exact cnt.toNat_lt, ?_⟩
    rw [baSlice_trans (by omega) h12, hs1, hs2]; dsimp only [argListBytes]; rw [u32_ofNat_eq hlen]

private theorem decodeSymListLoop0_of_bytes (ba : ByteArray) :
    ∀ (xs acc : List Sym0) (pos : Nat) (rem : UInt32) (rest : List UInt8),
      rem.toNat = xs.length → ba.data.toList.drop pos = symSeqBytes xs ++ rest →
      Codec0.decodeSymListLoop0 ba pos rem acc =
        .ok (acc.reverse ++ xs) (pos + (symSeqBytes xs).length)
  | [], acc, pos, rem, _, hlen, _ => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hlen)
    unfold Codec0.decodeSymListLoop0; rw [dite_true_eq hz, revSyms0_eq, List.append_nil]; rfl
  | s :: xs, acc, pos, rem, rest, hlen, hdrop => by
    obtain ⟨hpos, hrem1⟩ := u32_sub1_toNat (by simpa using hlen)
    dsimp only [symSeqBytes] at hdrop ⊢; rw [List.append_assoc] at hdrop
    have hd1 : ba.data.toList.drop (pos + 4) = symSeqBytes xs ++ rest := by
      rw [drop_pos_add, hdrop]; exact List.drop_left' rfl
    unfold Codec0.decodeSymListLoop0
    rw [dite_false_eq hpos, decodeU32_of_bytes ba pos s _ hdrop]; dsimp only
    rw [decodeSymListLoop0_of_bytes ba xs (s :: acc) (pos + 4) (rem - 1) rest hrem1 hd1]
    simp only [List.length_append, u32Bytes_length, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Nat.add_assoc]

public theorem decodeSymList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List Sym0)
    (rest : List UInt8) (hb : xs.length < 2 ^ 32)
    (h : ba.data.toList.drop pos = symListBytes xs ++ rest) :
    Codec0.decodeSymList0 ba pos = .ok xs (pos + (symListBytes xs).length) := by
  dsimp only [symListBytes] at h ⊢; rw [List.append_assoc] at h
  have hd1 : ba.data.toList.drop (pos + 4) = symSeqBytes xs ++ rest := by
    rw [drop_pos_add, h]; exact List.drop_left' rfl
  have hlen : (UInt32.ofNat xs.length).toNat = xs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hb]
  dsimp only [Codec0.decodeSymList0]
  rw [decodeU32_of_bytes ba pos (UInt32.ofNat xs.length) _ h]; dsimp only
  rw [decodeSymListLoop0_of_bytes ba xs [] (pos + 4) (UInt32.ofNat xs.length) rest hlen hd1]
  simp only [List.reverse_nil, List.nil_append, List.length_append, u32Bytes_length, Nat.add_assoc]

private theorem decodeSymListLoop0_ok_bytes (ba : ByteArray) :
    ∀ (n pos : Nat) (rem : UInt32) (acc res : List Sym0) (pos' : Nat),
      rem.toNat = n → Codec0.decodeSymListLoop0 ba pos rem acc = .ok res pos' →
      pos ≤ pos' ∧ (pos ≤ ba.size → pos' ≤ ba.size) ∧
        ∃ tail : List Sym0, tail.length = n ∧ res = acc.reverse ++ tail ∧
          baSlice ba pos pos' = symSeqBytes tail
  | 0, pos, rem, acc, res, pos', hn, h => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hn)
    unfold Codec0.decodeSymListLoop0 at h; rw [dite_true_eq hz, revSyms0_eq] at h; cases h
    exact ⟨Nat.le_refl _, fun hp => hp, [], rfl, rfl, baSlice_self ba pos⟩
  | n + 1, pos, rem, acc, res, pos', hn, h => by
    obtain ⟨hne, hrem1⟩ := u32_sub1_toNat hn
    unfold Codec0.decodeSymListLoop0 at h; rw [dite_false_eq hne] at h
    cases hs : Codec0.decodeU32 ba pos with
    | none => rw [hs] at h; cases h | ok s p1 =>
      rw [hs] at h; dsimp only at h
      obtain ⟨h01, h1s, hp1, hs1⟩ := decodeU32_ok_bytes ba pos s p1 hs; subst hp1
      obtain ⟨h12, h2s, tail, hlen, hres, hs2⟩ :=
        decodeSymListLoop0_ok_bytes ba n (pos + 4) (rem - 1) (s :: acc) res pos' hrem1 h
      refine ⟨by omega, fun _ => h2s h1s, s :: tail, by simp [hlen], ?_, ?_⟩
      · rw [hres]; simp [List.reverse_cons, List.append_assoc]
      · rw [baSlice_trans h01 h12, hs1, hs2]; rfl

public theorem decodeSymList0_ok_bytes (ba : ByteArray) (pos : Nat) (xs : List Sym0) (pos' : Nat)
    (h : Codec0.decodeSymList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧ baSlice ba pos pos' = symListBytes xs := by
  dsimp only [Codec0.decodeSymList0] at h
  cases hu : Codec0.decodeU32 ba pos with
  | none => rw [hu] at h; cases h | ok cnt p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU32_ok_bytes ba pos cnt p1 hu; subst hp1
    obtain ⟨h12, h2s, tail, hlen, hres, hs2⟩ :=
      decodeSymListLoop0_ok_bytes ba cnt.toNat (pos + 4) cnt [] xs pos' rfl h
    rw [List.reverse_nil, List.nil_append] at hres; subst xs
    refine ⟨by omega, h2s h1s, by rw [hlen]; exact cnt.toNat_lt, ?_⟩
    rw [baSlice_trans (by omega) h12, hs1, hs2]; dsimp only [symListBytes]; rw [u32_ofNat_eq hlen]


end Codec0Spec

end LeanQbe.T.Bootstrap0
